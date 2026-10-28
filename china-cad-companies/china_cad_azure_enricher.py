#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Research Chinese CAD firms with Azure OpenAI web_search, preserving XLSX formatting.

Requires Python >=3.10; pip install --upgrade openai lxml

The workbook is patched at OOXML level: only changed text cells and link relationships
are updated. All styles, filters, column widths, sheet order and other ZIP entries
are copied unchanged. Uncertain matches NEVER replace marketplace links.
"""

import argparse
import csv
import json
import os
import re
import shutil
import sys
import time
from collections import Counter
from pathlib import Path
from urllib.parse import urlsplit, urlunsplit
from zipfile import ZipFile

from lxml import etree as ET

M = 'http://schemas.openxmlformats.org/spreadsheetml/2006/main'
R = 'http://schemas.openxmlformats.org/officeDocument/2006/relationships'
P = 'http://schemas.openxmlformats.org/package/2006/relationships'
NS = {'m': M, 'r': R}
MARKETPLACE = {'zbj.com', '1688.com', 'made-in-china.com', 'alibaba.com', 'qcc.com', 'tianyancha.com', 'baidu.com', 'sogou.com'}
BAD_SCHEMES = ('javascript:', 'file:', 'data:', 'mailto:')

RESEARCH_SCHEMA = {
    'type': 'object', 'additionalProperties': False,
    'properties': {
        'status': {'type': 'string', 'enum': ['verified', 'candidate', 'not_found']},
        'official_site': {'type': 'string'},
        'matched_company_name': {'type': 'string'},
        'email': {'type': 'string'},
        'phone': {'type': 'string'},
        'contact_page': {'type': 'string'},
        'confidence': {'type': 'string', 'enum': ['high', 'medium', 'low']},
        'identity_evidence_urls': {'type': 'array', 'items': {'type': 'string'}},
        'contact_evidence_urls': {'type': 'array', 'items': {'type': 'string'}},
        'reasoning_summary': {'type': 'string'},
    },
    'required': ['status','official_site','matched_company_name','email','phone','contact_page',
                 'confidence','identity_evidence_urls','contact_evidence_urls','reasoning_summary'],
}


def normalize_name(s):
    return re.sub(r'[\s\-–—_·.。,，()（）【】\[\]"“”]', '', str(s or '')).casefold()


def clean_url(s):
    s = str(s or '').strip().rstrip('.,;，。')
    if not s or s.lower().startswith(BAD_SCHEMES):
        return ''
    if not s.startswith(('https://', 'http://')):
        return ''
    try:
        u = urlsplit(s)
        host = (u.hostname or '').lower().strip('.')
        if not host or '.' not in host or u.username or u.password:
            return ''
        if any(x in host for x in ('localhost', '127.0.0.1', '0.0.0.0')):
            return ''
        return urlunsplit((u.scheme, u.netloc, u.path or '/', u.query, ''))
    except ValueError:
        return ''


def domain(s):
    url = clean_url(s)
    return (urlsplit(url).hostname or '').lower().removeprefix('www.') if url else ''


def is_marketplace(s):
    d = domain(s)
    return any(d == x or d.endswith('.' + x) for x in MARKETPLACE)


def name_is_legal(s):
    t = str(s or '')
    return any(x in t for x in ('有限公司','有限责任公司','股份有限公司','集团公司',' Co.,',' Co.',' Ltd',' Limited',' Inc.'))


def read_strings(z):
    if 'xl/sharedStrings.xml' not in z.namelist():
        return []
    root = ET.fromstring(z.read('xl/sharedStrings.xml'))
    return [''.join(si.itertext()) for si in root.findall(f'{{{M}}}si')]


def cell_val(c, strings):
    if c is None:
        return ''
    v = c.find(f'{{{M}}}v')
    if c.get('t') == 's' and v is not None:
        try: return strings[int(v.text)]
        except (ValueError, IndexError, TypeError): return ''
    if v is not None:
        return v.text or ''
    inline = c.find(f'{{{M}}}is')
    return ''.join(inline.itertext()) if inline is not None else ''


def cells_by_col(row):
    return {re.match(r'[A-Z]+', c.get('r', '')).group(): c for c in row.findall(f'{{{M}}}c') if re.match(r'[A-Z]+', c.get('r', ''))}


def workbook_mode(z):
    required={'xl/styles.xml','xl/workbook.xml','xl/worksheets/sheet1.xml'}
    if not required.issubset(z.namelist()):
        raise ValueError('This input is not a supported XLSX workbook')
    root=ET.fromstring(z.read('xl/workbook.xml'))
    names=[x.get('name') for x in root.findall(f'.//{{{M}}}sheet')]
    if names[:3]==['All Companies','Website Audit','Summary']:
        return 'unified', names
    if names[:5]==['Firm Leads','Companies','Qualified Leads','Review','Stats']:
        return 'original', names
    raise ValueError(f'Unsupported sheet order: {names}. Refusing to risk workbook formatting.')


def xlsx_records(src):
    with ZipFile(src) as z:
        strings=read_strings(z)
        mode,names=workbook_mode(z)
        for sheet_idx in ([1] if mode=='unified' else [1,4]):
            root=ET.fromstring(z.read(f'xl/worksheets/sheet{sheet_idx}.xml'))
            data=root.find(f'{{{M}}}sheetData')
            for row in data.findall(f'{{{M}}}row'):
                i=int(row.get('r'))
                if i<2:continue
                cols=cells_by_col(row)
                get=lambda letter: str(cell_val(cols.get(letter),strings) or '')
                name=get('A').strip()
                if not name:continue
                yield {
                    'row': i,'name':name,'site':get('B'),'city':get('C'),
                    'services':get('D'),'type':get('E'),'software':get('I'),
                    'email':get('J'),'phone':get('K'),'source':get('N') or get('M'),
                    'name_type':get('AD') if mode=='unified' else '',
                    'original_list':get('X') if mode=='unified' else names[sheet_idx-1],
                    'status':get('Z') if mode=='unified' else '',
                }


def append_audit(path, result):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('a', encoding='utf-8') as f:
        f.write(json.dumps(result, ensure_ascii=False, sort_keys=True) + '\n')
        f.flush()
        os.fsync(f.fileno())


def read_audit(path):
    found = {}
    if not path.exists():
        return found
    with path.open('r', encoding='utf-8') as f:
        for line in f:
            try:
                r = json.loads(line)
                if r.get('status') != 'api_error':
                    found[normalize_name(r.get('name'))] = r
            except (ValueError, KeyError):
                continue
    return found


def web_sources(resp):
    """Ground candidate domains in URLs actually returned by web_search."""
    out = []
    try:
        dump = resp.model_dump(exclude_none=True)
    except AttributeError:
        return out
    for item in dump.get('output', []):
        if item.get('type') != 'web_search_call':
            continue
        action = item.get('action') or {}
        for entry in action.get('sources') or []:
            if isinstance(entry, dict) and clean_url(entry.get('url', '')):
                out.append(clean_url(entry['url']))
    return list(dict.fromkeys(out))


class WebSearchNotRun(RuntimeError):
    """No web search was performed; the result must not be used as evidence."""


def azure_base_url(endpoint):
    """Normalize an Azure OpenAI resource endpoint for the Azure v1 Responses API."""
    endpoint = str(endpoint or '').strip().rstrip('/')
    if not endpoint:
        raise ValueError('Set AZURE_OPENAI_ENDPOINT (e.g. https://RESOURCE.openai.azure.com).')
    parsed = urlsplit(endpoint)
    if parsed.scheme != 'https' or not parsed.hostname or parsed.username or parsed.password:
        raise ValueError('Azure endpoint must be a valid HTTPS URL without embedded credentials.')
    path = parsed.path.rstrip('/')
    if path == '/openai/v1':
        return endpoint + '/'
    if path:
        raise ValueError('Use Azure resource root or /openai/v1/, not a deployments/ or project URL.')
    return endpoint + '/openai/v1/'


def research(client, rec, model, web_tool='web_search', reasoning_effort='', simple_json=False):
    prompt = f'''Research whether this EXACT China-based CAD design supplier has an independent official website.
Company (original name): {rec['name']}
City / province: {rec['city'] or 'unspecified'}
CAD/services context: {rec['services'][:380]}
Known marketplace/profile URL (not proof of ownership): {rec['site'][:250]}
Other company context: {rec['software'][:100]}

You MUST perform a real web search. Search the public web with multiple CHINESE query variations as needed:
- exact company name 官网, 官方网站, 企业官网
- exact company name 联系方式, 联系我们, 邮箱, 电话
- company name + city + CAD/机械设计/工业设计
Distinguish similarly named firms and marketplace shop aliases from actual legal entities. Do not invent sites.
If possible consult an official-site page displaying the full Chinese registered company name, plus an independent company listing or ICP record. Only status=verified if a strong identity match is present. If ambiguous return candidate with reason; if nothing credible return not_found. No forced result. Search without substituting English names.
For email/phone, only public CORPORATE contact data, not personal phone numbers from scraped profiles. Include URLs where the contact was published; otherwise leave empty.
Return JSON matching the schema. Report independently identifiable source URLs, not links you guessed.'''
    params = {
        'model': model,
        'tools': [{'type': web_tool, 'search_context_size': 'high'}],
        'tool_choice': 'auto',
        'include': ['web_search_call.action.sources'],
        'input': prompt,
        'store': False,
    }
    if reasoning_effort:
        params['reasoning'] = {'effort': reasoning_effort}
    if simple_json:
        params['text'] = {'format': {'type': 'json_object'}}
    else:
        params['text'] = {'format': {'type': 'json_schema', 'name': 'cad_firm_research',
                                    'strict': True, 'schema': RESEARCH_SCHEMA}}
    res = client.responses.create(**params)
    search_count = sum(1 for item in res.output if getattr(item, 'type', '') == 'web_search_call')
    if not search_count:
        raise WebSearchNotRun('Azure returned no web_search_call. Search is disabled or unavailable; refusing ungrounded matches.')
    try:
        obj=json.loads(res.output_text or '')
    except json.JSONDecodeError as exc:
        raise ValueError('Azure returned non-JSON data; try a deployment supporting JSON schema, or --simple-json.') from exc
    if not isinstance(obj, dict):
        raise ValueError('Azure response is not a JSON object.')
    obj['_web_sources']=web_sources(res)
    obj['_api_search_events']=search_count
    return obj


def supported_by_sources(url, urls):
    host = domain(url)
    return bool(host) and any(domain(s) == host for s in urls)


def classify(rec, model_data):
    status=model_data.get('status', 'candidate')
    official=clean_url(model_data.get('official_site', ''))
    sources = [clean_url(u) for u in model_data.get('_web_sources', [])]
    evidence = [clean_url(u) for u in model_data.get('identity_evidence_urls', [])]
    evidence = [u for u in evidence if u]
    # Require model's purported evidence to really be in the web-search tool's retrieved sources.
    corroborated = [u for u in evidence if u in sources]
    matched=normalize_name(model_data.get('matched_company_name', ''))
    legal_name_match = name_is_legal(rec['name']) and matched == normalize_name(rec['name'])
    same_site_evidence = supported_by_sources(official, corroborated)
    accepted = (
        status == 'verified' and model_data.get('confidence') == 'high'
        and bool(official) and not is_marketplace(official)
        and legal_name_match and same_site_evidence
    )
    reason = []
    if status == 'verified' and not accepted:
        if not legal_name_match: reason.append('exact registered-name match not established')
        if not same_site_evidence: reason.append('official-domain evidence not in actual search sources')
        if not official or is_marketplace(official): reason.append('official site empty or marketplace domain')
    final_status = 'verified' if accepted else ('candidate' if status != 'not_found' and official else 'not_found')
    # Contacts are accepted only if sourced from the verified official domain.
    contact_sources = [clean_url(u) for u in model_data.get('contact_evidence_urls', [])]
    contact_sources = [u for u in contact_sources if u in sources]
    contact_ok = any(domain(x) == domain(official) for x in contact_sources)
    email = str(model_data.get('email','')).strip() if accepted and contact_ok else ''
    phone = str(model_data.get('phone','')).strip() if accepted and contact_ok else ''
    contact_page = clean_url(model_data.get('contact_page','')) if accepted and contact_ok else ''
    if email and (not re.fullmatch(r'[^\s@]+@[^\s@]+\.[^\s@]+', email) or len(email)>254): email=''
    if phone and not re.fullmatch(r'[+()\d.\- \u3000]{6,32}', phone): phone=''
    return {
        'status': final_status, 'official_site': official if final_status != 'not_found' else '',
        'email': email, 'phone': phone, 'contact_page': contact_page,
        'confidence': 'High' if accepted else 'Needs review',
        'evidence_url': corroborated[0] if corroborated else '',
        'candidate_evidence': corroborated,
        'search_sources': sources[:25],
        'reason': '; '.join(reason or [str(model_data.get('reasoning_summary',''))[:380]]),
        'api_search_events': int(model_data.get('_api_search_events',0)),
        'source_count': len(sources),
    }


def set_cell(row, letter, value):
    cells=cells_by_col(row)
    c=cells.get(letter)
    if c is None:
        c=ET.SubElement(row, f'{{{M}}}c', r=f'{letter}{row.get("r")}')
        # SpreadsheetML cell ordering, when adding an absent cell.
        def num(a):
            n=0
            for ch in a: n=n*26+ord(ch)-64
            return n
        new_idx=num(letter)
        for other in list(row):
            if other is c: continue
            match=re.match(r'[A-Z]+', other.get('r', ''))
            if match and num(match.group())>new_idx:
                row.remove(c); row.insert(list(row).index(other),c); break
    # Retain c's style ID, metadata, and every other cell in the row.
    c.set('t','str')
    for x in list(c):
        if x.tag in (f'{{{M}}}v',f'{{{M}}}is',f'{{{M}}}f'):
            c.remove(x)
    ET.SubElement(c, f'{{{M}}}v').text = str(value or '')


def new_hyperlink(sheet, ref, url, rels):
    """Add/replace an external hyperlink WITHOUT changing the cell's style."""
    if not clean_url(url):
        return
    links=sheet.find(f'{{{M}}}hyperlinks')
    if links is None:
        links=ET.Element(f'{{{M}}}hyperlinks')
        # Insert at SpreadsheetML schema-valid point, before print settings/drawings.
        successors={'printOptions','pageMargins','pageSetup','headerFooter','rowBreaks','colBreaks',
                    'customProperties','cellWatches','ignoredErrors','smartTags','drawing',
                    'legacyDrawing','legacyDrawingHF','picture','oleObjects','controls',
                    'webPublishItems','tableParts','extLst'}
        pos=len(sheet)
        for i,child in enumerate(sheet):
            if ET.QName(child).localname in successors:
                pos=i;break
        sheet.insert(pos,links)
    existing=next((h for h in links if h.get('ref')==ref),None)
    target_rel=None
    if existing is not None:
        rid=existing.get(f'{{{R}}}id')
        target_rel=next((r for r in rels if r.get('Id')==rid),None)
    else:
        existing=ET.SubElement(links,f'{{{M}}}hyperlink',ref=ref)
    if target_rel is None:
        ids={r.get('Id') for r in rels}
        i=1
        while f'rId{i}' in ids:i+=1
        rid=f'rId{i}'
        target_rel=ET.SubElement(rels,f'{{{P}}}Relationship',
            Id=rid,Type='http://schemas.openxmlformats.org/officeDocument/2006/relationships/hyperlink',
            Target=url,TargetMode='External')
        existing.set(f'{{{R}}}id',rid)
    else:
        target_rel.set('Target',url)
    if existing.get('location'):existing.attrib.pop('location')
    if existing.get('display'):existing.attrib.pop('display')


def remove_hyperlink(sheet, ref, rels):
    links=sheet.find(f'{{{M}}}hyperlinks')
    if links is None:return
    for link in list(links):
        if link.get('ref')!=ref:continue
        rid=link.get(f'{{{R}}}id')
        links.remove(link)
        # Remove unused external hyperlink relationships; unrelated links stay intact.
        if rid and not any(x.get(f'{{{R}}}id')==rid for x in links):
            for rel in list(rels):
                if rel.get('Id')==rid and rel.get('Type','').endswith('/hyperlink'):
                    rels.remove(rel)
    if len(links)==0:
        sheet.remove(links)


def make_rels(z, name):
    if name in z.namelist():
        return ET.fromstring(z.read(name))
    return ET.Element(f'{{{P}}}Relationships',nsmap={None:P})


def patch_workbook(inp, out, audit):
    """Patch text and URL relationships, keeping all XLSX styles and layout intact.

    Supports original five-sheet workbook and later three-sheet consolidated workbook.
    """
    tmp=out.with_name(out.stem+'.tmp.xlsx')
    modified_rows=0
    modified_names=set()
    with ZipFile(inp) as src:
        mode,_=workbook_mode(src)
        strings=read_strings(src)
        patch_indices=[1,2] if mode=='unified' else [1,2,3,4]
        parts={}
        for idx in patch_indices:
            sheet_name=f'xl/worksheets/sheet{idx}.xml'
            rel_name=f'xl/worksheets/_rels/sheet{idx}.xml.rels'
            sheet=ET.fromstring(src.read(sheet_name))
            rels=make_rels(src,rel_name)
            sheet_modified=False
            for row in sheet.findall(f'.//{{{M}}}sheetData/{{{M}}}row'):
                n=int(row.get('r'))
                if n<2:continue
                cols=cells_by_col(row)
                name=cell_val(cols.get('A'),strings)
                result=audit.get(normalize_name(name))
                if not result or result.get('status')!='verified':continue
                site=clean_url(result.get('official_site'))
                if not site or is_marketplace(site):continue
                old_site=cell_val(cols.get('B'),strings)
                if old_site and not is_marketplace(old_site) and domain(old_site)!=domain(site):
                    continue  # preserve an existing independent website
                set_cell(row,'B',site)
                new_hyperlink(sheet,f'B{n}',site,rels)
                for fld,col in [('email','J'),('phone','K'),('contact_page','L')]:
                    previous=cell_val(cols.get(col),strings)
                    if result.get(fld) and (not previous or is_marketplace(previous)):
                        set_cell(row,col,result[fld])
                # No duplicated vendor/catalog URL after a verified website replacement.
                for col in ('H','L','M','N'):
                    if is_marketplace(cell_val(cols.get(col),strings)):
                        set_cell(row,col,'')
                        remove_hyperlink(sheet,f'{col}{n}',rels)
                if mode=='unified' and idx==1:
                    set_cell(row,'Z','Official website confirmed (API research)')
                    set_cell(row,'AA','High')
                    set_cell(row,'AB',result.get('evidence_url') or site)
                    set_cell(row,'AC',f'Web search evidence in external audit; {result.get("reason", "")[:160]}')
                if mode=='unified' and idx==2:
                    set_cell(row,'C','Official website confirmed (API research)')
                    set_cell(row,'D','High')
                    set_cell(row,'E',result.get('evidence_url') or site)
                    set_cell(row,'H','Web search; see external audit JSONL')
                sheet_modified=True
                modified_rows+=1
                modified_names.add(normalize_name(name))
            if sheet_modified:
                parts[sheet_name]=ET.tostring(sheet,xml_declaration=False,encoding='utf-8')
                parts[rel_name]=ET.tostring(rels,xml_declaration=True,encoding='utf-8')
        with ZipFile(tmp,'w') as dst:
            for item in src.infolist():
                dst.writestr(item,parts.pop(item.filename,src.read(item.filename)))
            for name,content in parts.items():
                dst.writestr(name,content)
    tmp.replace(out)
    with ZipFile(inp) as x, ZipFile(out) as y:
        for n in x.namelist():
            if (n.startswith('xl/styles') or n=='xl/workbook.xml' or n.startswith('xl/theme/')
                    or n.startswith('xl/tables/') or n=='xl/worksheets/sheet5.xml'):
                assert x.read(n)==y.read(n), f'Formatting changed in {n}'
    return len(modified_names)


def count_discovered(all_rows, existing, allow_existing):
    eligible=[]
    seen=set()
    for r in sorted(all_rows,key=lambda x:(0 if x['original_list']=='Firm Leads' else 1,
                                         0 if name_is_legal(x['name']) else 1,x['row'])):
        key=normalize_name(r['name'])
        if key in seen:continue
        seen.add(key)
        if not allow_existing and r['site'] and not is_marketplace(r['site']):continue
        eligible.append(r)
    return eligible


def export_csv(path, results):
    fields=['company','row','status','official_site','email','phone','confidence','evidence_url','reason','api_search_events']
    with path.open('w',encoding='utf-8-sig',newline='') as fh:
        w=csv.DictWriter(fh,fieldnames=fields,extrasaction='ignore')
        w.writeheader()
        for r in results.values():w.writerow(r)


def cli():
    p=argparse.ArgumentParser(description='Azure OpenAI China CAD website matcher (format-preserving XLSX)')
    p.add_argument('--input',required=True,type=Path,help='Original five-sheet OR consolidated three-sheet Excel')
    p.add_argument('--out',type=Path,required=True,help='Output Excel; never the same as input')
    p.add_argument('--model',default='',help='Azure deployment name; default AZURE_OPENAI_DEPLOYMENT')
    p.add_argument('--azure-endpoint',default='',help='Azure resource URL; default AZURE_OPENAI_ENDPOINT')
    p.add_argument('--web-tool',choices=['web_search','web_search_preview'],default='web_search',help='Azure web tool; web_search is preferred')
    p.add_argument('--reasoning-effort',choices=['low','medium','high'],default='',help='Optional: only for deployments supporting reasoning')
    p.add_argument('--simple-json',action='store_true',help='Use json_object mode if strict JSON schema is unsupported')
    p.add_argument('--probe',action='store_true',help='One live API web-search test; writes NO Excel or cache')
    p.add_argument('--limit',type=int,default=20,help='0 = all remaining; default 20 to test safely')
    p.add_argument('--checkpoint-every',type=int,default=25)
    p.add_argument('--max-api-calls',type=int,default=2000,help='Hard upper bound on model requests (not search actions)')
    p.add_argument('--retry-not-found',action='store_true')
    p.add_argument('--retry-candidates',action='store_true',help='Revisit uncertain matches')
    p.add_argument('--deep',action='store_true',help='Second targeted web research on unconfirmed companies (higher cost)')
    p.add_argument('--dry-run',action='store_true')
    p.add_argument('--demo-patch',action='store_true',help='Offline test: use one simulated verified site; NO API requests')
    p.add_argument('--audit',type=Path,help='JSONL cache and provenance; default output stem + _audit.jsonl')
    p.add_argument('--pause',type=float,default=0.0,help='Optional time between API calls; API rate limits still apply')
    p.add_argument('--recheck-existing',action='store_true',help='Include rows with independent websites for review (never overwrite them)')
    return p.parse_args()


def main():
    args=cli()
    if args.input.resolve()==args.out.resolve():
        sys.exit('Input and output must be different to protect the source Excel file.')
    if not args.input.exists():
        sys.exit(f'Input Excel not found: {args.input}')
    audit_path=args.audit or args.out.with_name(args.out.stem+'_audit.jsonl')
    audit=read_audit(audit_path)
    records=list(xlsx_records(args.input))
    eligible=count_discovered(records,audit,args.recheck_existing)
    print(f'[input] {len(records)} records; {len(eligible)} unique companies eligible; cache {len(audit)}')
    if args.dry_run:
        for x in eligible[:min(args.limit or 10,10)]:print('[preview]',x['row'],x['name'],x['site'][:70])
        return
    if args.demo_patch:
        target=next((r for r in records if name_is_legal(r['name']) and is_marketplace(r['site'])),None)
        if not target:
            sys.exit('No demo company found')
        key=normalize_name(target['name'])
        audit[key]={'name':target['name'],'row':target['row'],'status':'verified',
                    'official_site':'https://example.org/test-verified-site/',
                    'email':'','phone':'','contact_page':'','evidence_url':'https://example.org/test-verified-site/',
                    'reason':'OFFLINE FIXTURE ONLY: not real evidence', 'confidence':'High','api_search_events':0}
        print('[demo] creating a FORMAT-ONLY test file. Example.org is NOT a verified real company site.')
        print('[demo]',patch_workbook(args.input,args.out,audit),'rows patched')
        return
    key = os.environ.get('AZURE_OPENAI_API_KEY', '').strip()
    if not key:
        sys.exit('Set AZURE_OPENAI_API_KEY in PowerShell. Never paste secrets into the source code or chat.')
    try:
        endpoint = azure_base_url(args.azure_endpoint or os.environ.get('AZURE_OPENAI_ENDPOINT'))
    except ValueError as exc:
        sys.exit(str(exc))
    deployment = (args.model or os.environ.get('AZURE_OPENAI_DEPLOYMENT') or '').strip()
    if not deployment:
        sys.exit('Set AZURE_OPENAI_DEPLOYMENT or pass --model with your Azure deployment name.')
    from openai import OpenAI
    client=OpenAI(api_key=key,base_url=endpoint,timeout=120.0,max_retries=2)
    if args.probe:
        rec=next((r for r in eligible if name_is_legal(r['name'])),eligible[0] if eligible else None)
        if not rec:
            sys.exit('No company available to test.')
        print(f'[probe] one live Azure search: {rec["name"]}; deployment={deployment}; tool={args.web_tool}')
        try:
            data=research(client,rec,deployment,args.web_tool,args.reasoning_effort,args.simple_json)
            result=classify(rec,data)
        except Exception as exc:
            sys.exit(f'[probe failed] {type(exc).__name__}: {exc}')
        print(f'[probe OK] web_search_calls={data["_api_search_events"]}; source_urls={result["source_count"]}')
        print(f'[probe result] {result["status"]}: {result["official_site"] or "no confirmed site"}')
        if result['source_count']==0:
            print('[warning] No search source URLs; automatic website verification will reject all ungrounded matches.')
        return
    calls=0
    processed=0
    for rec in eligible:
        key=normalize_name(rec['name'])
        cached=audit.get(key)
        if cached and not ((args.retry_not_found and cached.get('status')=='not_found')
                           or (args.retry_candidates and cached.get('status')=='candidate')):
            continue
        if args.limit>0 and processed>=args.limit:break
        if calls>=args.max_api_calls:break
        try:
            report=research(client,rec,deployment,args.web_tool,args.reasoning_effort,args.simple_json)
            result=classify(rec,report)
            calls_for_firm=1
            if args.deep and result['status']!='verified' and calls+calls_for_firm<args.max_api_calls:
                deep_rec=dict(rec)
                deep_rec['services'] = ('Search alternative exact names, official domains, corporate ICP registration, independent evidence. ' + rec['services'])
                second=research(client,deep_rec,deployment,args.web_tool,args.reasoning_effort,args.simple_json)
                second_result=classify(rec,second)
                calls_for_firm+=1
                if second_result['status']=='verified': result=second_result
                elif result['status']=='not_found' and second_result['status']=='candidate': result=second_result
            result['api_requests']=calls_for_firm
        except Exception as e:
            if isinstance(e,WebSearchNotRun) or type(e).__name__ in {'AuthenticationError','PermissionDeniedError','BadRequestError','NotFoundError'}:
                print(f'[fatal Azure configuration] {type(e).__name__}: {e}', file=sys.stderr)
                break
            result={'status':'api_error','reason':str(e)[:450],
                    'official_site':'','confidence':'Error','api_search_events':0}
        result.update({'name':rec['name'],'row':rec['row'],'company':rec['name'],
                       'searched_at_utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime())})
        append_audit(audit_path,result)
        if result['status']!='api_error': audit[key]=result
        calls+=result.get('api_requests',1)
        processed+=1
        print(f'[{calls} calls] {rec["name"][:35]} -> {result["status"]} {result.get("official_site","")[:65]}',flush=True)
        if processed % args.checkpoint_every==0:
            n=patch_workbook(args.input,args.out,audit)
            print(f'[checkpoint] {n} verified sites patched in {args.out}',flush=True)
        if args.pause>0:time.sleep(args.pause)
    changed=patch_workbook(args.input,args.out,audit)
    export_csv(args.out.with_name(args.out.stem+'_audit.csv'),audit)
    summary=Counter(x.get('status','?') for x in audit.values())
    print(f'[done] saved {args.out}; {changed} website replacements; {calls} model calls; statuses {dict(summary)}')
    print(f'[audit] {audit_path}; [review] {args.out.with_name(args.out.stem+"_audit.csv")}')
    print('[note] External evidence is machine-assisted and must be checked for high-value leads.')


if __name__=='__main__':
    main()
