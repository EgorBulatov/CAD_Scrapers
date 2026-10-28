#!/usr/bin/env python3
"""Audit EVERY CAD candidate row in a styled XLSX with Azure OpenAI web_search.

Reads name, current contact, profile (including GitHub/GitLab), project, and
supporting URL(s). Verifies existing emails and searches for a public,
person-specific email/LinkedIn when a row lacks a verified personal email.
Uses strict source + identity evidence; never guesses email patterns, and never
substitutes a repository owner's address for an individual contributor.

Requirements: Python >=3.10, `python -m pip install -U openai`.
Environment: AZURE_OPENAI_ENDPOINT, AZURE_OPENAI_DEPLOYMENT, AZURE_OPENAI_API_KEY.
No Google Sheets or browser dependency. Retains XLSX styles via targeted OOXML
patching, writes an audit CSV and an SQLite resume cache. The original XLSX
is not modified.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import csv
from collections import Counter, defaultdict
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime
import hashlib
from html import unescape
import ipaddress
import json
import os
from pathlib import Path
import posixpath
import random
import re
import sqlite3
import sys
import threading
import time
from urllib.parse import unquote, urlparse
from xml.etree import ElementTree as ET
from zipfile import ZipFile

MAIN = 'http://schemas.openxmlformats.org/spreadsheetml/2006/main'
REL = 'http://schemas.openxmlformats.org/officeDocument/2006/relationships'
PKG = 'http://schemas.openxmlformats.org/package/2006/relationships'
NS = {'m': MAIN, 'r': REL}
ET.register_namespace('', MAIN)
ET.register_namespace('r', REL)
ET.register_namespace('mc', 'http://schemas.openxmlformats.org/markup-compatibility/2006')

EMAIL_RE = re.compile(r'(?<![\w.+-])([\w.+-]+@[\w.-]+\.[a-z]{2,})(?![\w.-])', re.I)
URL_RE = re.compile(r'https?://[^\s;<>"\']+', re.I)
LI_RE = re.compile(r'https?://(?:[a-z]{2,3}\.)?linkedin\.com/(?:in|pub)/[\w%.-]+/?', re.I)
BAD_LOCAL = ('noreply','no-reply','donotreply','admin','support','info','sales',
             'office','contact','webmaster','privacy','press','helpdesk',
             'postmaster','newsletter','service','robot','dean','dekan',
             'rector','rektor','sekretariat','reception','admission','admissions',
             'kafedra','department','faculty','hr','jobs','career','sed','cpk')
BAD_DOMAIN = {'example.com','example.org','domain.com','wixpress.com','sentry.io','localhost'}
CYR = dict(zip('абвгдежзийклмнопрстуфхцчшщъыьэюя',
               ['a','b','v','g','d','e','zh','z','i','y','k','l','m','n','o','p','r',
                's','t','u','f','kh','ts','ch','sh','shch','','y','','e','yu','ya']))
AUDIT_HEADERS = [
    'sheet','row','name','profile_url','project_url','contact_cell',
    'original_contact','existing_email','existing_linkedin','status',
    'verified_existing_email','found_email','found_linkedin','written_contact',
    'email_source','linkedin_source','email_evidence','linkedin_evidence',
    'reason','api_calls','updated_utc']


def utc_now():
    return datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def translit(value):
    return ''.join(CYR.get(c, c) for c in str(value).lower().replace('ё','е'))


def identity_tokens(name):
    """Conservative possible surname/unique handle; avoids first-name matching."""
    original = re.findall(r'[a-zа-яё]+', str(name).lower())
    words = [translit(s) for s in original]
    if not words:
        return []
    if len(words) == 1:
        return [words[0]] if len(words[0]) >= 5 else []
    pat = ('ovich','evich','ovna','evna','ichna','inichna','ич','ович','евич','овна','евна','ична')
    if len(original) >= 3 and (original[-1].endswith(pat) or words[-1].endswith(pat)):
        word = words[0]
    else:
        word = words[-1]
    return [word] if len(word) >= 5 else []


def valid_email(value):
    value = unquote(unescape(str(value or ''))).strip().lower().strip('.,;:<>[]()"\'')
    if not EMAIL_RE.fullmatch(value) or len(value) > 254:
        return ''
    local, domain = value.split('@',1)
    if local.startswith(BAD_LOCAL) or domain in BAD_DOMAIN or len(local) < 2 or '..' in value:
        return ''
    if domain.endswith(('.png','.jpg','.jpeg','.svg','.webp')):
        return ''
    return value


def email_in(value):
    for match in EMAIL_RE.findall(str(value or '')):
        email = valid_email(match)
        if email:
            return email
    return ''


def safe_url(value):
    try:
        value = str(value or '').strip().strip('.,;\'"<>')
        p = urlparse(value)
        if p.scheme.lower() not in ('http','https') or not p.hostname or p.username or p.password:
            return ''
        host = p.hostname.lower()
        if host in ('localhost',) or host.endswith(('.local','.internal')):
            return ''
        try:
            addr = ipaddress.ip_address(host)
            if not addr.is_global:
                return ''
        except ValueError:
            pass
        return value
    except (ValueError, TypeError):
        return ''


def linkedin_in(value):
    match = LI_RE.search(str(value or ''))
    return safe_url(match.group(0)) if match else ''


def parse_urls(text, limit=6):
    found = []
    for match in URL_RE.findall(str(text or '')):
        u = safe_url(match.rstrip('.,;)]'))
        if u and u not in found:
            found.append(u)
        if len(found) >= limit:
            break
    return found


def xlsx_text(cell, shared):
    if cell is None:
        return ''
    typ = cell.get('t')
    if typ == 's':
        v = cell.find(f'{{{MAIN}}}v')
        try:
            return shared[int(v.text)] if v is not None else ''
        except (ValueError, IndexError, TypeError):
            return ''
    if typ in ('inlineStr','str'):
        return ''.join(n.text or '' for n in cell.findall(f'.//{{{MAIN}}}t'))
    v = cell.find(f'{{{MAIN}}}v')
    return (v.text or '') if v is not None else ''


def workbook_metadata(z):
    wb = ET.fromstring(z.read('xl/workbook.xml'))
    rels = ET.fromstring(z.read('xl/_rels/workbook.xml.rels'))
    paths = {}
    for node in rels:
        target = node.attrib.get('Target','')
        paths[node.get('Id')] = (target.lstrip('/') if target.startswith('/')
                                 else posixpath.normpath(posixpath.join('xl',target)))
    sheets = [(n.get('name'),paths.get(n.get(f'{{{REL}}}id')))
              for n in wb.findall('m:sheets/m:sheet',NS)]
    shared = []
    if 'xl/sharedStrings.xml' in z.namelist():
        root = ET.fromstring(z.read('xl/sharedStrings.xml'))
        shared = [''.join(n.text or '' for n in si.findall('.//m:t',NS))
                  for si in root.findall('m:si',NS)]
    return sheets,shared


def rels_path(path):
    folder, filename = posixpath.split(path)
    return posixpath.join(folder,'_rels',filename+'.rels')


def collect_candidates(z, only_sheets=None):
    sheets,shared = workbook_metadata(z)
    candidates, metadata = [], {}
    for sheet_name,path in sheets:
        if only_sheets and sheet_name.casefold() not in only_sheets:
            continue
        if not path or path not in z.namelist():
            continue
        root = ET.fromstring(z.read(path))
        rows = root.findall('m:sheetData/m:row',NS)
        if not rows:
            continue
        headers = {}
        for cell in rows[0].findall('m:c',NS):
            col = re.match(r'^[A-Z]+',cell.get('r',''))
            if col:
                headers[xlsx_text(cell,shared).strip().lower()] = col.group()
        name_col = next((headers[h] for h in ('username / name','name','candidate name','candidate') if h in headers),None)
        contact_col = next((headers[h] for h in ('email / linkedin','email/ linkedin','email / website',
                    'email / contact','email','contact','contact info','contact information') if h in headers),None)
        if not (name_col and contact_col):
            continue
        rpath = rels_path(path)
        relroot = ET.fromstring(z.read(rpath)) if rpath in z.namelist() else None
        relmap = {n.get('Id'):n.get('Target','') for n in relroot} if relroot is not None else {}
        links = root.find('m:hyperlinks',NS)
        hmap = {n.get('ref'):n for n in links} if links is not None else {}
        metadata[path] = (root,relroot,rpath,hmap)

        def data_at(data,field):
            return xlsx_text(data.get(headers.get(field,'')),shared).strip()

        for row in rows[1:]:
            cells = {}
            for cell in row.findall('m:c',NS):
                matched = re.match(r'^[A-Z]+',cell.get('r',''))
                if matched:
                    cells[matched.group()] = cell
            name = xlsx_text(cells.get(name_col),shared).strip()
            if not name:
                continue
            rnum = int(row.get('r'))
            addr = f'{contact_col}{rnum}'
            contact = xlsx_text(cells.get(contact_col),shared).strip()
            def text_and_hyperlink(field):
                value = data_at(cells,field)
                col = headers.get(field)
                hnode = hmap.get(f'{col}{rnum}') if col else None
                link = relmap.get(hnode.get(f'{{{REL}}}id'),'') if hnode is not None else ''
                return value,link
            profile,plink = text_and_hyperlink('profile url')
            project,projlink = text_and_hyperlink('cad repository / project')
            evidence,evlink = text_and_hyperlink('evidence url')
            other = data_at(cells,'all source urls')
            source_list = []
            for item in (profile,plink,contact,project,projlink,evidence,evlink,other):
                for url in parse_urls(item,limit=8):
                    if url not in source_list:
                        source_list.append(url)
            # Prefer the actual individual's profile, not the owner of a linked CAD repository.
            profile_url = next(iter(parse_urls(profile) + parse_urls(plink)), '')
            project_url = next(iter(parse_urls(project) + parse_urls(projlink)), '')
            existing_email = email_in(contact)
            if not existing_email:
                existing_email = email_in(data_at(cells,'public email'))
            existing_li = linkedin_in(contact) or linkedin_in(data_at(cells,'linkedin'))
            candidates.append({
                'sheet':sheet_name,'path':path,'row':rnum,'cell':addr,'name':name,
                'old':contact,'profile':profile_url,'project':project_url,
                'existing_email':existing_email,'existing_linkedin':existing_li,
                'sources':source_list[:10],
                'specialization':data_at(cells,'cad specialization')[:350],
                'platform':data_at(cells,'platform')[:100],
                'other_contact':data_at(cells,'contact form')[:350],
            })
    return candidates,metadata


def write_cell(cell,text):
    for child in list(cell):
        if child.tag in (f'{{{MAIN}}}v',f'{{{MAIN}}}f',f'{{{MAIN}}}is'):
            cell.remove(child)
    cell.set('t','inlineStr')
    el = ET.SubElement(cell,f'{{{MAIN}}}is')
    ET.SubElement(el,f'{{{MAIN}}}t').text = text


def ensure_cell(root,address):
    rownum = int(re.search(r'\d+',address).group())
    row = next((r for r in root.findall('m:sheetData/m:row',NS)
                if int(r.get('r','0')) == rownum),None)
    if row is None:
        raise ValueError('Cannot find source row for '+address)
    existing = next((c for c in row.findall('m:c',NS) if c.get('r')==address),None)
    if existing is not None:
        return existing
    cell = ET.Element(f'{{{MAIN}}}c',{'r':address})
    colidx = sum((ord(ch)-64)*26**i for i,ch in enumerate(re.match(r'[A-Z]+',address).group()[::-1]))
    nodes = list(row)
    pos = len(nodes)
    for i,old in enumerate(nodes):
        if old.tag != f'{{{MAIN}}}c':
            continue
        m = re.match(r'[A-Z]+',old.get('r',''))
        if m:
            otheridx = sum((ord(ch)-64)*26**j for j,ch in enumerate(m.group()[::-1]))
            if otheridx > colidx:
                pos = i
                break
    row.insert(pos,cell)
    return cell


def patch_xlsx(inp,out,metadata,changes):
    bysheet = defaultdict(dict)
    for record in changes:
        bysheet[record['path']][record['cell']] = record['written_contact']
    updates = {}
    for path,items in bysheet.items():
        root,rels,rpath,hmap = metadata[path]
        links = root.find('m:hyperlinks',NS)
        relbyid = {r.get('Id'):r for r in rels} if rels is not None else {}
        counts = Counter(node.get(f'{{{REL}}}id') for node in hmap.values())
        for addr,newvalue in items.items():
            cell = ensure_cell(root,addr)
            write_cell(cell,newvalue)
            oldlink = hmap.get(addr)
            destination = ('mailto:'+newvalue if email_in(newvalue)==newvalue
                           else newvalue if safe_url(newvalue) else '')
            if not destination:
                continue
            if rels is None:
                rels = ET.Element(f'{{{PKG}}}Relationships')
            if oldlink is not None:
                rid = oldlink.get(f'{{{REL}}}id')
                if rid in relbyid and counts[rid] == 1:
                    relbyid[rid].set('Target',destination)
                    relbyid[rid].set('TargetMode','External')
                    continue
            else:
                if links is None:
                    links = ET.SubElement(root,f'{{{MAIN}}}hyperlinks')
                oldlink = ET.SubElement(links,f'{{{MAIN}}}hyperlink',{'ref':addr})
                hmap[addr] = oldlink
            new_id = 'rIdContact'+str(len(relbyid)+1)
            while new_id in relbyid:
                new_id += 'x'
            relbyid[new_id] = ET.SubElement(rels,f'{{{PKG}}}Relationship',{
                'Id':new_id,'Type':REL+'/hyperlink','Target':destination,
                'TargetMode':'External'})
            oldlink.attrib.pop('location',None)
            oldlink.set(f'{{{REL}}}id',new_id)
        updates[path] = ET.tostring(root,encoding='utf-8',xml_declaration=True)
        if rels is not None:
            updates[rpath] = ET.tostring(rels,encoding='utf-8',xml_declaration=True)
    temp = out.with_suffix('.tmp.xlsx')
    with ZipFile(inp) as src,ZipFile(temp,'w') as dst:
        existing = set(src.namelist())
        for entry in src.infolist():
            dst.writestr(entry,updates.pop(entry.filename,src.read(entry.filename)))
        # A template without worksheet relationships is rare but supported.
        for path,data in updates.items():
            if path.endswith('.rels') and path not in existing:
                dst.writestr(path,data)
    with ZipFile(temp) as test:
        if test.testzip():
            raise ValueError('XLSX ZIP verification failed')
    temp.replace(out)


def key_for(candidate):
    # Cross-sheet reuse only when candidate identity + leading profile match.
    identity = candidate['profile'] or '|'.join(candidate['sources'][:1])
    return hashlib.sha256((candidate['name'].casefold().strip()+'\n'+identity.lower().strip()+
                           '\n'+candidate['existing_email'].lower()).encode('utf-8')).hexdigest()


def normalized_source(url):
    p = urlparse(safe_url(url))
    if not p.hostname:
        return None
    return p.hostname.lower().removeprefix('www.'),unquote(p.path).rstrip('/').casefold()


def source_supported(url,source_urls):
    target = normalized_source(url)
    return target is not None and any(normalized_source(x)==target for x in source_urls)


def person_identity_tokens(candidate):
    tokens = identity_tokens(candidate['name'])
    if not tokens:
        # A single-name person (e.g. Oleg) can be corroborated using the
        # unique handle from an explicitly linked PERSONAL code-host profile.
        p = urlparse(candidate['profile'])
        host = (p.hostname or '').lower()
        pieces = [x for x in p.path.split('/') if x]
        if host in ('github.com','www.github.com','gitlab.com','www.gitlab.com') and len(pieces)==1:
            handle = re.sub('[^a-z0-9]','',translit(unquote(pieces[0])))
            if len(handle)>=5:
                tokens.append(handle)
    return tokens


def email_evidence_specific(candidate,email,excerpt):
    excerpt = str(excerpt or '')[:500]
    if not excerpt or email.lower() not in re.sub(r'\s+','',unescape(excerpt).lower()):
        return False
    plain = re.sub('[^a-z0-9]','',translit(excerpt))
    return any(t in plain for t in person_identity_tokens(candidate))


def linkedin_evidence_specific(candidate,excerpt):
    plain = re.sub('[^a-z0-9]','',translit(str(excerpt or '')))
    return bool(plain) and any(t in plain for t in person_identity_tokens(candidate))


def surname_in_email(candidate,email):
    local = re.sub('[^a-z0-9]','',translit(email.split('@')[0]))
    return any(t in local for t in person_identity_tokens(candidate))


def parse_response_json(text):
    text = re.sub(r'^```(?:json)?\s*|\s*```$','',str(text or '').strip(),flags=re.I)
    try:
        obj = json.loads(text)
    except ValueError:
        start = text.find('{')
        if start < 0:
            raise ValueError('Azure response is not JSON')
        obj,_ = json.JSONDecoder().raw_decode(text[start:])
    if not isinstance(obj,dict):
        raise ValueError('Azure response must be a JSON object')
    return obj


def get_web_sources(response):
    urls,called = set(),False
    for item in getattr(response,'output',[]) or []:
        data = item.model_dump() if hasattr(item,'model_dump') else item if isinstance(item,dict) else {}
        if data.get('type')!='web_search_call':
            continue
        called = True
        for source in (data.get('action') or {}).get('sources') or []:
            url = source.get('url') if isinstance(source,dict) else None
            if isinstance(url,str) and safe_url(url):
                urls.add(url)
    return urls,called


def search_prompt(c):
    urls = '\n'.join('  - '+x for x in c['sources'][:8]) or '  none supplied'
    return f'''Use PUBLIC WEB SEARCH to audit the contact details for EXACTLY ONE CAD professional.
Name: {c['name']}
Individual's profile URL (may be GitHub/GitLab/Habr): {c['profile'] or 'none'}
Platform: {c['platform']}
Existing contact-cell value: {c['old'] or 'empty'}
Existing email claimed by spreadsheet: {c['existing_email'] or 'none'}
Existing LinkedIn claimed by spreadsheet: {c['existing_linkedin'] or 'none'}
CAD project/repository URL (PROJECT EVIDENCE ONLY; its OWNER might be a different person): {c['project'] or 'none'}
Other public URLs from the same row:\n{urls}

Search for the candidate's PUBLIC PROFESSIONAL email and/or personal LinkedIn profile.
Verify the existing email too when one was supplied; do not merely repeat it.
On GitHub/GitLab, check the specific user's public profile, linked portfolio,
user bio and associated personal pages. Do not assign the repository owner's
or another contributor's email to this candidate. On university team pages,
match precisely the person's own name/card and its email.
NEVER guess an email pattern, scrape private login-only pages, or report a
shared office/department email as an individual's personal address.

Return only JSON:
{{"email":"", "email_source":"", "email_evidence":"", "email_is_person_specific":false,
  "email_confidence":"low|medium|high", "existing_email_verified":false,
  "linkedin":"", "linkedin_source":"", "linkedin_evidence":"",
  "linkedin_is_person_specific":false, "reason":""}}
For a discovered email: email_source MUST be an exact searched URL, and
email_evidence MUST be a short contiguous verbatim excerpt (<=250 chars)
containing both the candidate's surname/unique handle and email IN THE SAME
person-specific passage. Mark email_is_person_specific only when explicit.
For LinkedIn: provide an exact /in/ or /pub/ URL tied to this person, a searched
source URL and a short passage identifying the candidate. If uncertain leave blank.
Set existing_email_verified=true only if it is explicitly associated with THIS
exact person in the publicly searched page. Do not invent sources or evidence.'''


def verify_prompt(c,found):
    return f'''Independently search the PUBLIC WEB for evidence linking this EXACT person to this email.
Candidate: {c['name']}
Person profile: {c['profile']}
Candidate's suspected email: {found['email']}
Suspected source: {found['email_source']}
This is a validation step. Do not assume prior claims are accurate. Do not confuse
candidate with a project owner, colleagues on university staff lists, or a
shared university office inbox. Check person-specific source and report uncertain
when no strong proof. Return only JSON:
{{"verified":false,"email":"","source_url":"","evidence_text":"","reason":""}}
For verified=true: exact email, searched source URL, and short verbatim excerpt
with the surname/unique handle AND email in the same named contact entry.'''


class Budget:
    def __init__(self,cap,minimum,maximum):
        self.cap,self.used = cap,0
        self.minimum,self.maximum = minimum,maximum
        self.lock = threading.Lock()
        self.next_at = 0.

    def reserve(self):
        with self.lock:
            if self.used >= self.cap:
                return False
            self.used += 1
            target = max(time.monotonic(),self.next_at)
            self.next_at = target + random.uniform(self.minimum,self.maximum)
        delay = target-time.monotonic()
        if delay > 0:
            time.sleep(delay)
        return True


class AzureAudit:
    def __init__(self,client,model,budget):
        self.client,self.model,self.budget = client,model,budget
        self.local = threading.local()

    def ask(self,prompt):
        for attempt in range(3):
            if not self.budget.reserve():
                return None,'budget_exhausted'
            self.local.calls = getattr(self.local,'calls',0)+1
            try:
                response = self.client.responses.create(
                    model=self.model,tools=[{'type':'web_search'}],
                    include=['web_search_call.action.sources'],input=prompt)
                sources,called = get_web_sources(response)
                if not called:
                    return None,'no_web_search'
                return (parse_response_json(getattr(response,'output_text','')),sources),'ok'
            except Exception as exc:
                code = getattr(exc,'status_code',None)
                msg = str(exc).lower()
                transient = code in (429,500,502,503,504) or any(
                    term in msg for term in ('rate limit','timeout','timed out','connection error'))
                if not transient or attempt==2:
                    return None,('throttled: ' if transient else 'api_error: ')+str(exc)[:180]
                headers = getattr(getattr(exc,'response',None),'headers',{}) or {}
                after = headers.get('retry-after','')
                try:
                    wait = float(after) if after else 0.
                except (TypeError,ValueError):
                    try:
                        wait = (parsedate_to_datetime(after)-datetime.now(timezone.utc)).total_seconds()
                    except (TypeError,ValueError):
                        wait = 0.
                delay = min(180,max(15,wait,15*2**attempt)+random.uniform(1,3))
                print(f'  [azure throttled] retry in {delay:.0f}s',flush=True)
                time.sleep(delay)
        return None,'failed'

    def audit(self,c):
        self.local.calls = 0
        empty = dict(status='not_found',verified_existing_email=False,
                     email='',email_source='',email_evidence='',linkedin='',
                     linkedin_source='',linkedin_evidence='',reason='',api_calls=0)
        response,status = self.ask(search_prompt(c))
        if response is None:
            empty.update(status=status,reason=status,api_calls=self.local.calls)
            return empty
        data,sources = response
        found_email = valid_email(data.get('email',''))
        email_source = str(data.get('email_source') or '').strip()
        email_excerpt = str(data.get('email_evidence') or '').strip()[:250]
        email_verified = bool(found_email and data.get('email_confidence')=='high' and
            data.get('email_is_person_specific') is True and
            source_supported(email_source,sources) and
            email_evidence_specific(c,found_email,email_excerpt))
        existing_verified = bool(email_verified and found_email==c['existing_email'] and
                                 data.get('existing_email_verified') is True)
        found_li = linkedin_in(data.get('linkedin',''))
        li_source = str(data.get('linkedin_source') or '').strip()
        li_evidence = str(data.get('linkedin_evidence') or '').strip()[:250]
        li_verified = bool(found_li and data.get('linkedin_is_person_specific') is True and
                source_supported(li_source,sources) and
                linkedin_evidence_specific(c,li_evidence))
        if email_verified and not surname_in_email(c,found_email):
            second,second_status = self.ask(verify_prompt(c,dict(email=found_email,email_source=email_source)))
            if second is None:
                email_verified = False
            else:
                check,check_sources = second
                email_verified = bool(check.get('verified') is True and
                    valid_email(check.get('email','')) == found_email and
                    source_supported(str(check.get('source_url','')),check_sources) and
                    email_evidence_specific(c,found_email,str(check.get('evidence_text',''))))
                if email_verified:
                    email_source = str(check['source_url'])
                    email_excerpt = str(check['evidence_text'])[:250]
            existing_verified = bool(existing_verified and email_verified)
        ret = dict(empty)
        ret.update(verified_existing_email=existing_verified,
                   email=found_email if email_verified else '',
                   email_source=email_source if email_verified else '',
                   email_evidence=email_excerpt if email_verified else '',
                   linkedin=found_li if li_verified else '',
                   linkedin_source=li_source if li_verified else '',
                   linkedin_evidence=li_evidence if li_verified else '',
                   api_calls=self.local.calls)
        if existing_verified:
            ret['status'] = 'existing_email_verified'
        elif email_verified:
            ret['status'] = 'new_email_verified'
        elif li_verified:
            ret['status'] = 'linkedin_verified'
        elif c['existing_email']:
            ret['status'] = 'existing_email_unverified'
        elif c['existing_linkedin']:
            ret['status'] = 'existing_linkedin_unverified'
        elif found_email or found_li:
            ret['status'] = 'needs_review'
        else:
            ret['status'] = 'not_found'
        ret['reason'] = str(data.get('reason') or '').strip()[:260]
        if found_email and not email_verified:
            ret['reason'] = ('Candidate email not independently confirmed: '+ret['reason'])[:260]
        return ret


def init_cache(path):
    db = sqlite3.connect(path)
    db.execute('PRAGMA journal_mode=WAL')
    db.execute('''CREATE TABLE IF NOT EXISTS audit_v2 (
        key TEXT PRIMARY KEY, name TEXT, profile TEXT, status TEXT,
        result_json TEXT, updated_utc TEXT)''')
    db.commit()
    return db


def cache_get(db,c):
    row = db.execute('SELECT result_json FROM audit_v2 WHERE key=?',(key_for(c),)).fetchone()
    try:
        return json.loads(row[0]) if row else None
    except (ValueError,TypeError):
        return None


def cache_put(db,c,result):
    db.execute('''INSERT INTO audit_v2 (key,name,profile,status,result_json,updated_utc)
        VALUES (?,?,?,?,?,?) ON CONFLICT(key) DO UPDATE SET
        status=excluded.status,result_json=excluded.result_json,
        updated_utc=excluded.updated_utc''',
        (key_for(c),c['name'],c['profile'],result['status'],json.dumps(result,ensure_ascii=False),utc_now()))
    db.commit()


def choose_contact(c,result,replace_existing_email=False):
    """Return value to place in D, never erase an existing contact."""
    existing = c['old']
    email = result.get('email','')
    link = result.get('linkedin','')
    if email:
        if c['existing_email'] and not replace_existing_email:
            return existing
        return email
    if link and not c['existing_email']:
        # Link to actual LinkedIn profile outranks generic site/GitHub/Telegram.
        if linkedin_in(existing):
            return existing
        return link
    return existing


def save_checkpoint(inp,out,metadata,people,db,replace_existing_email):
    audit,patches = [],[]
    statuses = Counter()
    for c in people:
        res = cache_get(db,c) or dict(status='not_run',verified_existing_email=False,
            email='',linkedin='',email_source='',linkedin_source='',email_evidence='',
            linkedin_evidence='',reason='',api_calls=0)
        statuses[res['status']] += 1
        new = choose_contact(c,res,replace_existing_email)
        record = dict(sheet=c['sheet'],row=c['row'],name=c['name'],
            profile_url=c['profile'],project_url=c['project'],contact_cell=c['cell'],
            original_contact=c['old'],existing_email=c['existing_email'],
            existing_linkedin=c['existing_linkedin'],status=res['status'],
            verified_existing_email=res.get('verified_existing_email',False),
            found_email=res.get('email',''),found_linkedin=res.get('linkedin',''),
            written_contact=new,email_source=res.get('email_source',''),
            linkedin_source=res.get('linkedin_source',''),
            email_evidence=res.get('email_evidence',''),
            linkedin_evidence=res.get('linkedin_evidence',''),
            reason=res.get('reason',''),api_calls=res.get('api_calls',0),updated_utc=utc_now())
        audit.append(record)
        if new != c['old']:
            patches.append({'path':c['path'],'cell':c['cell'],'written_contact':new})
    patch_xlsx(inp,out,metadata,patches)
    audit_path = out.with_name(out.stem+'_audit.csv')
    with audit_path.open('w',encoding='utf-8-sig',newline='') as fh:
        writer = csv.DictWriter(fh,fieldnames=AUDIT_HEADERS)
        writer.writeheader()
        writer.writerows(audit)
    return len(patches),statuses,audit_path


def main():
    ap = argparse.ArgumentParser(description='Azure audit of all CAD candidate rows; GitHub, GitLab, profile URLs included')
    ap.add_argument('--input',required=True,help='Original styled XLSX')
    ap.add_argument('--out',default='',help='New XLSX (must differ from input)')
    ap.add_argument('--state',default='',help='SQLite resume cache')
    ap.add_argument('--workers',type=int,default=3)
    ap.add_argument('--max-api-calls',type=int,default=2000,help='Hard cap per run, includes verification and retries')
    ap.add_argument('--checkpoint-every',type=int,default=50)
    ap.add_argument('--pause-min',type=float,default=2.0)
    ap.add_argument('--pause-max',type=float,default=5.0)
    ap.add_argument('--limit',type=int,default=0,help='0=all candidates; N=test first N')
    ap.add_argument('--sheets',default='',help='Comma-separated sheet names, empty=all candidate sheets')
    ap.add_argument('--refresh',action='store_true',help='Recheck cached candidate rows')
    ap.add_argument('--replace-existing-emails',action='store_true',
                    help='Overwrite an existing email ONLY with independently verified new email')
    args = ap.parse_args()
    inp = Path(args.input)
    out = Path(args.out) if args.out else inp.with_name(inp.stem+'_full_contact_audit.xlsx')
    state = Path(args.state) if args.state else inp.with_name(inp.stem+'_full_contact_audit_v2.sqlite3')
    if not inp.is_file():
        ap.error('File not found: '+str(inp))
    if inp.resolve()==out.resolve():
        ap.error('Input and output must be different')
    if args.workers < 1 or args.max_api_calls < 1 or args.checkpoint_every < 1 or args.limit < 0 or args.pause_min < 0 or args.pause_max < args.pause_min:
        ap.error('Invalid numeric arguments')
    sheets = {s.strip().casefold() for s in args.sheets.split(',') if s.strip()} or None
    with ZipFile(inp) as z:
        people,metadata = collect_candidates(z,sheets)
    if args.limit:
        people = people[:args.limit]
    if not people:
        ap.error('No candidate rows found; check --sheets and Excel column headers')
    types = Counter('email' if c['existing_email'] else 'linkedin' if c['existing_linkedin'] else 'missing' for c in people)
    print(f'[scan] {len(people)} candidate rows / {len(metadata)} candidate sheets; '
          f'existing_email={types["email"]}, linkedin_only={types["linkedin"]}, other_or_empty={types["missing"]}',flush=True)
    env = {key:os.getenv(key,'').strip() for key in
           ('AZURE_OPENAI_ENDPOINT','AZURE_OPENAI_DEPLOYMENT','AZURE_OPENAI_API_KEY')}
    if not all(env.values()):
        ap.error('Set AZURE_OPENAI_ENDPOINT, AZURE_OPENAI_DEPLOYMENT, AZURE_OPENAI_API_KEY')
    try:
        from openai import OpenAI
    except ImportError:
        ap.error('Missing package: python -m pip install -U openai')
    endpoint = env['AZURE_OPENAI_ENDPOINT'].rstrip('/')
    if not endpoint.endswith('/openai/v1'):
        endpoint += '/openai/v1'
    client = OpenAI(base_url=endpoint+'/',api_key=env['AZURE_OPENAI_API_KEY'],timeout=180,max_retries=0)
    worker = AzureAudit(client,env['AZURE_OPENAI_DEPLOYMENT'],Budget(args.max_api_calls,args.pause_min,args.pause_max))
    db = init_cache(state)
    try:
        unique = {}
        for c in people:
            unique.setdefault(key_for(c),c)
        retry_statuses = ('budget_exhausted','no_web_search','api_error','throttled','error','failed')
        todo = [c for c in unique.values() if args.refresh or cache_get(db,c) is None or
                any(str((cache_get(db,c) or {}).get('status','')).startswith(s) for s in retry_statuses)]
        print(f'[azure] {len(todo)} uncached unique candidate audits; API cap={args.max_api_calls}; workers={args.workers}',flush=True)
        completed=0
        # Batches ensure we stop gracefully when the API budget is depleted.
        batch_size = max(args.workers, min(args.checkpoint_every,args.workers*5))
        for start in range(0,len(todo),batch_size):
            if worker.budget.used >= worker.budget.cap:
                break
            subset = todo[start:start+batch_size]
            with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
                futures = {pool.submit(worker.audit,c):c for c in subset}
                for fut in concurrent.futures.as_completed(futures):
                    c = futures[fut]
                    try:
                        result = fut.result()
                    except Exception as exc:
                        result = dict(status='error',email='',linkedin='',
                                      reason=str(exc)[:200],api_calls=0)
                    if result.get('status') != 'budget_exhausted':
                        cache_put(db,c,result)
                    completed += 1
                    print(f'[{completed}/{len(todo)}] {c["sheet"]}!{c["cell"]} '
                          f'{c["name"][:35]} => {result["status"]}'
                          +(f' {result["email"]}' if result.get('email') else ''),flush=True)
                    if completed%args.checkpoint_every == 0:
                        n,counts,audit_path=save_checkpoint(inp,out,metadata,people,db,args.replace_existing_emails)
                        print(f'[checkpoint] updated_cells={n}, Azure_calls={worker.budget.used}/{worker.budget.cap}, '
                              f'remaining={len(todo)-completed}',flush=True)
        n,counts,audit_path=save_checkpoint(inp,out,metadata,people,db,args.replace_existing_emails)
        print(f'[done] rows={len(people)}, updated_cells={n}, Azure_calls={worker.budget.used}/{worker.budget.cap}; '
              f'by_status={dict(counts)}; output={out}; audit={audit_path}; cache={state}',flush=True)
    except KeyboardInterrupt:
        n,counts,audit_path=save_checkpoint(inp,out,metadata,people,db,args.replace_existing_emails)
        print(f'\n[stopped] saved {out}; updated_cells={n}',flush=True)
        raise SystemExit(130)
    finally:
        db.close()


if __name__=='__main__':
    main()
