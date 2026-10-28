#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""Maps-first + Azure verification of China CAD design firms (optional browser Maps research).

Python >= 3.10. Dependencies: pip install -U openai lxml

Search sources: Amap/Baidu official Places API (keys), optional OSM and CSV/XLSX import.
Azure OpenAI Responses API web_search (Bing grounding) verifies unresolved businesses.
Checks that official websites actually open before retaining firms in Excel, with
SQLite-cached HTTP results, excluded-sites CSV, and optional site-check workers.
Does not scrape Bing SERPs, bypass CAPTCHAs, or invent URLs.

The original 5-sheet XLSX is used as an immutable template. Exports four useful
sheets (Companies, Qualified Leads, Review, Stats), removes redundant tabs and
eight low-value columns while retaining remaining formatting and hyperlinks.
Persistent SQLite state and a CSV audit allow safe restart and review.
"""
import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import csv
import hashlib
import json
import copy
import subprocess
import os
import random
import re
import sqlite3
import sys
import time
import unicodedata
from collections import Counter
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import urlsplit, urlunsplit, urljoin, urlencode
from urllib.request import Request, urlopen, build_opener, HTTPRedirectHandler
from urllib.error import HTTPError, URLError
import socket
import ipaddress
from urllib.robotparser import RobotFileParser
from lxml import html as LHTML
from zipfile import ZipFile

from lxml import etree as ET

S = 'http://schemas.openxmlformats.org/spreadsheetml/2006/main'
R = 'http://schemas.openxmlformats.org/officeDocument/2006/relationships'
P = 'http://schemas.openxmlformats.org/package/2006/relationships'
MARKET_DOMAINS = ('zbj.com','made-in-china.com','alibaba.com','1688.com','qcc.com',
                  'tianyancha.com','aiqicha.baidu.com','baidu.com','sogou.com',
                  'b2b168.com','yellowpages.com','so.com','douyin.com',
                  'zhihu.com','linkedin.com','facebook.com')
LEGAL_SUFFIX = ('有限公司','有限责任公司','股份有限公司',' Co.,',' Co.',' Ltd',' Limited',' Inc.')
EMAIL_RX = re.compile(r'^[^\s@]+@[^\s@]+\.[^\s@]+$')
PHONE_RX = re.compile(r'^[+()\d.\- \u3000]{6,32}$')
VERSION = '5.11'
_FORM_CACHE = {}

# Use targeted regional and technical queries. Do not translate company names.
REGIONS = [
    '上海','北京','深圳','广州','东莞','苏州','杭州','宁波','南京','天津','武汉','成都',
    '重庆','佛山','无锡','常州','青岛','济南','西安','合肥','厦门','中山','惠州','郑州',
    '长沙','沈阳','大连','昆山','嘉兴','南通','温州','绍兴','福州','台州',
]
TOPICS = [
    ('parametric', '参数化三维建模 SolidWorks 工业设计公司 官网 联系方式'),
    ('assemblies', '机械装配体 三维CAD 非标机械设计公司 官网 联系我们'),
    ('machinery', '机械设计外包 非标自动化 机械设计公司 联系邮箱'),
    ('product', '产品结构设计 工业产品设计 3D CAD 企业 官网'),
    ('cad-engineering', '工程设计 Creo NX SolidWorks 建模 外包 公司'),
    ('industrial', '工业设计 产品研发 样机建模 结构设计 企业 邮箱 电话'),
    ('sheetmetal', '钣金设计 工装夹具 三维装配 机械设计 公司'),
    ('robotics', '机器人自动化设备 三维机械设计 外包 公司'),
]
NATIONAL = [
    '中国 机械结构设计 公司 SolidWorks 三维模型 官网 联系方式',
    '中国 3D CAD 参数化建模 装配设计 服务商 企业官网 邮箱',
    '机械设计公司 客户项目 三维CAD装配体 电话 联系我们',
    'SolidWorks 外包设计公司 中国 联系我们 技术支持',
    'Creo NX CATIA 参数化建模 工程设计服务 企业邮箱',
    '非标自动化 机械设计外包 企业 三维结构设计 工厂',
    '机电一体化 自动化设备设计 CAD模型 项目 公司 联系方式',
    '工业产品结构设计 三维装配 图纸 设计服务 公司 联系人',
]

DISCOVER_SCHEMA = {
    'type': 'object','additionalProperties': False,
    'properties': {
        'companies': {'type':'array', 'items': {'type':'object','additionalProperties':False,
            'properties':{
                'name':{'type':'string'},'city':{'type':'string'},
                'official_site':{'type':'string'},'company_source_url':{'type':'string'},
                'services':{'type':'string'},'cad_types':{'type':'string'},
                'cad_software':{'type':'string'}, 'email':{'type':'string'},
                'phone':{'type':'string'}, 'contact_page':{'type':'string'},
                'contact_form_url':{'type':'string'}, 'contact_source_url':{'type':'string'},
                'reason':{'type':'string'},
            },'required':['name','city','official_site','company_source_url','services',
                          'cad_types','cad_software','email','phone','contact_page',
                          'contact_form_url','contact_source_url','reason']}}
    },'required':['companies']
}
VERIFY_SCHEMA = {
    'type':'object','additionalProperties':False,
    'properties':{
        'status':{'type':'string','enum':['verified','candidate','not_found']},
        'matched_legal_name':{'type':'string'},'official_site':{'type':'string'},
        'identity_source_url':{'type':'string'},'second_source_url':{'type':'string'},
        'city':{'type':'string'},'services':{'type':'string'},
        'cad_types':{'type':'string'},'cad_software':{'type':'string'},
        'email':{'type':'string'},'phone':{'type':'string'},
        'contact_page':{'type':'string'},'contact_form_url':{'type':'string'},
        'has_contact_form':{'type':'boolean'},'contact_source_url':{'type':'string'},
        'confidence':{'type':'string','enum':['high','medium','low']},
        'identity_on_official_site':{'type':'boolean'},
        'cad_services_explicit':{'type':'boolean'},
        'rationale':{'type':'string'},
    },'required':['status','matched_legal_name','official_site','identity_source_url',
                  'second_source_url','city','services','cad_types','cad_software',
                  'email','phone','contact_page','contact_form_url','has_contact_form','contact_source_url','confidence',
                  'identity_on_official_site','cad_services_explicit','rationale']
}


def norm_name(name):
    s=unicodedata.normalize('NFKC',str(name or '')).casefold()
    return re.sub(r'[\s\-–—_·.。,，()（）【】\[\]"“”]', '', s)


def clean_url(s):
    s=str(s or '').strip().rstrip('.,;，。')
    if not s.startswith(('https://','http://')):return ''
    try:
        u=urlsplit(s)
        host=(u.hostname or '').lower()
        if not host or '.' not in host or u.username or u.password:return ''
        if host in ('localhost','127.0.0.1','0.0.0.0') or host.endswith('.local'):return ''
        return urlunsplit((u.scheme,u.netloc,u.path or '/',u.query,''))
    except ValueError:return ''


def domain(u):
    u=clean_url(u)
    return (urlsplit(u).hostname or '').lower().removeprefix('www.') if u else ''


def marketplace(url):
    d=domain(url)
    return any(d==x or d.endswith('.'+x) for x in MARKET_DOMAINS)


def legal(name):
    s=str(name or '')
    return any(x in s for x in LEGAL_SUFFIX)


def good_contact(v, kind):
    v=str(v or '').strip()
    if kind=='email':return v if len(v)<255 and EMAIL_RX.fullmatch(v) else ''
    return v if PHONE_RX.fullmatch(v) else ''


def base_url(endpoint):
    endpoint=str(endpoint or '').strip().rstrip('/')
    u=urlsplit(endpoint)
    if u.scheme!='https' or not u.hostname or u.username or u.password or u.query:return ''
    if u.path.rstrip('/') not in ('','/openai/v1'):return ''
    return f'{u.scheme}://{u.netloc}/openai/v1/'


def web_info(resp):
    payload=resp.model_dump(exclude_none=True)
    calls=sum(1 for i in payload.get('output',[]) if i.get('type')=='web_search_call')
    sources=[]
    for item in payload.get('output',[]):
        if item.get('type')=='web_search_call':
            for obj in (item.get('action') or {}).get('sources') or []:
                if isinstance(obj,dict):sources.append(clean_url(obj.get('url')))
        if item.get('type')=='message':
            for part in item.get('content') or []:
                for ann in part.get('annotations') or []:
                    if ann.get('type')=='url_citation':sources.append(clean_url(ann.get('url')))
    # Different Azure API versions expose search billing data in different fields.
    tool_usage=payload.get('tool_usage') or {}
    if isinstance(tool_usage,dict):
        web=tool_usage.get('web_search') or {}
        billed=web.get('num_requests') if isinstance(web,dict) else None
    else:billed=None
    return calls,list(dict.fromkeys(x for x in sources if x)),billed


def in_sources(url, sources):
    u=clean_url(url)
    # Must have a URL from an actual web_search source with the same domain.
    return bool(u) and any(domain(u)==domain(s) for s in sources)


def exact_sourced_page(url, sources):
    """Check cited URL at page (not just domain) granularity."""
    def key(value):
        value=clean_url(value)
        if not value:return None
        p=urlsplit(value)
        return (domain(value),p.path.rstrip('/').lower() or '/',p.query)
    target=key(url)
    return bool(target) and any(key(s)==target for s in sources)


def verified_form_url(result):
    """Distinguish an actual confirmed HTML form from a generic contact page."""
    return (clean_url(result.get('contact_form_url')) if result.get('form_dom_verified') is True
            else '')


TECHNICAL_NAMES = {'null', 'none', 'open', 'unknown', 'undefined', 'nan', 'n/a', 'test', 'admin', 'null有限公司'}


def valid_company_name(name):
    """No platform placeholders or bare technical values in output leads."""
    n=norm_name(name)
    return bool(n and n not in TECHNICAL_NAMES and n not in ('-', '0')
                and len(n)>3 and legal(name))


def contactable(result):
    return bool(result.get('email') or result.get('phone') or verified_form_url(result))


def contact_method(result):
    direct=bool(result.get('email') or result.get('phone'))
    form=bool(verified_form_url(result))
    if direct and form:return 'Email/phone + web form'
    if direct:return 'Email/phone'
    if form:return 'Web form'
    return 'No confirmed contact'


def contact_label(result):
    direct=bool(result.get('email') or result.get('phone'))
    form=bool(verified_form_url(result))
    if direct and form:return 'Ready to contact — email/phone or web form'
    if direct:return 'Ready to contact — email/phone'
    if form:return 'Ready to contact — official web form'
    return 'Official site verified — contact needs verification'


def _fetch_public_page(url, owning_domain, timeout=12):
    """Public same-domain HTML fetch; optional verification independent of model text.

    Failure is not proof of absent form. No access-control circumvention.
    """
    url=clean_url(url)
    if not url or marketplace(url) or domain(url)!=owning_domain:return None
    ua='ChinaCADResearch/2.0 (public business contact verification)'
    p=urlsplit(url)
    robots=f'{p.scheme}://{p.netloc}/robots.txt'
    rp=RobotFileParser();rp.set_url(robots)
    try:
        with urlopen(Request(robots,headers={'User-Agent':ua}),timeout=6) as rob:
            if int(rob.status)==200:
                lines=rob.read(100000).decode('utf-8','replace').splitlines()
                rp.parse(lines)
                if not rp.can_fetch(ua,url):return None
    except Exception:
        # No robots information available; only visit openly available pages.
        pass
    try:
        req=Request(url,headers={'User-Agent':ua,'Accept':'text/html,application/xhtml+xml'})
        with urlopen(req,timeout=timeout) as response:
            final=clean_url(response.url)
            if domain(final)!=owning_domain:return None
            mime=response.headers.get('Content-Type','').lower()
            if 'text/html' not in mime and 'application/xhtml+xml' not in mime:return None
            raw=response.read(400001)
            if len(raw)>400000:return None
        return final,LHTML.fromstring(raw,base_url=final)
    except Exception:return None


def _is_real_contact_form(root):
    """Requires actual editable enquiry fields and a submit control (not a search form)."""
    for form in root.xpath('//form'):
        if form.xpath('.//input[translate(@type,"ABCDEFGHIJKLMNOPQRSTUVWXYZ","abcdefghijklmnopqrstuvwxyz")="search"]'):
            continue
        fields=form.xpath('.//textarea | .//input[not(@type) or '
                          'translate(@type,"ABCDEFGHIJKLMNOPQRSTUVWXYZ","abcdefghijklmnopqrstuvwxyz")="text" or '
                          'translate(@type,"ABCDEFGHIJKLMNOPQRSTUVWXYZ","abcdefghijklmnopqrstuvwxyz")="email" or '
                          'translate(@type,"ABCDEFGHIJKLMNOPQRSTUVWXYZ","abcdefghijklmnopqrstuvwxyz")="tel"]')
        if not fields:continue
        names=' '.join((e.get('name','')+' '+e.get('placeholder','')).lower() for e in fields)
        if names.strip() in ('q','query','search','keyword','keywords') or ('search' in names and len(fields)==1):
            continue
        submit=form.xpath('.//button[not(@type) or @type="submit"] | .//input[@type="submit"]')
        if not submit:continue
        # A single newsletter subscription is not a customer enquiry form.
        if len(fields)==1 and 'email' in names and 'newsletter' in LHTML.tostring(form,encoding='unicode').lower():
            continue
        return True
    return False


def confirm_contact_form(site, suggested='', contact_page='', fetcher=None, limit=4, pause=(2.0,5.0)):
    """Resolve real own-domain form URL by inspecting HTML, including linked contact pages.

    A model's 'has_contact_form' assertion alone NEVER qualifies. Fail closed.
    """
    site=clean_url(site); owner=domain(site)
    if not owner:return ''
    fetcher=fetcher or _fetch_public_page
    checked=set(); queue=[]
    for item in (suggested,contact_page,site):
        u=clean_url(item)
        if u and domain(u)==owner and u not in queue:queue.append(u)
    while queue and len(checked)<limit:
        u=queue.pop(0)
        if u in checked:continue
        checked.add(u)
        cached=_FORM_CACHE.get(u)
        if cached is None:
            if pause[1] and fetcher is _fetch_public_page:
                time.sleep(random.uniform(*pause))
            value=fetcher(u,owner)
            _FORM_CACHE[u]=value if value is not None else False
        else:value=cached if cached is not False else None
        if value is None:continue
        final, root=value
        if domain(final)!=owner:continue
        if _is_real_contact_form(root):return final
        for link in root.xpath('//a[@href]'):
            label=' '.join(link.itertext()).lower()+' '+link.get('href','').lower()
            if not any(k in label for k in ('contact','联系','咨询','留言','询价','反馈','enquir','inquiry')):
                continue
            nxt=clean_url(urljoin(final,link.get('href','')))
            if nxt and domain(nxt)==owner and nxt not in checked and nxt not in queue:
                queue.append(nxt)
    return ''


def tool_json(client,model,prompt,schema,name,effort):
    request={
        'model':model,'store':False,
        'tools':[{'type':'web_search','search_context_size':'medium'}],
        'tool_choice':'auto','include':['web_search_call.action.sources'],
        'input':prompt,'text':{'format':{'type':'json_schema','name':name,
                                         'strict':True,'schema':schema}},
    }
    if effort:request['reasoning']={'effort':effort}
    res=client.responses.create(**request)
    calls,sources,billed=web_info(res)
    if calls<=0:raise RuntimeError('Azure response did not call web_search; refusing unsourced company data')
    data=json.loads(res.output_text or '{}')
    if not isinstance(data,dict):raise RuntimeError('Non-object JSON result')
    return data,sources,calls,billed


def discover(client,model,query,effort):
    prompt=f'''You are building a business-to-business list of CHINESE CAD DESIGN SERVICE FIRMS.
Search the public web NOW for this targeted sector query:
{query}
Find up to 8 DISTINCT real firms, not freelancers, personal shops, schools, software products,
retail stores, or directory websites. Prefer companies that create PARAMETRIC 3D CAD models,
3D MECHANICAL ASSEMBLIES, SolidWorks/Creo/NX/CATIA, nonstandard automation machinery.
For each firm, collect the EXACT legal Chinese company name (有限公司/有限责任公司 etc),
city, engineering services, CAD type, actual official site, corporate email,
company phone or real official-site contact form. A contact form is sufficient.
Provide EXACT contact_form_url when actual input fields and submission exist (not a bare
Contact Us address page), plus identity and contact evidence URLs.
Search across more than one source. Distinguish directories from the company's own site.
Leave uncertain fields blank, never fabricate domains or email addresses.
The official website must display/identify the specific company; never label a marketplace
store page as its corporate website. Return 0 companies if no good sourced firm is found.
Return ONLY JSON matching the schema.'''
    data,sources,calls,billed=tool_json(client,model,prompt,DISCOVER_SCHEMA,'cad_discover',effort)
    picked=[]
    for x in data.get('companies') or []:
        if not isinstance(x,dict):continue
        n=str(x.get('name','')).strip()
        if not legal(n):continue
        site=clean_url(x.get('official_site'))
        source=clean_url(x.get('company_source_url'))
        contact=clean_url(x.get('contact_source_url'))
        # Discovery is hints ONLY. The subsequent independent verification call
        # decides whether to modify an XLSX row.
        picked.append({
            'name':n,'city':str(x.get('city',''))[:100],
            'official_site_hint':site if site and not marketplace(site) and in_sources(site,sources) else '',
            'discovery_source':source if in_sources(source,sources) else '',
            'services':str(x.get('services',''))[:600],
            'cad_types':str(x.get('cad_types',''))[:180],
            'cad_software':str(x.get('cad_software',''))[:200],
            'email_hint':good_contact(x.get('email'),'email') if contact and in_sources(contact,sources) else '',
            'phone_hint':good_contact(x.get('phone'),'phone') if contact and in_sources(contact,sources) else '',
            'contact_hint':clean_url(x.get('contact_page')) if contact and in_sources(contact,sources) else '',
            'contact_form_hint':clean_url(x.get('contact_form_url')) if exact_sourced_page(x.get('contact_form_url'),sources) else '',
            'origin_query':query,
        })
    return picked,calls,billed,len(sources)


def verify(client,model,firm,effort):
    prompt=f'''Verify a SPECIFIC China-based industrial CAD/3D mechanical design SERVICE COMPANY.
Original legal/company name: {firm['name']}
Reported city: {firm.get('city') or 'unknown'}
CAD services: {firm.get('services','')[:400]}
Candidate official domain (UNVERIFIED): {firm.get('official_site_hint','')}
Candidate discovery listing (NOT evidence of site ownership): {firm.get('discovery_source','')}
Original directory profile URL (use to disambiguate legal name, NOT as official domain): {firm.get('directory_url','')}
Candidate contact form hint (UNVERIFIED): {firm.get('contact_form_hint','')}
Find its REAL own official website, using fresh web searches with the exact CHINESE name,
公司官网/官方网站/联系我们/邮箱/电话 and geographic and engineering context.
Only VERIFIED if the official website itself names the EXACT SAME legal company and clearly
provides industrial product / mechanical / parametric 3D / CAD design services.
If its legal name is different, return candidate. Prefer an independent reference as corroboration.
Set identity_on_official_site only if EXACT legal company name is visible on own corporate site.
Set cad_services_explicit only if the site explicitly offers paid design/engineering services,
not just product manufacturing, software, or general 3D printing.
Source fields must be REAL clicked/searched URLs visible to web_search.
Capture publicly published CORPORATE email, company phone OR an official enquiry form.
Contact forms are equally acceptable. has_contact_form=true ONLY if you see editable
name/email/message fields and a submission control, not merely a Contact Us page.
Supply the exact actual page URL as contact_form_url. A separate HTML verification
will independently check the page. contact_source_url must identify contact evidence.
Do not collect unrelated individuals' private contact details.
If there is no verifiable site, report candidate or not_found; never invent a plausible domain.
One company per response; JSON only.'''
    data,sources,calls,billed=tool_json(client,model,prompt,VERIFY_SCHEMA,'cad_verify',effort)
    site=clean_url(data.get('official_site'))
    identity=clean_url(data.get('identity_source_url'))
    contact_source=clean_url(data.get('contact_source_url'))
    matched=norm_name(data.get('matched_legal_name'))==norm_name(firm['name'])
    valid=(data.get('status')=='verified' and data.get('confidence')=='high' and
           legal(firm['name']) and matched and data.get('identity_on_official_site') is True
           and data.get('cad_services_explicit') is True and site and not marketplace(site) and
           in_sources(site,sources) and in_sources(identity,sources) and
           domain(identity)==domain(site))
    contacts_ok=valid and in_sources(contact_source,sources) and domain(contact_source)==domain(site)
    suggested_form=clean_url(data.get('contact_form_url'))
    form_url=''
    if valid and data.get('has_contact_form') is True:
        # Candidate form URLs must be cited at page granularity; also discover linked
        # real contact page if the model mistakenly supplied the homepage.
        candidate=suggested_form if exact_sourced_page(suggested_form,sources) else ''
        form_url=confirm_contact_form(site,candidate,clean_url(data.get('contact_page')))
    result={
        'name':firm['name'],'city':str(data.get('city') or firm.get('city',''))[:100],
        'status':'verified' if valid else ('candidate' if site else 'not_found'),
        'official_site':site if site and not marketplace(site) else '',
        'identity_url':identity if in_sources(identity,sources) else '',
        'second_source_url':clean_url(data.get('second_source_url')),
        'services':str(data.get('services') or firm.get('services',''))[:800],
        'cad_types':str(data.get('cad_types') or firm.get('cad_types',''))[:200],
        'cad_software':str(data.get('cad_software') or firm.get('cad_software',''))[:200],
        'email':good_contact(data.get('email'),'email') if contacts_ok else '',
        'phone':good_contact(data.get('phone'),'phone') if contacts_ok else '',
        'contact_page':form_url if form_url else (clean_url(data.get('contact_page')) if contacts_ok else ''),
        'contact_form_url':form_url,'form_dom_verified':bool(form_url),
        'contact_form_checked':True,
        'contact_source_url':form_url if form_url else (contact_source if contacts_ok else ''),
        'unverified_email':good_contact(data.get('email'),'email') if not contacts_ok and site and in_sources(contact_source,sources) and domain(contact_source)==domain(site) else '',
        'unverified_phone':good_contact(data.get('phone'),'phone') if not contacts_ok and site and in_sources(contact_source,sources) and domain(contact_source)==domain(site) else '',
        'unverified_contact_page':clean_url(data.get('contact_page')) if not contacts_ok and site and domain(data.get('contact_page'))==domain(site) else '',
        'unverified_contact_form_url':suggested_form if not valid and site and domain(suggested_form)==domain(site) else '',
        'confidence':data.get('confidence','low'),
        'reason':str(data.get('rationale',''))[:500],
        'search_events':calls,'source_count':len(sources),'billed_search_requests':billed,
        'checked_utc':datetime.now(timezone.utc).isoformat(),
        'origin_query':firm.get('origin_query',''),
    }
    if data.get('status')=='verified' and not valid:
        result['reason']='Verification rejected (name, source or domain mismatch): '+result['reason']
    return result



# Additional discovery queries are deliberately appended after the original 280.
# Existing SHA-256 query keys in the SQLite cache remain unchanged.
EXPANDED_DISCOVERY_TOPICS = [
    'SolidWorks 机械结构设计 服务 公司 官网',
    'SolidWorks 机械设计外包 企业 官网 邮箱',
    'SolidWorks 3D建模 装配设计 设计公司',
    'SolidWorks 非标机械设计 委托设计 公司',
    'SolidWorks 钣金件 展开设计 机械设计公司',
    'SolidWorks 工装夹具设计 研发公司 联系电话',
    'SolidWorks 运动仿真 机构设计 企业',
    'SolidWorks 逆向工程 三维重建 公司',
    'Creo 产品结构设计 外包 企业',
    'Creo 参数化建模 机械设计服务 公司',
    'Creo ProE 机构研发 图纸 公司',
    'CATIA 曲面设计 产品开发 企业',
    'CATIA 机械设计外包 工业设计公司',
    'NX UG 三维机械建模 设计服务 企业',
    'UG NX 模具设计 结构设计 公司 官网',
    'UG 非标自动化 设计外包 公司',
    'AutoCAD 机械工程图纸 设计公司',
    'Inventor 装配体设计 机械设计外包',
    'Fusion 360 产品设计 机械工程 公司',
    '工业设备 CAD建模 技术服务 公司 官网',
    '机械结构设计 研发外包 有限公司 官网',
    '非标设备 机械研发 设计公司 联系我们',
    '非标自动化 结构研发 设计咨询 公司',
    '自动化产线 机械设计 研发服务 企业',
    '工业机器人 末端执行器 结构设计 公司',
    '机器人夹爪 机械结构设计 企业',
    '机器人工作站 机械设计 工程服务 公司',
    '协作机器人 机械结构设计 服务商',
    '机械传动系统 设计开发 技术公司',
    '齿轮箱 机械结构设计 研发服务 公司',
    '减速机 传动设计 外包 公司',
    '机电一体化 机械设计 研发公司',
    '机床机械设计 定制设备 工程公司',
    '医疗器械 产品结构设计 设计公司',
    '消费电子 产品结构设计 工业设计公司',
    '汽车零部件 结构设计 工程服务公司',
    '航空航天 机械结构设计 设计服务公司',
    '新能源设备 机械结构设计 工程公司',
    '光伏设备 非标机械设计 技术公司',
    '半导体设备 精密机械设计 工程公司',
    '锂电设备 机械设计 研发外包 企业',
    '包装机械 结构设计 开发服务公司',
    '物流自动化 设备结构设计 公司',
    '自动分拣设备 机械研发 企业官网',
    '输送线 机械设计 工程服务 公司',
    '注塑产品 结构设计 设计公司',
    '塑胶件 产品结构设计 设计工作室 企业',
    '钣金结构 产品研发设计 公司 联系方式',
    '精密工装 夹具设计 机械工程公司',
    '治具 检具 结构设计 研发企业',
    '机械设备 外观结构 一体化设计 公司',
    '设备改造 机械设计 外包 服务商',
    '机械产品设计 3D装配 零件图 企业',
    '逆向设计 三维扫描 机械工程 公司',
    '三维扫描 CAD重建 工业设计公司',
    '三维数字化 参数化重构 设计服务企业',
    'DFM 可制造性设计 结构优化 企业',
    '产品研发 ODM 结构设计 公司官网',
    '样机开发 结构设计 三维建模 企业',
    '工业设计 创新设计 产品结构工程公司',
    '机械仿真 多体动力学 设计服务公司',
    '机械设计 CAD 外包技术服务 联系邮箱',
    '自动化夹具 机械装配设计 研发公司',
    '非标机构 气动机构 机械设计服务公司',
]

EXPANDED_DISCOVERY_NATIONAL = [
    '中国 SolidWorks 机械设计外包 公司 联系方式',
    '中国 工业CAD 机械设计 结构工程 服务企业',
    '国内 工业产品结构设计 研发外包 企业官网',
    '中国 非标设备 机械图纸 三维建模 设计公司',
    '工业设计 机械结构工程 设计服务 中国 企业',
    '中国 CAD机械装配设计 独立工程技术公司',
    '中国 医疗设备 产品结构设计 公司',
    '中国 机器人 机械结构设计 企业官网',
    '中国 NX UG 机械工程设计 服务商',
    '中国 CATIA Creo 结构设计工程 企业',
    '中国 自动化设备机械设计 工程咨询',
    '中国 汽车夹具 工装结构设计 公司',
    '中国 钣金机械结构设计 服务商',
    '中国 工业设备研发 机械结构设计外包',
    '中国 3D扫描 CAD逆向建模 企业',
    '中国 产品样机开发 机械结构设计 企业',
    '中国 工业机器人夹爪机构设计 公司',
    '中国 机械传动结构设计 工程外包',
    '中国 注塑产品 工程结构设计 服务公司',
    '中国 非标自动化产线 机械设计 服务企业',
]


def expanded_queries():
    base=[f'{r} {t}' for topic,t in TOPICS for r in REGIONS]
    original=NATIONAL+base
    additional=[f'{r} {t}' for t in EXPANDED_DISCOVERY_TOPICS for r in REGIONS]
    additional.extend(EXPANDED_DISCOVERY_NATIONAL)
    # Deterministic order and exact de-duplication; preserve original 280 first.
    return list(dict.fromkeys(original+additional))

def make_queries(custom=None, expanded=False):
    if custom:
        # One literal Chinese search query per line, comments supported.
        return [x.strip() for x in Path(custom).read_text(encoding='utf-8-sig').splitlines()
                if x.strip() and not x.lstrip().startswith('#')]
    # interleave regions and skill categories; early queries cover different cities
    queries=[f'{r} {t}' for topic,t in TOPICS for r in REGIONS]
    return expanded_queries() if expanded else NATIONAL+queries


def connect_db(path):
    path.parent.mkdir(parents=True,exist_ok=True)
    db=sqlite3.connect(path)
    db.row_factory=sqlite3.Row
    db.execute('PRAGMA journal_mode=WAL')
    db.executescript('''
        CREATE TABLE IF NOT EXISTS queries (
          key TEXT PRIMARY KEY, query TEXT NOT NULL, completed_at TEXT,
          search_events INTEGER NOT NULL DEFAULT 0, billed_requests INTEGER,
          candidates INTEGER NOT NULL DEFAULT 0);
        CREATE TABLE IF NOT EXISTS candidates (
          name_key TEXT PRIMARY KEY, data TEXT NOT NULL,
          verify_status TEXT NOT NULL DEFAULT 'pending', updated_at TEXT);
        CREATE TABLE IF NOT EXISTS results (
          name_key TEXT PRIMARY KEY, data TEXT NOT NULL, updated_at TEXT);
        CREATE TABLE IF NOT EXISTS events (
          id INTEGER PRIMARY KEY AUTOINCREMENT, time TEXT, operation TEXT,
          label TEXT, status TEXT, details TEXT);
        CREATE TABLE IF NOT EXISTS counters (name TEXT PRIMARY KEY, value INTEGER NOT NULL);
        CREATE TABLE IF NOT EXISTS verification_failures (name_key TEXT PRIMARY KEY, attempts INTEGER NOT NULL DEFAULT 0, last_error TEXT, updated_at TEXT);
    ''')
    db.commit();return db


# -------- Public official-site availability (no Azure calls) --------
# A failed HTTP probe is not evidence that the company does not exist: it only
# means its site cannot be independently opened at the time of checking.

def _site_public_url(url):
    """Reject invalid and nonpublic destinations, including redirect targets."""
    url=clean_url(url)
    if not url:return False
    parsed=urlsplit(url)
    host=(parsed.hostname or '').rstrip('.').lower()
    if not host or host.endswith(('.local','.internal','.test','.invalid','.localhost')):
        return False
    try:
        ip=ipaddress.ip_address(host)
        return ip.is_global
    except ValueError:
        pass
    try:
        addresses=socket.getaddrinfo(host,parsed.port or (443 if parsed.scheme=='https' else 80),type=socket.SOCK_STREAM)
        return bool(addresses) and all(ipaddress.ip_address(item[4][0]).is_global for item in addresses)
    except (socket.gaierror, ValueError, OSError):
        return False


class _PublicOnlyRedirects(HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl):
        if not _site_public_url(newurl):
            raise ValueError('Redirect blocked: private or invalid destination')
        return super().redirect_request(req,fp,code,msg,headers,newurl)


def probe_official_site(url, timeout=10.0):
    """Return independent site availability: live, inaccessible or invalid.

    At most two HTTP GETs (original scheme and alternate scheme). Follows
    public redirects, reads <= 16KiB, never downloads whole pages and never
    submits forms. CAPTCHA / 403 / 429 are *inaccessible*, not permanent death.
    """
    site=clean_url(url)
    if not site or marketplace(site):
        return {'status':'invalid','final_url':'','http_status':0,
                'details':'Missing official website or directory/marketplace link'}
    if not _site_public_url(site):
        return {'status':'inaccessible','final_url':'','http_status':0,
                'details':'No public DNS address / blocked nonpublic destination'}
    parsed=urlsplit(site)
    alternate=urlunsplit(('http' if parsed.scheme=='https' else 'https',parsed.netloc,
                          parsed.path,parsed.query,''))
    last={'status':'inaccessible','final_url':'','http_status':0,'details':'Connection failed'}
    opener=build_opener(_PublicOnlyRedirects())
    for candidate in dict.fromkeys((site,alternate)):
        if not _site_public_url(candidate):continue
        req=Request(candidate,headers={'User-Agent':'Mozilla/5.0 (compatible; PublicCompanyWebsiteCheck/1.0)',
                                       'Accept':'text/html,application/xhtml+xml;q=0.9,*/*;q=0.4',
                                       'Range':'bytes=0-16383'})
        try:
            with opener.open(req,timeout=timeout) as resp:
                final=clean_url(resp.geturl())
                if not final or marketplace(final) or not _site_public_url(final):
                    last={'status':'inaccessible','final_url':final,'http_status':resp.status,
                          'details':'Redirect ended outside a public corporate website'}
                    continue
                code=int(resp.status)
                content_type=(resp.headers.get('Content-Type') or '').lower()
                sample=resp.read(16384).lstrip().lower()
                htmlish=('html' in content_type or 'xhtml' in content_type or
                         sample.startswith((b'<!doctype html',b'<html',b'<?xml')) or b'<html' in sample[:1024])
                if 200 <= code < 400 and htmlish and sample:
                    return {'status':'live','final_url':final,'http_status':code,
                            'details':'Public HTML response'}
                last={'status':'inaccessible','final_url':final,'http_status':code,
                      'details':('Non-HTML response' if not htmlish else 'Empty or unexpected response')}
        except HTTPError as exc:
            last={'status':'inaccessible','final_url':candidate,'http_status':exc.code,
                  'details':f'HTTP {exc.code} (may be access restriction)'}
        except (URLError,TimeoutError,socket.timeout,ValueError,OSError) as exc:
            last={'status':'inaccessible','final_url':'','http_status':0,
                  'details':(type(exc).__name__+': '+str(exc))[:200]}
    return last


def init_site_checks(db):
    db.execute("""CREATE TABLE IF NOT EXISTS site_checks (
        url TEXT PRIMARY KEY, status TEXT NOT NULL, final_url TEXT,
        http_status INTEGER, details TEXT, checked_at TEXT, checked_unix REAL NOT NULL)""")
    db.commit()


def site_check_batch(db, urls, workers=8, timeout=10.0, cache_hours=24.0):
    """Check unique sites in parallel; serialize all SQLite updates."""
    init_site_checks(db)
    normalized={clean_url(u) for u in urls if clean_url(u)}
    cached={}
    now=time.time()
    for url in normalized:
        item=db.execute('SELECT * FROM site_checks WHERE url=?',(url,)).fetchone()
        if item and cache_hours>0 and now-float(item['checked_unix'])<cache_hours*3600:
            cached[url]=dict(item)
    pending=sorted(normalized-cached.keys())
    print(f'[site check] unique={len(normalized)} cached={len(cached)} new={len(pending)} '
          f'workers={workers}; timeout={timeout}s',flush=True)
    if pending:
        with ThreadPoolExecutor(max_workers=workers) as pool:
            jobs={pool.submit(probe_official_site,url,timeout):url for url in pending}
            for idx,fut in enumerate(as_completed(jobs),1):
                url=jobs[fut]
                try:result=fut.result()
                except Exception as exc:
                    result={'status':'inaccessible','final_url':'','http_status':0,
                            'details':f'Probe error: {type(exc).__name__}: {exc}'[:200]}
                record={'url':url,'status':result['status'],
                        'final_url':result.get('final_url',''),
                        'http_status':result.get('http_status',0),
                        'details':result.get('details','')[:300],
                        'checked_at':moment(),'checked_unix':time.time()}
                db.execute("""INSERT INTO site_checks(url,status,final_url,http_status,details,checked_at,checked_unix)
                  VALUES(:url,:status,:final_url,:http_status,:details,:checked_at,:checked_unix)
                  ON CONFLICT(url) DO UPDATE SET status=excluded.status,final_url=excluded.final_url,
                    http_status=excluded.http_status,details=excluded.details,
                    checked_at=excluded.checked_at,checked_unix=excluded.checked_unix""",record)
                cached[url]=record
                if idx%25==0 or idx==len(pending):
                    db.commit()
                    print(f'[site check] checked {idx}/{len(pending)}, '
                          f'live={sum(r["status"]=="live" for r in cached.values())}',flush=True)
    db.commit()
    return cached



# -------- Backfill public corporate email/phone from verified official sites --------
# Azure web_search discovers URLs; this stage reads those pages directly (no AI calls).
_EMAIL_IN_HTML=re.compile(r'(?i)(?<![a-z0-9._%+\-])([a-z0-9._%+\-]+@[a-z0-9.\-]+\.[a-z]{2,})(?![a-z0-9.\-])')
_CONTACT_PATHS=('/contact','/contact-us','/contact.html','/contactus','/lianxi','/lxwm','/about/contact')
_CONTACT_WORDS=('联系我们','联系我司','联系方式','联系电话','联系我们','联系','contact us','contact','get in touch')
_PHONE_LABEL=re.compile(r'(?i)(?:联系电话|咨询电话|公司电话|销售电话|服务电话|电话|tel(?:ephone)?|phone|hotline|传真|mobile|手机)\s*[:：]?\s*([+()0-9\-\s]{7,32})')
_PHONE_MOBILE=re.compile(r'(?<!\d)(?:\+?86[\s-]?)?1[3-9]\d{9}(?!\d)')
_PHONE_LAND=re.compile(r'(?<!\d)(?:\+?86[-\s]?)?0\d{2,3}[-\s]?\d{7,8}(?!\d)')


def _same_corporate_host(candidate, official):
    a,b=domain(candidate),domain(official)
    return bool(a and b and (a==b or a.endswith('.'+b) or b.endswith('.'+a)))


def _html_business_contacts(page_bytes, url):
    """Extract contact evidence from actual HTML without guessing phone numbers."""
    tree=LHTML.fromstring(page_bytes,base_url=url)
    for e in tree.xpath('//script|//style|//noscript|//svg'):
        e.drop_tree()
    text=' '.join(tree.xpath('//body//text()'))
    text=re.sub(r'\s+',' ',text)
    raw_emails=[]
    for el in tree.xpath('//a[starts-with(translate(@href,"MAILTO","mailto"),"mailto:")]'):
        raw_emails.append(el.get('href','').split(':',1)[-1].split('?',1)[0])
    raw_emails+=_EMAIL_IN_HTML.findall(text)
    emails=[]
    for e in raw_emails:
        e=e.strip().strip('.,;<>[]()')
        if not good_contact(e,'email') or any(x in e.lower() for x in ('example.com','yourdomain','domain.com','wix.com','sentry.io','cloudflare.com')):
            continue
        if e not in emails:emails.append(e)
    raw_phones=[]
    for el in tree.xpath('//a[starts-with(translate(@href,"TEL","tel"),"tel:")]'):
        raw_phones.append(el.get('href','').split(':',1)[-1].split('?',1)[0])
    for m in _PHONE_LABEL.finditer(text):
        raw_phones.append(m.group(1))
    # For mobile numbers, allow structured spans on actual contact pages only.
    if any(x in url.lower() for x in ('contact','lianxi','lxwm','/about')):
        raw_phones+=_PHONE_MOBILE.findall(text)
        raw_phones+=_PHONE_LAND.findall(text)
    phones=[]
    for raw in raw_phones:
        candidates=_PHONE_MOBILE.findall(raw)+_PHONE_LAND.findall(raw)
        if not candidates and raw.strip().startswith('+'):
            candidates=[raw.strip()]
        for v in candidates:
            v=v.strip()
            if good_contact(v,'phone') and v not in phones:phones.append(v)
    links=[]
    for a in tree.xpath('//a[@href]'):
        href=a.get('href','').strip()
        if not href or href.startswith(('#','javascript:','mailto:','tel:')):continue
        label=' '.join(a.xpath('.//text()')).strip().lower()
        joined=urljoin(url,href)
        if not clean_url(joined):continue
        if any(word in label for word in _CONTACT_WORDS) or any(t in urlsplit(joined).path.lower() for t in _CONTACT_PATHS):
            links.append(joined)
    return {'emails':emails,'phones':phones,'links':list(dict.fromkeys(links))}


def _download_official_html(url, official, timeout=12):
    url=clean_url(url)
    if not url or not _same_corporate_host(url,official) or not _site_public_url(url):return None
    req=Request(url,headers={'User-Agent':'Mozilla/5.0 (compatible; PublicBusinessContactResearch/1.0)',
                             'Accept':'text/html,application/xhtml+xml;q=0.9,*/*;q=0.4'})
    opener=build_opener(_PublicOnlyRedirects())
    try:
        with opener.open(req,timeout=timeout) as resp:
            final=clean_url(resp.geturl())
            if not final or not _same_corporate_host(final,official) or not _site_public_url(final):return None
            if not (200<=int(resp.status)<300):return None
            mime=(resp.headers.get('Content-Type') or '').lower()
            data=resp.read(350000)
            if 'html' not in mime and b'<html' not in data[:1500].lower():return None
            return final,data
    except (HTTPError,URLError,TimeoutError,OSError,socket.timeout,ValueError):
        return None


def inspect_contact_site(result, page_limit=4, timeout=12):
    official=clean_url(result.get('official_site'))
    if not official or marketplace(official):return {'email':'','phone':'','pages':[], 'status':'invalid'}
    root=urlsplit(official)
    homepage=urlunsplit((root.scheme,root.netloc,'/','',''))
    pool=[]
    for link in (result.get('contact_page'),official,homepage):
        if clean_url(link) and _same_corporate_host(link,official):pool.append(clean_url(link))
    for path in _CONTACT_PATHS[:3]:pool.append(urljoin(homepage,path))
    done=set();items=[];first_email='';first_phone='';email_page='';phone_page=''
    while pool and len(done)<page_limit:
        link=pool.pop(0)
        if link in done or not _same_corporate_host(link,official):continue
        done.add(link)
        response=_download_official_html(link,official,timeout)
        if not response:continue
        final,body=response
        try:found=_html_business_contacts(body,final)
        except (ValueError,TypeError,UnicodeError):continue
        items.append(final)
        if found['emails'] and not first_email:
            first_email=found['emails'][0];email_page=final
        if found['phones'] and not first_phone:
            first_phone=found['phones'][0];phone_page=final
        if first_email and first_phone:break
        for href in found['links']:
            if _same_corporate_host(href,official) and href not in done and href not in pool:
                pool.insert(min(len(pool),1),href)
    return {'email':first_email,'phone':first_phone,'email_url':email_page,
            'phone_url':phone_page,'pages':items,'status':'found' if (first_email or first_phone) else 'not_found'}


def backfill_website_contacts(db, args):
    """Backfill confirmed contacts, serialize SQLite writes; no Azure requests."""
    db.execute("""CREATE TABLE IF NOT EXISTS contact_enrichment (
       name_key TEXT PRIMARY KEY, checked_at TEXT NOT NULL, checked_unix REAL NOT NULL,
       status TEXT NOT NULL, email_source TEXT, phone_source TEXT, page_count INTEGER NOT NULL)""")
    db.commit()
    all_results=result_rows(db)
    tasks=[];now=time.time()
    for key,result in all_results.items():
        if result.get('status')!='verified' or not clean_url(result.get('official_site')):
            continue
        if result.get('email') and result.get('phone'):continue
        past=db.execute('SELECT checked_unix FROM contact_enrichment WHERE name_key=?',(key,)).fetchone()
        if past and args.contact_cache_hours>0 and now-float(past[0])<args.contact_cache_hours*3600:
            continue
        tasks.append((key,result))
    tasks=tasks[:args.contact_limit] if args.contact_limit else tasks
    print(f'[contact backfill] verified records requiring email/phone={len(tasks)}, workers={args.contact_workers}',flush=True)
    if not tasks:return
    added_email=added_phone=0
    with ThreadPoolExecutor(max_workers=args.contact_workers) as pool:
        jobs={pool.submit(inspect_contact_site,result,args.contact_pages,args.contact_timeout):(key,result)
              for key,result in tasks}
        for n,fut in enumerate(as_completed(jobs),1):
            key,result=jobs[fut]
            try:r=fut.result()
            except Exception as exc:
                r={'status':'error','email':'','phone':'','pages':[]}
                print(f'[contact warning] {result.get("name",key)}: {type(exc).__name__}: {exc}',flush=True)
            modified=False
            if r.get('email') and not result.get('email'):
                result['email']=r['email'];result['contact_email_source_url']=r.get('email_url','')
                added_email+=1;modified=True
            if r.get('phone') and not result.get('phone'):
                result['phone']=r['phone'];result['contact_phone_source_url']=r.get('phone_url','')
                added_phone+=1;modified=True
            if modified:
                result['contact_source_url']=r.get('email_url') or r.get('phone_url') or result.get('contact_source_url','')
                if not result.get('contact_page'):
                    result['contact_page']=r.get('email_url') or r.get('phone_url') or ''
                db.execute('UPDATE results SET data=?,updated_at=? WHERE name_key=?',
                           (json.dumps(result,ensure_ascii=False),moment(),key))
            db.execute("""INSERT INTO contact_enrichment(name_key,checked_at,checked_unix,status,email_source,phone_source,page_count)
                VALUES(?,?,?,?,?,?,?) ON CONFLICT(name_key) DO UPDATE SET
                checked_at=excluded.checked_at,checked_unix=excluded.checked_unix,
                status=excluded.status,email_source=excluded.email_source,
                phone_source=excluded.phone_source,page_count=excluded.page_count""",
                (key,moment(),time.time(),r.get('status','error'),r.get('email_url',''),
                 r.get('phone_url',''),len(r.get('pages') or [])))
            if n%25==0 or n==len(tasks):
                db.commit()
                print(f'[contact backfill] {n}/{len(tasks)}; new emails={added_email}, phones={added_phone}',flush=True)
    db.commit()

def export_site_checks(db, path):
    init_site_checks(db)
    path.parent.mkdir(parents=True,exist_ok=True)
    fields=('url','status','final_url','http_status','details','checked_at')
    with path.open('w',encoding='utf-8-sig',newline='') as fp:
        writer=csv.DictWriter(fp,fieldnames=fields);writer.writeheader()
        for row in db.execute('SELECT * FROM site_checks ORDER BY status,url'):
            writer.writerow({col:row[col] for col in fields})


def filter_export_by_live_sites(db, args, sheets, rels, strings):
    """Remove dead/blocked/missing websites from ALL exported company sheets."""
    urls=set()
    for idx in (2,3,4):
        for row in sheets[idx].find(f'{{{S}}}sheetData').findall(f'{{{S}}}row')[1:]:
            cols=map_cells(row)
            site=get_cell(cols.get('B'),strings)
            if clean_url(site) and not marketplace(site):urls.add(site)
    checked=site_check_batch(db,urls,workers=args.site_check_workers,
                             timeout=args.site_check_timeout,
                             cache_hours=args.site_check_cache_hours)
    excluded=Counter()
    excluded_rows=[]
    kept=0
    for idx in (2,3,4):
        sheet=sheets[idx]
        data=sheet.find(f'{{{S}}}sheetData')
        for row in list(data.findall(f'{{{S}}}row'))[1:]:
            cells=map_cells(row)
            site=clean_url(get_cell(cells.get('B'),strings))
            status=(checked.get(site) or {}).get('status','invalid')
            if status!='live':
                excluded[status]+=1
                audit=checked.get(site) or {}
                excluded_rows.append({'name':get_cell(cells.get('A'),strings),
                      'sheet':{2:'Companies',3:'Qualified Leads',4:'Review'}[idx],
                      'url':site,'status':status,
                      'http_status':audit.get('http_status',0),
                      'reason':audit.get('details','No valid official website URL'),
                      'checked_at':audit.get('checked_at','')})
                num=int(row.get('r'))
                for c in row.findall(f'{{{S}}}c'):
                    m=re.match(r'[A-Z]+',c.get('r',''))
                    if m:drop_link(sheet,rels[idx],f'{m.group()}{num}')
                data.remove(row)
                continue
            final=clean_url(checked[site].get('final_url',''))
            if final and final!=site:
                set_cell(row,'B',final)
                add_link(sheet,rels[idx],f'B{row.get("r")}',final)
            kept+=1
    print(f'[site filter] kept={kept}; excluded={sum(excluded.values())}: '
          f'{dict(excluded)} (inaccessible includes blocked/timeout, not necessarily dead)',flush=True)
    export_site_checks(db,args.out.with_name(args.out.stem+'_site_checks.csv'))
    excluded_path=args.out.with_name(args.out.stem+'_excluded_sites.csv')
    with excluded_path.open('w',encoding='utf-8-sig',newline='') as fp:
        fields=('name','sheet','url','status','http_status','reason','checked_at')
        writer=csv.DictWriter(fp,fieldnames=fields)
        writer.writeheader()
        writer.writerows(excluded_rows)
    return kept,excluded


def moment():return datetime.now(timezone.utc).isoformat(timespec='seconds')


def event(db,kind,label,status,msg=''):
    db.execute('INSERT INTO events(time,operation,label,status,details) VALUES(?,?,?,?,?)',
               (moment(),kind,str(label)[:250],status,str(msg)[:600]))
    db.commit()


def put_counter(db,key,amount=1):
    db.execute('INSERT INTO counters(name,value) VALUES(?,?) ON CONFLICT(name) DO UPDATE SET value=value+excluded.value',
               (key,amount));db.commit()


def counts(db):return {r['name']:r['value'] for r in db.execute('SELECT name,value FROM counters')}


def add_candidate(db,firm):
    key=norm_name(firm['name'])
    if not key:return False
    old=db.execute('SELECT data,verify_status FROM candidates WHERE name_key=?',(key,)).fetchone()
    if old:
        previous=json.loads(old['data'])
        for field in ('city','official_site_hint','discovery_source','services','cad_types',
                      'cad_software','email_hint','phone_hint','contact_hint','contact_form_hint'):
            if not previous.get(field) and firm.get(field):previous[field]=firm[field]
        db.execute('UPDATE candidates SET data=?, updated_at=? WHERE name_key=?',
                   (json.dumps(previous,ensure_ascii=False),moment(),key))
        return False
    db.execute('INSERT INTO candidates(name_key,data,updated_at) VALUES(?,?,?)',
               (key,json.dumps(firm,ensure_ascii=False),moment()))
    return True


def mark_verification_failure(db, name, exc):
    key=norm_name(name)
    db.execute("""INSERT INTO verification_failures(name_key,attempts,last_error,updated_at)
      VALUES(?,1,?,?) ON CONFLICT(name_key) DO UPDATE SET
      attempts=attempts+1,last_error=excluded.last_error,updated_at=excluded.updated_at""",
      (key,(type(exc).__name__+': '+str(exc))[:350],moment()))
    db.commit()
    attempts=db.execute('SELECT attempts FROM verification_failures WHERE name_key=?',(key,)).fetchone()['attempts']
    if attempts>=2:print(f'[verify skipped] {name}: {attempts} unsuccessful model responses; '
                         'use --retry-failed-verifications to reset the retry counter',flush=True)


def reset_verification_failures(db):
    amount=db.execute('SELECT COUNT(*) FROM verification_failures').fetchone()[0]
    db.execute('DELETE FROM verification_failures')
    db.commit()
    return amount


def result_rows(db):
    return {r['name_key']:json.loads(r['data']) for r in db.execute('SELECT name_key,data FROM results')}


def store_result(db, result):
    key=norm_name(result['name'])
    db.execute('DELETE FROM verification_failures WHERE name_key=?',(key,))
    old=db.execute('SELECT data FROM results WHERE name_key=?',(key,)).fetchone()
    if old:
        prev=json.loads(old['data'])
        if prev.get('status')=='verified' and result.get('status')!='verified':
            prev['contact_form_checked']=True
            db.execute('UPDATE results SET data=?,updated_at=? WHERE name_key=?',
                       (json.dumps(prev,ensure_ascii=False),moment(),key))
            db.commit()
            return
    db.execute('INSERT INTO results(name_key,data,updated_at) VALUES(?,?,?) '
               'ON CONFLICT(name_key) DO UPDATE SET data=excluded.data, updated_at=excluded.updated_at',
               (key,json.dumps(result,ensure_ascii=False),moment()))
    db.execute('UPDATE candidates SET verify_status=?,updated_at=? WHERE name_key=?',
               (result['status'],moment(),key))
    db.commit()


def read_strings(z):
    if 'xl/sharedStrings.xml' not in z.namelist():return []
    return [''.join(x.itertext()) for x in ET.fromstring(z.read('xl/sharedStrings.xml')).findall(f'{{{S}}}si')]


def get_cell(c,strings):
    if c is None:return ''
    v=c.find(f'{{{S}}}v')
    if c.get('t')=='s' and v is not None:
        try:return strings[int(v.text)]
        except (ValueError,IndexError,TypeError):return ''
    if v is not None:return v.text or ''
    inline=c.find(f'{{{S}}}is')
    return ''.join(inline.itertext()) if inline is not None else ''


def map_cells(row):
    out={}
    for c in row.findall(f'{{{S}}}c'):
        mt=re.match(r'[A-Z]+',c.get('r',''))
        if mt:out[mt.group()]=c
    return out


def input_firms(path):
    """Read original workbook without rebuilding/reformatting it."""
    if not path or not path.exists():return {},{},0
    by_name, master, rows={}, {},0
    with ZipFile(path) as z:
        names=[x.get('name') for x in ET.fromstring(z.read('xl/workbook.xml')).findall(f'.//{{{S}}}sheet')]
        if names[:5]!=['Firm Leads','Companies','Qualified Leads','Review','Stats']:
            raise ValueError('Expected the original five-sheet China CAD Excel. Refusing format-changing conversion.')
        ss=read_strings(z)
        for idx in (1,2,3,4):
            root=ET.fromstring(z.read(f'xl/worksheets/sheet{idx}.xml'))
            for r in root.findall(f'.//{{{S}}}sheetData/{{{S}}}row'):
                if int(r.get('r'))==1:continue
                c=map_cells(r)
                name=get_cell(c.get('A'),ss).strip()
                if not name:continue
                rows+=1
                key=norm_name(name)
                data={
                    'name':name,'official_site_hint':get_cell(c.get('B'),ss),
                    'city':get_cell(c.get('C'),ss),
                    'services':get_cell(c.get('D'),ss),
                    'cad_types':get_cell(c.get('E'),ss),
                    'cad_software':get_cell(c.get('I'),ss),
                    'discovery_source':get_cell(c.get('N'),ss),
                    'origin_query':'existing workbook',
                }
                if key not in by_name or (marketplace(by_name[key].get('official_site_hint')) and
                                          data['official_site_hint'] and not marketplace(data['official_site_hint'])):
                    by_name[key]=data
                if idx==1:master[key]=data
    return by_name,master,rows


def letters(n):
    result=''
    while n:n,r=divmod(n-1,26);result=chr(65+r)+result
    return result


def letter_no(s):
    out=0
    for ch in s:out=out*26+ord(ch)-64
    return out


def set_cell(row,col,value,template=None):
    columns=map_cells(row)
    c=columns.get(col)
    if c is None:
        attrib={'r':f'{col}{row.get("r")}'}
        if template is not None:
            style=map_cells(template).get(col)
            if style is not None and style.get('s'):attrib['s']=style.get('s')
        c=ET.Element(f'{{{S}}}c',**attrib)
        idx=letter_no(col)
        for i,child in enumerate(row):
            mt=re.match(r'[A-Z]+',child.get('r',''))
            if mt and letter_no(mt.group())>idx:
                row.insert(i,c);break
        else:row.append(c)
    # Inline XML text avoids having to rewrite sharedStrings (which could shift indices).
    for part in list(c):
        if part.tag in (f'{{{S}}}v',f'{{{S}}}is',f'{{{S}}}f'):c.remove(part)
    c.set('t','inlineStr')
    ET.SubElement(ET.SubElement(c,f'{{{S}}}is'),f'{{{S}}}t').text=str(value or '')


def hyperlinks_root(sheet):
    node=sheet.find(f'{{{S}}}hyperlinks')
    if node is not None:return node
    node=ET.Element(f'{{{S}}}hyperlinks')
    successors={'printOptions','pageMargins','pageSetup','headerFooter','rowBreaks','colBreaks',
                'customProperties','cellWatches','ignoredErrors','drawing','legacyDrawing',
                'picture','oleObjects','controls','webPublishItems','tableParts','extLst'}
    pos=next((i for i,x in enumerate(sheet) if ET.QName(x).localname in successors),len(sheet))
    sheet.insert(pos,node);return node


def drop_link(sheet, rels, cell_ref):
    node=sheet.find(f'{{{S}}}hyperlinks')
    if node is None:return
    for link in list(node):
        if link.get('ref')!=cell_ref:continue
        rid=link.get(f'{{{R}}}id')
        node.remove(link)
        if rid and not any(x.get(f'{{{R}}}id')==rid for x in node):
            for rel in list(rels):
                if rel.get('Id')==rid and rel.get('Type','').endswith('/hyperlink'):
                    rels.remove(rel)
    if not len(node):sheet.remove(node)


def add_link(sheet,rels,ref,url):
    if not clean_url(url):return
    drop_link(sheet,rels,ref)
    node=hyperlinks_root(sheet)
    ids={x.get('Id') for x in rels}
    i=1
    while f'rId{i}' in ids:i+=1
    rid=f'rId{i}'
    ET.SubElement(rels,f'{{{P}}}Relationship',Id=rid,
                  Type='http://schemas.openxmlformats.org/officeDocument/2006/relationships/hyperlink',
                  Target=url,TargetMode='External')
    ET.SubElement(node,f'{{{S}}}hyperlink',ref=ref,attrib={f'{{{R}}}id':rid})


def classify_cad(result):
    """Priority based on evidence of CAD deliverables, not software/machinery mentions.

    High: explicit parametric 3D/assembly CAD design services.
    Medium: 3D mechanical CAD modelling/part design with less specific deliverables.
    Low: 2D drafting, industrial design/engineering services without 3D evidence.
    Review: model manufacturing, software selling, or unsubstantiated CAD work.
    """
    deliverables=' '.join(str(result.get(k) or '') for k in ('cad_types','services')).lower()
    software=str(result.get('cad_software') or '').lower()
    negative=('cad软件销售','软件开发','软件代理','软件培训','仅制造','制造加工','only manufacturing',
              'software reseller','software development','software distribution','培训课程')
    high_terms=('参数化三维','三维参数化','参数化建模','参数化设计','三维装配','装配体',
                '机械装配设计','装配设计','3d cad assembly','cad assemblies',
                'parametric 3d','parametric cad','assembly modelling','assembly modeling',
                'mechanical assembly','solidworks assembly')
    medium_terms=('3d cad','三维cad','三维建模','三维模型','三维结构','产品结构设计',
                  '机械结构设计','机械三维设计','三维机械设计','3d modeling','3d modelling',
                  'mechanical 3d','cad model','3d product design','三维零件',
                  '工业产品建模','逆向建模','solidworks建模','creo建模')
    low_terms=('二维制图','2d cad','cad制图','工程制图','施工图','机械设计外包',
               '机械设计服务','工业设计','结构设计','机械设计')
    if any(t in deliverables for t in high_terms):
        if any(t in deliverables for t in negative) and not any(t in deliverables for t in ('外包','服务','设计','model')):
            return 'CAD evidence requires review','Review','Conflicting CAD service evidence'
        return 'Parametric 3D CAD models / assemblies','High','Explicit parametric or assembly design: '+next(t for t in high_terms if t in deliverables)
    if any(t in deliverables for t in medium_terms):
        return '3D CAD models (parametric/assembly unconfirmed)','Medium','Explicit 3D design: '+next(t for t in medium_terms if t in deliverables)
    if any(t in deliverables for t in low_terms):
        return 'CAD design/drawings (3D unconfirmed)','Low','CAD design service; no confirmed 3D parametric data'
    return 'CAD deliverables unconfirmed','Review','No clear evidence of CAD deliverables; software='+software[:40]


def category(result):
    dtype,priority,_=classify_cad(result)
    return dtype,priority



def fresh_row(no,template,fields):
    r=ET.Element(f'{{{S}}}row',r=str(no),spans='1:22')
    for c in template.findall(f'{{{S}}}c'):
        col=re.match(r'[A-Z]+',c.get('r',''))
        if col and letter_no(col.group())<=22:
            cnew=ET.SubElement(r,f'{{{S}}}c',r=f'{col.group()}{no}')
            if c.get('s'):cnew.set('s',c.get('s'))
            # leave unused cells entirely empty instead of copying content
    for col,val in fields.items():set_cell(r,col,val)
    return r


def result_fields(x):
    """Generate only the business-useful fields; auxiliary evidence remains in audit CSV."""
    dtype,priority=category(x)
    site=clean_url(x['official_site'])
    source=clean_url(x.get('identity_url')) or site
    return {
        'A':x['name'],'B':site,'C':x.get('city',''),'D':x.get('services',''),
        'E':dtype,'F':priority,'G':x.get('cad_types','') or x.get('services','')[:160],
        'H':source if source!=site else '','I':x.get('cad_software',''),
        'J':x.get('email',''),'K':x.get('phone',''),
        'L':verified_form_url(x) or x.get('contact_page',''),
        'O':'14' if priority=='High' else ('10' if priority=='Medium' else ('6' if priority=='Low' else '2')),
        'P':contact_label(x),
    }


def update_stats_sheet(root,strings,modified_sheets,results, ready_count=0, site_metrics=None):
    """Update old summary totals, append Azure metrics without altering Stats formatting.

    Source-crawl metrics (HTTP requests, browser counts, etc.) remain historical.
    """
    def entries(sheet):
        d=sheet.find(f'{{{S}}}sheetData')
        for row in d.findall(f'{{{S}}}row')[1:]:
            c=map_cells(row)
            if get_cell(c.get('A'),strings).strip():yield c

    totals={
        'firm_leads':len({norm_name(get_cell(c.get('A'),strings)) for i in (2,3) for c in entries(modified_sheets[i])}),
        'companies':sum(1 for _ in entries(modified_sheets[2])),
        'qualified_leads':sum(1 for _ in entries(modified_sheets[3])),
        'review':sum(1 for _ in entries(modified_sheets[4])),
    }
    firm_rows=list(entries(modified_sheets[2]))+list(entries(modified_sheets[3]))
    contact_rows=list(entries(modified_sheets[2]))
    priorities=Counter(get_cell(c.get('F'),strings).strip().lower() for c in contact_rows)
    for pr in ('high','medium','low'):
        totals['companies_priority_'+pr]=priorities.get(pr,0)
    class_counts=Counter(get_cell(c.get('E'),strings).strip() for c in contact_rows)
    for name in ('Parametric CAD models (3D unconfirmed)','3D CAD assemblies','Parametric 3D CAD models',
                 '3D CAD models','Technical drawings','2D CAD / drafting'):
        totals['companies_type_'+name]=class_counts.get(name,0)
    verified=[r for r in results.values() if r.get('status')=='verified']
    named_existing={norm_name(get_cell(c.get('A'),strings)) for c in firm_rows}
    metrics={
        'azure_pipeline_version':VERSION,
        'azure_verified_total':len(verified),
        'azure_verified_in_firm_leads':sum(norm_name(r['name']) in named_existing for r in verified),
        'azure_verified_contactable':sum(contactable(r) for r in verified),
        'azure_verified_no_contact':sum(not contactable(r) for r in verified),
        'azure_verified_with_email':sum(bool(r.get('email')) for r in verified),
        'azure_verified_with_phone':sum(bool(r.get('phone')) for r in verified),
        'azure_verified_with_html_contact_form':sum(bool(verified_form_url(r)) for r in verified),
        'azure_candidate_count':sum(r.get('status')=='candidate' for r in results.values()),
        'azure_not_found_count':sum(r.get('status')=='not_found' for r in results.values()),
        'azure_priority_high':sum(classify_cad(r)[1]=='High' for r in verified),
        'azure_priority_medium':sum(classify_cad(r)[1]=='Medium' for r in verified),
        'azure_priority_low':sum(classify_cad(r)[1]=='Low' for r in verified),
        'azure_priority_review':sum(classify_cad(r)[1]=='Review' for r in verified),
        'azure_stats_updated_utc':moment(),
    }
    if site_metrics:metrics.update(site_metrics)
    source_metrics=totals|metrics
    data=root.find(f'{{{S}}}sheetData')
    rows=data.findall(f'{{{S}}}row')
    existing=set()
    for row in rows[1:]:
        cells=map_cells(row)
        key=get_cell(cells.get('A'),strings).strip()
        if key in source_metrics:
            set_cell(row,'B',source_metrics[key]);existing.add(key)
            if key=='firm_leads':set_cell(row,'A','total_company_leads')
    template=rows[1] if len(rows)>1 else rows[0]
    next_row=max(int(r.get('r')) for r in rows)+1
    for key in metrics:
        if key in existing:continue
        row=ET.SubElement(data,f'{{{S}}}row',r=str(next_row),spans='1:2')
        set_cell(row,'A',key,template=template)
        set_cell(row,'B',metrics[key],template=template)
        next_row+=1
    dim=root.find(f'{{{S}}}dimension')
    if dim is not None:dim.set('ref',f'A1:B{next_row-1}')
    filt=root.find(f'{{{S}}}autoFilter')
    if filt is not None:filt.set('ref',f'A1:B{next_row-1}')
    return totals,metrics


def refresh_cached_forms(db, max_pages=4):
    """Inspect formerly found URLs, no AI calls; preserve all verified websites/emails."""
    counter=Counter()
    for row in db.execute('SELECT name_key,data FROM results').fetchall():
        result=json.loads(row['data'])
        if result.get('status')!='verified':continue
        site=clean_url(result.get('official_site'))
        if not site:continue
        # Never treat an old model-generated form URL as verified without HTML.
        current=verified_form_url(result)
        if current:
            counter['already_verified']+=1
            continue
        former=clean_url(result.get('contact_form_url'))
        candidate=former or clean_url(result.get('contact_page'))
        if not candidate:
            counter['no_contact_page']+=1
            continue
        verified=confirm_contact_form(site,former,result.get('contact_page',''),limit=max_pages)
        result['form_dom_verified']=bool(verified)
        result['contact_form_url']=verified
        result['contact_form_checked']=True
        result['form_inspected_utc']=moment()
        if verified:
            result['contact_page']=verified
            result['contact_source_url']=verified
            counter['forms_validated']+=1
        else:
            counter['not_confirmed']+=1
        db.execute('UPDATE results SET data=?,updated_at=? WHERE name_key=?',
                   (json.dumps(result,ensure_ascii=False),moment(),row['name_key']))
    db.commit()
    return counter


def _eligible_verified(results, all_existing):
    """Reject competing legal identities for the same owned domain (new or old)."""
    initial={k:v for k,v in results.items()
             if v.get('status')=='verified' and valid_company_name(v.get('name'))
             and clean_url(v.get('official_site')) and not marketplace(v['official_site'])}
    domain_names={}
    for key,val in initial.items():
        domain_names.setdefault(domain(val['official_site']),set()).add(key)
    for key,val in all_existing.items():
        old_site=val.get('official_site_hint','')
        if clean_url(old_site) and not marketplace(old_site) and valid_company_name(val.get('name')):
            domain_names.setdefault(domain(old_site),set()).add(key)
    conflict_domains={d for d,ks in domain_names.items() if len(ks)>1}
    accepted={k:v for k,v in initial.items() if domain(v['official_site']) not in conflict_domains}
    return accepted,conflict_domains


def _remove_rows_by_key(sheet,strings,remove_keys):
    """Remove stale category rows and their hyperlinks, preserving the other rows/styles."""
    if not remove_keys:return set()
    data=sheet.find(f'{{{S}}}sheetData')
    removed=set()
    for row in list(data.findall(f'{{{S}}}row'))[1:]:
        name=get_cell(map_cells(row).get('A'),strings)
        key=norm_name(name)
        if key in remove_keys:
            removed.add(key)
            data.remove(row)
    return removed


# Output keeps only the useful original columns. O/P move to M/N;
# Review reason (old W) becomes O on the Review sheet.
RETAINED_COLUMNS = ('A','B','C','D','E','F','G','H','I','J','K','L','O','P')
OMITTED_HEADERS = {
    'Evidence / source URL','Profile URL','Contact method / limitations',
    'Evidence level','CAD data licensing','Address (original)',
    'Collected (UTC)','Company identification evidence',
}


def _keep_unique_names(sheet, rels, strings, excluded=()):
    """Keep one row per name, remove source placeholders and cross-tab duplicates."""
    data=sheet.find(f'{{{S}}}sheetData')
    taken=set(excluded)
    for row in list(data.findall(f'{{{S}}}row'))[1:]:
        key=norm_name(get_cell(map_cells(row).get('A'),strings))
        if not key or key in TECHNICAL_NAMES or key in taken:
            oldnum=int(row.get('r'))
            for c in row.findall(f'{{{S}}}c'):
                mt=re.match(r'[A-Z]+',c.get('r',''))
                if mt:drop_link(sheet,rels,f'{mt.group()}{oldnum}')
            data.remove(row)
            continue
        taken.add(key)
    return taken


def _compact_and_sort_sheet(sheet, rels, strings, is_review=False):
    """Drop unwanted columns, preserve cell formats/URLs, and sort category priorities."""
    keep=RETAINED_COLUMNS+(('W',) if is_review else ())
    mapping={letter:letters(i+1) for i,letter in enumerate(keep)}
    data=sheet.find(f'{{{S}}}sheetData')
    rows=data.findall(f'{{{S}}}row')
    if not is_review:
        priorities={'High':0,'Medium':1,'Low':2,'Review':3}
        def ordering(row):
            c=map_cells(row)
            priority=get_cell(c.get('F'),strings)
            name=get_cell(c.get('A'),strings)
            return priorities.get(priority,4), name
        rows=[rows[0]]+sorted(rows[1:],key=ordering)
    old_to_new={int(row.get('r')):i+1 for i,row in enumerate(rows)}
    for row in list(data):data.remove(row)
    for idx,row in enumerate(rows,1):
        oldno=int(row.get('r'))
        row.set('r',str(idx))
        row.set('spans',f'1:{len(keep)}')
        for cell in list(row.findall(f'{{{S}}}c')):
            oldletter=re.match(r'[A-Z]+',cell.get('r',''))
            if not oldletter or oldletter.group() not in mapping:
                row.remove(cell)
            else:
                cell.set('r',f'{mapping[oldletter.group()]}{idx}')
        data.append(row)
    # Retarget hyperlink references and remove links to discarded columns/rows.
    links=sheet.find(f'{{{S}}}hyperlinks')
    if links is not None:
        for link in list(links):
            mt=re.fullmatch(r'([A-Z]+)(\d+)',link.get('ref',''))
            if not mt or mt.group(1) not in mapping or int(mt.group(2)) not in old_to_new:
                links.remove(link)
            else:
                link.set('ref',f'{mapping[mt.group(1)]}{old_to_new[int(mt.group(2))]}')
        used={link.get(f'{{{R}}}id') for link in links}
        for relation in list(rels):
            if relation.get('Type','').endswith('/hyperlink') and relation.get('Id') not in used:
                rels.remove(relation)
        if len(links)==0:sheet.remove(links)
    cols=sheet.find(f'{{{S}}}cols')
    if cols is not None:
        saved={}
        for col in cols.findall(f'{{{S}}}col'):
            for index in range(int(col.get('min','0')),int(col.get('max','0'))+1):
                letter=letters(index)
                if letter in mapping:
                    newindex=letter_no(mapping[letter])
                    cp=copy.deepcopy(col)
                    cp.set('min',str(newindex));cp.set('max',str(newindex))
                    saved[newindex]=cp
        for x in list(cols):cols.remove(x)
        for x in sorted(saved):cols.append(saved[x])
    last=len(rows)
    dim=sheet.find(f'{{{S}}}dimension')
    if dim is not None:dim.set('ref',f'A1:{letters(len(keep))}{last}')
    filt=sheet.find(f'{{{S}}}autoFilter')
    if filt is not None:filt.set('ref',f'A1:{letters(len(keep))}{last}')
    return last-1


def _remove_master_sheet_from_workbook(src, updates):
    """Remove redundant Firm Leads tab; Companies+Qualified are its partition."""
    wb=ET.fromstring(src.read('xl/workbook.xml'))
    rels=ET.fromstring(src.read('xl/_rels/workbook.xml.rels'))
    ct=ET.fromstring(src.read('[Content_Types].xml'))
    sheets=wb.find(f'{{{S}}}sheets')
    master=next((s for s in sheets if s.get('name')=='Firm Leads'),None)
    if master is None:raise ValueError('Original Firm Leads tab missing')
    rid=master.get(f'{{{R}}}id')
    sheets.remove(master)
    for rel in list(rels):
        if rel.get('Id')==rid:rels.remove(rel)
    for part in list(ct):
        if part.get('PartName')=='/xl/worksheets/sheet1.xml':ct.remove(part)
    updates['xl/workbook.xml']=ET.tostring(wb,encoding='utf-8',xml_declaration=True)
    updates['xl/_rels/workbook.xml.rels']=ET.tostring(rels,encoding='utf-8',xml_declaration=True)
    updates['[Content_Types].xml']=ET.tostring(ct,encoding='utf-8',xml_declaration=True)
    # These parts are also filtered from the finished ZIP archive.
    return {'xl/worksheets/sheet1.xml','xl/worksheets/_rels/sheet1.xml.rels'}


def publish_workbook(temp, out, retries=3, delay=2):
    """Publish atomically; if Windows locks the destination, keep a usable pending XLSX.

    Never delete or overwrite the user's existing workbook on a failed publish.
    SQLite remains authoritative and can regenerate the workbook later.
    """
    pending=out.with_name(out.stem+'.pending.xlsx')
    for attempt in range(retries):
        try:
            temp.replace(out)
        except PermissionError:
            if attempt+1<retries:
                print(f'[excel locked] Cannot replace {out.name}; retry '
                      f'{attempt+1}/{retries-1} in {delay}s (close Excel if open)',flush=True)
                time.sleep(delay)
                continue
            # Windows locks the existing file; do not let this kill discovery.
            try:
                temp.replace(pending)
            except PermissionError:
                # The user may also have the previous pending file open.
                stamp=datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S_%f')
                pending=out.with_name(f'{out.stem}.pending_{stamp}.xlsx')
                try:
                    temp.replace(pending)
                except PermissionError:
                    # Still leave the generated .writing.xlsx on disk for recovery.
                    pending=temp
            print(f'[excel deferred] {out.name} is locked. '
                  f'Latest generated Excel: {pending.name}. '
                  'SQLite state is safe; collection will continue. '
                  'Close Excel, then run --rebuild-from-cache to update the main file.',flush=True)
            return pending,False
        else:
            try:
                if pending.exists():pending.unlink()
            except OSError:
                pass
            return out,True
    raise AssertionError('unreachable')


def patch_workbook(inp,out,results,site_db=None,site_args=None):
    """Build deduplicated 4-sheet XLSX from immutable original and saved Azure results."""
    if inp.resolve()==out.resolve():raise ValueError('Output must differ from input')
    all_existing,master,_=input_firms(inp)
    accepted,conflicts=_eligible_verified(results,all_existing)
    added={k:v for k,v in accepted.items() if k not in master}
    changes=0
    updates={}
    sheet_roots={}
    sheet_rels={}
    site_metrics={}
    with ZipFile(inp) as src:
        strings=read_strings(src)
        for idx in (1,2,3,4):
            path=f'xl/worksheets/sheet{idx}.xml'
            relpath=f'xl/worksheets/_rels/sheet{idx}.xml.rels'
            sheet=ET.fromstring(src.read(path))
            rels=(ET.fromstring(src.read(relpath)) if relpath in src.namelist()
                  else ET.Element(f'{{{P}}}Relationships',nsmap={None:P}))
            data=sheet.find(f'{{{S}}}sheetData')
            existing_rows=data.findall(f'{{{S}}}row')
            template=existing_rows[1] if len(existing_rows)>1 else existing_rows[0]
            # Synchronize category views, but keep the source/master rows and unrelated historical data.
            # Already-verified contactable: Companies only; verified without contact: Qualified Leads only.
            if idx in (2,3):
                stale={k for k,v in accepted.items() if (idx==2 and not contactable(v)) or
                       (idx==3 and contactable(v))}
                removed=_remove_rows_by_key(sheet,strings,stale)
                for row in existing_rows[1:]:
                    if norm_name(get_cell(map_cells(row).get('A'),strings)) in removed:
                        n=int(row.get('r'))
                        for col in ('A','B','H','L'):
                            drop_link(sheet,rels,f'{col}{n}')
                changes+=len(removed)
            remaining=data.findall(f'{{{S}}}row')
            for row in remaining[1:]:
                c=map_cells(row)
                name=get_cell(c.get('A'),strings)
                key=norm_name(name)
                x=accepted.get(key)
                if not x:continue
                old_site=get_cell(c.get('B'),strings)
                if old_site and not marketplace(old_site) and domain(old_site)!=domain(x['official_site']):continue
                n=int(row.get('r'))
                site=x['official_site']
                set_cell(row,'B',site)
                add_link(sheet,rels,f'B{n}',site)
                for col,fld in [('J','email'),('K','phone')]:
                    if x.get(fld) and not get_cell(c.get(col),strings):set_cell(row,col,x[fld])
                for col in ('H','L'):
                    old=get_cell(c.get(col),strings)
                    if marketplace(old):
                        replacement=((verified_form_url(x) or x.get('contact_page','')) if col=='L'
                                     else (x.get('identity_url','') if x.get('identity_url','')!=site else '') if col=='H'
                                     else '')
                        set_cell(row,col,replacement)
                        if clean_url(replacement):add_link(sheet,rels,f'{col}{n}',replacement)
                        else:drop_link(sheet,rels,f'{col}{n}')
                link=verified_form_url(x) or x.get('contact_page','')
                if link and not get_cell(c.get('L'),strings):
                    set_cell(row,'L',link);add_link(sheet,rels,f'L{n}',link)
                elif verified_form_url(x) and get_cell(c.get('L'),strings)!=verified_form_url(x):
                    set_cell(row,'L',verified_form_url(x));add_link(sheet,rels,f'L{n}',verified_form_url(x))
                dtype,priority,cad_note=classify_cad(x)
                for col,txt in [('E',dtype),('F',priority),
                                ('O','14' if priority=='High' else ('10' if priority=='Medium' else ('6' if priority=='Low' else '2'))),
                                ('P',contact_label(x))]:
                    set_cell(row,col,txt)
                changes+=1
            current_names={norm_name(get_cell(map_cells(r).get('A'),strings))
                           for r in data.findall(f'{{{S}}}row')[1:]}
            if idx==1:
                sheet_add=added
            elif idx==2:
                sheet_add={k:v for k,v in accepted.items() if contactable(v) and k not in current_names}
            elif idx==3:
                sheet_add={k:v for k,v in accepted.items() if not contactable(v) and k not in current_names}
            else:sheet_add={}
            if sheet_add:
                next_no=max(int(r.get('r')) for r in existing_rows)+1
                for key,x in sorted(sheet_add.items(),key=lambda kv:kv[1]['name']):
                    row=fresh_row(next_no,template,result_fields(x))
                    data.append(row)
                    for col in ('B','H','L'):
                        link=result_fields(x).get(col,'')
                        if clean_url(link):add_link(sheet,rels,f'{col}{next_no}',link)
                    next_no+=1;changes+=1
            last_row=max(int(r.get('r')) for r in data.findall(f'{{{S}}}row'))
            dimension=sheet.find(f'{{{S}}}dimension')
            if dimension is not None:dimension.set('ref',f'A1:{"W" if idx in (3,4) else "V"}{last_row}')
            filt=sheet.find(f'{{{S}}}autoFilter')
            if filt is not None:filt.set('ref',f'A1:{"W" if idx in (3,4) else "V"}{last_row}')
            sheet_roots[idx]=sheet
            sheet_rels[idx]=rels
            updates[path]=ET.tostring(sheet,encoding='utf-8',xml_declaration=True)
            updates[relpath]=ET.tostring(rels,encoding='utf-8',xml_declaration=True)
        # The original master is a full duplicate of Companies + Qualified Leads.
        # Keep both categories, the separate Review queue, and Stats only.
        if site_db is not None and site_args is not None:
            sites_kept,sites_excluded=filter_export_by_live_sites(site_db,site_args,sheet_roots,sheet_rels,strings)
            site_metrics={'official_sites_live_rows':sites_kept,
                          'official_sites_excluded_rows':sum(sites_excluded.values()),
                          'official_sites_inaccessible_rows':sites_excluded.get('inaccessible',0),
                          'official_sites_missing_or_directory_rows':sites_excluded.get('invalid',0),
                          'official_sites_checked_utc':moment()}
        company_names=_keep_unique_names(sheet_roots[2],sheet_rels[2],strings)
        qualified_names=_keep_unique_names(sheet_roots[3],sheet_rels[3],strings,company_names)
        _keep_unique_names(sheet_roots[4],sheet_rels[4],strings,qualified_names)
        if site_db is not None:
            surviving=set()
            for idx in (2,3,4):
                data=sheet_roots[idx].find(f'{{{S}}}sheetData')
                for row in data.findall(f'{{{S}}}row')[1:]:
                    surviving.add(norm_name(get_cell(map_cells(row).get('A'),strings)))
            added={k:v for k,v in added.items() if k in surviving}
        # Remove low-value columns in the final output, not only from new records.
        for idx in (2,3,4):
            _compact_and_sort_sheet(sheet_roots[idx],sheet_rels[idx],strings,is_review=(idx==4))
            updates[f'xl/worksheets/sheet{idx}.xml']=ET.tostring(sheet_roots[idx],encoding='utf-8',xml_declaration=True)
            updates[f'xl/worksheets/_rels/sheet{idx}.xml.rels']=ET.tostring(sheet_rels[idx],encoding='utf-8',xml_declaration=True)
        stats_path='xl/worksheets/sheet5.xml'
        stats_root=ET.fromstring(src.read(stats_path))
        update_stats_sheet(stats_root,strings,sheet_roots,results,site_metrics=site_metrics)
        updates[stats_path]=ET.tostring(stats_root,encoding='utf-8',xml_declaration=True)
        omit_archive=_remove_master_sheet_from_workbook(src,updates)
        out.parent.mkdir(parents=True,exist_ok=True)
        temp=out.with_name(out.stem+'.writing.xlsx')
        with ZipFile(temp,'w') as dst:
            for item in src.infolist():
                if item.filename in omit_archive:continue
                dst.writestr(item,updates.pop(item.filename,src.read(item.filename)))
            for name,content in updates.items():dst.writestr(name,content)
        saved_path,saved_to_main=publish_workbook(temp,out)
    with ZipFile(inp) as original, ZipFile(saved_path) as saved:
        for name in original.namelist():
            if name.startswith(('xl/styles','xl/theme/','xl/tables/')):
                if original.read(name)!=saved.read(name):raise AssertionError('Formatting changed: '+name)
        if saved.testzip():raise AssertionError('Corrupt output ZIP')
    return len(added),changes,len(conflicts),saved_to_main


def export_review(db,path):
    fields=['name','status','city','official_site','email','phone','contact_page',
            'contact_form_url','form_dom_verified','contact_method','cad_priority','cad_type','cad_evidence','cad_types',
            'services','cad_software','identity_url','contact_source_url','reason',
            'confidence','source_count','search_events','billed_search_requests','origin_query']
    rows=result_rows(db)
    path.parent.mkdir(parents=True,exist_ok=True)
    with path.open('w',encoding='utf-8-sig',newline='') as f:
        w=csv.DictWriter(f,fieldnames=fields,extrasaction='ignore');w.writeheader()
        for r in rows.values():
            dtype,priority,note=classify_cad(r)
            w.writerow({**r,'contact_method':contact_method(r),
                        'cad_priority':priority,'cad_type':dtype,'cad_evidence':note})
    return Counter(r.get('status','?') for r in rows.values())



# -------- Maps-first discovery: licensed Places APIs or permitted public OSM --------
MAP_KEYWORDS = ('机械设计','工业设计','产品结构设计','机械设计外包','非标自动化',
                '自动化设备','机械工程','三维设计','模具设计','机器人研发',
                '工装夹具','智能装备','逆向工程','机械制造')
MAP_CITIES = REGIONS + ['潍坊','烟台','珠海','江门','肇庆','保定','石家庄','唐山',
                         '哈尔滨','长春','南昌','南宁','贵阳','昆明','太原','兰州']
# Approximate city centers (lat, lon), for focused OpenStreetMap requests only.
OSM_CENTERS = {'上海':(31.23,121.47),'北京':(39.90,116.40),'深圳':(22.54,114.06),
 '广州':(23.13,113.26),'东莞':(23.02,113.75),'苏州':(31.30,120.62),
 '杭州':(30.27,120.15),'宁波':(29.87,121.55),'南京':(32.06,118.80),
 '武汉':(30.59,114.30),'成都':(30.67,104.06),'天津':(39.12,117.20),
 '重庆':(29.56,106.55),'佛山':(23.02,113.12),'无锡':(31.49,120.31),
 '常州':(31.81,119.97),'青岛':(36.07,120.38),'济南':(36.67,117.02),
 '西安':(34.34,108.94),'合肥':(31.82,117.23),'厦门':(24.48,118.08),
 '中山':(22.52,113.39),'惠州':(23.11,114.42),'郑州':(34.75,113.62),
 '长沙':(28.23,112.94),'沈阳':(41.80,123.43),'大连':(38.91,121.61),
 '昆山':(31.38,120.98),'嘉兴':(30.75,120.75),'南通':(32.02,120.86),
 '温州':(27.99,120.70),'绍兴':(30.00,120.58),'福州':(26.07,119.30),
 '台州':(28.66,121.42)}
MAP_NAME_NEGATIVE = ('培训','教育','学校','学院','补习','招生','人力资源','房产','装饰设计',
                     '影视','动画','广告','婚纱','摄影','文创','传媒','美容','餐厅')
MAP_USER_AGENT='ChinaCADBusinessResearch/5.0 (public business listing research)'


def map_specs(args):
    keys = {'amap':os.environ.get('AMAP_KEY','').strip(),
            'baidu':os.environ.get('BAIDU_MAP_AK','').strip()}
    if args.map_source=='off':return []
    if args.map_source=='auto':
        sources=[k for k in ('amap','baidu') if keys[k]]
        if not sources:sources=['osm']
    elif args.map_source=='all':sources=['amap','baidu','osm']
    else:sources=[args.map_source]
    for s in sources:
        if s in keys and not keys[s]:
            raise RuntimeError(f'{s} Places API requires '+('AMAP_KEY' if s=='amap' else 'BAIDU_MAP_AK')+
                               ' environment variable; no unofficial private endpoints are used.')
    return sources


def map_queries(args):
    cities=(Path(args.map_cities_file).read_text(encoding='utf-8-sig').splitlines()
            if args.map_cities_file else MAP_CITIES)
    keywords=(Path(args.map_keywords_file).read_text(encoding='utf-8-sig').splitlines()
              if args.map_keywords_file else MAP_KEYWORDS)
    cities=list(dict.fromkeys(x.strip() for x in cities if x.strip() and not x.lstrip().startswith('#')))
    keywords=list(dict.fromkeys(x.strip() for x in keywords if x.strip() and not x.lstrip().startswith('#')))
    return cities,keywords


def map_init(db):
    db.executescript('''
      CREATE TABLE IF NOT EXISTS map_tasks (
        task_key TEXT PRIMARY KEY, provider TEXT, city TEXT, keyword TEXT, page INTEGER,
        count INTEGER, completed_at TEXT, status TEXT);
      CREATE TABLE IF NOT EXISTS map_raw (
        origin_key TEXT PRIMARY KEY, name TEXT, city TEXT, category TEXT, phone TEXT,
        website TEXT, address TEXT, provider TEXT, poi_id TEXT, added_at TEXT);
      CREATE TABLE IF NOT EXISTS html_checks (
        name_key TEXT PRIMARY KEY, checked_at TEXT, outcome TEXT);
    ''')
    db.commit()


def map_task_key(provider,city,keyword,page):
    return hashlib.sha256(json.dumps([provider,city,keyword,page],ensure_ascii=False).encode()).hexdigest()


def map_task_list(args):
    cities,words=map_queries(args)
    specs=map_specs(args)
    out=[]
    for provider in specs:
        if provider=='osm':
            # Public community infrastructure: deliberately small, city-scoped sampling.
            for city in cities[:args.osm_city_limit]:
                if city in OSM_CENTERS:out.append((provider,city,'CAD engineering offices',1))
        else:
            for city in cities:
                for word in words:
                    for page in range(1,args.map_pages+1):out.append((provider,city,word,page))
    return out


def json_http(url, params=None, timeout=20, post=None, retries=2):
    if params:url += ('&' if '?' in url else '?')+urlencode(params)
    for attempt in range(retries+1):
        try:
            headers={'User-Agent':MAP_USER_AGENT,'Accept':'application/json'}
            if post is not None:headers['Content-Type']='application/x-www-form-urlencoded'
            req=Request(url,data=post,headers=headers)
            with urlopen(req,timeout=timeout) as resp:
                if resp.status!=200:raise RuntimeError(f'HTTP {resp.status}')
                raw=resp.read(3500000)
                if len(raw)>=3500000:raise RuntimeError('Response exceeds safe size')
            return json.loads(raw.decode('utf-8-sig'))
        except Exception as exc:
            if attempt>=retries:raise
            if 'HTTP Error 401' in str(exc) or 'HTTP Error 403' in str(exc):raise
            time.sleep(2**attempt * 2)


def map_page(provider,city,keyword,page,args):
    if provider=='amap':
        info=json_http('https://restapi.amap.com/v5/place/text',{
          'key':os.environ['AMAP_KEY'],'keywords':keyword,'region':city,
          'city_limit':'true','page_size':25,'page_num':page,
          'show_fields':'business','output':'json'})
        if str(info.get('status'))!='1':
            raise RuntimeError('Amap API: '+str(info.get('info') or info.get('infocode'))[:150])
        rows=info.get('pois') or []
        if isinstance(rows,dict):rows=rows.get('poi') or []
        out=[]
        for p in rows:
            if not isinstance(p,dict):continue
            biz=p.get('business') or {}
            if not isinstance(biz,dict):biz={}
            out.append({'name':p.get('name',''),'city':p.get('cityname') or city,
               'category':p.get('type',''),'phone':biz.get('tel',''),
               'website':'','address':p.get('address',''),
               'poi_id':p.get('id','')})
        return out,25
    if provider=='baidu':
        info=json_http('https://api.map.baidu.com/place/v3/region',{
          'ak':os.environ['BAIDU_MAP_AK'],'query':keyword,'region':city,
          'region_limit':'true','page_size':20,'page_num':page-1,
          'output':'json','scope':2})
        if info.get('status') not in (0,'0'):
            raise RuntimeError('Baidu API: '+str(info.get('message') or info.get('status'))[:150])
        out=[]
        for p in info.get('results') or []:
            if not isinstance(p,dict):continue
            details=p.get('detail_info') or {}
            if not isinstance(details,dict):details={}
            out.append({'name':p.get('name',''),'city':p.get('city') or city,
                 'category':p.get('detail') or p.get('tag',''),'phone':p.get('telephone',''),
                 'website':details.get('website',''),
                 'address':p.get('address',''),'poi_id':p.get('uid','')})
        return out,20
    if provider=='osm':
        lat,lon=OSM_CENTERS[city]
        # Only explicitly tagged businesses with matching names; public Overpass can be rate-limited.
        box=f'{lat-0.25:.4f},{lon-0.33:.4f},{lat+0.25:.4f},{lon+0.33:.4f}'
        rule='机械设计|工业设计|自动化|机器人|三维|模具|机械工程|工程技术'
        q=f'''[out:json][timeout:35];(nwr["name"~"{rule}"]({box}););out center tags 150;'''
        raw=json_http('https://overpass.kumi.systems/api/interpreter',timeout=50,
                      post=urlencode({'data':q}).encode('utf-8'),retries=0)
        out=[]
        for p in raw.get('elements') or []:
            t=p.get('tags') or {}
            out.append({'name':t.get('name:zh') or t.get('name',''),'city':city,
                  'category':t.get('office') or t.get('industrial') or t.get('shop',''),
                  'phone':t.get('contact:phone') or t.get('phone',''),
                  'website':t.get('contact:website') or t.get('website',''),
                  'address':t.get('addr:full',''),
                  'poi_id':f"{p.get('type','')}:{p.get('id','')}"})
        return out,150
    raise ValueError('Unknown maps provider '+provider)


# Browser-mode discovery is intentionally opt-in. The public Google Maps UI is
# not a supported export API; consult the Maps terms before using it at scale.
# This browser component neither accesses private APIs nor evades access controls.

def browser_map_jobs(args):
    cities, words = map_queries(args)
    return [(city, word) for city in cities for word in words]


def browser_map_pending(db, args):
    if not args.browser_maps:
        return 0
    map_init(db)
    completed = {r['task_key'] for r in db.execute("SELECT task_key FROM map_tasks WHERE provider='google-browser' AND status IN ('ok','empty','error')")}
    return sum(map_task_key('google-browser', city, word, 1) not in completed
               for city, word in browser_map_jobs(args))


def _maps_blocked(page):
    url = page.url.lower()
    if any(t in url for t in ('/sorry/', '/recaptcha/', 'consent.google')):
        return True
    try:
        body = (page.locator('body').inner_text(timeout=3000) or '')[:5000].lower()
        return any(text in body for text in (
            'unusual traffic from your computer network',
            'our systems have detected unusual traffic',
            'automated queries', 'verify you are a human'))
    except Exception:
        return False


def _browser_sleep(args):
    time.sleep(random.uniform(args.browser_pause_min, args.browser_pause_max))


def _browser_first_text(page, selectors):
    for selector in selectors:
        try:
            loc=page.locator(selector).first
            if loc.count() and loc.is_visible():
                text=(loc.inner_text(timeout=1200) or '').strip()
                if text:return text[:300]
        except Exception:
            continue
    return ''


def _browser_attr(page, selectors, attr):
    for selector in selectors:
        try:
            loc=page.locator(selector).first
            if loc.count():
                value=(loc.get_attribute(attr,timeout=1200) or '').strip()
                if value:return value
        except Exception:
            continue
    return ''


def _google_maps_cards(page, args):
    # Use only user-visible result anchors: not undocumented Maps RPC endpoints.
    selectors='a.hfpxzc, div[role="feed"] a[href*="/maps/place/"], a[href*="/maps/place/"]'
    cards={}
    for step in range(args.browser_scrolls + 1):
        try:
            anchors=page.locator(selectors)
            for idx in range(min(anchors.count(),400)):
                item=anchors.nth(idx)
                href=item.get_attribute('href') or ''
                name=(item.get_attribute('aria-label') or '').strip()
                href=clean_url(href)
                if href and '/maps/place/' in href and name:
                    cards.setdefault(href,name)
                    if len(cards)>=args.browser_results_per_search:break
        except Exception:pass
        if len(cards)>=args.browser_results_per_search:break
        if step>=args.browser_scrolls:break
        try:
            page.locator('div[role="feed"]').first.evaluate('(el) => el.scrollBy(0, Math.max(700, el.clientHeight))')
        except Exception:
            page.mouse.wheel(0,900)
        _browser_sleep(args)
    return list(cards.items())[:args.browser_results_per_search]


def _google_maps_details(page, href, fallback, city, keyword, args):
    page.goto(href,wait_until='domcontentloaded',timeout=args.browser_timeout_ms)
    if _maps_blocked(page):
        raise RuntimeError('Google Maps displayed a consent, CAPTCHA, or automated-access block; stop and use a permitted source.')
    try:page.locator('h1.DUwDvf, h1').first.wait_for(timeout=9000)
    except Exception:pass
    name=_browser_first_text(page,['h1.DUwDvf','h1']) or fallback
    website=_browser_attr(page,['a[data-item-id="authority"]','a[aria-label^="Website:"]'],'href')
    if 'google.' in domain(website):website=''
    phone=_browser_attr(page,['button[data-item-id^="phone:tel:"]','button[aria-label^="Phone:"]'],'aria-label')
    phone=re.sub(r'^(Phone|Telephone|电话|联系电话)\s*[:：]\s*','',phone,flags=re.I).strip()
    address=_browser_attr(page,['button[data-item-id="address"]','button[aria-label^="Address:"]'],'aria-label')
    address=re.sub(r'^(Address|地址)\s*[:：]\s*','',address,flags=re.I).strip()
    category=_browser_first_text(page,['button.DkEaL','div.DkEaL']) or keyword
    return {'name':name,'city':city,'category':category,'phone':phone,'website':website,
            'address':address,'poi_id':href}


def run_browser_maps(db,args):
    if not args.browser_maps:return (0,0)
    map_init(db)
    try:
        from playwright.sync_api import sync_playwright
    except ImportError as exc:
        raise RuntimeError('Browser mode requires: python -m pip install playwright; python -m playwright install chromium') from exc
    all_jobs=browser_map_jobs(args)
    completed={r['task_key'] for r in db.execute("SELECT task_key FROM map_tasks WHERE provider='google-browser' AND status IN ('ok','empty','error')")}
    pending=[(city,word) for city,word in all_jobs if map_task_key('google-browser',city,word,1) not in completed]
    pending=pending[:args.browser_searches_batch]
    if not pending:
        print('[browser maps] Nothing pending within search batch.',flush=True)
        return (0,0)
    queries_done=new_candidates=raw_count=0
    print(f'[browser maps] batch={len(pending)}, total pending={browser_map_pending(db,args)}, '
          f'max visible results/search={args.browser_results_per_search}; browser API key: not required',flush=True)
    with sync_playwright() as pw:
        browser=pw.chromium.launch(headless=args.browser_headless)
        context=browser.new_context(locale='zh-CN',viewport={'width':1440,'height':1000})
        page=context.new_page()
        try:
            for city,keyword in pending:
                key=map_task_key('google-browser',city,keyword,1)
                query=f'{city} {keyword}'
                url='https://www.google.com/maps/search/?api=1&'+urlencode({'query':query})
                try:
                    page.goto(url,wait_until='domcontentloaded',timeout=args.browser_timeout_ms)
                    _browser_sleep(args)
                    if _maps_blocked(page):
                        print('[browser maps stop] Consent/CAPTCHA/block detected. No bypass attempted.',flush=True)
                        break
                    cards=_google_maps_cards(page,args)
                    if not cards:
                        # No visible results can also mean layout changed or page failed:
                        # do not mark such a search complete.
                        raise RuntimeError('No visible business-card anchors. Check map rendering/consent, or update selectors.')
                    added_here=0
                    for href,name in cards:
                        _browser_sleep(args)
                        try:
                            row=_google_maps_details(page,href,name,city,keyword,args)
                        except Exception as exc:
                            if 'block' in str(exc).lower() or 'captcha' in str(exc).lower():raise
                            event(db,'browser_maps',name,'detail_error',repr(exc))
                            continue
                        n_raw,n_new=map_store(db,row,'google-browser',city,keyword)
                        raw_count+=n_raw
                        added_here+=n_new
                        new_candidates+=n_new
                        db.commit()  # commit every record for safe Ctrl+C resume
                    db.execute('INSERT OR REPLACE INTO map_tasks VALUES(?,?,?,?,?,?,?,?)',
                               (key,'google-browser',city,keyword,1,len(cards),moment(),'ok'))
                    db.commit()
                    queries_done+=1
                    print(f'[browser maps] {city} {keyword}: listings={len(cards)}; new legal names={added_here}; '
                          f'done={queries_done}/{len(pending)}',flush=True)
                except KeyboardInterrupt:
                    print('[browser maps] Interrupted; SQLite is committed. Resume with the same command.',flush=True)
                    break
                except Exception as exc:
                    # A persistent selector/UI failure must not trap auto-continue on the same query forever.
                    db.execute('INSERT OR REPLACE INTO map_tasks VALUES(?,?,?,?,?,?,?,?)',
                        (key,'google-browser',city,keyword,1,0,moment(),'error'))
                    db.commit()
                    event(db,'browser_maps',query,'error',repr(exc))
                    print(f'[browser maps warning] {query}: {type(exc).__name__}: {str(exc)[:200]}',flush=True)
                    if 'block' in str(exc).lower() or 'captcha' in str(exc).lower():break
                    # Other failed searches are not marked completed; can be retried later.
                    break
        finally:
            context.close();browser.close()
    path=export_map_raw(db,args.out)
    print(f'[browser maps done] searches={queries_done}, raw observations={raw_count}, '
          f'new legal candidates={new_candidates}; CSV={path}',flush=True)
    return queries_done,new_candidates


def normalize_map_lead(row, provider, city, keyword):
    name=str(row.get('name') or '').strip()
    if not name or len(name)>120 or any(x in name for x in MAP_NAME_NEGATIVE):return None
    site=clean_url(row.get('website'))
    if marketplace(site):site=''
    p=str(row.get('phone') or '').strip()
    phone=next((good_contact(x.strip(),'phone') for x in re.split(r'[;,，；/]+',p)
                if good_contact(x.strip(),'phone')), '')
    return {'name':name,'city':str(row.get('city') or city)[:120],
        'official_site_hint':site,'discovery_source':'',
        'services':str(row.get('category') or keyword)[:400],
        'cad_types':'','cad_software':'','phone_hint':phone,'email_hint':'',
        'contact_hint':'','contact_form_hint':'',
        'origin_query':f'MAPS:{provider}:{city}:{keyword}',
        'map_provider':provider,'map_poi_id':str(row.get('poi_id') or '')[:200],
        'map_address':str(row.get('address') or '')[:300]}


def map_store(db,row,provider,city,keyword):
    lead=normalize_map_lead(row,provider,city,keyword)
    if not lead:return (0,0)
    name=lead['name']
    uid=str(row.get('poi_id') or '')
    if not uid:uid=norm_name(name)+'|'+city
    origin_key=provider+':'+uid
    db.execute('INSERT OR IGNORE INTO map_raw(origin_key,name,city,category,phone,website,address,provider,poi_id,added_at) '
       'VALUES(?,?,?,?,?,?,?,?,?,?)',(origin_key,name,lead['city'],lead['services'],
          lead['phone_hint'],lead['official_site_hint'],lead['map_address'],provider,uid,moment()))
    # Do not fabricate a legal company name from a short store/POI title.
    if not valid_company_name(name):return (1,0)
    return (1,int(add_candidate(db,lead)))


def export_map_raw(db,out):
    path=out.with_name(out.stem+'_map_candidates.csv')
    with path.open('w',newline='',encoding='utf-8-sig') as f:
        columns=('name','city','category','phone','website','address','provider','poi_id')
        w=csv.DictWriter(f,fieldnames=columns);w.writeheader()
        for r in db.execute('SELECT '+','.join(columns)+' FROM map_raw ORDER BY provider,city,name'):
            w.writerow(dict(r))
    return path


def run_maps(db,args):
    map_init(db)
    specs=map_specs(args)
    if args.map_source=='auto' and specs==['osm']:
        print('[maps] No Amap/Baidu API keys. Using small OpenStreetMap sample + optional imported lists; '
              'this is NOT equivalent to Chinese map-directory coverage.',flush=True)
    ncall=nraw=nnew=0
    done={r['task_key']:r for r in db.execute('SELECT * FROM map_tasks')}
    cap=args.map_lifetime_budget - counts(db).get('map_api_requests',0)
    if cap<=0 and specs:print('[maps] Map lifetime budget reached; no requests',flush=True)
    for prov,city,word,page in map_task_list(args):
        key=map_task_key(prov,city,word,page)
        if key in done:continue
        if page>1:
            prev=done.get(map_task_key(prov,city,word,page-1))
            if prev is not None and prev['count'] < (25 if prov=='amap' else 20):
                db.execute('INSERT OR IGNORE INTO map_tasks(task_key,provider,city,keyword,page,count,completed_at,status) '
                      'VALUES(?,?,?,?,?,?,?,?)',(key,prov,city,word,page,0,moment(),'empty'))
                db.commit();continue
        if ncall>=args.map_batch or ncall>=cap:break
        try:
            records,limit=map_page(prov,city,word,page,args)
            ncall+=1;put_counter(db,'map_api_requests')
            for r in records:
                rownew,candidate=map_store(db,r,prov,city,word)
                nraw+=rownew;nnew+=candidate
            db.execute('INSERT OR REPLACE INTO map_tasks VALUES(?,?,?,?,?,?,?,?)',
                       (key,prov,city,word,page,len(records),moment(),'ok'))
            db.commit()
            print(f'[maps] {prov} {city} / {word} p{page}: POIs={len(records)}, '
                  f'legal new={nnew}, requests={ncall}',flush=True)
        except Exception as exc:
            ncall+=1;put_counter(db,'map_api_requests')
            safe_error=str(exc)
            for secret in (os.environ.get('AMAP_KEY',''),os.environ.get('BAIDU_MAP_AK','')):
                if secret:safe_error=safe_error.replace(secret,'[REDACTED]')
            event(db,'maps',f'{prov}/{city}/{word}/p{page}','error',safe_error)
            db.execute('INSERT OR REPLACE INTO map_tasks VALUES(?,?,?,?,?,?,?,?)',
                       (key,prov,city,word,page,0,moment(),'failed'))
            db.commit()
            print(f'[maps warning] {prov} {city} {word}: {type(exc).__name__}: {safe_error}',flush=True)
            # Do not spin on provider authorization, quotas or rate limits.
            if prov in ('amap','baidu') or '429' in safe_error or '403' in safe_error:break
        if args.map_pause:time.sleep(args.map_pause)
    path=export_map_raw(db,args.out)
    if ncall or nraw:print(f'[maps done] map requests={ncall}, discovered POI entries={nraw}, '
                           f'new legal candidates={nnew}; raw CSV={path.name}',flush=True)
    return ncall,nnew


def import_leads(db,args):
    if not args.import_leads:return 0
    path=args.import_leads
    if not path.is_file():raise FileNotFoundError(path)
    blobhash=hashlib.sha256(path.read_bytes()).hexdigest()
    map_init(db)
    tag='import:'+blobhash
    if db.execute('SELECT 1 FROM map_tasks WHERE task_key=?',(tag,)).fetchone():return 0
    field_names={'name':('name','company','company name','business name','company_name',
                         '企业名称','公司名称','名称','title'),
       'city':('city','location','城市','cityname'),
       'phone':('phone','telephone','tel','电话','mobile','contact phone'),
       'website':('website','official website','web site','url','官网','官方网站'),
       'category':('category','services','type','specialty','focus','业务','服务'),
       'address':('address','地址'),'poi_id':('id','uid','place id','poi_id')}
    def convert(raw):
        d={str(k or '').strip().casefold():str(v or '').strip() for k,v in raw.items()}
        return {to:next((d[alias.casefold()] for alias in alternatives
                         if d.get(alias.casefold())), '') for to,alternatives in field_names.items()}
    rows=[]
    if path.suffix.lower()=='.csv':
        with path.open(encoding='utf-8-sig',newline='') as f:
            rows=[convert(row) for row in csv.DictReader(f)]
    elif path.suffix.lower()=='.xlsx':
        with ZipFile(path) as z:
            shared=read_strings(z)
            root=ET.fromstring(z.read('xl/worksheets/sheet1.xml'))
            rr=root.findall(f'.//{{{S}}}sheetData/{{{S}}}row')
            if rr:
                headers={col.lower():get_cell(c,shared) for col,c in map_cells(rr[0]).items()}
                for row in rr[1:]:
                    values={headers.get(k.lower(),''):get_cell(c,shared)
                            for k,c in map_cells(row).items()}
                    rows.append(convert(values))
    else:raise ValueError('--import-leads supports .csv or .xlsx only')
    new=0
    for row in rows:
        _,added=map_store(db,row,'import',row.get('city',''),'external list')
        new+=added
    db.execute('INSERT INTO map_tasks VALUES(?,?,?,?,?,?,?,?)',
               (tag,'import','',path.name,1,len(rows),moment(),'ok'))
    db.commit()
    export_map_raw(db,args.out)
    print(f'[import] rows={len(rows)}; NEW legal candidates={new}, file={path.name}',flush=True)
    return new


_EMAIL_SEARCH=re.compile(r'(?i)[a-z0-9._%+\-]+@[a-z0-9.\-]+\.[a-z]{2,}')
_PHONE_SEARCH=re.compile(r'(?:电话|热线|联系电话|Tel|Phone)[：:\s]*([+()0-9\- ]{7,22})',re.I)
_CAD_TERMS=('工业设计','机械设计','结构设计','三维建模','参数化建模','非标自动化设计',
            '产品设计','装配设计','SolidWorks','Creo','CATIA','机械研发')
_SERVICE_TERMS=('设计服务','研发设计','设计开发','委托设计','定制设计','技术服务',
                '机械设计','工业设计','结构设计','自动化设计','设计与制造','design service')


def quick_verify_sites(db,args):
    if not args.quick_verify:return 0
    map_init(db)
    verified=0;checks=0
    seen=result_rows(db)
    for rr in db.execute('SELECT name_key,data FROM candidates ORDER BY updated_at,name_key'):
        if checks>=args.quick_verify_batch:break
        if rr['name_key'] in seen or db.execute('SELECT 1 FROM html_checks WHERE name_key=?',(rr['name_key'],)).fetchone():
            continue
        item=json.loads(rr['data']);name=item.get('name','');url=clean_url(item.get('official_site_hint'))
        if not (valid_company_name(name) and url and not marketplace(url)):continue
        checks+=1
        fetched=_fetch_public_page(url,domain(url),timeout=10)
        status='unconfirmed'
        if fetched:
            landing,root=fetched
            body=' '.join(root.xpath('//body//text()[not(ancestor::script) and not(ancestor::style)]'))[:70000]
            # Legal identity and actual CAD design services must both be on official HTML.
            textnorm=norm_name(body)
            identity=norm_name(name) in textnorm
            cad=any(w.casefold() in body.casefold() for w in _CAD_TERMS)
            services=any(w.casefold() in body.casefold() for w in _SERVICE_TERMS)
            if identity and cad and services and domain(landing)==domain(url):
                email=next((e for e in _EMAIL_SEARCH.findall(body) if good_contact(e,'email')), '')
                phones=_PHONE_SEARCH.findall(body)
                phone=next((good_contact(v.strip(),'phone') for v in phones if good_contact(v.strip(),'phone')), '')
                result={'name':name,'city':item.get('city',''),'status':'verified',
                    'official_site':landing,'identity_url':landing,'second_source_url':'',
                    'services':item.get('services','')+'; '+next(w for w in _CAD_TERMS if w.casefold() in body.casefold()),
                    'cad_types':item.get('cad_types',''),'cad_software':item.get('cad_software',''),
                    'email':email,'phone':phone,'contact_page':'','contact_form_url':'',
                    'form_dom_verified':False,'contact_form_checked':False,
                    'contact_source_url':landing,'confidence':'high',
                    'reason':'Direct official HTML: legal name + explicit CAD design services. '
                             'No third-party corroboration; sample-check before outreach.',
                    'search_events':0,'source_count':1,'billed_search_requests':0,
                    'checked_utc':moment(),'origin_query':item.get('origin_query','')}
                store_result(db,result);verified+=1;status='verified_html'
        db.execute('INSERT OR REPLACE INTO html_checks VALUES(?,?,?)',(rr['name_key'],moment(),status))
        db.commit()
        print(f'[HTML quick-check] {name[:28]} => {status}',flush=True)
        if args.map_pause:time.sleep(args.map_pause)
    return verified


def remaining_map_tasks(db,args):
    if args.map_source=='off':return 0
    if counts(db).get('map_api_requests',0)>=args.map_lifetime_budget:return 0
    if not db.execute("SELECT name FROM sqlite_master WHERE type='table' AND name='map_tasks'").fetchone():
        return len(map_task_list(args))
    present={r['task_key'] for r in db.execute('SELECT task_key FROM map_tasks')}
    return sum(map_task_key(*t) not in present for t in map_task_list(args))


def directory_seeds_from_workbook(path):
    """Read directory-based leads from the original five-sheet workbook."""
    leads={}
    with ZipFile(path) as z:
        ss=read_strings(z)
        for idx in (2,3,4):
            root=ET.fromstring(z.read(f'xl/worksheets/sheet{idx}.xml'))
            for row in root.findall(f'.//{{{S}}}sheetData/{{{S}}}row'):
                if int(row.get('r'))==1:continue
                c=map_cells(row)
                name=get_cell(c.get('A'),ss).strip()
                if not name or len(norm_name(name))<3 or norm_name(name) in TECHNICAL_NAMES:continue
                web=get_cell(c.get('B'),ss)
                alternate=get_cell(c.get('N'),ss)
                original=web if marketplace(web) else (alternate if marketplace(alternate) else '')
                if not original:continue
                key=norm_name(name)
                if key in leads:continue
                leads[key]={
                    'name':name,'city':get_cell(c.get('C'),ss),
                    'services':get_cell(c.get('D'),ss),
                    'cad_types':get_cell(c.get('E'),ss),
                    'cad_software':get_cell(c.get('I'),ss),
                    'official_site_hint':web if not marketplace(web) else '',
                    'discovery_source':original,'directory_url':original,
                    'origin_query':'directory lead from '+('Qualified Leads' if idx==3 else ('Review' if idx==4 else 'Companies')),
                }
    return leads


def directory_should_retry(previous):
    """Only recheck incomplete or unverified previous results."""
    if not previous:return True
    return previous.get('status')!='verified' or not contactable(previous)


def directory_export(db,path,leads):
    found=result_rows(db)
    with path.open('w',encoding='utf-8-sig',newline='') as fp:
        columns=['name','city','directory_url','status','official_site','site_verification',
                 'email','phone','contact_form_url','contact_page','contact_method',
                 'unverified_email','unverified_phone','unverified_contact_page',
                 'unverified_contact_form_url','verification_attempted','reason']
        writer=csv.DictWriter(fp,fieldnames=columns)
        writer.writeheader()
        for key,firm in leads.items():
            r=found.get(key,{})
            attempt=db.execute('SELECT attempts FROM directory_checks WHERE name_key=?',(key,)).fetchone()
            writer.writerow({'name':firm['name'],'city':firm.get('city',''),
                'directory_url':firm['directory_url'],
                'status':r.get('status','unprocessed'),'official_site':r.get('official_site',''),
                'site_verification':'confirmed' if r.get('status')=='verified' else 'UNVERIFIED',
                'email':r.get('email',''),'phone':r.get('phone',''),
                'contact_form_url':r.get('contact_form_url',''),
                'contact_page':r.get('contact_page',''),
                'contact_method':contact_method(r) if r else '',
                'unverified_email':r.get('unverified_email',''),
                'unverified_phone':r.get('unverified_phone',''),
                'unverified_contact_page':r.get('unverified_contact_page',''),
                'unverified_contact_form_url':r.get('unverified_contact_form_url',''),
                'verification_attempted':int(attempt['attempts']) if attempt else 0,
                'reason':r.get('reason','')})


def run_directory_resolution(db,client,model,args,search_function,budget_fn,checkpoint_fn):
    """Run up to N concurrent Azure verifications; commit all results on main thread."""
    leads=directory_seeds_from_workbook(args.input)
    db.execute('CREATE TABLE IF NOT EXISTS directory_checks ('
               'name_key TEXT PRIMARY KEY, attempts INTEGER NOT NULL DEFAULT 0, '
               'status TEXT, checked_at TEXT)')
    db.commit()
    existing=result_rows(db)
    selected=[]
    for key,firm in leads.items():
        attempts=db.execute('SELECT attempts FROM directory_checks WHERE name_key=?',(key,)).fetchone()
        if attempts and attempts['attempts']>=args.directory_max_attempts:continue
        if not directory_should_retry(existing.get(key)):continue
        selected.append((key,firm))
    print(f'[directory] total directory leads={len(leads)}, pending eligible={len(selected)}, workers={args.directory_workers}; '
          'existing SQLite results respected',flush=True)
    directory_export(db,args.out.with_name(args.out.stem+'_directory_audit.csv'),leads)
    done=0
    index=0
    while index<len(selected) and budget_fn():
        slots=min(args.directory_workers,len(selected)-index)
        # Conservative headroom; actual Bing usage is reported after the call.
        if args._get_directory_budget is not None:
            api_left, web_left=args._get_directory_budget()
            slots=min(slots,api_left,max(0,int(web_left//80)))
        if slots<1:break
        batch=selected[index:index+slots]
        index+=slots
        futures={}
        with ThreadPoolExecutor(max_workers=slots) as executor:
            for key,firm in batch:
                db.execute('INSERT INTO directory_checks(name_key,attempts,status,checked_at) VALUES(?,1,?,?) '
                           'ON CONFLICT(name_key) DO UPDATE SET attempts=attempts+1,status=excluded.status,checked_at=excluded.checked_at',
                           (key,'started',moment()))
                db.commit()
                args._count_directory_call()
                futures[executor.submit(verify,client,model,firm,args.reasoning_effort)]=(key,firm)
                if args.pause_max:time.sleep(random.uniform(args.pause_min,args.pause_max))
            for future in as_completed(futures):
                key,firm=futures[future]
                try:
                    result=future.result()
                    result['directory_url']=firm['directory_url']
                    args._record_directory_usage(result)
                    store_result(db,result)
                    db.execute('UPDATE directory_checks SET status=?,checked_at=? WHERE name_key=?',
                               (result['status'],moment(),key))
                    db.commit()
                    existing[key]=result
                    event(db,'directory_resolve',firm['name'],result['status'],result.get('official_site',''))
                    print(f'[directory] {firm["name"][:36]} -> {result["status"]}: {result.get("official_site","")}',flush=True)
                except Exception as exc:
                    db.execute('UPDATE directory_checks SET status=?,checked_at=? WHERE name_key=?',
                               (type(exc).__name__,moment(),key))
                    db.commit()
                    event(db,'directory_resolve',firm['name'],'error',repr(exc))
                    print(f'[directory warning] {firm["name"]}: {type(exc).__name__}: {exc}',file=sys.stderr,flush=True)
                    if type(exc).__name__ in {'RateLimitError','AuthenticationError','PermissionDeniedError','BadRequestError','NotFoundError'}:
                        args._directory_fatal=type(exc).__name__+': '+str(exc)[:140]
                done+=1
        directory_export(db,args.out.with_name(args.out.stem+'_directory_audit.csv'),leads)
        checkpoint_fn()
        if args._directory_fatal:break
    current=result_rows(db)
    return sum(1 for k,f in leads.items() if directory_should_retry(current.get(k))
               and (not (r:=db.execute('SELECT attempts FROM directory_checks WHERE name_key=?',(k,)).fetchone())
                    or r['attempts']<args.directory_max_attempts))


def auto_continue(args):
    """Start finite, auditable runs. Reset ONLY local counters, not Azure quotas."""
    report_path=args.out.with_name(args.out.stem+'_cycle_report.json')
    if args.retry_failed_verifications or args.browser_retry_errors:
        state_path=args.state or args.out.with_name(args.out.stem+'_state.sqlite3')
        db=connect_db(state_path)
        if args.retry_failed_verifications:
            print(f'[verify retries reset] {reset_verification_failures(db)}',flush=True)
        if args.browser_retry_errors:
            map_init(db)
            db.execute("DELETE FROM map_tasks WHERE provider='google-browser' AND status='error'")
            db.commit()
            print('[browser maps] Cleared previously failed browser-search tasks',flush=True)
        db.close()
    total_api=0
    total_web=0
    last_remaining=None
    started=0
    for cycle in range(1,args.max_cycles+1):
        remaining_api=args.total_api_budget-total_api
        remaining_web=args.total_web_budget-total_web
        if remaining_api<=0 or remaining_web<=0:
            print(f'[auto stop] overall budget reached (API={total_api}, Bing={total_web})',flush=True)
            break
        per_api=min(args.max_api_calls,remaining_api)
        per_web=min(args.max_web_requests,remaining_web)
        # Args inherited from the invoking command; trailing flags override per-cycle budgets.
        argv=list(sys.argv[1:])
        # Strip supervisor-only arguments, supporting both "--name value" and "--name=value".
        no_value={'--auto-continue','--retry-failed-verifications','--browser-retry-errors'}
        valued={'--total-api-budget','--total-web-budget','--max-cycles','--cooldown-seconds'}
        child=[]
        idx=0
        while idx<len(argv):
            arg=argv[idx]
            flag=arg.split('=',1)[0]
            if flag in no_value:
                idx+=1;continue
            if flag in valued:
                idx+=1 if '=' in arg else 2
                continue
            child.append(arg)
            idx+=1
        child.extend(['--max-api-calls',str(per_api),
                      '--max-web-requests',str(per_web),
                      '--_cycle-report',str(report_path)])
        if args.phase=='both' and args.discovery_batch==0 and not args.no_azure_discovery:
            child.extend(['--discovery-batch','5'])
        if report_path.exists():report_path.unlink()
        print(f'\n[auto cycle {cycle}/{args.max_cycles}] per-cycle API ≤ {per_api}, '
              f'Bing target ≤ {per_web}; overall used API={total_api}, Bing={total_web}',flush=True)
        result=subprocess.run([sys.executable,'-u',str(Path(__file__).resolve()),*child],check=False)
        if result.returncode!=0:
            print(f'[auto stop] worker exit code {result.returncode}; state retained',flush=True)
            return result.returncode
        if not report_path.exists():
            print('[auto stop] worker report missing; stopping to avoid untracked charges',flush=True)
            return 1
        try:report=json.loads(report_path.read_text(encoding='utf-8'))
        except Exception:
            print('[auto stop] corrupt run report; stopping to protect budget',flush=True)
            return 1
        used_api=int(report.get('api_calls',0))
        used_web=int(report.get('billed_requests',0))
        total_api+=used_api
        total_web+=used_web
        started+=1
        if report.get('excel_pending'):
            print('[auto warning] Main Excel remains locked; current data is in SQLite '
                  'and in a .pending.xlsx file. Close Excel to allow the next checkpoint to publish.',flush=True)
        if report.get('unknown_billed',0):
            print('[auto stop] Bing billing count unavailable: cannot enforce overall search budget',flush=True)
            break
        if report.get('halt_reason'):
            print('[auto stop] Azure/configuration error; do NOT automatically retry rate limits: '+report['halt_reason'],flush=True)
            break
        pending_verify=int(report.get('pending_verify',0))
        pending_discovery=int(report.get('pending_discovery',0))
        pending_maps=int(report.get('pending_maps',0))
        pending_directory=int(report.get('pending_directory',0))
        pending_browser=int(report.get('pending_browser_maps',0))
        pending=pending_maps+pending_browser+(pending_directory if args.resolve_directory_links else 0)+(pending_verify if args.phase in ('verify','both') and not args.maps_only else 0)+(
                pending_discovery if args.phase in ('discover','both') and not args.maps_only else 0)
        print(f'[auto cycle complete] API {used_api}; Bing {used_web}; '
              f'cumulative API {total_api}/{args.total_api_budget}, '
              f'Bing {total_web}/{args.total_web_budget}; '
              f'pending directory={pending_directory}, verify={pending_verify}, discovery={pending_discovery}, maps={pending_maps}, browser={pending_browser}',flush=True)
        if pending<=0:
            print('[auto done] no work left in selected phase',flush=True)
            break
        if used_api==0 and not int(report.get('map_requests',0)) and not int(report.get('browser_map_searches',0)) and not int(report.get('map_imported',0)):
            print('[auto stop] no API/map calls in cycle — possible cap, failed source or empty queue',flush=True)
            break
        if total_api>=args.total_api_budget or total_web>=args.total_web_budget:
            print('[auto stop] overall budget reached; resume manually after checking usage',flush=True)
            break
        if cycle<args.max_cycles:
            print(f'[auto pause] {args.cooldown_seconds}s before next cycle (not an Azure quota reset)',flush=True)
            time.sleep(args.cooldown_seconds)
    print(f'[auto finished] cycles={started}; API calls={total_api}; billed Bing requests={total_web}; '
          'SQLite and Excel preserved. Check Azure billing separately.',flush=True)
    return 0


def main():
    p=argparse.ArgumentParser(description='Azure-first Chinese CAD company finder + contacts, keeps original Excel formatting')
    p.add_argument('--input',type=Path,required=True,help='Original immutable 5-sheet Excel template')
    p.add_argument('--out',type=Path,default=Path('china_cad_azure_discovered.xlsx'))
    p.add_argument('--state',type=Path,default=None,help='SQLite state; default <out>_state.sqlite3')
    p.add_argument('--model',default='',help='Azure deployment or AZURE_OPENAI_DEPLOYMENT')
    p.add_argument('--map-source',choices=['off','auto','amap','baidu','osm','all'],default='off',
                   help='Maps-first source; auto uses Amap/Baidu keys or small OSM fallback')
    p.add_argument('--maps-only',action='store_true',help='Collect/import map POIs without Azure charges')
    p.add_argument('--browser-maps',action='store_true',help='EXPERIMENTAL: visible Google Maps browser results, no Maps API; review platform terms')
    p.add_argument('--browser-headless',action='store_true',help='Use headless Chromium (default is visible browser)')
    p.add_argument('--browser-searches-batch',type=int,default=10,help='Browser map queries per execution')
    p.add_argument('--browser-results-per-search',type=int,default=15,help='Max visible business cards checked per browser query')
    p.add_argument('--browser-scrolls',type=int,default=5,help='Max visible results-feed scrolls per query')
    p.add_argument('--browser-timeout-ms',type=int,default=30000,help='Browser navigation timeout milliseconds')
    p.add_argument('--browser-pause-min',type=float,default=2.0)
    p.add_argument('--browser-pause-max',type=float,default=5.0)
    p.add_argument('--map-cities-file',type=Path,help='UTF-8 Chinese cities, one per line')
    p.add_argument('--map-keywords-file',type=Path,help='UTF-8 map keywords, one per line')
    p.add_argument('--map-pages',type=int,default=4,help='Up to N pages per city/keyword, per provider')
    p.add_argument('--map-batch',type=int,default=20,help='Max map HTTP requests per cycle')
    p.add_argument('--map-lifetime-budget',type=int,default=2000,
                   help='Lifetime HTTP map request cap in same SQLite (to increase, set larger value)')
    p.add_argument('--map-pause',type=float,default=2.0,help='Seconds between map requests')
    p.add_argument('--osm-city-limit',type=int,default=5,
                   help='Public OSM only: maximum number of cities sampled (small by design)')
    p.add_argument('--import-leads',type=Path,help='Import Google Maps/directory leads from CSV/XLSX')
    p.add_argument('--quick-verify',action='store_true',
                   help='Verify site-provided legal names and CAD services through own HTML, no Azure')
    p.add_argument('--quick-verify-batch',type=int,default=15,
                   help='Max candidate websites inspected per cycle')
    p.add_argument('--no-azure-discovery',action='store_true',
                   help='Skip the limited eight-hints-per-query Azure discovery; verify map candidates only')

    p.add_argument('--query-file',type=Path,help='Optional UTF-8 Chinese search queries, one per line')
    p.add_argument('--expanded-discovery',action='store_true',help='Expand the original 280 queries with 2196 new CAD-focused searches; preserves prior cache keys')
    p.add_argument('--phase',choices=['both','discover','verify'],default='both')
    p.add_argument('--resolve-directory-links',action='store_true',help='Find official sites/contact methods for original Qualified Leads and Review directory listings')
    p.add_argument('--directory-workers',type=int,default=10,help='Parallel directory-company verification (1..10)')
    p.add_argument('--directory-max-attempts',type=int,default=2,help='Maximum verification attempts per directory lead in this SQLite state')
    p.add_argument('--enrich-existing',action='store_true',help='Also verify original 769 master leads after finding new leads')
    p.add_argument('--retry-failed-verifications',action='store_true',help='Reset retry counter for Azure verification errors, e.g. empty JSON')
    p.add_argument('--browser-retry-errors',action='store_true',help='Retry skipped Maps queries and clear paused browser source marker')
    p.add_argument('--recheck-contact-forms',action='store_true',help='Recheck verified sites without validated contact forms')
    p.add_argument('--refresh-cached-forms',action='store_true',help='Inspect already cached form URLs via public HTML (no Azure calls)')
    p.add_argument('--rebuild-from-cache',action='store_true',help='Rebuild Excel/Stats and audit from SQLite without Azure calls')
    p.add_argument('--include-review',action='store_true',help='Also revisit original Review entries (expensive)')
    p.add_argument('--limit-queries',type=int,default=16,help='0=all queries; defaults to a diverse 16-query test')
    p.add_argument('--max-api-calls',type=int,default=100,help='Limit model requests per run, not web searches')
    p.add_argument('--max-web-requests',type=int,default=500,help='Approximate Bing search budget per run if Azure returns billed counts')
    p.add_argument('--max-new-firms',type=int,default=0,help='Stop after this many verified NEW companies, 0=unlimited')
    p.add_argument('--enrich-missing-contacts',action='store_true',
                   help='Download verified official site/contact pages and backfill public email/phone without Azure')
    p.add_argument('--contact-workers',type=int,default=6,help='Parallel website contact extraction, 1..12')
    p.add_argument('--contact-pages',type=int,default=4,help='Max pages per official website, 1..8')
    p.add_argument('--contact-timeout',type=float,default=12.0,help='HTTP timeout per page in seconds')
    p.add_argument('--contact-limit',type=int,default=500,help='Max company websites extracted per run (0=all)')
    p.add_argument('--contact-cache-hours',type=float,default=24.0,help='Cache unsuccessful extraction before retry (0=refresh)')
    p.add_argument('--site-check-workers',type=int,default=8,help='Parallel public website checks, 1..16')
    p.add_argument('--site-check-timeout',type=float,default=10.0,help='Per-website HTTP timeout, seconds')
    p.add_argument('--site-check-cache-hours',type=float,default=24.0,
                   help='Reuse website reachability checks for this many hours (0 forces refresh)')
    p.add_argument('--auto-continue',action='store_true',help='Run successive finite cycles using the same SQLite state')
    p.add_argument('--total-api-budget',type=int,default=500,help='TOTAL API call cap across all auto cycles')
    p.add_argument('--total-web-budget',type=int,default=8000,help='TOTAL observed Bing request cap across auto cycles')
    p.add_argument('--max-cycles',type=int,default=10,help='Maximum number of auto cycles')
    p.add_argument('--cooldown-seconds',type=float,default=15.0,help='Pause between cycles (not quota reset)')
    p.add_argument('--discovery-batch',type=int,default=0,help='Max NEW discovery queries per cycle; 0=unlimited')
    p.add_argument('--discovery-workers',type=int,default=5,
                   help='Parallel Azure Discovery searches, 1..5 (default 5)')
    p.add_argument('--verify-workers',type=int,default=4,
                   help='Parallel Azure verification calls for newly discovered map/CAD candidates, 1..5 (default 4)')
    p.add_argument('--_cycle-report',type=Path,default=None,help=argparse.SUPPRESS)
    p.add_argument('--checkpoint-every',type=int,default=10,help='Save Excel every N model calls')
    p.add_argument('--reasoning-effort',choices=['low','medium','high'],default='',
                   help='Optional; leave unset for deployment compatibility')
    p.add_argument('--pause-min',type=float,default=2.0,help='Pause between Azure requests, seconds (default 2)')
    p.add_argument('--pause-max',type=float,default=5.0,help='Maximum pause in seconds (default 5)')
    p.add_argument('--plan',action='store_true',help='Show planned searches; NO API use or output file')
    p.add_argument('--probe',action='store_true',help='One live discovery search, then exit; no Excel modifications')
    args=p.parse_args()
    if not args.input.exists():p.error('Missing source: '+str(args.input))
    if args.input.resolve()==args.out.resolve():p.error('Input and output cannot be the same file')
    if args.max_api_calls<1 or args.max_web_requests<1 or args.checkpoint_every<1:p.error('Budget/checkpoint limits must be positive')
    if args.pause_min<0 or args.pause_max<args.pause_min:p.error('Invalid pause range')
    if not 1<=args.discovery_workers<=5:p.error('--discovery-workers must be 1..5')
    if not 1<=args.verify_workers<=5:p.error('--verify-workers must be 1..5')
    if not (1<=args.contact_workers<=12 and 1<=args.contact_pages<=8 and
            1<=args.contact_timeout<=90 and args.contact_limit>=0 and args.contact_cache_hours>=0):
        p.error('Invalid contact enrichment settings')
    if not 1<=args.site_check_workers<=16 or not 1<=args.site_check_timeout<=90 or args.site_check_cache_hours<0:
        p.error('Invalid site-check workers, timeout or cache settings')
    if not 1<=args.directory_workers<=10 or args.directory_max_attempts<1:p.error('Invalid directory worker/attempt settings')
    if args.max_cycles<1 or args.total_api_budget<1 or args.total_web_budget<1:
        p.error('Auto budget/cycle counts must be positive')
    if args.cooldown_seconds<0 or args.discovery_batch<0:p.error('Invalid cooldown or discovery batch')
    if args.map_batch<1 or args.map_pages<1 or args.map_pages>8 or args.map_pause<0 or args.osm_city_limit<0 or args.map_lifetime_budget<1:
        p.error('Invalid maps limits')
    if args.browser_searches_batch<1 or args.browser_results_per_search<1 or args.browser_scrolls<0 or args.browser_timeout_ms<1000:
        p.error('Invalid browser map batch/result/scroll/timeout limits')
    if args.browser_pause_min<0 or args.browser_pause_max<args.browser_pause_min:
        p.error('Invalid browser pause range')
    if args.maps_only and args.probe:p.error('--maps-only cannot be combined with --probe')
    if args.auto_continue and (args.probe or args.plan or args.rebuild_from_cache):
        p.error('--auto-continue cannot be combined with --probe, --plan or --rebuild-from-cache')

    known,master,rows=input_firms(args.input)
    queries=make_queries(args.query_file,args.expanded_discovery)
    print(f'[input] {rows} source rows; {len(known)} unique names; {len(master)} primary leads')
    print(f'[queries] {len(queries)} prepared; phase={args.phase}')
    if args.plan:
        if args.map_source!='off':
            try:
                tasks=map_task_list(args)
                print(f'[maps plan] provider(s)={map_specs(args)}; pages={len(tasks)}; '
                      f'per-cycle batch={args.map_batch}; lifetime budget={args.map_lifetime_budget}')
                for task in tasks[:8]:print('  [map]',task)
            except Exception as exc:print(f'[maps plan ERROR] {exc}')
        if args.browser_maps:
            print(f'[browser maps plan] searches={len(browser_map_jobs(args))}, '
                  f'per run={args.browser_searches_batch}, per search={args.browser_results_per_search}')
            for city,word in browser_map_jobs(args)[:5]:print('  [browser map]',city,word)
        for q in queries[:args.limit_queries or len(queries)]:print('  -',q)
        return
    state_path=args.state or args.out.with_name(args.out.stem+'_state.sqlite3')
    if args.rebuild_from_cache:
        if not state_path.exists():p.error('SQLite state not found: '+str(state_path))
        db=connect_db(state_path)
        if args.refresh_cached_forms:
            changes=refresh_cached_forms(db)
            print(f'[cached forms] {dict(changes)}',flush=True)
        if args.enrich_missing_contacts:
            backfill_website_contacts(db,args)
        outcomes=export_review(db,args.out.with_name(args.out.stem+'_audit.csv'))
        added,changes,conflicts,excel_saved=patch_workbook(args.input,args.out,result_rows(db),db,args)
        print(f'[rebuild] new firms={added}; writes={changes}; domain conflicts={conflicts}; '
              f'Stats refreshed in {"main Excel" if excel_saved else "pending Excel"}; '
              f'outcomes={dict(outcomes)}; no Azure API calls',flush=True)
        db.close()
        if not excel_saved:
            sys.exit('[rebuild] Main Excel was locked; close it and retry --rebuild-from-cache')
        return
    if args.auto_continue:
        return auto_continue(args)
    if args.maps_only:
        db=connect_db(state_path)
        added=import_leads(db,args)
        requests,from_maps=run_maps(db,args)
        browser_calls,browser_new=run_browser_maps(db,args)
        html_ok=quick_verify_sites(db,args)
        outcomes=export_review(db,args.out.with_name(args.out.stem+'_audit.csv'))
        added_excel,changes,conflicts,saved=patch_workbook(args.input,args.out,result_rows(db),db,args)
        pending=remaining_map_tasks(db,args)
        pending_browser=browser_map_pending(db,args)
        print(f'[maps-only done] map requests={requests}, new legal POIs={from_maps}, '
              f'imported={added}, HTML verified={html_ok}, pending map pages={pending}; browser searches={browser_calls}, pending browser={pending_browser}; '
              f'Excel={"saved" if saved else "pending"}; no Azure requests',flush=True)
        if args._cycle_report:
            summary={'api_calls':0,'billed_requests':0,'unknown_billed':0,'map_requests':requests,
                     'map_imported':added,'pending_maps':pending,'pending_browser_maps':pending_browser,
                     'browser_map_searches':browser_calls,'pending_verify':0,
                     'pending_discovery':0,'halt_reason':'','excel_pending':not saved,'utc':moment()}
            args._cycle_report.write_text(json.dumps(summary),encoding='utf-8')
        db.close();return
    endpoint=base_url(os.environ.get('AZURE_OPENAI_ENDPOINT'))
    token=os.environ.get('AZURE_OPENAI_API_KEY','').strip()
    model=args.model or os.environ.get('AZURE_OPENAI_DEPLOYMENT','').strip()
    if not endpoint or not token or not model:
        sys.exit('Set AZURE_OPENAI_ENDPOINT, AZURE_OPENAI_API_KEY, AZURE_OPENAI_DEPLOYMENT in PowerShell. Never paste keys into code/chat.')
    from openai import OpenAI
    client=OpenAI(api_key=token,base_url=endpoint,timeout=180.0,max_retries=2)
    db=connect_db(state_path)
    if args.retry_failed_verifications:
        print(f'[verify retries reset] {reset_verification_failures(db)}',flush=True)
    if args.browser_retry_errors:
        map_init(db)
        db.execute("DELETE FROM map_tasks WHERE provider='google-browser' AND status='error'")
        db.commit()
        print('[browser maps] Cleared failed browser searches',flush=True)
    imported_now=import_leads(db,args)
    map_calls,map_new=run_maps(db,args)
    browser_calls,browser_new=run_browser_maps(db,args)
    html_verified=quick_verify_sites(db,args)
    calls=0;billed=0;search_events=0;unknown_billed=0;halt_reason=''
    excel_pending=False

    def one_search(func,label,*fnargs):
        nonlocal calls,billed,search_events,unknown_billed
        print(f'[azure] {label}',flush=True)
        calls+=1  # include failed/charged attempts in per-run request budget
        answer,events,billing,sources=func(client,model,*fnargs,args.reasoning_effort)
        search_events+=events
        if billing is None:
            unknown_billed+=1
            if unknown_billed==1:
                print('[warning] Azure omitted billed Bing request count; '
                      '--max-web-requests cannot be guaranteed. --max-api-calls remains enforced.',flush=True)
        else:billed+=int(billing)
        put_counter(db,'api_calls')
        put_counter(db,'web_search_events',events)
        if billing is not None:put_counter(db,'billed_bing_requests',int(billing))
        else:put_counter(db,'responses_without_billing_count')
        if args.pause_max:time.sleep(random.uniform(args.pause_min,args.pause_max))
        return answer,events,billing,sources

    def budget():
        return calls<args.max_api_calls and billed<args.max_web_requests

    args._get_directory_budget=lambda: (max(0,args.max_api_calls-calls),max(0,args.max_web_requests-billed))
    args._directory_fatal=''
    def directory_count_call():
        nonlocal calls
        calls+=1
    def directory_record_usage(result):
        nonlocal billed,search_events,unknown_billed
        ev=int(result.get('search_events') or 0)
        bing=result.get('billed_search_requests')
        search_events+=ev
        put_counter(db,'api_calls')
        put_counter(db,'web_search_events',ev)
        if bing is None:
            unknown_billed+=1
            put_counter(db,'responses_without_billing_count')
        else:
            billed+=int(bing)
            put_counter(db,'billed_bing_requests',int(bing))
    args._count_directory_call=directory_count_call
    args._record_directory_usage=directory_record_usage

    def checkpoint():
        nonlocal excel_pending
        if args.enrich_missing_contacts:
            backfill_website_contacts(db,args)
        stats=export_review(db,args.out.with_name(args.out.stem+'_audit.csv'))
        added,changed,conflicts,excel_saved=patch_workbook(args.input,args.out,result_rows(db),db,args)
        excel_pending=not excel_saved
        print(f'[checkpoint] newly verified firms={added}; updates/insertions={changed}; domain conflicts={conflicts}; '
              f'Excel={"saved" if excel_saved else "pending (file locked)"}; '
              f'Azure calls={calls}; Bing requests={billed if not unknown_billed else "partial " + str(billed)}; '
              f'outcomes={dict(stats)}',flush=True)

    if args.probe:
        q=queries[0]
        try:
            firms,ev,bing,src=one_search(discover,q,q)
            print(f'[probe OK] companies={len(firms)}, search_events={ev}, '
                  f'billed_Bing_requests={bing}, source_urls={src}')
            for r in firms[:5]:print('  ',r['name'],r['official_site_hint'])
        except Exception as exc:sys.exit(f'[probe ERROR] {type(exc).__name__}: {exc}')
        return

    if args.phase in ('both','discover') and not args.no_azure_discovery:
        completed={r['key'] for r in db.execute('SELECT key FROM queries WHERE completed_at IS NOT NULL')}
        todo=queries[:args.limit_queries] if args.limit_queries else queries
        if args.discovery_batch:
            todo=[q for q in todo if hashlib.sha256(q.encode('utf-8')).hexdigest() not in completed][:args.discovery_batch]
        if args.discovery_workers>1:
            remaining_now=sum(hashlib.sha256(q.encode('utf-8')).hexdigest() not in completed for q in todo)
            print(f'[parallel discovery] workers={args.discovery_workers}; '
                  f'discovery queries available={remaining_now}; '
                  'SQLite writes remain single-threaded',flush=True)
        if args.discovery_workers > 1:
            # IMPORTANT: only Azure HTTP calls run on workers. All SQLite/Excel
            # operations run on this main thread, preventing database contention.
            pending_queries=[q for q in todo if hashlib.sha256(q.encode('utf-8')).hexdigest() not in completed]
            index=0
            last_checkpoint=calls
            with ThreadPoolExecutor(max_workers=args.discovery_workers) as executor:
                while index < len(pending_queries) and budget() and not halt_reason:
                    # Bing usage is reported only AFTER a model call. Keep headroom
                    # for in-flight searches (80 is a conservative estimate, not a hard cap).
                    room_api=args.max_api_calls-calls
                    room_web=args.max_web_requests-billed
                    size=min(args.discovery_workers, room_api,
                             max(0,int(room_web//80)),len(pending_queries)-index)
                    if size<=0:
                        print('[parallel discovery] Stopping early to keep estimated Bing headroom. '
                              'Actual search billing is only known after a response.',flush=True)
                        break
                    batch=pending_queries[index:index+size]
                    index+=size
                    futures={}
                    for j,q in enumerate(batch):
                        print(f'[azure parallel {j+1}/{size}] {q}',flush=True)
                        # Count submitted calls before execution so API-call cap
                        # includes requests that later fail or time out.
                        calls+=1
                        futures[executor.submit(discover,client,model,q,args.reasoning_effort)]=q
                        if j+1<size and args.pause_max:
                            time.sleep(random.uniform(args.pause_min,args.pause_max))
                    for future in as_completed(futures):
                        q=futures[future]
                        key=hashlib.sha256(q.encode('utf-8')).hexdigest()
                        try:
                            firms,ev,bing,src=future.result()
                            search_events+=ev
                            if bing is None:
                                unknown_billed+=1
                                if unknown_billed==1:
                                    print('[warning] Missing Bing usage; search budget is only approximate.',flush=True)
                            else:
                                billed+=int(bing)
                            put_counter(db,'api_calls')
                            put_counter(db,'web_search_events',ev)
                            if bing is None:put_counter(db,'responses_without_billing_count')
                            else:put_counter(db,'billed_bing_requests',int(bing))
                            new=0
                            for firm in firms:
                                if add_candidate(db,firm):new+=1
                            db.execute('INSERT INTO queries(key,query,completed_at,search_events,billed_requests,candidates) '
                                       'VALUES(?,?,?,?,?,?) ON CONFLICT(key) DO UPDATE SET completed_at=excluded.completed_at',
                                       (key,q,moment(),ev,bing,len(firms)))
                            db.commit()
                            event(db,'discovery',q,'ok',f'{len(firms)} hints, {new} new; Bing={bing}')
                            print(f'[discovery] {len(firms)} legal-name hints; {new} unique NEW to state; '
                                  f'Azure calls={calls}; Bing={billed}',flush=True)
                        except Exception as exc:
                            event(db,'discovery',q,'error',repr(exc))
                            print(f'[warning] discovery {q}: {type(exc).__name__}: {exc}',
                                  file=sys.stderr,flush=True)
                            if (type(exc).__name__ in {'AuthenticationError','PermissionDeniedError',
                                    'BadRequestError','NotFoundError','RateLimitError'}
                                    or 'did not call web_search' in str(exc)):
                                halt_reason=type(exc).__name__+': '+str(exc)[:140]
                    if calls-last_checkpoint>=args.checkpoint_every:
                        checkpoint()
                        last_checkpoint=calls
        else:
            for q in todo:
                key=hashlib.sha256(q.encode('utf-8')).hexdigest()
                if key in completed:continue
                if not budget():break
                try:
                    firms,ev,bing,src=one_search(discover,q,q)
                    new=0
                    for firm in firms:
                        if add_candidate(db,firm):new+=1
                    db.execute('INSERT INTO queries(key,query,completed_at,search_events,billed_requests,candidates) '
                               'VALUES(?,?,?,?,?,?) ON CONFLICT(key) DO UPDATE SET completed_at=excluded.completed_at',
                               (key,q,moment(),ev,bing,len(firms)))
                    db.commit()
                    event(db,'discovery',q,'ok',f'{len(firms)} hints, {new} new; Bing={bing}')
                    print(f'[discovery] {len(firms)} legal-name hints; {new} unique NEW to state',flush=True)
                except Exception as exc:
                    event(db,'discovery',q,'error',repr(exc))
                    print(f'[warning] {type(exc).__name__}: {exc}',file=sys.stderr,flush=True)
                    # Configuration errors and missing web search should stop, rather than flooding API.
                    if (type(exc).__name__ in {'AuthenticationError','PermissionDeniedError','BadRequestError','NotFoundError','RateLimitError'}
                            or 'did not call web_search' in str(exc)):
                        halt_reason=type(exc).__name__+': '+str(exc)[:140]
                        break
                if calls and calls%args.checkpoint_every==0:checkpoint()

    directory_pending=0
    if args.resolve_directory_links and args.phase in ('both','verify') and not halt_reason:
        directory_pending=run_directory_resolution(db,client,model,args,None,budget,checkpoint)
        if args._directory_fatal:halt_reason=args._directory_fatal

    if args.phase in ('both','verify') and not halt_reason and not args.resolve_directory_links:
        if args.enrich_existing:
            # only the master sheet unless explicitly told to expand to Review
            seeds=known if args.include_review else master
            for key,v in seeds.items():
                if not legal(v['name']) or (v.get('official_site_hint') and not marketplace(v['official_site_hint'])):continue
                add_candidate(db,v)
            db.commit()
        if args.refresh_cached_forms:
            changes=refresh_cached_forms(db)
            print(f'[cached forms] {dict(changes)}',flush=True)
        seen=result_rows(db)
        queue=[]
        for row in db.execute('SELECT name_key,data FROM candidates ORDER BY updated_at,name_key'):
            recheck=(args.recheck_contact_forms and row['name_key'] in seen and
                     seen[row['name_key']].get('status')=='verified' and
                     not contactable(seen[row['name_key']]) and
                     not seen[row['name_key']].get('contact_form_checked'))
            failed=db.execute('SELECT attempts FROM verification_failures WHERE name_key=?',(row['name_key'],)).fetchone()
            if failed and failed['attempts']>=2:continue
            if row['name_key'] not in seen or recheck:
                c=json.loads(row['data'])
                # Prefer research of LEGAL firms rather than short store aliases.
                if legal(c['name']):queue.append(c)
        queue.sort(key=lambda firm: (not str(firm.get('origin_query','')).startswith('MAPS:google-browser:'),
                                     str(firm.get('name',''))))
        print(f'[verify] pending={len(queue)}; workers={args.verify_workers}; '
              f'verified already={sum(v.get("status")=="verified" for v in seen.values())}')
        if args.verify_workers>1:
            # Concurrency is restricted to API calls; SQLite and Excel stay on main thread.
            # Each batch is bounded so the supervisor can account for returned Bing usage.
            pos=0
            with ThreadPoolExecutor(max_workers=args.verify_workers) as executor:
                while pos<len(queue) and budget() and not halt_reason:
                    headroom=min(args.verify_workers,args.max_api_calls-calls,
                                 max(0,(args.max_web_requests-billed)//80),len(queue)-pos)
                    if headroom<=0:
                        print('[verify parallel] Bing headroom too small for a new batch',flush=True)
                        break
                    batch=queue[pos:pos+headroom]
                    pos+=headroom
                    futures={}
                    for firm in batch:
                        calls+=1
                        futures[executor.submit(verify,client,model,firm,args.reasoning_effort)]=firm
                        print(f'[verify parallel] {firm["name"]}',flush=True)
                        if args.pause_max:time.sleep(random.uniform(args.pause_min,args.pause_max))
                    for future in as_completed(futures):
                        firm=futures[future]
                        label=firm['name']
                        try:
                            res=future.result()
                            ev=int(res.get('search_events') or 0)
                            bing=res.get('billed_search_requests')
                            search_events+=ev
                            if bing is None:
                                unknown_billed+=1
                                if unknown_billed==1:
                                    print('[warning] Bing count unavailable; budget approximate',flush=True)
                            else:billed+=int(bing)
                            put_counter(db,'api_calls');put_counter(db,'web_search_events',ev)
                            if bing is None:put_counter(db,'responses_without_billing_count')
                            else:put_counter(db,'billed_bing_requests',int(bing))
                            store_result(db,res)
                            seen[norm_name(label)]=res
                            event(db,'verification',label,res['status'],res.get('reason',''))
                            print(f'[verified parallel] {label} => {res["status"]}: {res["official_site"]}',flush=True)
                        except Exception as exc:
                            mark_verification_failure(db,label,exc)
                            event(db,'verification',label,'error',repr(exc))
                            print(f'[verify warning] {label}: {type(exc).__name__}: {exc}',file=sys.stderr,flush=True)
                            if type(exc).__name__ in {'AuthenticationError','PermissionDeniedError',
                                                       'BadRequestError','NotFoundError','RateLimitError'} or 'did not call web_search' in str(exc):
                                halt_reason=type(exc).__name__+': '+str(exc)[:140]
                    if calls and calls%args.checkpoint_every < len(batch):checkpoint()
            queue=[]
        for firm in queue:
            if not budget():break
            if args.max_new_firms:
                verified_new=sum(v['status']=='verified' and k not in master for k,v in seen.items())
                if verified_new>=args.max_new_firms:break
            label=firm['name']
            try:
                # Verification is exactly ONE Azure model call. Count it before execution,
                # including failures, so the configured request budget is enforced.
                calls+=1
                prompt_return=verify(client,model,firm,args.reasoning_effort)
                ev=int(prompt_return.get('search_events') or 0)
                search_events+=ev
                bing=prompt_return.get('billed_search_requests')
                if bing is None:
                    unknown_billed+=1
                    if unknown_billed==1:
                        print('[warning] Azure omitted billed Bing request count; '
                              '--max-web-requests cannot be guaranteed. --max-api-calls remains enforced.',flush=True)
                else:billed+=int(bing)
                put_counter(db,'api_calls');put_counter(db,'web_search_events',ev)
                if bing is None:put_counter(db,'responses_without_billing_count')
                else:put_counter(db,'billed_bing_requests',int(bing))
                store_result(db,prompt_return);seen[norm_name(label)]=prompt_return
                event(db,'verification',label,prompt_return['status'],prompt_return['reason'])
                print(f'[verified?] {label[:32]} => {prompt_return["status"]}: {prompt_return["official_site"][:65]}',flush=True)
                if args.pause_max:time.sleep(random.uniform(args.pause_min,args.pause_max))
            except Exception as exc:
                mark_verification_failure(db,label,exc)
                event(db,'verification',label,'error',repr(exc))
                print(f'[warning] verify {label}: {type(exc).__name__}: {exc}',file=sys.stderr,flush=True)
                if (type(exc).__name__ in {'AuthenticationError','PermissionDeniedError','BadRequestError','NotFoundError','RateLimitError'}
                        or 'did not call web_search' in str(exc)):
                    halt_reason=type(exc).__name__+': '+str(exc)[:140]
                    break
            if calls and calls%args.checkpoint_every==0:checkpoint()
    checkpoint()
    if excel_pending:
        print('[warning] Main Excel was locked at the final checkpoint. '
              'All search/verification data is saved in SQLite. '
              'Close the workbook and run --rebuild-from-cache to refresh it.',flush=True)
    print(f'[done] {args.out}; state saved for resume. This run model_calls={calls}, '
          f'Bing_requests={billed} (unknown-count responses={unknown_billed}).')
    print('[safety] Web forms are HTML-validated, not submission-tested; manual review before outreach.')
    if args._cycle_report:
        completed={r['key'] for r in db.execute('SELECT key FROM queries WHERE completed_at IS NOT NULL')}
        wanted=queries[:args.limit_queries] if args.limit_queries else queries
        left_discover=sum(hashlib.sha256(q.encode('utf-8')).hexdigest() not in completed for q in wanted)
        if args.no_azure_discovery:left_discover=0
        left_maps=remaining_map_tasks(db,args)
        left_browser_maps=browser_map_pending(db,args)
        seen_now=result_rows(db)
        left_verify=(0 if args.resolve_directory_links else sum(
                        row['name_key'] not in seen_now and
                        valid_company_name(json.loads(row['data']).get('name')) and
                        (lambda e:not e or e['attempts']<2)(db.execute(
                            'SELECT attempts FROM verification_failures WHERE name_key=?',(row['name_key'],)).fetchone())
                        for row in db.execute('SELECT name_key,data FROM candidates')))
        summary={'api_calls':calls,'billed_requests':billed,'unknown_billed':unknown_billed,
                 'pending_discovery':left_discover,'pending_verify':left_verify,
                 'pending_directory':directory_pending,
                 'pending_maps':left_maps,'pending_browser_maps':left_browser_maps,
                 'browser_map_searches':browser_calls,'map_requests':map_calls,'map_imported':imported_now,
                 'halt_reason':halt_reason,'excel_pending':excel_pending,'utc':moment()}
        tmp=args._cycle_report.with_suffix('.writing.json')
        tmp.write_text(json.dumps(summary,ensure_ascii=False,indent=2),encoding='utf-8')
        tmp.replace(args._cycle_report)
    db.close()


if __name__=='__main__':
    main()
