#!/usr/bin/env python3
"""Public-source Russian CAD talent discovery (quality-first v1.10). Python 3.10+.

Uses official GitHub/GitLab APIs and optional Azure OpenAI grounded web search.
No login-wall scraping, personal-email guessing, SMTP probing, or mass messaging.
Commits every candidate/job to SQLite, uses bounded parallel Azure searches and
exports Excel/CSV periodically and at shutdown (stdlib only).
"""
from __future__ import annotations

import argparse
from collections import deque
from email.utils import parsedate_to_datetime
import concurrent.futures
import csv
import hashlib
import html
from html.parser import HTMLParser
import ipaddress
import json
import os
from pathlib import Path
import random
import re
import socket
import sqlite3
import sys
import threading
import time
from datetime import datetime, timezone, timedelta
from urllib.parse import quote, urlsplit, urlunsplit, urlencode
from urllib.robotparser import RobotFileParser
from xml.sax.saxutils import escape as xe
from zipfile import ZipFile, ZIP_DEFLATED
import xml.etree.ElementTree as ET

try:
    import requests
except ImportError:
    raise SystemExit('Missing package. Run: python -m pip install requests openai')

SEEDS = [
    'FreeCAD/FreeCAD', 'CadQuery/cadquery', 'CadQuery/CQ-editor',
    'build123d/build123d', 'Open-Cascade-SAS/OCCT',
    'realthunder/FreeCAD_assembly3', 'solvespace/solvespace',
    'fougue/mayo', 'partcad/partcad', 'neka-nat/freecad-mcp',
    'jscad/OpenJSCAD.org', 'CadQuery/ocp-build-system',
]
TECH_TERMS = [
    'CadQuery', 'FreeCAD', 'OpenCascade', 'OpenCASCADE', 'OCCT',
    'build123d', 'OpenSCAD', 'SolveSpace', 'SolidWorks API',
    'Siemens NX Open', 'CATIA CAA', 'КОМПАС-3D API', 'CAD automation',
    'parametric CAD', 'geometric kernel', '3D modeling Python',
    # Expanded CAD development, automation and geometry ecosystem.
    'Autodesk Inventor API', 'AutoCAD .NET', 'Fusion 360 API',
    'Revit API', 'Dynamo Revit', 'RhinoCommon', 'Grasshopper Python',
    'BricsCAD API', 'nanoCAD API', 'PythonOCC', 'pythonocc-core',
    'OCP CAD Python', 'CGAL geometry', 'libigl mesh', 'Open CASCADE Technology',
    'STEP AP242', 'NURBS geometry', 'BRep modeling', 'Parasolid SDK',
    'CAM automation', 'FEA CAD integration', 'IFCOpenShell', 'OpenBIM',
    'C++ geometric modeling', 'C# CAD addins', 'Python CAD scripting',
    'reverse engineering CAD', '3D CAD plugins', 'CAD extensions',
    'QCAD development', 'CAD interoperability', 'CAD/CAM software',
]
CITY_TERMS = [
    'Russia', 'Moscow', 'Saint-Petersburg', 'Novosibirsk',
    'Ekaterinburg', 'Kazan', 'Nizhny-Novgorod', 'Samara', 'Tomsk',
    'Москва', 'Санкт-Петербург', 'Россия', 'Новосибирск', 'Екатеринбург',
]
RU_LOCATION = re.compile(
    r'\b(russia|russian federation|moscow|saint[ -]?petersburg|st\.?[ -]?petersburg|'
    r'novosibirsk|yekaterinburg|ekaterinburg|kazan|nizhny[ -]?novgorod|'
    r'samara|tomsk|omsk|ufa|perm|krasnoyarsk|voronezh|rostov[ -]?on[ -]?don|'
    r'kaliningrad|chelyabinsk|vladivostok|irkutsk)\b|'
    r'росси[яи]|москв|петербург|санкт[ -]?петербург|\bспб\b|'
    r'новосибирск|екатеринбург|казан|нижн(?:ий|его)[ -]?новгород|'
    r'самар|томск|омск|уфа|перм|красноярск|воронеж|ростов|'
    r'калининград|челябинск|владивосток|иркутск', re.I)
STRONG_SKILLS = {
    'CadQuery': [r'\bcadquery\b'],
    'FreeCAD': [r'\bfreecad\b'],
    'OpenCascade/OCCT': [r'\bopen.?cascade\b', r'\bocct\b', r'\bpythonocc\b'],
    'build123d': [r'\bbuild123d\b'],
    'OpenSCAD': [r'\bopenscad\b'],
    'SolveSpace': [r'\bsolvespace\b'],
    'SolidWorks API': [r'solidworks.{0,20}\b(api|macro|automation|add.?in|sdk)\b'],
    'Siemens NX Open': [r'\bnx.?open\b', r'siemens nx.{0,20}(api|automation)'],
    'CATIA CAA': [r'\bcatia\b.{0,20}(caa|api|automation|macro)'],
    'КОМПАС-3D API': [r'компас.{0,14}(api|апи|макрос|автоматизац)'],
    'CAD automation': [r'\bcad\b.{0,22}(automation|developer|programming|api|plugin|add.?in)',
                       r'автоматизац.{0,25}(cad|сапр|проектирован)',
                       r'(разработчик|программист).{0,25}(cad|сапр)'],
    'Geometry kernels': [r'(geometry|geometric|геометрическ).{0,25}(kernel|ядро)',
                         r'\bopencascade\b'],
}
WEAK_SKILLS = {
    'CAD modeling': [r'\bcad\b', r'\b3d[ -]?model', r'\bsolidworks\b',
                     r'\binventor\b', r'\bfusion.?360\b', r'\bсапр\b', r'3d.?модел'],
}
CONTACT_RE = re.compile(r'(?<![\w.+-])[\w.+-]+@[\w.-]+\.[a-z]{2,}(?![\w.-])', re.I)
LI_RE = re.compile(r'https?://(?:[a-z]{2,3}\.)?linkedin\.com/(?:in|pub)/[\w%.-]+/?', re.I)
BAD_EMAIL_PREFIX = ('noreply', 'no-reply', 'donotreply', 'support', 'info', 'admin', 'contact', 'sales', 'hello', 'webmaster')
BAD_EMAIL_DOMAINS = {'users.noreply.github.com', 'example.com', 'example.org', 'localhost'}
MAX_ATTEMPTS = 3
HEADERS = ['Name', 'Country evidence', 'Location', 'Platform', 'Profile URL',
           'Email', 'LinkedIn', 'Contact page', 'CAD skills', 'CAD evidence URLs',
           'Contact evidence URL', 'Source URLs', 'Public repositories (all)', 'Seed repo contributions',
           'Score', 'Confidence', 'Status reason', 'Last checked (UTC)']


def now():
    return datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def clean_url(value):
    value = (value or '').strip().strip('.,;<>"\'')
    if not value or len(value) > 1600: return ''
    try:
        parts = urlsplit(value)
        if parts.scheme not in ('https', 'http') or not parts.hostname: return ''
        if parts.username or parts.password: return ''
        host = parts.hostname.lower().rstrip('.')
        if host in ('localhost', 'localhost.localdomain') or host.endswith(('.local', '.internal')): return ''
        try:
            ip = ipaddress.ip_address(host)
            if not ip.is_global: return ''
        except ValueError:
            pass
        return urlunsplit((parts.scheme, parts.netloc.lower(), parts.path.rstrip('/') or '/', '', ''))
    except ValueError:
        return ''


def public_website(value):
    value=(value or '').strip()
    if value and not re.match(r'^https?://',value,re.I) and re.match(r'^(?:www\.)?[\w.-]+\.[a-z]{2,}(?:/|$)',value,re.I):
        value='https://'+value
    return clean_url(value)


def norm_email(value):
    v = (value or '').strip().lower()
    if not CONTACT_RE.fullmatch(v) or len(v) > 254: return ''
    local, domain = v.rsplit('@', 1)
    if domain in BAD_EMAIL_DOMAINS or any(local.startswith(s) for s in BAD_EMAIL_PREFIX): return ''
    if local.endswith('.png') or local.endswith('.jpg'): return ''
    return v


def linkedin_link(value):
    if value and value.lower().lstrip().startswith(('www.linkedin.com/', 'linkedin.com/')):
        value='https://'+value.strip()
    m = LI_RE.search(value or '')
    return clean_url(m.group(0)) if m else ''


def list_unique(values):
    return list(dict.fromkeys(v for v in values if v))


def extract_skills(text):
    found = []
    for label, patterns in {**STRONG_SKILLS, **WEAK_SKILLS}.items():
        if any(re.search(p, text or '', re.I) for p in patterns): found.append(label)
    return found


def geo_proof(location):
    """Require a Russian location signal and reject obvious misleading matches.

    Moscow, Idaho and Saint Petersburg, Florida are not Russian locations;
    similarly, an explicit negation ('not Russia') is not a positive signal.
    An unsubstantiated or ambiguous location must not enter recruiter output.
    """
    value=str(location or '').strip()
    if not RU_LOCATION.search(value):
        return False
    if re.search(r'\b(?:not|outside|except|never)\s+(?:in\s+|from\s+)?russia\b|'
                 r'\bmoscow\s*,\s*(?:idaho|id|usa|united states)\b|'
                 r'\b(?:saint|st\.?)\s*petersburg\s*,\s*(?:florida|fl|usa)\b',
                 value,re.I):
        return False
    return True


def is_person_email(email):
    return bool(norm_email(email))


class PageParser(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.links=[]; self.words=[]; self.hidden=0; self.has_form=False; self.form_message=False
    def handle_starttag(self, tag, attrs):
        d=dict(attrs)
        if tag in ('script','style','noscript'): self.hidden+=1
        if tag=='a' and d.get('href'): self.links.append(d['href'])
        if tag=='form': self.has_form=True
        if tag=='textarea' or (tag=='input' and any(w in str(d.get('name','')).lower() for w in ('message','сообщение','comment'))):
            self.form_message=True
    def handle_endtag(self, tag):
        if tag in ('script','style','noscript'): self.hidden=max(0,self.hidden-1)
    def handle_data(self, data):
        if not self.hidden and data.strip(): self.words.append(data.strip())


class HostThrottle:
    def __init__(self, pause_min=2.0, pause_max=5.0):
        self.min=float(pause_min); self.max=float(pause_max)
        self.lock=threading.RLock(); self.available={}
    def wait(self, host):
        with self.lock:
            wait=max(0, self.available.get(host,0)-time.monotonic())
            self.available[host]=time.monotonic()+wait+random.uniform(self.min,self.max)
        if wait: time.sleep(wait)


class HttpClient:
    def __init__(self, args):
        self.throttle=HostThrottle(args.pause_min,args.pause_max)
        self.tlocal=threading.local()
        self.tokens={'api.github.com':os.getenv('GITHUB_TOKEN','').strip(),
                     'gitlab.com':os.getenv('GITLAB_TOKEN','').strip()}
        self.robot_cache={}
        self.robot_lock=threading.Lock()
        self.timeout=args.timeout
        self.inspect_portfolios=args.inspect_portfolios
        self.requests_count=0
        self.counter_lock=threading.Lock()
    def session(self):
        if not hasattr(self.tlocal,'session'):
            self.tlocal.session=requests.Session()
            self.tlocal.session.headers.update({'User-Agent':'CADTalentResearch/1.0 (+public professional profiles; no auth-bypass)'})
        return self.tlocal.session
    def get(self,url,params=None,api=True):
        host=urlsplit(url).hostname or ''
        headers={'Accept':'application/json'} if api else {'Accept':'text/html'}
        if host=='api.github.com' and self.tokens[host]: headers['Authorization']='Bearer '+self.tokens[host]
        if host=='gitlab.com' and self.tokens[host]: headers['PRIVATE-TOKEN']=self.tokens[host]
        for attempt in range(3):
            self.throttle.wait(host)
            with self.counter_lock: self.requests_count+=1
            try:
                r=self.session().get(url,params=params,headers=headers,timeout=self.timeout,allow_redirects=False)
            except requests.RequestException as exc:
                if attempt==2: raise RuntimeError(str(exc)) from exc
                time.sleep(2**attempt+random.random());continue
            if r.status_code in (301,302,303,307,308):
                # Only follow redirects explicitly for public HTML, not arbitrary API endpoints.
                if not api:
                    target=requests.compat.urljoin(url,r.headers.get('Location',''))
                    if target.startswith('https://') and clean_url(target) and self.allowed_robots(target):
                        url=target; continue
                raise RuntimeError('redirect blocked: '+url)
            if r.status_code in (429,500,502,503,504) or (r.status_code==403 and r.headers.get('X-RateLimit-Remaining')=='0'):
                if attempt==2: raise RuntimeError(f'HTTP {r.status_code} rate/server limit at {host}')
                delay=r.headers.get('Retry-After')
                try: wait=float(delay) if delay else 2**(attempt+2)
                except ValueError: wait=2**(attempt+2)
                reset=r.headers.get('X-RateLimit-Reset')
                if reset and r.headers.get('X-RateLimit-Remaining')=='0':
                    try: wait=max(wait,min(300,int(reset)-time.time()+2))
                    except ValueError: pass
                time.sleep(min(300,max(1,wait))+random.random());continue
            if r.status_code in (404,204): return None
            if r.status_code==401: raise RuntimeError('HTTP 401: token rejected or API not authorized')
            if r.status_code==403: raise RuntimeError('HTTP 403: API access denied or throttled')
            r.raise_for_status()
            if api:
                try: return r.json()
                except ValueError: raise RuntimeError('Invalid API JSON from '+host)
            if len(r.content)>1_200_000: return ''
            return r.text
        return None
    def allowed_robots(self,url):
        p=urlsplit(url)
        if p.scheme!='https' or not p.hostname or not clean_url(url): return False
        host=p.hostname.lower()
        # Defensive: no links to private hosts in direct web fetching.
        try:
            addresses=socket.getaddrinfo(host,443,type=socket.SOCK_STREAM)
            if not addresses or any(not ipaddress.ip_address(a[4][0]).is_global for a in addresses): return False
        except (OSError,ValueError): return False
        with self.robot_lock:
            if host in self.robot_cache: return self.robot_cache[host].can_fetch('CADTalentResearch',url)
            robots=RobotFileParser()
            robots.set_url(f'https://{host}/robots.txt')
            try:
                self.throttle.wait(host)
                resp=self.session().get(f'https://{host}/robots.txt',timeout=min(8,self.timeout),allow_redirects=False)
                if resp.status_code==404: robots.parse([])
                elif resp.status_code!=200 or len(resp.content)>200_000: return False
                else: robots.parse(resp.text.splitlines())
            except requests.RequestException: return False
            self.robot_cache[host]=robots
            return robots.can_fetch('CADTalentResearch',url)
    def public_page(self,url):
        if not self.allowed_robots(url): return None
        try: return self.get(url,api=False)
        except Exception: return None


class Store:
    def __init__(self, path):
        self.db=sqlite3.connect(path)
        self.db.execute('PRAGMA journal_mode=WAL')
        self.db.execute('''CREATE TABLE IF NOT EXISTS jobs(
            key TEXT PRIMARY KEY, completed_at TEXT, attempts INTEGER NOT NULL DEFAULT 0,
            last_error TEXT, updated_at TEXT)''')
        self.db.execute('''CREATE TABLE IF NOT EXISTS profiles(
            url TEXT PRIMARY KEY, data TEXT NOT NULL, updated_at TEXT NOT NULL)''')
        self.db.execute('''CREATE TABLE IF NOT EXISTS seeds(
            platform TEXT NOT NULL, user_id TEXT NOT NULL, data TEXT NOT NULL,
            PRIMARY KEY(platform,user_id))''')
        # Non-destructive cross-platform identity groups. Raw source records stay intact.
        self.db.execute('CREATE TABLE IF NOT EXISTS identity_members(url TEXT PRIMARY KEY, cluster TEXT NOT NULL)')
        self.db.execute('CREATE INDEX IF NOT EXISTS ix_identity_members_cluster ON identity_members(cluster)')
        self.db.execute('CREATE TABLE IF NOT EXISTS identity_keys(key TEXT PRIMARY KEY, cluster TEXT NOT NULL)')
        # v1.2 SQLite databases have no identity index: build it once from stored profiles.
        historic=self.db.execute('''SELECT p.url,p.data FROM profiles p
            LEFT JOIN identity_members i ON i.url=p.url WHERE i.url IS NULL''').fetchall()
        for url,raw in historic:
            try:self._index_candidate(json.loads(raw))
            except (ValueError,TypeError):pass
        self.db.commit()
        if historic:print(f'[resume] Indexed {len(historic)} legacy profiles for database-side deduplication.',flush=True)
        self.write_count=0
        self.checkpoint_every=0
        self.checkpoint_callback=None
    def configure_checkpoints(self,every,callback):
        self.checkpoint_every=max(0,int(every))
        self.checkpoint_callback=callback
    def stats(self):
        profiles=self.db.execute('SELECT COUNT(*) FROM profiles').fetchone()[0]
        completed=self.db.execute('SELECT COUNT(*) FROM jobs WHERE completed_at IS NOT NULL').fetchone()[0]
        pending=self.db.execute('SELECT COUNT(*) FROM jobs WHERE completed_at IS NULL').fetchone()[0]
        return profiles,completed,pending
    def due(self,key,refresh_days=0):
        row=self.db.execute('SELECT completed_at, attempts, last_error FROM jobs WHERE key=?',(key,)).fetchone()
        if not row: return True
        if row[0]:
            if refresh_days<=0: return False
            try: return datetime.fromisoformat(row[0].replace('Z','+00:00')) < datetime.now(timezone.utc)-timedelta(days=refresh_days)
            except ValueError: return False
        # Historical v1.6 stored 429 errors as failed attempts. Do not let
        # transient Azure throttling permanently exclude these searches.
        if row[2] and any(x in str(row[2]).lower() for x in
                          ('429','rate_limit_exceeded','token rate limit')):
            return True
        return row[1]<MAX_ATTEMPTS
    def mark(self,key,ok,error=''):
        self.db.execute('''INSERT INTO jobs(key,completed_at,attempts,last_error,updated_at)
            VALUES(?,?,1,?,?) ON CONFLICT(key) DO UPDATE SET
            completed_at=excluded.completed_at,attempts=jobs.attempts+1,
            last_error=excluded.last_error,updated_at=excluded.updated_at''',
            (key,now() if ok else None,error[:400],now()))
        self.db.commit()
    def existing(self,url):
        r=self.db.execute('SELECT data FROM profiles WHERE url=?',(url,)).fetchone()
        return json.loads(r[0]) if r else None
    def _index_candidate(self,c):
        url=c.get('profile_url','')
        if not url:return
        keys=[]
        li=linkedin_link(c.get('linkedin'))
        if li:keys.append('li:'+li.lower())
        # Do not merge people based on unverified, search-reported email addresses.
        email=norm_email(c.get('email'))
        if email and c.get('contact_trust')=='direct':keys.append('email:'+email)
        current=self.db.execute('SELECT cluster FROM identity_members WHERE url=?',(url,)).fetchone()
        clusters={url}
        if current:clusters.add(current[0])
        for k in keys:
            found=self.db.execute('SELECT cluster FROM identity_keys WHERE key=?',(k,)).fetchone()
            if found:clusters.add(found[0])
        canonical=min(clusters)
        for old in clusters:
            if old==canonical:continue
            self.db.execute('UPDATE identity_members SET cluster=? WHERE cluster=?',(canonical,old))
            self.db.execute('UPDATE identity_keys SET cluster=? WHERE cluster=?',(canonical,old))
        self.db.execute('INSERT INTO identity_members(url,cluster) VALUES(?,?) '
                        'ON CONFLICT(url) DO UPDATE SET cluster=excluded.cluster',(url,canonical))
        for k in keys:
            self.db.execute('INSERT INTO identity_keys(key,cluster) VALUES(?,?) '
                            'ON CONFLICT(key) DO UPDATE SET cluster=excluded.cluster',(k,canonical))
    def merged_profiles(self):
        groups={}
        for cluster,raw in self.db.execute('''SELECT COALESCE(i.cluster,p.url),p.data FROM profiles p
            LEFT JOIN identity_members i ON i.url=p.url'''):
            groups.setdefault(cluster,[]).append(json.loads(raw))
        return [merge_profile_group(group) for group in groups.values()]
    def put(self,c):
        url=clean_url(c.get('profile_url',''))
        if not url: return False
        c['profile_url']=url
        old=self.existing(url)
        if old:
            incoming_api = c.get('confidence')=='API verified'
            old_api = old.get('confidence')=='API verified'
            if old_api and not incoming_api:
                # Never allow search-derived claims to overwrite a directly checked API profile.
                for field in ('name','location','email','linkedin','contact_page','contact_evidence','bio','repos','commits','contact_trust'):
                    c[field]=old.get(field,c.get(field))
                c['confidence']='API verified'
            for k in ('name','location','email','linkedin','contact_page','bio','repo_url','contact_evidence'):
                if not c.get(k): c[k]=old.get(k,'')
            if not c.get('contact_trust') and old.get('contact_trust')=='direct' and not incoming_api:
                c['contact_trust']='direct'
            for k in ('skills','cad_evidence','sources'):
                c[k]=list_unique((old.get(k) or [])+(c.get(k) or []))
            for k in ('repos','commits'):
                c[k]=max(int(c.get(k) or 0),int(old.get(k) or 0))
        c['checked_at']=now()
        self.db.execute('''INSERT INTO profiles(url,data,updated_at) VALUES(?,?,?)
            ON CONFLICT(url) DO UPDATE SET data=excluded.data,updated_at=excluded.updated_at''',
            (url,json.dumps(c,ensure_ascii=False),now()))
        self._index_candidate(c)
        self.db.commit()
        self.write_count+=1
        if self.checkpoint_every and self.write_count%self.checkpoint_every==0 and self.checkpoint_callback:
            try:
                print(f'[checkpoint] {self.write_count} profile writes since start; creating Excel/CSV snapshot...',flush=True)
                self.checkpoint_callback()
            except Exception as exc:
                # SQLite is already committed; never lose collection due to XLSX I/O.
                print(f'[checkpoint warning] export failed: {type(exc).__name__}: {exc}. SQLite remains saved.',file=sys.stderr,flush=True)
        return True
    def all_profiles(self):
        return [json.loads(r[0]) for r in self.db.execute('SELECT data FROM profiles')]
    def remember_seed(self,platform,user_id,data):
        key=str(user_id)
        old=self.db.execute('SELECT data FROM seeds WHERE platform=? AND user_id=?',(platform,key)).fetchone()
        if old:
            prev=json.loads(old[0])
            if platform=='github' and int(prev.get('contrib') or 0)>int(data.get('contrib') or 0):data=prev
            else:
                for k,v in prev.items():
                    if not data.get(k):data[k]=v
        self.db.execute('INSERT INTO seeds(platform,user_id,data) VALUES(?,?,?) ON CONFLICT(platform,user_id) DO UPDATE SET data=excluded.data',
                        (platform,key,json.dumps(data,ensure_ascii=False)))
        self.db.commit()
    def get_seeds(self,platform):
        return {key:json.loads(data) for key,data in self.db.execute(
            'SELECT user_id,data FROM seeds WHERE platform=?',(platform,))}
    def close(self): self.db.close()



def inspect_portfolio(api, candidate, website):
    """Optionally read a publicly linked professional website, respecting robots.txt.

    Never guess contact addresses, log in, or inspect unrelated people.
    Only the portfolio homepage and at most one explicit contact page are read.
    """
    base=clean_url(website)
    if not base:return candidate
    host=urlsplit(base).hostname or ''
    if host in ('github.com','gitlab.com','linkedin.com','www.linkedin.com'):
        return candidate
    content=api.public_page(base)
    if not content:return candidate
    parser=PageParser()
    try:parser.feed(content[:600000])
    except Exception:return candidate
    text=' '.join(parser.words)
    # An author-linked portfolio is public evidence, but emails are usable only
    # when explicitly written on that professional page (or in mailto links).
    mails=CONTACT_RE.findall(text+' '+' '.join(x for x in parser.links if x.lower().startswith('mailto:')))
    public_email=next((norm_email(x) for x in mails if norm_email(x)), '')
    li=next((linkedin_link(link) for link in parser.links if linkedin_link(link)), '')
    if not candidate.get('email') and public_email:
        candidate['email']=public_email
        candidate['contact_evidence']=base
        candidate['contact_trust']='direct'
    if not candidate.get('linkedin') and li:
        candidate['linkedin']=li
        candidate['contact_evidence']=base
        candidate['contact_trust']='direct'
    found_skills=extract_skills(text[:18000])
    if found_skills:
        candidate['skills']=list_unique(candidate.get('skills',[])+found_skills)
        candidate['cad_evidence']=list_unique(candidate.get('cad_evidence',[])+[base])
    candidate['sources']=list_unique(candidate.get('sources',[])+[base])
    # Contact form counts only when a form element is actually visible.
    if parser.has_form and parser.form_message and not candidate.get('contact_page'):
        candidate['contact_page']=base
        candidate['contact_evidence']=base
        candidate['contact_trust']='direct'
    if not candidate.get('email') and not candidate.get('linkedin'):
        from urllib.parse import urljoin
        for href in parser.links:
            h=href.lower()
            if not any(w in h for w in ('contact','контакт','связ')):continue
            target=clean_url(urljoin(base,href))
            if not target or urlsplit(target).hostname!=host or target==base:continue
            page=api.public_page(target)
            if not page:break
            sub=PageParser()
            try:sub.feed(page[:600000])
            except Exception:break
            text=' '.join(sub.words)
            mails=CONTACT_RE.findall(text+' '+' '.join(x for x in sub.links if x.lower().startswith('mailto:')))
            email=next((norm_email(x) for x in mails if norm_email(x)), '')
            li=next((linkedin_link(link) for link in sub.links if linkedin_link(link)), '')
            if email and not candidate.get('email'):candidate['email']=email
            if li and not candidate.get('linkedin'):candidate['linkedin']=li
            if sub.has_form and sub.form_message:candidate['contact_page']=target
            if email or li or (sub.has_form and sub.form_message):
                candidate['contact_trust']='direct'
                candidate['contact_evidence']=target
                candidate['sources']=list_unique(candidate['sources']+[target])
            break
    return candidate


# Strong CAD evidence is required before spending API calls on repo contributors.
# Broad matches like "cad", "geometry" or "3d" alone are not sufficient.
NON_CAD_REPO = re.compile(r'(?:^|[\W_])(?:awesome|catppuccin|wallpaper|theme|icons?|dotfiles|config|cheatsheet|translation|localization)(?:$|[\W_])',re.I)
CAD_TECH_RE = re.compile(
    r'cadquery|freecad|build123d|open[ -]?cascade|\bocct\b|pythonocc|openscad|'
    r'solvespace|solidworks|\bcatia\b|\bnx[ -]?open\b|\bкомпас[ -]?3d\b|'
    r'\binventor\s+api\b|\bautocad\s+(?:api|\.net|lisp)\b|'
    r'\b(?:CAD|САПР)\s*(?:api|sdk|automation|plugin|add[- ]?in|developer|kernel)\b|'
    r'(?:geometric|geometry)\s+(?:kernel|modeling|modelling)\b',re.I)


def repo_is_cad(meta):
    # Validate search results by repository metadata, not the search term alone.
    if not isinstance(meta,dict) or meta.get('fork') or meta.get('archived'):return False
    desc=' '.join([meta.get('name') or '',meta.get('description') or '',
                   ' '.join(meta.get('topics') or [])])
    if NON_CAD_REPO.search(meta.get('name') or ''):return False
    return bool(CAD_TECH_RE.search(desc))


def profile_cad_support(c):
    # Reuse the same strong-skill detection as candidate_assess().  Older
    # releases inconsistently used literal skill-label membership here,
    # pushing genuine Russian CAD engineers with differently worded skills
    # into Archive even when candidate_assess recognized them.
    skills=c.get('skills') or []
    text=' '.join(skills)+' '+(c.get('bio') or '')
    recognized=set(extract_skills(text))
    strong=bool(set(skills).intersection(STRONG_SKILLS) or
                recognized.intersection(STRONG_SKILLS))
    evidence=any(clean_url(url) for url in (c.get('cad_evidence') or []))
    return strong,evidence


def cad_screening_signal(c):
    """Screen RU candidates with actual CAD signals, even if a project URL is missing.

    v1.10 required BOTH a CAD evidence URL and skills, incorrectly archiving
    Russian CAD engineers whose public profiles described their experience
    without linking to a dedicated repository. This classification is only
    for human screening, never for automatic qualification.
    """
    skills=c.get('skills') or []
    content=' '.join(str(x) for x in skills)+' '+str(c.get('bio') or '')
    if extract_skills(content):
        return True
    if re.search(r'\b(?:cad|cae|bim|plm|cam)\b|сапр|компас|машиностроен|'
                 r'механическ.{0,16}проектирован|геометрическ.{0,16}моделирован|'
                 r'параметрическ.{0,18}моделирован|чертеж|3d[ -]?cad', content, re.I):
        return True
    # A CAD-specific project is still useful as a weaker screening hint.
    return any(CAD_TECH_RE.search(str(url)) for url in (c.get('cad_evidence') or []))


def gh_user_queries():
    # Keep the original 56 strings first: old SQLite search keys remain stable.
    q=[]
    locations=['Russia','Moscow','Saint-Petersburg','Novosibirsk','Kazan','Tomsk','Россия','Москва']
    keywords=['cadquery','freecad','opencascade','build123d','openscad','cad','solidworks']
    for loc in locations:
        for keyword in keywords:
            q.append(f'{keyword} in:bio location:"{loc}"')
    # Expanded Russia city / CAD-technology combinations.
    more_locations=[
        'Ekaterinburg','Nizhny-Novgorod','Samara','Perm','Ufa','Omsk',
        'Krasnoyarsk','Voronezh','Rostov-on-Don','Chelyabinsk',
        'Kaliningrad','Vladivostok','Irkutsk','Saratov','Tula',
        'Краснодар','Екатеринбург','Казань','Нижний Новгород','Самара',
    ]
    more_keywords=[
        'freecad','cadquery','opencascade','build123d','solidworks',
        'CAD','autocad','revit','3d modeling','geometry','компас','сапр',
    ]
    for loc in more_locations:
        for keyword in more_keywords:
            q.append(f'{keyword} in:bio location:"{loc}"')
    return list_unique(q)

def gh_candidate(user,proof_url='',contrib=0):
    return {'login':user, 'proof_url':proof_url,'contrib':int(contrib or 0)}


def discover_github(api,store,args):
    if 'github' not in args.sources: return {}
    found=store.get_seeds('github')
    for fullname in SEEDS[:args.seed_projects]:
        for page in range(1,args.contributor_pages+1):
            key=f'gh:contributors:{fullname}:{page}'
            if not store.due(key,args.refresh_days): continue
            try:
                results=api.get('https://api.github.com/repos/'+fullname+'/contributors',
                                {'per_page':100,'page':page}) or []
                if not isinstance(results,list): raise RuntimeError('Expected contributor array')
                for x in results:
                    if x.get('login') and x.get('type')=='User':
                        u=x['login']; prev=found.get(u,gh_candidate(u))
                        if x.get('contributions',0)>=prev['contrib']:
                            found[u]=gh_candidate(u,f'https://github.com/{fullname}',x['contributions'])
                            store.remember_seed('github',u,found[u])
                store.mark(key,True)
                print(f'[github contributors] {fullname} page={page}: {len(results)}')
                if len(results)<100:break
            except Exception as e:
                store.mark(key,False,str(e));print('[warning] github contributors:',str(e),file=sys.stderr)
                if 'rate' in str(e).lower(): return found
    # Discover additional public CAD repositories beyond the curated seed set.
    # A repository must be relevant by name/description; its contributors are then
    # profiled individually and filtered by geographic evidence and public contact.
    selected=0
    for term in TECH_TERMS[:args.repo_search_terms]:
        if selected>=args.max_searched_repos:break
        search_key='gh:repo-search:'+term
        if store.due(search_key,args.refresh_days):
            try:
                result=api.get('https://api.github.com/search/repositories',
                               {'q':term+' in:name,description','per_page':20,'sort':'stars'}) or {}
                projects=result.get('items',[]) if isinstance(result,dict) else []
                for repo in projects:
                    full=repo.get('full_name','')
                    if not full or full in SEEDS or not repo_is_cad(repo):continue
                    store.remember_seed('github_repo',full,{'full_name':full})
                store.mark(search_key,True)
                print(f'[github repo-search] {term}: {len(projects)} projects')
            except Exception as exc:
                store.mark(search_key,False,str(exc));print('[warning] github repo search:',exc,file=sys.stderr)
        repo_candidates=store.get_seeds('github_repo')
        for full in repo_candidates:
            if selected>=args.max_searched_repos:break
            rkey='gh:project-contributors:'+full
            if not store.due(rkey,args.refresh_days):continue
            selected+=1
            try:
                # Old SQLite seeds may originate from overbroad searches.
                # Revalidate project metadata before trusting their contributors.
                metadata=api.get('https://api.github.com/repos/'+full) or {}
                if not repo_is_cad(metadata):
                    store.mark(rkey,True)
                    print(f'[github skipped non-CAD repo] {full}')
                    continue
                res=api.get('https://api.github.com/repos/'+full+'/contributors',
                            {'per_page':100,'page':1}) or []
                if not isinstance(res,list):raise RuntimeError('Expected contributor array')
                for u in res:
                    login=u.get('login')
                    if not login or u.get('type')!='User':continue
                    prev=found.get(login,gh_candidate(login))
                    if int(u.get('contributions') or 0)>int(prev['contrib']):
                        found[login]=gh_candidate(login,'https://github.com/'+full,int(u.get('contributions') or 0))
                        store.remember_seed('github',login,found[login])
                store.mark(rkey,True)
                print(f'[github repo contributors] {full}: {len(res)}')
            except Exception as exc:
                store.mark(rkey,False,str(exc));print('[warning] repository contributors:',exc,file=sys.stderr)
                if 'rate' in str(exc).lower():break
    for query in gh_user_queries()[:args.github_queries]:
        # Preserve legacy query strings/cache keys, but skip overly broad phrases
        # that attracted unrelated engineering and general 3D-modeling accounts.
        term=query.split(' in:bio ',1)[0].strip().lower()
        if term in {'cad','geometry','3d modeling'}:
            continue
        for page in range(1,args.github_pages+1):
            key='gh:search:'+query+':'+str(page)
            if not store.due(key,args.refresh_days): continue
            try:
                results=api.get('https://api.github.com/search/users',
                                {'q':query,'per_page':100,'page':page}) or {}
                if not isinstance(results,dict): raise RuntimeError('Invalid user-search response')
                items=results.get('items',[])
                for x in items:
                    if x.get('login') and x.get('type')=='User':
                        if x['login'] not in found:
                            found[x['login']]=gh_candidate(x['login'])
                            store.remember_seed('github',x['login'],found[x['login']])
                store.mark(key,True)
                print(f'[github search] {query}: {len(items)}')
                if len(items)<100:break
            except Exception as e:
                store.mark(key,False,str(e));print('[warning] github search:',str(e),file=sys.stderr)
                if 'rate' in str(e).lower(): return found
    return found


def enrich_github(api,login,seed):
    u=api.get('https://api.github.com/users/'+quote(login))
    if not isinstance(u,dict) or u.get('type')!='User': return None
    repos=api.get('https://api.github.com/users/'+quote(login)+'/repos',
                  {'sort':'updated','per_page':100,'type':'public'}) or []
    if not isinstance(repos,list):repos=[]
    snippets=[]; skills=[]; links=[]
    if seed.get('proof_url') and (seed['proof_url'].rstrip('/') in
                                   {'https://github.com/'+x for x in SEEDS}
                                   or CAD_TECH_RE.search(seed['proof_url'])):
        snippets.append(seed['proof_url']); links.append(seed['proof_url'])
        skills+=extract_skills(seed['proof_url'])
    for r in repos:
        if not repo_is_cad(r):continue
        line=' '.join([r.get('name') or '',r.get('description') or '',r.get('topics') and ' '.join(r['topics']) or ''])
        hit=extract_skills(line)
        if hit:
            skills+=hit
            if r.get('html_url'): links.append(r['html_url'])
            snippets.append(line)
    # Relevance in biography alone is not definitive CAD-development evidence.
    biography=(u.get('bio') or '')+' '+(u.get('company') or '')
    skills+=extract_skills(biography)
    # Do not re-add an unvalidated repository as CAD evidence.
    li=linkedin_link(biography) or linkedin_link(u.get('blog') or '')
    email=norm_email(u.get('email'))
    blog=public_website(u.get('blog',''))
    contact_page=''  # A generic website/homepage is NOT a confirmed contact channel.
    result={'name':u.get('name') or login,'platform':'GitHub','profile_url':u.get('html_url') or 'https://github.com/'+login,
            'location':u.get('location') or '', 'bio':biography,'email':email,'linkedin':li,
            'contact_page':contact_page,'contact_evidence':u.get('html_url') if email or li else '',
            'contact_trust':'direct' if email or li else '',
            'skills':list_unique(skills),'cad_evidence':list_unique(links),
            'sources':list_unique([u.get('html_url')]+links),'repos':u.get('public_repos') or len(repos),
            'commits':seed.get('contrib',0),'checked_at':now(),'confidence':'API verified'}
    return inspect_portfolio(api,result,blog) if api.inspect_portfolios else result


def discover_gitlab(api,store,args):
    if 'gitlab' not in args.sources:return {}
    users=store.get_seeds('gitlab')
    for term in TECH_TERMS[:args.gitlab_terms]:
        for page in range(1,args.gitlab_pages+1):
            key=f'gl:users:{term}:{page}'
            if not store.due(key,args.refresh_days):continue
            try:
                result=api.get('https://gitlab.com/api/v4/users',
                               {'search':term,'per_page':100,'page':page}) or []
                if not isinstance(result,list):raise RuntimeError('Expected users list')
                for u in result:
                    if u.get('id') and not u.get('bot'):
                        users[str(u['id'])]=u
                        store.remember_seed('gitlab',u['id'],u)
                store.mark(key,True)
                print(f'[gitlab users] {term}: {len(result)}')
                if len(result)<100:break
            except Exception as exc:
                store.mark(key,False,str(exc));print('[warning] gitlab search:',exc,file=sys.stderr)
    # Include public personal project owners returned by GitLab project search.
    for term in TECH_TERMS[:args.gitlab_terms]:
        key='gl:projects:'+term
        if not store.due(key,args.refresh_days):continue
        try:
            projects=api.get('https://gitlab.com/api/v4/projects',
                             {'search':term,'per_page':100,'order_by':'last_activity_at'}) or []
            for p in projects:
                namespace=p.get('namespace') or {}
                if namespace.get('kind')=='user' and namespace.get('id'):
                    if str(namespace['id']) not in users:
                        u={'id':namespace['id'],'username':namespace.get('path','')}
                        users[str(namespace['id'])]=u
                        store.remember_seed('gitlab',namespace['id'],u)
            store.mark(key,True)
            print(f'[gitlab projects] {term}: {len(projects)}')
        except Exception as exc:
            store.mark(key,False,str(exc)); print('[warning] gitlab projects:',exc,file=sys.stderr)
    return users


def enrich_gitlab(api,user):
    uid=user['id']
    u=api.get('https://gitlab.com/api/v4/users/'+str(uid)) or {}
    if not isinstance(u,dict):return None
    project_api='https://gitlab.com/api/v4/users/'+str(uid)+'/projects'
    projects=api.get(project_api,{'per_page':100,'order_by':'last_activity_at'}) or []
    if not isinstance(projects,list):projects=[]
    skills=[]; links=[]
    for p in projects:
        if not repo_is_cad({'name':p.get('name'),'description':p.get('description'),
                            'topics':p.get('tag_list') or [],'fork':False}):continue
        brief=' '.join([p.get('name') or '',p.get('description') or '',
                        ' '.join(p.get('tag_list') or [])])
        hits=extract_skills(brief)
        if hits:
            skills+=hits
            if p.get('web_url'):links.append(p['web_url'])
    bio=(u.get('bio') or '')+' '+(u.get('organization') or '')
    skills+=extract_skills(bio)
    website=public_website(u.get('website_url') or '')
    li=linkedin_link(bio) or linkedin_link(u.get('linkedin') or '') or linkedin_link(website)
    email=norm_email(u.get('public_email') or '')
    profile=clean_url(u.get('web_url') or ('https://gitlab.com/'+(u.get('username') or user.get('username',''))))
    result={'name':u.get('name') or u.get('username',''),'platform':'GitLab','profile_url':profile,
            'location':u.get('location') or '', 'bio':bio,'email':email,'linkedin':li,
            'contact_page':'',
            'contact_evidence':profile if (email or li) else '',
            'contact_trust':'direct' if email or li else '',
            'skills':list_unique(skills),'cad_evidence':list_unique(links),
            'sources':list_unique([profile]+links),'repos':len(projects),'commits':0,
            'confidence':'API verified','checked_at':now()}
    return inspect_portfolio(api,result,website) if api.inspect_portfolios else result


def make_web_queries():
    # Search engine indexed public pages, never login-only pages.
    groups=[
       ('LinkedIn', 'site:linkedin.com/in/'),
       ('Habr Career', 'site:career.habr.com/'),
       ('HH.ru', 'site:hh.ru/resume/'),
       ('Freelance', 'site:freelance.ru/'),
       ('Freelancehunt', 'site:freelancehunt.com/'),
       ('Kwork', 'site:kwork.ru/user/'),
       ('Academia', 'site:edu.ru'),
       ('Academia', 'site:researchgate.net/profile/'),
       ('GitHub', 'site:github.com/'),
       ('GitLab', 'site:gitlab.com/'),
       ('Portfolio', 'CAD инженер разработчик портфолио'),
    ]
    terms=[
       'FreeCAD разработчик', 'CadQuery developer', 'OpenCascade C++ engineer',
       'build123d Python CAD', 'SolidWorks API developer', 'КОМПАС-3D API разработчик',
       'CAD automation engineer', 'Siemens NX Open developer',
       'CATIA CAA developer', 'САПР разработчик C++',
       'CAD Python скрипты', 'разработчик геометрического ядра',
       'параметрическое моделирование Python', 'CAD plugin developer',
       'фриланс САПР программирование', 'исследователь САПР',
    ]
    places=['Россия','Москва','Санкт-Петербург','Новосибирск','Казань','Екатеринбург']
    result=[]
    for platform,site in groups:
        for i,term in enumerate(terms):
            # Interleave platform/topic/location to avoid a single-platform batch.
            result.append({'platform':platform,'q':f'{site} {term} {places[(i+len(platform))%len(places)]}'})
    for place in places:
        for term in terms:
            result.append({'platform':'Open web','q':f'{place} {term} email linkedin профиль разработчик'})
    # Expanded pool. Preserve all old query strings for cache continuity.
    more_terms=[
        'PythonOCC геометрическое моделирование','Autodesk Inventor API C#',
        'AutoCAD .NET разработчик','Fusion 360 API Python',
        'Revit API C# разработчик','RhinoCommon Grasshopper developer',
        'Open CASCADE Technology C++','CGAL вычислительная геометрия',
        'NURBS BRep developer','QCAD plugin developer',
        'BlenderBIM IfcOpenShell Python','nanoCAD API разработчик',
        'BricsCAD BRX developer','САПР CAD CAM разработка плагинов',
        'геометрическое ядро САПР C++','CAD аддоны автоматизация C#',
        'CAD Python разработчик','SolidWorks макросы VBA C#',
        'КОМПАС 3D SDK API','Siemens NX Open C++',
        'CATIA CAA V5 C++','3D CAD reverse engineering engineer',
        'параметрическая модель CAD Python','STEP IGES CAD conversion',
    ]
    more_places=[
        'Самара','Томск','Уфа','Пермь','Омск','Красноярск','Воронеж',
        'Ростов-на-Дону','Нижний Новгород','Челябинск','Иркутск','Владивосток',
    ]
    # Additional targeted site searches plus regional open-web discovery.
    for platform,site in groups:
        for i,term in enumerate(more_terms):
            result.append({'platform':platform,
                           'q':f'{site} {term} {more_places[(i+len(platform))%len(more_places)]}'})
    for place in more_places:
        for term in more_terms:
            result.append({'platform':'Open web',
                           'q':f'{place} {term} CAD разработчик портфолио email linkedin'})
    # v1.6: grow the pool with precisely targeted developer/API searches.
    # Existing queries above remain byte-for-byte identical for SQLite resume.
    expansion_terms=[
        'FreeCAD Python workbench developer',
        'CadQuery parametric automation Python',
        'build123d Python CAD developer',
        'OpenCascade OCCT C++ engineer',
        'PythonOCC Open CASCADE developer',
        'SolidWorks API C# add-in developer',
        'SolidWorks VBA macro programming',
        'Autodesk Inventor iLogic C# developer',
        'Fusion 360 Python API automation',
        'Siemens NX Open C++ C# developer',
        'CATIA CAA C++ programming',
        'КОМПАС-3D API программист',
        'nanoCAD .NET C# разработчик',
        'AutoCAD ObjectARX C++ разработчик',
        'AutoCAD .NET API C# разработчик',
        'Revit API BIM C# developer',
        'RhinoCommon Grasshopper Python developer',
        'BricsCAD BRX C++ developer',
        'Parasolid geometry kernel C++',
        'CGAL computational geometry C++',
        'NURBS BRep geometric modeling developer',
        'STEP IGES AP242 CAD converter developer',
        'IFCOpenShell BIM Python developer',
        'CAD CAM postprocessor Python C++ developer',
        'САПР геометрическое ядро программист C++',
        'разработчик плагинов CAD C# Python',
    ]
    expansion_cities=[
        'Москва','Санкт-Петербург','Новосибирск','Казань','Екатеринбург',
        'Самара','Томск','Нижний Новгород','Пермь','Уфа','Воронеж',
        'Красноярск','Омск','Ростов-на-Дону','Челябинск','Иркутск',
    ]
    # Narrow site-specific queries beat general geometry/3D queries for recruiting.
    expansion_sites=[
        ('LinkedIn','site:linkedin.com/in/'),
        ('Habr Career','site:career.habr.com/'),
        ('HH.ru','site:hh.ru/resume/'),
        ('Freelance','site:freelance.ru/'),
    ]
    for platform,site in expansion_sites:
        for i,term in enumerate(expansion_terms):
            for j,city in enumerate(expansion_cities):
                result.append({'platform':platform,
                               'q':f'{site} {term} {city} разработчик САПР'})
    for city in expansion_cities:
        for term in expansion_terms:
            result.append({'platform':'Open web',
                           'q':f'{city} {term} инженер CAD API контакты linkedin'})
    # Stable de-dup across runs.
    dedup=[];keys=set()
    for q in result:
        if q['q'] not in keys:dedup.append(q);keys.add(q['q'])
    return dedup


def parse_json_fragment(s):
    s=(s or '').strip()
    s=re.sub(r'^```(?:json)?\s*|\s*```$','',s,flags=re.I)
    try:return json.loads(s)
    except json.JSONDecodeError:
        start=min([k for k in [s.find('{'),s.find('[')] if k>=0],default=-1)
        if start<0:raise
        decoder=json.JSONDecoder()
        return decoder.raw_decode(s[start:])[0]


def source_match(url,allowed):
    p=clean_url(url)
    if not p:return False
    a=urlsplit(p)
    for src in allowed:
        b=urlsplit(clean_url(src))
        if a.hostname==b.hostname and (a.path==b.path or a.path.rstrip('/')==b.path.rstrip('/') or
                                       b.path.rstrip('/').startswith(a.path.rstrip('/')+'/')):
            return True
    return False


def azure_search_one(client,deployment,q):
    """One network-only Azure task. Never use SQLite from a worker thread."""
    instruction=(
        'Search the PUBLIC web for real Russian-based CAD software developers, CAD automation engineers, '
        'or researchers in CAD geometry software relevant to the query. Include only real individuals, not firms or projects. '
        'Collect at most 8 people directly evidenced by PUBLIC profile pages. '
        'Do not guess emails, LinkedIn links, Russian location, or CAD experience. '
        'Do not invent URLs, infer Russian location from a Russian-sounding name, or include private resumes. '
        'Use only professional email visibly published or explicitly listed LinkedIn; contact page is acceptable. '
        'Return only JSON: {"people":[{"name":"", "platform":"", "profile_url":"", '
        '"location":"", "email":"", "linkedin":"", "contact_page":"", '
        '"skills":[""], "cad_evidence_url":"", "contact_evidence_url":"", "reason":""}]}. '
        'If any essential field is unsupported, leave it empty; fewer reliable leads are preferable. '
        'Perform web search; do not answer from memory. Query: '+q['q'])
    response=client.responses.create(model=deployment,tools=[{'type':'web_search'}],
        include=['web_search_call.action.sources'],input=instruction)
    outputs=getattr(response,'output',[]) or []
    if not any(getattr(x,'type',None)=='web_search_call' for x in outputs):
        raise RuntimeError('Model did not call web_search; do not trust ungrounded leads')
    sources=[]
    for out in outputs:
        if getattr(out,'type','')=='web_search_call':
            d=out.model_dump() if hasattr(out,'model_dump') else {}
            sources.extend(x.get('url','') for x in (d.get('action',{}).get('sources',[]) or []) if isinstance(x,dict))
    parsed=parse_json_fragment(getattr(response,'output_text',''))
    people=parsed.get('people',[]) if isinstance(parsed,dict) else parsed
    if not isinstance(people,list):raise RuntimeError('Invalid people list')
    entries=[]
    for p in people[:8]:
        if not isinstance(p,dict):continue
        profile=clean_url(p.get('profile_url'))
        evidence=clean_url(p.get('cad_evidence_url'))
        contact_source=clean_url(p.get('contact_evidence_url'))
        if not profile or not source_match(profile,sources):continue
        if evidence and not source_match(evidence,sources):evidence=''
        if contact_source and not source_match(contact_source,sources):contact_source=''
        email=norm_email(p.get('email')) if contact_source else ''
        li=linkedin_link(p.get('linkedin')) if contact_source else ''
        cp=clean_url(p.get('contact_page')) if contact_source else ''
        entries.append({'name':str(p.get('name',''))[:160],
            'platform':str(p.get('platform') or q['platform'])[:55],
            'profile_url':profile,'location':str(p.get('location') or '')[:150],
            'bio':str(p.get('reason') or '')[:400], 'email':email,'linkedin':li,'contact_page':cp,
            'contact_evidence':contact_source,'contact_trust':'search',
            'skills':[str(x)[:60] for x in (p.get('skills') or []) if isinstance(x,str)],
            'cad_evidence':[evidence] if evidence else [],
            'sources':list_unique([profile,evidence,contact_source]),
            'repos':0,'commits':0,'confidence':'Web search reported (review required)','checked_at':now()})
    return entries


def azure_hard_error(exc):
    """Auth/configuration/exhausted-billing errors are not transient TPM limits."""
    status=getattr(exc,'status_code',None)
    msg=str(exc).lower()
    return (status in (400,401,403,404) or
            any(x in msg for x in ('insufficient_quota','billing_hard_limit',
                                   'invalid_api_key','permissiondenied','authenticationerror',
                                   'deploymentnotfound','deployment not found')))


def azure_rate_error(exc):
    """Azure's 429 token/request throttling is usually recoverable after cooldown."""
    if azure_hard_error(exc):return False
    status=getattr(exc,'status_code',None)
    msg=str(exc).lower()
    return status==429 or 'ratelimiterror' in type(exc).__name__.lower() or any(
        x in msg for x in ('429','rate_limit_exceeded','token rate limit','too_many_requests'))


def azure_retry_after(exc):
    """Read server-supplied cooldown (seconds), without assuming it is present."""
    response=getattr(exc,'response',None)
    headers=getattr(response,'headers',{}) or {}
    try:
        value=headers.get('retry-after') or headers.get('Retry-After')
        if value:
            try:return min(600.,max(0.,float(value)))
            except (ValueError,TypeError):
                from datetime import datetime as _dt
                parsed=parsedate_to_datetime(value)
                return min(600.,max(0.,(parsed-_dt.now(timezone.utc)).total_seconds()))
        ms=headers.get('retry-after-ms') or headers.get('x-ms-retry-after-ms')
        if ms:return min(600.,max(0.,float(ms)/1000.))
    except (ValueError,TypeError,OverflowError):pass
    return 0.


def azure_query_pool(args):
    """Deterministic query selection. Web-only mode excludes code-host searches."""
    queries=make_web_queries()
    grouped={}
    for q in queries:
        if q['platform']=='GitHub' and 'github' not in args.sources:continue
        if q['platform']=='GitLab' and 'gitlab' not in args.sources:continue
        grouped.setdefault(q['platform'],[]).append(q)
    interleaved=[]
    while any(grouped.values()):
        for value in grouped.values():
            if value:interleaved.append(value.pop(0))
    return interleaved[:args.web_queries]


def azure_pending(store,args):
    return sum(store.due('web:query:'+q['q'],args.refresh_days) for q in azure_query_pool(args))


def run_azure_web(store,args,call_cap=None):
    """Bounded, adaptive Azure scheduler. All DB operations stay on main thread.

    A throttled request is *not* counted as a failed SQLite attempt: it is
    returned to the queue after cooldown. Every HTTP submission, including
    throttled submissions, counts against the API-call budget.
    """
    if 'web' not in args.sources:
        return {'submitted':0,'saved':0,'fatal':False,'available':0,'reason':'disabled',
                'rate_limited':False,'recommended_pause':0}
    key=os.getenv('AZURE_OPENAI_API_KEY','').strip()
    endpoint=os.getenv('AZURE_OPENAI_ENDPOINT','').strip()
    deployment=os.getenv('AZURE_OPENAI_DEPLOYMENT','').strip()
    if not (key and endpoint and deployment):
        print('[web] skipped: set AZURE_OPENAI_ENDPOINT, AZURE_OPENAI_API_KEY, AZURE_OPENAI_DEPLOYMENT')
        return {'submitted':0,'saved':0,'fatal':True,'available':0,'reason':'missing Azure credentials',
                'rate_limited':False,'recommended_pause':0}
    try:from openai import OpenAI
    except ImportError:
        print('[web] missing openai package; pip install openai',file=sys.stderr)
        return {'submitted':0,'saved':0,'fatal':True,'available':0,'reason':'missing openai package',
                'rate_limited':False,'recommended_pause':0}
    endpoint=endpoint.rstrip('/')+'/'
    if '/openai/v1/' not in endpoint:endpoint=endpoint.rstrip('/')+'/openai/v1/'
    client=OpenAI(api_key=key,base_url=endpoint,timeout=180.0,max_retries=0)
    todo=[q for q in azure_query_pool(args)
          if store.due('web:query:'+q['q'],args.refresh_days)]
    # Limit *HTTP submissions*, not unique queries: 429 retries must count too.
    limit=(min(args.max_azure_calls,
              args.max_azure_calls if call_cap is None else max(0,call_cap)) if todo else 0)
    active=min(args.azure_workers,args.azure_start_workers)
    print(f'[azure web] available={len(todo)}, cap={limit}, max workers={args.azure_workers}, '
          f'start workers={active}; successful queries resumed from SQLite',flush=True)
    if not limit:
        return {'submitted':0,'saved':0,'fatal':False,'available':len(todo),
                'reason':'no work or cycle budget','rate_limited':False,'recommended_pause':0}

    from collections import deque
    pending=deque(todo)
    submitted=0; finished=0; saved_total=0
    rate_hits=0; cooldown_rounds=0; successes_since_throttle=0
    rate_limited=False; fatal=False; reason='ok'; recommended_pause=0.
    last_start=0.; blocked_until=0.; futures={}
    pause_min=args.azure_pause_min
    pause_max=args.azure_pause_max

    def schedule(pool):
        nonlocal submitted,last_start
        while pending and len(futures)<active and submitted<limit and not fatal:
            clock=time.monotonic()
            if clock < blocked_until:return
            if submitted:
                gap=random.uniform(pause_min,pause_max)
                if clock-last_start<gap:return
            q=pending.popleft()
            fut=pool.submit(azure_search_one,client,deployment,q)
            futures[fut]=q
            submitted+=1
            last_start=time.monotonic()
            print(f'[azure start {submitted}/{limit}] {q["platform"]} | {q["q"][:60]}',flush=True)
            # Avoid launching all requests at once: global pacing also
            # applies when free worker slots are available.
            if pause_min>0 or pause_max>0:return

    with concurrent.futures.ThreadPoolExecutor(max_workers=args.azure_workers) as pool:
        while (pending or futures) and not fatal:
            schedule(pool)
            if not futures:
                if submitted>=limit:break
                delay=max(0.,blocked_until-time.monotonic(),
                          last_start+pause_min-time.monotonic() if submitted else 0.)
                time.sleep(max(0.05,min(1.,delay)))
                continue
            # Short wait: can fill other available slots after the shared pause.
            done,_=concurrent.futures.wait(futures,timeout=0.5,
                return_when=concurrent.futures.FIRST_COMPLETED)
            if not done:continue
            for future in done:
                q=futures.pop(future)
                jobkey='web:query:'+q['q']
                finished+=1
                try:
                    entries=future.result()
                    saved=sum(bool(store.put(e)) for e in entries)
                    saved_total+=saved
                    store.mark(jobkey,True)
                    successes_since_throttle+=1
                    cooldown_rounds=0
                    if successes_since_throttle>=8 and active<args.azure_workers:
                        active+=1
                        successes_since_throttle=0
                        print(f'[azure adapt] 8 successes; workers increased to {active}',flush=True)
                    print(f'[azure done {finished}/{limit}] {q["platform"]} | '
                          f'{q["q"][:60]} -> {saved} grounded profiles; saved={saved_total}',flush=True)
                except Exception as exc:
                    if azure_rate_error(exc):
                        # No store.mark: retryable 429 MUST NOT consume the
                        # SQLite job attempt allowance (MAX_ATTEMPTS).
                        rate_limited=True
                        rate_hits+=1
                        successes_since_throttle=0
                        pending.appendleft(q)
                        active=max(1,active//2)
                        # Wait for the rolling TPM window / Retry-After.
                        delay=max(args.azure_tpm_cooldown,
                                  azure_retry_after(exc),
                                  min(600.,args.azure_tpm_cooldown*(2**min(3,cooldown_rounds))))
                        delay+=random.uniform(0,3)
                        blocked_until=max(blocked_until,time.monotonic()+delay)
                        recommended_pause=max(recommended_pause,delay)
                        pause_min=min(60.,max(pause_min,args.azure_pause_min*2))
                        pause_max=min(90.,max(pause_max,args.azure_pause_max*2))
                        print(f'[azure 429] TPM/RPM throttle; workers={active}, '
                              f'cooldown={delay:.0f}s; query kept retryable in SQLite.',flush=True)
                    elif azure_hard_error(exc):
                        store.mark(jobkey,False,str(exc))
                        fatal=True;reason='auth/configuration/quota'
                        print(f'[azure stop] Non-retryable Azure configuration/auth error: '
                              f'{type(exc).__name__}: {exc}',file=sys.stderr,flush=True)
                    else:
                        store.mark(jobkey,False,str(exc))
                        print(f'[warning] Azure query failed: '
                              f'{type(exc).__name__}: {exc}',file=sys.stderr,flush=True)
            if rate_limited and not futures:
                cooldown_rounds+=1
                if cooldown_rounds>args.azure_max_cooldowns:
                    reason='sustained rate throttling'
                    fatal=True
                    print('[azure stop] Repeated TPM throttling. All throttled queries remain '
                          'retryable. Reduce --azure-workers or increase pauses.',flush=True)
            if submitted>=limit and not futures:break
        # Drain already-started futures if a hard error was encountered.
        for future,q in list(futures.items()):
            jobkey='web:query:'+q['q']
            try:
                entries=future.result()
                saved_total+=sum(bool(store.put(e)) for e in entries)
                store.mark(jobkey,True)
            except Exception as exc:
                if not azure_rate_error(exc):store.mark(jobkey,False,str(exc))
            finally:
                finished+=1

    print(f'[web] model calls submitted this cycle={submitted}; completed={finished}; '
          f'profiles written={saved_total}; throttled={rate_hits}. '
          'Check Azure billing for web_search usage.',flush=True)
    return {'submitted':submitted,'saved':saved_total,'fatal':fatal,
            'available':len(todo),'reason':reason,'rate_limited':rate_limited,
            'recommended_pause':recommended_pause}


def validate_web_code_profiles(api,store,args):
    """Promote search-discovered GitHub/GitLab profiles only after API evidence."""
    done=0
    for p in store.all_profiles():
        if done>=args.web_profile_validation:break
        if p.get('confidence')=='API verified':continue
        url=urlsplit(p.get('profile_url',''))
        host=(url.hostname or '').lower()
        path=url.path.strip('/').split('/')
        if len(path)!=1 or not re.fullmatch(r'[a-zA-Z0-9_.-]+',path[0]):continue
        if host not in ('github.com','gitlab.com','www.github.com'):continue
        key='validate:code:'+host+':'+path[0].lower()
        if not store.due(key,args.refresh_days):continue
        done+=1
        try:
            if 'github.com' in host:
                c=enrich_github(api,path[0],gh_candidate(path[0]))
            else:
                users=api.get('https://gitlab.com/api/v4/users',{'username':path[0],'per_page':10}) or []
                user=next((u for u in users if u.get('username','').lower()==path[0].lower()),None)
                c=enrich_gitlab(api,user) if user else None
            if c:
                # Preserve any additional sourced LinkedIn/contact evidence from the search.
                store.put(c)
            store.mark(key,True)
        except Exception as e:
            store.mark(key,False,str(e))
            print('[warning] validation of indexed code profile:',e,file=sys.stderr)
    if done:print(f'[cross-validate] checked {done} web-discovered code profiles by official APIs')


def rows_from_csv(filepath):
    with open(filepath,encoding='utf-8-sig',newline='') as f:
        r=csv.DictReader(f)
        for row in r:yield {str(k).strip().lower().replace(' ','_'):v for k,v in row.items() if k}


def import_public_leads(store,path):
    count=0
    for row in rows_from_csv(path):
        url=clean_url(row.get('profile_url') or row.get('url') or '')
        if not url:continue
        loc=row.get('location') or row.get('country') or ''
        skills=row.get('cad_skills') or row.get('skills') or ''
        evidence=clean_url(row.get('cad_evidence_url') or row.get('evidence_url') or '')
        contact_evidence=clean_url(row.get('contact_evidence_url') or '')
        li=linkedin_link(row.get('linkedin') or '') if contact_evidence else ''
        em=norm_email(row.get('email') or '') if contact_evidence else ''
        c={'name':row.get('name') or row.get('username') or '',
           'platform':row.get('platform') or 'Imported public lead','profile_url':url,
           'location':loc,'skills':[s.strip() for s in re.split('[,;|]',skills) if s.strip()],
           'email':em,'linkedin':li,'contact_page':clean_url(row.get('contact_page')) if contact_evidence else '',
           'contact_evidence':contact_evidence, 'contact_trust':'imported',
           'cad_evidence':[evidence] if evidence else [],'sources':list_unique([url,evidence,contact_evidence]),
           'bio':'Imported: provenance/identity needs review','repos':0,'commits':0,
           'confidence':'Imported (review required)','checked_at':now()}
        if store.put(c):count+=1
    print(f'[import] {count} public-profile URLs imported for review')


def candidate_assess(c):
    skills=c.get('skills') or []
    text=' '.join(skills)+' '+(c.get('bio') or '')
    strong=any(label in skills for label in STRONG_SKILLS) or bool(extract_skills(text) and
              any(s in STRONG_SKILLS for s in extract_skills(text)))
    relevant_evidence=bool(c.get('cad_evidence'))
    contact=bool(norm_email(c.get('email')) or linkedin_link(c.get('linkedin')) or
                 (clean_url(c.get('contact_page')) and clean_url(c.get('contact_evidence'))))
    geo=geo_proof(c.get('location'))
    verified_api=c.get('confidence')=='API verified'
    score=(35 if relevant_evidence and strong else (15 if strong else 0)) + (30 if geo else 0) + \
          (25 if contact else 0) + (10 if verified_api else 0)
    reasons=[]
    if not geo:reasons.append('Russian location not substantiated')
    if not strong:reasons.append('CAD programming/development not substantiated')
    if not relevant_evidence:reasons.append('No direct CAD project/evidence URL')
    if not contact:reasons.append('No public professional contact')
    elif c.get('contact_trust')!='direct':reasons.append('Contact is search/import reported, not directly verified')
    if not verified_api:reasons.append('Web/import claim requires independent verification')
    qualified=geo and strong and relevant_evidence and contact and verified_api and c.get('contact_trust')=='direct'
    return qualified,score,'; '.join(reasons) or 'Public API profile + CAD evidence + RU location + contact'


def merge_profile_group(group):
    # Preserve best-evidenced primary profile and collect corroborating source URLs.
    if len(group)==1:return group[0]
    group.sort(key=lambda c:(candidate_assess(c)[1],c.get('confidence')=='API verified'),reverse=True)
    best=dict(group[0])
    for other in group[1:]:
        for field in ('email','linkedin','contact_page','location','name','contact_evidence'):
            if not best.get(field):best[field]=other.get(field,'')
        if not best.get('contact_trust') and other.get('contact_trust')=='direct':
            best['contact_trust']='direct'
        for field in ('skills','cad_evidence','sources'):
            best[field]=list_unique((best.get(field) or [])+(other.get(field) or []))
        best['repos']=max(int(best.get('repos') or 0),int(other.get('repos') or 0))
        best['commits']=max(int(best.get('commits') or 0),int(other.get('commits') or 0))
        best['sources']=list_unique(best['sources']+[other.get('profile_url','')])
    return best


def dedupe_candidates(profiles):
    # Avoid merging merely similar Russian names, jobs, or company shared mailboxes.
    parent=list(range(len(profiles)))
    def root(i):
        while parent[i]!=i:parent[i]=parent[parent[i]];i=parent[i]
        return i
    def union(i,j):
        a,b=root(i),root(j)
        if a!=b:parent[max(a,b)]=min(a,b)
    seen={}
    for i,c in enumerate(profiles):
        email=norm_email(c.get('email'))
        linkedin=linkedin_link(c.get('linkedin'))
        keys=[]
        if email:keys.append(('email',email))
        if linkedin:keys.append(('linkedin',linkedin.lower()))
        for key in keys:
            if key in seen:union(i,seen[key])
            else:seen[key]=i
    groups={}
    for i in range(len(profiles)):groups.setdefault(root(i),[]).append(profiles[i])
    out=[]
    for group in groups.values():
        group.sort(key=lambda c:(candidate_assess(c)[1],c.get('confidence')=='API verified'),reverse=True)
        best=dict(group[0])
        for other in group[1:]:
            for field in ('email','linkedin','contact_page','location','name','contact_evidence'):
                if not best.get(field):best[field]=other.get(field,'')
            if not best.get('contact_trust') and other.get('contact_trust')=='direct':
                best['contact_trust']='direct'
            for field in ('skills','cad_evidence','sources'):
                best[field]=list_unique((best.get(field) or [])+(other.get(field) or []))
            best['repos']=max(int(best.get('repos') or 0),int(other.get('repos') or 0))
            best['commits']=max(int(best.get('commits') or 0),int(other.get('commits') or 0))
            best['sources']=list_unique(best['sources']+[other.get('profile_url','')])
            # Do NOT automatically upgrade imported/web evidence to API-verified identity.
        out.append(best)
    return out


def record_values(c,score,reason):
    return [c.get('name',''), 'Russia (profile stated)' if geo_proof(c.get('location','')) else '',
       c.get('location',''), c.get('platform',''),c.get('profile_url',''),
       c.get('email',''),c.get('linkedin',''),c.get('contact_page',''),
       ', '.join(c.get('skills') or []), '; '.join(c.get('cad_evidence') or []),
       c.get('contact_evidence',''),'; '.join(c.get('sources') or []),
       int(c.get('repos') or 0),int(c.get('commits') or 0),score,
       c.get('confidence',''),reason,c.get('checked_at','')]


def protect_excel_text(value):
    s=str(value if value is not None else '')
    # All data are written as literal inline strings, never executed as formulas.
    # XML 1.0 allows tab/LF/CR and valid Unicode scalar values only.
    # Azure and public profiles can occasionally contain invalid XML control
    # characters or Unicode noncharacters that make Excel repair entire sheets.
    return ''.join(ch for ch in s if ch in '\t\n\r' or
                   (0x20 <= ord(ch) <= 0xD7FF) or
                   (0xE000 <= ord(ch) <= 0xFFFD) or
                   (0x10000 <= ord(ch) <= 0x10FFFF))[:32500]


def excel_column(n):
    result=''
    while n:
        n,r=divmod(n-1,26);result=chr(65+r)+result
    return result


# Workbook layout deliberately matches our original GitHub/GitLab and China CAD
# candidate spreadsheets: useful contact fields first, individually colored
# column headers, live hyperlinks and a compact one-row-per-person table.
DISPLAY_HEADERS = [
    'Username / Name', 'CAD Repository / Project', 'Country', 'Email / LinkedIn',
    'Platform', 'CAD specialization', 'Profile URL', 'CAD score',
    'Verification', 'Evidence URL', 'Location (raw)', 'Last checked'
]
# The removed columns remain available in SQLite and detailed audit CSVs;
# only the presentation workbook becomes compact.
HEADER_PALETTE = [
    '123C69', '197A6D', '0E7490', '8B5E34', '6D4C91', '6D4C91',
    '197A6D', 'C25454', '6D4C91', '197A6D', '0E7490', '123C69'
]
COLUMN_WIDTHS = [27, 40, 24, 38, 19, 42, 42, 14, 27, 41, 28, 20]


def make_display_row(row):
    evidence=next((s.strip() for s in str(row[9]).split(';') if s.strip().startswith(('https://','http://'))),'')
    profile=str(row[4]).strip()
    email=str(row[5]).strip()
    linkedin=str(row[6]).strip()
    contact=email or linkedin or str(row[7]).strip()
    return [row[0], evidence, row[1] or row[2], contact, row[3], row[8],
            profile, row[14], row[15], row[10], row[2], row[17]]


def excel_styles_xml():
    # Style IDs are created deterministically; no external XLSX dependency.
    fonts=[
        '<font><sz val="11"/><name val="Calibri"/><b/><color rgb="FFFFFFFF"/></font>',
        '<font><sz val="10"/><name val="Calibri"/><color rgb="FF263647"/></font>',
        '<font><sz val="10"/><name val="Calibri"/><u/><color rgb="FF1261A0"/></font>',
        '<font><sz val="10"/><name val="Calibri"/><b/><color rgb="FF183452"/></font>',
        '<font><sz val="10"/><name val="Calibri"/><b/><color rgb="FF176D4E"/></font>',
        '<font><sz val="10"/><name val="Calibri"/><b/><color rgb="FF9D5A10"/></font>',
    ]
    fills=['<fill><patternFill patternType="none"/></fill>',
           '<fill><patternFill patternType="gray125"/></fill>']
    for color in dict.fromkeys(HEADER_PALETTE+['F2F6F9','E8F4EC','FFF1DD','FAEAEA','E7EFF7']):
        fills.append('<fill><patternFill patternType="solid"><fgColor rgb="FF'+color+'"/><bgColor indexed="64"/></patternFill></fill>')
    # white + light gray borders are similar to the China-company workbook.
    borders=['<border><left/><right/><top/><bottom/><diagonal/></border>',
             '<border><left style="hair"><color rgb="FFE2E8ED"/></left>'
             '<right style="hair"><color rgb="FFE2E8ED"/></right>'
             '<top/><bottom style="hair"><color rgb="FFE2E8ED"/></bottom><diagonal/></border>']
    color_to_fill={c:i+2 for i,c in enumerate(dict.fromkeys(HEADER_PALETTE+['F2F6F9','E8F4EC','FFF1DD','FAEAEA','E7EFF7']))}
    xfs=[]
    def add(font=1,fill=0,align='left',bold=False,number=False):
        sid=len(xfs)
        a='horizontal="'+align+'" vertical="center"' + (' wrapText="1"' if bold else '')
        xfs.append('<xf numFmtId="'+('1' if number else '0')+'" fontId="'+str(font)+'" fillId="'+str(fill)+'" borderId="1" xfId="0" applyFill="1" applyFont="1" applyAlignment="1"><alignment '+a+'/></xf>')
        return sid
    base=add()
    alt=add(fill=color_to_fill['F2F6F9'])
    link=add(font=2)
    linkalt=add(font=2,fill=color_to_fill['F2F6F9'])
    num=add(align='center',number=True)
    numalt=add(fill=color_to_fill['F2F6F9'],align='center',number=True)
    good=add(font=4,fill=color_to_fill['E8F4EC'],align='center')
    caution=add(font=5,fill=color_to_fill['FFF1DD'],align='center')
    bad=add(fill=color_to_fill['FAEAEA'],align='center')
    overview_label=add(font=3,fill=color_to_fill['E7EFF7'],bold=True)
    overview_value=add(font=3,fill=color_to_fill['F2F6F9'])
    header_ids={c:add(font=0,fill=color_to_fill[c],align='center',bold=True) for c in dict.fromkeys(HEADER_PALETTE)}
    styles=('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
      '<styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">'
      '<fonts count="'+str(len(fonts))+'">'+''.join(fonts)+'</fonts>'
      '<fills count="'+str(len(fills))+'">'+''.join(fills)+'</fills>'
      '<borders count="'+str(len(borders))+'">'+''.join(borders)+'</borders>'
      '<cellStyleXfs count="1"><xf numFmtId="0" fontId="1" fillId="0" borderId="0"/></cellStyleXfs>'
      '<cellXfs count="'+str(len(xfs))+'">'+''.join(xfs)+'</cellXfs>'
      '<cellStyles count="1"><cellStyle name="Normal" xfId="0" builtinId="0"/></cellStyles>'
      '</styleSheet>')
    return styles,{'base':base,'alt':alt,'link':link,'linkalt':linkalt,
                   'num':num,'numalt':numalt,'good':good,'caution':caution,'bad':bad,
                   'overview_label':overview_label,'overview_value':overview_value,
                   'header_ids':header_ids}


def worksheet_xml(headers,rows,hyperlink_col=None,tab_color="3182BD",styles=None):
    """Write a styled recruiting sheet with real hyperlink relationships."""
    overview=headers[0]=='Metric'
    columns=[32,92] if overview else COLUMN_WIDTHS
    cols=''.join(f'<col min="{i}" max="{i}" width="{width}" customWidth="1"/>'
                 for i,width in enumerate(columns,start=1))
    freeze=('<sheetViews><sheetView workbookViewId="0"/></sheetViews>' if overview else
            '<sheetViews><sheetView workbookViewId="0"><pane xSplit="2" ySplit="1" topLeftCell="C2" activePane="bottomRight" state="frozen"/></sheetView></sheetViews>')
    xml=['<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',
         '<worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
         'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships">',
         f'<sheetPr><tabColor rgb="FF{tab_color}"/></sheetPr>',
         freeze,
         '<sheetFormatPr defaultRowHeight="22"/><cols>'+cols+'</cols>',
         '<sheetData>']
    all_rows=[headers]+rows
    relations=[]
    hids=styles['header_ids']
    for ri,values in enumerate(all_rows,1):
        xml.append(f'<row r="{ri}"'+(' ht="34" customHeight="1"' if ri==1 else (' ht="23" customHeight="1"' if not overview else ''))+'>')
        for ci,raw in enumerate(values,1):
            ref=f'{excel_column(ci)}{ri}'
            first=ri==1
            field_index=ci-1
            url=''
            if not first and not overview:
                profile=clean_url(values[6])
                if field_index==0:
                    url=profile
                elif field_index==1:
                    url=clean_url(raw)
                elif field_index==3:
                    text=str(raw).strip()
                    url='mailto:'+text if norm_email(text) else clean_url(text)
                elif field_index in (6,9):
                    url=clean_url(raw)
            if first:
                color='123C69' if overview else HEADER_PALETTE[field_index%len(HEADER_PALETTE)]
                style=hids[color]
            elif overview:
                style=styles['overview_label'] if ci==1 else styles['overview_value']
            elif field_index==7:
                score=float(raw or 0)
                style=styles['good'] if score>=80 else styles['caution'] if score>=45 else styles['bad']
            elif field_index==8:
                confidence=str(raw).lower()
                style=styles['good'] if 'api verified' in confidence else styles['caution']
            elif url:
                style=styles['linkalt'] if ri%2==0 else styles['link']
            else:
                style=styles['alt'] if ri%2==0 else styles['base']
            if isinstance(raw,(int,float)) and not first:
                xml.append(f'<c r="{ref}" s="{style}"><v>{raw}</v></c>')
            else:
                value=protect_excel_text(raw)
                xml.append(f'<c r="{ref}" s="{style}" t="inlineStr"><is><t xml:space="preserve">{xe(value)}</t></is></c>')
            if url:relations.append((ref,url))
        xml.append('</row>')
    xml.append('</sheetData>')
    if not overview:
        xml.append(f'<autoFilter ref="A1:{excel_column(len(headers))}{len(all_rows)}"/>')
    # OOXML worksheet child order is significant. In Excel's CT_Worksheet
    # schema, <hyperlinks> MUST precede <printOptions> and <pageSetup>.
    # The previous order caused Excel to repair/remove sheets 2-5.
    if relations:
        xml.append('<hyperlinks>')
        for idx,(cell,url) in enumerate(relations,1):
            xml.append(f'<hyperlink ref="{cell}" r:id="rId{idx}"/>')
        xml.append('</hyperlinks>')
    if not overview:
        xml.append('<printOptions headings="0" gridLines="0"/>')
        xml.append('<pageSetup orientation="landscape" fitToWidth="1"/>')
    xml.append('</worksheet>')
    relxml=['<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',
            '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">']
    for idx,(cell,url) in enumerate(relations,1):
        escaped_url=xe(url, {'"': '&quot;'})
        relxml.append(f'<Relationship Id="rId{idx}" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/hyperlink" '
                      f'Target="{escaped_url}" TargetMode="External"/>')
    relxml.append('</Relationships>')
    return ''.join(xml),''.join(relxml)


def export_excel(path,sheets):
    # OOXML, dependency free, preserving every profile from SQLite; no hidden truncation.
    content=['<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',
      '<Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types">',
      '<Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/>',
      '<Default Extension="xml" ContentType="application/xml"/>',
      '<Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>',
      '<Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/>']
    for i in range(1,len(sheets)+1):content.append(f'<Override PartName="/xl/worksheets/sheet{i}.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>')
    content.append('</Types>')
    wbxml=['<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',
      '<workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" '
      'xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><sheets>']
    wbrels=['<?xml version="1.0" encoding="UTF-8" standalone="yes"?>',
      '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">']
    for i,(name,_,_) in enumerate(sheets,1):
        wbxml.append(f'<sheet name="{xe(name)}" sheetId="{i}" r:id="rId{i}"/>')
        wbrels.append(f'<Relationship Id="rId{i}" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet{i}.xml"/>')
    wbxml.append('</sheets></workbook>')
    wbrels.append(f'<Relationship Id="rId{len(sheets)+1}" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/>')
    wbrels.append('</Relationships>')
    styles,style_ids=excel_styles_xml()
    package_rels=('<?xml version="1.0" encoding="UTF-8" standalone="yes"?>'
      '<Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">'
      '<Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/></Relationships>')
    tmp=path.with_name(path.name+'.tmp')
    with ZipFile(tmp,'w',compression=ZIP_DEFLATED) as z:
        z.writestr('[Content_Types].xml',''.join(content))
        z.writestr('_rels/.rels',package_rels)
        z.writestr('xl/workbook.xml',''.join(wbxml))
        z.writestr('xl/_rels/workbook.xml.rels',''.join(wbrels))
        z.writestr('xl/styles.xml',styles)
        for i,(_,headers,rows) in enumerate(sheets,1):
            sheetxml,rels=worksheet_xml(headers,rows,tab_color=('123C69','197A6D','B7791F','8B5E34','6375A8','8C98A5')[(i-1)%6],styles=style_ids)
            z.writestr(f'xl/worksheets/sheet{i}.xml',sheetxml)
            z.writestr(f'xl/worksheets/_rels/sheet{i}.xml.rels',rels)
    # Validate ALL XML parts before replacing the existing workbook. This is
    # deliberately stricter than checking that ZipFile itself is readable.
    # Excel often "repairs" valid XML with worksheet elements in the wrong order.
    validate_excel_package(tmp)
    tmp.replace(path)


def validate_excel_package(path):
    """Fail closed on malformed worksheet XML and unsafe OOXML child order."""
    ns='{http://schemas.openxmlformats.org/spreadsheetml/2006/main}'
    rel_ns='{http://schemas.openxmlformats.org/officeDocument/2006/relationships}'
    with ZipFile(path, 'r') as archive:
        bad=archive.testzip()
        if bad:
            raise ValueError(f'Invalid XLSX ZIP member: {bad}')
        for name in archive.namelist():
            if not (name.endswith('.xml') or name.endswith('.rels')):
                continue
            root=ET.fromstring(archive.read(name))
            if not (name.startswith('xl/worksheets/sheet') and name.endswith('.xml')):
                continue
            children=[el.tag for el in root]
            # Only enforce the nodes whose relative order matters here.
            canonical=['autoFilter','hyperlinks','printOptions','pageSetup']
            present=[key for key in canonical if ns+key in children]
            offsets=[children.index(ns+key) for key in present]
            if offsets!=sorted(offsets):
                raise ValueError(f'Invalid XLSX worksheet element order in {name}')
            rels_name=name.replace('xl/worksheets/', 'xl/worksheets/_rels/')+'.rels'
            if ns+'hyperlinks' in children:
                if rels_name not in archive.namelist():
                    raise ValueError(f'Missing hyperlink relationships for {name}')
                relationship_root=ET.fromstring(archive.read(rels_name))
                valid_ids={elem.attrib.get('Id') for elem in relationship_root}
                link_group=root.find(ns+'hyperlinks')
                for link in link_group:
                    if link.attrib.get(rel_ns+'id') not in valid_ids:
                        raise ValueError(f'Unresolved hyperlink in {name}')


def export(store,args):
    """Recruiter-facing export: Russian CAD candidates only.

    Excluded/uncertain profiles remain in the SQLite source of truth so that
    no existing discovery progress or raw evidence is destroyed.
    """
    people=store.merged_profiles()
    qualified=[];review=[];ru_screening=[]
    excluded_foreign_or_unknown=0
    excluded_not_cad=0
    for p in people:
        geo=geo_proof(p.get('location'))
        if not geo:
            excluded_foreign_or_unknown+=1
            continue
        ok,score,reason=candidate_assess(p)
        strong,evidence=profile_cad_support(p)
        entry=record_values(p,score,reason)
        if ok and strong and evidence:
            qualified.append(entry)
        elif strong and evidence:
            review.append(entry)
        elif cad_screening_signal(p):
            # Explicit RU location + CAD signal, even without a project URL.
            # Screening is not an assurance of suitability or direct contacts.
            ru_screening.append(entry)
        else:
            excluded_not_cad+=1
    for seq in (qualified,review,ru_screening):
        seq.sort(key=lambda row:(row[14],row[0]),reverse=True)
    out=Path(args.out)
    out.parent.mkdir(parents=True,exist_ok=True)
    def csv_out(name,records):
        final=out.with_name(out.stem+'_'+name+'.csv')
        temp=final.with_suffix('.writing.csv')
        with open(temp,'w',newline='',encoding='utf-8-sig') as f:
            w=csv.writer(f);w.writerow(HEADERS)
            for record in records:
                w.writerow([("'"+v if isinstance(v,str) and v.lstrip().startswith(('=','+','-','@')) else v) for v in record])
        try:temp.replace(final)
        except PermissionError:
            print(f'[export warning] {final} is open; latest CSV kept at {temp}',file=sys.stderr)
    for name,records in [('qualified',qualified),('review',review),('ru_screening',ru_screening)]:
        csv_out(name,records)
    summary=[['Metric','Count / description'],
             ['Qualified',len(qualified)],
             ['Russia: strong CAD profiles to review',len(review)],
             ['Russia: CAD screening needed',len(ru_screening)],
             ['Russian CAD candidates shown',len(qualified)+len(review)+len(ru_screening)],
             ['Excluded: location not confirmed as Russian',excluded_foreign_or_unknown],
             ['Excluded: Russian location but no CAD signal',excluded_not_cad],
             ['Raw profiles saved in SQLite',store.stats()[0]],
             ['After identity dedup (SQLite)',len(people)],
             ['Created UTC',now()],
             ['Qualified rule','RU location + strong CAD technology + CAD evidence + directly verified contact'],
             ['Review RU rule','RU location + strong CAD technology + CAD evidence; additional verification required'],
             ['RU CAD Screening rule','RU location + at least one CAD signal; may lack project evidence or contact'],
             ['Location rule','Self-reported Russian location; do not infer Russia from a Russian name or .ru domain'],
             ['Data preservation','Excluded profiles are hidden from Excel, not removed from SQLite']]
    sheets=[('Overview',summary[0],summary[1:]),
            ('Qualified',DISPLAY_HEADERS,[make_display_row(r) for r in qualified]),
            ('Review RU',DISPLAY_HEADERS,[make_display_row(r) for r in review]),
            ('RU CAD Screening',DISPLAY_HEADERS,[make_display_row(r) for r in ru_screening])]
    try:
        export_excel(out,sheets)
    except PermissionError:
        pending=out.with_name(out.stem+'.pending.xlsx')
        export_excel(pending,sheets)
        print(f'[export warning] {out} is open; wrote {pending} instead.',file=sys.stderr)
    # These are legacy Excel-adjacent exports, not the SQLite source data.
    # The user requested to remove non-RU/Archive output entirely.
    for old_suffix in ('location_unverified','archive'):
        obsolete=out.with_name(out.stem+'_'+old_suffix+'.csv')
        if obsolete.exists():
            try:obsolete.unlink()
            except OSError:
                print(f'[export warning] Close obsolete CSV to remove it: {obsolete}',file=sys.stderr)
    print(f'[export] {out} | qualified={len(qualified)} RU_review={len(review)} '
          f'RU_screening={len(ru_screening)} omitted_geo={excluded_foreign_or_unknown} '
          f'omitted_no_cad={excluded_not_cad} after_dedup={len(people)}',flush=True)


def process_profiles(api,store,users,enricher,provider,args):
    work=[]
    for id_,seed in users.items():
        key=f'{provider}:profile:{id_}'
        if store.due(key,args.refresh_days):work.append((key,id_,seed))
    work=work[:args.max_profiles]
    print(f'[{provider}] queued {len(work)} profile enrichments')
    # Bound in-flight requests and keep ALL SQLite writes on the main thread.
    index=0
    with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
        while index<len(work):
            batch=work[index:index+args.workers];index+=len(batch)
            futures={pool.submit(enricher,api,uid,seed) if provider=='github' else
                     pool.submit(enricher,api,seed):(key,uid) for key,uid,seed in batch}
            for future in concurrent.futures.as_completed(futures):
                key,uid=futures[future]
                try:
                    entry=future.result()
                    if entry:store.put(entry)
                    store.mark(key,True)
                except Exception as exc:
                    store.mark(key,False,str(exc))
                    print(f'[warning] {provider} profile {uid}: {exc}',file=sys.stderr)
            if index%max(args.workers*5,1)==0: print(f'[{provider}] processed {index}/{len(work)}')


def main():
    parser=argparse.ArgumentParser(description='Russian CAD talent: public API + grounded web search, SQLite resume, Excel & CSV')
    parser.add_argument('--out',default='ru_cad_candidates.xlsx')
    parser.add_argument('--state',default=None,help='Default: <out>.sqlite3')
    parser.add_argument('--sources',default='github,gitlab,web',help='github,gitlab,web; e.g. github,gitlab to disable Azure')
    parser.add_argument('--workers',type=int,default=5)
    parser.add_argument('--pause-min',type=float,default=2.0)
    parser.add_argument('--pause-max',type=float,default=5.0)
    parser.add_argument('--timeout',type=int,default=30)
    parser.add_argument('--no-portfolio-inspection',dest='inspect_portfolios',action='store_false',
                        help='Disable robots-compliant public portfolio contact discovery')
    parser.set_defaults(inspect_portfolios=True)
    parser.add_argument('--max-profiles',type=int,default=600,help='Maximum profiles per provider per invocation')
    parser.add_argument('--github-queries',type=int,default=24)
    parser.add_argument('--github-pages',type=int,default=2)
    parser.add_argument('--seed-projects',type=int,default=len(SEEDS))
    parser.add_argument('--repo-search-terms',type=int,default=10)
    parser.add_argument('--max-searched-repos',type=int,default=40)
    parser.add_argument('--contributor-pages',type=int,default=2)
    parser.add_argument('--gitlab-terms',type=int,default=10)
    parser.add_argument('--gitlab-pages',type=int,default=2)
    parser.add_argument('--web-queries',type=int,default=80,help='Web query pool limit, not free!')
    parser.add_argument('--azure-workers',type=int,default=5,
                        help='Concurrent Azure web searches; separate from API profile workers (default 5)')
    parser.add_argument('--export-every',type=int,default=300,
                        help='Write an Excel/CSV snapshot every N stored profile results; 0=final only (default 300)')
    parser.add_argument('--web-profile-validation',type=int,default=100,
                        help='Cross-check indexed GitHub/GitLab people via official APIs')
    parser.add_argument('--max-azure-calls',type=int,default=80,help='Maximum billable model calls per run (web search may trigger multiple charged searches per call)')
    parser.add_argument('--auto-continue',action='store_true',
                        help='Run more Azure web batches until selected queries or overall budget are exhausted')
    parser.add_argument('--total-azure-calls',type=int,default=2400,
                        help='Overall submitted Azure model calls across auto cycles in THIS invocation')
    parser.add_argument('--max-cycles',type=int,default=12,
                        help='Maximum automatic Azure cycles in THIS invocation')
    parser.add_argument('--cooldown-seconds',type=float,default=20,
                        help='Wait between Azure cycles in seconds; not a quota reset')
    parser.add_argument('--azure-pause-min',type=float,default=1.5)
    parser.add_argument('--azure-pause-max',type=float,default=3.0)
    parser.add_argument('--azure-start-workers',type=int,default=2,
                        help='Conservative initial concurrency; adapt upward after successful searches')
    parser.add_argument('--azure-tpm-cooldown',type=float,default=75.0,
                        help='Minimum cooldown in seconds after 429 TPM throttling')
    parser.add_argument('--azure-max-cooldowns',type=int,default=4,
                        help='Stop after this many consecutive cooldown rounds without recovery')
    parser.add_argument('--refresh-days',type=int,default=0,help='0 = never repeat successful jobs')
    parser.add_argument('--import-csv',action='append',default=[],help='Import public profile leads, optional multiple')
    parser.add_argument('--plan',action='store_true')
    parser.add_argument('--export-only',action='store_true')
    args=parser.parse_args()
    args.sources={s.strip().lower() for s in args.sources.split(',') if s.strip()}
    if not args.sources <= {'github','gitlab','web'}:parser.error('Unknown --sources; allowed: github,gitlab,web')
    if not (1<=args.workers<=12):parser.error('--workers must be between 1 and 12')
    if not (1<=args.azure_workers<=12):parser.error('--azure-workers must be between 1 and 12')
    if not (1<=args.azure_start_workers<=args.azure_workers):
        parser.error('--azure-start-workers must be 1..--azure-workers')
    if args.azure_tpm_cooldown<0 or args.azure_max_cooldowns<1:
        parser.error('Invalid Azure cooldown settings')
    if args.export_every<0:parser.error('--export-every must be nonnegative')
    if args.max_cycles<1 or args.total_azure_calls<1 or args.cooldown_seconds<0:
        parser.error('Invalid auto cycle/budget parameters')
    if args.auto_continue and (args.export_only or args.plan or 'web' not in args.sources):
        parser.error('--auto-continue needs web source and cannot be combined with --plan or --export-only')
    if not(0<=args.pause_min<=args.pause_max):parser.error('Invalid pause range')
    if not(0<=args.azure_pause_min<=args.azure_pause_max):parser.error('Invalid Azure pause range')
    if any(v<0 for v in (args.github_queries,args.gitlab_terms,args.web_queries,args.max_azure_calls,args.refresh_days,args.max_profiles,args.repo_search_terms,args.max_searched_repos,args.web_profile_validation)):
        parser.error('Limits must be nonnegative')
    if not (1<=args.github_pages<=10 and 1<=args.gitlab_pages<=10 and 1<=args.contributor_pages<=10):
        parser.error('Page counts must be 1..10')
    if args.plan:
        print(json.dumps({'sources':sorted(args.sources), 'github queries':len(gh_user_queries()),
                'GitHub seed projects':len(SEEDS),'GitLab terms':len(TECH_TERMS),
                'web queries prepared':len(make_web_queries()), 'web queries requested':args.web_queries,
                'Azure call cap':args.max_azure_calls,'max workers':args.workers,
                'Azure parallel workers':args.azure_workers,'export every profile writes':args.export_every,
                'automatic cycles':args.auto_continue,'overall Azure budget':args.total_azure_calls},indent=2))
        return
    state=Path(args.state or Path(args.out).with_suffix('.sqlite3'))
    state.parent.mkdir(parents=True,exist_ok=True)
    store=Store(state)
    profiles,completed,failed=store.stats()
    print(f'[resume] SQLite={state} | profiles={profiles}, completed jobs={completed}, '
          f'failed/retryable job records={failed}. Successful work is not repeated unless --refresh-days is set.',flush=True)
    store.configure_checkpoints(args.export_every,lambda:export(store,args))
    try:
        for path in args.import_csv:import_public_leads(store,path)
        if not args.export_only:
            api=HttpClient(args)
            gh=discover_github(api,store,args)
            if gh:process_profiles(api,store,gh,enrich_github,'github',args)
            gl=discover_gitlab(api,store,args)
            if gl:process_profiles(api,store,gl,enrich_gitlab,'gitlab',args)
            if args.auto_continue:
                spent=0
                for cycle in range(1,args.max_cycles+1):
                    allowance=min(args.max_azure_calls,args.total_azure_calls-spent)
                    if allowance<=0:
                        print('[auto stop] Overall Azure call budget reached.',flush=True)
                        break
                    print(f'[auto cycle {cycle}/{args.max_cycles}] per-cycle cap={allowance}; '
                          f'overall submitted={spent}/{args.total_azure_calls}; '
                          f'pending before cycle={azure_pending(store,args)}',flush=True)
                    result=run_azure_web(store,args,call_cap=allowance)
                    spent+=result['submitted']
                    if result['saved']:
                        print('[auto checkpoint] Exporting new profiles for this cycle...',flush=True)
                        export(store,args)
                    pending=azure_pending(store,args)
                    print(f'[auto cycle complete] submitted={result["submitted"]}, '
                          f'new/updated profiles={result["saved"]}, pending={pending}, '
                          f'overall calls={spent}/{args.total_azure_calls}',flush=True)
                    if result['fatal']:
                        print('[auto stop] Azure rate/auth/quota error: do not start another batch.',flush=True)
                        break
                    if not result['submitted']:
                        print('[auto stop] No Azure requests were submitted.',flush=True)
                        break
                    if pending==0:
                        print('[auto done] No eligible web queries remain within selected pool.',flush=True)
                        break
                    if spent>=args.total_azure_calls:
                        print('[auto stop] Overall Azure call budget reached.',flush=True)
                        break
                    if cycle<args.max_cycles:
                        delay=max(args.cooldown_seconds,
                                  args.azure_tpm_cooldown if result.get('rate_limited') else 0)
                        if delay:
                            print(f'[auto pause] {delay:.0f}s before next cycle',flush=True)
                            time.sleep(delay)
                print(f'[auto finished] Azure model calls submitted this invocation={spent}',flush=True)
            else:
                run_azure_web(store,args)
            # Web-only means no GitHub/GitLab API checks, including profile validation.
            if 'github' in args.sources or 'gitlab' in args.sources:
                validate_web_code_profiles(api,store,args)
    except KeyboardInterrupt:
        print('\n[interrupted] Collection interrupted; committed SQLite progress is safe.',flush=True)
    finally:
        try:
            print('[final export] Generating XLSX/CSV from committed SQLite...',flush=True)
            export(store,args)
        finally:
            store.close()


if __name__=='__main__':main()
