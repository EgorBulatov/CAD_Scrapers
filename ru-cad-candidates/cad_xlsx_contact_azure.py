#!/usr/bin/env python3
"""Azure OpenAI web_search enrichment of public contact info in CAD candidates XLSX.

Requirements: Python 3.10+, pip install openai. Uses existing AZURE_OPENAI_* vars.
Preserves original Excel formatting/hyperlinks with targeted OOXML cell patches.
No website scraping, Google Sheets, Playwright or external email guessing.
Conservative replacement requires public, name-specific evidence from Azure search.
"""

from __future__ import annotations

import argparse
import csv
from collections import Counter, defaultdict
from concurrent.futures import ThreadPoolExecutor, as_completed
from html import unescape
from html.parser import HTMLParser
import ipaddress
from pathlib import Path
import posixpath
import random
import re
import socket
import threading
import time
from urllib.parse import urljoin, urlparse, unquote
from xml.etree import ElementTree as ET
from zipfile import ZipFile, ZIP_DEFLATED


MAIN = 'http://schemas.openxmlformats.org/spreadsheetml/2006/main'
REL = 'http://schemas.openxmlformats.org/officeDocument/2006/relationships'
PKG = 'http://schemas.openxmlformats.org/package/2006/relationships'
NS = {'m': MAIN, 'r': REL, 'p': PKG}
ET.register_namespace('', MAIN)
ET.register_namespace('r', REL)
ET.register_namespace('mc', 'http://schemas.openxmlformats.org/markup-compatibility/2006')

EMAIL = re.compile(r'(?<![\w.+-])([\w.+-]+@[\w.-]+\.[a-z]{2,})(?![\w.-])', re.I)
WEB = re.compile(r'^https?://', re.I)
EXCLUDE_HOSTS = ('linkedin.com', 'github.com', 'gitlab.com', 't.me',
                 'telegram.me', 'facebook.com', 'vk.com', 'twitter.com',
                 'x.com', 'instagram.com', 'youtube.com', 'mailto:')
BAD_LOCAL = ('noreply', 'no-reply', 'donotreply', 'admin', 'support', 'info',
             'sales', 'office', 'contact', 'webmaster', 'privacy', 'press',
             'helpdesk', 'postmaster', 'newsletter', 'service', 'robot',
             'dean', 'dekan', 'rector', 'rektor', 'sekretariat', 'reception',
             'admission', 'admissions', 'kafedra', 'department', 'faculty',
             'hr', 'jobs', 'career', 'sed', 'cpk')
BAD_DOMAIN = ('example.com', 'example.org', 'domain.com', 'wixpress.com',
              'sentry.io', 'localhost')
CONTACT_HINTS = ('contact', 'about', 'team', 'staff', 'personnel', 'people',
                 'связ', 'контакт', 'команда', 'сотрудник', 'people', 'members')
CYR = dict(zip('абвгдежзийклмнопрстуфхцчшщъыьэюя',
               ['a','b','v','g','d','e','zh','z','i','y','k','l','m','n','o','p','r',
                's','t','u','f','kh','ts','ch','sh','shch','','y','','e','yu','ya']))


def translit(s):
    return ''.join(CYR.get(c, c) for c in s.lower().replace('ё', 'е'))


def name_parts(name):
    clean = re.sub(r'[^a-zа-яё\s-]', ' ', name.lower())
    words = [translit(w) for w in re.findall(r'[a-zа-яё]+', clean)]
    return [w for w in words if len(w) >= 4 and w not in ('unknown', 'user', 'admin')]


def good_email(email):
    email = unquote(unescape(email)).strip().lower().strip('.,;:<>[]()"\'')
    m = EMAIL.fullmatch(email)
    if not m or len(email) > 254:
        return ''
    local, domain = email.split('@', 1)
    if local.startswith(BAD_LOCAL) or domain in BAD_DOMAIN or domain.endswith('.png'):
        return ''
    if len(local) < 2 or '..' in email or domain.endswith(('.svg', '.jpg', '.jpeg', '.webp')):
        return ''
    return email


def safe_url(url):
    try:
        p = urlparse(url.strip())
        if p.scheme.lower() not in ('http', 'https') or not p.hostname or p.username or p.password:
            return ''
        host = p.hostname.lower()
        if host in ('localhost',) or host.endswith(('.local', '.internal')):
            return ''
        ip = None
        try:
            ip = ipaddress.ip_address(host)
        except ValueError:
            pass
        if ip and not ip.is_global:
            return ''
        return url
    except ValueError:
        return ''




def identity_tokens(name):
    """Return surnames / unique handles, NEVER first names or patronymics.

    For a 3-part Russian name, use the patronymic to detect whether surname
    comes first (Ivanov Ivan Ivanovich) or last (Ivan Ivanovich Ivanov).
    English names and short display names use their final component.
    """
    words = name_parts(name)
    if not words:
        return []
    if len(words) == 1:
        return words if len(words[0]) >= 5 else []
    parts = re.findall(r'[a-zа-яё]+', str(name).lower())
    if len(parts) >= 3:
        endings = ('ovich', 'evich', 'ovna', 'evna', 'ichna', 'ich',
                   'ович', 'евич', 'овна', 'евна', 'ична', 'инична')
        if translit(parts[-1]).endswith(endings) or parts[-1].endswith(endings):
            # Surname, first name, patronymic
            result = translit(parts[0])
        else:
            # First name, patronymic, surname (or Latin first/middle/last)
            result = translit(parts[-1])
    else:
        result = words[-1]
    return [result] if len(result) >= 5 else []




def xlsx_text(cell, shared):
    typ = cell.get('t')
    if typ == 's':
        v = cell.find(f'{{{MAIN}}}v')
        try:
            return shared[int(v.text)] if v is not None else ''
        except (ValueError, IndexError, TypeError):
            return ''
    if typ in ('inlineStr', 'str'):
        return ''.join(el.text or '' for el in cell.findall(f'.//{{{MAIN}}}t'))
    v = cell.find(f'{{{MAIN}}}v')
    return (v.text or '') if v is not None else ''


def write_cell(cell, email):
    # Convert shared-string/formula/inline text to self-contained inline string,
    # leaving style, protection and all other cell attributes untouched.
    for child in list(cell):
        if child.tag in (f'{{{MAIN}}}v', f'{{{MAIN}}}is', f'{{{MAIN}}}f'):
            cell.remove(child)
    cell.set('t', 'inlineStr')
    is_node = ET.SubElement(cell, f'{{{MAIN}}}is')
    ET.SubElement(is_node, f'{{{MAIN}}}t').text = email


def rels_path(sheet_path):
    directory, basename = posixpath.split(sheet_path)
    return posixpath.join(directory, '_rels', basename + '.rels')


def load_workbook_metadata(z):
    wb = ET.fromstring(z.read('xl/workbook.xml'))
    wb_rels = ET.fromstring(z.read('xl/_rels/workbook.xml.rels'))
    paths = {}
    for rel in wb_rels:
        target = rel.attrib.get('Target', '')
        path = target.lstrip('/') if target.startswith('/') else posixpath.normpath(posixpath.join('xl', target))
        paths[rel.attrib.get('Id')] = path
    sheets = [(s.get('name'), paths.get(s.get(f'{{{REL}}}id')))
              for s in wb.findall('m:sheets/m:sheet', NS)]
    shared = []
    if 'xl/sharedStrings.xml' in z.namelist():
        root = ET.fromstring(z.read('xl/sharedStrings.xml'))
        for si in root.findall('m:si', NS):
            shared.append(''.join(t.text or '' for t in si.findall('.//m:t', NS)))
    return sheets, shared


def is_website(value):
    if not WEB.match(value.strip()):
        return False
    p = urlparse(value.strip())
    if not safe_url(value):
        return False
    host = (p.hostname or '').lower()
    return not any(host == h or host.endswith('.' + h) for h in EXCLUDE_HOSTS)


def collect_jobs(z):
    worksheets, shared = load_workbook_metadata(z)
    jobs = []
    metadata = {}
    for sheet_name, path in worksheets:
        if not path or path not in z.namelist():
            continue
        root = ET.fromstring(z.read(path))
        rpath = rels_path(path)
        rel_root = ET.fromstring(z.read(rpath)) if rpath in z.namelist() else None
        rel_target = {x.get('Id'): x.get('Target', '') for x in rel_root} if rel_root is not None else {}
        hlinks = root.find('m:hyperlinks', NS)
        hmap = {x.get('ref'): x for x in hlinks} if hlinks is not None else {}
        rows = root.findall('m:sheetData/m:row', NS)
        if not rows:
            continue
        header_cells = {re.match(r'^[A-Z]+', c.get('r', '')).group(): xlsx_text(c, shared).strip().lower()
                        for c in rows[0].findall('m:c', NS) if re.match(r'^[A-Z]+', c.get('r', ''))}
        ccols = [col for col, title in header_cells.items()
                 if title in ('email / linkedin', 'email/ linkedin', 'email / website',
                              'email / contact', 'contact', 'contact info', 'contact information',
                              'email', 'email / linkedin / website')]
        ncols = [col for col, title in header_cells.items()
                 if title in ('username / name', 'name', 'candidate', 'candidate name', 'username / fullname')]
        if not ccols or not ncols:
            continue
        name_col = ncols[0]
        for row in rows[1:]:
            cells = {re.match(r'^[A-Z]+', c.get('r', '')).group(): c
                     for c in row.findall('m:c', NS) if re.match(r'^[A-Z]+', c.get('r', ''))}
            name_cell = cells.get(name_col)
            if name_cell is None:
                continue
            name = xlsx_text(name_cell, shared)
            for col in ccols:
                cell = cells.get(col)
                if cell is None:
                    continue
                addr = cell.get('r', '')
                value = xlsx_text(cell, shared).strip()
                hnode = hmap.get(addr)
                htarget = rel_target.get(hnode.get(f'{{{REL}}}id'), '') if hnode is not None else ''
                url = value if is_website(value) else (htarget if is_website(htarget) else '')
                if url:
                    jobs.append({'sheet': sheet_name, 'path': path, 'cell': addr,
                                 'name': name, 'old': value, 'url': url})
        metadata[path] = (root, rel_root, rpath, hmap)
    return jobs, metadata


def save_patched(input_path, output_path, metadata, changes):
    by_sheet = defaultdict(dict)
    for entry in changes:
        by_sheet[entry['path']][entry['cell']] = entry['email']
    updates = {}
    for path, emails in by_sheet.items():
        root, rel_root, rpath, hmap = metadata[path]
        cells = {c.get('r'): c for c in root.findall('.//m:sheetData/m:row/m:c', NS)}
        targets = {r.get('Id'): r for r in rel_root} if rel_root is not None else {}
        used = Counter(node.get(f'{{{REL}}}id') for node in hmap.values())
        for addr, email in emails.items():
            write_cell(cells[addr], email)
            link = hmap.get(addr)
            if link is not None and rel_root is not None:
                rid = link.get(f'{{{REL}}}id')
                if rid and rid in targets:
                    if used[rid] == 1:
                        targets[rid].set('Target', 'mailto:' + email)
                    else:
                        # Relationship used by other cells: create a dedicated mailto ID.
                        new_id = 'rIdEmail' + str(len(targets) + 1)
                        while new_id in targets:
                            new_id += 'x'
                        new_rel = ET.SubElement(rel_root, f'{{{PKG}}}Relationship',
                            {'Id': new_id, 'Type': REL + '/hyperlink',
                             'Target': 'mailto:' + email, 'TargetMode': 'External'})
                        targets[new_id] = new_rel
                        link.set(f'{{{REL}}}id', new_id)
            elif link is not None and link.get('location'):
                # Old internal navigation should not remain on an email address.
                link.attrib.pop('location', None)
        updates[path] = ET.tostring(root, encoding='utf-8', xml_declaration=True)
        if rel_root is not None:
            updates[rpath] = ET.tostring(rel_root, encoding='utf-8', xml_declaration=True)
    tmp = output_path.with_suffix('.tmp.xlsx')
    with ZipFile(input_path) as src, ZipFile(tmp, 'w') as dst:
        for item in src.infolist():
            dst.writestr(item, updates.get(item.filename, src.read(item.filename)))
    with ZipFile(tmp) as chk:
        bad = chk.testzip()
        if bad:
            raise ValueError('Damaged Excel output: ' + bad)
        for part in updates:
            ET.fromstring(chk.read(part))
    tmp.replace(output_path)




# ---- Azure-backed, evidence-checked enrichment ----
import concurrent.futures
import hashlib
import json
import os
import sqlite3
import sys
from datetime import datetime, timezone
from email.utils import parsedate_to_datetime

AUDIT_COLUMNS = ['sheet', 'cell', 'name', 'url', 'old', 'email', 'source',
                 'status', 'reason', 'evidence_text', 'api_calls', 'updated_utc']


def utc_now():
    return datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def key_of(job):
    return hashlib.sha256((job['name'].strip().casefold() + '\n' +
                           job['url'].strip().lower()).encode('utf-8')).hexdigest()


def normalize_url(url):
    try:
        p = urlparse(url)
        host = (p.hostname or '').lower().removeprefix('www.')
        if not host or p.scheme not in ('http', 'https'):
            return None
        return host, unquote(p.path).rstrip('/').casefold()
    except (ValueError, TypeError):
        return None


def source_is_supported(url, sources):
    """Require a page explicitly returned by Azure web_search (not a fabricated URL)."""
    target = normalize_url(url)
    if not target:
        return False
    host, path = target
    for src in sources:
        normalized = normalize_url(src)
        if not normalized:
            continue
        shost, spath = normalized
        # Exact URL, http/https or www variations; strip tracking query/fragment.
        if host == shost and path == spath:
            return True
    return False


def parse_json(text):
    s = (text or '').strip()
    s = re.sub(r'^```(?:json)?\s*|\s*```$', '', s, flags=re.I).strip()
    try:
        data = json.loads(s)
    except ValueError:
        pos = s.find('{')
        if pos < 0:
            raise ValueError('Azure did not return JSON')
        data, _ = json.JSONDecoder().raw_decode(s[pos:])
    if not isinstance(data, dict):
        raise ValueError('Azure JSON must be an object')
    return data


def output_sources(response):
    sources = set()
    used_search = False
    for item in (getattr(response, 'output', None) or []):
        data = item.model_dump() if hasattr(item, 'model_dump') else (
            item if isinstance(item, dict) else {})
        if data.get('type') != 'web_search_call':
            continue
        used_search = True
        action = data.get('action') or {}
        for src in action.get('sources') or []:
            uri = src.get('url') if isinstance(src, dict) else None
            if isinstance(uri, str) and safe_url(uri):
                sources.add(uri)
    return sources, used_search


def email_proof_is_specific(name, email, proof):
    """Require the exact email and candidate surname/handle in a short quoted passage."""
    if not email or not proof or len(proof) > 500:
        return False
    # Allow spaces around the @ only when text otherwise matches.
    compact = re.sub(r'\s+', '', unescape(str(proof)).casefold())
    if email.casefold() not in compact:
        return False
    txt = re.sub(r'[^a-z0-9]', '', translit(str(proof).casefold()))
    return any(token in txt for token in identity_tokens(name))


def surname_in_email(name, email):
    local = re.sub(r'[^a-z0-9]', '', translit(email.split('@', 1)[0]))
    return any(token in local for token in identity_tokens(name))


def candidate_prompt(job):
    return f'''Find a PUBLICLY POSTED professional email that belongs to EXACTLY this person, not a coworker or department.
Candidate full name: {job['name']}
Candidate contact/profile website: {job['url']}

MANDATORY: Perform web search for this specific person's website, name, and published email.
Read the person's entry on the linked website or directly associated public professional page.
Do NOT infer an address from domain, username or likely patterns. Do NOT cite unrelated people on staff/personnel pages.
Do NOT return an academic department's, secretariat's, admissions', lab's, or a generic shared inbox.
The email must be explicitly attributed to this individual in the SAME person-specific entry, bio, or contact block.
If there are several names/emails on a page, be extremely careful to match the correct row/card.
If uncertain or the page is not indexed/readable, report no email. No guesses.

Return ONLY a JSON object with keys:
{{"email":"", "source_url":"", "evidence_text":"", "is_direct_personal_contact":false, "confidence":"low|medium|high", "reason":""}}
- source_url must be the exact publicly searched page with evidence, not invented.
- evidence_text must be a SINGLE short verbatim excerpt (maximum 250 characters) that shows BOTH the candidate's surname/name and the exact email together.
- is_direct_personal_contact=true ONLY if the address is explicitly tied to this individual.
- If this exact evidence is not found, email/source_url/evidence_text MUST be empty.'''


def verification_prompt(job, proposed):
    return f'''Independently verify a suspected PERSONAL professional email using PUBLIC WEB SEARCH. Search web; do not rely only on supplied assertions.
Person: {job['name']}
Original profile/website: {job['url']}
Suspected address: {proposed['email']}
Alleged evidence page: {proposed['source']}

Does a public, person-specific biography/contact entry explicitly associate THIS precise person (not a colleague with a similar name) with THIS exact email?
Do not accept broad department email, an email belonging to a different person, generic office addresses, or mere co-occurrence elsewhere on a multi-person staff list.
If uncertain, answer false. Return ONLY:
{{"verified":false,"email":"","source_url":"","evidence_text":"","reason":""}}
When truly verified, set verified=true, email to the same suspected email, source_url to the directly confirming searched page, evidence_text to ONE short verbatim contiguous excerpt (max 250 chars) containing both the person's surname/name and the precise email.'''


class Budget:
    """Thread-safe actual HTTP submission budget, including attempts and verification."""
    def __init__(self, cap, min_pause, max_pause):
        self.cap = cap
        self.used = 0
        self.lock = threading.Lock()
        self.next_at = 0.0
        self.min_pause = min_pause
        self.max_pause = max_pause

    def reserve(self):
        with self.lock:
            if self.used >= self.cap:
                return False
            self.used += 1
            target = max(time.monotonic(), self.next_at)
            self.next_at = target + random.uniform(self.min_pause, self.max_pause)
        wait = target - time.monotonic()
        if wait > 0:
            time.sleep(wait)
        return True


class AzureVerifier:
    def __init__(self, client, deployment, budget, retries=2):
        self.client = client
        self.deployment = deployment
        self.budget = budget
        self.retries = retries
        self.local = threading.local()

    def search(self, prompt):
        """At most two retries for transient Azure errors; every call counts."""
        for attempt in range(self.retries + 1):
            if not self.budget.reserve():
                return None, 'budget_exhausted'
            self.local.calls = getattr(self.local, 'calls', 0) + 1
            try:
                response = self.client.responses.create(
                    model=self.deployment,
                    tools=[{'type': 'web_search'}],
                    include=['web_search_call.action.sources'],
                    input=prompt)
                sources, used_search = output_sources(response)
                if not used_search:
                    return None, 'no_web_search'
                return (parse_json(getattr(response, 'output_text', '')), sources), 'ok'
            except Exception as exc:
                status = getattr(exc, 'status_code', None)
                message = str(exc).lower()
                is_transient = status in (429, 500, 502, 503, 504) or any(
                    term in message for term in ('rate limit', 'timeout', 'timed out', 'connection error'))
                if not is_transient:
                    return None, 'api_error: ' + str(exc)[:180]
                if attempt >= self.retries:
                    return None, 'throttled: ' + str(exc)[:180]
                after = 0.0
                headers = getattr(getattr(exc, 'response', None), 'headers', {}) or {}
                try:
                    value = headers.get('retry-after')
                    if value:
                        try:
                            after = float(value)
                        except ValueError:
                            after = (parsedate_to_datetime(value) - datetime.now(timezone.utc)).total_seconds()
                except (ValueError, TypeError):
                    pass
                wait = max(15, after, (2 ** attempt) * 15) + random.uniform(0, 3)
                print(f'  [azure-rate] cooldown {wait:.0f}s after transient API error', flush=True)
                time.sleep(min(180, wait))
        return None, 'api_failed'

    def find_email(self, job):
        self.local.calls = 0
        result, status = self.search(candidate_prompt(job))
        if result is None:
            return dict(status=status, email='', source='', reason=status,
                        api_calls=self.local.calls)
        data, sources = result
        email = good_email(str(data.get('email') or ''))
        url = str(data.get('source_url') or '').strip()
        proof = str(data.get('evidence_text') or '').strip()
        if not email:
            return dict(status='not_found', email='', source='', reason=str(data.get('reason') or '')[:240],
                        api_calls=self.local.calls)
        if str(data.get('confidence') or '').lower() != 'high' or data.get('is_direct_personal_contact') is not True:
            return dict(status='needs_review', email='', source=url, reason='AI not high confidence / not direct personal contact',
                        api_calls=self.local.calls)
        if not source_is_supported(url, sources):
            return dict(status='needs_review', email='', source=url, reason='Evidence URL absent from actual web-search sources',
                        api_calls=self.local.calls)
        if not email_proof_is_specific(job['name'], email, proof):
            return dict(status='needs_review', email='', source=url, reason='No short name + email evidence in same excerpt',
                        api_calls=self.local.calls)
        if surname_in_email(job['name'], email):
            return dict(status='replaced', email=email, source=url, evidence_text=proof,
                        reason='Personal email and surname match; excerpt and source checked',
                        api_calls=self.local.calls)
        # For nonmatching addresses, spend an independent second Azure grounded search.
        second, second_status = self.search(verification_prompt(job, {'email': email, 'source': url}))
        if second is None:
            return dict(status=('budget_exhausted' if second_status == 'budget_exhausted' else 'needs_review'), email='', source=url,
                        reason='Second verification unavailable (' + second_status + ')',
                        api_calls=self.local.calls)
        verify, check_sources = second
        same_email = str(verify.get('email') or '').strip().lower() == email
        specific = email_proof_is_specific(job['name'], email, str(verify.get('evidence_text') or ''))
        supported = source_is_supported(str(verify.get('source_url') or ''), check_sources)
        if verify.get('verified') is True and same_email and specific and supported:
            return dict(status='replaced', email=email, evidence_text=str(verify.get('evidence_text') or ''),
                        source=str(verify.get('source_url') or ''),
                        reason='Independently cross-checked name + nonmatching email',
                        api_calls=self.local.calls)
        return dict(status='needs_review', email='', source=url,
                    reason='Second independent web search could not confirm this person owns the address',
                    api_calls=self.local.calls)


def init_cache(path):
    db = sqlite3.connect(path)
    db.execute('PRAGMA journal_mode=WAL')
    db.execute('''CREATE TABLE IF NOT EXISTS verified_contacts (
      key TEXT PRIMARY KEY, name TEXT, url TEXT, email TEXT, source TEXT,
      status TEXT, reason TEXT, evidence_text TEXT, api_calls INTEGER, updated_utc TEXT)''')
    # Migrate existing caches created by older revisions.
    columns = {r[1] for r in db.execute('PRAGMA table_info(verified_contacts)')}
    if 'evidence_text' not in columns:
        db.execute('ALTER TABLE verified_contacts ADD COLUMN evidence_text TEXT')
    db.commit()
    return db


def cached(db, job):
    row = db.execute('SELECT email,source,status,reason,evidence_text,api_calls,updated_utc FROM verified_contacts WHERE key=?',
                     (key_of(job),)).fetchone()
    if not row:
        return None
    return dict(zip(['email','source','status','reason','evidence_text','api_calls','updated_utc'], row))


def store(db, job, result):
    db.execute('''INSERT INTO verified_contacts
      (key,name,url,email,source,status,reason,evidence_text,api_calls,updated_utc)
      VALUES (?,?,?,?,?,?,?,?,?,?)
      ON CONFLICT(key) DO UPDATE SET email=excluded.email,source=excluded.source,
      status=excluded.status, reason=excluded.reason, evidence_text=excluded.evidence_text, api_calls=excluded.api_calls,
      updated_utc=excluded.updated_utc''',
      (key_of(job),job['name'],job['url'],result.get('email',''),result.get('source',''),
       result.get('status',''),result.get('reason',''),result.get('evidence_text',''),int(result.get('api_calls') or 0),utc_now()))
    db.commit()


def save_current(inp, out, metadata, jobs, cache):
    audit = []
    changes = []
    for job in jobs:
        found = cached(cache, job)
        result = found if found is not None else dict(status='not_run',email='',source='',reason='',api_calls=0)
        row = dict(job)
        row.update(result)
        audit.append(row)
        if row['status'] == 'replaced' and good_email(row['email']):
            changes.append(row)
    save_patched(inp, out, metadata, changes)
    audit_path = out.with_name(out.stem + '_audit.csv')
    with audit_path.open('w', encoding='utf-8-sig', newline='') as fh:
        w = csv.DictWriter(fh, fieldnames=AUDIT_COLUMNS, extrasaction='ignore')
        w.writeheader()
        for row in audit:
            w.writerow(row)
    return len(changes), audit_path


def main():
    parser = argparse.ArgumentParser(description='Azure web-search verification of email contacts in XLSX (no GSheets API)')
    parser.add_argument('--input', required=True)
    parser.add_argument('--out', default='', help='Separate XLSX output path')
    parser.add_argument('--state', default='', help='SQLite cache path; can resume without repeated Azure calls')
    parser.add_argument('--workers', type=int, default=3, help='Number of parallel Azure calls (default 3)')
    parser.add_argument('--limit', type=int, default=0, help='Process first N unique candidates, 0=all')
    parser.add_argument('--max-api-calls', type=int, default=100, help='Hard per-run API request cap including retries/second checks')
    parser.add_argument('--pause-min', type=float, default=2.0, help='Min seconds between Azure submissions')
    parser.add_argument('--pause-max', type=float, default=5.0)
    parser.add_argument('--checkpoint-every', type=int, default=25, help='Export XLSX + audit after N finished candidates')
    parser.add_argument('--refresh', action='store_true', help='Search again even for already cached candidates')
    args = parser.parse_args()
    inp = Path(args.input)
    out = Path(args.out) if args.out else inp.with_name(inp.stem+'_azure_emails.xlsx')
    state = Path(args.state) if args.state else inp.with_name(inp.stem+'_azure_email_cache.sqlite3')
    if not inp.is_file():
        parser.error('Input does not exist: '+str(inp))
    if inp.resolve() == out.resolve():
        parser.error('--out must differ from --input')
    if args.workers < 1 or args.max_api_calls < 1 or args.limit < 0 or args.checkpoint_every < 1 or args.pause_min < 0 or args.pause_max < args.pause_min:
        parser.error('Invalid numeric arguments')
    endpoint = os.getenv('AZURE_OPENAI_ENDPOINT','').strip()
    key = os.getenv('AZURE_OPENAI_API_KEY','').strip()
    deployment = os.getenv('AZURE_OPENAI_DEPLOYMENT','').strip()
    if not all((endpoint,key,deployment)):
        parser.error('Set AZURE_OPENAI_ENDPOINT, AZURE_OPENAI_API_KEY and AZURE_OPENAI_DEPLOYMENT')
    try:
        from openai import OpenAI
    except ImportError:
        parser.error('Install dependency: python -m pip install -U openai')
    endpoint = endpoint.rstrip('/')
    if not endpoint.endswith('/openai/v1'):
        endpoint += '/openai/v1'
    client = OpenAI(base_url=endpoint+'/', api_key=key, timeout=180, max_retries=0)
    verifier = AzureVerifier(client, deployment, Budget(args.max_api_calls,args.pause_min,args.pause_max))
    with ZipFile(inp) as src:
        jobs, metadata = collect_jobs(src)
    # Dedupe identical person+URL across different candidate tabs.
    unique = {}
    for j in jobs:
        unique.setdefault(key_of(j), j)
    print(f'[scan] {len(jobs)} URL cells / {len(unique)} unique candidate-website combinations; {len(metadata)} sheets',flush=True)
    if args.limit:
        unique = dict(list(unique.items())[:args.limit])
    db = init_cache(state)
    try:
        to_run = [job for job in unique.values() if args.refresh or cached(db,job) is None or
                  str((cached(db,job) or {}).get('status','')).startswith(('api_error','throttled','budget_exhausted','no_web_search','error'))]
        print(f'[azure] queued {len(to_run)} unique searches; per-run cap {args.max_api_calls} requests, workers={args.workers}',flush=True)
        completed = 0
        with concurrent.futures.ThreadPoolExecutor(max_workers=args.workers) as pool:
            futures = {pool.submit(verifier.find_email,job):job for job in to_run}
            for f in concurrent.futures.as_completed(futures):
                job = futures[f]
                try:
                    result = f.result()
                except Exception as exc:
                    result = dict(status='error',email='',source='',reason=str(exc)[:240],api_calls=0)
                # No budget run should not permanently cache unstarted candidates.
                if result['status'] != 'budget_exhausted':
                    store(db,job,result)
                completed += 1
                print(f'[{completed}/{len(to_run)}] {job["sheet"]}!{job["cell"]} '
                      f'{job["name"][:38]}: {result["status"]}' +
                      (f' => {result["email"]}' if result.get('email') else ''),flush=True)
                if completed % args.checkpoint_every == 0:
                    count, audit_path = save_current(inp,out,metadata,jobs,db)
                    print(f'[checkpoint] replacements={count}; excel={out}; calls={verifier.budget.used}/{verifier.budget.cap}',flush=True)
        count,audit_path = save_current(inp,out,metadata,jobs,db)
        print(f'[done] replaced={count}/{len(jobs)}, API requests={verifier.budget.used}/{verifier.budget.cap}, '
              f'output={out}, audit={audit_path}, cache={state}',flush=True)
    except KeyboardInterrupt:
        count,audit_path = save_current(inp,out,metadata,jobs,db)
        print(f'\n[stopped] checkpoint saved. Replacements={count}, output={out}',flush=True)
        raise SystemExit(130)
    finally:
        db.close()


if __name__ == '__main__':
    main()