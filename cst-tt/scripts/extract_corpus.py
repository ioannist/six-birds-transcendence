#!/usr/bin/env python3
"""Extract a complete theorem-like statement index from the 60-paper SBT archive.

This script is a provenance aid, not a TeX parser or proof checker. It records
source line spans and preserves compact source text for human audit.
"""
from __future__ import annotations
from pathlib import Path
import argparse, re, csv, json, hashlib, unicodedata, difflib

ENVNAMES = [
    'definition','theorem','proposition','lemma','corollary','postulate',
    'construction','principle','schema','nonclaim','limitationbox','remark',
    'example','convention','theorem*','Theorem','Lemma','Definition','Corollary','Remark'
]
KEYWORDS = {
 'carrier':['carrier','support','substrate','medium','implementation'],
 'transport':['transport','bridge','map','morphism','route','push','pullback','transfer','descent','lift'],
 'predictive':['predictive','continuation','future-sufficient','quotient','reachable image','memory'],
 'identity':['identity','lineage','persistence','continuity','fission','fusion','branch'],
 'recombination':['recombination','marking','erasure','interference','joint continuation'],
 'promotion':['promotion','strict extension','new-layer','exactification','surviving package'],
 'admissibility':['admissib','event package','global package','glue','aor'],
 'autonomy':['autonom','endogenous','maintenance','repair','self-maintain'],
 'viability':['viability','kernel','safe','currency','shadow price','constraint'],
 'hiddenness':['hidden','non-exposure','no-overread','blind spot','counterfeit','shadow'],
 'holonomy':['holonomy','route dependence','confluence','critical pair','loop'],
 'temporal':['time','temporal','clock','order','arrow','history'],
 'consciousness':['conscious','self-coordinate','binding','quality','valence','introspection','action credit'],
 'audit':['audit','certificate','residual','defect','status','control','falsif'],
 'finite':['finite','exact','enumerat','machine-check','lean'],
 'record':['record','interface','lens','observable','public'],
}

def balanced_arg(text: str, start: int):
    assert text[start] == '{'
    depth = 0
    for i in range(start, len(text)):
        c = text[i]
        if c == '{' and (i == 0 or text[i-1] != '\\'):
            depth += 1
        elif c == '}' and (i == 0 or text[i-1] != '\\'):
            depth -= 1
            if depth == 0:
                return text[start+1:i], i+1
    return '', start

def command_arg(text: str, cmd: str) -> str:
    m = re.search(r'\\' + re.escape(cmd) + r'\s*\{', text)
    if not m:
        return ''
    arg, _ = balanced_arg(text, m.end()-1)
    return arg

def clean_tex(s: str) -> str:
    s = re.sub(r'(?m)%.*$', '', s)
    s = s.replace('\\\\', ' — ')
    replacements = {
      r'\emph':'',r'\textbf':'',r'\textit':'',r'\textrm':'',r'\textsf':'',r'\mathrm':'',r'\operatorname':'',
      '~':' ', r'\,':' ', r'\;':' ', r'\:':' ', r'\!':'', r'\quad':' ', r'\qquad':' ',
      r'\textemdash':'—', r'\textendash':'–', r'\colon':':', r'\to':'→', r'\mapsto':'↦', r'\iff':'iff',
      r'\leq':'≤',r'\geq':'≥',r'\neq':'≠',r'\emptyset':'∅',r'\times':'×',r'\subseteq':'⊆',r'\in':'∈',
    }
    for a, b in replacements.items():
        s = s.replace(a, b)
    s = re.sub(r'\\begin\{[^}]+\}', ' ', s)
    s = re.sub(r'\\end\{[^}]+\}', ' ', s)
    s = re.sub(r'\\item(?:\[[^]]*\])?', ' • ', s)
    s = re.sub(r'\\(?:citep|citet|cite|url|href)\s*(?:\[[^]]*\])?\s*\{[^}]*\}(?:\{[^}]*\})?', ' ', s)
    for _ in range(6):
        ns = re.sub(r'\\[A-Za-z@]+\*?(?:\[[^]]*\])?\{([^{}]*)\}', r'\1', s)
        if ns == s:
            break
        s = ns
    s = re.sub(r'\\[A-Za-z@]+\*?', ' ', s)
    s = s.replace('{','').replace('}','').replace('$','`')
    s = re.sub(r'\s+', ' ', s).strip()
    return s

def line_of(text: str, pos: int) -> int:
    return text.count('\n', 0, pos) + 1

def extract_envs(text: str):
    out = []
    for env in ENVNAMES:
        start_pat = re.compile(r'\\begin\{' + re.escape(env) + r'\}(?:\[([^]]*)\])?')
        end_s = '\\end{' + env + '}'
        for m in start_pat.finditer(text):
            e = text.find(end_s, m.end())
            if e < 0:
                continue
            end = e + len(end_s)
            body = text[m.end():e]
            labelm = re.search(r'\\label\{([^}]+)\}', body)
            out.append({
                'kind': env,
                'name': clean_tex(m.group(1) or ''),
                'label': labelm.group(1) if labelm else '',
                'line_start': line_of(text, m.start()),
                'line_end': line_of(text, end),
                'raw': body.strip(),
                'compact': clean_tex(body)[:3000],
            })
    # Deduplicate aliases such as theorem/Theorem only if exact same span.
    uniq = {}
    for x in out:
        uniq[(x['line_start'], x['line_end'], x['label'], x['name'])] = x
    return sorted(uniq.values(), key=lambda x: (x['line_start'], x['line_end']))

def extract_sections(text: str):
    out = []
    pat = re.compile(r'\\(section|subsection|subsubsection)\*?\s*\{')
    for m in pat.finditer(text):
        arg, end = balanced_arg(text, m.end()-1)
        tail = text[end:end+180]
        lm = re.search(r'\\label\{([^}]+)\}', tail)
        out.append({'level':m.group(1),'title':clean_tex(arg),'label':lm.group(1) if lm else '', 'line':line_of(text,m.start())})
    return out

def parse_triage(path: Path):
    text = path.read_text(encoding='utf-8')
    heads = list(re.finditer(r'^###\s+(\d{2})\.\s+(.+)$', text, re.M))
    tri = {}
    for i, m in enumerate(heads):
        e = heads[i+1].start() if i+1 < len(heads) else len(text)
        # The final paper card is followed by report-level H2 sections rather
        # than another H3 paper card. Stop there so P60 does not absorb the
        # report's global gaps/recommendations into its boundary field.
        h2 = re.search(r'^##\s+', text[m.end():e], re.M)
        if h2:
            e = m.end() + h2.start()
        block = text[m.end():e]
        vm = re.search(r'\*\*Verdict:\*\*\s*([^\.]+)\.', block)
        um = re.search(r'\*\*Likely useful for the project:\*\*\s*([^\.]+)\.', block)
        wm = re.search(r'\*\*What is useful:\*\*\s*(.*?)(?=\n\n\*\*Boundary/caution:\*\*)', block, re.S)
        bm = re.search(r'\*\*Boundary/caution:\*\*\s*(.*?)(?=\n\n###|\Z)', block, re.S)
        tri[int(m.group(1))] = {
          'triage_title': m.group(2).strip(),
          'verdict': vm.group(1).strip() if vm else '',
          'useful': um.group(1).strip() if um else '',
          'triage_use': re.sub(r'\s+',' ',wm.group(1).strip()) if wm else '',
          'triage_boundary': re.sub(r'\s+',' ',bm.group(1).strip()) if bm else '',
        }
    if len(tri) != 60:
        raise RuntimeError(f'Expected 60 triage cards, found {len(tri)}')
    return tri

def norm_match(s: str) -> str:
    s = unicodedata.normalize('NFKD', s.lower()).encode('ascii','ignore').decode()
    s = re.sub(r'^tsiokos_2026_', '', s)
    s = re.sub(r'\.tex$', '', s)
    s = re.sub(r'[^a-z0-9]+', ' ', s)
    stop = {'a','an','the','of','on','in','for','with','and','to','is'}
    return ' '.join(x for x in s.split() if x not in stop)

def resolve_files(papers_dir: Path, tri: dict):
    files_all = list(papers_dir.glob('*.tex'))
    if len(files_all) != 60:
        raise RuntimeError(f'Expected 60 top-level TeX manuscripts, found {len(files_all)}')
    files, used = [], set()
    for idx in range(1, 61):
        title = tri[idx]['triage_title']
        if idx == 42:
            chosen = next(f for f in files_all if 'The_Usefulness' in f.name)
        elif idx == 60:
            chosen = next(f for f in files_all if 'Why_Mathematics' in f.name)
        else:
            nt = norm_match(title)
            scored = []
            for f in files_all:
                if f in used:
                    continue
                nf = norm_match(f.name)
                seq = difflib.SequenceMatcher(None, nt, nf).ratio()
                a, b = set(nt.split()), set(nf.split())
                jac = len(a & b) / max(1, len(a | b))
                scored.append((0.6*seq + 0.4*jac, f))
            chosen = max(scored, key=lambda x: x[0])[1]
        files.append(chosen); used.add(chosen)
    return files

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--papers-dir', type=Path, required=True)
    ap.add_argument('--triage', type=Path, required=True)
    ap.add_argument('--out-dir', type=Path, required=True)
    args = ap.parse_args()
    args.out_dir.mkdir(parents=True, exist_ok=True)
    tri = parse_triage(args.triage)
    files = resolve_files(args.papers_dir, tri)
    papers, all_statements = [], []
    for idx, f in enumerate(files, 1):
        text = f.read_text(errors='replace')
        title = clean_tex(command_arg(text, 'title'))
        am = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', text, re.S)
        abstract = clean_tex(am.group(1)) if am else ''
        envs = extract_envs(text)
        info = {
          'paper_id':f'P{idx:02d}','index':idx,'filename':f.name,'embedded_title':title,
          'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size,
          'lines':text.count('\n')+1,'abstract':abstract,'sections':extract_sections(text),
          'statement_count':len(envs),**tri[idx]
        }
        papers.append(info)
        for j, s in enumerate(envs, 1):
            hay = (s['name'] + ' ' + s['compact']).lower()
            tags, score = [], 0
            for tag, ks in KEYWORDS.items():
                hits = sum(hay.count(k) for k in ks)
                if hits:
                    tags.append(tag); score += min(hits, 4)
            if s['kind'] in ('theorem','proposition','corollary','definition','postulate','schema','nonclaim'):
                score += 2
            if s['name']:
                score += 1
            all_statements.append({
              'paper_id':f'P{idx:02d}','statement_seq':j,'statement_id':f'P{idx:02d}-S{j:03d}',
              'filename':f.name,'paper_title':title,'kind':s['kind'],'name':s['name'],'label':s['label'],
              'line_start':s['line_start'],'line_end':s['line_end'],'compact':s['compact'],
              'tags':';'.join(tags),'relevance_score':score,'raw':s['raw']
            })
    (args.out_dir/'papers.json').write_text(json.dumps(papers,indent=2,ensure_ascii=False),encoding='utf-8')
    (args.out_dir/'statements.json').write_text(json.dumps(all_statements,indent=2,ensure_ascii=False),encoding='utf-8')
    with (args.out_dir/'paper_inventory.csv').open('w',newline='',encoding='utf-8') as fh:
        fields=['paper_id','index','filename','embedded_title','triage_title','verdict','useful','sha256','bytes','lines','statement_count','abstract']
        w=csv.DictWriter(fh,fieldnames=fields); w.writeheader()
        w.writerows({k:p.get(k,'') for k in fields} for p in papers)
    with (args.out_dir/'all_statement_index.csv').open('w',newline='',encoding='utf-8') as fh:
        fields=['statement_id','paper_id','paper_title','filename','kind','name','label','line_start','line_end','tags','relevance_score','compact']
        w=csv.DictWriter(fh,fieldnames=fields); w.writeheader()
        w.writerows({k:s[k] for k in fields} for s in all_statements)
    print(json.dumps({'papers':len(papers),'statements':len(all_statements)},indent=2))

if __name__ == '__main__':
    main()
