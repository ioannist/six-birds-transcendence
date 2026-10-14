#!/usr/bin/env python3
"""W8 prose-style report; --strict enforces audience_style_guide.md §9.

Abstract, section/appendix prose and captions (including draft files) are scanned.
Captions are separate rows and counted once in TOTAL. Math is masked except its
balanced \\text arguments. First-line exemption markers exclude entire files.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
from check_manuscript import node_texts
from tex_utils import balanced, blank, commands, mask_spans, source_files, strip_comments, mask_math, NATBIB_KEYS

ROOT = Path(__file__).resolve().parents[2]
DENYLIST = ROOT / 'paper/prewriting/style_denylist.txt'
WORDS = re.compile(r"\b[A-Za-z]+(?:['-][A-Za-z]+)*\b")

EXEMPT = {'% style-lint: six-birds-section', '% style-lint: artifact-appendix'}
HIDDEN = {'ref', 'Cref', 'cref', 'eqref', 'pageref', 'autoref', 'nameref', 'label',
          'input', 'include', 'url', 'doi', 'nocite'}
ABBREVIATION = re.compile(r'\b(?:e\.g|i\.e|et al|cf|vs|Fig|Eq|Sec|[A-Z])\.', re.I)
PAPER_AGENT = re.compile(r'\b(?:this paper|the paper|this article|the article)\b', re.I)
PREPOSITION = re.compile(r'\b(?:in|of|to|for|from|with|throughout|beyond|within|about|across|by|on|at)\s*$', re.I)


def denylist(path=DENYLIST):
    rules = []
    for line in Path(path).read_text().splitlines():
        if not line.strip() or line.lstrip().startswith('#'): continue
        pattern, _, replacement = line.partition(' # ')
        rules.append((re.compile(pattern.strip()), replacement.strip()))
    return rules


def protected_text(text, metrics=False):
    text = mask_math(strip_comments(text))
    if metrics:
        # Keywords are a list, including physical continuation lines. Mask
        # only that paragraph; retain it unchanged for the denylist scan.
        spans = []
        for marker in re.finditer(r'(?m)^[ \t]*\\noindent\s*\\textbf\{Keywords\.\}', text):
            boundary = re.search(r'\n[ \t]*\n|\\par\b|^[ \t]*\\(?:input|include|section|subsection|subsubsection|paragraph|begin|end)\b',
                                 text[marker.end():], re.M)
            end = marker.end() + boundary.start() if boundary else len(text)
            spans.append((marker.start(), end))
        text = mask_spans(text, spans)
    hidden_names = HIDDEN | NATBIB_KEYS
    if metrics: hidden_names |= {'section','subsection','subsubsection','paragraph'}
    hidden = [c for c in commands(text) if c['name'] in hidden_names]
    text = mask_spans(text, [(c['start'], c['end']) for c in hidden])
    if metrics:
        for env in ['tikzpicture', 'table', 'table*', 'tabular', 'tabular*', 'tabularx', 'longtable', 'xltabular']:
            pattern = r'\\begin\{' + re.escape(env) + r'\}.*?\\end\{' + re.escape(env) + r'\}'
            text = re.sub(pattern, lambda m: blank(m[0]), text, flags=re.S)
    else:
        # Keep displayed node/label text, not TikZ options or coordinate names.
        def visible_nodes(match):
            raw=match[0]; out=list(blank(raw))
            for offset,label in node_texts(raw):
                pos=raw.find(label,offset)
                if pos<0:raise ValueError('Cannot locate visible TikZ label')
                out[pos:pos+len(label)]=label
            return ''.join(out)
        text=re.sub(r'\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}',visible_nodes,text,flags=re.S)
    return text


def prose(text, metrics=True):
    text = protected_text(text, metrics=metrics)
    text = re.sub(r'\\(?:begin|end)\{[^{}]*\}(?:\[[^]]*\])?', lambda m: blank(m[0]), text)
    # Consume control symbols (especially a line break) before a following
    # word, so \\\\toy keeps the visible word and does not become \\toy.
    text = re.sub(r'\\(?:([A-Za-z@]+)\*?|.)', lambda m: blank(m[0]) if m[1] else ' ', text, flags=re.S)
    return text.translate(str.maketrans({'{':' ', '}':' ', '~':' '}))


def hits(text, path=Path('<fixture>'), rules=None):
    rules = denylist() if rules is None else rules
    clean = prose(text, metrics=False); raw = protected_text(text)
    found = []
    for pattern, replacement in rules:
        # Command-specific rules (grade markers) also inspect the protected TeX.
        sources = [clean, raw] if pattern.pattern.startswith('\\\\') else [clean]
        seen = set()
        for source in sources:
            for match in pattern.finditer(source):
                line = source.count('\n', 0, match.start()) + 1
                key = line, match[0]
                if key in seen: continue
                seen.add(key)
                found.append(dict(file=str(path), line=line, match=match[0], replacement=replacement))
    return found


def outside_list_colons(text):
    depth = 0; count = 0; previous = 0
    events = re.finditer(r'\\(begin|end)\{(?:itemize|enumerate|description)\}', text)
    for event in events:
        if not depth: count += prose(text[previous:event.start()]).count(':')
        depth += 1 if event[1] == 'begin' else -1
        depth = max(0, depth); previous = event.end()
    if not depth: count += prose(text[previous:]).count(':')
    return count


def measures(text):
    body = prose(text); words = WORDS.findall(body); count = len(words)
    first = len(re.findall(r'\b(?:we|our|us)\b', body, re.I))
    agent = sum(not PREPOSITION.search(clause[:m.start()]) and bool(WORDS.search(clause[m.end():]))
                for clause in re.split(r'[.;:!?\n]', body) for m in PAPER_AGENT.finditer(clause))
    sentences = re.split(r'[.!?]+', ABBREVIATION.sub(lambda m:m[0].replace('.', '\0'), body))
    sentences = [s for s in sentences if WORDS.search(s)]
    rate = lambda n: 1000*n/count if count else 0.0
    return dict(words=count, first_person_per_1000=rate(first), paper_agent_per_1000=rate(agent),
                semicolons_per_1000=rate(body.count(';')), colons_per_1000=rate(outside_list_colons(protected_text(text, metrics=True))),
                mean_sentence_words=count/len(sentences) if sentences else 0.0)


def target_failures(row):
    failed = []
    if row['words']:
        for key, bound, minimum in [('first_person_per_1000',6,True), ('paper_agent_per_1000',.7,False),
                ('semicolons_per_1000',9,False), ('colons_per_1000',12,False), ('mean_sentence_words',26,False)]:
            if row.get('kind') == 'caption' and key == 'first_person_per_1000': continue
            if (row[key]<bound if minimum else row[key]>bound): failed.append(key)
    if row['denylist_hits']: failed.append('denylist_hits')
    return failed


def caption_commands(text):
    found = commands(text, {'caption','captionof'})
    for command in found:
        if command['name']=='captionof':
            pos=command['end']
            while pos<len(text) and text[pos].isspace(): pos+=1
            group=balanced(text,pos)
            if not group: raise ValueError('Missing captionof text')
            command.update(argument=text[group[0]:group[1]],arg_start=group[0],arg_end=group[1],end=group[2])
    return found


def analyze(paper):
    paper = Path(paper).resolve(); rows = []; exempt = []; total_parts = []
    rules = denylist()
    def add(name, path, text, kind, line_offset=0):
        findings=hits(text,path,rules)
        for finding in findings: finding['line']+=line_offset
        row = dict(section=name, file=str(path), kind=kind,
                   **measures('' if kind == 'table' else text), denylist_hits=findings)
        row['failed_targets'] = target_failures(row); rows.append(row)
        if kind != 'table': total_parts.append(text)
    for path in source_files(paper):
        text = path.read_text(); first = text.splitlines()[0].strip() if text.splitlines() else ''
        if first in EXEMPT:
            exempt.append(dict(file=str(path), marker=first)); continue
        clean = strip_comments(text)
        if path == paper/'main.tex':
            abstract = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', clean, re.S)
            if abstract: add('abstract', path, abstract[1], 'abstract', clean[:abstract.start(1)].count('\n'))
            document = re.search(r'\\begin\{document\}(.*?)\\end\{document\}',clean,re.S)
            if document:
                for i,caption in enumerate(caption_commands(document[1]),1):
                    add(f'main:caption:{i}',path,caption['argument'],'caption', clean[:document.start(1)+caption['arg_start']].count('\n'))
            continue
        if path.is_relative_to(paper/'includes') or path.is_relative_to(paper/'figures/generated'): continue
        abstract = re.search(r'\\begin\{abstract\}(.*?)\\end\{abstract\}', clean, re.S)
        if abstract:
            add('abstract', path, abstract[1], 'abstract', clean[:abstract.start(1)].count('\n'))
            clean = mask_spans(clean, [(abstract.start(), abstract.end())])
        captions = caption_commands(clean)
        for i, caption in enumerate(captions,1):
            add(f'{path.stem}:caption:{i}', path, caption['argument'], 'caption', clean[:caption['arg_start']].count('\n'))
        if any(path.is_relative_to(paper/directory) for directory in ['sections','appendices','figures','tables']):
            body = mask_spans(clean, [(c['start'],c['end']) for c in captions])
            kind = 'table' if path.is_relative_to(paper/'tables') else 'figure' if path.is_relative_to(paper/'figures') else 'section'
            add(path.stem, path, body, kind)
    combined = '\n\n'.join(total_parts)
    total = dict(section='TOTAL', kind='paper', **measures(combined), denylist_hits=[h for r in rows for h in r['denylist_hits']])
    total['failed_targets'] = target_failures(total)
    return dict(paper=str(paper), rows=rows, exempt=exempt, total=total)


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('paper', nargs='?', type=Path, default=ROOT/'paper')
    parser.add_argument('--strict',action='store_true'); parser.add_argument('--json',action='store_true'); args=parser.parse_args()
    try: result=analyze(args.paper)
    except (ValueError,FileNotFoundError) as exc:
        print('ERROR: unsupported TeX construction: '+str(exc));return 1
    if args.json: print(json.dumps(result,indent=2))
    else:
        print('section | words | we/1000 | paper-subject/1000 | semicolons/1000 | colons/1000 | mean sentence | deny hits | misses')
        for row in [*result['rows'],result['total']]:
            vals=[f'{row[k]:.2f}' for k in ['first_person_per_1000','paper_agent_per_1000','semicolons_per_1000','colons_per_1000','mean_sentence_words']]
            print(' | '.join([row['section'],str(row['words']),*vals,str(len(row['denylist_hits'])),','.join(row['failed_targets'])]))
        print(f"Exempt files: {len(result['exempt'])}")
    return int(args.strict and any(r['failed_targets'] for r in [*result['rows'],result['total']]))


if __name__=='__main__': raise SystemExit(main())
