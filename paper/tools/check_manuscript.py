#!/usr/bin/env python3
"""W8 read-only citation, claim-tag, figure-label and destination integrity."""
import argparse
import csv
import json
from pathlib import Path
import re
from tex_utils import balanced, commands, source_files, strip_comments, macro_declarations, top_level_split, mask_spans, resolve_input, NATBIB_KEYS, control_words

ROOT = Path(__file__).resolve().parents[2]
THEOREMS = {'theorem','lemma','proposition','corollary','definition'}
# Structural indices in the concept figure are not measured model values.
# They are legal only as the literal, complete body of a node in fig_three.tex.
SCHEMATIC_INDICES = {'episodeStageOne':'1','episodeStageTwo':'2',
                     'episodeStageThree':'3','episodeStageFour':'4'}


def bib_keys(path):
    text=re.sub(r'(?m)^\s*%.*$', '',path.read_text())
    return set(re.findall(r'(?im)^\s*@(?!(?:comment|string|preamble)\b)[a-z]+\s*[\{(]\s*([^,\s]+)\s*,',text))


def macro_records(text):
    records = {}
    for record in macro_declarations(text):
        if record['name'] in records and record != records[record['name']]:
            raise ValueError('Unsupported repeated macro declaration: '+record['name'])
        records[record['name']] = record
    for match in re.finditer(r'\\foreach\s*\\([A-Za-z]+)\s+in\s*\{([^}]+)\}', strip_comments(text)):
        records[match[1]] = dict(name=match[1], body=match[2], args=0, default=None)
    return records


def macro_definitions(text):
    return {name:r['body'] for name,r in macro_records(text).items()}


def macro_call(text, end, record):
    pos = end; values=[]
    def skip():
        nonlocal pos
        while pos<len(text) and text[pos].isspace():pos+=1
    if record['default'] is not None:
        skip()
        if pos<len(text) and text[pos]=='[':
            group=balanced(text,pos,'[',']')
            if not group:raise ValueError('Unbalanced optional macro argument')
            values.append(text[group[0]:group[1]]);pos=group[2]
        else:values.append(record['default'])
    while len(values)<record['args']:
        skip()
        if pos>=len(text):raise ValueError('Missing argument for macro '+record['name'])
        group=balanced(text,pos)
        if group:values.append(text[group[0]:group[1]]);pos=group[2]
        elif text[pos]=='\\':
            token=re.match(r'\\(?:[A-Za-z@]+|.)',text[pos:])
            if not token:raise ValueError('Unsupported macro argument')
            values.append(token[0]);pos+=token.end()
        else:values.append(text[pos]);pos+=1
    body=record['body']
    for index,value in reversed(list(enumerate(values,1))):body=body.replace('#'+str(index),value)
    return body,pos


def expand_macros(text, records, selected, approved, chain=()):
    if len(chain)>30:raise ValueError('Macro expansion depth exceeds supported limit')
    out=[]; previous=0
    for match in control_words(text):
        if match.start()<previous:continue
        name=match[1]
        if name not in selected or name in approved:continue
        if name in chain:raise ValueError('Recursive macro expansion: '+name)
        body,end=macro_call(text,match.end(),records[name])
        out.extend([text[previous:match.start()],expand_macros(body,records,selected,approved,chain+(name,))])
        previous=end
    out.append(text[previous:]);result=''.join(out)
    if len(result)>2000000:raise ValueError('Macro expansion exceeds supported size')
    return result


def numeric_label_errors(label, approved, definitions, seen=None, records=None, assigned=()):
    if records is None:
        records={name:dict(name=name,body=body,args=0,default=None) for name,body in definitions.items()}
    expanded=expand_macros(label,records,set(records),approved)
    errors=['Unsupported reassigned node macro: \\'+name for name in {m[1] for m in control_words(label)} & set(assigned)]
    if re.search(r'\d', expanded): errors.append('literal digit in TikZ node text (including macro expansion)')
    safe = set('text textbf textit textsf textrm texttt emph ensuremath mathbf mathit mathrm mathsf mathtt mathcal mathbb mathfrak operatorname frac tfrac dfrac sqrt left right cdot times to mapsto longrightarrow leftrightarrow implies iff in notin subset subseteq cup cap emptyset varnothing infty pm mp le ge leq geq neq equiv sim simeq approx vert Vert mid ldots cdots dots quad qquad small scriptsize tiny footnotesize normalsize large Large newline linebreak LaTeX TeX alpha beta gamma delta epsilon varepsilon zeta eta theta vartheta iota kappa lambda mu nu xi omicron pi varpi rho varrho sigma varsigma tau upsilon phi varphi chi psi omega Gamma Delta Theta Lambda Xi Pi Sigma Upsilon Phi Psi Omega'.split())
    for name in (m[1] for m in control_words(expanded)):
        if name not in approved and name not in safe:
            errors.append('Unsupported macro in TikZ node text: \\'+name)
        if name.startswith('snap') and name not in approved:errors.append('unknown snapshot macro \\'+name)
    return errors


def node_texts(text, assigned=()):
    for environment in re.finditer(r'\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}',text,re.S):
        block=environment[0]
        if block.count(r'\begin{tikzpicture}')>1:raise ValueError('Unsupported nested tikzpicture')
        changed={m[1] for m in control_words(block)} & set(assigned)
        if changed:raise ValueError('Unsupported reassigned macro in TikZ: '+','.join(sorted(changed)))
        unsupported=re.search(r'\\(?:csname|expandafter|let|edef|gdef|xdef|def|newcommand|renewcommand|pgfmathsetmacro|pgfmathtruncatemacro|pgfmathparse|tikzmath|foreach|directlua|scantokens)\b',block)
        if unsupported:raise ValueError('Unsupported dynamic TikZ construction: '+unsupported[0])
        consumed=0
        for node in re.finditer(r'(?<![A-Za-z])(?:\\)?node\b',block):
            if node.start()<consumed:continue
            pos=node.end()
            while pos<len(block) and block[pos]!=';':
                if block[pos]=='[':
                    group=balanced(block,pos,'[',']')
                    if not group:raise ValueError('Unbalanced TikZ node options')
                    for option in top_level_split(block[group[0]:group[1]]):
                        key,separator,value=option.partition('=')
                        if separator and key.strip() in {'label','pin'}:
                            value=value.strip()
                            group_value=balanced(value,0)
                            if group_value and group_value[2]==len(value):value=value[group_value[0]:group_value[1]]
                            # The last top-level colon separates positioning from
                            # displayed text; commas inside its braces stay intact.
                            value=top_level_split(value,':')[-1].strip()
                            yield environment.start()+pos,value
                    pos=group[2];continue
                if block[pos]=='(':
                    group=balanced(block,pos,'(',')')
                    if not group:raise ValueError('Unbalanced TikZ node coordinates')
                    pos=group[2];continue
                if block[pos]=='{':
                    group=balanced(block,pos)
                    if not group:raise ValueError('Unbalanced TikZ node text')
                    yield environment.start()+pos,block[group[0]:group[1]];consumed=group[2];break
                pos+=1
            else:raise ValueError('Unsupported TikZ node syntax: missing braced text')
    outside=mask_spans(text,[(m.start(),m.end()) for m in re.finditer(r'\\begin\{tikzpicture\}.*?\\end\{tikzpicture\}',text,re.S)])
    if re.search(r'\\(?:node|draw|path|tikz)\b',outside):
        raise ValueError('Unsupported drawing outside a parsed tikzpicture')


def mask_concept_ordinals(text):
    """Remove only validated standalone ordinal node bodies from inspection.

    Ordinals never enter the general approved-number set. Composition, aliases,
    option labels, and uses outside nodes remain errors, rather than new data.
    """
    declarations=[r for r in macro_declarations(text) if r['name'] in SCHEMATIC_INDICES]
    valid={r['name'] for r in declarations if r['body']==SCHEMATIC_INDICES[r['name']]
           and r['args']==0 and r['default'] is None}
    text=mask_spans(text,[(r['start'],r['end']) for r in declarations])
    spans=[]
    for offset,label in node_texts(text):
        if label.strip() not in {'\\'+name for name in valid}:continue
        # node_texts also yields option labels; only an actual node body qualifies.
        group=balanced(text,offset)
        if group and text[group[0]:group[1]]==label:
            spans.append((group[0],group[1]))
    text=mask_spans(text,spans)
    remaining={m[1] for m in control_words(text)} & set(SCHEMATIC_INDICES)
    if remaining:
        raise ValueError('Schematic ordinal must be the entire literal node body in fig_three.tex: '+
                         ','.join(sorted(remaining)))
    return text


def expanded_drawing_sources(paper, files, records, approved, assigned=()):
    """Preserve TikZ context across inputs and simple invoked drawing macros.

    Delimited/recursive/repeated declarations and dynamic PGF/TeX assignments
    are rejected; the checker does not claim to execute arbitrary TeX programs.
    """
    incoming=set()
    for path in files:
        for command in commands(strip_comments(path.read_text()),{'input','include'}):
            incoming.add(resolve_input(paper,path,command['argument']))
    roots=[p for p in files if p not in incoming or p==paper/'main.tex']
    drawings={name for name,r in records.items() if re.search(r'\\(?:node|draw|path|fill|shade|tikz|input|include)\b|\bnode\b',r['body'])}
    while True:
        extended=drawings|{name for name,r in records.items() if set(re.findall(r'\\([A-Za-z@]+)',r['body'])) & drawings}
        if extended==drawings:break
        drawings=extended
    if drawings & set(assigned):raise ValueError('Unsupported reassignment of drawing macro')
    def expand(path,chain=()):
        if path in chain:raise ValueError('Recursive input: '+str(path))
        text=strip_comments(path.read_text())
        if path==paper/'figures/fig_three.tex':text=mask_concept_ordinals(text)
        text=mask_spans(text,[(r['start'],r['end']) for r in macro_declarations(text)])
        text=expand_macros(text,records,drawings,approved)
        return expand_inputs(text,path,chain+(path,))
    def expand_inputs(text,path,chain):
        out=[];previous=0
        for command in commands(text,{'input','include'}):
            out.extend([text[previous:command['start']],expand(resolve_input(paper,path,command['argument']),chain)])
            previous=command['end']
        out.append(text[previous:]);result=''.join(out)
        if re.search(r'\\(?:input|include)\b',result):raise ValueError('Unsupported unbraced input or include')
        return result
    return [(path,expand(path)) for path in roots]


def check(paper, destination_map=None):
    paper=Path(paper).resolve(); errors=[]; labels=set(); files=source_files(paper)
    citations=bib_keys(paper/'prewriting/references_core.bib')|bib_keys(paper/'prewriting/references_sixbirds.bib')
    with (paper/'prewriting/claim_ledger.csv').open(newline='') as stream: claim_ids={r['claim_id'] for r in csv.DictReader(stream)}
    approved=set(macro_definitions((paper/'figures/generated/figdata.tex').read_text()))
    snapshot_names=set(approved)
    records={}; duplicates=set()
    for path in files:
        if path==paper/'figures/generated/figdata.tex':continue
        if path!=paper/'figures/fig_three.tex':
            for name in {m[1] for m in control_words(strip_comments(path.read_text()))} & set(SCHEMATIC_INDICES):
                errors.append('schematic ordinal used outside concept figure: '+name)
        for name,record in macro_records(path.read_text()).items():
            if name in SCHEMATIC_INDICES:
                if (path!=paper/'figures/fig_three.tex' or record['body']!=SCHEMATIC_INDICES[name]
                        or record['args']!=0 or record['default'] is not None):
                    errors.append('invalid schematic ordinal declaration: '+name)
            if name in records and records[name]['body']!=record['body']:duplicates.add(name)
            records[name]=record
    for name in sorted(duplicates):errors.append('Unsupported ambiguous macro redefinition: '+name)
    assigned={name for path in files for name in re.findall(
        r'\\(?:let|pgfmathsetmacro|pgfmathtruncatemacro)\s*(?:\{\s*)?\\([A-Za-z@]+)',
        strip_comments(path.read_text()))}
    for name in approved & assigned:errors.append('snapshot macro reassigned outside figdata.tex: \\'+name)
    for name in set(SCHEMATIC_INDICES) & assigned:errors.append('schematic ordinal reassigned: \\'+name)
    definitions={name:r['body'] for name,r in records.items()}
    for name in snapshot_names & set(definitions):
        errors.append('snapshot macro redefined outside figdata.tex: \\'+name)
    cite_count=theorem_count=node_count=0
    for path in files:
        raw=path.read_text(); clean=strip_comments(raw); display=str(path.relative_to(paper)); lines=raw.splitlines()
        for c in commands(clean):
            line=clean.count('\n',0,c['start'])+1
            if c['name'] in NATBIB_KEYS:
                for key in c['argument'].split(','):
                    key=key.strip(); cite_count+=1
                    if c['name']=='nocite' and key=='*':continue
                    if key not in citations: errors.append(f'{display}:{line}: unknown citation {key!r}')
            if c['name']=='label' and c['argument'].startswith('sec:'): labels.add(c['argument'])
        for begin in re.finditer(r'\\begin\{('+ '|'.join(sorted(THEOREMS)) +r')\}',clean):
            theorem_count+=1; line=clean.count('\n',0,begin.start())+1
            tag=lines[line] if line<len(lines) else ''
            match=re.fullmatch(r'\s*%\s*claim:\s*([^%]+?)\s*',tag)
            if not match:
                errors.append(f'{display}:{line}: {begin[1]} needs a claim comment on the next line'); continue
            for cid in (s.strip() for s in match[1].split(',')):
                if cid not in claim_ids: errors.append(f'{display}:{line+1}: unknown claim ID {cid!r}')
    try:
        for path,expanded in expanded_drawing_sources(paper,files,records,approved,assigned):
            for offset,label in node_texts(expanded,assigned):
                node_count+=1;line=expanded.count('\n',0,offset)+1
                for error in numeric_label_errors(label,approved,definitions,records=records,assigned=assigned):
                    errors.append(f'{path.relative_to(paper)}:expanded:{line}: {error}')
    except (ValueError,FileNotFoundError) as exc:
        errors.append('TikZ inspection error: '+str(exc))
    if destination_map is not None:
        # Future authored JSON mapping: logical slot -> sec:label (or a list).
        for slot,value in destination_map.items():
            values=[value] if isinstance(value,str) else value
            for label in values:
                if label not in labels: errors.append(f'destination {slot!r}: missing section label {label!r}')
    return dict(errors=errors,section_labels=sorted(labels),files=len(files),citation_keys=cite_count,
                theorem_environments=theorem_count,tikz_nodes=node_count,
                destinations='mapping pending' if destination_map is None else 'checked')


def main():
    parser=argparse.ArgumentParser(description=__doc__); parser.add_argument('paper',nargs='?',type=Path,default=ROOT/'paper')
    parser.add_argument('--destinations',type=Path,help='optional slot -> sec:label JSON mapping'); args=parser.parse_args()
    try:
        result=check(args.paper,json.loads(args.destinations.read_text()) if args.destinations else None)
    except (ValueError,FileNotFoundError) as exc:
        print('ERROR: unsupported manuscript construction: '+str(exc));return 1
    for error in result['errors']: print('ERROR: '+error)
    print(json.dumps(result,sort_keys=True)); return int(bool(result['errors']))


if __name__=='__main__': raise SystemExit(main())
