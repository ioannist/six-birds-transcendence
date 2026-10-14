#!/usr/bin/env python3
"""Generate Appendix C from authored result labels and generated Lean metadata.

Order is the order of labels in the recursively included manuscript, not CSV
order. No Lean name, axiom, or inventory flag is inferred by this renderer.
"""
import argparse
import csv
import json
from pathlib import Path
import re
import sys

from tex_utils import commands, strip_comments

PAPER = Path(__file__).resolve().parents[1]
OUTPUT = PAPER / 'appendices/app_c_index.tex'
PROSE_CLAIMS = ('TTH-02', 'TTH-03', 'TTH-10', 'TTF-01', 'TTF-02', 'TTS-01')
# These supporting claims are stated in prose in the indicated section.
PROSE_SECTIONS = {'TTH-02': 'sec:realization', 'TTH-03': 'sec:lineage',
                  'TTH-10': 'sec:lineage', 'TTF-01': 'sec:ancestry',
                  'TTF-02': 'sec:ancestry', 'TTS-01': 'sec:modes'}


def read_csv(path):
    with path.open(newline='') as source:
        return list(csv.DictReader(source))


def manuscript_labels(paper=PAPER):
    """Walk actual inputs in place, excluding this generated index's references."""
    labels = {}; stack = []
    def walk(path):
        if path == (paper / 'appendices/app_c_index.tex').resolve(): return
        if path in stack: raise ValueError('Recursive manuscript input: ' + str(path))
        stack.append(path)
        text = strip_comments(path.read_text())
        for command in commands(text, {'input', 'include', 'label'}):
            if command['name'] == 'label':
                label = command['argument']
                if label in labels: raise ValueError('Duplicate manuscript label: ' + label)
                labels[label] = (len(labels), path.name)
            else:
                name = Path(command['argument'])
                if not name.suffix: name = name.with_suffix('.tex')
                candidates = [paper / name, path.parent / name]
                target = next((p.resolve() for p in candidates if p.is_file()), None)
                # The generated output may not exist on the first run.
                if name.as_posix() == 'appendices/app_c_index.tex': continue
                if target is None: raise ValueError('Missing manuscript input: ' + str(name))
                if not target.is_relative_to(paper.resolve()): raise ValueError('Input outside paper')
                walk(target)
        stack.pop()
    walk((paper / 'main.tex').resolve())
    return labels


def tex(text):
    replacements = {'&': r'\&', '%': r'\%', '$': r'\$', '#': r'\#',
                    '_': r'\_', '{': r'\{', '}': r'\}', '~': r'\textasciitilde{}',
                    '^': r'\textasciicircum{}', '\\': r'\textbackslash{}'}
    return ''.join(replacements.get(c, c) for c in text)


def code(name):
    """Allow line breaks at namespace, underscore and camel-case boundaries."""
    pieces = re.split(r'(?<=[._])|(?<=[a-z0-9])(?=[A-Z])|(?<=[A-Z])(?=[A-Z][a-z])', name)
    return r'\texttt{' + r'\allowbreak{}'.join(tex(p) for p in pieces) + '}'


def metadata_cell(claim, declaration_map):
    if claim not in declaration_map: raise ValueError('Missing Lean evidence for ' + claim)
    row = declaration_map[claim]
    names = row['headline_declarations'].split(';')
    flags = row['in_inventory'].split(';')
    axioms = json.loads(row['declaration_axioms'])
    if len(names) != len(flags): raise ValueError('Inventory flag count for ' + claim)
    if any('UNRESOLVED' in name or name not in axioms for name in names):
        raise ValueError('Unresolved declaration or missing axiom probe for ' + claim)
    if any(flag not in {'yes', 'no'} for flag in flags): raise ValueError('Invalid inventory flag')
    # Letter tags pair each name with its own probe and flag. They are
    # metadata identifiers, not model values. A shared set is shown once.
    tags = [chr(ord('a') + i) for i in range(len(names))]
    declarations = r'\par\smallskip '.join(
        '(' + tag + ') ' + code(name) for tag, name in zip(tags, names))
    sets = [tuple(axioms[name]) for name in names]
    if len(set(sets)) == 1:
        ax = code(', '.join(sets[0]) if sets[0] else 'none')
    else:
        ax = r'\par\smallskip '.join('(' + tag + ') ' + code(', '.join(values) if values else 'none')
                                     for tag, values in zip(tags, sets))
    inventory = r'\par '.join('(' + tag + ') ' + flag for tag, flag in zip(tags, flags))
    return declarations + ' & ' + ax + ' & ' + inventory


def table(rows, ledger, declaration_map, prose=False):
    head = 'Section / claim' if prose else 'Result / title'
    columns = ''.join(r'>{\raggedright\arraybackslash}p{' + width + r'\textwidth}'
                      for width in ['.205', '.075', '.405', '.195', '.075'])
    lines = [r'\begin{longtable}{@{}' + columns + r'@{}}',
             r'\toprule', head + r' & Registry & Headline Lean declarations & Axioms & In inv. \\',
             r'\midrule', r'\endfirsthead', r'\toprule',
             head + r' & Registry & Headline Lean declarations & Axioms & In inv. \\',
             r'\midrule', r'\endhead', r'\midrule',
             r'\multicolumn{5}{r@{}}{\emph{Continued on next page}} \\',
             r'\endfoot', r'\bottomrule', r'\endlastfoot']
    for row in rows:
        claim = row['claim_id']
        if claim not in ledger: raise ValueError('Unknown ledger claim: ' + claim)
        if prose:
            result = r'\cref{' + PROSE_SECTIONS[claim] + r'}\newline ' + tex(claim)
        else:
            result = r'\cref{' + row['label'] + r'}\newline ' + tex(row['title'])
        lines.append('% claim-index: ' + claim + ('; label: ' + row['label'] if not prose else ''))
        lines.append(r'\raggedright ' + result + ' & ' + tex(ledger[claim]['source_rows'])
                     + ' & ' + metadata_cell(claim, declaration_map) + r' \\')
        lines.append(r'\addlinespace')
    lines.append(r'\end{longtable}')
    return '\n'.join(lines)


def render(paper=PAPER):
    labels = manuscript_labels(paper)
    results = read_csv(paper / 'prewriting/result_labels.csv')
    ledger = {r['claim_id']: r for r in read_csv(paper / 'prewriting/claim_ledger.csv')}
    declaration_map = {r['claim_id']: r for r in read_csv(paper / 'prewriting/lean_declaration_map.csv')}
    seen = set()
    for row in results:
        label = row['label']
        if label in seen: raise ValueError('Duplicate result label in CSV: ' + label)
        seen.add(label)
        if label not in labels: raise ValueError('Unplaced result label: ' + label)
        if labels[label][1] != row['file']: raise ValueError('Result file mismatch: ' + label)
    for claim in PROSE_CLAIMS:
        if PROSE_SECTIONS[claim] not in labels: raise ValueError('Missing prose section: ' + claim)
    results.sort(key=lambda r: labels[r['label']][0])
    lines = ['% style-lint: artifact-appendix',
             '% GENERATED by paper/tools/render_index.py; do not edit.',
             r'\clearpage',
             r'\section{Result-to-Lean index}', r'\label{app:index}',
             r'\begingroup', r'\scriptsize', r'\setlength{\tabcolsep}{2pt}',
             r'\setlength{\LTleft}{0pt}', r'\setlength{\LTright}{0pt}',
             r'\renewcommand{\arraystretch}{1.15}',
             table(results, ledger, declaration_map),
             r'\subsection*{Claims stated in prose}',
             table([{'claim_id': claim} for claim in PROSE_CLAIMS], ledger, declaration_map, prose=True),
             r'\endgroup', '']
    return '\n'.join(lines)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    args = parser.parse_args()
    try: result = render()
    except (ValueError, FileNotFoundError, KeyError) as exc:
        print('ERROR: ' + str(exc), file=sys.stderr); return 1
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_bytes() != result.encode():
            print('Index drift: ' + str(OUTPUT), file=sys.stderr); return 1
        print('PASS: result-to-Lean index matches its inputs'); return 0
    OUTPUT.write_text(result)
    print('Wrote ' + str(OUTPUT)); return 0


if __name__ == '__main__': raise SystemExit(main())
