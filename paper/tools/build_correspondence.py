#!/usr/bin/env python3
"""Generate paper/Lean statement pairs for W18, using fresh #check output."""
import argparse
import csv
import json
from pathlib import Path
import re
import subprocess
import sys

from render_index import manuscript_labels
from tex_utils import balanced, commands, strip_comments

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'paper'
OUTPUT = PAPER / 'prewriting/statement_correspondence.md'
PROBE = ROOT / 'lean/.validate-logs/W18a-statement-probe.lean'
PROBE_LOG = PROBE.with_suffix('.log')
TYPE_LIMIT = 4000
# Literal search phrases identify passages, not new paraphrases or evidence.
# Their concepts are the corresponding allowed_claim clauses in the ledger.
# Missing matches fail generation so wording changes cannot silently lose a pair.
PROSE_PHRASES = {
    'TTH-02': ('typed maps', 'each mapped piece'),
    'TTH-03': ('eight fields of the temporal signature', 'checked frontier of histories'),
    'TTH-10': ('record arrow', 'every strict step'),
    'TTF-01': ('predictive classes', 'unique'),
    'TTF-02': ('admissible seeds of provenance', 'least ancestry relation'),
    'TTS-01': ('relation of continuity paths', 'mixed paths compose'),
}


def read_csv(path):
    with path.open(newline='') as source: return list(csv.DictReader(source))


def source_file(paper, name):
    found = [p for folder in ['sections', 'appendices']
             if (p := paper / folder / name).is_file()]
    if len(found) != 1: raise ValueError('Ambiguous or missing result source: ' + name)
    return found[0]


def remove_metadata(body):
    return re.sub(r'(?m)^[ \t]*(?:%[ \t]*claim:[^\n]*|\\label\{[^}\n]+\})[ \t]*(?:\n|\Z)',
                  '', body).strip('\n')


def paper_statement(row, paper=PAPER):
    """Balance every environment, retaining original text rather than a regex body."""
    path = source_file(paper, row['file']); raw = path.read_text()
    clean = strip_comments(raw)
    labels = [c for c in commands(clean, {'label'}) if c['argument'] == row['label']]
    if len(labels) != 1: raise ValueError('Missing or duplicate result label: ' + row['label'])
    stack = []; candidates = []
    for token in re.finditer(r'\\(begin|end)\{([^}]+)\}', clean):
        name = token[2]
        if token[1] == 'begin':
            start = token.end()
            # A theorem's optional title is header metadata, not its body.
            pos = start
            while pos < len(clean) and clean[pos].isspace(): pos += 1
            if pos < len(clean) and clean[pos] == '[':
                optional = balanced(clean, pos, '[', ']')
                if not optional: raise ValueError('Unbalanced environment title: ' + row['label'])
                start = optional[2]
            stack.append((name, start))
        else:
            if not stack or stack[-1][0] != name:
                raise ValueError('Unbalanced environment in ' + str(path))
            _, start = stack.pop()
            if name == row['environment'] and start <= labels[0]['start'] < token.start():
                candidates.append((start, token.start()))
    if stack: raise ValueError('Unclosed environment in ' + str(path))
    if len(candidates) != 1: raise ValueError('Result environment mismatch: ' + row['label'])
    start, end = candidates[0]; body = raw[start:end]
    markers = re.findall(r'(?m)^\s*% claim:\s*([^\n]+)', body)
    if row['claim_id'] not in {c.strip() for marker in markers for c in marker.split(',')}:
        raise ValueError('Claim marker mismatch: ' + row['label'])
    statement = remove_metadata(body)
    if not statement.strip(): raise ValueError('Empty paper statement: ' + row['label'])
    return dict(text=statement, path=path.relative_to(paper).as_posix(),
                line=raw[:start].count('\n') + 1)


def prose_passages(claim, paper=PAPER):
    """Search whole paragraphs; preserve their LaTeX lines and source locations."""
    found = []
    structure = re.compile(r'^[ \t]*(?:%[^\n]*|\\label\{[^}]+\}|'
                           r'\\(?:begin|end)\{[^}]+\}(?:\[[^\n]*\])?)[ \t]*$')
    for path in sorted((paper / 'sections').glob('*.tex')):
        raw = path.read_text(); cursor = 0
        for paragraph in re.split(r'\n[ \t]*\n', raw):
            offset = raw.find(paragraph, cursor); cursor = offset + len(paragraph)
            normalized = re.sub(r'\s+', ' ', strip_comments(paragraph)).lower()
            if not all(phrase in normalized for phrase in PROSE_PHRASES[claim]): continue
            lines = paragraph.splitlines(keepends=True)
            while lines and (not lines[0].strip() or structure.fullmatch(lines[0].rstrip('\n'))):
                offset += len(lines.pop(0))
            while lines and (not lines[-1].strip() or structure.fullmatch(lines[-1].rstrip('\n'))):
                lines.pop()
            body = ''.join(lines).rstrip('\n')
            if not body.strip(): raise ValueError('Empty prose match: ' + claim)
            found.append(dict(text=body, path=path.relative_to(paper).as_posix(),
                              line=raw[:offset].count('\n') + 1))
    if not found: raise ValueError('No prose passage matches the declared phrases for ' + claim)
    return found


def headline_records(row):
    names = row['headline_declarations'].split(';')
    flags = row['in_inventory'].split(';')
    axioms = json.loads(row['declaration_axioms'])
    if len(names) != len(flags): raise ValueError('Inventory flag count: ' + row['claim_id'])
    records = []
    for name, flag in zip(names, flags):
        if not re.fullmatch(r"CSTTT\.[\w'.]+", name) or 'UNRESOLVED' in name or name not in axioms:
            raise ValueError('Unresolved headline or missing axiom set: ' + name)
        if flag not in {'yes', 'no'}: raise ValueError('Invalid inventory flag: ' + name)
        records.append(dict(name=name, axioms=axioms[name], in_inventory=flag))
    if not records: raise ValueError('No Lean declaration for ' + row['claim_id'])
    return records


def parse_probe(output, names):
    found = {}; failed = []
    for name in names:
        match = re.search(re.escape('W18A_BEGIN ' + name) + r'\n(.*?)\n' +
                          re.escape('W18A_END ' + name) + r'(?:\n|\Z)', output, re.S)
        if not match or not match[1].strip() or re.search(r'\b(?:error|warning):', match[1]):
            failed.append(name)
        else: found[name] = match[1].strip()
    if failed: raise ValueError('Lean #check failed: ' + '; '.join(failed))
    return found


def lean_types(names):
    names = sorted(set(names)); PROBE.parent.mkdir(parents=True, exist_ok=True)
    lines = ['import CSTTT', 'set_option pp.proofs false',
             'set_option pp.fullNames true']
    for name in names:
        lines += ['#eval IO.println ' + json.dumps('W18A_BEGIN ' + name),
                  '#check @' + name,
                  '#eval IO.println ' + json.dumps('W18A_END ' + name)]
    PROBE.write_text('\n'.join(lines) + '\n')
    result = subprocess.run(['lake', 'env', 'lean', str(PROBE.relative_to(ROOT / 'lean'))],
                            cwd=ROOT / 'lean', text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT, timeout=600)
    PROBE_LOG.write_text(result.stdout)
    types = parse_probe(result.stdout, names)
    if result.returncode: raise ValueError('Lean probe exited nonzero; see ' + str(PROBE_LOG))
    return types


def digest_items(text):
    matches = list(re.finditer(r'(?m)^## (.+)$', text))
    result = []
    for i, match in enumerate(matches):
        end = matches[i+1].start() if i+1 < len(matches) else len(text)
        title = match[1]
        slug = re.sub(r'[^\w\s-]', '', title.lower())
        slug = re.sub(r'\s', '-', slug)
        result.append(dict(title=title, body=text[match.end():end], slug=slug))
    return result


def digest_links(claim, records, items, source_rows=()):
    ids = [claim, *(row for row in source_rows if re.fullmatch(r'(?:TTH|TTN|TTD|TTF|TTS)-\d{2}', row))]
    pattern = re.compile(r'(?<![A-Za-z0-9-])(?:' + '|'.join(re.escape(x) for x in ids) + r')(?![A-Za-z0-9-])')
    matched = [item for item in items if pattern.search(item['title'])]
    if not matched:
        matched = [item for item in items if pattern.search(item['body']) or
                   any(record['name'] in item['title'] + item['body'] for record in records)]
    if not matched: return 'Digest item: none matched by claim/source-row ID or headline declaration.'
    return 'Digest: ' + '; '.join('[' + item['title'] + '](formal_digest.md#' + item['slug'] + ')'
                                 for item in matched)


def fence(language, text):
    # A longer fence preserves any literal Markdown fences in the source.
    longest = max((len(x) for x in re.findall(r'`+', text)), default=0)
    tick = '`' * max(3, longest+1)
    return tick + language + '\n' + text + '\n' + tick


def lean_cell(records, types):
    sections = []
    for record in records:
        name = record['name']
        if name not in types or not types[name].strip(): raise ValueError('No printed Lean type: ' + name)
        full = types[name]; shown = full[:TYPE_LIMIT]
        sections += ['#### `' + name + '`',
                     '**Axioms (declaration map):** ' + (', '.join('`' + ax + '`' for ax in record['axioms']) or 'none') +
                     '. **in_inventory:** `' + record['in_inventory'] + '`.', fence('lean', shown)]
        if len(full) > TYPE_LIMIT:
            sections.append('**TRUNCATED:** showing the first 4,000 characters of ' + str(len(full)) +
                            '. Full output: [W18a-statement-probe.log](../../lean/.validate-logs/W18a-statement-probe.log).')
    return '\n\n'.join(sections)


def pair(paper_cell, records, types):
    # Blank lines allow fenced Markdown inside HTML table cells in GFM.
    return ('<table>\n<tr><th>Paper statement (LaTeX)</th><th>Lean headline declarations</th></tr>\n'
            '<tr><td valign="top">\n\n' + paper_cell + '\n\n</td><td valign="top">\n\n' +
            lean_cell(records, types) + '\n\n</td></tr>\n</table>')


def collect(paper=PAPER):
    ledger = {r['claim_id']: r for r in read_csv(paper / 'prewriting/claim_ledger.csv')}
    declaration_map = {r['claim_id']: r for r in read_csv(paper / 'prewriting/lean_declaration_map.csv')}
    labels = manuscript_labels(paper)
    rows = read_csv(paper / 'prewriting/result_labels.csv')
    entries = []; seen = set()
    for row in sorted(rows, key=lambda r: labels[r['label']][0]):
        if row['label'] in seen: raise ValueError('Duplicate result label: ' + row['label'])
        seen.add(row['label']); claim = row['claim_id']
        if claim not in ledger or claim not in declaration_map: raise ValueError('Missing claim evidence: ' + claim)
        entries.append(dict(row=row, passages=[paper_statement(row, paper)],
                            records=headline_records(declaration_map[claim]), prose=False,
                            source_rows=ledger[claim]['source_rows'].split(';')))
    for claim in PROSE_PHRASES:
        if claim not in ledger or claim not in declaration_map: raise ValueError('Missing prose evidence: ' + claim)
        entries.append(dict(row=dict(claim_id=claim), passages=prose_passages(claim, paper),
                            records=headline_records(declaration_map[claim]), prose=True,
                            source_rows=ledger[claim]['source_rows'].split(';')))
    return entries


def render(entries, types, digest):
    lines = ['# Paper-to-Lean statement correspondence',
             '<!-- GENERATED by paper/tools/build_correspondence.py; do not edit. -->',
             'Formal entries follow manuscript label order. The paper column is verbatim LaTeX with '
             'claim and label lines removed; prose entries quote matched paragraphs. Lean columns '
             'are fresh `#check @Name` output, with `pp.proofs false` and `pp.fullNames true`. '
             'Axioms and inventory flags are copied from `lean_declaration_map.csv`. '
             'Digest links match claim/source-row IDs or full headline names; they are not a statement-correspondence verdict.',
             'Probe: [W18a-statement-probe.lean](../../lean/.validate-logs/W18a-statement-probe.lean); '
             '[full output](../../lean/.validate-logs/W18a-statement-probe.log).']
    items = digest_items(digest)
    for i, entry in enumerate(entries, 1):
        row = entry['row']; claim = row['claim_id']
        title = ('Prose-only claim `' + claim + '`' if entry['prose'] else
                 '`' + row['label'] + '` — ' + row['environment'] + ': ' + row['title'] + ' (`' + claim + '`)')
        lines += ['## ' + str(i) + '. ' + title, '<!-- correspondence-claim: ' + claim +
                  ('' if entry['prose'] else '; label: ' + row['label']) + ' -->',
                  digest_links(claim, entry['records'], items, entry['source_rows'])]
        passages = []
        for passage in entry['passages']:
            passages += ['Source: `' + passage['path'] + ':' + str(passage['line']) + '`.',
                         fence('latex', passage['text'])]
        lines.append(pair('\n\n'.join(passages), entry['records'], types))
    return '\n\n'.join(lines) + '\n'


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true'); args = parser.parse_args()
    try:
        entries = collect()
        types = lean_types(r['name'] for entry in entries for r in entry['records'])
        content = render(entries, types, (PAPER / 'prewriting/formal_digest.md').read_text())
    except (ValueError, KeyError, FileNotFoundError, subprocess.TimeoutExpired) as exc:
        print('ERROR: ' + str(exc), file=sys.stderr); return 1
    if args.check:
        if not OUTPUT.exists() or OUTPUT.read_bytes() != content.encode():
            print('Statement correspondence drift: ' + str(OUTPUT), file=sys.stderr); return 1
    else: OUTPUT.write_text(content)
    print(json.dumps(dict(entries=len(entries), formal_entries=sum(not e['prose'] for e in entries),
                          prose_claims=sum(e['prose'] for e in entries), declarations=len(types),
                          failed_checks=[], check=args.check)))
    return 0


if __name__ == '__main__': raise SystemExit(main())
