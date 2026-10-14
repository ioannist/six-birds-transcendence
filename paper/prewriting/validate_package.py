#!/usr/bin/env python3
"""Read-only W7 cross-file integrity checks; stdlib only, no Lean evaluation."""
from __future__ import annotations
from collections import Counter
import csv
from fnmatch import fnmatchcase
import json
from pathlib import Path
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
PRE = ROOT / 'paper/prewriting'
ROW_ID = re.compile(r'\b(?:TTH|TTN|TTD|TTF|TTS)-\d{2}\b')
CLAIM_ID = re.compile(r'(?<![A-Za-z0-9_-])(?:TTH|TTN|TTD|TTF|TTS|DEF|HYP|POST|ART|SCOPE|JOINT)-(?:\*|[A-Z0-9]+(?:-[A-Z0-9]+)*(?:-\*)?)(?![A-Za-z0-9_-])')


def rows(path):
    with path.open(newline='', encoding='utf-8') as stream:
        return list(csv.DictReader(stream))


def require(condition, message, errors):
    if not condition: errors.append(message)


def unique(records, field, filename, errors):
    values = [r[field] for r in records]
    require(all(values), f'{filename}: blank {field}', errors)
    duplicate = sorted(k for k, n in Counter(values).items() if n > 1)
    require(not duplicate, f'{filename}: duplicate {field}: {duplicate}', errors)
    return set(values)


def bib_keys(path, errors):
    # BibTeX comments are not entries; recognize all entry types, not only four.
    text = re.sub(r'(?m)^\s*%.*$', '', path.read_text())
    names = re.findall(r'(?im)^\s*@(?!(?:comment|string|preamble)\b)[a-z]+\s*[\{(]\s*([^,\s]+)\s*,', text)
    duplicate = sorted(k for k, n in Counter(names).items() if n > 1)
    require(not duplicate, f'{path.name}: duplicate citation keys: {duplicate}', errors)
    return set(names)


def destination_slots(text):
    match = re.search(r'^## Destination slots\s*\n(.*?)(?=^## |\Z)', text, re.M | re.S)
    if not match: raise ValueError('ledger_conventions.md: Destination slots table missing')
    slots = set(re.findall(r'^\|\s*`([^`]+)`\s*\|', match[1], re.M))
    if not slots: raise ValueError('ledger_conventions.md: no destination slots found')
    return slots


def destinations(records, identity, filename, slots, errors):
    for row in records:
        for item in row['destination'].split(';'):
            destination = item.strip()
            slot = destination.removeprefix('at-result:')
            require(slot in slots, f'{filename}:{row[identity]}: unknown destination {destination!r}', errors)


def outline_references(text, ids, errors):
    resolved = set()
    # Expand explicit same-family ID ranges, rather than ignoring the far end.
    range_pattern = re.compile(r'\b((?:TTH|TTN|TTD|TTF|TTS)-)(\d{2})\s*[–—-]\s*(?:\1)?(\d{2})\b')
    for number, line in enumerate(text.splitlines(), 1):
        for match in range_pattern.finditer(line):
            start, end = int(match[2]), int(match[3])
            require(start <= end, f'outline.md:{number}: reversed claim range {match[0]}', errors)
            for value in range(start, end + 1):
                name = match[1] + f'{value:02d}'
                require(name in ids, f'outline.md:{number}: unknown claim ID {name}', errors)
                if name in ids: resolved.add(name)
        for match in CLAIM_ID.finditer(range_pattern.sub('', line)):
            name = match[0]
            if '*' in name:
                matches = {i for i in ids if fnmatchcase(i, name)}
                require(bool(matches), f'outline.md:{number}: unmatched claim family {name}', errors)
                resolved.update(matches)
            else:
                require(name in ids, f'outline.md:{number}: unknown claim ID {name}', errors)
                if name in ids: resolved.add(name)
    return resolved


def snapshot_references(text, keys, ledger_columns, errors):
    # Inspect inline-code key references throughout the plan, including prose.
    # Paths and named authored ledger columns are not snapshot keys.
    references = set()
    for number, line in enumerate(text.splitlines(), 1):
        for token in re.findall(r'`([^`]+)`', line):
            if token in ledger_columns or not re.fullmatch(r'[a-z][a-z0-9_]*(?:\*)?', token):
                continue
            references.add(token)
            if '*' in token:
                require(any(fnmatchcase(k, token) for k in keys),
                        f'figure_table_plan.md:{number}: unmatched snapshot key pattern {token}', errors)
            else:
                require(token in keys, f'figure_table_plan.md:{number}: unknown snapshot key {token}', errors)
    return references


def check_main_placement(claims, outline, errors):
    resolved = outline_references(outline, {r['claim_id'] for r in claims}, errors)
    for claim in claims:
        if claim['role'] == 'main':
            require(claim['claim_id'] in resolved,
                    f'outline.md: main claim not placed: {claim["claim_id"]}', errors)
    return resolved


def check_source_rows(claims, registry, errors):
    # Split semicolons outside the disclosed parenthetical supplementary source.
    allowed = {'all', '(G26; no row)', 'CLAIM_LANE_REGISTRY'}
    for claim in claims:
        for token in re.split(r';(?![^()]*\))', claim['source_rows']):
            token = token.strip()
            if token in allowed or re.fullmatch(r'AS-\d{2}', token):
                continue
            found = ROW_ID.findall(token)
            for rid in found:
                require(rid in registry,
                        f'claim_ledger.csv:{claim["claim_id"]}: unknown source registry row {rid}', errors)
            if not ROW_ID.fullmatch(token):
                require(False, f'claim_ledger.csv:{claim["claim_id"]}: unsupported source_rows token {token!r}', errors)


def check_taxonomy_placement(claims, taxonomy, errors):
    indexed = {r['claim_id']: r for r in claims}
    for row in taxonomy:
        claim = indexed.get(row['claim_id'])
        if claim:
            require(row['paper_use'] == claim['role'],
                    f'claim_taxonomy.csv:{row["claim_id"]}: paper_use={row["paper_use"]!r}, ledger role={claim["role"]!r}', errors)


def validate(root=ROOT):
    pre = root / 'paper/prewriting'; errors = []
    claims = rows(pre / 'claim_ledger.csv')
    taxonomy = rows(pre / 'claim_taxonomy.csv')
    registry_rows = rows(root / 'cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv')
    registry = {r['theorem_id']: r for r in registry_rows}
    ids = unique(claims, 'claim_id', 'claim_ledger.csv', errors)
    tax_ids = unique(taxonomy, 'claim_id', 'claim_taxonomy.csv', errors)
    require(ids == tax_ids,
            f'claim taxonomy/ledger mismatch: ledger-only={sorted(ids-tax_ids)}, taxonomy-only={sorted(tax_ids-ids)}', errors)
    check_taxonomy_placement(claims, taxonomy, errors)
    check_source_rows(claims, registry, errors)
    covered = {rid for c in claims for rid in ROW_ID.findall(c['source_rows']) if rid in registry}
    require(covered == set(registry), f'Registry rows not covered: {sorted(set(registry)-covered)}', errors)
    slots = destination_slots((pre / 'ledger_conventions.md').read_text())
    destinations(claims, 'claim_id', 'claim_ledger.csv', slots, errors)
    nonclaims = rows(pre / 'nonclaim_survival.csv')
    destinations(nonclaims, 'nc_id', 'nonclaim_survival.csv', slots, errors)
    # Compare direct registry claims and suffixed registry claims. A definition
    # or scope row citing results in source_rows is not itself a registry result.
    for claim in claims:
        match = ROW_ID.match(claim['claim_id'])
        if match and match[0] in registry:
            expected = registry[match[0]]['status_09']
            require(claim['status_09'] == expected,
                    f'claim_ledger.csv:{claim["claim_id"]}: status_09={claim["status_09"]!r}, registry {match[0]}={expected!r}', errors)
    citation_ids = unique(rows(pre / 'citation_ledger.csv'), 'citation_key', 'citation_ledger.csv', errors)
    cross_ids = unique(rows(pre / 'literature_claim_crosswalk.csv'), 'citation_key', 'literature_claim_crosswalk.csv', errors)
    core_ids = bib_keys(pre / 'references_core.bib', errors)
    for filename, found in [('literature_claim_crosswalk.csv', cross_ids), ('references_core.bib', core_ids)]:
        require(found == citation_ids,
                f'{filename}/citation-ledger mismatch: file-only={sorted(found-citation_ids)}, ledger-only={sorted(citation_ids-found)}', errors)
    imports = rows(pre / 'sibling_import_map.csv')
    import_keys = {r['citation_key'] for r in imports}
    corpus_keys = bib_keys(pre / 'references_sixbirds.bib', errors)
    require(import_keys == corpus_keys,
            f'references_sixbirds.bib/import-map mismatch: bib-only={sorted(corpus_keys-import_keys)}, map-only={sorted(import_keys-corpus_keys)}', errors)
    placed = check_main_placement(claims, (pre / 'outline.md').read_text(), errors)
    snapshot = json.loads((root / 'paper/data/current_results.json').read_text())
    keys = {r['key'] for r in snapshot['entries'] + snapshot.get('schemas', [])}
    refs = snapshot_references((pre / 'figure_table_plan.md').read_text(), keys,
                               set(claims[0]) if claims else set(), errors)
    counts = dict(claims=len(claims), taxonomy=len(taxonomy), registry_rows=len(registry),
                  main_claims=sum(r['role']=='main' for r in claims),
                  placed_main_claims=sum(r['role']=='main' and r['claim_id'] in placed for r in claims),
                  covered_registry_rows=len(covered), nonclaims=len(nonclaims),
                  core_citations=len(citation_ids), corpus_citations=len(import_keys),
                  snapshot_references=len(refs), errors=len(errors))
    return errors, counts


def main():
    try: errors, counts = validate()
    except (OSError, ValueError, KeyError) as exc:
        print(f'ERROR: {exc}', file=sys.stderr); return 1
    for error in errors: print('ERROR: ' + error, file=sys.stderr)
    print(('FAIL: ' if errors else 'PASS: ') + json.dumps(counts, sort_keys=True))
    return 1 if errors else 0


if __name__ == '__main__':
    raise SystemExit(main())
