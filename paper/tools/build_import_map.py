#!/usr/bin/env python3
"""Pin W6 corpus sources and local DOI evidence; stdlib, archive-safe.

Line checks use the SHA256-matched frozen snapshot and its cited span, with
literal labels, names or authored excerpt fragments; never semantic guesses.
Current-file relocations are authored metadata, not generated semantic claims.
DOI statuses use local release metadata plus an optional authored verification
record. Default generation/checking uses bundled metadata, not sibling repos.
--live re-derives the bundle from siblings; --refresh-inputs explicitly updates it.
A reserved DOI is not evidence of publication. Registry
snapshot titles can precede current repository releases; doi_scope discloses that.
"""
from __future__ import annotations
import argparse
from collections import Counter
import csv
import hashlib
import io
import json
import os
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / 'paper/prewriting'
SIBLING_ROOT = Path(os.environ.get('SIXBIRDS_SIBLING_ROOT', '/home/repos'))
PAPERS = SIBLING_ROOT / 'six-birds-papers'
INPUTS = ROOT / 'paper/data/corpus_inputs.json'
# Repository identities verified from source links / corpus consciousness
# inventory, and matching titled source/release files; not filename guesses.
REPOS = {
    'P05': SIBLING_ROOT / 'six-birds-consciousness',
    'P07': SIBLING_ROOT / 'six-birds-quantum-os',
    'P14': SIBLING_ROOT / 'six-birds-born-repos/six-birds-route-transport',
    'P18': SIBLING_ROOT / 'six-birds-born-repos/six-birds-interference',
    'P30': SIBLING_ROOT / 'six-birds-meta-math',
    'P35': SIBLING_ROOT / 'six-birds-protocol-trap',
    'P50': SIBLING_ROOT / 'six-birds-confluence',
    'P53': SIBLING_ROOT / 'six-birds-time',
    'P57': SIBLING_ROOT / 'six-birds-agent',
}
KEYS = dict(zip(REPOS, [
    'Tsiokos2026AuditedClosureArchitecture', 'Tsiokos2026QuantumErrorCorrection',
    'Tsiokos2026HolonomyMemory', 'Tsiokos2026MarkingErasure',
    'Tsiokos2026FoundationsIV', 'Tsiokos2026ProtocolTrap',
    'Tsiokos2026FlattenStone', 'Tsiokos2026NotchStone', 'Tsiokos2026Agenthood']))
COLUMNS = ['statement_id', 'paper_id', 'source_file', 'source_lines', 'source_label',
           'statement_name', 'source_path', 'source_sha256', 'source_repo_commit',
           'literal_anchor_check', 'fixed_support', 'scope_note', 'citation_key', 'doi',
           'doi_status', 'doi_metadata_sources', 'doi_scope', 'doi_verification_date',
           'doi_verification_method', 'doi_publication_date',
           'corpus_snapshot_sha256', 'source_matches_snapshot', 'snapshot_path',
           'snapshot_sha256', 'current_lines', 'match', 'relocation_note',
           'source_metadata_path', 'source_provenance']


def read_csv(path):
    with path.open(newline='', encoding='utf-8') as stream:
        return list(csv.DictReader(stream))


def locate(filename):
    direct = PAPERS / filename
    if direct.is_file():
        return direct
    for base in [PAPERS, ROOT / 'cst-tt/corpus', ROOT / 'cst-tt/inputs/reference_surfaces']:
        found = sorted(base.rglob(filename))
        if found:
            hashes = {hashlib.sha256(p.read_bytes()).hexdigest() for p in found}
            if len(hashes) != 1:
                raise ValueError(f'Ambiguous source versions: {filename}')
            return found[0]
    raise ValueError(f'Source file not found: {filename}')


def git_commit(path):
    # Pin the last commit touching this source, so committing generated metadata
    # cannot cause perpetual drift for snapshots in this repository.
    result = subprocess.run(['git', '-C', str(path.parent), 'log', '-1', '--format=%H', '--', path.name],
                            capture_output=True, text=True)
    if result.returncode:
        return ''
    return result.stdout.strip()


def normalized(value):
    return ' '.join(value.casefold().split())


def literal_anchor_check(row, source, relocation=None):
    """Literal cited-content check ONLY within the frozen snapshot span.

    Names can be descriptive rather than literal source titles. In that case,
    test the authored relocation evidence's exact excerpt fragments, split at
    ellipses; require at least 16 characters and normalize only case/whitespace.
    No semantic match, TeX rewriting, or out-of-span relocation is inferred.
    """
    lines = source.splitlines()
    start, end = map(int, row['source_lines'].split('-'))
    if not 1 <= start <= end <= len(lines):
        return 'not_found'
    needles = [v for v in [row['source_label'], row['statement_name']] if v]
    if relocation:
        needles += [p.strip() for p in re.split(r'\s*\.\.\.\s*', relocation['evidence'])
                    if len(p.strip()) >= 16]
    block = normalized('\n'.join(lines[start - 1:end]))
    if any(normalized(n) in block for n in needles):
        return 'ok'
    return ('not_found' if row['source_label'] else
            'no_literal_anchor (unlabelled; content compared in import_relocation.csv)')


def snapshot_source(row, relocation, expected_hash):
    found = re.fullmatch(r'yes:\s+(.+?\.tex)(?:\s+\(.*\))?', relocation['snapshot_found'])
    if not found:
        raise ValueError(f'Snapshot path not disclosed: {row["statement_id"]}')
    # Authored relocation cells retain the original absolute provenance path.
    # Resolve its frozen-snapshot suffix inside this extraction, not that repo.
    prefix = 'cst-tt/inputs/reference_surfaces/'
    original = found[1]
    if prefix not in original:
        raise ValueError(f'Invalid snapshot path: {row["statement_id"]}: {original}')
    path = (ROOT / prefix / original.split(prefix, 1)[1]).resolve()
    base = (ROOT / 'cst-tt/inputs/reference_surfaces').resolve()
    if not path.is_relative_to(base) or not path.is_file() or path.name != row['source_file']:
        raise ValueError(f'Invalid snapshot path: {row["statement_id"]}: {path}')
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    if digest != expected_hash:
        raise ValueError(f'Snapshot SHA256 mismatch: {row["statement_id"]}')
    if relocation['snapshot_lines'] != row['source_lines']:
        raise ValueError(f'Snapshot line-range mismatch: {row["statement_id"]}')
    return path, digest


def braced_command(source, command):
    match = re.search(r'\\' + re.escape(command) + r'\s*\{', source)
    if not match:
        return ''
    start = match.end(); depth = 1
    for end in range(start, len(source)):
        if source[end] == '{': depth += 1
        if source[end] == '}': depth -= 1
        if depth == 0: return source[start:end]
    raise ValueError(f'Unclosed {command}')


def title_text(source):
    text = braced_command(source, 'title')
    text = re.sub(r'\\\\(?:\[[^]]*\])?', ' ', text)
    return ' '.join(text.split())


def doi_metadata(pid, source):
    repo = REPOS[pid]
    if not repo.is_dir():
        raise ValueError(f'Missing verified source repository: {repo}')
    current = re.search(r'\\newcommand\{\\paperdoi\}\{([^}]+)\}', source)
    own_dois = re.findall(r'10\.5281/zenodo\.\d+', source[:source.find('\\begin{document}')])
    preferred = current[1] if current else (own_dois[0] if own_dois else '')
    candidates = []
    # Only paper release records, including docs/paper and foundations_iv.
    for path in sorted(repo.rglob('zenodo*release.json')):
        if 'submission' not in path.parts or '.lake' in path.parts:
            continue
        record = json.loads(path.read_text())
        doi = record.get('doi') or record.get('reserved_doi') or record.get('doi_reservation', {}).get('identifier')
        if not doi:
            continue
        if preferred and doi != preferred:
            continue
        if pid == 'P30' and 'foundations_iv' not in path.parts:
            continue
        stage = record.get('stage', '')
        if stage == 'published' or record.get('published') is True:
            status = 'published'
        elif record.get('doi_reservation') or record.get('reserved_doi') or 'draft' in record.get('action', '').lower():
            status = 'reserved'
        else:
            raise ValueError(f'DOI status not disclosed: {path}')
        candidates.append((doi, status, path))
    # Cross-check any authored reservation note (without inferring publication).
    for path in sorted(repo.rglob('RESERVED_DOI.md')):
        if 'submission' not in path.parts:
            continue
        text = path.read_text()
        match = re.search(r'Reserved DOI:\s*(10\.5281/zenodo\.\d+)', text)
        if match and (not preferred or match[1] == preferred):
            candidates.append((match[1], 'reserved', path))
    values = {(d, s) for d, s, _ in candidates}
    if len(values) > 1:
        raise ValueError(f'Conflicting DOI evidence: {pid}: {values}')
    if not candidates:
        if preferred:
            raise ValueError(f'Source DOI has no verified status: {pid}: {preferred}')
        return '', 'none', '', 'No DOI/release record found for this corpus source in its verified repository or central manifest.'
    doi, status = next(iter(values))
    scope = 'Current source-version DOI; status is as recorded in local release metadata.'
    if pid == 'P05':
        scope = ('Reservation for the revised architecture successor in the source repository; '
                 'not a DOI identity claim for this historical audited-architecture snapshot. '
                 'Omitted from this snapshot BibTeX entry.')
    return doi, status, ';'.join(str(p) for _, _, p in candidates), scope


def input_text(data):
    return json.dumps(data, indent=2, sort_keys=True) + '\n'


def derive_inputs():
    """Explicit live acquisition of minimal metadata; no sibling writes."""
    registry = read_csv(ROOT / 'cst-tt/registries/FINAL_SBT_PROVENANCE.csv')
    manifest_path = PAPERS / 'manifest.json'
    manifest = json.loads(manifest_path.read_text())
    filenames = {r['source_file'] for r in registry}
    selected = [r for r in manifest if Path(r['output']).name in filenames]
    data = dict(schema_version='1.0', definition=(
        'Current-source metadata and SHA256 pins acquired with --live; source_path '
        'and origin_path are provenance, not archive dependencies. Full current '
        'papers are not bundled. Frozen cited sources remain under cst-tt/inputs/reference_surfaces.'),
        manifest=dict(origin_path=str(manifest_path),
                      sha256=hashlib.sha256(manifest_path.read_bytes()).hexdigest(), entries=selected),
        papers={})
    copies = {}
    for row in registry:
        pid = row['paper_id']
        if pid in data['papers']: continue
        path = locate(row['source_file']); source = path.read_text()
        doi, status, metadata, scope = doi_metadata(pid, source)
        records = []
        for name in filter(None, metadata.split(';')):
            origin = Path(name)
            target = Path('paper/data/corpus_metadata') / pid / origin.relative_to(REPOS[pid])
            content = origin.read_bytes(); copies[target] = content
            records.append(dict(origin_path=name, bundled_path=str(target),
                                sha256=hashlib.sha256(content).hexdigest()))
        data['papers'][pid] = dict(source_file=row['source_file'], source_path=str(path.resolve()),
            source_sha256=hashlib.sha256(path.read_bytes()).hexdigest(), source_repo_commit=git_commit(path),
            title_tex=braced_command(source, 'title'), author_tex=braced_command(source, 'author'),
            year=re.search(r'_(\d{4})_', row['source_file'])[1], doi=doi, doi_status=status,
            doi_scope=scope, doi_metadata=records)
    return data, copies


def bundled_inputs():
    data = json.loads(INPUTS.read_text())
    if data.get('schema_version') != '1.0' or set(data['papers']) != set(REPOS):
        raise ValueError('Invalid corpus input bundle')
    for pid, paper in data['papers'].items():
        if not re.fullmatch(r'[0-9a-f]{64}', paper['source_sha256']):
            raise ValueError('Invalid current-source SHA256: ' + pid)
        if paper['source_repo_commit'] and not re.fullmatch(r'[0-9a-f]{40}', paper['source_repo_commit']):
            raise ValueError('Invalid current-source commit: ' + pid)
        for metadata in paper['doi_metadata']:
            path = (ROOT / metadata['bundled_path']).resolve()
            if not path.is_relative_to(ROOT / 'paper/data/corpus_metadata'):
                raise ValueError('Metadata path outside corpus bundle')
            if hashlib.sha256(path.read_bytes()).hexdigest() != metadata['sha256']:
                raise ValueError('Corpus metadata SHA256 mismatch: ' + metadata['bundled_path'])
    return data


def publication_verifications():
    path = OUTPUT / 'corpus_doi_verification.json'
    if not path.exists(): return {}
    record = json.loads(path.read_text())
    if record.get('schema_version') != '1.0' or record.get('verified_by') not in {'agent_live', 'owner_reported'}:
        raise ValueError('Invalid DOI verification provenance')
    from datetime import date
    date.fromisoformat(record['verification_date'])
    if not record.get('method'): raise ValueError('Missing DOI verification method')
    rows = {}
    for item in record['records']:
        pid = item['paper_id']; doi = item['doi']
        if pid not in REPOS or pid in {'P05', 'P18'} or pid in rows:
            raise ValueError('Invalid/duplicate DOI verification paper: ' + pid)
        match = re.fullmatch(r'10\.5281/zenodo\.(\d+)', doi)
        if not match: raise ValueError('Invalid verified DOI: ' + doi)
        if item['doi_http_status'] != 302 or item['api_http_status'] != 200 or item['api_status'] != 'published':
            raise ValueError('Publication verification is not a published DOI/API response: ' + doi)
        if item['api_record_id'] != int(match[1]) or item['api_url'] != 'https://zenodo.org/api/records/' + match[1]:
            raise ValueError('Verified API record mismatch: ' + doi)
        date.fromisoformat(item['publication_date'])
        portable_path = str(path.relative_to(ROOT)) if path.is_relative_to(ROOT) else str(path)
        rows[pid] = dict(item, verification_date=record['verification_date'],
                         method=record['method'], verified_by=record['verified_by'], path=portable_path)
    return rows


def apply_publication_verification(pid, doi, title, status, metadata, scope, verifications):
    if pid not in verifications: return status, metadata, scope, '', '', ''
    item = verifications[pid]
    if item['doi'] != doi or normalized(item['title']) != normalized(title):
        raise ValueError('Verified DOI/title differs from the corpus source: ' + pid)
    method = item['verified_by'] + ': ' + item['method']
    note = 'Publication verified ' + item['verification_date'] + ' (' + method + ').'
    return ('published', metadata + ';' + item['path'],
            'Current source-version DOI. ' + note,
            item['verification_date'], method, item['publication_date'])


def generate(inputs=None):
    registry = read_csv(ROOT / 'cst-tt/registries/FINAL_SBT_PROVENANCE.csv')
    if len(registry) != 19 or len({r['statement_id'] for r in registry}) != 19:
        raise ValueError('Expected 19 distinct provenance rows')
    relocation_rows = read_csv(OUTPUT / 'import_relocation.csv')
    relocations = {r['statement_id']: r for r in relocation_rows}
    if len(relocations) != len(relocation_rows) or set(relocations) != {r['statement_id'] for r in registry}:
        raise ValueError('Relocation entries must cover every provenance row exactly once')
    inventory = {r['paper_id']: r for r in read_csv(ROOT / 'cst-tt/corpus/machine_index/paper_inventory.csv')}
    inputs = bundled_inputs() if inputs is None else inputs
    manifest = inputs['manifest']['entries']
    verifications = publication_verifications()
    outputs, bibliography, papers = [], [], {}
    for row in registry:
        pid = row['paper_id']
        if pid not in papers:
            pinned = inputs['papers'][pid]
            if pinned['source_file'] != row['source_file']:
                raise ValueError('Pinned source filename mismatch: ' + pid)
            path = Path(pinned['source_path'])
            doi, status, scope = (pinned[k] for k in ['doi', 'doi_status', 'doi_scope'])
            metadata = ';'.join(r['bundled_path'] for r in pinned['doi_metadata'])
            title = title_text('\\title{' + pinned['title_tex'] + '}')
            if not title: raise ValueError(f'Missing source title: {pid}')
            status, metadata, scope, verified_date, verified_method, publication_date = apply_publication_verification(
                pid, doi, title, status, metadata, scope, verifications)
            # Manifest is inspected for source/DOI metadata, never treated as a
            # publication assertion when it only lists export paths and titles.
            matches = [r for r in manifest if Path(r['output']).name == row['source_file']]
            for r in matches:
                if r.get('doi') and r['doi'] != doi:
                    raise ValueError(f'Manifest/release DOI mismatch: {pid}')
            digest = pinned['source_sha256']
            papers[pid] = dict(source_path=str(path), source_sha256=digest,
                source_repo_commit=pinned['source_repo_commit'], citation_key=KEYS[pid], doi=doi,
                doi_status=status, doi_metadata_sources=metadata, doi_scope=scope,
                doi_verification_date=verified_date, doi_verification_method=verified_method,
                doi_publication_date=publication_date,
                corpus_snapshot_sha256=inventory[pid]['sha256'],
                source_matches_snapshot='yes' if digest == inventory[pid]['sha256'] else 'no',
                source_metadata_path=str(INPUTS.relative_to(ROOT)),
                source_provenance='External current-source path/hash pinned in bundled metadata; frozen cited source is snapshot_path.')
            author = pinned['author_tex'].split('\\')[0].strip()
            # A bibliography identifier's year is not authority for a field.
            # The source filename and corpus inventory independently give 2026.
            year = pinned['year']
            fields = [('author', author), ('title', title), ('year', year)]
            if doi and pid != 'P05': fields.append(('doi', doi))
            bibliography.append('% ' + pid + ': ' + str(path) + '\n% DOI status: ' + status + '. ' + scope + '\n'
                + '@misc{' + KEYS[pid] + ',\n' + ',\n'.join('  ' + k + ' = {' + v + '}' for k, v in fields) + '\n}\n')
        values = {k: row[k] for k in COLUMNS if k in row}
        values.update(papers[pid])
        relocation = relocations[row['statement_id']]
        snapshot, digest = snapshot_source(row, relocation, inventory[pid]['sha256'])
        values.update(snapshot_path=str(snapshot.relative_to(ROOT)), snapshot_sha256=digest,
                      current_lines=relocation['current_lines'], match=relocation['match'],
                      relocation_note=relocation['note'])
        values['literal_anchor_check'] = literal_anchor_check(row, snapshot.read_text(), relocation)
        outputs.append(values)
    stream = io.StringIO(newline=''); writer = csv.DictWriter(stream, fieldnames=COLUMNS, lineterminator='\n')
    writer.writeheader(); writer.writerows(outputs)
    summary = {'rows': len(outputs), 'papers': len(papers),
        'literal_anchor_check': dict(Counter(r['literal_anchor_check'].split(':')[0] for r in outputs)),
        'doi_statuses': {pid: {'doi': r['doi'], 'status': r['doi_status']} for pid, r in papers.items()}}
    return {'sibling_import_map.csv': stream.getvalue(),
            'references_sixbirds.bib': '% Generated by paper/tools/build_import_map.py; offline local metadata and authored verification records.\n\n' + '\n'.join(bibliography)}, summary


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--live', action='store_true', help='Re-derive pinned metadata from sibling repositories (no network)')
    parser.add_argument('--refresh-inputs', action='store_true', help='With --live, explicitly replace the bundled metadata inputs')
    args = parser.parse_args()
    if args.refresh_inputs and (not args.live or args.check):
        parser.error('--refresh-inputs requires --live and cannot be combined with --check')
    try:
        if args.live:
            inputs, copies = derive_inputs()
            drift = not INPUTS.is_file() or INPUTS.read_text() != input_text(inputs)
            for path, content in copies.items():
                target = ROOT / path
                drift |= not target.is_file() or target.read_bytes() != content
            if args.refresh_inputs:
                for path, content in copies.items():
                    target = ROOT / path; target.parent.mkdir(parents=True, exist_ok=True); target.write_bytes(content)
                INPUTS.write_text(input_text(inputs))
            elif drift:
                raise ValueError('Live corpus inputs differ from bundle; review before --live --refresh-inputs')
        outputs, summary = generate()
    except (ValueError, OSError) as exc:
        print(str(exc), file=sys.stderr); return 1
    drift = [n for n, s in outputs.items() if not (OUTPUT / n).is_file() or (OUTPUT / n).read_bytes() != s.encode()]
    if args.check and drift:
        print('Import-map drift: ' + ', '.join(drift), file=sys.stderr); return 1
    if not args.check:
        for name, content in outputs.items(): (OUTPUT / name).write_text(content)
    print(json.dumps(summary, sort_keys=True)); return 0


if __name__ == '__main__':
    raise SystemExit(main())
