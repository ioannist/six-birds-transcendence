"""W6 source identity, exact registry transcription, and drift gates."""
import csv
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / 'paper/prewriting'


def rows(path):
    with path.open(newline='', encoding='utf-8') as stream:
        return list(csv.DictReader(stream))


def load_generator():
    spec = importlib.util.spec_from_file_location('w6_import_map', ROOT / 'paper/tools/build_import_map.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_check_passes():
    result = subprocess.run([sys.executable, str(ROOT / 'paper/tools/build_import_map.py'), '--check'],
                            capture_output=True, text=True, cwd=ROOT)
    assert result.returncode == 0, (result.stdout + result.stderr)[-4000:]


def test_every_row_has_an_existing_hashed_source_and_exact_scope():
    registry = rows(ROOT / 'cst-tt/registries/FINAL_SBT_PROVENANCE.csv')
    mapped = rows(OUTPUT / 'sibling_import_map.csv')
    assert len(mapped) == len(registry) == 19
    indexed = {r['statement_id']: r for r in registry}
    assert {r['statement_id'] for r in mapped} == set(indexed)
    module = load_generator()
    relocation = {r['statement_id']: r for r in rows(OUTPUT / 'import_relocation.csv')}
    inventory = {r['paper_id']: r for r in rows(ROOT / 'cst-tt/corpus/machine_index/paper_inventory.csv')}
    assert set(relocation) == set(indexed)
    for row in mapped:
        # The current source is external provenance, not promised archive content.
        # Its metadata/hash is pinned; the actual cited source is bundled below.
        metadata_path = ROOT / row['source_metadata_path']
        assert metadata_path.is_file()
        pinned = json.loads(metadata_path.read_text())['papers'][row['paper_id']]
        for field in ['source_path', 'source_sha256', 'source_repo_commit']:
            assert row[field] == pinned[field]
        for field in ['paper_id', 'source_file', 'source_lines', 'source_label', 'statement_name', 'fixed_support', 'scope_note']:
            assert row[field] == indexed[row['statement_id']][field]
        snapshot = ROOT / row['snapshot_path']
        assert snapshot.is_file() and snapshot.is_relative_to(ROOT / 'cst-tt/inputs/reference_surfaces')
        assert row['snapshot_sha256'] == hashlib.sha256(snapshot.read_bytes()).hexdigest()
        assert row['snapshot_sha256'] == inventory[row['paper_id']]['sha256'] == row['corpus_snapshot_sha256']
        authored = relocation[row['statement_id']]
        assert row['current_lines'] == authored['current_lines']
        assert row['match'] == authored['match']
        assert row['relocation_note'] == authored['note']
        assert row['literal_anchor_check'] == module.literal_anchor_check(row, snapshot.read_text(), authored)
        assert row['doi_status'] in {'published', 'reserved', 'none'}
        assert bool(row['doi']) == (row['doi_status'] != 'none')
        for metadata in row['doi_metadata_sources'].split(';'):
            if metadata: assert (ROOT / metadata).is_file()


def test_single_citation_key_and_doi_per_paper():
    keys = {}
    bib = (OUTPUT / 'references_sixbirds.bib').read_text()
    for row in rows(OUTPUT / 'sibling_import_map.csv'):
        triple = row['citation_key'], row['doi'], row['doi_status']
        assert keys.setdefault(row['paper_id'], triple) == triple
        assert row['citation_key'].startswith('Tsiokos2026')
    assert len(keys) == 9
    assert len({v[0] for v in keys.values()}) == 9
    for key, _, _ in keys.values(): assert bib.count('@misc{' + key + ',') == 1


def test_literal_anchor_check_does_not_guess_paraphrases():
    module = load_generator()
    row = {'source_lines': '1-1', 'source_label': 'thm:exact', 'statement_name': 'Exact title'}
    assert module.literal_anchor_check(row, r'\label{thm:exact}') == 'ok'
    assert module.literal_anchor_check(row, 'unrelated\nExact title') == 'not_found'
    assert module.literal_anchor_check(row, 'A vaguely similar claim') == 'not_found'
    excerpt = {'evidence': 'Unrelated current wording ... Exact snapshot excerpt.'}
    assert module.literal_anchor_check(row, 'Exact snapshot excerpt.', excerpt) == 'ok'
    assert module.literal_anchor_check(row, 'unrelated\nExact snapshot excerpt.', excerpt) == 'not_found'


def test_drift_detection_never_overwrites(tmp_path, monkeypatch, capsys):
    module = load_generator()
    outputs = {name: (OUTPUT / name).read_text() for name in ['sibling_import_map.csv', 'references_sixbirds.bib']}
    for name, content in outputs.items(): (tmp_path / name).write_text(content)
    target = tmp_path / 'references_sixbirds.bib'
    target.write_text(outputs[target.name] + '\n')
    before = target.read_bytes()
    monkeypatch.setattr(module, 'OUTPUT', tmp_path)
    monkeypatch.setattr(module, 'generate', lambda: (outputs, {}))
    monkeypatch.setattr(sys, 'argv', ['build_import_map.py', '--check'])
    assert module.main() == 1
    assert target.name in capsys.readouterr().err
    assert target.read_bytes() == before


def test_unlabelled_failed_anchor_is_preserved():
    module = load_generator()
    row = {'source_lines': '1-1', 'source_label': '', 'statement_name': 'Descriptive title'}
    assert module.literal_anchor_check(row, 'Different snapshot text') == (
        'no_literal_anchor (unlabelled; content compared in import_relocation.csv)')
    for record in rows(OUTPUT / 'sibling_import_map.csv'):
        assert 'line_check' not in record
        if not record['source_label'] and record['literal_anchor_check'] != 'ok':
            assert record['literal_anchor_check'].startswith('no_literal_anchor (unlabelled;')


def test_default_generation_uses_no_siblings_or_git(monkeypatch):
    module = load_generator()
    for name in ['locate', 'doi_metadata', 'git_commit', 'derive_inputs']:
        monkeypatch.setattr(module, name, lambda *a, **k: (_ for _ in ()).throw(AssertionError('live dependency')))
    monkeypatch.setattr(module, 'PAPERS', Path('/does-not-exist/six-birds-papers'))
    outputs, _ = module.generate()
    for name, content in outputs.items(): assert (OUTPUT / name).read_text() == content


def test_snapshot_absolute_provenance_resolves_inside_extraction():
    module = load_generator()
    registry = rows(ROOT / 'cst-tt/registries/FINAL_SBT_PROVENANCE.csv')
    relocations = {r['statement_id']: r for r in rows(OUTPUT / 'import_relocation.csv')}
    inventory = {r['paper_id']: r for r in rows(ROOT / 'cst-tt/corpus/machine_index/paper_inventory.csv')}
    for row in registry:
        authored = dict(relocations[row['statement_id']])
        authored['snapshot_found'] = authored['snapshot_found'].replace('/home/repos/six-birds-transcendence/', '/absent/original-repo/')
        path, _ = module.snapshot_source(row, authored, inventory[row['paper_id']]['sha256'])
        assert path.is_relative_to(ROOT)


def test_bundled_metadata_hash_drift_is_rejected(tmp_path, monkeypatch):
    module = load_generator(); data = module.bundled_inputs()
    first = next(p for p in data['papers'].values() if p['doi_metadata'])['doi_metadata'][0]
    first['sha256'] = '0' * 64
    path = tmp_path / 'inputs.json'; path.write_text(json.dumps(data))
    monkeypatch.setattr(module, 'INPUTS', path)
    import pytest
    with pytest.raises(ValueError, match='metadata SHA256 mismatch'): module.bundled_inputs()
