"""W3 evidence metadata gates; unresolved headlines are fatal."""
from __future__ import annotations

import csv
import json
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / 'paper/prewriting'


def rows(path):
    with path.open(newline='', encoding='utf-8') as stream:
        return list(csv.DictReader(stream))


def test_check_passes():
    run = subprocess.run([sys.executable, str(ROOT / 'paper/tools/build_evidence_map.py'), '--check'],
                         cwd=ROOT, capture_output=True, text=True)
    assert run.returncode == 0, (run.stdout + run.stderr)[-4000:]


def test_every_registry_row_is_mapped():
    registry = rows(ROOT / 'cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv')
    matrix = rows(OUTPUT / 'evidence_matrix.csv')
    assert len(matrix) == len(registry) == 39
    assert {r['row_id'] for r in matrix} == {r['theorem_id'] for r in registry}
    by_id = {r['theorem_id']: r for r in registry}
    inventory = {r['row_id']: r for r in json.loads((ROOT / 'lean/row_inventory.json').read_text())['rows']}
    for r in matrix:
        assert r['status_09'] == by_id[r['row_id']]['status_09']
        assert r['ceiling_09'] == by_id[r['row_id']]['ceiling_09']
        assert int(r['inventory_declaration_count']) == len(inventory[r['row_id']]['declarations'])


def test_every_lean_bearing_ledger_claim_is_mapped():
    ledger = rows(OUTPUT / 'claim_ledger.csv')
    mapped = rows(OUTPUT / 'lean_declaration_map.csv')
    expected = {r['claim_id'] for r in ledger if 'CSTTT.' in r['evidence']}
    assert len(mapped) == len(expected)
    assert {r['claim_id'] for r in mapped} == expected
    authored = {r['claim_id']: r['not_mechanized'] for r in rows(OUTPUT / 'not_mechanized.csv')}
    assert all(r['not_mechanized'] == authored.get(r['claim_id'], '') for r in mapped)


def test_no_unresolved_names():
    actual = [n for r in rows(OUTPUT / 'lean_declaration_map.csv')
              for n in r['headline_declarations'].split(';') if n.startswith('UNRESOLVED:')]
    assert not actual, actual


def load_generator():
    import importlib.util
    spec = importlib.util.spec_from_file_location('w3_evidence_map', ROOT / 'paper/tools/build_evidence_map.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_missing_in_memory_headline_fails_even_without_drift(tmp_path, monkeypatch):
    module = load_generator()
    original_read = module.read_csv
    ledger_path = ROOT / 'paper/prewriting/claim_ledger.csv'
    ledger = original_read(ledger_path)
    bad = dict(ledger[0], claim_id='NEGATIVE-TEST', evidence='CSTTT.DoesNotExist')
    authored_path = OUTPUT / 'not_mechanized.csv'
    def injected_read(path):
        if path == ledger_path: return [*ledger, bad]
        if path == authored_path: return [{'claim_id': bad['claim_id'], 'not_mechanized': 'Authored scope; preserve verbatim.'}]
        return original_read(path)
    monkeypatch.setattr(module, 'read_csv', injected_read)
    generated, summary = module.generate('2026-10-13')
    assert summary['unresolved_names'] == ['CSTTT.DoesNotExist']
    import io
    mapped = list(csv.DictReader(io.StringIO(generated['lean_declaration_map.csv'])))
    assert next(r for r in mapped if r['claim_id'] == bad['claim_id'])['not_mechanized'] == 'Authored scope; preserve verbatim.'
    for name, content in generated.items():
        (tmp_path / name).write_text(content)
    monkeypatch.setattr(module, 'OUTPUT', tmp_path)
    monkeypatch.setattr(module, 'generate', lambda _: (generated, summary))
    monkeypatch.setattr(sys, 'argv', ['build_evidence_map.py', '--check'])
    assert module.main() == 1


def test_inventory_and_supplemental_flags():
    module = load_generator()
    ledger = {r['claim_id']: r for r in rows(OUTPUT / 'claim_ledger.csv')}
    for row in rows(OUTPUT / 'lean_declaration_map.csv'):
        meta = module.headline_metadata(ledger[row['claim_id']])
        assert row['headline_declarations'].split(';') == [n for n, _ in meta]
        assert row['in_inventory'].split(';') == ['no' if supplemental else 'yes' for _, supplemental in meta]


def test_import_closure():
    result = load_generator().check_import_closure()
    assert result['external_roots'] == ['Init', 'Lean', 'Std']
    assert result['hiddenness_sources']


def test_axioms_and_artifact_paths():
    trusted = {s.strip() for s in (ROOT / 'lean/trust_base.txt').read_text().splitlines()
               if s.strip() and not s.lstrip().startswith('#')}
    for r in rows(OUTPUT / 'lean_declaration_map.csv'):
        names = {n for n in r['headline_declarations'].split(';') if not n.startswith('UNRESOLVED:')}
        axioms = json.loads(r['declaration_axioms'])
        assert set(axioms) == names
        assert all(set(values) <= trusted for values in axioms.values())
        for path in r['lean_modules'].split(';'):
            if path:
                assert (ROOT / path).is_file()
    for filename in ['lean_declaration_map.csv', 'evidence_matrix.csv']:
        for r in rows(OUTPUT / filename):
            for key in ['model_files', 'transcription_scripts']:
                for path in r[key].split(';'):
                    if path:
                        assert (ROOT / path).is_file()
                        if key == 'transcription_scripts':
                            assert path.startswith('scripts/check_') and path.endswith('.py')


def test_check_reports_drift_without_overwriting(tmp_path, monkeypatch, capsys):
    # Exercise the CLI comparison with probe-independent deterministic fixtures.
    import importlib.util
    spec = importlib.util.spec_from_file_location('w3_evidence_map', ROOT / 'paper/tools/build_evidence_map.py')
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    expected = {name: (OUTPUT / name).read_text() for name in
                ['lean_declaration_map.csv', 'evidence_matrix.csv', 'lean_traceability.md']}
    for name, content in expected.items():
        (tmp_path / name).write_text(content)
    target = tmp_path / 'evidence_matrix.csv'
    target.write_text(expected[target.name] + '\n')
    changed = target.read_bytes()
    monkeypatch.setattr(module, 'OUTPUT', tmp_path)
    monkeypatch.setattr(module, 'generate', lambda _: (expected, {'untrusted_axioms': []}))
    monkeypatch.setattr(sys, 'argv', ['build_evidence_map.py', '--check', '--as-of', '2026-10-13'])
    assert module.main() == 1
    assert 'evidence_matrix.csv' in capsys.readouterr().err
    assert target.read_bytes() == changed
