"""Read-only prewriting integrity wrapper and negative cross-reference cases."""
import importlib.util
from pathlib import Path
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
VALIDATOR = ROOT / 'paper/prewriting/validate_package.py'


@pytest.fixture
def validator():
    spec = importlib.util.spec_from_file_location('w7_package', VALIDATOR)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_current_package_is_consistent():
    result = subprocess.run([sys.executable, str(VALIDATOR)], capture_output=True, text=True, cwd=ROOT)
    assert result.returncode == 0, result.stdout + result.stderr


def test_unknown_claim_and_ranges_are_rejected(validator):
    errors = []
    validator.outline_references('TTN-01–03; DEF-MISSING; HYP-*', {'TTN-01', 'TTN-03', 'HYP-FELT'}, errors)
    assert len(errors) == 2
    assert any('TTN-02' in e for e in errors)
    assert any('DEF-MISSING' in e for e in errors)


def test_missing_snapshot_key_is_rejected(validator):
    errors = []
    text = '| ID | Data |\n|---|---|\n| F1 | `unknown_key`, `pos04_*`, `claim_ledger.csv`, `condition_grades` |\nAdditional value: `outside_missing`.'
    refs = validator.snapshot_references(text, {'pos04_c3_trajectory'}, {'condition_grades'}, errors)
    assert refs == {'unknown_key', 'pos04_*', 'outside_missing'}
    assert len(errors) == 2 and 'unknown_key' in errors[0] and 'outside_missing' in errors[1]


def test_destination_vocabulary_is_read_and_at_result_checked(validator):
    slots = validator.destination_slots('## Destination slots\n| Slot | Content |\n| `strict` | Strict |\n## Later\n')
    errors = []
    validator.destinations([{'claim_id': 'A', 'destination': 'strict;at-result:strict;at-result:missing'}],
                           'claim_id', 'ledger.csv', slots, errors)
    assert len(errors) == 1 and 'at-result:missing' in errors[0]


def test_missing_main_claim_placement_in_memory(validator):
    import re
    pre = ROOT / 'paper/prewriting'
    claims = validator.rows(pre / 'claim_ledger.csv')
    outline = re.sub(r'\bTTN-02\b', '', (pre / 'outline.md').read_text())
    assert 'TTN-02' not in outline
    errors = []
    validator.check_main_placement(claims, outline, errors)
    assert any('main claim not placed: TTN-02' in e for e in errors)


def test_unknown_source_registry_row_in_memory(validator):
    claims = validator.rows(ROOT / 'paper/prewriting/claim_ledger.csv')
    registry = {r['theorem_id']: r for r in validator.rows(ROOT / 'cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv')}
    claims[0]['source_rows'] += ';TTH-99'
    errors = []
    validator.check_source_rows(claims, registry, errors)
    assert len(errors) == 1 and 'unknown source registry row TTH-99' in errors[0]


def test_taxonomy_role_mutation_in_memory(validator):
    pre = ROOT / 'paper/prewriting'
    claims = validator.rows(pre / 'claim_ledger.csv')
    taxonomy = validator.rows(pre / 'claim_taxonomy.csv')
    target = next(r for r in taxonomy if r['claim_id'] == 'DEF-FINITE')
    target['paper_use'] = 'appendix'
    errors = []
    validator.check_taxonomy_placement(claims, taxonomy, errors)
    assert len(errors) == 1 and 'DEF-FINITE' in errors[0] and 'paper_use' in errors[0]


def test_outline_families_and_ranges_resolve_every_member(validator):
    ids = {'HYP-A','HYP-B','POST-A','POST-B','TTN-01','TTN-02','TTN-03'}
    errors = []
    assert validator.outline_references('HYP-*; POST-*; TTN-01–03', ids, errors) == ids
    assert not errors


def test_disclosed_nonrow_source_tokens_are_allowed(validator):
    errors = []
    validator.check_source_rows([{'claim_id':'META', 'source_rows':'AS-01;all;(G26; no row);CLAIM_LANE_REGISTRY'}], {}, errors)
    assert not errors
