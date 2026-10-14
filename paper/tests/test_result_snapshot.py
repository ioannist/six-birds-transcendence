"""W4 snapshot contracts; one fresh Lean export is shared across the tests."""
from __future__ import annotations

import csv
from fractions import Fraction
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

import jsonschema
import pytest

ROOT = Path(__file__).resolve().parents[2]
EXPORTER = ROOT/'paper/tools/export_results.py'
DATA = ROOT/'paper/data'


@pytest.fixture(scope='session')
def exporter():
    spec = importlib.util.spec_from_file_location('w4_exporter',EXPORTER)
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


@pytest.fixture(scope='session')
def snapshot():
    return json.loads((DATA/'current_results.json').read_text(encoding='utf-8'))


@pytest.fixture(scope='session')
def fresh_check():
    result = subprocess.run([sys.executable,str(EXPORTER),'--check'],cwd=ROOT,
                            text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,
                            timeout=3200)
    assert result.returncode==0,result.stdout[-3000:]
    return result


def test_schema_validity(snapshot):
    schema = json.loads((DATA/'current_results.schema.json').read_text(encoding='utf-8'))
    jsonschema.Draft202012Validator.check_schema(schema)
    validator = jsonschema.Draft202012Validator(schema)
    errors = list(validator.iter_errors(snapshot))
    assert not errors,[(list(e.path),e.message[:220]) for e in errors]


def test_schema_rejects_unknown_fields(snapshot):
    schema = json.loads((DATA/'current_results.schema.json').read_text(encoding='utf-8'))
    changed = dict(snapshot,untracked_value='unsupported')
    assert not jsonschema.Draft202012Validator(schema).is_valid(changed)
    changed = json.loads(json.dumps(snapshot))
    changed['entries'][0]['untracked_value']='unsupported'
    assert not jsonschema.Draft202012Validator(schema).is_valid(changed)


def test_check_passes(fresh_check):
    assert json.loads(fresh_check.stdout)['check'] is True


def test_claim_ids_exist(snapshot):
    with (ROOT/'paper/prewriting/claim_ledger.csv').open(newline='',encoding='utf-8') as stream:
        claims = {row['claim_id'] for row in csv.DictReader(stream)}
    assert {e['claim_id'] for e in snapshot['entries']}<=claims
    assert {e['claim_id'] for e in snapshot['schemas']}<=claims


def test_every_pin_resolves_with_standard_axioms(snapshot,exporter,fresh_check):
    names = sorted({e['pinned_by'] for e in snapshot['entries']+snapshot['schemas']}|
                   {n for e in snapshot['entries'] for n in e['pinning']['bridge_theorems']})
    log = (ROOT/'lean/.validate-logs/W4-extraction-and-axioms.log').read_text(encoding='utf-8')
    results = exporter.parse_probe(log,names,exporter.STANDARD_AXIOMS)
    for name in names:
        item = results[name]
        assert item['resolved'],(name,item['errors'])
        assert item['kind']=='theorem',name
        assert item['axiom_reported'] and not item['untrusted_axioms'],name
        for entry in snapshot['entries']+snapshot['schemas']:
            if entry['pinned_by']==name:
                assert entry.get('pinning',entry)['axioms']==item['axioms']
        for entry in snapshot['entries']:
            if name in entry['pinning']['bridge_theorems']:
                assert entry['pinning']['bridge_theorems'][name]==item['axioms']


def test_canonical_exact_values(snapshot,exporter):
    for e in snapshot['entries']:
        exporter.canonical_value(e['value_type'],e['value'])
        parts = json.loads(e['value']) if e['value_type'].endswith('_list') else [e['value']]
        for part in parts:
            assert part in e['pinning']['checked_statement'],e['key']
            if '/' in part:
                q = Fraction(part)
                assert part==f'{q.numerator}/{q.denominator}'
                assert q.denominator>0


def test_unique_keys_and_diagnostic_separation(snapshot,exporter):
    entries = {e['key'] for e in snapshot['entries']}
    diagnostics = {e['key'] for e in snapshot['candidate_findings']}
    assert len(entries)==len(snapshot['entries'])
    assert not entries & diagnostics
    assert entries=={s['key'] for s in exporter.specs()}
    assert diagnostics=={s['key'] for s in exporter.candidate_specs()}
    assert all(e['disposition']=='not_exported_missing_numeric_pin'
               for e in snapshot['candidate_findings'])


def test_protocol_evaluation_path_is_disclosed(snapshot, exporter):
    by_key = {e['key']: e for e in snapshot['entries']}
    expected = {s['key']: s['value_from'] for s in exporter.specs() if 'value_from' in s}
    derived = {e['key']: e['evaluation_source_key'] for e in snapshot['entries']
               if e['extraction'] == 'evaluated_via_protocol'}
    assert derived == expected
    assert not any(e['extraction'] == 'pinned_only' for e in snapshot['entries'])
    for key, origin in derived.items():
        entry, source = by_key[key], by_key[origin]
        assert source['extraction'] == 'evaluated'
        assert entry['value'] == source['value']
        assert entry['computed_by'] == source['computed_by']
        assert source['pinned_by'] in entry['pinning']['bridge_theorems']
        assert 'holonomyReadout' in entry['pinning']['checked_statement']
        assert 'some' in entry['pinning']['checked_statement']


def test_check_detects_byte_drift(snapshot,exporter,monkeypatch,tmp_path,capsys):
    monkeypatch.setattr(exporter,'DATA',tmp_path)
    monkeypatch.setattr(exporter,'build_snapshot',lambda:snapshot)
    monkeypatch.setattr(sys,'argv',[str(EXPORTER),'--check'])
    target = tmp_path/'current_results.json'
    target.write_text(exporter.render_snapshot(snapshot)+'\n',encoding='utf-8')
    assert exporter.main()==1
    assert 'drift' in capsys.readouterr().err
    target.write_text(exporter.render_snapshot(snapshot),encoding='utf-8')
    assert exporter.main()==0


@pytest.mark.parametrize('value',['2/4','1/-2','1/0','01/2','-0/1'])
def test_bad_rationals_are_rejected(exporter,value):
    with pytest.raises((ValueError,ZeroDivisionError)):
        exporter.canonical_value('rational',value)


def test_paper_support_pins_are_not_registry_evidence(snapshot):
    inventory = json.loads((ROOT/'lean/row_inventory.json').read_text())
    registry_names = {name for row in inventory['rows'] for name in row['declarations']}
    support = [e for e in snapshot['entries']
               if e['pinned_by'].startswith('CSTTT.PaperSupport.')]
    assert {e['key'] for e in support} == {
        'pos04_tagged_ambient_states', 'pos04_tagged_lethal_states',
        'pos04_c1_epsilon', 'g7_native_factor_states'}
    assert all(e['pinned_by'] not in registry_names for e in support)
    assert all(e['extraction'] == 'evaluated' for e in support)
