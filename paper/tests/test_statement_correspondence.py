"""W18 statement extraction, fresh Lean correspondence, and drift protection."""
import csv
import importlib.util
from pathlib import Path
import re
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
TOOLS = ROOT / 'paper/tools'


def load():
    if str(TOOLS) not in sys.path: sys.path.insert(0, str(TOOLS))
    spec = importlib.util.spec_from_file_location('w18_correspondence', TOOLS / 'build_correspondence.py')
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


@pytest.fixture(scope='session')
def fresh_check():
    result = subprocess.run([sys.executable, str(TOOLS / 'build_correspondence.py'), '--check'],
                            cwd=ROOT, capture_output=True, text=True, timeout=600)
    assert result.returncode == 0, result.stdout + result.stderr
    return result


def test_check_regenerates_with_actual_lean(fresh_check):
    assert '"failed_checks": []' in fresh_check.stdout


def test_every_result_has_verbatim_paper_text_and_a_printed_declaration(fresh_check):
    tool = load(); entries = tool.collect()
    output = tool.OUTPUT.read_text()
    with (tool.PAPER / 'prewriting/result_labels.csv').open(newline='') as source:
        rows = list(csv.DictReader(source))
    formal = [entry for entry in entries if not entry['prose']]
    assert len(formal) == len(rows)
    assert {e['row']['label'] for e in formal} == {r['label'] for r in rows}
    types = tool.parse_probe(tool.PROBE_LOG.read_text(),
                             sorted({r['name'] for e in entries for r in e['records']}))
    for entry in entries:
        assert entry['records']
        for passage in entry['passages']:
            assert passage['text'].strip()
            assert tool.fence('latex', passage['text']) in output
        for record in entry['records']:
            assert types[record['name']].strip()
            assert tool.fence('lean', types[record['name']][:tool.TYPE_LIMIT]) in output
    assert {e['row']['claim_id'] for e in entries if e['prose']} == set(tool.PROSE_PHRASES)


def test_nested_statement_extraction_is_verbatim(tmp_path):
    tool = load(); (tmp_path / 'sections').mkdir()
    body = 'For every $x$, the following holds.\n'+r'\begin{enumerate}'+'\n'+r'\item Keep $x$.'+'\n'+r'\end{enumerate}'
    source = r'\begin{proposition}[A [nested] title]'+'\n% claim: TEST\n'+r'\label{prop:test}'+'\n'+body+'\n'+r'\end{proposition}'+'\n'
    (tmp_path / 'sections/sec.tex').write_text(source)
    row = dict(file='sec.tex',label='prop:test',environment='proposition',claim_id='TEST')
    assert tool.paper_statement(row,tmp_path)['text'] == body
    with pytest.raises(ValueError,match='environment mismatch'):
        tool.paper_statement(dict(row,environment='lemma'),tmp_path)
    (tmp_path / 'sections/sec.tex').write_text(source.replace(body,''))
    with pytest.raises(ValueError,match='Empty paper statement'):
        tool.paper_statement(row,tmp_path)


def test_failed_check_is_not_replaced_with_an_inferred_type():
    tool = load()
    with pytest.raises(ValueError,match='Lean #check failed: CSTTT.DoesNotExist'):
        tool.parse_probe('W18A_BEGIN CSTTT.DoesNotExist\nprobe: error: unknown constant\n'
                         'W18A_END CSTTT.DoesNotExist\n',['CSTTT.DoesNotExist'])


def test_long_type_has_a_visible_truncation_notice():
    tool = load(); name='CSTTT.Example.longType'
    text=tool.lean_cell([dict(name=name,axioms=[],in_inventory='yes')],{name:'A'*4001})
    assert 'A'*4000 in text and 'A'*4001 not in text
    assert '**TRUNCATED:** showing the first 4,000 characters of 4001' in text


def test_drift_is_detected_without_overwriting(tmp_path,monkeypatch,fresh_check):
    tool=load(); entries=tool.collect()
    names=sorted({r['name'] for e in entries for r in e['records']})
    types=tool.parse_probe(tool.PROBE_LOG.read_text(),names)
    monkeypatch.setattr(tool,'lean_types',lambda _: types)
    output=tmp_path/'correspondence.md';output.write_text(tool.OUTPUT.read_text()+'\nDRIFT\n')
    before=output.read_bytes()
    monkeypatch.setattr(tool,'OUTPUT',output)
    monkeypatch.setattr(sys,'argv',['build_correspondence.py','--check'])
    assert tool.main()==1
    assert output.read_bytes()==before


def test_digest_links_prefer_the_claims_own_item():
    tool=load()
    items=tool.digest_items('## 1. TTN-02: public shadow\nDescription.\n'
                            '## 2. Another claim\nCompare TTN-02.\n')
    links=tool.digest_links('TTN-02',[],items)
    assert 'formal_digest.md#1-ttn-02-public-shadow' in links
    assert 'Another claim' not in links


def test_suffixed_claim_uses_its_explicit_ledger_source_row():
    tool=load()
    items=tool.digest_items('## 1. TTH-06: generic and instance\nDescription.\n')
    assert 'none matched' in tool.digest_links('TTH-06-INST',[],items)
    assert 'formal_digest.md#1-tth-06-generic-and-instance' in tool.digest_links(
        'TTH-06-INST',[],items,source_rows=['TTH-06'])
