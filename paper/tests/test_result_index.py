"""W14 generated result-to-Lean index and figure-data regressions."""
import csv
import importlib.util
import json
from pathlib import Path
import re
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[2]
PAPER = ROOT / 'paper'
TOOLS = PAPER / 'tools'


def load(name):
    if str(TOOLS) not in sys.path: sys.path.insert(0, str(TOOLS))
    spec = importlib.util.spec_from_file_location('w14_' + name, TOOLS / (name + '.py'))
    module = importlib.util.module_from_spec(spec); spec.loader.exec_module(module)
    return module


def test_index_check():
    result = subprocess.run([sys.executable, str(TOOLS / 'render_index.py'), '--check'],
                            cwd=ROOT, text=True, capture_output=True)
    assert result.returncode == 0, result.stdout + result.stderr


def test_every_manuscript_claim_marker_has_an_authored_result_label():
    # Derive expectations from the manuscript, never a maintained ID list.
    # Include the authored appendices so the supplementary proposition is
    # protected too. The generated appendix uses claim-index, not claim.
    with (PAPER / 'prewriting/result_labels.csv').open(newline='') as source:
        rows = list(csv.DictReader(source))
    actual = {(r['claim_id'],r['label'],r['file']) for r in rows}
    expected = set()
    for directory in ['sections','appendices']:
        for path in (PAPER / directory).glob('*.tex'):
            text=path.read_text()
            for marker in re.finditer(r'(?m)^\s*% claim:\s*([^\n]+)',text):
                label=re.search(r'\\label\{([^}]+)\}',text[marker.end():])
                assert label, f'Unlabelled claim marker in {path.name}: {marker[1]}'
                for claim in marker[1].split(','):
                    expected.add((claim.strip(),label[1],path.name))
    assert expected, 'No manuscript claim markers found'
    assert expected <= actual, f'Missing result labels: {sorted(expected-actual)}'


def test_every_authored_result_label_and_claim_is_present_in_paper_order():
    tool = load('render_index')
    labels = tool.manuscript_labels()
    with (PAPER / 'prewriting/result_labels.csv').open(newline='') as source:
        rows = list(csv.DictReader(source))
    output = (PAPER / 'appendices/app_c_index.tex').read_text()
    assert output.splitlines()[0] == '% style-lint: artifact-appendix'
    assert r'\label{app:index}' in output
    expected = sorted(rows, key=lambda row: labels[row['label']][0])
    actual = re.findall(r'% claim-index: ([^;\n]+); label: ([^\n]+)', output)
    assert actual == [(row['claim_id'], row['label']) for row in expected]
    for row in rows:
        assert row['label'] in labels
        assert labels[row['label']][1] == row['file']
        assert output.count(r'\cref{' + row['label'] + '}') == 1
        assert r'\cref{' + row['label'] + r'}\newline ' in output
    for claim in tool.PROSE_CLAIMS:
        assert '% claim-index: ' + claim + '\n' in output


def test_index_drift_fails_without_writing(tmp_path, monkeypatch):
    tool = load('render_index'); output = tmp_path / 'index.tex'
    output.write_text(tool.render() + '% drift\n')
    before = output.read_bytes()
    monkeypatch.setattr(tool, 'OUTPUT', output)
    monkeypatch.setattr(sys, 'argv', ['render_index.py', '--check'])
    assert tool.main() == 1
    assert output.read_bytes() == before


def test_unresolved_or_missing_metadata_is_rejected():
    tool = load('render_index')
    with pytest.raises(ValueError, match='Missing Lean evidence'):
        tool.metadata_cell('Missing', {})
    bad = {'headline_declarations': 'UNRESOLVED:CSTTT.Missing', 'in_inventory': 'yes',
           'declaration_axioms': '{}'}
    with pytest.raises(ValueError, match='Unresolved'):
        tool.metadata_cell('Bad', {'Bad': bad})


def test_list_selector_macros_copy_actual_pinned_values():
    tool = load('render_figure_data')
    snapshot = json.loads((PAPER / 'data/current_results.json').read_text())
    entries = {entry['key']: entry for entry in snapshot['entries']}
    selectors = tool.element_macros(snapshot)
    assert len(selectors) == sum(len(json.loads(e['value'])) for e in entries.values()
                                 if e['value_type'].endswith('_list'))
    for key, name, body in selectors:
        base, index = re.fullmatch(r'(.+)\[(\d+)\]', key).groups()
        assert body == tool.number_tex(json.loads(entries[base]['value'])[int(index)])
        assert re.fullmatch(r'[A-Za-z]+', name)
        assert rf'\newcommand{{\{name}}}{{\ensuremath{{{body}}}}}' in tool.render(snapshot)


def test_linebreak_is_not_a_control_word_and_visible_dialect_survives():
    checker = load('check_manuscript'); linter = load('style_lint')
    assert checker.numeric_label_errors(r'Target\\keeps going', set(), {}) == []
    assert checker.numeric_label_errors(r'\hidden', set(), {'hidden': r'Target\\9'})
    assert linter.hits(r'Target\\toy')


def test_external_abstract_is_measured_as_abstract(tmp_path):
    (tmp_path / 'sections').mkdir()
    (tmp_path / 'main.tex').write_text(r'\begin{document}\input{sections/abstract}\end{document}')
    (tmp_path / 'sections/abstract.tex').write_text(
        r'\begin{abstract}We prove our bound.\end{abstract}'+'\n'+r'\noindent Keywords. Tests.')
    report = load('style_lint').analyze(tmp_path)
    abstracts = [row for row in report['rows'] if row['kind'] == 'abstract']
    assert len(abstracts) == 1 and abstracts[0]['words'] == 4


def test_assembled_figures_and_table_are_used_once():
    files = list((PAPER / 'sections').glob('*.tex'))
    text = '\n'.join(path.read_text() for path in files)
    for name, label in [('three', 'three'), ('gluing', 'gluing'),
                        ('chain', 'chain'), ('clock', 'clock'), ('fork', 'fork'), ('fusion', 'fusion')]:
        assert text.count(r'\input{figures/fig_' + name + '}') == 1
        assert text.count(r'\label{fig:' + label + '}') == 1
    assert r'\input{figures/fig_copy}' not in text and r'\label{fig:copy}' not in text
    assert not (PAPER/'figures/fig_copy.tex').exists()
    assert text.count(r'\input{tables/tab_grades}') == 1
    assert not (PAPER / 'appendices/app_00_stub.tex').exists()
