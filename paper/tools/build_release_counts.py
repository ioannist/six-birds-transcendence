#!/usr/bin/env python3
"""Offline W19 release counts: recomputed static facts plus dated run receipts.

--check validates schema and regenerates both JSON and TeX without running
tests, Lean, LaTeX, or a network request. Run-recorded facts are read from exact
command receipts; their summary metrics are parsed again, never hand typed.
"""
import argparse
from collections import Counter
import csv
import hashlib
import json
from pathlib import Path
import re
import sys

from jsonschema import Draft202012Validator
from record_release_check import measurement
from render_figure_data import macro_name

ROOT=Path(__file__).resolve().parents[2]
PAPER=ROOT/'paper'
OUTPUT=PAPER/'data/release_counts.json'
TEX=PAPER/'includes/release_counts.tex'
SCHEMA=PAPER/'data/release_counts.schema.json'
RECEIPTS=PAPER/'data/release_receipts'
REPORT=PAPER/'data/release_verification.md'
ALLOWED={'propext','Quot.sound','Classical.choice'}


def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()


def csv_rows(path):
    with path.open(newline='') as source:return list(csv.DictReader(source))


def static_counts():
    registry=ROOT/'cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv'
    invpath=ROOT/'lean/row_inventory.json';mapfile=PAPER/'prewriting/lean_declaration_map.csv'
    rows=csv_rows(registry);statuses=Counter(r['status_09'] for r in rows)
    known={'proved','checked finite countermodel','open'}
    if set(statuses)-known:raise ValueError('Unexpected registry status; classify it explicitly')
    inventory=json.loads(invpath.read_text())
    if {r['row_id'] for r in inventory['rows']}!={r['theorem_id'] for r in rows}:raise ValueError('Inventory/registry mismatch')
    entries=[n for r in inventory['rows'] for n in r['declarations']]
    modules=sorted((ROOT/'lean/CSTTT').rglob('*.lean'))
    tree='\n'.join(str(p.relative_to(ROOT))+':'+sha(p) for p in modules)
    mapped=csv_rows(mapfile);names=set();axioms=set()
    for r in mapped:
        decl=r['headline_declarations'].split(';');proofs=json.loads(r['declaration_axioms'])
        if any(not n.startswith('CSTTT.') or n.startswith('UNRESOLVED:') or n not in proofs for n in decl):
            raise ValueError('Unresolved headline or missing axiom probe')
        names.update(decl)
        for n in decl:axioms.update(proofs[n])
    if axioms-ALLOWED:raise ValueError('Untrusted headline axiom: '+str(axioms-ALLOWED))
    modelpaths=sorted({p for file in [mapfile,PAPER/'prewriting/evidence_matrix.csv']
                       for row in csv_rows(file) for p in row['model_files'].split(';')
                       if p.startswith('audit/proposed_models/') and p.endswith('.model.json')})
    for p in modelpaths:
        if not (ROOT/p).is_file():raise ValueError('Missing paper model spec: '+p)
    return dict(
        registry=dict(rows=len(rows),proved=statuses['proved'],checked_finite_countermodel=statuses['checked finite countermodel'],
                      open=statuses['open'],source=str(registry.relative_to(ROOT)),sha256=sha(registry)),
        inventory=dict(declaration_entries=len(entries),unique_declarations=len(set(entries)),
                       definition='Sum of declarations arrays in all row_inventory.json rows; unique count deduplicates names.',
                       source=str(invpath.relative_to(ROOT)),sha256=sha(invpath)),
        modules=dict(under_csttt_directory=len(modules),including_root=len(modules)+int((ROOT/'lean/CSTTT.lean').is_file()),
                     definition='*.lean source files recursively under lean/CSTTT; including_root also counts lean/CSTTT.lean.',
                     source='lean/CSTTT/**/*.lean',tree_sha256=hashlib.sha256(tree.encode()).hexdigest()),
        headlines=dict(distinct=len(names),axioms=sorted(axioms),source=str(mapfile.relative_to(ROOT)),sha256=sha(mapfile)),
        model_specs=dict(count=len(modelpaths),files=modelpaths,sha256={p:sha(ROOT/p) for p in modelpaths},
                         definition='Distinct audit/proposed_models/*.model.json files named by model_files in either evidence map. '
                         'This counts specification files, not distinct raw worlds; finite physical factors may have unbounded histories.'),
        toolchain=dict(value=(ROOT/'lean/lean-toolchain').read_text().strip(),source='lean/lean-toolchain',sha256=sha(ROOT/'lean/lean-toolchain')))


def run_records(evidence=None):
    records=[]
    for path in sorted(RECEIPTS.glob('*.json')):
        record=json.loads(path.read_text())
        if path.stem!=record['id']:raise ValueError('Receipt filename/id mismatch')
        if record['status']!=('pass' if record['exit_code']==0 else 'fail'):raise ValueError('Receipt status/exit mismatch')
        if record.get('metrics_status', 'valid') == 'invalid':
            raise ValueError('Invalid receipt measurement: '+record['id']+': '+record.get('metrics_note',''))
        # Full logs are authoritative when available. In exported archives only
        # the dated receipt summary remains; disclose that fallback at runtime.
        log=ROOT/record['log_path']
        if not log.resolve().is_relative_to(ROOT): raise ValueError('Release log outside repository')
        if log.is_file():
            if sha(log)!=record['log_sha256']:raise ValueError('Release log drift: '+str(log))
            source=log.read_bytes().decode('utf-8',errors='replace');mode='full_logs_verified'
        else:
            source=record['summary'];mode='summary_only_ids'
        observed=measurement(record['kind'],source,record['exit_code'])
        # A saved tail can end in a blank line; splitting that tail again is
        # not idempotent. Without a full log, the saved text itself is the
        # evidence, so reparse its metrics/status but do not normalize it again.
        keys=['metrics','metrics_status','metrics_note']
        if log.is_file(): keys.append('summary')
        for key in keys:
            expected=record.get(key, 'valid' if key=='metrics_status' else '')
            if observed[key]!=expected:
                raise ValueError(('Full log/receipt ' if log.is_file() else 'Receipt summary/')+key+' mismatch: '+record['id'])
        if evidence is not None: evidence.setdefault(mode, []).append(record['id'])
        records.append(record)
    return records


def build(evidence=None):
    records=run_records(evidence);byid={r['id']:r for r in records}
    if 'lean_build' not in byid:raise ValueError('Fresh lean_build receipt required')
    tests={r['id']:r['metrics'] for r in records if r['kind'] in {'pytest','selftest'} and 'passed' in r['metrics']}
    data=dict(schema_version='1.0',static=static_counts(),
              run_recorded=dict(definition='Dated actual command receipts; no commands are rerun by --check. '
                                'Failures remain failures. Pass counts count completed tests/probes, not Lean theorems.',
                                lean_build_jobs=byid['lean_build']['metrics'].get('jobs'),tests=tests,commands=records),
              verification_status='pass' if records and all(r['exit_code']==0 for r in records) else 'fail')
    Draft202012Validator.check_schema(json.loads(SCHEMA.read_text()))
    Draft202012Validator(json.loads(SCHEMA.read_text())).validate(data)
    return data


def tex_macros(data):
    s=data['static'];r=data['run_recorded']
    values=dict(registry_rows=s['registry']['rows'],proved_rows=s['registry']['proved'],
                checked_countermodels=s['registry']['checked_finite_countermodel'],open_rows=s['registry']['open'],
                lean_declarations=s['inventory']['declaration_entries'],unique_inventory_declarations=s['inventory']['unique_declarations'],
                csttt_modules=s['modules']['under_csttt_directory'],csttt_modules_with_root=s['modules']['including_root'],
                headline_declarations=s['headlines']['distinct'],model_specs=s['model_specs']['count'])
    if r['lean_build_jobs'] is not None: values['lean_build_jobs']=r['lean_build_jobs']
    for suite,counts in sorted(r['tests'].items()):
        for key,count in counts.items():values[suite+'_tests_'+key]=count
    lines=['% GENERATED by paper/tools/build_release_counts.py; do not edit.',
           '% Source: paper/data/release_counts.json. Static and run-recorded counts are distinguished there.',
           '% LeanDeclarations counts inventory entries, not every declaration in the Lean environment.']
    for key,value in values.items():
        name='rel'+macro_name(key).removeprefix('snap')
        lines.append(rf'\newcommand{{\{name}}}{{\ensuremath{{{value}}}}}')
    toolchain=s['toolchain']['value'].replace('_',r'\_')
    lines.append(r'\newcommand{\relLeanToolchain}{\texttt{'+toolchain+'}}')
    lines.append(r'\newcommand{\relHeadlineAxioms}{\texttt{'+', '.join(s['headlines']['axioms'])+'}}')
    return '\n'.join(lines)+'\n'


def report(data):
    s=data['static'];r=data['run_recorded']
    lines=['# W19 release verification (generated)',
           'Generated from static inputs and actual command receipts. Overall recorded status: **'+data['verification_status'].upper()+'**.',
           'A successful counts-generator check confirms reproducibility of the record; it does not turn failed commands into passes.',
           'When a full log is present, the checker re-extracts its metrics and summary and checks the log hash. '
           'An exported archive normally omits ignored logs: its check uses the recorded summary only, '
           'and explicitly reports the summary-only receipt IDs. This fallback does not rerun the original commands.',
           '| Count | Value | Classification / source |','|---|---|---|',
           f"| Registry | {s['registry']['rows']} rows: {s['registry']['proved']} proved / {s['registry']['checked_finite_countermodel']} checked finite countermodel / {s['registry']['open']} open | static: `{s['registry']['source']}` |",
           f"| Inventory declarations | {s['inventory']['declaration_entries']} entries; {s['inventory']['unique_declarations']} unique | static: `{s['inventory']['source']}` |",
           f"| CSTTT modules | {s['modules']['under_csttt_directory']} under directory; {s['modules']['including_root']} including root | static: `{s['modules']['source']}` |",
           f"| Lean build jobs | {r['lean_build_jobs']} | run-recorded: `lean_build` receipt |",
           f"| Paper headline declarations | {s['headlines']['distinct']} | static: `{s['headlines']['source']}` |",
           f"| Headline axiom union | {', '.join(s['headlines']['axioms'])} | static: fresh-probed declaration map |",
           f"| Model specification files | {s['model_specs']['count']} | static: {s['model_specs']['definition']} |",
           f"| Lean toolchain | `{s['toolchain']['value']}` | static: `{s['toolchain']['source']}` |"]
    for suite,counts in r['tests'].items():lines.append('| '+suite+' | '+', '.join(str(n)+' '+key for key,n in counts.items())+' | run-recorded receipt |')
    byid={item['id']:item for item in r['commands']}
    lines+=['','## Retained failed attempts','']
    if byid.get('cst_tt',{}).get('status')=='fail':
        count=byid['cst_tt']['metrics'].get('failed','unavailable')
        lines.append(f'- `cst_tt`: the configured legacy CST-TT suite has {count} pre-existing failures, '
                     'also reported at `ba3e5dd`. They concern raw-text vocabulary/placeholder scans, '
                     'a historical import-layer restriction, two references to the retired countermodel '
                     'kernel, and historical-builder idempotence. They are not all scaffold scans. '
                     'Historical generated assets rewritten by that test were restored byte-for-byte.')
    if byid.get('cst_tt_initial_setup',{}).get('status')=='fail':
        lines.append('- `cst_tt_initial_setup`: an unconfigured pytest invocation failed during '
                     'collection because `tt07a_data` was not on `PYTHONPATH`. The configured '
                     '`cst_tt` invocation supplies `PYTHONPATH=src:scripts` and is the test-count '
                     'source. The initial collection attempt remains FAIL; it is not another suite '
                     'of completed test cases.')
    lines+=['','## Exact verification commands','',
            '| ID | Command (cwd; environment) | Recorded UTC | Result | Log SHA256 |','|---|---|---|---|---|']
    for item in r['commands']:
        cmd=' '.join(item['command']).replace('|',r'\|')
        lines.append('| '+item['id']+' | `'+cmd+'` (cwd `'+item['cwd']+'`; `'+str(item['environment'])+'`) | '+item['recorded_at']+' | '+item['status'].upper()+' | `'+item['log_sha256']+'` |')
    failures=[line for item in r['commands'] for line in item['summary'].splitlines() if line.startswith('FAILED ')]
    if failures:lines+=['','## Reported failing test cases','',*['- `'+line+'`' for line in failures]]
    return '\n'.join(lines)+'\n'


def main():
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('--check',action='store_true');a=p.parse_args()
    evidence={}
    try:data=build(evidence)
    except Exception as exc:print('ERROR: '+str(exc),file=sys.stderr);return 1
    outputs={OUTPUT:json.dumps(data,indent=2,sort_keys=True)+'\n',TEX:tex_macros(data),REPORT:report(data)}
    drift=[str(path) for path,text in outputs.items() if not path.exists() or path.read_bytes()!=text.encode()]
    if a.check and drift:print('Release-count drift: '+', '.join(drift),file=sys.stderr);return 1
    if not a.check:
        for path,text in outputs.items():path.parent.mkdir(parents=True,exist_ok=True);path.write_text(text)
    print(json.dumps({'check':a.check,'static_counts_verified':True,'recorded_commands':len(data['run_recorded']['commands']),
                      'recorded_verification_status':data['verification_status'],
                      'full_logs_verified':len(evidence.get('full_logs_verified',[])),
                      'summary_only_receipts':len(evidence.get('summary_only_ids',[])),
                      'summary_only_ids':evidence.get('summary_only_ids',[])}))
    return 0


if __name__=='__main__':raise SystemExit(main())
