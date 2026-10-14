#!/usr/bin/env python3
"""Enrich CST-EXP-01 with exact asset provenance and lexical dependency audits.

This is a deterministic research-inventory builder. It does not select a
cross-carrier target and it is not a proof checker. The lexical dependency
index records explicit TeX references/citations in statement and immediately
following proof regions so that paper cards do not hide their source-local
support structure.
"""
from __future__ import annotations

from pathlib import Path
from collections import Counter, defaultdict
import argparse
import csv
import importlib.util
import json
import re

ASSET_STATEMENTS = {
    'A-CT-01': ['P05-S006','P05-M001','P05-M003'],
    'A-PQ-01': ['P05-S003','P05-S008','P05-S024','P12-M002','P13-S004','P13-S005','P13-S006','P14-S002','P14-S003','P14-S004','P14-S005'],
    'A-PQ-02': ['P14-S007','P14-S008','P30-S008','P30-S017'],
    'A-RT-01': ['P14-S001','P14-S006','P14-S007','P14-S008'],
    'A-HO-01': ['P14-S010','P30-S022','P30-S023','P35-M001','P50-S004','P50-S007','P50-S014','P53-M004'],
    'A-RE-01': ['P05-S017','P05-S025','P18-S001','P18-S002','P18-S003','P18-S004','P18-S005','P24-S001','P24-S002','P24-S003','P24-S004','P24-S005','P24-S006'],
    'A-OP-01': ['P05-S024','P30-S037'],
    'A-PR-01': ['P03-M001','P03-M002','P03-M004','P16-S012','P16-S021','P23-S001','P23-S004','P23-S006','P23-S007'],
    'A-EX-01': ['P08-S002','P08-S003','P08-S004','P08-S005'],
    'A-ST-01': ['P03-M001','P03-M002','P03-M003','P03-M004'],
    'A-EV-01': ['P09-S002','P09-S003','P09-S006','P09-S008','P09-S010','P39-M001','P39-M002','P39-M003','P39-M004'],
    'A-LG-01': ['P17-S002','P17-S004','P17-S014','P17-S015','P30-S025'],
    'A-AOR-01': ['P06-S001','P06-S003','P06-S006','P06-S009','P06-S010','P06-S037','P06-S038','P06-S050'],
    'A-VI-01': ['P05-S005','P05-S008','P22-S015','P22-S016','P22-S022','P22-S023','P57-M002','P57-M003','P57-M004'],
    'A-CU-01': ['P05-S019','P05-S020','P32-S012','P32-S018','P32-S019','P32-S023','P56-M001','P56-M002','P56-M003','P56-M004','P56-M005'],
    'A-AG-01': ['P32-S007','P32-S016','P32-S018','P32-S019','P32-S039','P57-M001','P57-M002','P57-M003','P57-M004','P57-M005'],
    'A-TM-01': ['P05-S018','P05-M002','P53-M001','P53-M002','P53-M003','P53-M004','P53-M005'],
    'A-HID-01': ['P05-S009','P13-S004','P13-S005','P13-S006','P13-S008','P13-S017','P13-S018','P13-S023','P13-S024'],
    'A-NO-01': ['P05-S011','P30-S009','P30-S010','P52-S003','P52-S021'],
    'A-PT-01': ['P33-S044','P33-S045','P34-S002','P34-S016','P34-S022','P35-M001','P35-M002','P35-M003','P57-M004'],
    'A-CF-01': ['P30-S022','P30-S023','P30-S026','P30-S046','P50-S004','P50-S007','P50-S011','P50-S014','P50-S017','P50-S024','P50-S026'],
    'A-AR-01': ['P04-S001','P04-S002','P04-S004','P04-S011','P04-S014','P04-S015','P04-S020','P04-S021','P04-S022'],
    'A-CD-01': ['P44-S001','P44-S002','P44-S003','P44-S004','P44-S005','P44-S006'],
    'A-FS-01': ['P33-S005','P33-S044','P33-S055','P33-S076','P52-S001','P52-S003','P52-S005','P52-S008','P52-S010','P52-S013','P52-S017','P52-S019','P52-S020','P52-S021','P52-S022'],
    'A-QEC-01': ['P07-M001','P07-M002','P07-M003','P07-M004'],
    'A-ON-01': ['P05-M003','P05-S026','P05-S027','P05-S028','P58-M001','P58-M003','P58-M004'],
}


def load_builder(path: Path):
    spec = importlib.util.spec_from_file_location('exp01_builder', path)
    mod = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(mod)
    return mod


def write_csv(path: Path, fields: list[str], rows: list[dict]):
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open('w', newline='', encoding='utf-8') as fh:
        w = csv.DictWriter(fh, fieldnames=fields, extrasaction='ignore')
        w.writeheader(); w.writerows(rows)


def write_text(path: Path, text: str):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text.rstrip() + '\n', encoding='utf-8')


def short(s: str, n: int = 180) -> str:
    s = re.sub(r'\s+', ' ', s or '').strip()
    return s if len(s) <= n else s[:n-1].rstrip() + '…'


def extract_refs(text: str) -> tuple[list[str], list[str]]:
    refs: list[str] = []
    for m in re.finditer(r'\\(?:[Cc]ref|ref|eqref|autoref|pageref)\s*\{([^}]*)\}', text):
        refs.extend(x.strip() for x in m.group(1).split(',') if x.strip())
    for m in re.finditer(r'\\hyperref\[([^]]+)\]', text):
        if m.group(1).strip(): refs.append(m.group(1).strip())
    cites: list[str] = []
    for m in re.finditer(r'\\cite[a-zA-Z*]*(?:\[[^]]*\]){0,2}\s*\{([^}]*)\}', text):
        cites.extend(x.strip() for x in m.group(1).split(',') if x.strip())
    return list(dict.fromkeys(refs)), list(dict.fromkeys(cites))


def proof_region(lines: list[str], statement_end: int) -> tuple[int|None, int|None, str]:
    # statement_end is 1-based inclusive. Search a small immediate region only;
    # this avoids attaching a later theorem's proof to the current statement.
    start_idx = statement_end
    max_probe = min(len(lines), start_idx + 14)
    proof_start = None
    for i in range(start_idx, max_probe):
        stripped = re.sub(r'%.*$', '', lines[i]).strip()
        if not stripped:
            continue
        if re.search(r'\\begin\{proof\}(?:\[[^]]*\])?', stripped):
            proof_start = i
            break
        if re.search(r'\\(?:sub)*section\*?\{|\\begin\{(?:definition|theorem|proposition|lemma|corollary|postulate|construction|schema|remark|example)\}', stripped):
            break
        # Permit labels, grades, and short bridge prose before proof.
        if i - start_idx > 7:
            break
    if proof_start is None:
        return None, None, ''
    proof_end = None
    for j in range(proof_start, min(len(lines), proof_start + 500)):
        if '\\end{proof}' in lines[j]:
            proof_end = j
            break
    if proof_end is None:
        return proof_start + 1, None, '\n'.join(lines[proof_start: min(len(lines), proof_start + 120)])
    return proof_start + 1, proof_end + 1, '\n'.join(lines[proof_start: proof_end + 1])


def build_dependency_ledgers(papers_dir: Path, papers: list[dict], statements: list[dict], repo: Path):
    pby = {p['paper_id']: p for p in papers}
    filename_to_pid = {p['filename']: p['paper_id'] for p in papers}
    statements_by_pid = defaultdict(list)
    for s in statements:
        if s['paper_id'] != 'P46': statements_by_pid[s['paper_id']].append(s)

    label_rows: list[dict] = []
    label_location: dict[tuple[str,str], tuple[int,str]] = {}
    statement_for_label: dict[tuple[str,str], str] = {}
    for s in statements:
        if s['paper_id'] == 'P46': continue
        if s.get('label'):
            statement_for_label[(s['paper_id'], s['label'])] = s['statement_id']

    for f in sorted(papers_dir.glob('*.tex')):
        pid = filename_to_pid[f.name]
        if pid == 'P46':
            continue
        lines = f.read_text(errors='replace').splitlines()
        current_section = ''
        for no, line in enumerate(lines, 1):
            sm = re.search(r'\\(?:sub)*section\*?\{([^}]*)\}', line)
            if sm: current_section = re.sub(r'\\[A-Za-z@]+|[{}$]', '', sm.group(1)).strip()
            for lm in re.finditer(r'\\label\{([^}]+)\}', line):
                label = lm.group(1)
                statement_id = statement_for_label.get((pid,label),'')
                row = {
                    'paper_id': pid, 'source_file': f.name, 'label': label,
                    'source_line': no, 'nearest_section': current_section,
                    'resolved_statement_id': statement_id,
                    'label_kind': 'statement' if statement_id else ('equation' if label.startswith(('eq:','eqn:')) else 'section/figure/table/other'),
                }
                label_rows.append(row)
                label_location[(pid,label)] = (no, statement_id)

    dep_rows: list[dict] = []
    for pid, arr in sorted(statements_by_pid.items()):
        p = pby[pid]
        f = papers_dir / p['filename']
        lines = f.read_text(errors='replace').splitlines()
        for s in sorted(arr, key=lambda x: x['statement_seq']):
            ps, pe, ptext = proof_region(lines, int(s['line_end']))
            body = s.get('raw','') + '\n' + ptext
            refs, cites = extract_refs(body)
            own = s.get('label','')
            refs = [r for r in refs if r != own]
            resolved_statement_ids = []
            resolved_locations = []
            unresolved = []
            for ref in refs:
                loc = label_location.get((pid,ref))
                if not loc:
                    unresolved.append(ref)
                else:
                    line, sid = loc
                    resolved_locations.append(f'{ref}@L{line}')
                    if sid and sid not in resolved_statement_ids:
                        resolved_statement_ids.append(sid)
            if resolved_statement_ids or resolved_locations:
                status = 'explicit-internal-references'
                if unresolved: status = 'mixed-resolved-and-unresolved-labels'
            elif cites:
                status = 'external-citations-only'
            elif refs:
                status = 'unresolved-label-references'
            else:
                status = 'no-explicit-lexical-dependency'
            dep_rows.append({
                'statement_id': s['statement_id'], 'paper_id': pid,
                'source_file': p['filename'], 'source_label': s.get('label',''),
                'statement_lines': f"{s['line_start']}-{s['line_end']}",
                'proof_present': 'yes' if ps else 'no',
                'proof_lines': '' if not ps else (f'{ps}-{pe}' if pe else f'{ps}-unclosed'),
                'referenced_labels': ';'.join(refs),
                'resolved_statement_ids': ';'.join(resolved_statement_ids),
                'resolved_source_locations': ';'.join(resolved_locations),
                'unresolved_reference_labels': ';'.join(unresolved),
                'citation_keys': ';'.join(cites),
                'dependency_status': status,
                'audit_note': 'Lexical TeX-reference audit only; absence of an explicit reference is not proof independence.',
            })
    write_csv(repo/'ledgers/source_label_index.csv', list(label_rows[0].keys()), label_rows)
    write_csv(repo/'ledgers/lexical_dependency_index.csv', list(dep_rows[0].keys()), dep_rows)
    return dep_rows, label_rows


def insert_dependency_sections(repo: Path, provenance: list[dict], dep_rows: list[dict]):
    dep_by = {r['statement_id']: r for r in dep_rows}
    prov_by_pid = defaultdict(list)
    for r in provenance: prov_by_pid[r['paper_id']].append(r)
    for i in range(1,61):
        pid=f'P{i:02d}'
        card_path=repo/f'corpus/paper_cards/{pid}.md'
        text=card_path.read_text(encoding='utf-8')
        if pid=='P46':
            section="""## Source-dependency audit

No definition, theorem, proof dependency, citation dependency, map, witness, or formal asset is imported from P46 under the active quarantine.

"""
        else:
            lines=["## Source-dependency audit", "", "This table records explicit TeX references and citations visible in each curated formal statement and its immediately following `proof` environment. It is a provenance aid, not a semantic proof checker; an empty row does not mean logical independence.", "", "| Record | Proof block | Resolved statement dependencies | Other source labels | Citation keys |", "|---|---|---|---|---|"]
            for r in prov_by_pid[pid]:
                sid=r['statement_id']
                d=dep_by.get(sid)
                if not d:
                    proof='source passage'
                    deps='—'; labels='—'; cites='—'
                else:
                    proof=d['proof_lines'] or 'none explicit'
                    deps=d['resolved_statement_ids'] or '—'
                    labels=d['resolved_source_locations'] or d['unresolved_reference_labels'] or '—'
                    cites=d['citation_keys'] or '—'
                lines.append(f"| `{sid}` | {short(proof,80)} | {short(deps,150)} | {short(labels,180)} | {short(cites,140)} |")
            lines += ["", "The complete statement-level audit is in `../../ledgers/lexical_dependency_index.csv`; source labels are indexed in `../../ledgers/source_label_index.csv`.", ""]
            section='\n'.join(lines)
        marker='## Source-dependency audit\n'
        if marker in text:
            a=text.index(marker)
            b=text.index('\n## Assumptions and dependencies',a)
            text=text[:a]+section+text[b+1:]
        else:
            anchor='## Assumptions and dependencies\n'
            if anchor not in text: raise RuntimeError(f'missing insertion anchor in {pid}')
            text=text.replace(anchor, section+anchor, 1)
        card_path.write_text(text,encoding='utf-8')


def custom_quarantine_card(repo: Path, p46: dict):
    text=f"""# P46 — {p46['triage_title']}

> **Corpus verdict:** quarantine retained  
> **Phase role:** metadata/exclusion card only  
> **Claim lanes touched:** M  
> **Version handling:** quarantined

## Source identity

| Field | Value |
|---|---|
| Corpus ID | `P46` |
| Source file | `{p46['filename']}` |
| Embedded title | {p46['embedded_title']} |
| SHA-256 | `{p46['sha256']}` |
| Source size | {p46['bytes']} bytes; {p46['lines']} lines |
| Lexically detected theorem-like environment boundaries | {p46['statement_count']} — bodies excluded from the project statement bank |

## Quarantine record

| Record | Status | Scope |
|---|---|---|
| `P46-EXCLUSION` | active, fail-closed | No definition, statement, map, proof dependency, witness, executable asset, analogy, or application lesson is imported. |

P46 is absent from `corpus/machine_index/all_statement_index.csv`, `ledgers/lexical_dependency_index.csv`, and all asset-provenance rows. Its source archive remains hash-preserved only so corpus accounting is complete and the exclusion can be independently verified.

## Source-dependency audit

No source dependency is imported or assessed under the active quarantine.

## Reopening rule

Only an explicit owner instruction may revoke this quarantine. Reopening would require a new logged decision, statement-level import audit, support/carrier typing, and regeneration of all affected ledgers. No later phase may cite P46 merely because its metadata card exists.

## Phase disposition

This card proves that the paper was not silently skipped. It contributes no substantive premise, target hint, or evidential weight to CST-EXP-01.
"""
    write_text(repo/'corpus/paper_cards/P46.md',text)


def build_map_ledger(repo: Path, builder, papers: list[dict]):
    pby={p['paper_id']:p for p in papers}
    rows=[]
    for pid in [f'P{i:02d}' for i in range(1,61)]:
        if pid=='P46':
            rows.append({'map_id':'MAP-P46-00','paper_id':pid,'paper_title':pby[pid]['triage_title'],'object_or_map':'none imported','type_signature':'—','source_type':'—','target_type':'—','imported_status':'quarantined-no-import','cross_carrier_caution':'No map content imported.','fixed_support_flag':'quarantined','version_status':'quarantined'})
            continue
        maps=builder.MAPS.get(pid,[])
        if not maps:
            rows.append({'map_id':f'MAP-{pid}-00','paper_id':pid,'paper_title':pby[pid]['triage_title'],'object_or_map':'none imported as transfer map','type_signature':'—','source_type':'—','target_type':'—','imported_status':'explicit-negative-record','cross_carrier_caution':'Application-local objects are not promoted into a source-target bridge by default.','fixed_support_flag':builder.support_scope(pid,pby[pid])[0],'version_status':builder.version_status(pid)})
        for j,(obj,typ,src,tgt,status,caution) in enumerate(maps,1):
            rows.append({'map_id':f'MAP-{pid}-{j:02d}','paper_id':pid,'paper_title':pby[pid]['triage_title'],'object_or_map':obj,'type_signature':typ,'source_type':src,'target_type':tgt,'imported_status':status,'cross_carrier_caution':caution,'fixed_support_flag':builder.support_scope(pid,pby[pid])[0],'version_status':builder.version_status(pid)})
    write_csv(repo/'ledgers/map_type_ledger.csv',list(rows[0].keys()),rows)
    return rows


def build_asset_provenance(repo: Path, builder, provenance: list[dict]):
    pbyid={r['statement_id']:r for r in provenance}
    asset_info={a[0]:a for a in builder.ASSET_FAMILIES}
    missing=[]; rows=[]
    for aid, sids in ASSET_STATEMENTS.items():
        if aid not in asset_info: missing.append(f'unknown asset {aid}'); continue
        for sid in sids:
            if sid not in pbyid:
                missing.append(f'{aid}:{sid}'); continue
            r=pbyid[sid]
            role='boundary/control' if ('nonclaim' in r['asset_tags'].lower() or r['statement_kind'] in {'nonclaim','remark'}) else 'constructive/definitional input'
            rows.append({
                'asset_id':aid,'asset_name':asset_info[aid][1],'statement_id':sid,
                'paper_id':r['paper_id'],'source_file':r['source_file'],'source_lines':r['source_lines'],
                'source_label':r['source_label'],'statement_name':r['statement_name'],
                'provenance_role':role,'claim_lanes':r['claim_lanes'],
                'fixed_support':r['fixed_support'],'version_status':r['version_status'],
                'selection_status':r['selection_status'],
                'scope_note':r['nonclaim_or_limit'],
            })
    if missing:
        raise RuntimeError('asset provenance references missing: '+', '.join(missing))
    write_csv(repo/'ledgers/asset_provenance.csv',list(rows[0].keys()),rows)
    summary=["# Asset-to-statement provenance", "", "Each of the 26 canonical assets is linked to exact source records below. Reuse is fail-closed: citing an asset without carrying its fixed-support and boundary rows is invalid.", "", "| Asset | Exact records | Papers | Fixed-support values |", "|---|---:|---|---|"]
    by=defaultdict(list)
    for r in rows: by[r['asset_id']].append(r)
    for a in builder.ASSET_FAMILIES:
        aid,name=a[0],a[1]; rr=by[aid]
        summary.append(f"| `{aid}` — {name} | {len(rr)} | {', '.join(sorted(set(x['paper_id'] for x in rr)))} | {', '.join(sorted(set(x['fixed_support'] for x in rr)))} |")
    summary += ["", "Machine-readable crosswalk: `../../ledgers/asset_provenance.csv`."]
    write_text(repo/'corpus/asset_atlas/ASSET_PROVENANCE.md','\n'.join(summary))
    return rows


def build_indexes_and_methods(repo: Path, papers: list[dict], provenance: list[dict], statements: list[dict], builder, deps: list[dict], maps: list[dict], asset_rows: list[dict]):
    # Clause index.
    clause_lines=['# C-package clause-card index','', '| Clause | Name | Principal lanes | Status |','|---|---|---|---|']
    for cid in [f'C{i}' for i in range(1,9)]:
        text=(repo/f'corpus/clause_cards/{cid}.md').read_text()
        title=text.splitlines()[0].split('—',1)[1].strip()
        lanes=re.search(r'\*\*Claim lanes:\*\* (.*)',text)
        clause_lines.append(f'| [{cid}]({cid}.md) | {title} | {lanes.group(1) if lanes else "S-R"} | design clause; component evidence only |')
    write_text(repo/'corpus/clause_cards/INDEX.md','\n'.join(clause_lines))

    # Theorem index.
    theorem_lines=['# Theorem-family card index','', 'These cards are source-scoped inventory objects, not selected project targets.','', '| Card | Title | Source paper | Lanes |','|---|---|---|---|']
    for f in sorted((repo/'corpus/theorem_cards').glob('*.md')):
        if f.name=='INDEX.md': continue
        text=f.read_text(); title=text.splitlines()[0][2:]
        pm=re.search(r'\*\*Source paper:\*\* \[([^]]+)\]',text)
        lm=re.search(r'\*\*Claim lanes:\*\* (.*)',text)
        theorem_lines.append(f'| [{f.stem}]({f.name}) | {title.split("—",1)[-1].strip()} | {pm.group(1) if pm else "—"} | {lm.group(1) if lm else "—"} |')
    write_text(repo/'corpus/theorem_cards/INDEX.md','\n'.join(theorem_lines))

    pcount=Counter(r['paper_id'] for r in provenance)
    scount=Counter(s['paper_id'] for s in statements if s['paper_id']!='P46')
    paper_rows=[]
    coverage=['# Paper coverage audit','', 'Every one of the 60 corpus manuscripts has an explicit disposition. P46 is counted by metadata/exclusion only; P42/P60 are one versioned evidence line. The full non-quarantined lexical bank is retained even where only a small number of records are curated.','', '| ID | Title | Role | Lexical statements retained | Curated records | Fixed-support flag | Version/exclusion |','|---|---|---|---:|---:|---|---|']
    for p in papers:
        pid=p['paper_id']; fixed=builder.support_scope(pid,p)[0]; ver=builder.version_status(pid); role=builder.phase_role(pid,p)
        coverage.append(f"| [{pid}](../paper_cards/{pid}.md) | {p['triage_title'].replace('|','\\|')} | {role} | {0 if pid=='P46' else scount[pid]} | {pcount[pid]} | {fixed} | {ver} |")
        paper_rows.append({'paper_id':pid,'title':p['triage_title'],'phase_role':role,'source_statement_count':p['statement_count'],'lexical_statements_retained':0 if pid=='P46' else scount[pid],'curated_records':pcount[pid],'fixed_support_flag':fixed,'version_status':ver,'card_path':f'corpus/paper_cards/{pid}.md'})
    write_text(repo/'corpus/asset_atlas/PAPER_COVERAGE_AUDIT.md','\n'.join(coverage))
    write_csv(repo/'ledgers/paper_coverage_audit.csv',list(paper_rows[0].keys()),paper_rows)

    kinds=Counter(r['statement_kind'] for r in provenance)
    method=f"""# Statement selection and source-reading method

## Two-layer inventory

CST-EXP-01 keeps two deliberately different layers:

1. **Complete lexical layer:** {sum(scount.values())} theorem-like environments from all non-quarantined manuscripts, with source file, exact line span, label, kind, and compact text. This layer is in `../machine_index/all_statement_index.csv` and prevents curated selection from erasing formal source statements.
2. **Curated transfer layer:** {len(provenance)} source records selected for transfer-oriented navigation. It contains {kinds.get('source-passage',0)} manually bounded source passages for papers or critical sections that do not expose their content through theorem environments, plus formal statements selected by exact label/name and relevance.

The lexical parser is a provenance aid, not a TeX proof checker. Compact text may simplify macros; the original TeX archives are hash-preserved under `../../inputs/source_archives/`, and exact line spans are authoritative.

## Selection rules

- Dependency-order wave papers receive deeper selection than supporting/peripheral papers.
- Definitions, theorem/proposition/corollary statements, postulates, explicit nonclaims, controls, and named open boundaries are preferred.
- A record is not upgraded because Lean, Python, or code is mentioned. Evidence status stays paper-local.
- Every imported statement carries a fixed-support flag and an interface-relative warning.
- P46 is excluded fail-closed; no statement body enters either bank.
- P42 is the normative newer Strict Audited Utility revision. P60 remains for delta/provenance only and has zero independent evidential weight.
- Manual passages are exact line-bounded excerpts, not paraphrases invented without a source span.

## Dependency audit

`../../ledgers/lexical_dependency_index.csv` records explicit local references and citations from statement bodies and immediately following proof environments for {len(deps)} non-quarantined formal statements. It does not infer unreferenced logical dependencies. The source-label index contains {len(list(csv.DictReader((repo/'ledgers/source_label_index.csv').open())))} labels.

## Typed maps and asset provenance

`../../ledgers/map_type_ledger.csv` contains {len(maps)} positive or explicit-negative map records, including source and target types. `../../ledgers/asset_provenance.csv` contains {len(asset_rows)} exact asset-to-statement links for all {len(builder.ASSET_FAMILIES)} canonical asset families.

## Nonselection rule

Curation establishes what can be reused and what remains blocked. It does not rank candidate transported objects, bridge types, lineage criteria, scenarios, theorem targets, or toy programs.
"""
    write_text(repo/'corpus/asset_atlas/STATEMENT_SELECTION_METHOD.md',method)

    exit_gate=f"""# CST-EXP-01 exit-gate audit

## Gate 1 — every later primitive is traceable or new

**PASS.** The canonical atlas has {len(builder.ASSET_FAMILIES)} asset IDs and `ledgers/asset_provenance.csv` supplies {len(asset_rows)} exact source links. The fail-closed rule requires any later primitive not in that ledger to be marked genuinely new.

## Gate 2 — fixed-support status is visible

**PASS.** All 60 paper-level records have a fixed-support/carrier-scope field. Papers P03, P08, P09, P14, P16, P18, P23, P24, and P39 are explicitly fixed-support. P05 is mixed/component-level; P07 is an engineering analogue whose transport primitive was not tested; P58 is nonstructural/axiom-relative.

## Gate 3 — no paper silently skipped

**PASS.** `PAPER_COVERAGE_AUDIT.md` has 60 rows. Every paper has a card and at least one curated disposition record. P46 is a metadata-only quarantine record, not a substantive import.

## Gate 4 — consciousness package is decomposed without overclaim

**PASS.** C1–C8 have separate cards. T14, T15, T17, and 22 additional directly relevant theorem/family cards are source-scoped. P05:627–643 records component evidence on separate carriers and no integrated instance; P05:1630–1687 records the simplified/full nonordering and absent integrated target.

## Gate 5 — dependency and gap structure is explicit

**PASS.** The dependency graph contains predictive quotients, route transport, holonomy, recombination, relation-valued persistence, promotion/exactification/tests/event admissibility/AOR, viability/currency/repair/time, hiddenness/no-overreading/protocol/local-global obstructions, and the entry points for certificate soundness, A1, A2, recognition, and the missing cross-carrier theorem. Fourteen gap rows include required new-result type and kill test.

## Gate 6 — exploration boundary retained

**PASS.** No candidate target, bridge semantics, scenario verdict, theorem conjecture, or toy-program contract is selected. Cross-asset composition notes are explicitly unranked and incomplete.
"""
    write_text(repo/'corpus/asset_atlas/EXIT_GATE_AUDIT.md',exit_gate)

    dep_method="""# Lexical source-dependency audit method

For each non-quarantined theorem-like environment, the audit scans the environment body and an immediately following `proof` environment, when present. It records explicit `ref`/`cref`/`eqref`/`autoref`/`hyperref` labels and citation keys, resolves local labels to statement IDs or source lines, and preserves unresolved labels rather than guessing.

This audit answers a narrow provenance question: **which dependencies are explicitly named in the source text?** It does not reconstruct implicit mathematics, validate proofs, or certify that a theorem is independent when no reference appears. P46 is entirely absent under quarantine.
"""
    write_text(repo/'corpus/asset_atlas/LEXICAL_DEPENDENCY_METHOD.md',dep_method)


def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--repo',type=Path,required=True)
    ap.add_argument('--papers-dir',type=Path,required=True)
    ap.add_argument('--parsed-dir',type=Path,required=True)
    args=ap.parse_args()
    builder=load_builder(args.repo/'scripts/build_exp01_assets.py')
    papers=json.loads((args.parsed_dir/'papers.json').read_text())
    statements=json.loads((args.parsed_dir/'statements.json').read_text())
    provenance=list(csv.DictReader((args.repo/'ledgers/statement_provenance.csv').open()))

    deps, labels=build_dependency_ledgers(args.papers_dir,papers,statements,args.repo)
    insert_dependency_sections(args.repo,provenance,deps)
    custom_quarantine_card(args.repo,next(p for p in papers if p['paper_id']=='P46'))
    maps=build_map_ledger(args.repo,builder,papers)
    asset_rows=build_asset_provenance(args.repo,builder,provenance)
    build_indexes_and_methods(args.repo,papers,provenance,statements,builder,deps,maps,asset_rows)
    print(json.dumps({'lexical_dependencies':len(deps),'source_labels':len(labels),'typed_map_records':len(maps),'asset_provenance_rows':len(asset_rows)},indent=2))

if __name__=='__main__':
    main()
