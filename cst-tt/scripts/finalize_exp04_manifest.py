#!/usr/bin/env python3
"""Freeze CST-EXP-04 phase summary, completion report, manifest, checksums, and tree."""
from __future__ import annotations
import hashlib, json, os
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
DATE='2026-08-10'
EXCLUDE_MANIFEST={
 'manifests/MANIFEST.json','manifests/SHA256SUMS','manifests/REPO_TREE.txt',
 'manifests/VALIDATION_REPORT.md','manifests/VALIDATION_RESULTS.json'
}
EXCLUDE_SUMS={'manifests/SHA256SUMS','manifests/VALIDATION_REPORT.md','manifests/VALIDATION_RESULTS.json'}

def files(root:Path):
    for p in sorted(root.rglob('*')):
        if not p.is_file() or '.git' in p.parts or '__pycache__' in p.parts or p.suffix=='.pyc': continue
        yield p

def sha(p:Path):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
    return h.hexdigest()

def write(p:Path,s:str):
    p.parent.mkdir(parents=True,exist_ok=True)
    clean='\n'.join(line.rstrip() for line in s.splitlines())
    p.write_text(clean.rstrip()+'\n',encoding='utf-8')

def main():
    root=ROOT
    phase_summary={
      'schema_version':'1.0','project':'CST-EXP','phase':'CST-EXP-04','state_version':'CST-EXP-04-v1','generated_date':DATE,
      'objective':'Adversarially stress all ten candidate schemas, mine precise no-go prospects, confront them with targeted external literature, and freeze a nontrivial survivor shortlist without selecting a final theorem target.',
      'counts':{
        'candidate_schemas_stressed':10,'hard_cases':18,'candidate_hard_case_records':180,'internal_sbt_lenses':13,'candidate_lens_records':130,
        'no_go_prospects':18,'external_sources':26,'external_crosswalk_rows':103,'red_team_positions':7,'survivor_families':3,
        'scenario_records_preserved':350,'assumption_exposure_records':200,'portable_rebuild_surfaces':85
      },
      'survivors':[
        {'id':'SF-01','title':'Integrated Autonomous Handoff','core':'TS-02','claim_lane':'target structural realization and autonomy'},
        {'id':'SF-02','title':'Causal-Overlap Process Lineage','core':'TS-03','claim_lane':'conservative live-process lineage'},
        {'id':'SF-03','title':'Relation-Valued Predictive Ancestry','core':'TS-10','claim_lane':'branching/fusion ancestry relation'},
      ],
      'component_roles':{
        'TS-01':'predictive-invariant component','TS-04':'autonomy/viability gate','TS-05':'optional encode/recover bridge mechanism',
        'TS-06':'global gluing gate','TS-07':'route/recombination audit','TS-08':'temporal/provenance gate','TS-09':'approximation/stability layer'
      },
      'validation':{'pre_manifest':'305/305 PASS','full_expected':'310/310 PASS after manifest freeze','portable_rebuild':'85/85 deterministic surfaces; rebuilt prevalidation 305/305 PASS'},
      'boundary':'No theorem or no-go was proved; no toy program was implemented; no final target was selected; no consciousness, survival, or personal-identity conclusion was made.'
    }
    write(root/'manifests/PHASE_SUMMARY.json',json.dumps(phase_summary,indent=2,sort_keys=True))
    completion=f"""# CST-EXP-04 Completion Report

**Phase:** CST-EXP-04 — adversarial stress, no-go mining, and external confrontation
**State version:** CST-EXP-04-v1
**Freeze date:** {DATE}
**Exit gate:** PASS subject to the frozen full validation report

## Completed work

- Applied 13 internal SBT adversarial lenses to all 10 CST-EXP-03 candidates: **130 complete audits**.
- Forced all candidates through the required 18 hard cases: **180 complete stress records**.
- Preserved all **350** phase-03 scenario verdicts byte-for-byte and added phase-04 interpretation without changing any lane output.
- Exposed all **200** candidate-assumption records, including A1, A2-P, certificate soundness, recognition, autonomy, route flatness, and identity interpretation.
- Formulated **18** finite-witness no-go/theorem prospects, each with assumptions, proof spine, falsifier, and nonclaim. None is represented as proved.
- Conducted a targeted current external-literature challenge pass with **26** retained primary/authoritative sources across organizational invariance, uploading, branching identity, WBE, enactivism, causal abstraction, consciousness theory, QEC, migration, distributed state, and observer duplication.
- Wrote **7** red-team reviews.
- Froze **3 unranked survivor families** and retained the other 7 candidates as gates, mechanisms, or approximation layers.

## Scientific result

The phase rejects a one-predicate notion of consciousness transfer. A plausible target must keep at least these components distinct:

1. integrated target structural realization;
2. source–target lineage or ancestry;
3. target-native post-withdrawal autonomy;
4. route, recombination, temporal, and approximation audits;
5. empirical recognition and ontological interpretation.

The survivors are:

- **SF-01 — Integrated Autonomous Handoff** (`TS-02` core; `TS-04/06/07/08/09` mandatory modules; `TS-05` optional mechanism);
- **SF-02 — Causal-Overlap Process Lineage** (`TS-03` core; `TS-04/07/08` mandatory modules);
- **SF-03 — Relation-Valued Predictive Ancestry** (`TS-10` core; `TS-01/07/09` mandatory modules).

They are not ranked. SF-01 may later pair with either lineage family. SF-02 and SF-03 deliberately disagree on some destructive-copy, temporal-gap, and ancestry cases.

## Strongest no-go prospects

The most promising negative targets concern public-shadow nonidentifiability, symmetric-duplication impossibility, branchwise/recombination separation, decoder dependence versus autonomy, route holonomy and bridge noncongruence, local-to-global obstruction, and global-residual/local-catastrophe separation.

## Verification

- Pre-manifest phase validator: **305/305 PASS**.
- Portable rebuild from the committed CST-EXP-03 tree: **85/85 deterministic surfaces reproduced byte-for-byte**; rebuilt pre-validation **305/305 PASS**.
- Full frozen-repository validator: see `manifests/VALIDATION_REPORT.md`.
- Inherited CST-EXP-03 candidate registry, scenario ledger, assumption matrix, question bank, anti-conflation bank, primitive registry, scenario registry, and corpus statement bank remain byte-frozen against `manifests/CST-EXP-03_MANIFEST.json`.

## Boundary

No theorem or no-go was proved. No Lean development, toy program, full Six Birds simulation, or empirical recognition protocol was implemented. No target consciousness, personal survival, numerical identity, or A2 carrier-invariance conclusion was established.

The next authorized phase is **CST-EXP-05 — theorem and toy-program reconnaissance**.
"""
    write(root/'manifests/CST-EXP-04_COMPLETION_REPORT.md',completion)
    restore="""# Restore and Verify CST-EXP-04

From the extracted repository root:

```bash
git status --short
python scripts/validate_exp04.py
python scripts/verify_exp04_rebuild.py
sha256sum -c manifests/SHA256SUMS
```

Expected phase validation: `PASS 310/310` after the manifest is frozen.
Expected portable rebuild: `PASS 85 surfaces` and rebuilt pre-validation `PASS 305/305`.

The archive contains the full Git history. The phase tag is `CST-EXP-04-v1` after final freeze.
"""
    write(root/'manifests/RESTORE_AND_VERIFY.md',restore)

    # Repository tree is generated before the manifest/sums, then regenerated once at the end.
    tree=[str(p.relative_to(root)) for p in files(root)]
    write(root/'manifests/REPO_TREE.txt','\n'.join(tree))

    entries=[]
    for p in files(root):
        rel=str(p.relative_to(root))
        if rel in EXCLUDE_MANIFEST: continue
        entries.append({'path':rel,'bytes':p.stat().st_size,'sha256':sha(p)})
    man={
      'schema_version':'1.0','project':'CST-EXP','phase':'CST-EXP-04','generated_date':DATE,
      'scope':'all non-Git, non-cache repository files except dynamic validation/manifest surfaces',
      'excluded':sorted(EXCLUDE_MANIFEST),'file_count':len(entries),'files':entries
    }
    write(root/'manifests/MANIFEST.json',json.dumps(man,indent=2,sort_keys=True))

    # Regenerate tree now that all static manifest surfaces exist.
    tree=[str(p.relative_to(root)) for p in files(root)]
    write(root/'manifests/REPO_TREE.txt','\n'.join(tree))
    sums=[]
    for p in files(root):
        rel=str(p.relative_to(root))
        if rel in EXCLUDE_SUMS: continue
        sums.append(f"{sha(p)}  {rel}")
    write(root/'manifests/SHA256SUMS','\n'.join(sums))
    print(f"Frozen manifest with {len(entries)} files; SHA256SUMS has {len(sums)} rows")

if __name__=='__main__': main()
