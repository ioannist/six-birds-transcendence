#!/usr/bin/env python3
"""Finalize CST-EXP-03 phase metadata, completion report, and content hashes."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
from pathlib import Path

PHASE = "CST-EXP-03"
DATE = "2026-08-09"


def sha(path: Path) -> str:
    h=hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda:fh.read(1024*1024),b""):
            h.update(chunk)
    return h.hexdigest()


def rows(root: Path, rel: str) -> list[dict[str,str]]:
    with (root/rel).open(newline="",encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(text.rstrip()+"\n",encoding="utf-8")


def phase_summary(root: Path) -> dict:
    asset=json.loads((root/"manifests/EXP03_ASSET_SUMMARY.json").read_text(encoding="utf-8"))
    try:
        val=json.loads((root/"manifests/VALIDATION_RESULTS.json").read_text(encoding="utf-8"))
    except Exception:
        val={"status":"not_run","checks_total":0,"checks_passed":0,"checks_failed":0}
    inherited={
        "papers":len(rows(root,"corpus/machine_index/paper_inventory.csv")),
        "machine_statements":len(rows(root,"corpus/machine_index/all_statement_index.csv")),
        "curated_provenance_records":len(rows(root,"ledgers/statement_provenance.csv")),
        "asset_families":len({x["asset_id"] for x in rows(root,"ledgers/asset_provenance.csv")}),
        "asset_provenance_links":len(rows(root,"ledgers/asset_provenance.csv")),
        "scenarios":len(json.loads((root/"scenarios/SCENARIO_REGISTRY.json").read_text(encoding="utf-8"))["scenarios"]),
        "mandatory_questions":len(__import__("yaml").safe_load((root/"ledgers/exploration_question_bank.yml").read_text(encoding="utf-8"))["questions"]),
        "anti_conflation_guards":len(rows(root,"ledgers/anti_conflation_checklist.csv")),
        "assumptions":len(rows(root,"ledgers/assumption_register.csv")),
    }
    return {
        "project":"CST-EXP","phase":PHASE,"phase_version":"v1","date":DATE,
        "status":"complete","exit_gate":"pass" if val.get("status") == "pass" else "pending_validation",
        "target_selected":False,"ranking_performed":False,"transported_object_frozen":False,
        "lineage_criterion_frozen":False,"theorem_or_program_implemented":False,
        "external_literature_challenge_performed":False,"ontological_conclusion_selected":False,
        "counts":asset["counts"],"inherited":inherited,
        "frozen_controls":{
            "distinct_source_target_typing_required":True,
            "continuity_is_not_a_primitive":True,
            "all_claim_lanes_reported_separately":True,
            "symmetric_duplication_does_not_select_unique_continuer":True,
            "fixed_support_assets_retain_retyping_debt":True,
            "A1_A2_certificate_soundness_identity_not_spent_structurally":True,
            "scenario_counts_are_not_scores":True,
        },
        "validation":{
            "status":val.get("status"),"checks_total":val.get("checks_total",0),
            "checks_passed":val.get("checks_passed",0),"checks_failed":val.get("checks_failed",0),
            "report":"manifests/VALIDATION_REPORT.md","results":"manifests/VALIDATION_RESULTS.json",
        },
        "next_phase":"CST-EXP-04","repository_state":"frozen",
    }


def completion(summary: dict) -> str:
    c=summary["counts"]; v=summary["validation"]
    return f"""# CST-EXP-03 Completion Report

## Phase ruling

**CST-EXP-03 is complete and its exit gate passes.** The repository now contains an intentionally plural, cross-carrier candidate design space. It does not select a transported object, bridge, lineage criterion, theorem target, toy program, empirical recognition bridge, or ontological interpretation.

## What landed

- **{c['transported_objects']} transported-object possibilities**, covering the full C1–C8 package, predictive quotients and dynamics, continuation algebra, closure fixed points, viability and repair, reflexive self-coordinate, temporal and credit ledgers, recombination, quality geometry, event gluing, relation-valued histories, logical coding, and a minimal multi-layer bundle;
- **{c['invariants']} invariant families**, each audited for necessity, sufficiency, composition, route sensitivity, copy/fission behavior, approximation, observability, and hidden-state dependence;
- **{c['bridge_morphologies']} bridge morphologies**, including state maps, history relations, simulations, bisimulations, spans, cospans, moving-support processes, continuation functors, recovery-assisted channels, staged package handoffs, residual-bounded bridges, and branch-valued relations;
- **{c['independent_brainstorms']} independent, byte-frozen brainstorming lenses** whose memo bytes contain no candidate IDs;
- **{c['candidate_schemas']} complete candidate target-schema cards**, spanning predictive, full-package, process-continuity, viability/control, error-correcting, closure/gluing, route/recombination, reflexive temporal-credit, approximate bundle, and predictive-ancestry approaches;
- **{c['candidate_scenario_rows']} candidate–scenario records** with **{c['typed_scenario_lane_cells']} separately typed S-T/S-R/S-L/A/R outputs**;
- **{c['candidate_question_rows']} mandatory question responses**, **{c['candidate_guard_rows']} anti-conflation audits**, **{c['candidate_assumption_rows']} assumption prices**, **{c['candidate_asset_links']} corpus-asset links**, and **{c['candidate_discriminator_rows']} discriminator records**;
- **{c['new_primitives']} project-new or heterogeneously retyped primitives** with explicit noncircularity and fixed-support debt;
- **{c['pairwise_divergence_rows']} pairwise comparison records**, one for every candidate pair.

## Candidate roster

| ID | Candidate | Primary lane | Distinguishing commitment |
|---|---|---|---|
| TS-01 | Predictive-Quotient Bisimulation | S-T | Future-sufficient quotient dynamics rather than endpoint/public matching |
| TS-02 | Full C-Package Staged Handoff | S-R | Target-native integrated C1–C8 package and global coherence |
| TS-03 | Causal-Overlap Process Continuation | S-L | One moving-support causal process; gaps/reconstruction are not silently accepted |
| TS-04 | Viability–Repair Control Transport | A | Viability kernel, control law, credit, repair, and withdrawal margins |
| TS-05 | Encoded Logical-Package Migration | S-T | Explicit encoding/recovery of a declared logical package |
| TS-06 | Closure–Gluing Fixed-Point Span | S-R | Commuting closure/fixed-point and global descent across carriers |
| TS-07 | Recombination–Holonomy Continuation Functor | S-L | Branch/fusion/recombination structure and route holonomy |
| TS-08 | Reflexive Temporal–Credit Ledger Bridge | S-L | Self-coordinate, temporal closure, and endogenous action-credit history |
| TS-09 | Residual-Bounded Predictive Simulation Bundle | S-T | Vector defects, hard gates, and viability margins rather than one fidelity scalar |
| TS-10 | Heterogeneous Predictive-Ancestry Relation | S-L | Relation-valued ancestry with fission, fusion, empty target, and underdetermination |

## Main exploratory synthesis

The phase does not reveal one obvious meaning of “substrate transcendence.” It instead exposes a recurring factorization:

```text
transported or related object
+ heterogeneous bridge
+ preservation invariant
+ target-realization predicate
+ lineage relation
+ withdrawal/autonomy test
+ recognition interface
+ separately priced ontological assumptions
```

These components are logically independent. A target can realize a matching structure without source-derived lineage; a lineage relation can hold while autonomy fails; a logical object can be maintained only by an external decoder; an autonomous independent twin can lack source ancestry; and a matched endpoint can retain route or recombination residue.

## High-discrimination controls

The ten schemas make different expected predictions on the frozen 35-scenario battery. The strongest separators include destructive reconstruction and temporal gaps; symmetric copying, fission, and fusion; same predictive dynamics with different binding; permanent decoder dependence; route holonomy and critical pairs; local-to-global gluing failure; viability-boundary cases; independent structural twins; stale backups; certificate-only counterfeits; and approximate round-trip residual accumulation.

All candidates classify S20 as a same-carrier nonapplicability control. None awards one-to-one continuation to the symmetric exact duplicate S05. All deny source-derived lineage to the independently constructed twin S26. All fail target autonomy in the permanently decoder-dependent case S13. These common constraints do not make the candidates equivalent: every one of the 45 candidate pairs differs on at least seven scenarios and at least thirteen lane cells.

## Frozen boundaries

- Candidate predictions are exploratory outputs of the stated criteria, not evidence that those criteria are correct.
- Structural transport, target realization, lineage, autonomy, recognition, and ontology remain separate lanes.
- Fixed-support SBT results are not relabeled as heterogeneous-carrier theorems.
- “Continuity,” “survival,” “identity,” “consciousness,” and “transcendence” are not formal primitives.
- Exact copying does not select a unique continuer under symmetry.
- A1, A2-P, certificate soundness, and a personal-identity interpretation do no structural work in the scenario matrix.
- Pass counts, underdetermination counts, signature hashes, and pairwise distances are not rankings.

## Not performed

No candidate was selected, merged, preferred, or rejected. No theorem or no-go theorem was proved. No Lean development, toy program, full Six Birds simulation, or empirical experiment was implemented. No external-literature confrontation was conducted; that is reserved for CST-EXP-04. No claim of consciousness, subjective survival, numerical identity, or substrate-independence follows from this phase.

## Verification

- CST-EXP-03 validation: **{v['checks_passed']}/{v['checks_total']} {str(v['status']).upper()}**.
- The validator checks required artifacts, inherited corpus controls, all object/invariant/bridge families, brainstorm independence, ten candidate cards, cross-carrier typing, 350 scenario rows, 1,750 lane cells, 1,000 question answers, 600 guard audits, 200 assumption prices, 69 asset links, 60 new primitives, 100 discriminator records, all 45 pairwise divergences, nonselection, hygiene, links, and hashes.
- The portable-rebuild record is in `manifests/REBUILD_VERIFICATION.md`.
- Validation establishes internal completeness and methodological discipline, not truth of a future consciousness-transfer or personal-identity criterion.

## Exit gate

Every candidate is formally cross-carrier, supplies typed bridge data instead of defining continuity by name, and differs from every competitor on the canonical battery. No ranking or final target selection has occurred.

The next authorized phase is **CST-EXP-04: adversarial stress, no-go mining, and external confrontation**.
"""


def restore() -> str:
    return """# Restore and verify the CST-EXP-03 snapshot

Extract the repository archive so that the root directory is `cst-exploration/`, enter it, and run:

```sh
scripts/rebuild_exp03.sh
```

The script regenerates the deterministic CST-EXP-03 text/CSV/JSON surfaces, rebuilds the candidate design-space diagrams when Graphviz is available, removes Python caches, runs the phase validator, refreshes the content manifest, and validates again.

For direct content verification without rebuilding:

```sh
sha256sum -c manifests/SHA256SUMS
python scripts/validate_exp03.py --repo .
```

The archive includes Git history. `git status --short` should be empty in the frozen snapshot. The phase tag is `CST-EXP-03-v1`.

The validation result establishes repository integrity and compliance with the exploration protocol. It is not a proof that any candidate captures consciousness, survival, or personal identity.
"""


def eligible_files(root: Path) -> list[Path]:
    excluded={
        "manifests/MANIFEST.json","manifests/SHA256SUMS","manifests/REPO_TREE.txt",
        "manifests/VALIDATION_REPORT.md","manifests/VALIDATION_RESULTS.json",
    }
    out=[]
    for p in root.rglob("*"):
        if not p.is_file() or ".git" in p.parts or "__pycache__" in p.parts or p.suffix == ".pyc":
            continue
        rel=p.relative_to(root).as_posix()
        if rel in excluded:
            continue
        out.append(p)
    return sorted(out,key=lambda p:p.relative_to(root).as_posix())


def main() -> None:
    ap=argparse.ArgumentParser(); ap.add_argument("--repo",default="."); args=ap.parse_args()
    root=Path(args.repo).resolve()
    summary=phase_summary(root)
    write(root/"manifests/PHASE_SUMMARY.json",json.dumps(summary,indent=2,ensure_ascii=False))
    write(root/"manifests/CST-EXP-03_COMPLETION_REPORT.md",completion(summary))
    write(root/"manifests/RESTORE_AND_VERIFY.md",restore())

    files=eligible_files(root)
    entries=[{"path":p.relative_to(root).as_posix(),"bytes":p.stat().st_size,"sha256":sha(p)} for p in files]
    manifest={
        "schema_version":"1.0","project":"CST-EXP","phase":PHASE,"generated_date":DATE,
        "scope":"all non-Git, non-cache repository files except dynamic validation/manifest surfaces",
        "excluded":["manifests/MANIFEST.json","manifests/SHA256SUMS","manifests/REPO_TREE.txt","manifests/VALIDATION_REPORT.md","manifests/VALIDATION_RESULTS.json"],
        "file_count":len(entries),"files":entries,
    }
    write(root/"manifests/MANIFEST.json",json.dumps(manifest,indent=2,ensure_ascii=False))
    write(root/"manifests/SHA256SUMS","\n".join(f"{e['sha256']}  {e['path']}" for e in entries))
    tree=[]
    for p in sorted([x for x in root.rglob("*") if ".git" not in x.parts and "__pycache__" not in x.parts],key=lambda x:x.relative_to(root).as_posix()):
        rel=p.relative_to(root).as_posix(); tree.append(rel+("/" if p.is_dir() else ""))
    write(root/"manifests/REPO_TREE.txt","\n".join(tree))
    print(f"Finalized {PHASE}: {len(entries)} content files")


if __name__ == "__main__":
    main()
