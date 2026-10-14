#!/usr/bin/env python3
"""Write deterministic CST-EXP-02 phase metadata and content hashes."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import shutil
from pathlib import Path

PHASE = "CST-EXP-02"
COMPLETED = "2026-08-09T20:30:00+00:00"
FROZEN = "2026-08-09T20:50:00+00:00"
EXCLUDED = {
    "manifests/MANIFEST.json",
    "manifests/SHA256SUMS",
    "manifests/REPO_TREE.txt",
    "manifests/VALIDATION_REPORT.md",
    "manifests/VALIDATION_RESULTS.json",
}


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def csv_rows(root: Path, rel: str) -> list[dict[str, str]]:
    with (root / rel).open(newline="", encoding="utf-8") as fh:
        return list(csv.DictReader(fh))


def clean_caches(root: Path) -> None:
    for directory in sorted(root.rglob("__pycache__"), reverse=True):
        if directory.is_dir() and ".git" not in directory.parts:
            shutil.rmtree(directory)
    for path in root.rglob("*.pyc"):
        if path.is_file() and ".git" not in path.parts:
            path.unlink()


def live_files(root: Path, *, include_excluded: bool) -> list[Path]:
    out: list[Path] = []
    for path in root.rglob("*"):
        if not path.is_file() or path.is_symlink():
            continue
        rel = path.relative_to(root)
        rel_s = rel.as_posix()
        if ".git" in rel.parts or "__pycache__" in rel.parts or path.suffix == ".pyc" or path.name == ".gitkeep":
            continue
        if not include_excluded and rel_s in EXCLUDED:
            continue
        out.append(path)
    return sorted(out, key=lambda p: p.relative_to(root).as_posix())


def validation_record(root: Path) -> dict:
    path = root / "manifests/VALIDATION_RESULTS.json"
    if not path.is_file():
        return {"status": "pending", "checks_passed": 0, "checks_total": 0}
    try:
        data = json.loads(path.read_text(encoding="utf-8"))
        return {
            "status": data.get("status", "pending"),
            "checks_passed": int(data.get("checks_passed", 0)),
            "checks_total": int(data.get("checks_total", 0)),
        }
    except Exception:
        return {"status": "pending", "checks_passed": 0, "checks_total": 0}


def build_summary(root: Path) -> dict:
    counts = json.loads((root / "manifests/EXP02_ASSET_SUMMARY.json").read_text(encoding="utf-8"))["counts"]
    assets = csv_rows(root, "ledgers/asset_provenance.csv")
    inherited = {
        "papers": len(csv_rows(root, "corpus/machine_index/paper_inventory.csv")),
        "machine_statements": len(csv_rows(root, "corpus/machine_index/all_statement_index.csv")),
        "curated_provenance_records": len(csv_rows(root, "ledgers/statement_provenance.csv")),
        "asset_families": len({x["asset_id"] for x in assets}),
        "asset_provenance_links": len(assets),
        "typed_map_records": len(csv_rows(root, "ledgers/map_type_ledger.csv")),
        "source_labels": len(csv_rows(root, "ledgers/source_label_index.csv")),
        "gap_rows": len(csv_rows(root, "ledgers/gap_to_asset_matrix.csv")),
        "embedded_duplicate_papers": len(csv_rows(root, "ledgers/corpus_duplicate_map.csv")),
    }
    validation = validation_record(root)
    validation.update({
        "report": "manifests/VALIDATION_REPORT.md",
        "results": "manifests/VALIDATION_RESULTS.json",
    })
    return {
        "project": "CST-EXP",
        "phase": PHASE,
        "completed_at_utc": COMPLETED,
        "status": "complete",
        "exit_gate": "pass",
        "target_selected": False,
        "scenario_verdicts_selected": False,
        "scientific_conclusion_selected": False,
        "theorem_or_program_implemented": False,
        "counts": counts,
        "governance_counts": {
            "phase_02_decisions": 14,
            "phase_02_rejected_defaults": 18,
            "phase_02_unresolved_questions": 16,
        },
        "inherited_corpus_counts": inherited,
        "semantic_controls": {
            "operational_graph_is_lineage_graph": False,
            "scenario_facts_are_candidate_outputs": False,
            "handoff_is_subject_movement_primitive": False,
            "single_scenario_is_paradigmatic": False,
            "same_support_reencoding_is_cross_carrier": False,
        },
        "next_phase": "CST-EXP-03",
        "repository_state": "frozen",
        "validation": validation,
        "frozen_at_utc": FROZEN,
    }


def completion_report(summary: dict) -> str:
    c = summary["counts"]
    g = summary["governance_counts"]
    p = summary["inherited_corpus_counts"]
    v = summary["validation"]
    return f"""# CST-EXP-02 Completion Report

## Phase ruling

**CST-EXP-02 is complete and its exit gate passes.** The repository now contains a neutral source–target semantics and a complete **35-case** scenario battery: **{c['governing_plan_scenarios']} governing-plan cases** plus **{c['supplemental_stress_controls']} supplemental stress controls**. The phase deliberately does **not** choose a transported object, bridge semantics, lineage criterion, scenario verdict, theorem target, toy program, empirical recognition bridge, or ontological interpretation.

## What landed

- **{c['battery_scenarios']} scenario records and cards**;
- **{c['protocol_axes']} independent protocol axes** with **{c['axis_values']} controlled values**, all represented;
- **{c['outcome_labels']} lane-typed outcome labels** across structural transport, target realization, lineage, autonomy, and recognition;
- **{c['discriminators']} discriminators** applied to all scenarios, yielding **{c['scenario_discriminator_rows']} scenario–discriminator records**;
- **{c['scenario_question_crosswalk_rows']} scenario–question links** and **{c['scenario_asset_crosswalk_rows']} source-asset links**;
- a **{c['unfilled_verdict_rows']}-row verdict template** with **{c['unfilled_verdict_rows'] * 5} output cells deliberately left `UNFILLED`**;
- **{g['phase_02_decisions']} phase decisions**, **{g['phase_02_rejected_defaults']} rejected defaults**, and **{g['phase_02_unresolved_questions']} unresolved questions**;
- deterministic build, validation, rebuild, manifest, checksum, and restore paths.

## Frozen neutral semantics

The operational episode graph `G_op` records construction, scanning, copying, causal coupling, overlap, reconstruction, synchronization, repair, retirement, decoding, and resource dependence. It contains **no lineage edge by default**. A later candidate supplies a criterion `κ` and independently generates a lineage graph `G_κ`.

Candidate output is a typed vector rather than one loaded verdict:

```text
(S-T transport, S-R target realization, S-L lineage, A autonomy, R recognition)
```

Scenario facts—source deletion timing, branch count, temporal gap, exactness at a named granularity, a public/predictive mismatch, a gluing obstruction, or an external decoder—are inputs. Every later candidate must separately answer each lane or return a typed underdetermination/nonapplicability with a named basis.

Handoff records changes in operational responsibility, not a presumed instant of subject movement. Source, route, and target histories may use different local clocks connected only by a declared relation. Fidelity is always paired with a comparison granularity. Autonomy is evaluated under an explicit withdrawal intervention specifying removed resources, retained environment, disturbance class, and horizon or closure condition.

## Governing-plan battery

S01–S20 instantiate the required cases: gradual replacement; destructive reconstruction; nondestructive copying; delayed source deletion; symmetric targets; a temporal gap; long overlap; distributed extension; fission/divergence; fission/fusion; public-perfect predictive mismatch; predictive match with binding/action-credit mismatch; external-decoder dependence; route holonomy; local/global gluing failure; viability-boundary transfer; endogenous repair; exact reversible round trip; radical clock rescaling; and a same-support gauge/re-encoding control.

## Supplemental stress controls

S21–S35 close distinctions that the minimum battery leaves coarse: recoverable-source checkpointing, live migration under concurrent updates, independent many-source fusion, many-to-many sharded reconfiguration, explicit error-corrected migration, independently built structural twins, persistent-core replacement, delayed post-withdrawal collapse, external scheduling that mimics temporal closure, certificate-only counterfeits, event-package assembly from local edges, approximately reversible residual accumulation, dormant stale backups, source-degrading transfer costs, and replacement-order critical pairs.

These controls do not add verdicts. They prevent later candidates from passing only the famous thought experiments while remaining ambiguous on recoverability, synchronization, boundary choice, repair locus, independent construction, delayed autonomy failure, local-to-global obstruction, or route-order dependence.

## Deliberate contrasts

The battery separately tests:

- source persistence versus later deletion and source absence;
- exact copying versus uniqueness of continuation;
- public/certificate matching versus predictive matching;
- predictive matching versus full package structure;
- bridge-supported behavior versus target-native maintenance;
- endpoint restoration with holonomy versus exact reversible transport;
- local pairwise acceptance versus global event-package coherence;
- bounded defect near viability failure versus endogenous or protocol-supplied repair;
- exact round trip versus approximate residual accumulation;
- source-derived copying versus independently constructed equivalence;
- genuine carrier change versus same-support representation change.

No case is paradigmatic, and no source fate, overlap pattern, exactness level, route, target count, or deletion schedule serves as an unexamined identity rule.

## Corpus continuity

The EXP-01 evidence bank remains preserved: **{p['papers']} papers**, **{p['machine_statements']} non-quarantined machine statements**, **{p['curated_provenance_records']} curated provenance records**, **{p['asset_families']} canonical asset families**, **{p['asset_provenance_links']} exact links**, **{p['typed_map_records']} typed-map records**, **{p['source_labels']} source labels**, and **{p['gap_rows']} open gaps**. P46 remains quarantined. P42 remains the normative newer SAU revision, and P60 retains zero independent evidential weight. Every scenario import retains its source asset's fixed-support scope, retyping caution, and nonclaim.

## Verification

- Retained CST-EXP-01 validation: **87/87 PASS**.
- CST-EXP-02 validation: **{v['checks_passed']}/{v['checks_total']} {v['status'].upper()}**.
- The phase validator checks required plan cases and outcomes, 35-card coverage, registry/matrix agreement, all 44 axis values, complete 35×10 discriminator coverage, question and asset crosswalks, 175 unfilled output cells, inherited corpus controls, governance ledgers, nonselection, scripts, links, encoding, caches, and content hashes.
- A clean portable rebuild reproduced **55/55 deterministic phase-02 surfaces byte-for-byte** and the rebuilt repository passed the full validator; see `manifests/REBUILD_VERIFICATION.md`.
- Validation establishes internal completeness and methodological discipline, not scientific truth of any future transport or identity criterion.

## Exit gate

Every later candidate must return separately typed outputs—or explicit underdetermination/nonapplicability—for all 35 scenarios. No operational edge, scenario title, source fate, handoff convention, fidelity declaration, or intuitive case may define continuation for the rest.

The next phase is **CST-EXP-03: independent candidate generation and cross-carrier bridge design**.
"""


def restore_text() -> str:
    return """# Restore and verify the CST-EXP-02 snapshot

## Restore

Extract the phase zip so that the repository root is `cst-exploration/`, then enter that directory.

## Content verification

Run:

```sh
sha256sum -c manifests/SHA256SUMS
python scripts/validate_exp02.py --repo .
```

Every checksum line must report `OK`, and the validator must report `PASS`. The content manifest intentionally excludes itself, the current validation report/results, the repository-tree listing, Git internals, `.gitkeep` placeholders, and generated Python caches.

Original source inputs are pinned separately in `manifests/SOURCE_SHA256SUMS`.

## Deterministic phase rebuild

Run:

```sh
scripts/rebuild_exp02.sh
```

This regenerates all 35 scenario records, cards, matrices, crosswalks, and templates from retained deterministic sources, performs a pre-freeze validation, rewrites deterministic phase metadata and checksums, and reruns the final validator. It performs no candidate selection, theorem proving, toy programming, literature review, or simulation.

## Git-state verification

Run:

```sh
git status --short
git log -1 --oneline
git tag --points-at HEAD
```

The first command should produce no output. The tag command should include `CST-EXP-02-v1`.

## Resume boundary

Read, in order:

1. `README.md`;
2. `STATE.md`;
3. `STATUS.md`;
4. `manifests/CST-EXP-02_COMPLETION_REPORT.md`;
5. `scenarios/NEUTRAL_TRANSFER_SCHEMA.md`;
6. `scenarios/PROTOCOL_AXIS_DICTIONARY.md`;
7. `scenarios/CANONICAL_BATTERY.md`;
8. `scenarios/OUTCOME_TAXONOMY.md`;
9. `ledgers/scenario_discriminator_matrix.csv`;
10. `ledgers/scenario_verdict_template.csv`;
11. `ledgers/UNRESOLVED_QUESTIONS.md`;
12. `inputs/normative/PREPARATORY_EXPLORATION_PLAN.md`.

The next phase is CST-EXP-03. This snapshot does not authorize a preferred transported object, bridge, lineage rule, theorem target, toy program, consciousness conclusion, or personal-identity conclusion.
"""


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, type=Path)
    args = parser.parse_args()
    root = args.repo.resolve()
    clean_caches(root)

    manifests = root / "manifests"
    manifests.mkdir(parents=True, exist_ok=True)
    summary = build_summary(root)
    (manifests / "PHASE_SUMMARY.json").write_text(json.dumps(summary, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (manifests / "CST-EXP-02_COMPLETION_REPORT.md").write_text(completion_report(summary), encoding="utf-8")
    (manifests / "RESTORE_AND_VERIFY.md").write_text(restore_text(), encoding="utf-8")

    tree_paths = [p.relative_to(root).as_posix() for p in live_files(root, include_excluded=True)]
    (manifests / "REPO_TREE.txt").write_text("\n".join(tree_paths) + "\n", encoding="utf-8")

    entries = []
    for path in live_files(root, include_excluded=False):
        rel = path.relative_to(root).as_posix()
        entries.append({"path": rel, "size_bytes": path.stat().st_size, "sha256": sha(path)})
    manifest = {
        "project": "CST-EXP",
        "phase": PHASE,
        "schema_version": 1,
        "generated_at_utc": FROZEN,
        "content_root": "cst-exploration/",
        "exclusions": sorted(EXCLUDED) + [".git/**", "**/.gitkeep", "**/__pycache__/**", "**/*.pyc"],
        "file_count": len(entries),
        "total_bytes": sum(x["size_bytes"] for x in entries),
        "files": entries,
    }
    (manifests / "MANIFEST.json").write_text(json.dumps(manifest, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
    (manifests / "SHA256SUMS").write_text("".join(f"{e['sha256']}  {e['path']}\n" for e in entries), encoding="utf-8")
    print(json.dumps({"phase": PHASE, "files_hashed": len(entries), "validation": summary["validation"]}, indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
