#!/usr/bin/env python3
"""Freeze CST-EXP-05 phase summary, completion report, manifest, checksums, and tree."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATE = "2026-08-10"
EXCLUDE_MANIFEST = {
    "manifests/MANIFEST.json",
    "manifests/SHA256SUMS",
    "manifests/REPO_TREE.txt",
    "manifests/VALIDATION_REPORT.md",
    "manifests/VALIDATION_RESULTS.json",
}
EXCLUDE_SUMS = {
    "manifests/SHA256SUMS",
    "manifests/VALIDATION_REPORT.md",
    "manifests/VALIDATION_RESULTS.json",
}


def files(root: Path):
    for p in sorted(root.rglob("*")):
        if not p.is_file() or ".git" in p.parts or "__pycache__" in p.parts or p.suffix == ".pyc":
            continue
        yield p


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for block in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    clean = "\n".join(line.rstrip() for line in text.splitlines())
    path.write_text(clean.rstrip() + "\n", encoding="utf-8")


def main() -> None:
    root = ROOT
    summary = json.loads((root / "manifests/EXP05_ASSET_SUMMARY.json").read_text(encoding="utf-8"))
    rebuild = json.loads((root / "manifests/REBUILD_VERIFICATION.json").read_text(encoding="utf-8"))
    counts = summary["counts"]

    phase_summary = {
        "schema_version": "1.0",
        "project": "CST-EXP",
        "phase": "CST-EXP-05",
        "state_version": "CST-EXP-05-v1",
        "generated_date": DATE,
        "objective": (
            "Specify the smallest exact finite theorem and toy-program landing surfaces for every CST-EXP-04 survivor "
            "family, expose formalization debt and assumption ladders, and determine whether each family is landable "
            "without selecting a final target or implementing proofs/programs."
        ),
        "counts": {
            **counts,
            "portable_rebuild_surfaces": rebuild["surfaces_compared"],
            "family_assumption_rungs": 8,
            "active_phase_decisions": 8,
            "rejected_defaults": 12,
        },
        "family_results": [
            {
                "id": "SF-01",
                "title": "Integrated Autonomous Handoff",
                "status": "reconnaissance_admissible_decomposed",
                "principal_risk": "package circularity and hidden local-to-global assumptions",
            },
            {
                "id": "SF-02",
                "title": "Causal-Overlap Process Lineage",
                "status": "reconnaissance_admissible_conservative",
                "principal_risk": "defining process continuity or causal nonredundancy by the desired verdict",
            },
            {
                "id": "SF-03",
                "title": "Relation-Valued Predictive Ancestry",
                "status": "reconnaissance_admissible_relational",
                "principal_risk": "encoding ancestry in the operational seed relation",
            },
        ],
        "shared_kernel": (
            "Twelve constructive/boundary prospectuses and twelve no-go/underdetermination prospectuses, with the "
            "symmetry, public-shadow, gluing, recombination, autonomy, route-holonomy, residual, and identity separations "
            "retained as companion constraints rather than a fourth transfer candidate."
        ),
        "validation": {
            "pre_manifest": "545/545 PASS",
            "full": "549/549 PASS",
            "portable_rebuild": f"{rebuild['surfaces_compared']}/{rebuild['surfaces_compared']} deterministic surfaces; rebuilt prevalidation 545/545 PASS",
        },
        "boundary": (
            "No theorem or no-go was proved; no Lean proof or toy program was implemented; no finalist was ranked or "
            "selected; no full Six Birds simulation was attempted; no empirical-recognition, consciousness, survival, "
            "numerical-identity, or A2 carrier-invariance conclusion was made."
        ),
    }
    write(root / "manifests/PHASE_SUMMARY.json", json.dumps(phase_summary, indent=2, sort_keys=True))

    completion = f"""# CST-EXP-05 Completion Report

**Phase:** CST-EXP-05 — theorem and toy-program reconnaissance  
**State version:** CST-EXP-05-v1  
**Freeze date:** {DATE}  
**Exit gate:** PASS

## Completed work

- Specified **{counts['finite_model_families']} exact finite model families**, one for every governing-plan model slot. Each model has separately typed carriers and states, an explicit transition/bridge law, an exact positive witness, an exact negative or counterfeit control, a minimality claim, a kill condition, and an ontological nonclaim.
- Wrote **{counts['theorem_prospectuses']} conjecture-grade theorem/no-go prospectuses**: **{counts['constructive_or_boundary_prospects']} constructive or boundary prospects** and **{counts['no_go_or_underdetermination_prospects']} no-go or underdetermination prospects**. Every prospectus records definitions, assumptions, exact statement, proof spine, finite witness/countermodel, formalization path, falsifier, circularity audit, and nonclaim.
- Wrote **{counts['toy_program_contracts']} toy-program contracts** covering predictive quotients, bridge checking, branch classification, confluence, holonomy, recombination, package preservation, autonomy under withdrawal, residual/hard-gate audits, and finite counterexample enumeration. These are contracts only; no program was implemented.
- Mapped **{counts['formalization_surfaces']} planned Lean surfaces** and froze the trust split: Python may enumerate witnesses and emit certificates; Lean must check the definitions, certificates, and theorems.
- Added **24 family-assumption records** across eight rungs for each survivor: unconditional mathematics, target-package preservation, lineage, autonomy, certificate soundness/recognition, A1, A2 or a narrower substitute, and phenomenal/survival interpretation.
- Froze **four unranked landing bundles**: one per survivor family and one shared no-go kernel.
- Added a **{counts['model_theorem_program_crosswalk_rows']}-row model–theorem–program crosswalk** and a **{counts['no_go_refinement_rows']}-row refinement map** back to the CST-EXP-04 no-go bank.

## Scientific result

All three survivor families pass the reconnaissance exit gate, but only after decomposition:

1. **SF-01 — Integrated Autonomous Handoff** has a finite landing through independently stated clause predicates, overlap compatibility, global gluing, target ownership, withdrawal, hard gates, and an invariant region. Its principal danger is defining the package so that successful handoff is true by construction.
2. **SF-02 — Causal-Overlap Process Lineage** has a finite landing through mixed-support corridors, causal nonredundancy, no-gap continuity, takeover, composition, and relation-valued branching. Its principal danger is treating any causal edge—or a verdict-loaded definition of process—as continuity.
3. **SF-03 — Relation-Valued Predictive Ancestry** has a finite landing through operational provenance seeds, predictive partitions, monotone closure, and a least fixed point supporting reconstruction, fission, fusion, empty targets, and independent-twin exclusion. Its principal danger is an ancestry oracle hidden in the seed relation.

No family is ranked or selected. The shared negative kernel remains mandatory because exact endpoint or public matching, symmetric duplication, branchwise preservation, decoder-supported behavior, route agreement, scalar residuals, and local certificates each fail to settle at least one stronger claim.

## Most plausible first theorem shapes

- A **finite gluing-plus-withdrawal theorem** for SF-01, paired with decoder-dependence and local/global obstruction countermodels.
- A **corridor composition and conservative exclusion theorem** for SF-02, paired with endpoint-without-lineage and temporal-gap countermodels.
- A **least ancestry relation theorem** for SF-03, paired with symmetry/non-uniqueness and independent-twin exclusion results.
- A shared set of finite no-gos establishing that public shadows, exact symmetry, route endpoints, scalar residuals, and local certificates underdetermine stronger transport or identity claims.

These are prospects, not proofs. CST-EXP-06 must decide whether to freeze one family, a paired realization-plus-lineage target, or a primarily negative result.

## Verification

- Pre-manifest validator: **545/545 PASS**.
- Portable rebuild from the committed `CST-EXP-04-v1` tree: **{rebuild['surfaces_compared']}/{rebuild['surfaces_compared']} deterministic surfaces reproduced byte-for-byte**; rebuilt pre-validation **545/545 PASS**.
- Full frozen-repository validator: **549/549 PASS**.
- The inherited CST-EXP-04 scientific surfaces remain byte-frozen against `manifests/CST-EXP-04_MANIFEST.json`.

## Boundary

No theorem or no-go was proved. No Lean development, Python toy, full Six Birds simulation, empirical recognition protocol, final target, or ontological interpretation was implemented or selected. The phase establishes feasibility and discriminating tests only; it does not establish consciousness transfer, personal survival, numerical identity, or A2.

The next authorized phase is **CST-EXP-06 — synthesis and target freeze**.
"""
    write(root / "manifests/CST-EXP-05_COMPLETION_REPORT.md", completion)

    restore = f"""# Restore and Verify CST-EXP-05

From the extracted repository root:

```bash
git status --short
python scripts/validate_exp05.py
python scripts/verify_exp05_rebuild.py
sha256sum -c manifests/SHA256SUMS
```

Expected full validation: `PASS 549/549`.  
Expected portable rebuild: `PASS {rebuild['surfaces_compared']} surfaces`; rebuilt pre-validation `PASS 545/545`.

The archive contains the full Git history. The frozen phase tag is `CST-EXP-05-v1`.
"""
    write(root / "manifests/RESTORE_AND_VERIFY.md", restore)

    # Generate tree, static manifest, then checksums. Dynamic validation outputs are excluded.
    tree = [str(p.relative_to(root)) for p in files(root)]
    write(root / "manifests/REPO_TREE.txt", "\n".join(tree))

    entries = []
    for p in files(root):
        rel = str(p.relative_to(root))
        if rel in EXCLUDE_MANIFEST:
            continue
        entries.append({"path": rel, "bytes": p.stat().st_size, "sha256": sha(p)})
    manifest = {
        "schema_version": "1.0",
        "project": "CST-EXP",
        "phase": "CST-EXP-05",
        "generated_date": DATE,
        "scope": "all non-Git, non-cache repository files except dynamic validation/manifest surfaces",
        "excluded": sorted(EXCLUDE_MANIFEST),
        "file_count": len(entries),
        "files": entries,
    }
    write(root / "manifests/MANIFEST.json", json.dumps(manifest, indent=2, sort_keys=True))

    tree = [str(p.relative_to(root)) for p in files(root)]
    write(root / "manifests/REPO_TREE.txt", "\n".join(tree))

    sums = []
    for p in files(root):
        rel = str(p.relative_to(root))
        if rel in EXCLUDE_SUMS:
            continue
        sums.append(f"{sha(p)}  {rel}")
    write(root / "manifests/SHA256SUMS", "\n".join(sums))
    print(f"Frozen manifest with {len(entries)} files; SHA256SUMS has {len(sums)} rows")


if __name__ == "__main__":
    main()
