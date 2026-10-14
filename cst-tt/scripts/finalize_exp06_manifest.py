#!/usr/bin/env python3
"""Freeze CST-EXP-06 summary, completion report, manifest, checksums, and tree."""
from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATE = "2026-08-10"
PRE_CHECKS = 1428
FULL_CHECKS = 1440
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
    asset = json.loads((root / "manifests/EXP06_ASSET_SUMMARY.json").read_text(encoding="utf-8"))
    rebuild = json.loads((root / "manifests/REBUILD_VERIFICATION.json").read_text(encoding="utf-8"))
    pre = json.loads((root / "manifests/CST-EXP-06_PREVALIDATION_RESULTS.json").read_text(encoding="utf-8"))
    counts = asset["counts"]
    if pre.get("status") != "pass" or pre.get("checks") != PRE_CHECKS:
        raise RuntimeError(f"unexpected prevalidation state: {pre.get('status')} {pre.get('checks')}")
    if rebuild.get("status") != "pass":
        raise RuntimeError("portable rebuild did not pass")

    phase_summary = {
        "schema_version": "1.0",
        "project": "CST-EXP",
        "phase": "CST-EXP-06",
        "state_version": "CST-EXP-06-v1",
        "generated_date": DATE,
        "objective": (
            "Compare the surviving finite architectures under hard gates and soft criteria, conduct the final "
            "copy-versus-continuation audit, freeze a narrow primary target and a substantive fallback, and hand "
            "off a fully specified later theorem-and-toy landing without implementing it."
        ),
        "primary_target": {
            "id": "FT-01",
            "code": "FIACH",
            "title": "Finite Integrated Autonomous Causal Handoff",
            "status": "frozen_for_later_implementation",
            "soft_score": asset["soft_totals"]["FT-01"],
            "claim_lanes": ["S-R", "S-L", "A"],
        },
        "fallback_target": {
            "id": "FT-02",
            "code": "IAPS",
            "title": "Integrated Autonomous Predictive Successorship",
            "status": "frozen_fallback",
            "soft_score": asset["soft_totals"]["FT-02"],
            "claim_lanes": ["S-R", "S-L", "A"],
        },
        "mandatory_companion": {
            "id": "FT-NG",
            "title": "Shared finite no-go and underdetermination kernel",
            "status": "mandatory_companion_and_terminal_fallback",
        },
        "counts": {
            **counts,
            "portable_rebuild_surfaces": rebuild["surfaces_compared"],
            "pre_manifest_validation_checks": PRE_CHECKS,
            "full_validation_checks": FULL_CHECKS,
        },
        "decision": (
            "FIACH is primary because it is the narrowest nontrivial architecture that separately but jointly "
            "establishes target realization, live source-target structural lineage, and post-withdrawal autonomy, "
            "while exact detached copying can hold endpoint/package/autonomy facts fixed and still fail its interior "
            "mixed-process condition. IAPS is fallback because it retains target realization and autonomy while "
            "permitting source-derived destructive reconstruction as relation-valued structural successorship."
        ),
        "validation": {
            "pre_manifest": f"{PRE_CHECKS}/{PRE_CHECKS} PASS",
            "full_expected_and_verified_after_freeze": f"{FULL_CHECKS}/{FULL_CHECKS} PASS",
            "portable_rebuild": f"{rebuild['surfaces_compared']}/{rebuild['surfaces_compared']} deterministic surfaces; rebuilt prevalidation {PRE_CHECKS}/{PRE_CHECKS} PASS",
        },
        "boundary": (
            "No theorem or no-go is proved; no Lean proof or toy program is implemented; no full Six Birds "
            "simulation or empirical recognition protocol is run; and no consciousness, personal-survival, "
            "numerical-identity, certificate-soundness, A1, or A2-P conclusion is made."
        ),
    }
    write(root / "manifests/PHASE_SUMMARY.json", json.dumps(phase_summary, indent=2, sort_keys=True))

    completion = f"""# CST-EXP-06 Completion Report

**Phase:** CST-EXP-06 — synthesis, target freeze, and landing brief  
**State version:** CST-EXP-06-v1  
**Freeze date:** {DATE}  
**Exit gate:** PASS

## Frozen decision

The primary later theorem-and-toy target is **FT-01 / FIACH — Finite Integrated Autonomous Causal Handoff**. For distinct finite carriers, it requires three separately checkable fields:

1. independently defined local clause witnesses glue into one target-owned integrated package;
2. a no-gap mixed-support causal corridor, containing at least one counterfactually nonredundant source-and-target update, supplies live structural lineage and reaches target takeover; and
3. the target package remains inside a target-owned controlled invariant region after the source, bridge, decoder, scheduler, and undeclared repair support are withdrawn.

FIACH is a relation, not a function or identity predicate. A valid symmetric live fork may relate the source to both targets. Detached destructive reconstruction fails the primary live-corridor field even when endpoint package and autonomy match.

The frozen fallback is **FT-02 / IAPS — Integrated Autonomous Predictive Successorship**. It reuses the package and autonomy fields but replaces live-overlap lineage with the least no-ex-nihilo relation generated by operational provenance and predictive compatibility. It may classify a source-derived destructive reconstruction as a structural successor, excludes a disconnected independent twin, and remains branch-valued under exact copying. It does not assert unique identity.

The **FT-NG finite no-go kernel** is mandatory under either target and becomes the terminal landing if both constructive lineage engines fail their noncircularity or nonvacuity gates.

## Phase assets

- Compared **{counts['finalist_architectures']} architectures** under **{counts['hard_gates']} hard gates** and **{counts['soft_criteria']} weighted soft criteria**, producing **{counts['scorecard_records']} scorecard records**.
- Froze **{counts['target_scenario_records']} typed target-scenario records**: thirty-five canonical scenarios for FIACH and thirty-five for IAPS.
- Froze **{counts['primary_theorem_targets']} primary** and **{counts['fallback_theorem_targets']} fallback** conjecture-grade theorem/no-go targets.
- Froze **{counts['frozen_witnesses_controls']} exact witness/control contracts**, including live handoff, detached copy, decoder shadow, independent twin, symmetric fission, fusion/recombination conflict, route holonomy, public shadows, and hard-gate residual counterfeits.
- Completed the explicit copy-versus-continuation audit: exact duplication, fission, uniqueness, destructive reconstruction, gradual replacement, autonomy, and the structural claim ceiling are each answered separately.
- Wrote a self-contained exploration dossier and a bounded later landing handoff with theorem order, toy contracts, controls, switch conditions, and no requirement for a full Six Birds simulation.
- Added **{counts['phase_decisions']} final decisions**, **{counts['phase_rejected_defaults']} rejected defaults**, and **{counts['retained_implementation_questions']} retained implementation questions.

## Why FIACH rather than IAPS first

The weighted totals are close—FIACH `{asset['soft_totals']['FT-01']:.1f}/100`, IAPS `{asset['soft_totals']['FT-02']:.1f}/100`—and are explicitly not evidence. FIACH is selected because interior process history performs indispensable work: two episodes can agree on target state, package, public behavior, and autonomy while only the live staged episode contains the required mixed nonredundant corridor. This is the narrowest finite structural meaning of “move” that survived the adversarial battery. IAPS is retained because source-derived destructive reconstruction is an important exact case that FIACH intentionally excludes rather than misclassifies.

## Later landing

The later project should build no-go microtheorems and exact countermodels first, freeze independent package/corridor/autonomy definitions, implement certificate-producing finite checkers, prove gluing/composition/invariance lemmas, and only then attempt the combined FIACH certificate theorem. It switches to IAPS only for a documented scientific failure of the live-corridor engine, not because the proof is difficult. Python may enumerate and emit certificates; Lean or another trusted kernel must check them.

## Verification

- Pre-manifest validation: **{PRE_CHECKS}/{PRE_CHECKS} PASS**.
- Portable clean-base rebuild from `CST-EXP-05-v1`: **{rebuild['surfaces_compared']}/{rebuild['surfaces_compared']} generated surfaces reproduced byte-for-byte**; rebuilt validation **{PRE_CHECKS}/{PRE_CHECKS} PASS**.
- Full frozen-repository validation: **{FULL_CHECKS}/{FULL_CHECKS} PASS**.
- Inherited CST-EXP-05 scientific surfaces remain byte-frozen against `manifests/CST-EXP-05_MANIFEST.json`.

## Boundary

No theorem or no-go has been proved. No Lean development, Python toy, full Six Birds simulation, empirical recognition bridge, consciousness result, personal-survival result, numerical-identity result, certificate-soundness theorem, A1 result, or A2-P carrier-invariance result is claimed. The preparatory exploration is complete; implementation belongs to a separate later project.
"""
    write(root / "manifests/CST-EXP-06_COMPLETION_REPORT.md", completion)

    restore = f"""# Restore and Verify CST-EXP-06

From the extracted repository root:

```bash
git status --short
python scripts/validate_exp06.py
python scripts/verify_exp06_rebuild.py
sha256sum -c manifests/SHA256SUMS
```

Expected full validation: `PASS {FULL_CHECKS}/{FULL_CHECKS}`.  
Expected portable rebuild: `PASS {rebuild['surfaces_compared']} surfaces`; rebuilt pre-validation `PASS {PRE_CHECKS}/{PRE_CHECKS}`.

The archive contains the full Git history. The frozen phase tag is `CST-EXP-06-v1`; the prior base tag is `CST-EXP-05-v1`.
"""
    write(root / "manifests/RESTORE_AND_VERIFY.md", restore)

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
        "phase": "CST-EXP-06",
        "generated_date": DATE,
        "scope": "all non-Git, non-cache repository files except dynamic validation and manifest surfaces",
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
    print(f"Frozen CST-EXP-06 manifest with {len(entries)} files; SHA256SUMS has {len(sums)} rows")


if __name__ == "__main__":
    main()
