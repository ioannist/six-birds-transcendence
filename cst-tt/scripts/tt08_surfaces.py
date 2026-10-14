from __future__ import annotations

"""Authoritative CST-TT-08 generated release surfaces."""

from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

FIXED_GENERATED_SURFACES: tuple[str, ...] = (
    "README.md",
    "RESTORE_AND_VERIFY.md",
    "STATE.md",
    "STATUS.md",
    "CHANGELOG.md",
    "changelog/CST-TT-08.md",
    "docs/PHASE_BOUNDARY.md",
    "docs/RESTORE_AND_BUILD.md",
    "docs/CST-TT-08_FINAL_SCIENCE_CLOSURE.md",
    "formal/README.md",
    "formal/TOOLCHAIN_STATUS.json",
    "handoff/CST-TT-08_SCIENCE_HANDOFF.md",
    "handoff/FINAL_CLAIM_CEILING.md",
    "handoff/FINAL_DEPENDENCY_DAG.dot",
    "handoff/FINAL_DEPENDENCY_DAG.svg",
    "handoff/FINAL_FAILED_ALTERNATIVES.md",
    "handoff/FINAL_MODEL_CATALOG.md",
    "handoff/FINAL_PROOF_DEPENDENCY_GUIDE.md",
    "handoff/FINAL_SBT_PROVENANCE.md",
    "handoff/FINAL_THEOREM_AUDIT.md",
    "handoff/PAPER_RESULT_TABLES.md",
    "registries/FINAL_CERTIFICATE_INDEX.csv",
    "registries/FINAL_CLAIM_ASSUMPTION_NONCLAIM_LEDGER.csv",
    "registries/FINAL_DEPENDENCY_DAG.json",
    "registries/FINAL_DEPENDENCY_EDGES.csv",
    "registries/FINAL_DEPENDENCY_NODES.csv",
    "registries/FINAL_MODEL_INDEX.csv",
    "registries/FINAL_REBUILD_MATRIX.csv",
    "registries/FINAL_SBT_PROVENANCE.csv",
    "registries/FINAL_THEOREM_STATUS.csv",
    "registries/FINAL_THEOREM_STATUS.json",
    "registries/FINAL_TOY_CATALOG.csv",
    "registries/PROJECT_REGISTRY.json",
    "manifests/CST-TT-08_COMPLETION_REPORT.md",
    "manifests/CST-TT-08_MODEL_CERTIFICATE_DELTA.csv",
    "manifests/CST-TT-08_PHASE_SUMMARY.json",
    "manifests/CST-TT-08_THEOREM_STATUS_DELTA.csv",
    "manifests/COMPLETION_REPORT.md",
    "manifests/PHASE_SUMMARY.json",
)

GENERATED_DIRECTORIES: tuple[str, ...] = ("archive/rejected",)

LEGACY_DRAFT_SURFACES: tuple[str, ...] = (
    "docs/CST-TT-08_FAILED_ALTERNATIVES_AND_REJECTED_DEFINITIONS.md",
    "docs/CST-TT-08_FINAL_CLAIM_ASSUMPTION_NONCLAIM_LEDGER.md",
    "docs/CST-TT-08_FINAL_DEPENDENCY_DAG.dot",
    "docs/CST-TT-08_FINAL_DEPENDENCY_DAG.md",
    "docs/CST-TT-08_FINAL_DEPENDENCY_DAG.svg",
    "docs/CST-TT-08_FINAL_MODEL_AND_CERTIFICATE_CATALOG.md",
    "docs/CST-TT-08_FINAL_SCIENCE_HANDOFF.md",
    "docs/CST-TT-08_FINAL_THEOREM_STATUS_AND_AUDIT.md",
    "docs/CST-TT-08_PAPER_FACING_RESULT_TABLES.md",
    "docs/CST-TT-08_REPRODUCIBILITY_AND_TOOLCHAIN_STATUS.md",
    "docs/CST-TT-08_SBT_PROVENANCE_MAP.md",
    "registries/FINAL_CERTIFICATE_CATALOG.csv",
    "registries/FINAL_FAILED_ALTERNATIVES.csv",
    "registries/FINAL_MODEL_CATALOG.csv",
    "registries/FINAL_PROOF_EVIDENCE.csv",
    "registries/FINAL_SOURCE_PROVENANCE.csv",
    "registries/FINAL_THEOREM_STATEMENTS.json",
)


def generated_paths(root: Path = ROOT) -> list[Path]:
    paths = {root / rel for rel in FIXED_GENERATED_SURFACES}
    for rel_dir in GENERATED_DIRECTORIES:
        directory = root / rel_dir
        if directory.is_dir():
            paths.update(path for path in directory.rglob("*") if path.is_file())
    return sorted(paths)
