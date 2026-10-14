from __future__ import annotations

import json
import os
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

GENERATED_DIRS = (
    "models/strengthenings",
    "formal/certificates/strengthenings",
)

FIXED_GENERATED = (
    "formal/certificates/search/OVERLAP_DIRECT_RELATION_TRUTH_TABLE.json",
    "formal/certificates/search/VECTOR_DEFECT_EXHAUSTION.json",
    "formal/certificates/search/VECTOR_DEFECT_DOWNWARD_CLOSURE.json",
    "formal/certificates/search/BOUNDED_TEMPORAL_MARGIN_EXHAUSTION.json",
    "formal/certificates/search/UNBOUNDED_POLICY_PREFIX_STRESS.json",
    "formal/certificates/search/ARBITRARILY_LONG_FINITE_PREFIX_FAMILY.json",
    "registries/DEFECT_PROFILE_REGISTRY.csv",
    "registries/ROBUSTNESS_REGISTRY.csv",
    "registries/UNBOUNDED_INVARIANT_REGISTRY.csv",
    "registries/THEOREM_REGISTRY.csv",
    "registries/TOY_MODEL_REGISTRY.csv",
    "registries/DEFINITION_REGISTRY.csv",
    "registries/ASSUMPTION_LEDGER.csv",
    "registries/DEPENDENCY_EDGES.csv",
    "registries/CERTIFICATE_SCHEMA_REGISTRY.csv",
    "registries/KILL_CRITERIA.csv",
    "registries/PROJECT_REGISTRY.json",
    "schemas/certificates/generalized_continuity_certificate.schema.json",
    "schemas/certificates/defect_profile_certificate.schema.json",
    "schemas/certificates/temporal_robustness_certificate.schema.json",
    "schemas/certificates/unbounded_invariant_certificate.schema.json",
    "examples/scaffold/generalized_continuity_certificate.scaffold.json",
    "examples/scaffold/defect_profile_certificate.scaffold.json",
    "examples/scaffold/temporal_robustness_certificate.scaffold.json",
    "examples/scaffold/unbounded_invariant_certificate.scaffold.json",
    "docs/CST-TT-07A_DIRECT_SUCCESSOR_RELATION.md",
    "docs/CST-TT-07A_EXACT_VECTOR_DEFECT_SEMANTICS.md",
    "docs/CST-TT-07A_BOUNDED_TEMPORAL_ROBUSTNESS.md",
    "docs/CST-TT-07A_MODEL_RELATIVE_UNBOUNDED_INVARIANCE.md",
    "docs/CST-TT-07A_PRIMARY_STRENGTHENING_SYNTHESIS.md",
    "docs/CST-TT-07A_DECISION_GATE.md",
    "docs/PHASE_BOUNDARY.md",
    "docs/RESTORE_AND_BUILD.md",
    "README.md",
    "STATE.md",
    "STATUS.md",
    "CHANGELOG.md",
    "RESTORE_AND_VERIFY.md",
    "changelog/CST-TT-07A.md",
    "formal/README.md",
    "formal/TOOLCHAIN_STATUS.json",
    "manifests/CST-TT-07A_COMPLETION_REPORT.md",
    "manifests/CST-TT-07A_PHASE_SUMMARY.json",
    "manifests/CST-TT-07A_THEOREM_STATUS_DELTA.csv",
    "manifests/CST-TT-07A_MODEL_CERTIFICATE_DELTA.csv",
    "manifests/COMPLETION_REPORT.md",
    "manifests/PHASE_SUMMARY.json",
)


def generated_paths() -> list[Path]:
    paths = {ROOT / rel for rel in FIXED_GENERATED}
    for rel_dir in GENERATED_DIRS:
        paths.update(path for path in (ROOT / rel_dir).rglob("*") if path.is_file())
    return sorted(path for path in paths if path.is_file())


def test_builder_is_idempotent_in_place() -> None:
    project = json.loads((ROOT / "registries/PROJECT_REGISTRY.json").read_text(encoding="utf-8"))
    if project.get("phase") == "CST-TT-08":
        from tt08_surfaces import generated_paths as tt08_generated_paths

        paths = [path for path in tt08_generated_paths(ROOT) if path.is_file()]
        before = {path.relative_to(ROOT): path.read_bytes() for path in paths}
        completed = subprocess.run(
            [sys.executable, "scripts/build_tt08_assets.py"],
            cwd=ROOT,
            check=True,
            capture_output=True,
            text=True,
            env={**os.environ, "PYTHONPATH": "src:scripts", "PYTHONHASHSEED": "0"},
        )
        assert "CST-TT-08 assets built" in completed.stdout
        after = {path.relative_to(ROOT): path.read_bytes() for path in paths}
        assert before == after
        return

    before = {path.relative_to(ROOT): path.read_bytes() for path in generated_paths()}
    completed = subprocess.run(
        [sys.executable, "scripts/build_tt07a_assets.py"],
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
        env={**os.environ, "PYTHONPATH": "src:scripts", "PYTHONHASHSEED": "0"},
    )
    assert "CST-TT-07A assets built" in completed.stdout
    after = {path.relative_to(ROOT): path.read_bytes() for path in generated_paths()}
    assert before == after


def test_phase_summary_matches_frozen_counts() -> None:
    project = json.loads((ROOT / "registries/PROJECT_REGISTRY.json").read_text(encoding="utf-8"))
    if project.get("phase") == "CST-TT-08":
        summary = json.loads((ROOT / "manifests/CST-TT-08_PHASE_SUMMARY.json").read_text(encoding="utf-8"))
        assert summary["phase"] == "CST-TT-08"
        assert summary["base_tag"] == "CST-TT-07A-v1"
        assert summary["theorem_status_counts"] == {
            "checked finite countermodel": 12,
            "conditional": 19,
            "open": 8,
        }
        assert summary["model_index_count"] == 203
        assert summary["certificate_and_search_index_count"] == 233
        assert summary["toy_contract_count"] == 28
        assert summary["next_phase"] == "none-science-program-closed"
        return

    summary = json.loads((ROOT / "manifests/CST-TT-07A_PHASE_SUMMARY.json").read_text(encoding="utf-8"))
    assert summary["phase"] == "CST-TT-07A"
    assert summary["base_tag"] == "CST-TT-06-v1"
    assert summary["primary"] == "Temporal-FIACH strict overlap remains unchanged"
    assert summary["defect_profiles"] == {"positive": 1, "controls": 6, "equal_scalar_pairs": 1}
    assert summary["robustness"] == {"box_points": 945, "violations": 0, "controls": 6}
    assert summary["unbounded"] == {"prefix_words_checked": 8191, "counterfamily_models": 13}
    assert summary["fallback_unlocked"] is False
    assert summary["next_phase"] == "CST-TT-08"
