from __future__ import annotations

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_imported_temporal_audit_hashes_resolve() -> None:
    checksum_file = ROOT / "inputs/normative/cst-tt-00/IMPORTED_SHA256SUMS.txt"
    for line in checksum_file.read_text(encoding="utf-8").splitlines():
        digest, rel = line.split(maxsplit=1)
        path = ROOT / rel.lstrip("*")
        assert path.is_file(), path
        assert sha256(path) == digest


def test_all_nine_temporal_source_manuscripts_are_present() -> None:
    sources = list((ROOT / "inputs/reference_surfaces/temporal_audit").glob("*.tex"))
    assert len(sources) == 9


def test_project_registry_records_exact_finite_handoff_without_overclaim() -> None:
    registry = json.loads((ROOT / "registries/PROJECT_REGISTRY.json").read_text(encoding="utf-8"))
    assert registry["phase"] in {"CST-TT-07A", "CST-TT-08"}
    if registry["phase"] == "CST-TT-08":
        assert registry["phase_base_tag"] == "CST-TT-07A-v1"
        assert registry["phase_base_commit"] == "7ba9167d39e6751706a7ad7152911c61f77af6af"
        assert registry["science_program_closed"] is True
        assert registry["fallback_status"] == "Temporal-IAPS remains open and unauthorized; no primary kill fired"
        assert registry["final_theorem_status_counts"] == {
            "checked finite countermodel": 12,
            "conditional": 19,
            "open": 8,
        }
    else:
        assert registry["phase_base_tag"] == "CST-TT-06-v1"
        assert registry["phase_base_commit"] == "6c8f510c67087a8db9dd1c4107008b3b7cfb0847"
    assert registry["checked_finite_countermodels"] == 15
    assert registry["checked_finite_package_witnesses"] == 4
    assert registry["checked_temporal_transport_certificates"] == 2
    assert registry["checked_strict_corridor_certificates"] == 4
    assert registry["checked_full_handoff_composition_certificates"] == 1
    assert registry["checked_relation_valued_fission_certificates"] == 1
    assert registry["checked_fusion_boundary_certificates"] == 1
    assert registry["checked_route_completion_certificates"] == 2
    assert registry["checked_primary_common_toy_suite"] == "13/13"
    assert registry["checked_generalized_continuity_certificates"] == 4
    assert registry["checked_defect_profile_certificates"] == 8
    assert registry["checked_robustness_certificates"] == 7
    assert registry["checked_unbounded_invariant_certificates"] == 1
    assert registry["positive_handoff_witnesses"] == 4
    assert registry["fallback_unlocked"] is False
    assert registry["generic_theorems_lean_compiled"] == 0
    assert registry["negative_kernel_status"] == "frozen"
    assert registry["claim_ceiling"] == "exact finite structural precursor only"


def test_phase_boundary_states_landed_and_unlanded_claims() -> None:
    text = (ROOT / "docs/PHASE_BOUNDARY.md").read_text(encoding="utf-8")
    project = json.loads((ROOT / "registries/PROJECT_REGISTRY.json").read_text(encoding="utf-8"))
    if project["phase"] == "CST-TT-08":
        phrases = (
            "theorem-and-toy science program",
            "Temporal-FIACH",
            "direct succession",
            "consciousness",
            "ontological",
            "CST-TT-08",
        )
    else:
        phrases = (
            "full-handoff composition",
            "relation-valued fission",
            "fusion/recombination boundary",
            "13/13 primary/common toy closure",
            "consciousness",
            "survival",
            "numerical identity",
            "CST-TT-07A",
        )
    for phrase in phrases:
        assert phrase in text
