from __future__ import annotations

import json
from pathlib import Path

from cst_tt.branching import audit_fusion_boundary, audit_temporal_fission

ROOT = Path(__file__).resolve().parents[1]


def load(rel: str) -> dict:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


def test_relation_valued_fission_replays_and_does_not_select() -> None:
    cert = load("formal/certificates/fission/FISSION-POS-01.certificate.json")
    audit = audit_temporal_fission(cert, ROOT)
    assert audit.relation_valued_fission_valid is True
    assert audit.to_dict() == cert["audit"]
    assert (audit.source_code, audit.left_target_code, audit.right_target_code) == (17, 201, 202)
    assert audit.target_shapes_symmetric is True
    assert audit.relation_contains_both_branches is True
    assert audit.swap_involutive is True
    assert audit.swap_fixed_point_free is True
    assert audit.validity_preserved_by_swap is True
    assert audit.invariant_singleton_selector_absent is True
    assert audit.uniqueness_claim_absent is True


def test_every_fission_control_breaks_its_named_obligation() -> None:
    rows = (ROOT / "registries/FISSION_CONTROL_REGISTRY.csv").read_text(encoding="utf-8").splitlines()
    assert len(rows) == 7
    for path in sorted((ROOT / "formal/certificates/fission/controls").glob("*.certificate.json")):
        cert = json.loads(path.read_text(encoding="utf-8"))
        assert cert["result_status"] == "checked-fission-obligation-countermodel"
        assert cert["expected_primary_failure"] in cert["observed_failures"]
        assert cert["audit"]["relation_valued_fission_valid"] is False


def test_fission_symmetry_exhaustion_has_no_invariant_selector() -> None:
    search = load("formal/certificates/search/FISSION_SYMMETRY_EXHAUSTION.json")
    assert search["candidates_examined"] == 6564
    assert search["minimum_target_count"] == 2
    assert search["qualified_symmetric_forks"] > 0
    assert search["invariant_singleton_selector_violations"] == 0


def test_fusion_lineages_do_not_force_integrated_target_package() -> None:
    cert = load("formal/certificates/fusion/FUSION-BOUNDARY-01.certificate.json")
    audit = audit_fusion_boundary(cert, ROOT)
    assert audit.fusion_boundary_valid is True
    assert audit.to_dict() == cert["audit"]
    assert audit.left_lineage_valid and audit.right_lineage_valid
    assert audit.common_target is True
    assert audit.branchwise_payload_preserved is True
    assert audit.action_credit_conflict_witnessed is True
    assert audit.recombination_failure_witnessed is True
    assert audit.integrated_target_package_fails is True
    assert audit.merger_does_not_imply_package is True


def test_fusion_boolean_boundary_is_exact() -> None:
    search = load("formal/certificates/search/FUSION_BOUNDARY_EXHAUSTION.json")
    assert search["candidates_examined"] == 128
    assert search["merger_premise_cases"] == 4
    assert search["boundary_cases"] == 3
