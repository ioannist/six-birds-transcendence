from __future__ import annotations

import json
from pathlib import Path

from cst_tt.handoff_composition import audit_full_handoff_composition, audit_staged_composition

ROOT = Path(__file__).resolve().parents[1]


def load(rel: str) -> dict:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


def test_full_handoff_composition_replays_exactly() -> None:
    cert = load("formal/certificates/composition/FIACH-COMP-01.certificate.json")
    audit = audit_full_handoff_composition(cert, ROOT)
    assert audit.composition_valid is True
    assert audit.to_dict() == cert["audit"]
    assert audit.source_code == 17
    assert audit.shared_code == 55
    assert audit.target_code == 101
    assert audit.route_status == "route-indexed"
    assert audit.shared_package_exact is True
    assert audit.shared_temporal_frontier_exact is True
    assert audit.shared_route_memory_exact is True
    assert audit.shared_temporal_ownership_exact is True
    assert audit.left_autonomy_closes_shared_package is True
    assert audit.final_autonomy_target_system_inherited is True
    assert audit.all_upstream_support_withdrawn is True


def test_staged_maps_factor_through_same_intermediate_package() -> None:
    cert = load("formal/certificates/composition/STG-COMP-01.certificate.json")
    audit = audit_staged_composition(cert, ROOT)
    assert audit.composition_valid is True
    assert audit.shared_intermediate_model_exact is True
    assert audit.intermediate_value_interface_exact is True
    assert audit.composite_maps_factor_through_intermediate is True
    assert audit.hard_gates_remain_unaveraged is True


def test_outer_autonomy_withdraws_source_and_intermediate() -> None:
    model = load("models/composition/autonomy/AUT-COMP-OUTER.model.json")
    removed = model["withdrawal"]["removed_resources"]
    source_owners = {row["owner"]["code"] for row in removed if row["role"] == "source"}
    assert source_owners == {17, 55}
    assert model["target"]["code"] == 101


def test_composition_interface_exhaustion_rejects_every_single_deletion() -> None:
    search = load("formal/certificates/search/FULL_HANDOFF_INTERFACE_EXHAUSTION.json")
    assert search["candidates_examined"] == 1024
    assert search["accepted_candidates"] == 1
    assert search["all_single_failures_rejected"] is True
    assert all(search["single_failure_rejections"].values())
