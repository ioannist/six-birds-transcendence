from __future__ import annotations

import json
from pathlib import Path

from cst_tt.defect_semantics import audit_defect_profile, bounded_defect_exhaustion, bounded_downward_closure_exhaustion
from tt07a_data import defect_controls, equal_scalar_profiles, full_defect_profile

ROOT = Path(__file__).resolve().parents[1]


def load(rel: str) -> dict:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


def test_positive_exact_vector_profile_and_every_control_replay() -> None:
    positive = audit_defect_profile(full_defect_profile())
    assert positive.accepted
    assert sum(row.gate_kind == "hard" for row in positive.component_audits) == 12
    assert sum(row.gate_kind == "soft" for row in positive.component_audits) == 5
    assert positive.every_hard_gate_exact
    assert positive.every_component_within_tolerance
    assert positive.scalar_summary_diagnostic_only

    for control_id, failed_obligation, profile in defect_controls():
        audit = audit_defect_profile(profile)
        assert not audit.accepted, control_id
        assert failed_obligation in audit.failed_obligations


def test_equal_scalar_profiles_have_opposite_exact_verdicts() -> None:
    accepted_profile, rejected_profile = equal_scalar_profiles()
    accepted = audit_defect_profile(accepted_profile)
    rejected = audit_defect_profile(rejected_profile)
    assert accepted.accepted
    assert not rejected.accepted
    assert accepted.scalar_summary == rejected.scalar_summary
    frozen = load("formal/certificates/strengthenings/defects/DEF-EQUAL-SCALAR-01.certificate.json")
    assert frozen["same_scalar_summary"] is True
    assert frozen["accepted_audit"]["accepted"] is True
    assert frozen["rejected_audit"]["accepted"] is False


def test_bounded_defect_exhaustions_match_frozen_results() -> None:
    exact = bounded_defect_exhaustion()
    downward = bounded_downward_closure_exhaustion()
    assert exact == load("formal/certificates/search/VECTOR_DEFECT_EXHAUSTION.json")
    assert downward == load("formal/certificates/search/VECTOR_DEFECT_DOWNWARD_CLOSURE.json")
    assert exact["candidates_examined"] == 4096
    assert exact["accepted_candidates"] == 256
    assert exact["scalar_small_but_rejected"] == 4
    assert exact["equal_scalar_opposite_verdict_pairs"] == 32
    assert downward["ordered_pairs_examined"] == 531441
    assert downward["accepted-upper-premise-pairs"] == 6561
    assert downward["violations"] == 0
