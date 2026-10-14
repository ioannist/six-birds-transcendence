from __future__ import annotations

import json
from pathlib import Path

from cst_tt.robustness import audit_robustness, audit_specific_perturbation, enumerate_bounded_perturbations
from tt07a_data import robustness_controls, robustness_model

ROOT = Path(__file__).resolve().parents[1]


def load(rel: str) -> dict:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


def test_bounded_temporal_robustness_box_replays() -> None:
    model = robustness_model()
    audit = audit_robustness(model)
    assert audit.robustness_valid
    assert audit.bounded_box_size == 945
    assert audit.bounded_perturbations_checked == 945
    assert audit.bounded_violations == 0
    assert audit.minimum_observed_increments == {
        "predictive-step": 2,
        "order-step": 2,
        "tick-step": 2,
        "progress-step": 1,
        "record-step": 2,
    }
    assert audit.every_hard_gate_frozen_true
    assert audit.approximation_does_not_override_hard_gates


def test_robustness_boundary_controls_fail_for_the_declared_reason() -> None:
    model = robustness_model()
    for control_id, _description, deltas, gates in robustness_controls():
        result = audit_specific_perturbation(model, deltas, gates)
        assert result["accepted"] is False, control_id
        if control_id in {"ROB-C01", "ROB-C02"}:
            assert result["within_declared_box"] is False
        else:
            assert result["hard_gates_exact_and_true"] is False


def test_bounded_perturbation_exhaustion_is_frozen_exactly() -> None:
    result = enumerate_bounded_perturbations(robustness_model())
    assert result == load("formal/certificates/search/BOUNDED_TEMPORAL_MARGIN_EXHAUSTION.json")
    assert result["candidates_examined"] == 945
    assert result["violations"] == 0
