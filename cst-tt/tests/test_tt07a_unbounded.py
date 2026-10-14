from __future__ import annotations

import json
from pathlib import Path

from cst_tt.unbounded import audit_unbounded_invariant, arbitrary_finite_prefix_counterfamily, bounded_disturbance_prefix_check
from tt07a_data import unbounded_spec

ROOT = Path(__file__).resolve().parents[1]


def load(rel: str) -> dict:
    return json.loads((ROOT / rel).read_text(encoding="utf-8"))


def test_total_target_owned_policy_supplies_model_relative_unbounded_runs() -> None:
    spec = unbounded_spec()
    autonomy = load(spec["autonomy_model_ref"])
    audit = audit_unbounded_invariant(spec, autonomy)
    assert audit.unbounded_model_invariance_valid
    assert audit.base_autonomy_valid
    assert audit.policy_total
    assert audit.policy_deterministic
    assert audit.every_successor_inside
    assert audit.every_action_target_owned
    assert audit.every_step_progresses
    assert audit.every_record_strictly_advances
    assert audit.every_step_budget_solvent
    assert audit.package_invariant
    assert audit.model_relative_claim_only
    assert audit.physical_liveness_not_claimed
    assert len(audit.lasso_witnesses) == 2
    assert all(witness.cycle_state_ids for witness in audit.lasso_witnesses)


def test_prefix_stress_and_arbitrary_finite_prefix_family_match_release() -> None:
    autonomy = load("models/autonomy/AUT-POS-01.model.json")
    prefix = bounded_disturbance_prefix_check(autonomy, 12)
    family = arbitrary_finite_prefix_counterfamily(12)
    assert prefix == load("formal/certificates/search/UNBOUNDED_POLICY_PREFIX_STRESS.json")
    assert family == load("formal/certificates/search/ARBITRARILY_LONG_FINITE_PREFIX_FAMILY.json")
    assert prefix == {
        "search_id": "UNBOUNDED_POLICY_PREFIX_STRESS",
        "maximum_depth": 12,
        "words_checked": 8191,
        "violations": 0,
    }
    assert family["models_constructed"] == 13
    assert family["every_horizon_has_countermodel"]
    assert all(row["all_declared_prefix_steps_live"] and row["fails_at_next_step"] for row in family["rows"])
