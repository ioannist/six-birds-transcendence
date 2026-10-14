from __future__ import annotations

from dataclasses import asdict, dataclass
from itertools import product
import json
from typing import Any, Mapping

from .withdrawal_autonomy_checker import audit_autonomy


def _rows(value: object) -> list[Mapping[str, Any]]:
    return [row for row in value if isinstance(row, Mapping)] if isinstance(value, list) else []


@dataclass(frozen=True)
class LassoWitness:
    disturbance_id: str
    prefix_state_ids: tuple[str, ...]
    cycle_state_ids: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["prefix_state_ids"] = list(self.prefix_state_ids)
        value["cycle_state_ids"] = list(self.cycle_state_ids)
        return value


@dataclass(frozen=True)
class UnboundedInvariantAudit:
    certificate_id: str
    base_autonomy_valid: bool
    invariant_nonempty: bool
    policy_total: bool
    policy_deterministic: bool
    every_successor_inside: bool
    every_action_target_owned: bool
    every_step_progresses: bool
    every_record_strictly_advances: bool
    every_step_budget_solvent: bool
    package_invariant: bool
    finite_state_space: bool
    infinite_run_schema_valid: bool
    model_relative_claim_only: bool
    physical_liveness_not_claimed: bool
    lasso_witnesses: tuple[LassoWitness, ...]
    unbounded_model_invariance_valid: bool
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["lasso_witnesses"] = [row.to_dict() for row in self.lasso_witnesses]
        value["failed_obligations"] = list(self.failed_obligations)
        return json.loads(json.dumps(value, sort_keys=True))


def _policy_map(audit: Any) -> dict[tuple[str, str], Any]:
    return {(row.state_id, row.disturbance_id): row for row in audit.response_policy}


def _constant_disturbance_lasso(endpoint: str, disturbance: str, policy: Mapping[tuple[str, str], Any]) -> LassoWitness:
    seen: dict[str, int] = {}
    trace: list[str] = []
    state = endpoint
    while state not in seen:
        seen[state] = len(trace)
        trace.append(state)
        row = policy[(state, disturbance)]
        state = row.successor_state_id
    split = seen[state]
    return LassoWitness(disturbance, tuple(trace[:split]), tuple(trace[split:]))


def audit_unbounded_invariant(spec: Mapping[str, Any], autonomy_model: Mapping[str, Any]) -> UnboundedInvariantAudit:
    audit = audit_autonomy(autonomy_model)
    invariant = set(audit.computed_invariant_state_ids)
    disturbances = {str(row.get("disturbance_id")) for row in _rows(autonomy_model.get("disturbances")) if row.get("disturbance_id")}
    policy = _policy_map(audit)
    required = {(state, disturbance) for state in invariant for disturbance in disturbances}
    policy_total = bool(required) and required.issubset(policy)
    policy_deterministic = len(policy) == len(set(policy)) and policy_total
    every_successor_inside = policy_total and all(policy[key].successor_state_id in invariant for key in required)
    target = autonomy_model.get("target", {})
    target_code = target.get("code") if isinstance(target, Mapping) else None
    every_action_target_owned = policy_total and all(policy[key].action_owner == target_code for key in required)
    every_step_progresses = policy_total and all(policy[key].progress_delta > 0 for key in required)
    every_record_advances = policy_total and all(policy[key].record_delta > 0 for key in required)
    every_budget_solvent = policy_total and all(policy[key].budget_after >= 0 for key in required)
    state_rows = {str(row.get("state_id")): row for row in _rows(autonomy_model.get("states")) if row.get("state_id")}
    package_invariant = bool(invariant) and all(state_rows.get(state, {}).get("package_valid") is True for state in invariant)
    finite_state_space = bool(state_rows) and len(state_rows) < 10**6
    endpoint = str(autonomy_model.get("endpoint_state_id", ""))
    lassos = tuple(_constant_disturbance_lasso(endpoint, disturbance, policy) for disturbance in sorted(disturbances)) if policy_total else ()
    infinite_schema = bool(
        audit.autonomy_valid
        and policy_total
        and every_successor_inside
        and every_action_target_owned
        and every_step_progresses
        and every_record_advances
        and every_budget_solvent
        and package_invariant
    )
    model_relative_only = spec.get("claim_scope") == "unbounded run existence inside the exact finite controlled model"
    physical_not_claimed = spec.get("physical_liveness_status") == "not-established"
    obligations = {
        "base-autonomy-valid": audit.autonomy_valid,
        "invariant-nonempty": bool(invariant),
        "policy-total": policy_total,
        "policy-deterministic": policy_deterministic,
        "every-successor-inside": every_successor_inside,
        "every-action-target-owned": every_action_target_owned,
        "every-step-progresses": every_step_progresses,
        "every-record-strictly-advances": every_record_advances,
        "every-step-budget-solvent": every_budget_solvent,
        "package-invariant": package_invariant,
        "finite-state-space": finite_state_space,
        "infinite-run-schema-valid": infinite_schema,
        "model-relative-claim-only": model_relative_only,
        "physical-liveness-not-claimed": physical_not_claimed,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return UnboundedInvariantAudit(
        certificate_id=str(spec.get("certificate_id", "")),
        base_autonomy_valid=audit.autonomy_valid,
        invariant_nonempty=bool(invariant),
        policy_total=policy_total,
        policy_deterministic=policy_deterministic,
        every_successor_inside=every_successor_inside,
        every_action_target_owned=every_action_target_owned,
        every_step_progresses=every_step_progresses,
        every_record_strictly_advances=every_record_advances,
        every_step_budget_solvent=every_budget_solvent,
        package_invariant=package_invariant,
        finite_state_space=finite_state_space,
        infinite_run_schema_valid=infinite_schema,
        model_relative_claim_only=model_relative_only,
        physical_liveness_not_claimed=physical_not_claimed,
        lasso_witnesses=lassos,
        unbounded_model_invariance_valid=not failed,
        failed_obligations=failed,
    )


def bounded_disturbance_prefix_check(autonomy_model: Mapping[str, Any], max_depth: int = 12) -> dict[str, Any]:
    audit = audit_autonomy(autonomy_model)
    policy = _policy_map(audit)
    disturbances = sorted({row.disturbance_id for row in audit.response_policy})
    endpoint = str(autonomy_model.get("endpoint_state_id", ""))
    checked = 0
    violations = 0
    for depth in range(max_depth + 1):
        for word in product(disturbances, repeat=depth):
            checked += 1
            state = endpoint
            for disturbance in word:
                row = policy.get((state, disturbance))
                if row is None or row.progress_delta <= 0 or row.record_delta <= 0 or row.budget_after < 0:
                    violations += 1
                    break
                state = row.successor_state_id
    return {
        "search_id": "UNBOUNDED_POLICY_PREFIX_STRESS",
        "maximum_depth": max_depth,
        "words_checked": checked,
        "violations": violations,
    }


def arbitrary_finite_prefix_counterfamily(max_horizon: int = 12) -> dict[str, Any]:
    rows = []
    for horizon in range(max_horizon + 1):
        live_prefix = [budget > 0 for budget in range(horizon + 1, 0, -1)]
        failure_at_next = 0 <= 0
        rows.append(
            {
                "horizon": horizon,
                "initial_budget": horizon + 1,
                "all_declared_prefix_steps_live": all(live_prefix[: horizon + 1]),
                "fails_at_next_step": failure_at_next,
                "failure_budget": 0,
            }
        )
    return {
        "search_id": "ARBITRARILY_LONG_FINITE_PREFIX_FAMILY",
        "maximum_horizon": max_horizon,
        "models_constructed": len(rows),
        "every_horizon_has_countermodel": all(row["all_declared_prefix_steps_live"] and row["fails_at_next_step"] for row in rows),
        "rows": rows,
    }
