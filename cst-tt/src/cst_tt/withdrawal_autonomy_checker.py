from __future__ import annotations

from collections import deque
from dataclasses import asdict, dataclass
from itertools import product
from typing import Any, Iterable, Mapping, Sequence
import json

MANDATORY_REMOVED_ROLES = frozenset(
    {
        "source",
        "bridge",
        "migration-controller",
        "external-decoder",
        "external-scheduler",
        "undeclared-repair",
    }
)
FORBIDDEN_VERDICT_KEYS = frozenset(
    {
        "fiach",
        "lineage",
        "identity",
        "survival",
        "consciousness",
        "phenomenal",
        "same_subject",
        "personal_identity",
    }
)


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _carrier_code(value: Any) -> int | None:
    if isinstance(value, Mapping):
        code = value.get("code")
        return int(code) if _is_int(code) and int(code) >= 0 else None
    if _is_int(value) and int(value) >= 0:
        return int(value)
    return None


def _walk_keys(value: Any) -> Iterable[str]:
    if isinstance(value, Mapping):
        for key, child in value.items():
            yield str(key)
            yield from _walk_keys(child)
    elif isinstance(value, list):
        for child in value:
            yield from _walk_keys(child)


def _forbidden_hits(model: Mapping[str, Any]) -> tuple[str, ...]:
    hits: set[str] = set()
    for key in _walk_keys(model):
        normalized = key.lower().replace("-", "_")
        if normalized in FORBIDDEN_VERDICT_KEYS:
            hits.add(key)
    return tuple(sorted(hits))


def _resource_rows(model: Mapping[str, Any]) -> tuple[list[Mapping[str, Any]], list[Mapping[str, Any]]]:
    withdrawal = model.get("withdrawal", {})
    if not isinstance(withdrawal, Mapping):
        return [], []
    removed = withdrawal.get("removed_resources", [])
    retained = withdrawal.get("retained_resources", [])
    return (
        [row for row in removed if isinstance(row, Mapping)] if isinstance(removed, list) else [],
        [row for row in retained if isinstance(row, Mapping)] if isinstance(retained, list) else [],
    )


def _id_map(rows: Any, key: str) -> dict[str, Mapping[str, Any]]:
    if not isinstance(rows, list):
        return {}
    result: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        if not isinstance(row, Mapping):
            continue
        value = row.get(key)
        if isinstance(value, str) and value:
            result[value] = row
    return result


def _transition_rows(model: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    rows = model.get("transitions", [])
    return [row for row in rows if isinstance(row, Mapping)] if isinstance(rows, list) else []


@dataclass(frozen=True)
class ResponseChoice:
    state_id: str
    disturbance_id: str
    action_id: str
    successor_state_id: str
    action_owner: int
    progress_delta: int
    record_delta: int
    budget_before: int
    budget_cost: int
    budget_regeneration: int
    budget_after: int

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class CollapseStep:
    state_id: str
    disturbance_id: str
    action_id: str | None
    successor_state_id: str | None
    failure: str | None

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class AutonomyAudit:
    model_id: str
    source_target_distinct: bool
    boundary_fixed_before_evaluation: bool
    disturbance_class_fixed_before_evaluation: bool
    withdrawal_shape_valid: bool
    withdrawal_complete: bool
    mandatory_removed_roles_present: bool
    removed_retained_disjoint: bool
    retained_resources_target_owned: bool
    package_contract_hash_bound: bool
    state_table_well_formed: bool
    disturbance_table_well_formed: bool
    action_table_well_formed: bool
    transition_table_well_formed: bool
    forbidden_verdict_fields_absent: bool
    computed_invariant_state_ids: tuple[str, ...]
    declared_invariant_state_ids: tuple[str, ...]
    declared_invariant_matches_computed: bool
    endpoint_inside: bool
    package_inside: bool
    resource_closed_on_invariant: bool
    target_owned_responses: bool
    anti_stall_on_invariant: bool
    budget_solvent_on_invariant: bool
    response_total_on_invariant: bool
    finite_horizon: int
    finite_words_checked: int
    finite_horizon_survives: bool
    response_policy: tuple[ResponseChoice, ...]
    collapse_trace: tuple[CollapseStep, ...]
    collapse_trace_length: int | None
    autonomy_valid: bool
    failed_obligations: tuple[str, ...]
    errors: tuple[str, ...]
    removal_rounds: Mapping[str, int]

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["response_policy"] = [row.to_dict() for row in self.response_policy]
        payload["collapse_trace"] = [row.to_dict() for row in self.collapse_trace]
        payload["removal_rounds"] = dict(sorted(self.removal_rounds.items()))
        return json.loads(json.dumps(payload, sort_keys=True))


def _resource_id(row: Mapping[str, Any]) -> str | None:
    value = row.get("resource_id")
    return value if isinstance(value, str) and value else None


def _resource_owner(row: Mapping[str, Any]) -> int | None:
    return _carrier_code(row.get("owner"))


def _state_required_resources(state: Mapping[str, Any]) -> tuple[str, ...]:
    values = state.get("required_resources", [])
    if not isinstance(values, list) or not all(isinstance(value, str) and value for value in values):
        return ()
    return tuple(values)


def _action_required_resources(action: Mapping[str, Any]) -> tuple[str, ...]:
    values = action.get("required_resources", [])
    if not isinstance(values, list) or not all(isinstance(value, str) and value for value in values):
        return ()
    return tuple(values)


def _valid_state(
    state: Mapping[str, Any],
    *,
    target_code: int,
    retained_ids: set[str],
) -> bool:
    state_owner = _carrier_code(state.get("maintenance_owner"))
    budget = state.get("budget")
    required = set(_state_required_resources(state))
    return bool(
        state.get("package_valid") is True
        and state_owner == target_code
        and _is_int(budget)
        and int(budget) >= 0
        and required.issubset(retained_ids)
    )


def _transition_admissible(
    row: Mapping[str, Any],
    *,
    states: Mapping[str, Mapping[str, Any]],
    actions: Mapping[str, Mapping[str, Any]],
    disturbances: Mapping[str, Mapping[str, Any]],
    target_code: int,
    retained_ids: set[str],
    removed_ids: set[str],
    tick_modulus: int,
    candidate_successors: set[str] | None = None,
) -> tuple[bool, tuple[str, ...], ResponseChoice | None]:
    failures: list[str] = []
    source_id = row.get("from_state")
    target_id = row.get("to_state")
    disturbance_id = row.get("disturbance_id")
    action_id = row.get("action_id")
    if not isinstance(source_id, str) or source_id not in states:
        failures.append("unknown-source-state")
    if not isinstance(target_id, str) or target_id not in states:
        failures.append("unknown-successor-state")
    if not isinstance(disturbance_id, str) or disturbance_id not in disturbances:
        failures.append("unknown-disturbance")
    if not isinstance(action_id, str) or action_id not in actions:
        failures.append("unknown-action")
    if failures:
        return False, tuple(failures), None
    source = states[source_id]
    successor = states[target_id]
    action = actions[action_id]
    owner = _carrier_code(action.get("owner"))
    if owner != target_code:
        failures.append("action-not-target-owned")
    required = set(_action_required_resources(action))
    if not required.issubset(retained_ids):
        failures.append("action-requires-nonretained-resource")
    if required.intersection(removed_ids):
        failures.append("action-requires-removed-resource")
    if not _valid_state(source, target_code=target_code, retained_ids=retained_ids):
        failures.append("source-state-not-package-valid-and-resource-closed")
    if not _valid_state(successor, target_code=target_code, retained_ids=retained_ids):
        failures.append("successor-state-not-package-valid-and-resource-closed")
    if candidate_successors is not None and target_id not in candidate_successors:
        failures.append("successor-outside-candidate-region")

    progress_delta = action.get("progress_delta")
    record_delta = action.get("record_delta")
    if not _is_int(progress_delta) or int(progress_delta) <= 0:
        failures.append("no-genuine-progress")
    if not _is_int(record_delta) or int(record_delta) <= 0:
        failures.append("no-strict-record-advance")
    source_phase = source.get("tick_phase")
    successor_phase = successor.get("tick_phase")
    if (
        not _is_int(source_phase)
        or not _is_int(successor_phase)
        or tick_modulus <= 1
        or (int(source_phase) + int(progress_delta or 0)) % tick_modulus != int(successor_phase)
    ):
        failures.append("tick-phase-does-not-realize-progress")

    before = source.get("budget")
    after = successor.get("budget")
    cost = action.get("budget_cost")
    regeneration = action.get("budget_regeneration")
    if not all(_is_int(value) for value in (before, after, cost, regeneration)):
        failures.append("budget-arithmetic-not-integral")
    else:
        before_i = int(before)
        after_i = int(after)
        cost_i = int(cost)
        regeneration_i = int(regeneration)
        if cost_i < 0 or regeneration_i < 0 or before_i < cost_i:
            failures.append("budget-action-insolvent")
        if after_i != before_i - cost_i + regeneration_i:
            failures.append("budget-successor-mismatch")
        if regeneration_i > 0:
            resource = action.get("regeneration_resource")
            if not isinstance(resource, str) or resource not in retained_ids:
                failures.append("regeneration-resource-not-retained")
            if _carrier_code(action.get("regeneration_owner")) != target_code:
                failures.append("regeneration-not-target-owned")

    if failures:
        return False, tuple(sorted(set(failures))), None
    assert isinstance(source_id, str)
    assert isinstance(target_id, str)
    assert isinstance(disturbance_id, str)
    assert isinstance(action_id, str)
    assert owner is not None
    return (
        True,
        (),
        ResponseChoice(
            state_id=source_id,
            disturbance_id=disturbance_id,
            action_id=action_id,
            successor_state_id=target_id,
            action_owner=owner,
            progress_delta=int(progress_delta),
            record_delta=int(record_delta),
            budget_before=int(before),
            budget_cost=int(cost),
            budget_regeneration=int(regeneration),
            budget_after=int(after),
        ),
    )


def _maximal_controlled_invariant(
    model: Mapping[str, Any],
    *,
    states: Mapping[str, Mapping[str, Any]],
    actions: Mapping[str, Mapping[str, Any]],
    disturbances: Mapping[str, Mapping[str, Any]],
    target_code: int,
    retained_ids: set[str],
    removed_ids: set[str],
    tick_modulus: int,
) -> tuple[set[str], dict[str, int], dict[str, str], dict[tuple[str, str], tuple[ResponseChoice, ...]]]:
    candidate = {
        state_id
        for state_id, state in states.items()
        if _valid_state(state, target_code=target_code, retained_ids=retained_ids)
    }
    removal_rounds: dict[str, int] = {state_id: 0 for state_id in states if state_id not in candidate}
    removal_witness: dict[str, str] = {state_id: "invalid-state" for state_id in states if state_id not in candidate}
    transitions = _transition_rows(model)
    round_index = 1
    while True:
        to_remove: dict[str, str] = {}
        for state_id in sorted(candidate):
            for disturbance_id in sorted(disturbances):
                available = []
                for row in transitions:
                    if row.get("from_state") != state_id or row.get("disturbance_id") != disturbance_id:
                        continue
                    ok, _, choice = _transition_admissible(
                        row,
                        states=states,
                        actions=actions,
                        disturbances=disturbances,
                        target_code=target_code,
                        retained_ids=retained_ids,
                        removed_ids=removed_ids,
                        tick_modulus=tick_modulus,
                        candidate_successors=candidate,
                    )
                    if ok and choice is not None:
                        available.append(choice)
                if not available:
                    to_remove[state_id] = disturbance_id
                    break
        if not to_remove:
            break
        for state_id, disturbance_id in to_remove.items():
            candidate.remove(state_id)
            removal_rounds[state_id] = round_index
            removal_witness[state_id] = disturbance_id
        round_index += 1

    response_sets: dict[tuple[str, str], tuple[ResponseChoice, ...]] = {}
    for state_id in sorted(candidate):
        for disturbance_id in sorted(disturbances):
            available: list[ResponseChoice] = []
            for row in transitions:
                if row.get("from_state") != state_id or row.get("disturbance_id") != disturbance_id:
                    continue
                ok, _, choice = _transition_admissible(
                    row,
                    states=states,
                    actions=actions,
                    disturbances=disturbances,
                    target_code=target_code,
                    retained_ids=retained_ids,
                    removed_ids=removed_ids,
                    tick_modulus=tick_modulus,
                    candidate_successors=candidate,
                )
                if ok and choice is not None:
                    available.append(choice)
            response_sets[(state_id, disturbance_id)] = tuple(
                sorted(available, key=lambda item: (item.action_id, item.successor_state_id))
            )
    return candidate, removal_rounds, removal_witness, response_sets


def _canonical_policy(
    candidate: set[str],
    disturbances: Mapping[str, Mapping[str, Any]],
    response_sets: Mapping[tuple[str, str], tuple[ResponseChoice, ...]],
) -> tuple[ResponseChoice, ...]:
    selected: list[ResponseChoice] = []
    for state_id in sorted(candidate):
        for disturbance_id in sorted(disturbances):
            choices = response_sets.get((state_id, disturbance_id), ())
            if choices:
                selected.append(choices[0])
    return tuple(selected)


def _finite_horizon_check(
    endpoint: str,
    horizon: int,
    disturbances: Sequence[str],
    candidate: set[str],
    policy: Mapping[tuple[str, str], ResponseChoice],
) -> tuple[bool, int]:
    if endpoint not in candidate or horizon < 0:
        return False, 0
    words_checked = 0
    for length in range(horizon + 1):
        for word in product(disturbances, repeat=length):
            words_checked += 1
            state = endpoint
            for disturbance in word:
                choice = policy.get((state, disturbance))
                if choice is None or choice.successor_state_id not in candidate:
                    return False, words_checked
                state = choice.successor_state_id
    return True, words_checked


def _collapse_trace(
    endpoint: str,
    *,
    states: Mapping[str, Mapping[str, Any]],
    actions: Mapping[str, Mapping[str, Any]],
    disturbances: Mapping[str, Mapping[str, Any]],
    transitions: Sequence[Mapping[str, Any]],
    target_code: int,
    retained_ids: set[str],
    removed_ids: set[str],
    tick_modulus: int,
    invariant: set[str],
    removal_rounds: Mapping[str, int],
    removal_witness: Mapping[str, str],
) -> tuple[CollapseStep, ...]:
    if endpoint in invariant:
        return ()
    if endpoint not in states:
        return (CollapseStep(endpoint, "", None, None, "unknown-endpoint"),)
    trace: list[CollapseStep] = []
    current = endpoint
    visited: set[str] = set()
    while current not in invariant:
        if current in visited:
            trace.append(CollapseStep(current, "", None, None, "collapse-trace-cycle"))
            break
        visited.add(current)
        disturbance_id = removal_witness.get(current, sorted(disturbances)[0] if disturbances else "")
        if disturbance_id == "invalid-state":
            trace.append(CollapseStep(current, "", None, None, "invalid-package-or-resource-state"))
            break
        candidates: list[tuple[int, ResponseChoice]] = []
        failure_reasons: list[str] = []
        for row in transitions:
            if row.get("from_state") != current or row.get("disturbance_id") != disturbance_id:
                continue
            ok, failures, choice = _transition_admissible(
                row,
                states=states,
                actions=actions,
                disturbances=disturbances,
                target_code=target_code,
                retained_ids=retained_ids,
                removed_ids=removed_ids,
                tick_modulus=tick_modulus,
                candidate_successors=None,
            )
            if ok and choice is not None:
                rank = removal_rounds.get(choice.successor_state_id, -1)
                candidates.append((rank, choice))
            else:
                failure_reasons.extend(failures)
        if not candidates:
            reason = sorted(set(failure_reasons))[0] if failure_reasons else "no-target-owned-safe-response"
            trace.append(CollapseStep(current, disturbance_id, None, None, reason))
            break
        _, choice = max(candidates, key=lambda item: (item[0], item[1].action_id))
        trace.append(
            CollapseStep(
                current,
                disturbance_id,
                choice.action_id,
                choice.successor_state_id,
                None,
            )
        )
        current = choice.successor_state_id
    return tuple(trace)


def audit_autonomy(model: Mapping[str, Any]) -> AutonomyAudit:
    errors: list[str] = []
    model_id = str(model.get("model_id", ""))
    target_code = _carrier_code(model.get("target"))
    source_code = _carrier_code(model.get("source"))
    source_target_distinct = target_code is not None and source_code is not None and target_code != source_code
    if target_code is None:
        target_code = -1
        errors.append("invalid target carrier")
    if source_code is None:
        errors.append("invalid source carrier")

    boundary = model.get("boundary", {})
    boundary_fixed = isinstance(boundary, Mapping) and boundary.get("fixed_before_evaluation") is True
    disturbance_fixed = isinstance(boundary, Mapping) and boundary.get("disturbance_class_fixed_before_evaluation") is True

    removed_rows, retained_rows = _resource_rows(model)
    removed_ids_list = [_resource_id(row) for row in removed_rows]
    retained_ids_list = [_resource_id(row) for row in retained_rows]
    resource_ids_valid = all(value is not None for value in (*removed_ids_list, *retained_ids_list))
    removed_ids = {value for value in removed_ids_list if value is not None}
    retained_ids = {value for value in retained_ids_list if value is not None}
    unique_resources = len(removed_ids) == len(removed_ids_list) and len(retained_ids) == len(retained_ids_list)
    removed_retained_disjoint = removed_ids.isdisjoint(retained_ids)
    removed_roles = {str(row.get("role")) for row in removed_rows if isinstance(row.get("role"), str)}
    mandatory_removed_roles_present = MANDATORY_REMOVED_ROLES.issubset(removed_roles)
    retained_resources_target_owned = all(_resource_owner(row) == target_code for row in retained_rows)

    withdrawal = model.get("withdrawal", {})
    withdrawal_flags = (
        "source_removed",
        "bridge_removed",
        "migration_controller_removed",
        "external_decoder_removed",
        "external_scheduler_removed",
        "undeclared_repair_removed",
    )
    withdrawal_complete = isinstance(withdrawal, Mapping) and all(withdrawal.get(key) is True for key in withdrawal_flags)
    withdrawal_shape_valid = bool(
        isinstance(withdrawal, Mapping)
        and resource_ids_valid
        and unique_resources
        and removed_retained_disjoint
        and mandatory_removed_roles_present
    )

    states = _id_map(model.get("states"), "state_id")
    disturbances = _id_map(model.get("disturbances"), "disturbance_id")
    actions = _id_map(model.get("actions"), "action_id")
    transitions = _transition_rows(model)
    state_rows = model.get("states", [])
    disturbance_rows = model.get("disturbances", [])
    action_rows = model.get("actions", [])
    state_table_well_formed = bool(
        isinstance(state_rows, list)
        and len(states) == len(state_rows)
        and states
        and all(
            _is_int(row.get("tick_phase"))
            and _is_int(row.get("budget"))
            and isinstance(row.get("package_valid"), bool)
            and _carrier_code(row.get("maintenance_owner")) is not None
            and isinstance(row.get("required_resources", []), list)
            for row in states.values()
        )
    )
    disturbance_table_well_formed = bool(
        isinstance(disturbance_rows, list)
        and len(disturbances) == len(disturbance_rows)
        and disturbances
        and all(row.get("predeclared") is True for row in disturbances.values())
    )
    action_table_well_formed = bool(
        isinstance(action_rows, list)
        and len(actions) == len(action_rows)
        and actions
        and all(
            _carrier_code(row.get("owner")) is not None
            and _is_int(row.get("progress_delta"))
            and _is_int(row.get("record_delta"))
            and _is_int(row.get("budget_cost"))
            and _is_int(row.get("budget_regeneration"))
            and isinstance(row.get("required_resources", []), list)
            for row in actions.values()
        )
    )
    transition_keys = {
        (row.get("from_state"), row.get("disturbance_id"), row.get("action_id"), row.get("to_state"))
        for row in transitions
    }
    transition_table_well_formed = bool(
        transitions
        and len(transition_keys) == len(transitions)
        and all(
            isinstance(row.get("from_state"), str)
            and row.get("from_state") in states
            and isinstance(row.get("to_state"), str)
            and row.get("to_state") in states
            and isinstance(row.get("disturbance_id"), str)
            and row.get("disturbance_id") in disturbances
            and isinstance(row.get("action_id"), str)
            and row.get("action_id") in actions
            for row in transitions
        )
    )

    contract = model.get("package_contract", {})
    package_contract_hash_bound = bool(
        isinstance(contract, Mapping)
        and isinstance(contract.get("package_certificate_ref"), str)
        and isinstance(contract.get("package_certificate_sha256"), str)
        and len(contract.get("package_certificate_sha256", "")) == 64
        and contract.get("package_owner") == target_code
    )
    forbidden_hits = _forbidden_hits(model)
    forbidden_absent = not forbidden_hits

    tick_modulus = model.get("tick_modulus")
    if not _is_int(tick_modulus) or int(tick_modulus) <= 1:
        tick_modulus = 2
        errors.append("tick_modulus must be an integer greater than one")
    horizon = model.get("finite_horizon")
    if not _is_int(horizon) or int(horizon) < 0:
        horizon = 0
        errors.append("finite_horizon must be nonnegative")

    invariant, removal_rounds, removal_witness, response_sets = _maximal_controlled_invariant(
        model,
        states=states,
        actions=actions,
        disturbances=disturbances,
        target_code=target_code,
        retained_ids=retained_ids,
        removed_ids=removed_ids,
        tick_modulus=int(tick_modulus),
    )
    declared_raw = model.get("declared_invariant_state_ids", [])
    declared = tuple(sorted(value for value in declared_raw if isinstance(value, str))) if isinstance(declared_raw, list) else ()
    declared_match = set(declared) == invariant and len(declared) == len(set(declared))
    endpoint = model.get("endpoint_state_id")
    endpoint_inside = isinstance(endpoint, str) and endpoint in invariant
    package_inside = bool(invariant) and all(states[state_id].get("package_valid") is True for state_id in invariant)
    resource_closed = bool(invariant) and all(
        set(_state_required_resources(states[state_id])).issubset(retained_ids) for state_id in invariant
    )
    policy_rows = _canonical_policy(invariant, disturbances, response_sets)
    policy = {(row.state_id, row.disturbance_id): row for row in policy_rows}
    required_pair_count = len(invariant) * len(disturbances)
    response_total = bool(invariant) and len(policy_rows) == required_pair_count and all(response_sets.get(key) for key in policy)
    target_owned = response_total and all(row.action_owner == target_code for row in policy_rows)
    anti_stall = response_total and all(
        row.progress_delta > 0 and row.record_delta > 0 and row.state_id != "" for row in policy_rows
    )
    budget_solvent = response_total and all(
        row.budget_before >= row.budget_cost
        and row.budget_after == row.budget_before - row.budget_cost + row.budget_regeneration
        and row.budget_after >= 0
        for row in policy_rows
    )
    horizon_survives, words_checked = _finite_horizon_check(
        endpoint if isinstance(endpoint, str) else "",
        int(horizon),
        tuple(sorted(disturbances)),
        invariant,
        policy,
    )
    collapse = _collapse_trace(
        endpoint if isinstance(endpoint, str) else "",
        states=states,
        actions=actions,
        disturbances=disturbances,
        transitions=transitions,
        target_code=target_code,
        retained_ids=retained_ids,
        removed_ids=removed_ids,
        tick_modulus=int(tick_modulus),
        invariant=invariant,
        removal_rounds=removal_rounds,
        removal_witness=removal_witness,
    )

    obligations = {
        "AUT-O01-distinct-source-and-target": source_target_distinct,
        "AUT-O02-boundary-fixed-before-evaluation": boundary_fixed,
        "AUT-O03-disturbance-class-fixed-before-evaluation": disturbance_fixed,
        "AUT-O04-withdrawal-shape-and-completeness": withdrawal_shape_valid and withdrawal_complete,
        "AUT-O05-target-owned-retained-resources": retained_resources_target_owned,
        "AUT-O06-package-contract-hash-bound": package_contract_hash_bound,
        "AUT-O07-finite-system-well-formed": state_table_well_formed
        and disturbance_table_well_formed
        and action_table_well_formed
        and transition_table_well_formed,
        "AUT-O08-endpoint-in-computed-controlled-invariant": endpoint_inside,
        "AUT-O09-declared-invariant-is-maximal-fixed-point": declared_match,
        "AUT-O10-package-and-resource-closure": package_inside and resource_closed,
        "AUT-O11-target-owned-total-response-law": target_owned and response_total,
        "AUT-O12-anti-stall-progress-and-arrow": anti_stall,
        "AUT-O13-budget-solvency": budget_solvent,
        "AUT-O14-finite-horizon-survival": horizon_survives,
        "AUT-O15-verdict-field-separation": forbidden_absent,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    autonomy_valid = not failed
    if forbidden_hits:
        errors.append("forbidden verdict keys: " + ", ".join(forbidden_hits))
    return AutonomyAudit(
        model_id=model_id,
        source_target_distinct=source_target_distinct,
        boundary_fixed_before_evaluation=boundary_fixed,
        disturbance_class_fixed_before_evaluation=disturbance_fixed,
        withdrawal_shape_valid=withdrawal_shape_valid,
        withdrawal_complete=withdrawal_complete,
        mandatory_removed_roles_present=mandatory_removed_roles_present,
        removed_retained_disjoint=removed_retained_disjoint,
        retained_resources_target_owned=retained_resources_target_owned,
        package_contract_hash_bound=package_contract_hash_bound,
        state_table_well_formed=state_table_well_formed,
        disturbance_table_well_formed=disturbance_table_well_formed,
        action_table_well_formed=action_table_well_formed,
        transition_table_well_formed=transition_table_well_formed,
        forbidden_verdict_fields_absent=forbidden_absent,
        computed_invariant_state_ids=tuple(sorted(invariant)),
        declared_invariant_state_ids=declared,
        declared_invariant_matches_computed=declared_match,
        endpoint_inside=endpoint_inside,
        package_inside=package_inside,
        resource_closed_on_invariant=resource_closed,
        target_owned_responses=target_owned,
        anti_stall_on_invariant=anti_stall,
        budget_solvent_on_invariant=budget_solvent,
        response_total_on_invariant=response_total,
        finite_horizon=int(horizon),
        finite_words_checked=words_checked,
        finite_horizon_survives=horizon_survives,
        response_policy=policy_rows,
        collapse_trace=collapse,
        collapse_trace_length=None if autonomy_valid else len(collapse),
        autonomy_valid=autonomy_valid,
        failed_obligations=failed,
        errors=tuple(sorted(set(errors))),
        removal_rounds=dict(sorted(removal_rounds.items())),
    )


def bounded_invariant_algorithm_exhaustion() -> dict[str, Any]:
    """Exhaust a two-state/two-disturbance deterministic family.

    The family varies successor, action ownership, and progress on each of four
    state/disturbance rows.  For every candidate we compare the fixed-point
    algorithm with brute-force enumeration of all state subsets.
    """

    states = ("q0", "q1")
    disturbances = ("d0", "d1")
    pairs = tuple(product(states, disturbances))
    candidates = 0
    endpoint_autonomous = 0
    mismatches = 0
    for successors in product(states, repeat=len(pairs)):
        for owners in product((0, 1), repeat=len(pairs)):
            for progress in product((0, 1), repeat=len(pairs)):
                candidates += 1
                table = {
                    pair: (successors[index], owners[index] == 1 and progress[index] == 1)
                    for index, pair in enumerate(pairs)
                }

                candidate = set(states)
                while True:
                    remove = {
                        state
                        for state in candidate
                        if any(
                            not table[(state, disturbance)][1]
                            or table[(state, disturbance)][0] not in candidate
                            for disturbance in disturbances
                        )
                    }
                    if not remove:
                        break
                    candidate.difference_update(remove)

                invariant_subsets: list[set[str]] = []
                for mask in range(1 << len(states)):
                    subset = {states[index] for index in range(len(states)) if mask & (1 << index)}
                    if all(
                        table[(state, disturbance)][1]
                        and table[(state, disturbance)][0] in subset
                        for state in subset
                        for disturbance in disturbances
                    ):
                        invariant_subsets.append(subset)
                brute = set().union(*invariant_subsets) if invariant_subsets else set()
                if candidate != brute:
                    mismatches += 1
                if "q0" in candidate:
                    endpoint_autonomous += 1
    return {
        "schema_version": "CST-TT-05",
        "family": "two-state-two-disturbance-successor-owner-progress",
        "candidate_count": candidates,
        "endpoint_autonomous_count": endpoint_autonomous,
        "algorithm_bruteforce_mismatch_count": mismatches,
        "all_candidates_verified": mismatches == 0,
    }


def finite_horizon_word_count(disturbance_count: int, horizon: int) -> int:
    if disturbance_count < 0 or horizon < 0:
        raise ValueError("counts must be nonnegative")
    return sum(disturbance_count**length for length in range(horizon + 1))
