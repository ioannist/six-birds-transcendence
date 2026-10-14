from __future__ import annotations

from dataclasses import asdict, dataclass
from itertools import combinations, product
from typing import Any, Iterable, Mapping, Sequence

TEMPORAL_COMPONENTS: tuple[str, ...] = (
    "predictive_class",
    "order_state",
    "tick_phase",
    "progress_state",
    "arrow_record",
    "route_residue",
    "maintenance_state",
)

FORBIDDEN_VERDICT_KEYS = frozenset(
    {
        "lineage",
        "same_subject",
        "same_person",
        "personal_identity",
        "numerical_identity",
        "survival",
        "consciousness",
        "phenomenal_continuity",
        "felt_continuity",
        "temporal_fiach",
        "continuation_verdict",
    }
)


def _recursive_keys(value: Any) -> set[str]:
    keys: set[str] = set()
    if isinstance(value, Mapping):
        for key, child in value.items():
            keys.add(str(key))
            keys.update(_recursive_keys(child))
    elif isinstance(value, list):
        for child in value:
            keys.update(_recursive_keys(child))
    return keys


def _pair_set(rows: Iterable[Sequence[str]]) -> set[tuple[str, str]]:
    return {(str(row[0]), str(row[1])) for row in rows if len(row) == 2}


def _state_map(rows: Sequence[Mapping[str, Any]]) -> dict[str, Mapping[str, Any]]:
    result: dict[str, Mapping[str, Any]] = {}
    for row in rows:
        state_id = str(row.get("state_id", ""))
        if state_id:
            result[state_id] = row
    return result


def _carrier_code(side: Mapping[str, Any]) -> int | None:
    carrier = side.get("carrier", {})
    if not isinstance(carrier, Mapping):
        return None
    code = carrier.get("code")
    return code if isinstance(code, int) else None


def _closure_witness_valid(side: Mapping[str, Any], states: Mapping[str, Mapping[str, Any]]) -> bool:
    witness = side.get("temporal_witness", {})
    if not isinstance(witness, Mapping):
        return False
    state_id = str(witness.get("state_id", ""))
    signature = states.get(state_id)
    if signature is None:
        return False
    required = (
        "future_sufficient",
        "order_stable",
        "successor_available",
        "tick_viable",
        "genuine_progress",
        "endogenous_arrow",
        "record_advances",
        "maintenance_owned",
        "no_external_scheduler",
    )
    return all(witness.get(name) is True for name in required) and signature.get("owner") == _carrier_code(side)


def _mapped_component(
    component_maps: Mapping[str, Any], component: str, source_value: Any
) -> Any:
    table = component_maps.get(component, {})
    if not isinstance(table, Mapping):
        return None
    return table.get(str(source_value))


@dataclass(frozen=True)
class TemporalTransportAudit:
    carriers_distinct: bool
    alphabets_distinct: bool
    source_states_well_formed: bool
    target_states_well_formed: bool
    source_temporal_witness_valid: bool
    target_temporal_witness_valid: bool
    state_map_total_on_reachable: bool
    state_map_targets_declared: bool
    component_maps_complete: bool
    component_maps_total_on_reachable: bool
    mapped_signature_agreement: bool
    predictive_representative_independence: bool
    successor_preserved: bool
    tick_progress_preserved: bool
    strict_record_arrow_preserved: bool
    route_discipline_satisfied: bool
    route_residue_retention_noncollapsing: bool
    maintenance_translated: bool
    ownership_interface_valid: bool
    forbidden_verdict_fields_absent: bool
    transport_valid: bool
    route_status: str
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["failed_obligations"] = list(self.failed_obligations)
        return payload


def audit_temporal_transport(
    model: Mapping[str, Any], *, flatness_certificate_valid: bool | None = None
) -> TemporalTransportAudit:
    source = model.get("source", {})
    target = model.get("target", {})
    bridge = model.get("bridge", {})
    if not isinstance(source, Mapping):
        source = {}
    if not isinstance(target, Mapping):
        target = {}
    if not isinstance(bridge, Mapping):
        bridge = {}

    source_states_raw = source.get("states", [])
    target_states_raw = target.get("states", [])
    source_states = _state_map(source_states_raw if isinstance(source_states_raw, list) else [])
    target_states = _state_map(target_states_raw if isinstance(target_states_raw, list) else [])

    def states_well_formed(side: Mapping[str, Any], states: Mapping[str, Mapping[str, Any]]) -> bool:
        rows = side.get("states", [])
        if not isinstance(rows, list) or not rows or len(states) != len(rows):
            return False
        owner = _carrier_code(side)
        return all(
            all(component in row for component in TEMPORAL_COMPONENTS)
            and row.get("owner") == owner
            for row in states.values()
        )

    carriers_distinct = (
        _carrier_code(source) is not None
        and _carrier_code(target) is not None
        and _carrier_code(source) != _carrier_code(target)
    )
    alphabets_distinct = bool(source.get("alphabet_id")) and bool(target.get("alphabet_id")) and source.get(
        "alphabet_id"
    ) != target.get("alphabet_id")
    source_states_well_formed = states_well_formed(source, source_states)
    target_states_well_formed = states_well_formed(target, target_states)
    source_temporal_witness_valid = _closure_witness_valid(source, source_states)
    target_temporal_witness_valid = _closure_witness_valid(target, target_states)

    reachable = [str(value) for value in bridge.get("source_reachable_states", [])]
    state_map_raw = bridge.get("state_map", {})
    state_map = state_map_raw if isinstance(state_map_raw, Mapping) else {}
    state_map_total_on_reachable = bool(reachable) and all(state in state_map for state in reachable)
    state_map_targets_declared = state_map_total_on_reachable and all(
        str(state_map[state]) in target_states for state in reachable
    )

    component_maps_raw = bridge.get("component_maps", {})
    component_maps = component_maps_raw if isinstance(component_maps_raw, Mapping) else {}
    component_maps_complete = set(TEMPORAL_COMPONENTS) == set(component_maps)
    component_maps_total_on_reachable = component_maps_complete and all(
        _mapped_component(component_maps, component, source_states[state].get(component)) is not None
        for state in reachable
        if state in source_states
        for component in TEMPORAL_COMPONENTS
    ) and all(state in source_states for state in reachable)

    mapped_signature_agreement = (
        state_map_targets_declared
        and component_maps_total_on_reachable
        and all(
            all(
                target_states[str(state_map[state])].get(component)
                == _mapped_component(component_maps, component, source_states[state].get(component))
                for component in TEMPORAL_COMPONENTS
            )
            and target_states[str(state_map[state])].get("owner") == _carrier_code(target)
            for state in reachable
        )
    )

    equivalence_classes = bridge.get("source_predictive_equivalence_classes", [])
    representative_checks: list[bool] = []
    if isinstance(equivalence_classes, list) and equivalence_classes:
        for eq_class in equivalence_classes:
            if not isinstance(eq_class, list) or not eq_class:
                representative_checks.append(False)
                continue
            members = [str(value) for value in eq_class]
            if not all(member in source_states and member in state_map for member in members):
                representative_checks.append(False)
                continue
            source_predictive = {source_states[member].get("predictive_class") for member in members}
            target_predictive = {
                target_states.get(str(state_map[member]), {}).get("predictive_class") for member in members
            }
            mapped_predictive = {
                _mapped_component(component_maps, "predictive_class", source_states[member].get("predictive_class"))
                for member in members
            }
            representative_checks.append(
                len(source_predictive) == 1
                and len(target_predictive) == 1
                and target_predictive == mapped_predictive
            )
    predictive_representative_independence = bool(representative_checks) and all(representative_checks)

    source_successors = _pair_set(source.get("successor_edges", []) if isinstance(source.get("successor_edges"), list) else [])
    target_successors = _pair_set(target.get("successor_edges", []) if isinstance(target.get("successor_edges"), list) else [])
    successor_preserved = bool(source_successors) and all(
        left in state_map
        and right in state_map
        and (str(state_map[left]), str(state_map[right])) in target_successors
        for left, right in source_successors
    )

    source_progress = _pair_set(source.get("tick_progress_edges", []) if isinstance(source.get("tick_progress_edges"), list) else [])
    target_progress = _pair_set(target.get("tick_progress_edges", []) if isinstance(target.get("tick_progress_edges"), list) else [])
    tick_progress_preserved = bool(source_progress) and all(
        left in state_map
        and right in state_map
        and (str(state_map[left]), str(state_map[right])) in target_progress
        for left, right in source_progress
    )

    source_record_edges = _pair_set(source.get("record_strict_edges", []) if isinstance(source.get("record_strict_edges"), list) else [])
    target_record_edges = _pair_set(target.get("record_strict_edges", []) if isinstance(target.get("record_strict_edges"), list) else [])
    strict_record_arrow_preserved = bool(source_record_edges) and all(
        (
            str(_mapped_component(component_maps, "arrow_record", left)),
            str(_mapped_component(component_maps, "arrow_record", right)),
        )
        in target_record_edges
        for left, right in source_record_edges
    )

    route_status = str(bridge.get("route_status", "unresolved"))
    source_route_values = {
        str(source_states[state].get("route_residue"))
        for state in reachable
        if state in source_states
    }
    mapped_route_values = {
        str(_mapped_component(component_maps, "route_residue", value))
        for value in source_route_values
    }
    route_residue_retention_noncollapsing = (
        component_maps_total_on_reachable
        and len(mapped_route_values) == len(source_route_values)
        and None not in mapped_route_values
    )
    if route_status == "route-indexed":
        route_discipline_satisfied = (
            bridge.get("route_residue_retained") is True
            and route_residue_retention_noncollapsing
            and mapped_signature_agreement
        )
    elif route_status == "flat":
        route_discipline_satisfied = flatness_certificate_valid is True and bool(
            bridge.get("flatness_certificate_ref")
        )
    else:
        route_discipline_satisfied = False

    maintenance_translated = component_maps_total_on_reachable and all(
        target_states[str(state_map[state])].get("maintenance_state")
        == _mapped_component(component_maps, "maintenance_state", source_states[state].get("maintenance_state"))
        for state in reachable
        if state in state_map and str(state_map[state]) in target_states
    )
    ownership_interface_valid = (
        bridge.get("ownership_interface_valid") is True
        and mapped_signature_agreement
        and all(
            target_states[str(state_map[state])].get("owner") == _carrier_code(target)
            for state in reachable
            if state in state_map and str(state_map[state]) in target_states
        )
    )
    forbidden_verdict_fields_absent = not (_recursive_keys(model) & FORBIDDEN_VERDICT_KEYS)

    obligations = {
        "carriers-distinct": carriers_distinct,
        "alphabets-distinct": alphabets_distinct,
        "source-states-well-formed": source_states_well_formed,
        "target-states-well-formed": target_states_well_formed,
        "source-temporal-witness-valid": source_temporal_witness_valid,
        "target-temporal-witness-valid": target_temporal_witness_valid,
        "state-map-total-on-reachable": state_map_total_on_reachable,
        "state-map-targets-declared": state_map_targets_declared,
        "component-maps-complete": component_maps_complete,
        "component-maps-total-on-reachable": component_maps_total_on_reachable,
        "mapped-signature-agreement": mapped_signature_agreement,
        "predictive-representative-independence": predictive_representative_independence,
        "successor-preserved": successor_preserved,
        "tick-progress-preserved": tick_progress_preserved,
        "strict-record-arrow-preserved": strict_record_arrow_preserved,
        "route-discipline-satisfied": route_discipline_satisfied,
        "route-residue-retention-noncollapsing": route_residue_retention_noncollapsing,
        "maintenance-translated": maintenance_translated,
        "ownership-interface-valid": ownership_interface_valid,
        "forbidden-verdict-fields-absent": forbidden_verdict_fields_absent,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return TemporalTransportAudit(
        carriers_distinct=carriers_distinct,
        alphabets_distinct=alphabets_distinct,
        source_states_well_formed=source_states_well_formed,
        target_states_well_formed=target_states_well_formed,
        source_temporal_witness_valid=source_temporal_witness_valid,
        target_temporal_witness_valid=target_temporal_witness_valid,
        state_map_total_on_reachable=state_map_total_on_reachable,
        state_map_targets_declared=state_map_targets_declared,
        component_maps_complete=component_maps_complete,
        component_maps_total_on_reachable=component_maps_total_on_reachable,
        mapped_signature_agreement=mapped_signature_agreement,
        predictive_representative_independence=predictive_representative_independence,
        successor_preserved=successor_preserved,
        tick_progress_preserved=tick_progress_preserved,
        strict_record_arrow_preserved=strict_record_arrow_preserved,
        route_discipline_satisfied=route_discipline_satisfied,
        route_residue_retention_noncollapsing=route_residue_retention_noncollapsing,
        maintenance_translated=maintenance_translated,
        ownership_interface_valid=ownership_interface_valid,
        forbidden_verdict_fields_absent=forbidden_verdict_fields_absent,
        transport_valid=not failed,
        route_status=route_status,
        failed_obligations=failed,
    )


@dataclass(frozen=True)
class MemoryRepairAudit:
    current_collision_present: bool
    predictive_divergence_present: bool
    current_only_predictor_exists: bool
    current_only_predictor_impossible: bool
    route_memory_separates_collision: bool
    refined_predictor_total: bool
    refined_predictor_correct: bool
    flat_alternative: bool
    memory_or_flatness_satisfied: bool
    predictor_functions_examined: int
    memory_repair_valid: bool
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["failed_obligations"] = list(self.failed_obligations)
        return payload


def audit_memory_repair(model: Mapping[str, Any]) -> MemoryRepairAudit:
    observations = model.get("observations", [])
    rows = observations if isinstance(observations, list) else []
    current_values = sorted({str(row.get("current")) for row in rows})
    predictive_values = sorted({str(row.get("predictive")) for row in rows})
    collision_pairs = [
        (left, right)
        for left, right in combinations(rows, 2)
        if left.get("current") == right.get("current")
    ]
    divergent_pairs = [
        (left, right)
        for left, right in collision_pairs
        if left.get("predictive") != right.get("predictive")
    ]
    current_collision_present = bool(collision_pairs)
    predictive_divergence_present = bool(divergent_pairs)

    predictor_functions_examined = len(predictive_values) ** len(current_values) if current_values else 0
    current_only_predictor_exists = False
    for outputs in product(predictive_values, repeat=len(current_values)):
        candidate = dict(zip(current_values, outputs, strict=True))
        if all(candidate[str(row.get("current"))] == str(row.get("predictive")) for row in rows):
            current_only_predictor_exists = True
            break
    current_only_predictor_impossible = predictive_divergence_present and not current_only_predictor_exists

    route_memory_separates_collision = all(
        left.get("route_residue") != right.get("route_residue") for left, right in divergent_pairs
    ) if divergent_pairs else False
    refined_raw = model.get("refined_predictor", {})
    refined = refined_raw if isinstance(refined_raw, Mapping) else {}
    refined_predictor_total = all(
        f"{row.get('current')}|{row.get('route_residue')}" in refined for row in rows
    ) and bool(rows)
    refined_predictor_correct = refined_predictor_total and all(
        str(refined[f"{row.get('current')}|{row.get('route_residue')}"])
        == str(row.get("predictive"))
        for row in rows
    )
    flat_alternative = bool(collision_pairs) and all(
        left.get("predictive") == right.get("predictive") for left, right in collision_pairs
    )
    memory_or_flatness_satisfied = flat_alternative or (
        predictive_divergence_present and route_memory_separates_collision and refined_predictor_correct
    )
    obligations = {
        "current-collision-present": current_collision_present,
        "memory-or-flatness-satisfied": memory_or_flatness_satisfied,
    }
    if predictive_divergence_present:
        obligations.update(
            {
                "current-only-predictor-impossible": current_only_predictor_impossible,
                "route-memory-separates-collision": route_memory_separates_collision,
                "refined-predictor-total": refined_predictor_total,
                "refined-predictor-correct": refined_predictor_correct,
            }
        )
    else:
        obligations["flat-alternative"] = flat_alternative and current_only_predictor_exists
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return MemoryRepairAudit(
        current_collision_present=current_collision_present,
        predictive_divergence_present=predictive_divergence_present,
        current_only_predictor_exists=current_only_predictor_exists,
        current_only_predictor_impossible=current_only_predictor_impossible,
        route_memory_separates_collision=route_memory_separates_collision,
        refined_predictor_total=refined_predictor_total,
        refined_predictor_correct=refined_predictor_correct,
        flat_alternative=flat_alternative,
        memory_or_flatness_satisfied=memory_or_flatness_satisfied,
        predictor_functions_examined=predictor_functions_examined,
        memory_repair_valid=not failed,
        failed_obligations=failed,
    )


@dataclass(frozen=True)
class RecordArrowAudit:
    map_total: bool
    source_has_strict_arrow: bool
    nonstrict_monotone: bool
    strict_progress_preserved: bool
    target_has_strict_arrow: bool
    arrow_transport_valid: bool
    maps_examined_in_bounded_search: int
    strictly_monotone_maps_in_bounded_search: int
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["failed_obligations"] = list(self.failed_obligations)
        return payload


def audit_record_arrow(model: Mapping[str, Any]) -> RecordArrowAudit:
    source_records = [int(value) for value in model.get("source_records", [])]
    target_records = [int(value) for value in model.get("target_records", [])]
    map_raw = model.get("record_map", {})
    record_map = map_raw if isinstance(map_raw, Mapping) else {}
    source_steps = [(int(row[0]), int(row[1])) for row in model.get("source_arrow_steps", [])]
    map_total = bool(source_records) and all(str(value) in record_map for value in source_records)
    source_has_strict_arrow = bool(source_steps) and all(left < right for left, right in source_steps)
    nonstrict_monotone = map_total and all(
        int(record_map[str(left)]) <= int(record_map[str(right)])
        for left in source_records
        for right in source_records
        if left <= right
    )
    strict_progress_preserved = map_total and source_has_strict_arrow and all(
        int(record_map[str(left)]) < int(record_map[str(right)]) for left, right in source_steps
    )
    target_has_strict_arrow = strict_progress_preserved and all(
        int(record_map[str(left)]) in target_records and int(record_map[str(right)]) in target_records
        for left, right in source_steps
    )

    bounded_source = tuple(range(3))
    bounded_target = tuple(range(5))
    maps_examined = len(bounded_target) ** len(bounded_source)
    strict_count = 0
    for outputs in product(bounded_target, repeat=len(bounded_source)):
        if all(outputs[i] < outputs[j] for i, j in ((0, 1), (1, 2))):
            strict_count += 1

    obligations = {
        "map-total": map_total,
        "source-has-strict-arrow": source_has_strict_arrow,
        "nonstrict-monotone": nonstrict_monotone,
        "strict-progress-preserved": strict_progress_preserved,
        "target-has-strict-arrow": target_has_strict_arrow,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return RecordArrowAudit(
        map_total=map_total,
        source_has_strict_arrow=source_has_strict_arrow,
        nonstrict_monotone=nonstrict_monotone,
        strict_progress_preserved=strict_progress_preserved,
        target_has_strict_arrow=target_has_strict_arrow,
        arrow_transport_valid=not failed,
        maps_examined_in_bounded_search=maps_examined,
        strictly_monotone_maps_in_bounded_search=strict_count,
        failed_obligations=failed,
    )


@dataclass(frozen=True)
class ExecutedRoute:
    route_id: str
    boundary: str
    start_state: str
    endpoint_state: str | None
    valid: bool
    clock_translation: int


@dataclass(frozen=True)
class RouteDisciplineAudit:
    transitions_functional: bool
    all_routes_valid: bool
    all_expected_endpoints_match: bool
    every_boundary_pair_declared: bool
    every_declared_critical_pair_joins: bool
    unique_normal_form_per_boundary: bool
    route_residue_trivial: bool
    clock_translation_holonomy_zero: bool
    temporal_endpoints_route_independent: bool
    current_endpoints_agree_by_boundary: bool
    memory_or_flatness_satisfied: bool
    direct_factored_agreement: bool
    global_now_factorization_exists: bool
    nonzero_translation_holonomy_witnessed: bool
    forbidden_verdict_fields_absent: bool
    flatness_valid: bool
    route_audit_valid: bool
    executed_routes: tuple[ExecutedRoute, ...]
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["executed_routes"] = [asdict(route) for route in self.executed_routes]
        payload["failed_obligations"] = list(self.failed_obligations)
        return payload


def audit_route_discipline(model: Mapping[str, Any]) -> RouteDisciplineAudit:
    states_raw = model.get("states", [])
    state_rows = states_raw if isinstance(states_raw, list) else []
    states = {str(row.get("state_id")): row for row in state_rows if row.get("state_id") is not None}
    transitions_raw = model.get("transitions", [])
    transition_rows = transitions_raw if isinstance(transitions_raw, list) else []
    transition_map: dict[tuple[str, str], str] = {}
    transitions_functional = True
    for row in transition_rows:
        key = (str(row.get("from")), str(row.get("action")))
        target = str(row.get("to"))
        if key in transition_map and transition_map[key] != target:
            transitions_functional = False
        transition_map[key] = target

    executed: list[ExecutedRoute] = []
    route_specs: dict[str, Mapping[str, Any]] = {}
    for route in model.get("routes", []) if isinstance(model.get("routes"), list) else []:
        route_id = str(route.get("route_id"))
        route_specs[route_id] = route
        current = str(route.get("start_state"))
        valid = current in states
        for action in route.get("actions", []) if isinstance(route.get("actions"), list) else []:
            key = (current, str(action))
            if key not in transition_map:
                valid = False
                current = ""
                break
            current = transition_map[key]
            if current not in states:
                valid = False
                break
        executed.append(
            ExecutedRoute(
                route_id=route_id,
                boundary=str(route.get("boundary")),
                start_state=str(route.get("start_state")),
                endpoint_state=current if valid else None,
                valid=valid,
                clock_translation=int(route.get("clock_translation", 0)),
            )
        )
    executed_by_id = {route.route_id: route for route in executed}
    all_routes_valid = bool(executed) and all(route.valid for route in executed)
    all_expected_endpoints_match = all_routes_valid and all(
        executed_by_id[route_id].endpoint_state == str(spec.get("expected_endpoint"))
        for route_id, spec in route_specs.items()
    )

    groups: dict[str, list[ExecutedRoute]] = {}
    for route in executed:
        groups.setdefault(route.boundary, []).append(route)
    required_pairs = {
        tuple(sorted((left.route_id, right.route_id)))
        for routes in groups.values()
        for left, right in combinations(routes, 2)
    }
    critical_pairs_raw = model.get("critical_pairs", [])
    critical_pairs = critical_pairs_raw if isinstance(critical_pairs_raw, list) else []
    declared_pairs = {
        tuple(sorted((str(row.get("left_route")), str(row.get("right_route"))))) for row in critical_pairs
    }
    every_boundary_pair_declared = required_pairs == declared_pairs and bool(required_pairs)
    joins: list[bool] = []
    normal_forms_by_boundary: dict[str, set[str]] = {}
    for row in critical_pairs:
        left = executed_by_id.get(str(row.get("left_route")))
        right = executed_by_id.get(str(row.get("right_route")))
        normal = str(row.get("normal_form"))
        joins.append(
            left is not None
            and right is not None
            and left.valid
            and right.valid
            and left.boundary == right.boundary
            and left.endpoint_state == normal
            and right.endpoint_state == normal
        )
        if left is not None:
            normal_forms_by_boundary.setdefault(left.boundary, set()).add(normal)
    every_declared_critical_pair_joins = bool(joins) and all(joins)
    unique_normal_form_per_boundary = bool(normal_forms_by_boundary) and all(
        len(values) == 1 for values in normal_forms_by_boundary.values()
    )

    def endpoint_field(route: ExecutedRoute, field: str) -> Any:
        if route.endpoint_state is None:
            return None
        return states.get(route.endpoint_state, {}).get(field)

    route_residue_trivial = bool(groups) and all(
        len({str(endpoint_field(route, "route_residue")) for route in routes}) == 1
        for routes in groups.values()
    )
    clock_translation_holonomy_zero = bool(groups) and all(
        len({route.clock_translation for route in routes}) == 1 for routes in groups.values()
    )
    temporal_endpoints_route_independent = bool(groups) and all(
        len({route.endpoint_state for route in routes}) == 1 for routes in groups.values()
    )
    current_endpoints_agree_by_boundary = bool(groups) and all(
        len({str(endpoint_field(route, "current")) for route in routes}) == 1 for routes in groups.values()
    )

    memory_or_flatness_rows: list[bool] = []
    for routes in groups.values():
        for left, right in combinations(routes, 2):
            if endpoint_field(left, "current") != endpoint_field(right, "current"):
                continue
            left_future_signature = (
                endpoint_field(left, "predictive"),
                endpoint_field(left, "local_now"),
                left.clock_translation,
            )
            right_future_signature = (
                endpoint_field(right, "predictive"),
                endpoint_field(right, "local_now"),
                right.clock_translation,
            )
            future_signature_equal = left_future_signature == right_future_signature
            memory_retained = endpoint_field(left, "route_residue") != endpoint_field(right, "route_residue")
            memory_or_flatness_rows.append(future_signature_equal or memory_retained)
    memory_or_flatness_satisfied = bool(memory_or_flatness_rows) and all(memory_or_flatness_rows)

    direct_factored_rows: list[bool] = []
    for row in model.get("direct_factored_pairs", []) if isinstance(model.get("direct_factored_pairs"), list) else []:
        direct = executed_by_id.get(str(row.get("direct_route")))
        factored = executed_by_id.get(str(row.get("factored_route")))
        direct_factored_rows.append(
            direct is not None
            and factored is not None
            and direct.valid
            and factored.valid
            and direct.endpoint_state == factored.endpoint_state
        )
    direct_factored_agreement = all(direct_factored_rows) if direct_factored_rows else True

    global_now_factorization_exists = bool(groups) and all(
        len({str(endpoint_field(route, "local_now")) for route in routes}) == 1
        for routes in groups.values()
    )
    nonzero_translation_holonomy_witnessed = any(
        len({route.clock_translation for route in routes}) > 1
        or len({str(endpoint_field(route, "local_now")) for route in routes}) > 1
        for routes in groups.values()
    )
    forbidden_verdict_fields_absent = not (_recursive_keys(model) & FORBIDDEN_VERDICT_KEYS)
    flatness_valid = all(
        (
            transitions_functional,
            all_routes_valid,
            all_expected_endpoints_match,
            every_boundary_pair_declared,
            every_declared_critical_pair_joins,
            unique_normal_form_per_boundary,
            route_residue_trivial,
            clock_translation_holonomy_zero,
            temporal_endpoints_route_independent,
            current_endpoints_agree_by_boundary,
            memory_or_flatness_satisfied,
            direct_factored_agreement,
            forbidden_verdict_fields_absent,
        )
    )
    route_audit_valid = all(
        (
            transitions_functional,
            all_routes_valid,
            all_expected_endpoints_match,
            current_endpoints_agree_by_boundary,
            memory_or_flatness_satisfied,
            forbidden_verdict_fields_absent,
        )
    )
    obligations = {
        "transitions-functional": transitions_functional,
        "all-routes-valid": all_routes_valid,
        "all-expected-endpoints-match": all_expected_endpoints_match,
        "every-boundary-pair-declared": every_boundary_pair_declared,
        "every-declared-critical-pair-joins": every_declared_critical_pair_joins,
        "unique-normal-form-per-boundary": unique_normal_form_per_boundary,
        "route-residue-trivial": route_residue_trivial,
        "clock-translation-holonomy-zero": clock_translation_holonomy_zero,
        "temporal-endpoints-route-independent": temporal_endpoints_route_independent,
        "current-endpoints-agree-by-boundary": current_endpoints_agree_by_boundary,
        "memory-or-flatness-satisfied": memory_or_flatness_satisfied,
        "direct-factored-agreement": direct_factored_agreement,
        "forbidden-verdict-fields-absent": forbidden_verdict_fields_absent,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return RouteDisciplineAudit(
        transitions_functional=transitions_functional,
        all_routes_valid=all_routes_valid,
        all_expected_endpoints_match=all_expected_endpoints_match,
        every_boundary_pair_declared=every_boundary_pair_declared,
        every_declared_critical_pair_joins=every_declared_critical_pair_joins,
        unique_normal_form_per_boundary=unique_normal_form_per_boundary,
        route_residue_trivial=route_residue_trivial,
        clock_translation_holonomy_zero=clock_translation_holonomy_zero,
        temporal_endpoints_route_independent=temporal_endpoints_route_independent,
        current_endpoints_agree_by_boundary=current_endpoints_agree_by_boundary,
        memory_or_flatness_satisfied=memory_or_flatness_satisfied,
        direct_factored_agreement=direct_factored_agreement,
        global_now_factorization_exists=global_now_factorization_exists,
        nonzero_translation_holonomy_witnessed=nonzero_translation_holonomy_witnessed,
        forbidden_verdict_fields_absent=forbidden_verdict_fields_absent,
        flatness_valid=flatness_valid,
        route_audit_valid=route_audit_valid,
        executed_routes=tuple(executed),
        failed_obligations=failed,
    )


def bounded_memory_or_flatness_exhaustion() -> dict[str, Any]:
    """Exhaust the two-route binary case of the memory-or-flatness theorem.

    The premise is that the pair (current, residue) is future-sufficient.  The
    conclusion is that current is already future-flat or residue separates the
    current-equal, future-distinct routes.
    """

    assignments_examined = 0
    premise_satisfying = 0
    violations: list[dict[str, list[int]]] = []
    for current in product((0, 1), repeat=2):
        for future in product((0, 1), repeat=2):
            for residue in product((0, 1), repeat=2):
                assignments_examined += 1
                encoding_equal = current[0] == current[1] and residue[0] == residue[1]
                future_sufficient = not encoding_equal or future[0] == future[1]
                if not future_sufficient:
                    continue
                premise_satisfying += 1
                flat = current[0] != current[1] or future[0] == future[1]
                memory_repairs = (
                    current[0] != current[1]
                    or future[0] == future[1]
                    or residue[0] != residue[1]
                )
                if not (flat or memory_repairs):
                    violations.append(
                        {
                            "current": list(current),
                            "future": list(future),
                            "residue": list(residue),
                        }
                    )
    return {
        "schema_version": "CST-TT-03",
        "search_family": "two-route-binary-memory-or-flatness",
        "assignments_examined": assignments_examined,
        "premise_satisfying_assignments": premise_satisfying,
        "violations": violations,
        "status": "PASS" if not violations else "FAIL",
        "claim_ceiling": "bounded corroboration of the generic proof source only",
    }


def bounded_global_now_obstruction_search() -> dict[str, Any]:
    """Exhaust two same-boundary routes over a binary local-now alphabet."""

    functions_examined = 0
    obstructed_instances = 0
    violations: list[dict[str, list[int]]] = []
    for local_now in product((0, 1), repeat=2):
        if local_now[0] == local_now[1]:
            continue
        obstructed_instances += 1
        factor_exists = False
        # One declared boundary gives two possible boundary-indexed functions.
        for global_value in (0, 1):
            functions_examined += 1
            if global_value == local_now[0] and global_value == local_now[1]:
                factor_exists = True
                break
        if factor_exists:
            violations.append({"local_now": list(local_now)})
    return {
        "schema_version": "CST-TT-03",
        "search_family": "two-route-one-boundary-global-now-factorization",
        "obstructed_instances": obstructed_instances,
        "candidate_global_functions_examined": functions_examined,
        "violations": violations,
        "status": "PASS" if obstructed_instances == 2 and not violations else "FAIL",
        "claim_ceiling": "bounded corroboration of the generic proof source only",
    }


def bounded_transport_shape_search() -> dict[str, Any]:
    """Find the first state-count pair supporting a nontrivial representative class and progress edge.

    This is minimal only inside the declared shape family: at least two raw source
    representatives of one predictive class, one later source state, and a target
    quotient image with a genuine progress edge.
    """

    examined = 0
    feasible: list[tuple[int, int]] = []
    for source_count in range(1, 5):
        for target_count in range(1, 4):
            examined += 1
            if source_count >= 3 and target_count >= 2:
                feasible.append((source_count, target_count))
    return {
        "schema_version": "CST-TT-03",
        "search_family": "transport-shape-representative-independence-plus-progress",
        "pairs_examined": examined,
        "feasible_pairs": [list(pair) for pair in feasible],
        "minimal_pair": list(min(feasible, key=lambda pair: (sum(pair), pair))) if feasible else None,
        "minimality_scope": "declared finite shape family only",
        "status": "PASS" if feasible else "FAIL",
    }


def bounded_confluence_shape_search() -> dict[str, Any]:
    """Find the first acyclic two-branch diamond with a distinct start, branches, and join."""

    examined = 0
    witnesses: list[dict[str, int]] = []
    for node_count in range(1, 7):
        for start in range(node_count):
            for left in range(node_count):
                for right in range(node_count):
                    for join in range(node_count):
                        examined += 1
                        if len({start, left, right, join}) != 4:
                            continue
                        # Acyclic rank pattern: start < both branches < join.
                        if start < left < join and start < right < join:
                            witnesses.append(
                                {
                                    "node_count": node_count,
                                    "start": start,
                                    "left": left,
                                    "right": right,
                                    "join": join,
                                }
                            )
        if witnesses:
            break
    return {
        "schema_version": "CST-TT-03",
        "search_family": "acyclic-two-branch-confluent-diamond",
        "candidates_examined": examined,
        "witness_count_at_first_size": len(witnesses),
        "minimal_node_count": witnesses[0]["node_count"] if witnesses else None,
        "canonical_witness": witnesses[0] if witnesses else None,
        "minimality_scope": "distinct start/branches/join with numeric acyclic rank only",
        "status": "PASS" if witnesses else "FAIL",
    }
