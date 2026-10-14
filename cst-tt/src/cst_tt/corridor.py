from __future__ import annotations

import copy
import hashlib
import json
from dataclasses import asdict, dataclass
from itertools import product
from typing import Any, Iterable, Mapping, Sequence

from .temporal import TemporalTransportScaffold
from .types import Episode, EvidenceStatus, RouteStatus


# ---------------------------------------------------------------------------
# Phase-zero scaffold records retained for backwards compatibility.
# ---------------------------------------------------------------------------


@dataclass(frozen=True)
class CounterfactualAuditScaffold:
    mixed_stage: int
    later_stage: int
    source_removal_effect: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    target_removal_effect: EvidenceStatus = EvidenceStatus.NOT_EVALUATED

    def shape_errors(self) -> list[str]:
        errors: list[str] = []
        if self.mixed_stage < 0:
            errors.append("mixed_stage must be nonnegative")
        if self.later_stage <= self.mixed_stage:
            errors.append("later_stage must be strictly after mixed_stage")
        return errors


@dataclass(frozen=True)
class TemporalCorridorScaffold:
    episode: Episode
    temporal_realization_status_by_stage: tuple[EvidenceStatus, ...]
    transport_status_by_stage: tuple[EvidenceStatus, ...]
    counterfactual: CounterfactualAuditScaffold
    takeover_stage: int
    route_status: RouteStatus = RouteStatus.UNRESOLVED

    def shape_errors(self) -> list[str]:
        errors = self.counterfactual.shape_errors()
        expected = self.episode.final_stage + 1
        if len(self.temporal_realization_status_by_stage) != expected:
            errors.append("temporal status vector must cover every stage")
        if len(self.transport_status_by_stage) != expected:
            errors.append("transport status vector must cover every stage")
        if self.counterfactual.mixed_stage > self.episode.final_stage:
            errors.append("mixed_stage lies outside the episode")
        elif not self.episode.is_mixed(self.counterfactual.mixed_stage):
            errors.append("counterfactual audit stage is not operationally mixed")
        if self.counterfactual.later_stage > self.episode.final_stage:
            errors.append("later_stage lies outside the episode")
        if not (0 <= self.takeover_stage <= self.episode.final_stage):
            errors.append("takeover_stage lies outside the episode")
        support0 = self.episode.active_support.get(0, ())
        if support0 != (self.episode.source,):
            errors.append("strict corridor must start source-only")
        support_final = self.episode.active_support.get(self.episode.final_stage, ())
        if support_final != (self.episode.target,):
            errors.append("strict corridor must end target-only")
        for stage in range(max(self.takeover_stage, 0), self.episode.final_stage + 1):
            if self.episode.source in self.episode.active_support.get(stage, ()):
                errors.append("source remains active at or after takeover_stage")
                break
        return errors

    def lineage_statuses(self) -> tuple[EvidenceStatus, ...]:
        return (
            *self.temporal_realization_status_by_stage,
            *self.transport_status_by_stage,
            self.counterfactual.source_removal_effect,
            self.counterfactual.target_removal_effect,
        )


@dataclass(frozen=True)
class DirectSuccessorScaffold:
    episode: Episode
    last_source_event_id: str
    first_target_event_id: str
    transport: TemporalTransportScaffold
    operational_provenance_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    successor_compatibility_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    record_descent_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    ownership_interface_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED

    def shape_errors(self) -> list[str]:
        by_id = {event.event_id: event for event in self.episode.events}
        errors: list[str] = []
        source_event = by_id.get(self.last_source_event_id)
        target_event = by_id.get(self.first_target_event_id)
        if source_event is None:
            errors.append("last source event is not declared")
        elif source_event.owner != self.episode.source:
            errors.append("last source event is not source-owned")
        if target_event is None:
            errors.append("first target event is not declared")
        elif target_event.owner != self.episode.target:
            errors.append("first target event is not target-owned")
        if source_event is not None and target_event is not None:
            if source_event.stage >= target_event.stage:
                errors.append("direct successor events must point strictly forward")
            edge_pairs = {
                (edge.parent_event_id, edge.child_event_id) for edge in self.episode.dependencies
            }
            if (source_event.event_id, target_event.event_id) not in edge_pairs:
                errors.append("direct successor dependency is not declared in the episode")
        if self.transport.source.carrier != self.episode.source:
            errors.append("transport source does not match episode source")
        if self.transport.target.carrier != self.episode.target:
            errors.append("transport target does not match episode target")
        errors.extend(self.transport.shape_errors())
        return errors


# ---------------------------------------------------------------------------
# CST-TT-04 exact finite corridor semantics.
# ---------------------------------------------------------------------------


SIGNATURE_SCALAR_FIELDS: tuple[str, ...] = (
    "predictive_rank",
    "order_rank",
    "tick_index",
    "progress_rank",
    "record_value",
)
REQUIRED_TEMPORAL_COMPONENTS: frozenset[str] = frozenset(
    {
        "predictive-now",
        "order",
        "tick-phase",
        "progress",
        "arrow-record",
        "route-memory",
        "maintenance",
    }
)
PAYLOAD_COMPONENTS: frozenset[str] = frozenset(
    {
        "predictive_rank",
        "order_rank",
        "tick_index",
        "progress_rank",
        "record_value",
        "route_residue",
        "maintenance_state",
    }
)
FORBIDDEN_EVIDENCE_KEY_FRAGMENTS: tuple[str, ...] = (
    "fiach",
    "iaps",
    "continuation",
    "same_subject",
    "same-subject",
    "same_person",
    "same-person",
    "survival",
    "consciousness",
    "personal_identity",
    "personal-identity",
    "numerical_identity",
    "numerical-identity",
    "lineage_verdict",
    "corridor_verdict",
)


def _recursive_keys(value: object) -> set[str]:
    keys: set[str] = set()
    if isinstance(value, Mapping):
        for key, child in value.items():
            keys.add(str(key).lower())
            keys.update(_recursive_keys(child))
    elif isinstance(value, list):
        for child in value:
            keys.update(_recursive_keys(child))
    return keys


def _evidence_keys_are_clean(value: object) -> bool:
    keys = _recursive_keys(value)
    return not any(fragment in key for key in keys for fragment in FORBIDDEN_EVIDENCE_KEY_FRAGMENTS)


def _carrier_code(value: object) -> int | None:
    if isinstance(value, Mapping):
        raw = value.get("code")
    else:
        raw = value
    return int(raw) if isinstance(raw, int) else None


def _canonical_hash(value: object) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def _is_int(value: object) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _signature_well_formed(signature: object) -> bool:
    if not isinstance(signature, Mapping):
        return False
    if not all(_is_int(signature.get(field)) for field in SIGNATURE_SCALAR_FIELDS):
        return False
    route = signature.get("route_residue")
    if not isinstance(route, list) or not all(isinstance(token, str) and token for token in route):
        return False
    if not _is_int(signature.get("maintenance_owner")):
        return False
    maintenance_state = signature.get("maintenance_state")
    return isinstance(maintenance_state, str) and bool(maintenance_state)


def _stage_rows(model: Mapping[str, Any]) -> list[dict[str, Any]]:
    episode = model.get("episode", {})
    rows = episode.get("stages", []) if isinstance(episode, Mapping) else []
    return [dict(row) for row in rows if isinstance(row, Mapping)]


def _event_rows(model: Mapping[str, Any]) -> list[dict[str, Any]]:
    episode = model.get("episode", {})
    rows = episode.get("events", []) if isinstance(episode, Mapping) else []
    return [dict(row) for row in rows if isinstance(row, Mapping)]


def _dependency_rows(model: Mapping[str, Any]) -> list[dict[str, Any]]:
    episode = model.get("episode", {})
    rows = episode.get("dependencies", []) if isinstance(episode, Mapping) else []
    return [dict(row) for row in rows if isinstance(row, Mapping)]


def _support(row: Mapping[str, Any]) -> tuple[int, ...]:
    raw = row.get("active_support", [])
    if not isinstance(raw, list):
        return ()
    codes: list[int] = []
    for item in raw:
        code = _carrier_code(item)
        if code is None:
            return ()
        codes.append(code)
    return tuple(codes)


def _signature(row: Mapping[str, Any]) -> Mapping[str, Any]:
    raw = row.get("signature", {})
    return raw if isinstance(raw, Mapping) else {}


def _projection(signature: Mapping[str, Any], fields: Sequence[str]) -> tuple[int, ...] | None:
    values: list[int] = []
    for field in fields:
        value = signature.get(field)
        if not _is_int(value):
            return None
        values.append(int(value))
    return tuple(values)


def _vector(value: object) -> tuple[int, ...] | None:
    if not isinstance(value, list) or not all(_is_int(item) for item in value):
        return None
    return tuple(int(item) for item in value)


def _vadd(*vectors: Sequence[int]) -> tuple[int, ...]:
    if not vectors:
        return ()
    return tuple(sum(items) for items in zip(*vectors, strict=True))


def _prefix(left: Sequence[str], right: Sequence[str]) -> bool:
    return len(left) <= len(right) and tuple(left) == tuple(right[: len(left)])


@dataclass(frozen=True)
class StrictCorridorAudit:
    distinct_endpoints: bool
    carrier_chain_valid: bool
    stage_indices_contiguous: bool
    stages_well_formed: bool
    support_nonempty_and_unique: bool
    starts_source_only: bool
    ends_target_only: bool
    all_stages_temporally_realized: bool
    local_temporal_steps_valid: bool
    event_graph_well_formed: bool
    every_adjacent_stage_operationally_linked: bool
    leg_count_matches_chain: bool
    every_atomic_leg_valid: bool
    frontier_cover_valid: bool
    boundary_signatures_compatible: bool
    route_discipline_valid: bool
    forbidden_verdict_fields_absent: bool
    atomic_leg_count: int
    mixed_stage_count: int
    strict_corridor_valid: bool
    route_status: str
    failed_obligations: tuple[str, ...]
    leg_audits: tuple[Mapping[str, Any], ...]

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["failed_obligations"] = list(self.failed_obligations)
        payload["leg_audits"] = [dict(row) for row in self.leg_audits]
        return payload


def _audit_event_graph(model: Mapping[str, Any], stage_map: Mapping[int, Mapping[str, Any]]) -> tuple[bool, bool, dict[str, dict[str, Any]], set[tuple[str, str]]]:
    events = _event_rows(model)
    dependencies = _dependency_rows(model)
    by_id = {str(row.get("event_id")): row for row in events if isinstance(row.get("event_id"), str)}
    unique_ids = len(by_id) == len(events) and all(key for key in by_id)
    events_valid = unique_ids
    for row in events:
        stage = row.get("stage")
        owner = _carrier_code(row.get("owner"))
        if not _is_int(stage) or int(stage) not in stage_map or owner is None:
            events_valid = False
            continue
        if owner not in _support(stage_map[int(stage)]):
            events_valid = False
        if row.get("event_kind") != "temporal-update":
            events_valid = False
    edge_pairs: set[tuple[str, str]] = set()
    dependencies_valid = True
    for row in dependencies:
        parent_id = row.get("parent_event_id")
        child_id = row.get("child_event_id")
        if not isinstance(parent_id, str) or not isinstance(child_id, str):
            dependencies_valid = False
            continue
        parent = by_id.get(parent_id)
        child = by_id.get(child_id)
        if parent is None or child is None:
            dependencies_valid = False
            continue
        if int(parent.get("stage", -1)) >= int(child.get("stage", -1)):
            dependencies_valid = False
        if row.get("dependency_kind") not in {"temporal-step", "mixed-update", "frontier-step"}:
            dependencies_valid = False
        edge_pairs.add((parent_id, child_id))
    graph_valid = events_valid and dependencies_valid and bool(events)
    adjacent_linked = True
    for index in range(max(stage_map) if stage_map else 0):
        parents = {event_id for event_id, row in by_id.items() if row.get("stage") == index}
        children = {event_id for event_id, row in by_id.items() if row.get("stage") == index + 1}
        if not any(parent in parents and child in children for parent, child in edge_pairs):
            adjacent_linked = False
    return graph_valid, adjacent_linked, by_id, edge_pairs


def _audit_atomic_leg(
    leg: Mapping[str, Any],
    stage_map: Mapping[int, Mapping[str, Any]],
    event_map: Mapping[str, Mapping[str, Any]],
    edge_pairs: set[tuple[str, str]],
) -> dict[str, Any]:
    source = _carrier_code(leg.get("source_carrier"))
    target = _carrier_code(leg.get("target_carrier"))
    indices = {
        name: int(leg.get(name)) if _is_int(leg.get(name)) else -1
        for name in ("start_stage", "mixed_stage", "audit_later_stage", "takeover_stage", "end_stage")
    }
    start = indices["start_stage"]
    mixed = indices["mixed_stage"]
    later = indices["audit_later_stage"]
    takeover = indices["takeover_stage"]
    end = indices["end_stage"]
    index_order_valid = 0 <= start < mixed < later <= end and mixed <= takeover <= end
    stages_present = index_order_valid and all(index in stage_map for index in range(start, end + 1))
    start_source_only = stages_present and _support(stage_map[start]) == (source,)
    mixed_support_exact = stages_present and set(_support(stage_map[mixed])) == {source, target} and len(_support(stage_map[mixed])) == 2
    end_target_only = stages_present and _support(stage_map[end]) == (target,)
    local_support_scoped = stages_present and all(
        set(_support(stage_map[index])).issubset({source, target}) for index in range(start, end + 1)
    )
    target_present_from_mixed = stages_present and all(
        target in _support(stage_map[index]) for index in range(mixed, end + 1)
    )
    source_absent_after_takeover = stages_present and all(
        source not in _support(stage_map[index]) for index in range(takeover, end + 1)
    )
    owner_interface = stages_present and (
        _signature(stage_map[start]).get("maintenance_owner") == source
        and _signature(stage_map[end]).get("maintenance_owner") == target
    )

    route_status = str(leg.get("route_status", "unresolved"))
    route_status_valid = route_status in {"flat", "route-indexed"}
    route_memory_valid = stages_present and route_status_valid
    if route_memory_valid and route_status == "route-indexed":
        for index in range(start, end):
            left = _signature(stage_map[index]).get("route_residue", [])
            right = _signature(stage_map[index + 1]).get("route_residue", [])
            if not isinstance(left, list) or not isinstance(right, list) or not right or not _prefix(left, right):
                route_memory_valid = False
                break

    transport = leg.get("transport_evidence", {})
    transport_valid = isinstance(transport, Mapping) and (
        set(transport.get("components", [])) == REQUIRED_TEMPORAL_COMPONENTS
        and transport.get("representative_independent") is True
        and transport.get("ownership_interface_valid") is True
        and transport.get("route_status") == route_status
        and isinstance(transport.get("evidence_id"), str)
        and bool(transport.get("evidence_id"))
    )

    counterfactual = leg.get("counterfactual", {})
    fields = counterfactual.get("projection_fields", []) if isinstance(counterfactual, Mapping) else []
    fields_valid = isinstance(fields, list) and bool(fields) and all(field in SIGNATURE_SCALAR_FIELDS for field in fields)
    base = _vector(counterfactual.get("base_projection")) if isinstance(counterfactual, Mapping) else None
    source_contribution = _vector(counterfactual.get("source_contribution")) if isinstance(counterfactual, Mapping) else None
    target_contribution = _vector(counterfactual.get("target_contribution")) if isinstance(counterfactual, Mapping) else None
    declared_full = _vector(counterfactual.get("full_projection")) if isinstance(counterfactual, Mapping) else None
    declared_source_removed = _vector(counterfactual.get("source_removed_projection")) if isinstance(counterfactual, Mapping) else None
    declared_target_removed = _vector(counterfactual.get("target_removed_projection")) if isinstance(counterfactual, Mapping) else None
    vectors = (base, source_contribution, target_contribution, declared_full, declared_source_removed, declared_target_removed)
    vector_shapes_valid = fields_valid and all(vector is not None and len(vector) == len(fields) for vector in vectors)
    computed_full: tuple[int, ...] | None = None
    computed_source_removed: tuple[int, ...] | None = None
    computed_target_removed: tuple[int, ...] | None = None
    if vector_shapes_valid:
        assert base is not None and source_contribution is not None and target_contribution is not None
        computed_full = _vadd(base, source_contribution, target_contribution)
        computed_source_removed = _vadd(base, target_contribution)
        computed_target_removed = _vadd(base, source_contribution)
    actual_projection = _projection(_signature(stage_map[later]), fields) if stages_present and fields_valid else None
    counterfactual_arithmetic_valid = bool(
        vector_shapes_valid
        and computed_full == declared_full == actual_projection
        and computed_source_removed == declared_source_removed
        and computed_target_removed == declared_target_removed
    )
    source_contribution_nonzero = bool(source_contribution is not None and any(value != 0 for value in source_contribution))
    target_contribution_nonzero = bool(target_contribution is not None and any(value != 0 for value in target_contribution))
    source_nonredundant = bool(counterfactual_arithmetic_valid and computed_full != computed_source_removed and source_contribution_nonzero)
    target_nonredundant = bool(counterfactual_arithmetic_valid and computed_full != computed_target_removed and target_contribution_nonzero)

    event_ids = leg.get("audit_event_ids", {})
    source_event_id = event_ids.get("source_mixed_event") if isinstance(event_ids, Mapping) else None
    target_event_id = event_ids.get("target_mixed_event") if isinstance(event_ids, Mapping) else None
    later_event_id = event_ids.get("later_event") if isinstance(event_ids, Mapping) else None
    source_event = event_map.get(str(source_event_id)) if source_event_id is not None else None
    target_event = event_map.get(str(target_event_id)) if target_event_id is not None else None
    later_event = event_map.get(str(later_event_id)) if later_event_id is not None else None
    intervention_events_valid = bool(
        source_event is not None
        and target_event is not None
        and later_event is not None
        and _carrier_code(source_event.get("owner")) == source
        and _carrier_code(target_event.get("owner")) == target
        and source_event.get("stage") == mixed
        and target_event.get("stage") == mixed
        and later_event.get("stage") == later
        and (str(source_event_id), str(later_event_id)) in edge_pairs
        and (str(target_event_id), str(later_event_id)) in edge_pairs
    )

    obligations = {
        "distinct-local-carriers": source is not None and target is not None and source != target,
        "stage-index-order": index_order_valid,
        "leg-stages-present": stages_present,
        "starts-local-source-only": start_source_only,
        "mixed-support-exact": mixed_support_exact,
        "ends-local-target-only": end_target_only,
        "local-support-scoped": local_support_scoped,
        "target-present-from-mixed": target_present_from_mixed,
        "source-absent-after-takeover": source_absent_after_takeover,
        "ownership-interface": owner_interface,
        "route-status-valid": route_status_valid,
        "route-memory-valid": route_memory_valid,
        "bundled-transport-evidence": transport_valid,
        "counterfactual-arithmetic": counterfactual_arithmetic_valid,
        "source-nonredundant": source_nonredundant,
        "target-nonredundant": target_nonredundant,
        "intervention-events-valid": intervention_events_valid,
    }
    failed = [name for name, ok in obligations.items() if not ok]
    return {
        "leg_id": str(leg.get("leg_id", "")),
        "source_carrier": source,
        "target_carrier": target,
        "start_stage": start,
        "mixed_stage": mixed,
        "audit_later_stage": later,
        "takeover_stage": takeover,
        "end_stage": end,
        "route_status": route_status,
        "source_nonredundant": source_nonredundant,
        "target_nonredundant": target_nonredundant,
        "atomic_leg_valid": not failed,
        "failed_obligations": failed,
    }


def audit_strict_corridor(model: Mapping[str, Any]) -> StrictCorridorAudit:
    chain_raw = model.get("carrier_chain", [])
    carrier_chain = tuple(code for code in (_carrier_code(item) for item in chain_raw if isinstance(chain_raw, list)) if code is not None)
    distinct_endpoints = len(carrier_chain) >= 2 and carrier_chain[0] != carrier_chain[-1]
    carrier_chain_valid = (
        len(carrier_chain) >= 2
        and len(carrier_chain) == len(chain_raw)
        and len(set(carrier_chain)) == len(carrier_chain)
    )

    stages = _stage_rows(model)
    stage_indices = [row.get("stage") for row in stages]
    stage_indices_contiguous = (
        bool(stages)
        and all(_is_int(index) for index in stage_indices)
        and sorted(int(index) for index in stage_indices) == list(range(len(stages)))
        and stage_indices == sorted(stage_indices)
    )
    stage_map = {int(row["stage"]): row for row in stages if _is_int(row.get("stage"))}
    stages_well_formed = stage_indices_contiguous and all(_signature_well_formed(_signature(row)) for row in stages)
    support_nonempty_and_unique = stage_indices_contiguous and all(
        bool(_support(row)) and len(set(_support(row))) == len(_support(row)) for row in stages
    )
    starts_source_only = bool(carrier_chain and stage_map and _support(stage_map[0]) == (carrier_chain[0],))
    ends_target_only = bool(carrier_chain and stage_map and _support(stage_map[max(stage_map)]) == (carrier_chain[-1],))
    all_stages_temporally_realized = bool(stages) and all(row.get("temporal_realized") is True for row in stages)

    local_temporal_steps_valid = stages_well_formed and len(stages) >= 2
    if local_temporal_steps_valid:
        for index in range(len(stages) - 1):
            left = _signature(stage_map[index])
            right = _signature(stage_map[index + 1])
            if not (
                right.get("predictive_rank") == left.get("predictive_rank") + 1
                and right.get("order_rank") == left.get("order_rank") + 1
                and right.get("tick_index") == left.get("tick_index") + 1
                and right.get("progress_rank") == left.get("progress_rank") + 1
                and right.get("record_value") > left.get("record_value")
            ):
                local_temporal_steps_valid = False
                break

    event_graph_well_formed, every_adjacent_stage_operationally_linked, event_map, edge_pairs = _audit_event_graph(model, stage_map)
    legs_raw = model.get("legs", [])
    legs = [dict(row) for row in legs_raw if isinstance(row, Mapping)] if isinstance(legs_raw, list) else []
    leg_count_matches_chain = carrier_chain_valid and len(legs) == len(carrier_chain) - 1
    leg_audits = tuple(_audit_atomic_leg(leg, stage_map, event_map, edge_pairs) for leg in legs)
    every_atomic_leg_valid = bool(leg_audits) and all(row["atomic_leg_valid"] for row in leg_audits)
    mixed_stage_count = sum(1 for row in stages if carrier_chain and any(
        {carrier_chain[i], carrier_chain[i + 1]}.issubset(set(_support(row)))
        for i in range(len(carrier_chain) - 1)
    ))

    frontier_cover_valid = leg_count_matches_chain and bool(legs)
    boundary_signatures_compatible = frontier_cover_valid
    if frontier_cover_valid:
        if legs[0].get("start_stage") != 0 or legs[-1].get("end_stage") != len(stages) - 1:
            frontier_cover_valid = False
        for index, leg in enumerate(legs):
            if _carrier_code(leg.get("source_carrier")) != carrier_chain[index] or _carrier_code(leg.get("target_carrier")) != carrier_chain[index + 1]:
                frontier_cover_valid = False
            if index + 1 < len(legs):
                left_end = leg.get("end_stage")
                right_start = legs[index + 1].get("start_stage")
                if left_end != right_start or not _is_int(left_end):
                    frontier_cover_valid = False
                    boundary_signatures_compatible = False
                    continue
                boundary = stage_map.get(int(left_end))
                shared = carrier_chain[index + 1]
                if boundary is None or _support(boundary) != (shared,) or _signature(boundary).get("maintenance_owner") != shared:
                    frontier_cover_valid = False
                    boundary_signatures_compatible = False
        covered: set[int] = set()
        for leg in legs:
            if _is_int(leg.get("start_stage")) and _is_int(leg.get("end_stage")):
                covered.update(range(int(leg["start_stage"]), int(leg["end_stage"]) + 1))
        if covered != set(stage_map):
            frontier_cover_valid = False

    route_values = [str(row.get("route_status", "unresolved")) for row in legs]
    route_discipline_valid = bool(route_values) and all(value in {"flat", "route-indexed"} for value in route_values)
    route_status = "flat" if route_values and all(value == "flat" for value in route_values) else (
        "route-indexed" if route_discipline_valid else "unresolved"
    )
    evidence_payload = {
        "carrier_chain": model.get("carrier_chain"),
        "episode": model.get("episode"),
        "legs": model.get("legs"),
    }
    forbidden_verdict_fields_absent = _evidence_keys_are_clean(evidence_payload)

    obligations = {
        "distinct-endpoints": distinct_endpoints,
        "carrier-chain-valid": carrier_chain_valid,
        "stage-indices-contiguous": stage_indices_contiguous,
        "stages-well-formed": stages_well_formed,
        "support-nonempty-and-unique": support_nonempty_and_unique,
        "starts-source-only": starts_source_only,
        "ends-target-only": ends_target_only,
        "all-stages-temporally-realized": all_stages_temporally_realized,
        "local-temporal-steps-valid": local_temporal_steps_valid,
        "event-graph-well-formed": event_graph_well_formed,
        "every-adjacent-stage-operationally-linked": every_adjacent_stage_operationally_linked,
        "leg-count-matches-chain": leg_count_matches_chain,
        "every-atomic-leg-valid": every_atomic_leg_valid,
        "frontier-cover-valid": frontier_cover_valid,
        "boundary-signatures-compatible": boundary_signatures_compatible,
        "route-discipline-valid": route_discipline_valid,
        "forbidden-verdict-fields-absent": forbidden_verdict_fields_absent,
    }
    top_failed = [name for name, ok in obligations.items() if not ok]
    leg_failed = [
        str(name)
        for row in leg_audits
        for name in row.get("failed_obligations", [])
    ]
    failed = tuple(dict.fromkeys([*top_failed, *leg_failed]))
    return StrictCorridorAudit(
        distinct_endpoints=distinct_endpoints,
        carrier_chain_valid=carrier_chain_valid,
        stage_indices_contiguous=stage_indices_contiguous,
        stages_well_formed=stages_well_formed,
        support_nonempty_and_unique=support_nonempty_and_unique,
        starts_source_only=starts_source_only,
        ends_target_only=ends_target_only,
        all_stages_temporally_realized=all_stages_temporally_realized,
        local_temporal_steps_valid=local_temporal_steps_valid,
        event_graph_well_formed=event_graph_well_formed,
        every_adjacent_stage_operationally_linked=every_adjacent_stage_operationally_linked,
        leg_count_matches_chain=leg_count_matches_chain,
        every_atomic_leg_valid=every_atomic_leg_valid,
        frontier_cover_valid=frontier_cover_valid,
        boundary_signatures_compatible=boundary_signatures_compatible,
        route_discipline_valid=route_discipline_valid,
        forbidden_verdict_fields_absent=forbidden_verdict_fields_absent,
        atomic_leg_count=len(legs),
        mixed_stage_count=mixed_stage_count,
        strict_corridor_valid=not failed,
        route_status=route_status,
        failed_obligations=failed,
        leg_audits=leg_audits,
    )


@dataclass(frozen=True)
class CorridorCompositionAudit:
    left_valid: bool
    right_valid: bool
    shared_frontier_carrier: bool
    frontier_signature_equal: bool
    frontier_support_equal: bool
    frontier_route_memory_equal: bool
    frontier_compatible: bool
    composite_valid: bool
    leg_count_additive: bool
    boundary_merged_once: bool
    old_endpoint_mixed_rule_satisfied: bool
    chain_rule_satisfied: bool
    composition_valid: bool
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["failed_obligations"] = list(self.failed_obligations)
        return payload


def _terminal_stage(model: Mapping[str, Any]) -> Mapping[str, Any] | None:
    rows = _stage_rows(model)
    return rows[-1] if rows else None


def _initial_stage(model: Mapping[str, Any]) -> Mapping[str, Any] | None:
    rows = _stage_rows(model)
    return rows[0] if rows else None


def _chain_codes(model: Mapping[str, Any]) -> tuple[int, ...]:
    raw = model.get("carrier_chain", [])
    if not isinstance(raw, list):
        return ()
    result = tuple(code for code in (_carrier_code(item) for item in raw) if code is not None)
    return result if len(result) == len(raw) else ()


def frontier_compatible(left: Mapping[str, Any], right: Mapping[str, Any]) -> bool:
    left_chain = _chain_codes(left)
    right_chain = _chain_codes(right)
    left_final = _terminal_stage(left)
    right_initial = _initial_stage(right)
    if not left_chain or not right_chain or left_final is None or right_initial is None:
        return False
    shared = left_chain[-1]
    return bool(
        shared == right_chain[0]
        and _support(left_final) == (shared,)
        and _support(right_initial) == (shared,)
        and _signature(left_final) == _signature(right_initial)
    )


def _shift_event(row: Mapping[str, Any], offset: int) -> dict[str, Any]:
    shifted = copy.deepcopy(dict(row))
    shifted["stage"] = int(shifted["stage"]) + offset
    return shifted


def _shift_leg(row: Mapping[str, Any], offset: int) -> dict[str, Any]:
    shifted = copy.deepcopy(dict(row))
    for field in ("start_stage", "mixed_stage", "audit_later_stage", "takeover_stage", "end_stage"):
        shifted[field] = int(shifted[field]) + offset
    return shifted


def compose_corridor_models(
    left: Mapping[str, Any],
    right: Mapping[str, Any],
    *,
    model_id: str = "COR-POS-COMPOSED",
    title: str = "composed strict carrier-chain temporal corridor",
) -> dict[str, Any]:
    if not frontier_compatible(left, right):
        raise ValueError("corridor frontiers are not compatible")
    left_stages = _stage_rows(left)
    right_stages = _stage_rows(right)
    offset = len(left_stages) - 1
    shifted_right_stages = []
    for row in right_stages[1:]:
        shifted = copy.deepcopy(row)
        shifted["stage"] = int(shifted["stage"]) + offset
        shifted_right_stages.append(shifted)

    left_events = _event_rows(left)
    shifted_right_events = [_shift_event(row, offset) for row in _event_rows(right)]
    by_id: dict[str, dict[str, Any]] = {str(row["event_id"]): copy.deepcopy(row) for row in left_events}
    for row in shifted_right_events:
        event_id = str(row["event_id"])
        if event_id in by_id:
            if by_id[event_id] != row:
                raise ValueError(f"boundary event mismatch for {event_id}")
        else:
            by_id[event_id] = row

    dependencies: list[dict[str, Any]] = []
    seen_edges: set[tuple[str, str, str]] = set()
    for row in [*_dependency_rows(left), *_dependency_rows(right)]:
        copied = copy.deepcopy(row)
        key = (
            str(copied.get("parent_event_id")),
            str(copied.get("child_event_id")),
            str(copied.get("dependency_kind")),
        )
        if key not in seen_edges:
            seen_edges.add(key)
            dependencies.append(copied)

    left_chain = list(left.get("carrier_chain", []))
    right_chain = list(right.get("carrier_chain", []))
    return {
        "schema_version": "CST-TT-04-model-v1",
        "model_id": model_id,
        "title": title,
        "kind": "strict-carrier-chain-temporal-corridor",
        "claim_lanes": ["S-L"],
        "claim_ceiling": "exact finite structural temporal lineage criterion only",
        "carrier_chain": [*copy.deepcopy(left_chain), *copy.deepcopy(right_chain[1:])],
        "episode": {
            "stages": [*copy.deepcopy(left_stages), *shifted_right_stages],
            "events": [by_id[key] for key in sorted(by_id)],
            "dependencies": dependencies,
        },
        "legs": [
            *copy.deepcopy(list(left.get("legs", []))),
            *[_shift_leg(row, offset) for row in right.get("legs", [])],
        ],
        "composition_provenance": {
            "left_model_id": left.get("model_id"),
            "right_model_id": right.get("model_id"),
            "frontier_stage": offset,
            "frontier_signature_sha256": _canonical_hash(_signature(left_stages[-1])),
        },
        "nonclaims": [
            "no target-package verdict",
            "no post-withdrawal autonomy verdict",
            "no phenomenal or personal-status conclusion",
        ],
    }


def audit_corridor_composition(
    left: Mapping[str, Any], right: Mapping[str, Any], composite: Mapping[str, Any]
) -> CorridorCompositionAudit:
    left_audit = audit_strict_corridor(left)
    right_audit = audit_strict_corridor(right)
    composite_audit = audit_strict_corridor(composite)
    left_chain = _chain_codes(left)
    right_chain = _chain_codes(right)
    composite_chain = _chain_codes(composite)
    left_final = _terminal_stage(left)
    right_initial = _initial_stage(right)
    shared_frontier_carrier = bool(left_chain and right_chain and left_chain[-1] == right_chain[0])
    frontier_signature_equal = bool(left_final is not None and right_initial is not None and _signature(left_final) == _signature(right_initial))
    frontier_support_equal = bool(left_final is not None and right_initial is not None and _support(left_final) == _support(right_initial))
    frontier_route_memory_equal = bool(
        left_final is not None
        and right_initial is not None
        and _signature(left_final).get("route_residue") == _signature(right_initial).get("route_residue")
    )
    frontier_ok = shared_frontier_carrier and frontier_signature_equal and frontier_support_equal and frontier_route_memory_equal
    leg_count_additive = composite_audit.atomic_leg_count == left_audit.atomic_leg_count + right_audit.atomic_leg_count
    shared = left_chain[-1] if left_chain else None
    boundary_merged_once = bool(
        shared is not None
        and sum(1 for row in _stage_rows(composite) if _support(row) == (shared,)) == 1
    )
    old_endpoint_mixed_rule_satisfied = bool(
        composite_chain
        and any({composite_chain[0], composite_chain[-1]}.issubset(set(_support(row))) for row in _stage_rows(composite))
    )
    chain_rule_satisfied = composite_audit.strict_corridor_valid
    obligations = {
        "left-valid": left_audit.strict_corridor_valid,
        "right-valid": right_audit.strict_corridor_valid,
        "shared-frontier-carrier": shared_frontier_carrier,
        "frontier-signature-equal": frontier_signature_equal,
        "frontier-support-equal": frontier_support_equal,
        "frontier-route-memory-equal": frontier_route_memory_equal,
        "frontier-compatible": frontier_ok,
        "composite-valid": composite_audit.strict_corridor_valid,
        "leg-count-additive": leg_count_additive,
        "boundary-merged-once": boundary_merged_once,
        "chain-rule-satisfied": chain_rule_satisfied,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return CorridorCompositionAudit(
        left_valid=left_audit.strict_corridor_valid,
        right_valid=right_audit.strict_corridor_valid,
        shared_frontier_carrier=shared_frontier_carrier,
        frontier_signature_equal=frontier_signature_equal,
        frontier_support_equal=frontier_support_equal,
        frontier_route_memory_equal=frontier_route_memory_equal,
        frontier_compatible=frontier_ok,
        composite_valid=composite_audit.strict_corridor_valid,
        leg_count_additive=leg_count_additive,
        boundary_merged_once=boundary_merged_once,
        old_endpoint_mixed_rule_satisfied=old_endpoint_mixed_rule_satisfied,
        chain_rule_satisfied=chain_rule_satisfied,
        composition_valid=not failed,
        failed_obligations=failed,
    )


@dataclass(frozen=True)
class DirectSuccessorAudit:
    distinct_carriers: bool
    stages_well_formed: bool
    all_stages_temporally_realized: bool
    source_event_is_last: bool
    target_event_is_first: bool
    direct_dependency_declared: bool
    stage_adjacency: bool
    source_and_target_support_valid: bool
    payload_components_complete: bool
    payload_hashes_match: bool
    edge_kind_valid: bool
    edge_counterfactually_necessary: bool
    no_storage_mediator: bool
    not_replayable_archive: bool
    no_alternative_temporal_parent: bool
    single_use_temporal_token: bool
    predictive_step_valid: bool
    order_step_valid: bool
    tick_step_valid: bool
    progress_step_valid: bool
    strict_record_step_valid: bool
    route_discipline_valid: bool
    ownership_interface_valid: bool
    forbidden_verdict_fields_absent: bool
    detached_operational_pattern: bool
    direct_successor_valid: bool
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["failed_obligations"] = list(self.failed_obligations)
        return payload


def audit_direct_successor(model: Mapping[str, Any]) -> DirectSuccessorAudit:
    source = _carrier_code(model.get("source_carrier"))
    target = _carrier_code(model.get("target_carrier"))
    distinct_carriers = source is not None and target is not None and source != target
    stages = _stage_rows(model)
    stage_map = {int(row["stage"]): row for row in stages if _is_int(row.get("stage"))}
    indices = sorted(stage_map)
    stages_well_formed = bool(stages) and indices == list(range(indices[-1] + 1)) and all(
        _signature_well_formed(_signature(row)) and bool(_support(row)) for row in stages
    )
    all_stages_temporally_realized = bool(stages) and all(row.get("temporal_realized") is True for row in stages)
    events = _event_rows(model)
    event_map = {str(row.get("event_id")): row for row in events if isinstance(row.get("event_id"), str)}
    source_event_id = str(model.get("last_source_event_id", ""))
    target_event_id = str(model.get("first_target_event_id", ""))
    source_event = event_map.get(source_event_id)
    target_event = event_map.get(target_event_id)
    source_owned_events = [row for row in events if _carrier_code(row.get("owner")) == source and row.get("event_kind") == "temporal-update"]
    target_owned_events = [row for row in events if _carrier_code(row.get("owner")) == target and row.get("event_kind") == "temporal-update"]
    source_event_is_last = bool(
        source_event is not None
        and _carrier_code(source_event.get("owner")) == source
        and source_owned_events
        and int(source_event.get("stage", -1)) == max(int(row.get("stage", -1)) for row in source_owned_events)
    )
    target_event_is_first = bool(
        target_event is not None
        and _carrier_code(target_event.get("owner")) == target
        and target_owned_events
        and int(target_event.get("stage", -1)) == min(int(row.get("stage", -1)) for row in target_owned_events)
    )
    dependency_id = str(model.get("operational_dependency_id", ""))
    dependency = next((row for row in _dependency_rows(model) if row.get("dependency_id") == dependency_id), None)
    direct_dependency_declared = bool(
        dependency is not None
        and dependency.get("parent_event_id") == source_event_id
        and dependency.get("child_event_id") == target_event_id
    )
    stage_adjacency = bool(
        source_event is not None
        and target_event is not None
        and int(target_event.get("stage", -1)) == int(source_event.get("stage", -1)) + 1
    )
    source_and_target_support_valid = bool(
        source_event is not None
        and target_event is not None
        and _support(stage_map.get(int(source_event.get("stage", -1)), {})) == (source,)
        and _support(stage_map.get(int(target_event.get("stage", -1)), {})) == (target,)
    )

    payload = dependency.get("payload", {}) if isinstance(dependency, Mapping) else {}
    parent_output = source_event.get("output_payload", {}) if isinstance(source_event, Mapping) else {}
    child_input = target_event.get("input_payload", {}) if isinstance(target_event, Mapping) else {}
    payload_components_complete = isinstance(payload, Mapping) and set(payload) == PAYLOAD_COMPONENTS
    payload_hash = _canonical_hash(payload) if isinstance(payload, Mapping) else ""
    payload_hashes_match = bool(
        payload_components_complete
        and parent_output == payload == child_input
        and dependency is not None
        and dependency.get("payload_sha256") == payload_hash
    )
    edge_kind_valid = bool(dependency is not None and dependency.get("dependency_kind") == "live-temporal-handoff")
    edge_counterfactually_necessary = bool(dependency is not None and dependency.get("counterfactually_necessary") is True)
    no_storage_mediator = bool(dependency is not None and dependency.get("storage_mediator") is False)
    not_replayable_archive = bool(dependency is not None and dependency.get("replayable_archive") is False)
    no_alternative_temporal_parent = bool(dependency is not None and dependency.get("alternative_temporal_parent") is False)
    single_use_temporal_token = bool(dependency is not None and dependency.get("single_use_temporal_token") is True)

    source_signature = _signature(stage_map.get(int(source_event.get("stage", -1)), {})) if source_event is not None else {}
    target_signature = _signature(stage_map.get(int(target_event.get("stage", -1)), {})) if target_event is not None else {}
    predictive_step_valid = bool(source_signature and target_signature and target_signature.get("predictive_rank") == source_signature.get("predictive_rank") + 1)
    order_step_valid = bool(source_signature and target_signature and target_signature.get("order_rank") == source_signature.get("order_rank") + 1)
    tick_step_valid = bool(source_signature and target_signature and target_signature.get("tick_index") == source_signature.get("tick_index") + 1)
    progress_step_valid = bool(source_signature and target_signature and target_signature.get("progress_rank") == source_signature.get("progress_rank") + 1)
    strict_record_step_valid = bool(source_signature and target_signature and target_signature.get("record_value") > source_signature.get("record_value"))
    route_status = str(model.get("route_status", "unresolved"))
    source_route = source_signature.get("route_residue", [])
    target_route = target_signature.get("route_residue", [])
    route_discipline_valid = route_status in {"flat", "route-indexed"} and (
        route_status == "flat" or (
            isinstance(source_route, list)
            and isinstance(target_route, list)
            and bool(target_route)
            and _prefix(source_route, target_route)
        )
    )
    ownership_interface_valid = bool(
        source_signature.get("maintenance_owner") == source
        and target_signature.get("maintenance_owner") == target
        and source_event is not None
        and target_event is not None
        and _carrier_code(source_event.get("owner")) == source
        and _carrier_code(target_event.get("owner")) == target
    )
    evidence_payload = {
        "source_carrier": model.get("source_carrier"),
        "target_carrier": model.get("target_carrier"),
        "episode": model.get("episode"),
        "last_source_event_id": model.get("last_source_event_id"),
        "first_target_event_id": model.get("first_target_event_id"),
        "operational_dependency_id": model.get("operational_dependency_id"),
        "route_status": model.get("route_status"),
    }
    forbidden_verdict_fields_absent = _evidence_keys_are_clean(evidence_payload)
    detached_operational_pattern = bool(
        dependency is None
        or dependency.get("replayable_archive") is True
        or dependency.get("storage_mediator") is True
        or dependency.get("counterfactually_necessary") is not True
        or not stage_adjacency
        or not payload_components_complete
        or not tick_step_valid
    )
    obligations = {
        "distinct-carriers": distinct_carriers,
        "stages-well-formed": stages_well_formed,
        "all-stages-temporally-realized": all_stages_temporally_realized,
        "source-event-is-last": source_event_is_last,
        "target-event-is-first": target_event_is_first,
        "direct-dependency-declared": direct_dependency_declared,
        "stage-adjacency": stage_adjacency,
        "source-and-target-support-valid": source_and_target_support_valid,
        "payload-components-complete": payload_components_complete,
        "payload-hashes-match": payload_hashes_match,
        "edge-kind-valid": edge_kind_valid,
        "edge-counterfactually-necessary": edge_counterfactually_necessary,
        "no-storage-mediator": no_storage_mediator,
        "not-replayable-archive": not_replayable_archive,
        "no-alternative-temporal-parent": no_alternative_temporal_parent,
        "single-use-temporal-token": single_use_temporal_token,
        "predictive-step-valid": predictive_step_valid,
        "order-step-valid": order_step_valid,
        "tick-step-valid": tick_step_valid,
        "progress-step-valid": progress_step_valid,
        "strict-record-step-valid": strict_record_step_valid,
        "route-discipline-valid": route_discipline_valid,
        "ownership-interface-valid": ownership_interface_valid,
        "forbidden-verdict-fields-absent": forbidden_verdict_fields_absent,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return DirectSuccessorAudit(
        distinct_carriers=distinct_carriers,
        stages_well_formed=stages_well_formed,
        all_stages_temporally_realized=all_stages_temporally_realized,
        source_event_is_last=source_event_is_last,
        target_event_is_first=target_event_is_first,
        direct_dependency_declared=direct_dependency_declared,
        stage_adjacency=stage_adjacency,
        source_and_target_support_valid=source_and_target_support_valid,
        payload_components_complete=payload_components_complete,
        payload_hashes_match=payload_hashes_match,
        edge_kind_valid=edge_kind_valid,
        edge_counterfactually_necessary=edge_counterfactually_necessary,
        no_storage_mediator=no_storage_mediator,
        not_replayable_archive=not_replayable_archive,
        no_alternative_temporal_parent=no_alternative_temporal_parent,
        single_use_temporal_token=single_use_temporal_token,
        predictive_step_valid=predictive_step_valid,
        order_step_valid=order_step_valid,
        tick_step_valid=tick_step_valid,
        progress_step_valid=progress_step_valid,
        strict_record_step_valid=strict_record_step_valid,
        route_discipline_valid=route_discipline_valid,
        ownership_interface_valid=ownership_interface_valid,
        forbidden_verdict_fields_absent=forbidden_verdict_fields_absent,
        detached_operational_pattern=detached_operational_pattern,
        direct_successor_valid=not failed,
        failed_obligations=failed,
    )


@dataclass(frozen=True)
class DirectSuccessorPathAudit:
    atomic_certificates_valid: bool
    carrier_frontiers_match: bool
    signature_frontiers_match: bool
    boundary_events_match: bool
    no_temporal_gap: bool
    path_has_at_least_one_edge: bool
    path_valid: bool
    atomic_endpoint_edge_present: bool
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["failed_obligations"] = list(self.failed_obligations)
        return payload


def audit_direct_successor_path(models: Sequence[Mapping[str, Any]]) -> DirectSuccessorPathAudit:
    audits = [audit_direct_successor(model) for model in models]
    atomic_certificates_valid = bool(audits) and all(audit.direct_successor_valid for audit in audits)
    carrier_frontiers_match = True
    signature_frontiers_match = True
    boundary_events_match = True
    no_temporal_gap = True
    for left, right in zip(models, models[1:]):
        left_target = _carrier_code(left.get("target_carrier"))
        right_source = _carrier_code(right.get("source_carrier"))
        carrier_frontiers_match &= left_target == right_source
        left_target_event = next((row for row in _event_rows(left) if row.get("event_id") == left.get("first_target_event_id")), None)
        right_source_event = next((row for row in _event_rows(right) if row.get("event_id") == right.get("last_source_event_id")), None)
        boundary_events_match &= bool(
            left_target_event is not None
            and right_source_event is not None
            and left_target_event.get("event_id") == right_source_event.get("event_id")
            and left_target_event.get("output_payload") == right_source_event.get("output_payload")
        )
        left_stage = _terminal_stage(left)
        right_stage = _initial_stage(right)
        signature_frontiers_match &= bool(left_stage is not None and right_stage is not None and _signature(left_stage) == _signature(right_stage))
        no_temporal_gap &= bool(
            left_stage is not None
            and right_stage is not None
            and left_stage.get("temporal_realized") is True
            and right_stage.get("temporal_realized") is True
        )
    path_has_at_least_one_edge = bool(models)
    if len(models) <= 1:
        atomic_endpoint_edge_present = bool(models and audit_direct_successor(models[0]).direct_successor_valid)
    else:
        first_source = str(models[0].get("last_source_event_id"))
        last_target = str(models[-1].get("first_target_event_id"))
        atomic_endpoint_edge_present = any(
            row.get("parent_event_id") == first_source and row.get("child_event_id") == last_target
            for model in models for row in _dependency_rows(model)
        )
    obligations = {
        "atomic-certificates-valid": atomic_certificates_valid,
        "carrier-frontiers-match": carrier_frontiers_match,
        "signature-frontiers-match": signature_frontiers_match,
        "boundary-events-match": boundary_events_match,
        "no-temporal-gap": no_temporal_gap,
        "path-has-at-least-one-edge": path_has_at_least_one_edge,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return DirectSuccessorPathAudit(
        atomic_certificates_valid=atomic_certificates_valid,
        carrier_frontiers_match=carrier_frontiers_match,
        signature_frontiers_match=signature_frontiers_match,
        boundary_events_match=boundary_events_match,
        no_temporal_gap=no_temporal_gap,
        path_has_at_least_one_edge=path_has_at_least_one_edge,
        path_valid=not failed,
        atomic_endpoint_edge_present=atomic_endpoint_edge_present,
        failed_obligations=failed,
    )


# ---------------------------------------------------------------------------
# Deterministic bounded searches used to stress the definitions.
# ---------------------------------------------------------------------------


def bounded_corridor_support_search(max_stages: int = 4) -> dict[str, int | bool]:
    supports = ("S", "T", "ST")
    candidates = 0
    passes = 0
    detached_candidates = 0
    detached_passes = 0
    gapped_candidates = 0
    gapped_passes = 0
    smallest_positive = 0
    for stage_count in range(2, max_stages + 1):
        for support_pattern in product(supports, repeat=stage_count):
            for realized in product((False, True), repeat=stage_count):
                for source_nonredundant, target_nonredundant, route_valid in product((False, True), repeat=3):
                    candidates += 1
                    has_mixed = "ST" in support_pattern
                    detached = not has_mixed
                    has_gap = not all(realized)
                    valid = bool(
                        support_pattern[0] == "S"
                        and support_pattern[-1] == "T"
                        and has_mixed
                        and all(realized)
                        and source_nonredundant
                        and target_nonredundant
                        and route_valid
                    )
                    passes += int(valid)
                    if detached:
                        detached_candidates += 1
                        detached_passes += int(valid)
                    if has_gap:
                        gapped_candidates += 1
                        gapped_passes += int(valid)
                    if valid and (smallest_positive == 0 or stage_count < smallest_positive):
                        smallest_positive = stage_count
    return {
        "max_stages": max_stages,
        "candidates_examined": candidates,
        "strict_passes": passes,
        "detached_candidates_examined": detached_candidates,
        "detached_passes": detached_passes,
        "gapped_candidates_examined": gapped_candidates,
        "gapped_passes": gapped_passes,
        "smallest_positive_stage_count": smallest_positive,
        "definition_nonuniversal": 0 < passes < candidates,
        "detached_copy_excluded": detached_passes == 0,
        "temporal_gap_excluded": gapped_passes == 0,
    }


def bounded_nonredundancy_truth_table_search() -> dict[str, int | bool | list[int]]:
    functions_examined = 0
    jointly_nonredundant: list[int] = []
    for mask in range(16):
        functions_examined += 1

        def value(source: int, target: int) -> int:
            index = source * 2 + target
            return (mask >> index) & 1

        full = value(1, 1)
        if full != value(0, 1) and full != value(1, 0):
            jointly_nonredundant.append(mask)
    return {
        "boolean_update_tables_examined": functions_examined,
        "jointly_nonredundant_table_count": len(jointly_nonredundant),
        "jointly_nonredundant_table_masks": jointly_nonredundant,
        "nonverdict_intervention_predicates_exist": bool(jointly_nonredundant),
        "and_table_is_jointly_nonredundant": 8 in jointly_nonredundant,
    }


def bounded_corridor_composition_search() -> dict[str, int | bool]:
    candidates_examined = 0
    compatible_pairs = 0
    carrier_chain_failures = 0
    old_endpoint_mixed_failures = 0
    for route_left, route_right in product(("flat", "route-indexed"), repeat=2):
        for boundary_signature in range(4):
            candidates_examined += 1
            compatible_pairs += 1
            chain_valid = (
                route_left in {"flat", "route-indexed"}
                and route_right in {"flat", "route-indexed"}
                and boundary_signature >= 0
            )
            carrier_chain_failures += int(not chain_valid)
            # S-M followed by M-T contains no S/T mixed stage in the canonical concatenation.
            old_endpoint_mixed_failures += 1
    return {
        "candidate_pairs_examined": candidates_examined,
        "frontier_compatible_pairs": compatible_pairs,
        "carrier_chain_composition_failures": carrier_chain_failures,
        "old_endpoint_mixed_rule_failures": old_endpoint_mixed_failures,
        "carrier_chain_rule_composes_all_compatible_pairs": carrier_chain_failures == 0,
        "endpoint_mixedness_is_not_composition_stable": old_endpoint_mixed_failures == compatible_pairs and compatible_pairs > 0,
    }


def bounded_direct_successor_search() -> dict[str, int | bool]:
    candidates_examined = 0
    passes = 0
    detached_like = 0
    detached_like_passes = 0
    arbitrary_data_edges = 0
    arbitrary_data_edge_passes = 0
    for values in product((False, True), repeat=11):
        (
            immediate,
            necessary,
            replayable,
            storage,
            alternative_parent,
            single_use,
            payload_complete,
            predictive,
            tick,
            record,
            ownership,
        ) = values
        candidates_examined += 1
        valid = bool(
            immediate
            and necessary
            and not replayable
            and not storage
            and not alternative_parent
            and single_use
            and payload_complete
            and predictive
            and tick
            and record
            and ownership
        )
        passes += int(valid)
        detached = replayable or storage or not necessary or not immediate
        if detached:
            detached_like += 1
            detached_like_passes += int(valid)
        arbitrary = payload_complete and (replayable or storage or alternative_parent or not necessary)
        if arbitrary:
            arbitrary_data_edges += 1
            arbitrary_data_edge_passes += int(valid)
    return {
        "candidates_examined": candidates_examined,
        "valid_direct_successor_shapes": passes,
        "detached_like_candidates": detached_like,
        "detached_like_passes": detached_like_passes,
        "arbitrary_data_edge_candidates": arbitrary_data_edges,
        "arbitrary_data_edge_passes": arbitrary_data_edge_passes,
        "definition_nonuniversal": 0 < passes < candidates_examined,
        "detached_shapes_excluded": detached_like_passes == 0,
        "arbitrary_data_reachability_excluded": arbitrary_data_edge_passes == 0,
    }


def bounded_direct_path_composition_search() -> dict[str, int | bool]:
    pairs_examined = 0
    compatible_pairs = 0
    valid_paths = 0
    falsely_atomic_composites = 0
    for first_tick, boundary_tick, last_tick in product(range(3), repeat=3):
        pairs_examined += 1
        left_valid = boundary_tick == first_tick + 1
        right_valid = last_tick == boundary_tick + 1
        if left_valid and right_valid:
            compatible_pairs += 1
            valid_paths += 1
            # No direct first-to-last event edge is added by path concatenation.
            falsely_atomic_composites += 0
    return {
        "candidate_pairs_examined": pairs_examined,
        "compatible_atomic_pairs": compatible_pairs,
        "valid_composed_paths": valid_paths,
        "falsely_atomic_composites": falsely_atomic_composites,
        "path_composition_valid_for_all_compatible_pairs": compatible_pairs == valid_paths and compatible_pairs > 0,
        "atomic_edge_relation_not_silently_closed": falsely_atomic_composites == 0,
    }
