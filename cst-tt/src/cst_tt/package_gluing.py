from __future__ import annotations

from dataclasses import asdict, dataclass
import json
from itertools import product
from typing import Any, Iterable, Mapping, Sequence

from .types import ClauseId

CLAUSE_ORDER: tuple[str, ...] = tuple(clause.value for clause in ClauseId)
C6 = ClauseId.C6_TEMPORAL_CLOSURE.value

FORBIDDEN_INTEGRATED_KEYS = frozenset(
    {
        "source",
        "ancestry",
        "lineage",
        "corridor",
        "fiach",
        "survival",
        "identity",
        "autonomy",
        "withdrawal",
        "consciousness",
        "phenomenal",
    }
)


@dataclass(frozen=True)
class ClauseAudit:
    clause: str
    scope_exact: bool
    accepted: bool
    hard_gate_passed: bool
    errors: tuple[str, ...]


@dataclass(frozen=True)
class JoinTreeAudit:
    root_declared: bool
    all_nodes_covered: bool
    exactly_one_parent_per_nonroot: bool
    connected: bool
    acyclic: bool
    edge_count_correct: bool
    running_intersection: bool
    edge_compatible: bool
    all_overlap_compatible: bool
    errors: tuple[str, ...]

    @property
    def valid_shape(self) -> bool:
        return all(
            (
                self.root_declared,
                self.all_nodes_covered,
                self.exactly_one_parent_per_nonroot,
                self.connected,
                self.acyclic,
                self.edge_count_correct,
            )
        )


@dataclass(frozen=True)
class TemporalSubstanceAudit:
    future_sufficient: bool
    order_stable: bool
    successor_available: bool
    viable_tick: bool
    genuine_progress: bool
    endogenous_arrow: bool
    record_descends: bool
    route_residue_retained: bool
    no_external_scheduler: bool
    temporal_owner_matches: bool
    maintenance_owner_matches: bool
    errors: tuple[str, ...]

    @property
    def valid(self) -> bool:
        return all(
            (
                self.future_sufficient,
                self.order_stable,
                self.successor_available,
                self.viable_tick,
                self.genuine_progress,
                self.endogenous_arrow,
                self.record_descends,
                self.route_residue_retained,
                self.no_external_scheduler,
                self.temporal_owner_matches,
                self.maintenance_owner_matches,
            )
        )


@dataclass(frozen=True)
class PackageAudit:
    model_id: str
    exact_clause_coverage: bool
    unique_clause_slots: bool
    every_scope_exact: bool
    every_clause_accepted: bool
    every_hard_gate_passed: bool
    join_tree: JoinTreeAudit
    global_constructible: bool
    supplied_global_matches: bool
    global_restricts_to_every_local: bool
    temporal_substance: TemporalSubstanceAudit
    target_owned: bool
    forbidden_field_free: bool
    integrated_package_valid: bool
    derived_global_assignment: Mapping[str, Any]
    failed_obligations: tuple[str, ...]
    errors: tuple[str, ...]
    clause_audits: tuple[ClauseAudit, ...]

    def to_dict(self) -> dict[str, Any]:
        result = asdict(self)
        result["join_tree"]["valid_shape"] = self.join_tree.valid_shape
        result["temporal_substance"]["valid"] = self.temporal_substance.valid
        return json.loads(json.dumps(result, sort_keys=True))


@dataclass(frozen=True)
class StagedAssemblyAudit:
    assembly_id: str
    source_package_valid: bool
    target_package_valid: bool
    carriers_distinct: bool
    exactly_eight_clause_maps: bool
    maps_separately_typed: bool
    coordinate_maps_total: bool
    value_maps_sound: bool
    hard_gates_never_averaged: bool
    target_global_assembled: bool
    forbidden_verdict_fields_absent: bool
    staged_assembly_valid: bool
    failed_obligations: tuple[str, ...]
    errors: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        return json.loads(json.dumps(asdict(self), sort_keys=True))


def _is_nonempty_string(value: Any) -> bool:
    return isinstance(value, str) and bool(value.strip())


def _is_int(value: Any) -> bool:
    return isinstance(value, int) and not isinstance(value, bool)


def _clause_rule(clause: str, assignment: Mapping[str, Any], target_code: int) -> tuple[bool, bool, list[str]]:
    errors: list[str] = []

    def req(condition: bool, message: str) -> bool:
        if not condition:
            errors.append(message)
        return condition

    if clause == ClauseId.C1_OBJECTHOOD.value:
        accepted = all(
            (
                req(_is_nonempty_string(assignment.get("object_token")), "C1 object token is absent"),
                req(assignment.get("boundary_closed") is True, "C1 boundary is not closed"),
                req(_is_nonempty_string(assignment.get("cross_predictive_tag")), "C1 predictive tag is absent"),
            )
        )
        gate = req(assignment.get("c1_audit_sealed") is True, "C1 audit seal fails")
    elif clause == ClauseId.C2_STRICT_PROMOTION.value:
        before = assignment.get("promotion_rank_before")
        after = assignment.get("promotion_rank_after")
        accepted = all(
            (
                req(_is_int(before), "C2 prior rank is not an integer"),
                req(_is_int(after), "C2 promoted rank is not an integer"),
                req(_is_int(before) and _is_int(after) and after > before, "C2 promotion is not strict"),
                req(_is_int(assignment.get("episode_epoch")) and assignment["episode_epoch"] >= 0, "C2 epoch is invalid"),
            )
        )
        gate = all(
            (
                req(assignment.get("strict_test_pass") is True, "C2 strict test fails"),
                req(assignment.get("promotion_audit_sealed") is True, "C2 audit seal fails"),
            )
        )
    elif clause == ClauseId.C3_REFLEXIVE_SELF_COORDINATE.value:
        accepted = all(
            (
                req(_is_nonempty_string(assignment.get("self_coordinate")), "C3 self-coordinate is absent"),
                req(assignment.get("self_model_reflexive") is True, "C3 reflexive self-model fails"),
                req(_is_nonempty_string(assignment.get("cross_predictive_tag")), "C3 predictive tag is absent"),
            )
        )
        gate = req(assignment.get("self_audit_sealed") is True, "C3 audit seal fails")
    elif clause == ClauseId.C4_INTERFACE_NONEXPOSURE.value:
        accepted = all(
            (
                req(_is_nonempty_string(assignment.get("public_shadow")), "C4 public interface is absent"),
                req(assignment.get("hidden_state_nonexposed") is True, "C4 hidden state is exposed"),
            )
        )
        gate = req(assignment.get("interface_leak") is False, "C4 interface leak gate fails")
    elif clause == ClauseId.C5_ACTION_CREDIT.value:
        accepted = all(
            (
                req(_is_nonempty_string(assignment.get("action_token")), "C5 action token is absent"),
                req(assignment.get("action_credit_owner") == target_code, "C5 action credit is not target-local"),
                req(assignment.get("credit_source_internal") is True, "C5 credit source is external"),
            )
        )
        gate = all(
            (
                req(assignment.get("credit_audit_sealed") is True, "C5 audit seal fails"),
                req(assignment.get("control_owner") == target_code, "C5 control owner mismatch"),
            )
        )
    elif clause == ClauseId.C6_TEMPORAL_CLOSURE.value:
        accepted = all(
            (
                req(assignment.get("future_sufficient") is True, "C6 predictive now is not future-sufficient"),
                req(assignment.get("order_stable") is True, "C6 order is unstable"),
                req(assignment.get("successor_total_on_viable") is True, "C6 viable successor is unavailable"),
                req(assignment.get("tick_viable") is True, "C6 tick is not viable"),
            )
        )
        before = assignment.get("record_before")
        after = assignment.get("record_after")
        gate = all(
            (
                req(_is_int(assignment.get("tick_progress")) and assignment["tick_progress"] > 0, "C6 tick does not progress"),
                req(assignment.get("arrow_endogenous") is True, "C6 arrow is not endogenous"),
                req(_is_int(before) and _is_int(after) and after > before, "C6 record does not strictly descend in the declared arrow order"),
                req(isinstance(assignment.get("route_residue"), list) and len(assignment["route_residue"]) > 0, "C6 route residue is absent"),
                req(assignment.get("external_scheduler") is False, "C6 depends on an external scheduler"),
                req(assignment.get("temporal_owner") == target_code, "C6 temporal owner mismatch"),
                req(assignment.get("maintenance_owner") == target_code, "C6 maintenance owner mismatch"),
                req(assignment.get("control_owner") == target_code, "C6 control owner mismatch"),
            )
        )
    elif clause == ClauseId.C7_BINDING_RECOMBINATION.value:
        left = assignment.get("left_branch")
        right = assignment.get("right_branch")
        pairs = assignment.get("recombination_pairs")
        accepted = all(
            (
                req(assignment.get("binding_integrated") is True, "C7 binding is not integrated"),
                req(_is_nonempty_string(left) and _is_nonempty_string(right) and left != right, "C7 branches are not distinctly bound"),
                req(isinstance(pairs, list) and len(pairs) >= 2, "C7 recombination table is too small"),
            )
        )
        gate = all(
            (
                req(assignment.get("recombination_relation_preserved") is True, "C7 joint recombination relation fails"),
                req(_is_nonempty_string(assignment.get("joint_relation_tag")), "C7 joint relation tag is absent"),
            )
        )
    elif clause == ClauseId.C8_VIABILITY_REPAIR.value:
        accepted = all(
            (
                req(assignment.get("viable") is True, "C8 viability fails"),
                req(assignment.get("repair_enabled") is True, "C8 repair is disabled"),
            )
        )
        gate = all(
            (
                req(_is_int(assignment.get("repair_budget")) and assignment["repair_budget"] > 0, "C8 repair budget is insolvent"),
                req(assignment.get("repair_owner") == target_code, "C8 repair owner mismatch"),
                req(assignment.get("control_owner") == target_code, "C8 control owner mismatch"),
            )
        )
    else:
        accepted = False
        gate = False
        errors.append(f"unknown clause {clause}")
    return accepted, gate, errors


def _walk_keys(value: Any, path: tuple[str, ...] = ()) -> Iterable[tuple[tuple[str, ...], str]]:
    if isinstance(value, Mapping):
        for key, child in value.items():
            key_text = str(key)
            yield path, key_text
            yield from _walk_keys(child, (*path, key_text))
    elif isinstance(value, list):
        for index, child in enumerate(value):
            yield from _walk_keys(child, (*path, str(index)))


def _forbidden_key_hits(model: Mapping[str, Any], *, allow_source: bool = False) -> list[str]:
    forbidden = set(FORBIDDEN_INTEGRATED_KEYS)
    if allow_source:
        forbidden.remove("source")
    hits: list[str] = []
    explicit = {
        "source", "source_carrier", "source_state", "source_package",
        "ancestry", "ancestry_verdict", "lineage", "lineage_verdict",
        "corridor", "temporal_corridor", "fiach", "fiach_verdict",
        "survival", "survival_verdict", "identity", "identity_verdict",
        "autonomy", "autonomy_verdict", "withdrawal",
        "consciousness", "consciousness_verdict", "phenomenal", "phenomenal_verdict",
    }
    if allow_source:
        explicit.difference_update({"source", "source_carrier", "source_state", "source_package"})
    for path, key in _walk_keys(model):
        normalized = key.lower().replace("-", "_")
        if normalized in explicit:
            hits.append("/".join((*path, key)))
    return sorted(set(hits))


def _tree_audit(
    clauses: Mapping[str, Mapping[str, Any]],
    root: Any,
    edges_raw: Any,
) -> tuple[JoinTreeAudit, dict[str, str | None], dict[str, set[str]]]:
    errors: list[str] = []
    nodes = set(clauses)
    root_declared = isinstance(root, str) and root in nodes
    if not root_declared:
        errors.append("join-tree root is not a declared clause")
    parent: dict[str, str | None] = {node: None for node in nodes}
    seen_children: set[str] = set()
    edge_pairs: list[tuple[str, str]] = []
    if not isinstance(edges_raw, list):
        edges_raw = []
        errors.append("join-tree edges are not a list")
    for item in edges_raw:
        if not isinstance(item, Mapping):
            errors.append("join-tree edge is not an object")
            continue
        child = item.get("child")
        par = item.get("parent")
        if not isinstance(child, str) or not isinstance(par, str) or child not in nodes or par not in nodes:
            errors.append("join-tree edge names an undeclared clause")
            continue
        if child == par:
            errors.append(f"join-tree self edge at {child}")
            continue
        edge_pairs.append((child, par))
        if child in seen_children:
            errors.append(f"join-tree child {child} has multiple parents")
        else:
            parent[child] = par
            seen_children.add(child)
    exactly_one_parent = bool(root_declared)
    if root_declared:
        if root in seen_children:
            exactly_one_parent = False
            errors.append("join-tree root has a parent")
        for node in sorted(nodes - {root}):
            if node not in seen_children:
                exactly_one_parent = False
                errors.append(f"join-tree nonroot {node} has no parent")
    else:
        exactly_one_parent = False

    edge_count_correct = len(edge_pairs) == max(0, len(nodes) - 1)
    if not edge_count_correct:
        errors.append("join-tree does not have exactly n-1 edges")

    acyclic = True
    connected = root_declared
    if root_declared:
        for node in nodes:
            cursor = node
            visited: set[str] = set()
            while cursor != root:
                if cursor in visited:
                    acyclic = False
                    connected = False
                    errors.append(f"join-tree cycle reaches {cursor}")
                    break
                visited.add(cursor)
                nxt = parent.get(cursor)
                if nxt is None:
                    connected = False
                    errors.append(f"join-tree node {node} does not reach root")
                    break
                cursor = nxt
    else:
        acyclic = False
        connected = False

    adjacency: dict[str, set[str]] = {node: set() for node in nodes}
    for child, par in edge_pairs:
        adjacency[child].add(par)
        adjacency[par].add(child)

    all_coords = sorted({coord for clause in clauses.values() for coord in clause.get("scope", []) if isinstance(coord, str)})
    running_intersection = True
    for coord in all_coords:
        holders = {node for node, clause in clauses.items() if coord in clause.get("scope", [])}
        if len(holders) <= 1:
            continue
        start = min(holders)
        reached = {start}
        frontier = [start]
        while frontier:
            current = frontier.pop()
            for neighbor in adjacency[current]:
                if neighbor in holders and neighbor not in reached:
                    reached.add(neighbor)
                    frontier.append(neighbor)
        if reached != holders:
            running_intersection = False
            errors.append(f"running intersection fails for coordinate {coord}")

    edge_compatible = True
    for child, par in edge_pairs:
        child_scope = set(clauses[child].get("scope", []))
        parent_scope = set(clauses[par].get("scope", []))
        child_assignment = clauses[child].get("assignment", {})
        parent_assignment = clauses[par].get("assignment", {})
        for coord in sorted(child_scope & parent_scope):
            if child_assignment.get(coord) != parent_assignment.get(coord):
                edge_compatible = False
                errors.append(f"edge overlap conflict at {child}/{par}/{coord}")

    all_overlap_compatible = True
    coordinate_values: dict[str, list[Any]] = {}
    for clause in clauses.values():
        assignment = clause.get("assignment", {})
        for coord in clause.get("scope", []):
            if coord in assignment:
                coordinate_values.setdefault(coord, []).append(assignment[coord])
    for coord, values in coordinate_values.items():
        if values and any(value != values[0] for value in values[1:]):
            all_overlap_compatible = False
            errors.append(f"global overlap conflict at {coord}")

    audit = JoinTreeAudit(
        root_declared=root_declared,
        all_nodes_covered=set(parent) == nodes,
        exactly_one_parent_per_nonroot=exactly_one_parent,
        connected=connected,
        acyclic=acyclic,
        edge_count_correct=edge_count_correct,
        running_intersection=running_intersection,
        edge_compatible=edge_compatible,
        all_overlap_compatible=all_overlap_compatible,
        errors=tuple(sorted(set(errors))),
    )
    return audit, parent, adjacency


def _temporal_audit(assignment: Mapping[str, Any], target_code: int) -> TemporalSubstanceAudit:
    checks = {
        "future_sufficient": assignment.get("future_sufficient") is True,
        "order_stable": assignment.get("order_stable") is True,
        "successor_available": assignment.get("successor_total_on_viable") is True,
        "viable_tick": assignment.get("tick_viable") is True,
        "genuine_progress": _is_int(assignment.get("tick_progress")) and assignment["tick_progress"] > 0,
        "endogenous_arrow": assignment.get("arrow_endogenous") is True,
        "record_descends": _is_int(assignment.get("record_before"))
        and _is_int(assignment.get("record_after"))
        and assignment["record_after"] > assignment["record_before"],
        "route_residue_retained": isinstance(assignment.get("route_residue"), list)
        and len(assignment["route_residue"]) > 0,
        "no_external_scheduler": assignment.get("external_scheduler") is False,
        "temporal_owner_matches": assignment.get("temporal_owner") == target_code,
        "maintenance_owner_matches": assignment.get("maintenance_owner") == target_code,
    }
    errors = tuple(name for name, status in checks.items() if not status)
    return TemporalSubstanceAudit(**checks, errors=errors)


def audit_package(model: Mapping[str, Any]) -> PackageAudit:
    errors: list[str] = []
    model_id = str(model.get("model_id", ""))
    target = model.get("target", {})
    target_code = target.get("code") if isinstance(target, Mapping) else None
    if not _is_int(target_code) or target_code < 0:
        target_code = -1
        errors.append("target carrier code is invalid")

    clause_items = model.get("clauses", [])
    if not isinstance(clause_items, list):
        clause_items = []
        errors.append("clauses must be a list")
    clause_names = [item.get("clause") for item in clause_items if isinstance(item, Mapping)]
    unique_clause_slots = len(clause_names) == len(set(clause_names))
    exact_clause_coverage = set(clause_names) == set(CLAUSE_ORDER) and len(clause_names) == len(CLAUSE_ORDER)
    if not unique_clause_slots:
        errors.append("clause slots are duplicated")
    if not exact_clause_coverage:
        errors.append("certificate does not contain exactly C1-C8")

    clauses: dict[str, Mapping[str, Any]] = {}
    clause_audits: list[ClauseAudit] = []
    for item in clause_items:
        if not isinstance(item, Mapping):
            continue
        clause = str(item.get("clause", ""))
        scope = item.get("scope", [])
        assignment = item.get("assignment", {})
        scope_valid = (
            isinstance(scope, list)
            and len(scope) > 0
            and all(_is_nonempty_string(coord) for coord in scope)
            and len(scope) == len(set(scope))
            and isinstance(assignment, Mapping)
            and set(assignment) == set(scope)
        )
        local_errors: list[str] = []
        if not scope_valid:
            local_errors.append("scope is empty, duplicated, or does not exactly match assignment keys")
        accepted, gate, rule_errors = _clause_rule(clause, assignment if isinstance(assignment, Mapping) else {}, target_code)
        local_errors.extend(rule_errors)
        clause_audits.append(
            ClauseAudit(
                clause=clause,
                scope_exact=scope_valid,
                accepted=accepted,
                hard_gate_passed=gate,
                errors=tuple(local_errors),
            )
        )
        if clause not in clauses:
            clauses[clause] = item

    every_scope_exact = len(clause_audits) == 8 and all(row.scope_exact for row in clause_audits)
    every_clause_accepted = len(clause_audits) == 8 and all(row.accepted for row in clause_audits)
    every_hard_gate_passed = len(clause_audits) == 8 and all(row.hard_gate_passed for row in clause_audits)

    join = model.get("join_tree", {})
    if not isinstance(join, Mapping):
        join = {}
    tree_audit, _parent, _adjacency = _tree_audit(clauses, join.get("root"), join.get("edges"))

    derived: dict[str, Any] = {}
    conflicts = False
    for clause in CLAUSE_ORDER:
        item = clauses.get(clause)
        if item is None:
            continue
        assignment = item.get("assignment", {})
        if not isinstance(assignment, Mapping):
            continue
        for coord in item.get("scope", []):
            value = assignment.get(coord)
            if coord in derived and derived[coord] != value:
                conflicts = True
            else:
                derived.setdefault(coord, value)
    global_constructible = exact_clause_coverage and every_scope_exact and not conflicts and tree_audit.all_overlap_compatible
    supplied = model.get("declared_global_assignment")
    supplied_global_matches = isinstance(supplied, Mapping) and dict(supplied) == derived
    if not supplied_global_matches:
        errors.append("declared global assignment does not equal the canonical glued assignment")
    global_restricts = global_constructible
    if global_constructible:
        for item in clauses.values():
            assignment = item.get("assignment", {})
            if any(derived.get(coord) != assignment.get(coord) for coord in item.get("scope", [])):
                global_restricts = False
                break

    c6_assignment = clauses.get(C6, {}).get("assignment", {}) if C6 in clauses else {}
    temporal = _temporal_audit(c6_assignment if isinstance(c6_assignment, Mapping) else {}, target_code)

    owner_values = []
    for item in clauses.values():
        assignment = item.get("assignment", {})
        if isinstance(assignment, Mapping) and "package_owner" in assignment:
            owner_values.append(assignment["package_owner"])
    target_owned = bool(owner_values) and all(value == target_code for value in owner_values)
    target_owned = target_owned and c6_assignment.get("temporal_owner") == target_code and c6_assignment.get("maintenance_owner") == target_code

    forbidden_hits = _forbidden_key_hits(model)
    forbidden_field_free = not forbidden_hits
    if forbidden_hits:
        errors.extend(f"forbidden integrated-package key: {hit}" for hit in forbidden_hits)

    failed: list[str] = []
    obligations = {
        "PKG-O01-exact-C1-C8-coverage": exact_clause_coverage and unique_clause_slots,
        "PKG-O02-local-scope-and-clause-acceptance": every_scope_exact and every_clause_accepted,
        "PKG-O03-nonnegotiable-hard-gates": every_hard_gate_passed,
        "PKG-O04-rooted-join-tree-shape": tree_audit.valid_shape,
        "PKG-O05-running-intersection": tree_audit.running_intersection,
        "PKG-O06-edge-overlap-compatibility": tree_audit.edge_compatible,
        "PKG-O07-global-gluing-and-restriction": global_constructible and supplied_global_matches and global_restricts,
        "PKG-O08-substantive-C6-temporal-closure": temporal.valid,
        "PKG-O09-target-local-package-ownership": target_owned,
        "PKG-O10-verdict-field-separation": forbidden_field_free,
    }
    failed.extend(name for name, value in obligations.items() if not value)
    integrated = all(obligations.values())
    errors.extend(error for row in clause_audits for error in row.errors)
    errors.extend(tree_audit.errors)
    errors.extend(f"temporal: {error}" for error in temporal.errors)
    return PackageAudit(
        model_id=model_id,
        exact_clause_coverage=exact_clause_coverage,
        unique_clause_slots=unique_clause_slots,
        every_scope_exact=every_scope_exact,
        every_clause_accepted=every_clause_accepted,
        every_hard_gate_passed=every_hard_gate_passed,
        join_tree=tree_audit,
        global_constructible=global_constructible,
        supplied_global_matches=supplied_global_matches,
        global_restricts_to_every_local=global_restricts,
        temporal_substance=temporal,
        target_owned=target_owned,
        forbidden_field_free=forbidden_field_free,
        integrated_package_valid=integrated,
        derived_global_assignment=dict(sorted(derived.items())),
        failed_obligations=tuple(failed),
        errors=tuple(sorted(set(errors))),
        clause_audits=tuple(clause_audits),
    )


def _clause_map_by_id(model: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    result: dict[str, Mapping[str, Any]] = {}
    for item in model.get("clauses", []):
        if isinstance(item, Mapping) and isinstance(item.get("clause"), str):
            result[item["clause"]] = item
    return result


def audit_staged_assembly(
    assembly: Mapping[str, Any],
    source_model: Mapping[str, Any],
    target_model: Mapping[str, Any],
) -> StagedAssemblyAudit:
    errors: list[str] = []
    source_audit = audit_package(source_model)
    target_audit = audit_package(target_model)
    source_code = source_model.get("target", {}).get("code")
    target_code = target_model.get("target", {}).get("code")
    carriers_distinct = _is_int(source_code) and _is_int(target_code) and source_code != target_code
    maps = assembly.get("clause_maps", [])
    if not isinstance(maps, list):
        maps = []
    map_ids = [item.get("clause") for item in maps if isinstance(item, Mapping)]
    exactly_eight = len(maps) == 8 and set(map_ids) == set(CLAUSE_ORDER) and len(set(map_ids)) == 8
    separately_typed = assembly.get("separately_typed_carrier_vocabularies") is True
    source_clauses = _clause_map_by_id(source_model)
    target_clauses = _clause_map_by_id(target_model)
    coordinate_total = exactly_eight
    value_sound = exactly_eight
    gates_never_averaged = assembly.get("hard_gates_never_averaged") is True
    for item in maps:
        if not isinstance(item, Mapping):
            coordinate_total = False
            value_sound = False
            continue
        clause = item.get("clause")
        entries = item.get("entries", [])
        if clause not in source_clauses or clause not in target_clauses or not isinstance(entries, list):
            coordinate_total = False
            value_sound = False
            continue
        src_scope = set(source_clauses[clause].get("scope", []))
        tgt_scope = set(target_clauses[clause].get("scope", []))
        src_assignment = source_clauses[clause].get("assignment", {})
        tgt_assignment = target_clauses[clause].get("assignment", {})
        mapped_src: set[str] = set()
        mapped_tgt: set[str] = set()
        for entry in entries:
            if not isinstance(entry, Mapping):
                value_sound = False
                continue
            src_coord = entry.get("source_coordinate")
            tgt_coord = entry.get("target_coordinate")
            if src_coord not in src_scope or tgt_coord not in tgt_scope:
                coordinate_total = False
                continue
            mapped_src.add(src_coord)
            mapped_tgt.add(tgt_coord)
            if entry.get("source_value") != src_assignment.get(src_coord):
                value_sound = False
            if entry.get("target_value") != tgt_assignment.get(tgt_coord):
                value_sound = False
            if entry.get("translation_attested") is not True:
                value_sound = False
        if mapped_src != src_scope or mapped_tgt != tgt_scope:
            coordinate_total = False
    forbidden_hits = _forbidden_key_hits(assembly, allow_source=True)
    forbidden = not forbidden_hits
    errors.extend(f"forbidden staged-assembly verdict key: {hit}" for hit in forbidden_hits)
    obligations = {
        "STG-O01-source-package-valid": source_audit.integrated_package_valid,
        "STG-O02-target-package-valid": target_audit.integrated_package_valid,
        "STG-O03-distinct-carrier-types": carriers_distinct,
        "STG-O04-exactly-eight-clause-maps": exactly_eight,
        "STG-O05-separately-typed-vocabularies": separately_typed,
        "STG-O06-total-coordinate-maps": coordinate_total,
        "STG-O07-value-translation-soundness": value_sound,
        "STG-O08-hard-gates-not-averaged": gates_never_averaged,
        "STG-O09-target-global-assembly": target_audit.global_constructible and target_audit.global_restricts_to_every_local,
        "STG-O10-no-lineage-or-autonomy-verdict-fields": forbidden,
    }
    failed = tuple(name for name, value in obligations.items() if not value)
    valid = all(obligations.values())
    return StagedAssemblyAudit(
        assembly_id=str(assembly.get("assembly_id", "")),
        source_package_valid=source_audit.integrated_package_valid,
        target_package_valid=target_audit.integrated_package_valid,
        carriers_distinct=carriers_distinct,
        exactly_eight_clause_maps=exactly_eight,
        maps_separately_typed=separately_typed,
        coordinate_maps_total=coordinate_total,
        value_maps_sound=value_sound,
        hard_gates_never_averaged=gates_never_averaged,
        target_global_assembled=target_audit.global_constructible and target_audit.global_restricts_to_every_local,
        forbidden_verdict_fields_absent=forbidden,
        staged_assembly_valid=valid,
        failed_obligations=failed,
        errors=tuple(sorted(set(errors))),
    )


def _is_connected_subset(mask: int, n: int, parent: Sequence[int | None]) -> bool:
    nodes = [i for i in range(n) if mask & (1 << i)]
    if not nodes:
        return False
    adjacency = {i: set() for i in range(n)}
    for child, par in enumerate(parent):
        if par is not None:
            adjacency[child].add(par)
            adjacency[par].add(child)
    reached = {nodes[0]}
    frontier = [nodes[0]]
    while frontier:
        current = frontier.pop()
        for neighbor in adjacency[current]:
            if neighbor in nodes and neighbor not in reached:
                reached.add(neighbor)
                frontier.append(neighbor)
    return reached == set(nodes)


def bounded_gluing_exhaustion() -> dict[str, Any]:
    """Exhaustively check the constructive gluing algorithm on small binary families.

    This is corroborating finite evidence.  The generic mathematical proof lives in
    `CSTTT/Package/FiniteGluing.lean`; enumeration is not represented as that proof.
    """

    configurations: list[tuple[str, tuple[int | None, ...], int]] = [
        ("path-2", (None, 0), 2),
        ("path-3", (None, 0, 1), 2),
        ("star-3", (None, 0, 0), 2),
        ("path-4", (None, 0, 1, 2), 3),
        ("star-4", (None, 0, 0, 0), 3),
    ]
    candidates = 0
    premise_cases = 0
    glued_cases = 0
    violations: list[dict[str, Any]] = []
    per_configuration: list[dict[str, Any]] = []
    for name, parent, coord_count in configurations:
        n = len(parent)
        local_candidates = 0
        local_premises = 0
        local_glued = 0
        subsets = range(1, 1 << n)
        edges = [(child, par) for child, par in enumerate(parent) if par is not None]
        for scope_masks in product(subsets, repeat=coord_count):
            occurrences = [
                (node, coord)
                for coord, mask in enumerate(scope_masks)
                for node in range(n)
                if mask & (1 << node)
            ]
            running = all(_is_connected_subset(mask, n, parent) for mask in scope_masks)
            for value_bits in range(1 << len(occurrences)):
                candidates += 1
                local_candidates += 1
                values = {
                    occurrence: (value_bits >> index) & 1
                    for index, occurrence in enumerate(occurrences)
                }
                edge_compatible = True
                for child, par in edges:
                    for coord, mask in enumerate(scope_masks):
                        if mask & (1 << child) and mask & (1 << par):
                            if values[(child, coord)] != values[(par, coord)]:
                                edge_compatible = False
                                break
                    if not edge_compatible:
                        break
                if not (running and edge_compatible):
                    continue
                premise_cases += 1
                local_premises += 1
                global_assignment: dict[int, int] = {}
                for coord, mask in enumerate(scope_masks):
                    chosen = min(node for node in range(n) if mask & (1 << node))
                    global_assignment[coord] = values[(chosen, coord)]
                agrees = all(global_assignment[coord] == values[(node, coord)] for node, coord in occurrences)
                if agrees:
                    glued_cases += 1
                    local_glued += 1
                else:
                    violations.append(
                        {
                            "configuration": name,
                            "scope_masks": scope_masks,
                            "values": sorted((node, coord, value) for (node, coord), value in values.items()),
                        }
                    )
        per_configuration.append(
            {
                "configuration": name,
                "nodes": n,
                "coordinates": coord_count,
                "candidates": local_candidates,
                "premise_cases": local_premises,
                "glued_cases": local_glued,
            }
        )
    return {
        "schema_version": "1.0",
        "algorithm": "deterministic-exhaustive-binary-running-intersection-check",
        "configurations": per_configuration,
        "candidates_examined": candidates,
        "premise_cases": premise_cases,
        "glued_cases": glued_cases,
        "violations": violations,
        "status": "PASS" if not violations and premise_cases == glued_cases else "FAIL",
        "claim_ceiling": "bounded corroboration of the generic proof source; not a replacement for Lean checking",
    }
