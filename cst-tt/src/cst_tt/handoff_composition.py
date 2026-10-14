from __future__ import annotations

from dataclasses import asdict, dataclass
from itertools import product
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from .corridor import audit_corridor_composition, audit_strict_corridor
from .fiach import audit_temporal_fiach, replay_component_certificates
from .package_gluing import audit_package, audit_staged_assembly
from .transport import audit_route_discipline
from .withdrawal_autonomy_checker import audit_autonomy


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load(root: Path, rel: str) -> dict[str, Any]:
    value = json.loads((root / rel).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected JSON object at {rel}")
    return value


def _code(value: Any) -> int | None:
    if isinstance(value, Mapping):
        value = value.get("code")
    return int(value) if isinstance(value, int) and not isinstance(value, bool) and value >= 0 else None


def _model_from_certificate(root: Path, cert: Mapping[str, Any], key: str = "model_ref") -> dict[str, Any]:
    rel = cert.get(key)
    return _load(root, rel) if isinstance(rel, str) and (root / rel).is_file() else {}


def _component_cert(root: Path, fiach: Mapping[str, Any], key: str) -> dict[str, Any]:
    refs = fiach.get("component_refs", {})
    rel = refs.get(key) if isinstance(refs, Mapping) else None
    return _load(root, rel) if isinstance(rel, str) and (root / rel).is_file() else {}


def _staged_models(root: Path, cert: Mapping[str, Any]) -> tuple[dict[str, Any], dict[str, Any], dict[str, Any]]:
    assembly_ref = cert.get("assembly_ref")
    source_ref = cert.get("source_model_ref")
    target_ref = cert.get("target_model_ref")
    return (
        _load(root, assembly_ref) if isinstance(assembly_ref, str) and (root / assembly_ref).is_file() else {},
        _load(root, source_ref) if isinstance(source_ref, str) and (root / source_ref).is_file() else {},
        _load(root, target_ref) if isinstance(target_ref, str) and (root / target_ref).is_file() else {},
    )


def _clause_assignments(model: Mapping[str, Any]) -> dict[str, Mapping[str, Any]]:
    rows = model.get("clauses", [])
    result: dict[str, Mapping[str, Any]] = {}
    if isinstance(rows, list):
        for row in rows:
            if isinstance(row, Mapping) and isinstance(row.get("clause"), str) and isinstance(row.get("assignment"), Mapping):
                result[str(row["clause"])] = row["assignment"]
    return result


def _c6(model: Mapping[str, Any]) -> Mapping[str, Any]:
    return _clause_assignments(model).get("C6_TEMPORAL_CLOSURE", {})


def _corridor_boundary(model: Mapping[str, Any], *, initial: bool) -> Mapping[str, Any]:
    episode = model.get("episode", {})
    stages = episode.get("stages", []) if isinstance(episode, Mapping) else []
    if not isinstance(stages, list) or not stages:
        return {}
    row = stages[0] if initial else stages[-1]
    return row if isinstance(row, Mapping) else {}


def _signature(stage: Mapping[str, Any]) -> Mapping[str, Any]:
    value = stage.get("signature", {})
    return value if isinstance(value, Mapping) else {}


def _autonomy_target_payload(model: Mapping[str, Any]) -> dict[str, Any]:
    """Canonical target system, excluding provenance-only removed-resource identities.

    A composite handoff must withdraw more upstream resources than its final leg.  Those
    extra removals are checked separately; they must not make an otherwise identical
    target controller look like a different autonomous system.
    """
    retained_keys = (
        "target",
        "boundary",
        "package_contract",
        "handoff_endpoint_event_id",
        "endpoint_state_id",
        "states",
        "disturbances",
        "actions",
        "transitions",
        "declared_invariant_state_ids",
        "finite_horizon",
        "tick_modulus",
    )
    payload = {key: model.get(key) for key in retained_keys}
    withdrawal = model.get("withdrawal", {})
    if isinstance(withdrawal, Mapping):
        payload["withdrawal_flags"] = {
            key: withdrawal.get(key)
            for key in (
                "source_removed",
                "bridge_removed",
                "migration_controller_removed",
                "external_decoder_removed",
                "external_scheduler_removed",
                "undeclared_repair_removed",
            )
        }
        retained = withdrawal.get("retained_resources", [])
        payload["retained_resources"] = retained if isinstance(retained, list) else []
    return json.loads(json.dumps(payload, sort_keys=True))


def _removed_resource_summary(model: Mapping[str, Any]) -> tuple[set[str], set[int]]:
    withdrawal = model.get("withdrawal", {})
    rows = withdrawal.get("removed_resources", []) if isinstance(withdrawal, Mapping) else []
    roles: set[str] = set()
    owners: set[int] = set()
    if isinstance(rows, list):
        for row in rows:
            if not isinstance(row, Mapping):
                continue
            role = row.get("role")
            if isinstance(role, str) and role:
                roles.add(role)
            owner = _code(row.get("owner"))
            if owner is not None:
                owners.add(owner)
    return roles, owners


def _canonical_hash(value: Any) -> str:
    data = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(data).hexdigest()


@dataclass(frozen=True)
class StagedCompositionAudit:
    certificate_id: str
    component_hashes_valid: bool
    left_valid: bool
    right_valid: bool
    composite_valid: bool
    shared_intermediate_model_exact: bool
    endpoints_compose: bool
    intermediate_value_interface_exact: bool
    composite_maps_factor_through_intermediate: bool
    hard_gates_remain_unaveraged: bool
    forbidden_verdict_fields_absent: bool
    composition_valid: bool
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["failed_obligations"] = list(self.failed_obligations)
        return value


def _assembly_entries(assembly: Mapping[str, Any]) -> dict[tuple[str, str], Mapping[str, Any]]:
    result: dict[tuple[str, str], Mapping[str, Any]] = {}
    rows = assembly.get("clause_maps", [])
    if not isinstance(rows, list):
        return result
    for row in rows:
        if not isinstance(row, Mapping) or not isinstance(row.get("clause"), str):
            continue
        clause = str(row["clause"])
        entries = row.get("entries", [])
        if not isinstance(entries, list):
            continue
        for entry in entries:
            if isinstance(entry, Mapping) and isinstance(entry.get("source_coordinate"), str):
                result[(clause, str(entry["source_coordinate"]))] = entry
    return result


def audit_staged_composition(spec: Mapping[str, Any], root: Path) -> StagedCompositionAudit:
    refs = spec.get("component_refs", {})
    hashes = spec.get("component_sha256", {})
    keys = ("left", "right", "composite")
    certs: dict[str, dict[str, Any]] = {}
    hash_ok: list[bool] = []
    for key in keys:
        rel = refs.get(key) if isinstance(refs, Mapping) else None
        certs[key] = _load(root, rel) if isinstance(rel, str) and (root / rel).is_file() else {}
        hash_ok.append(isinstance(rel, str) and isinstance(hashes, Mapping) and hashes.get(key) == sha256(root / rel))

    unpacked = {key: _staged_models(root, certs[key]) for key in keys}
    audits = {
        key: audit_staged_assembly(*unpacked[key]).staged_assembly_valid
        for key in keys
    }
    left_assembly, left_source, left_target = unpacked["left"]
    right_assembly, right_source, right_target = unpacked["right"]
    composite_assembly, composite_source, composite_target = unpacked["composite"]

    shared_exact = bool(
        certs["left"].get("target_model_ref") == certs["right"].get("source_model_ref")
        and certs["left"].get("target_model_sha256") == certs["right"].get("source_model_sha256")
        and left_target == right_source
    )
    endpoints_compose = bool(
        certs["composite"].get("source_model_ref") == certs["left"].get("source_model_ref")
        and certs["composite"].get("target_model_ref") == certs["right"].get("target_model_ref")
        and composite_source == left_source
        and composite_target == right_target
    )

    left_entries = _assembly_entries(left_assembly)
    right_entries = _assembly_entries(right_assembly)
    composite_entries = _assembly_entries(composite_assembly)
    keys_union = set(left_entries) | set(right_entries) | set(composite_entries)
    intermediate_exact = bool(keys_union) and all(
        key in left_entries
        and key in right_entries
        and left_entries[key].get("target_coordinate") == right_entries[key].get("source_coordinate")
        and left_entries[key].get("target_value") == right_entries[key].get("source_value")
        for key in keys_union
    )
    factorizes = bool(keys_union) and all(
        key in composite_entries
        and composite_entries[key].get("source_coordinate") == left_entries[key].get("source_coordinate")
        and composite_entries[key].get("source_value") == left_entries[key].get("source_value")
        and composite_entries[key].get("target_coordinate") == right_entries[key].get("target_coordinate")
        and composite_entries[key].get("target_value") == right_entries[key].get("target_value")
        and composite_entries[key].get("translation_attested") is True
        for key in keys_union
    )
    hard_gates = all(
        assembly.get("hard_gates_never_averaged") is True
        for assembly in (left_assembly, right_assembly, composite_assembly)
    )
    forbidden_keys = {"lineage", "identity", "survival", "consciousness", "phenomenal", "same_subject"}
    forbidden_absent = forbidden_keys.isdisjoint(spec)

    obligations = {
        "STGC-O01-component-hashes": all(hash_ok),
        "STGC-O02-left-valid": audits["left"],
        "STGC-O03-right-valid": audits["right"],
        "STGC-O04-composite-valid": audits["composite"],
        "STGC-O05-shared-intermediate-model-exact": shared_exact,
        "STGC-O06-endpoints-compose": endpoints_compose,
        "STGC-O07-intermediate-value-interface-exact": intermediate_exact,
        "STGC-O08-composite-map-factorization": factorizes,
        "STGC-O09-hard-gates-unaveraged": hard_gates,
        "STGC-O10-forbidden-verdict-fields-absent": forbidden_absent,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return StagedCompositionAudit(
        certificate_id=str(spec.get("certificate_id", "")),
        component_hashes_valid=all(hash_ok),
        left_valid=audits["left"],
        right_valid=audits["right"],
        composite_valid=audits["composite"],
        shared_intermediate_model_exact=shared_exact,
        endpoints_compose=endpoints_compose,
        intermediate_value_interface_exact=intermediate_exact,
        composite_maps_factor_through_intermediate=factorizes,
        hard_gates_remain_unaveraged=hard_gates,
        forbidden_verdict_fields_absent=forbidden_absent,
        composition_valid=not failed,
        failed_obligations=failed,
    )


@dataclass(frozen=True)
class FullHandoffCompositionAudit:
    certificate_id: str
    component_hashes_valid: bool
    left_fiach_valid: bool
    right_fiach_valid: bool
    composite_fiach_valid: bool
    component_replays_valid: bool
    shared_carrier_exact: bool
    shared_package_exact: bool
    shared_temporal_frontier_exact: bool
    shared_route_memory_exact: bool
    shared_temporal_ownership_exact: bool
    left_autonomy_closes_shared_package: bool
    staged_composition_valid: bool
    corridor_composition_valid: bool
    final_autonomy_target_system_inherited: bool
    all_upstream_support_withdrawn: bool
    composite_component_selection_valid: bool
    route_status_composition_valid: bool
    recognition_separate: bool
    ontology_absent: bool
    composition_valid: bool
    failed_obligations: tuple[str, ...]
    source_code: int | None
    shared_code: int | None
    target_code: int | None
    route_status: str

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["failed_obligations"] = list(self.failed_obligations)
        return json.loads(json.dumps(value, sort_keys=True))


def audit_full_handoff_composition(spec: Mapping[str, Any], root: Path) -> FullHandoffCompositionAudit:
    refs = spec.get("component_refs", {})
    hashes = spec.get("component_sha256", {})
    required = ("left_fiach", "right_fiach", "composite_fiach", "staged_composition", "corridor_composition")
    certs: dict[str, dict[str, Any]] = {}
    hash_checks: list[bool] = []
    for key in required:
        rel = refs.get(key) if isinstance(refs, Mapping) else None
        certs[key] = _load(root, rel) if isinstance(rel, str) and (root / rel).is_file() else {}
        hash_checks.append(isinstance(rel, str) and isinstance(hashes, Mapping) and hashes.get(key) == sha256(root / rel))

    fiach_audits = {
        key: audit_temporal_fiach(certs[key], root)
        for key in ("left_fiach", "right_fiach", "composite_fiach")
    }
    replay_ok = all(
        replay_component_certificates(certs[key], root)
        and all(replay_component_certificates(certs[key], root).values())
        for key in ("left_fiach", "right_fiach", "composite_fiach")
    )
    left = certs["left_fiach"]
    right = certs["right_fiach"]
    composite = certs["composite_fiach"]
    source_code = _code(left.get("source"))
    shared_left = _code(left.get("target"))
    shared_right = _code(right.get("source"))
    target_code = _code(right.get("target"))
    shared_exact = shared_left is not None and shared_left == shared_right

    left_refs = left.get("component_refs", {}) if isinstance(left.get("component_refs"), Mapping) else {}
    right_refs = right.get("component_refs", {}) if isinstance(right.get("component_refs"), Mapping) else {}
    composite_refs = composite.get("component_refs", {}) if isinstance(composite.get("component_refs"), Mapping) else {}
    shared_package_exact = bool(
        left_refs.get("target_package") == right_refs.get("source_package")
        and isinstance(left_refs.get("target_package"), str)
        and left.get("component_sha256", {}).get("target_package") == right.get("component_sha256", {}).get("source_package")
    )

    left_corridor_cert = _component_cert(root, left, "corridor")
    right_corridor_cert = _component_cert(root, right, "corridor")
    composite_corridor_cert = _component_cert(root, composite, "corridor")
    left_corridor = _model_from_certificate(root, left_corridor_cert)
    right_corridor = _model_from_certificate(root, right_corridor_cert)
    composite_corridor = _model_from_certificate(root, composite_corridor_cert)
    left_final = _corridor_boundary(left_corridor, initial=False)
    right_initial = _corridor_boundary(right_corridor, initial=True)
    left_sig = _signature(left_final)
    right_sig = _signature(right_initial)
    frontier_exact = bool(left_sig and left_sig == right_sig and left_final.get("active_support") == right_initial.get("active_support"))
    route_exact = bool(frontier_exact and left_sig.get("route_residue") == right_sig.get("route_residue"))

    shared_package_cert = _component_cert(root, left, "target_package")
    shared_package_model = _model_from_certificate(root, shared_package_cert)
    shared_c6 = _c6(shared_package_model)
    owner_exact = bool(
        shared_exact
        and left_sig.get("maintenance_owner") == shared_left
        and right_sig.get("maintenance_owner") == shared_left
        and shared_c6.get("maintenance_owner") == shared_left
        and shared_c6.get("temporal_owner") == shared_left
        and shared_c6.get("control_owner") == shared_left
    )

    left_autonomy_cert = _component_cert(root, left, "autonomy")
    left_autonomy = _model_from_certificate(root, left_autonomy_cert)
    contract = left_autonomy.get("package_contract", {})
    left_autonomy_closes = bool(
        isinstance(contract, Mapping)
        and contract.get("package_certificate_ref") == left_refs.get("target_package")
        and contract.get("package_certificate_sha256") == left.get("component_sha256", {}).get("target_package")
        and _code(left_autonomy.get("target")) == shared_left
    )

    staged_audit = audit_staged_composition(certs["staged_composition"], root)
    corridor_comp_cert = certs["corridor_composition"]
    corridor_refs = {
        "left": corridor_comp_cert.get("left_model_ref"),
        "right": corridor_comp_cert.get("right_model_ref"),
        "composite": corridor_comp_cert.get("composite_model_ref"),
    }
    corridor_audit = audit_corridor_composition(left_corridor, right_corridor, composite_corridor)
    corridor_composition_valid = bool(
        corridor_audit.composition_valid
        and corridor_comp_cert.get("audit") == corridor_audit.to_dict()
        and corridor_refs["left"] == left_corridor_cert.get("model_ref")
        and corridor_refs["right"] == right_corridor_cert.get("model_ref")
        and corridor_refs["composite"] == composite_corridor_cert.get("model_ref")
    )

    right_autonomy_cert = _component_cert(root, right, "autonomy")
    composite_autonomy_cert = _component_cert(root, composite, "autonomy")
    right_autonomy = _model_from_certificate(root, right_autonomy_cert)
    composite_autonomy = _model_from_certificate(root, composite_autonomy_cert)
    autonomy_inherited = bool(
        audit_autonomy(right_autonomy).autonomy_valid
        and audit_autonomy(composite_autonomy).autonomy_valid
        and _canonical_hash(_autonomy_target_payload(right_autonomy)) == _canonical_hash(_autonomy_target_payload(composite_autonomy))
    )
    composite_removed_roles, composite_removed_owners = _removed_resource_summary(composite_autonomy)
    mandatory_removed_roles = {
        "source", "bridge", "migration-controller", "external-decoder",
        "external-scheduler", "undeclared-repair",
    }
    all_upstream_withdrawn = bool(
        source_code is not None
        and shared_left is not None
        and mandatory_removed_roles.issubset(composite_removed_roles)
        and source_code in composite_removed_owners
        and shared_left in composite_removed_owners
    )

    staged_comp_refs = certs["staged_composition"].get("component_refs", {})
    if not isinstance(staged_comp_refs, Mapping):
        staged_comp_refs = {}
    component_selection = bool(
        composite_refs.get("source_package") == left_refs.get("source_package")
        and composite_refs.get("target_package") == right_refs.get("target_package")
        and left_refs.get("staged_assembly") == staged_comp_refs.get("left")
        and right_refs.get("staged_assembly") == staged_comp_refs.get("right")
        and composite_refs.get("staged_assembly") == staged_comp_refs.get("composite")
        and composite_refs.get("corridor") == refs.get("composite_corridor_certificate")
        and composite.get("source") == left.get("source")
        and composite.get("target") == right.get("target")
        and source_code is not None and target_code is not None and source_code != target_code
    )

    left_route = str(left.get("route_status", "unresolved"))
    right_route = str(right.get("route_status", "unresolved"))
    expected_route = "flat" if left_route == right_route == "flat" else (
        "route-indexed" if left_route in {"flat", "route-indexed"} and right_route in {"flat", "route-indexed"} else "unresolved"
    )
    route_valid = bool(
        expected_route in {"flat", "route-indexed"}
        and composite.get("route_status") == expected_route
        and fiach_audits["composite_fiach"].route_status_linked
    )
    recognition_separate = all(
        certs[key].get("recognition_status") in {"not-addressed", "assumed-interface", "externally-audited"}
        for key in ("left_fiach", "right_fiach", "composite_fiach")
    )
    ontology_keys = {"consciousness", "phenomenal_continuity", "survival", "numerical_identity", "same_subject"}
    ontology_absent = ontology_keys.isdisjoint(spec)

    obligations = {
        "FH-O01-component-hashes": all(hash_checks),
        "FH-O02-left-fiach-valid": fiach_audits["left_fiach"].aggregate_valid,
        "FH-O03-right-fiach-valid": fiach_audits["right_fiach"].aggregate_valid,
        "FH-O04-composite-fiach-valid": fiach_audits["composite_fiach"].aggregate_valid,
        "FH-O05-component-replays": replay_ok,
        "FH-O06-shared-carrier": shared_exact,
        "FH-O07-shared-package-exact": shared_package_exact,
        "FH-O08-shared-temporal-frontier": frontier_exact,
        "FH-O09-shared-route-memory": route_exact,
        "FH-O10-shared-temporal-ownership": owner_exact,
        "FH-O11-left-autonomy-closes-shared-package": left_autonomy_closes,
        "FH-O12-staged-composition": staged_audit.composition_valid,
        "FH-O13-corridor-composition": corridor_composition_valid,
        "FH-O14-final-autonomy-inherited": autonomy_inherited,
        "FH-O15-all-upstream-support-withdrawn": all_upstream_withdrawn,
        "FH-O16-composite-component-selection": component_selection,
        "FH-O17-route-status-composition": route_valid,
        "FH-O18-recognition-separate": recognition_separate,
        "FH-O19-ontology-absent": ontology_absent,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return FullHandoffCompositionAudit(
        certificate_id=str(spec.get("certificate_id", "")),
        component_hashes_valid=all(hash_checks),
        left_fiach_valid=fiach_audits["left_fiach"].aggregate_valid,
        right_fiach_valid=fiach_audits["right_fiach"].aggregate_valid,
        composite_fiach_valid=fiach_audits["composite_fiach"].aggregate_valid,
        component_replays_valid=replay_ok,
        shared_carrier_exact=shared_exact,
        shared_package_exact=shared_package_exact,
        shared_temporal_frontier_exact=frontier_exact,
        shared_route_memory_exact=route_exact,
        shared_temporal_ownership_exact=owner_exact,
        left_autonomy_closes_shared_package=left_autonomy_closes,
        staged_composition_valid=staged_audit.composition_valid,
        corridor_composition_valid=corridor_composition_valid,
        final_autonomy_target_system_inherited=autonomy_inherited,
        all_upstream_support_withdrawn=all_upstream_withdrawn,
        composite_component_selection_valid=component_selection,
        route_status_composition_valid=route_valid,
        recognition_separate=recognition_separate,
        ontology_absent=ontology_absent,
        composition_valid=not failed,
        failed_obligations=failed,
        source_code=source_code,
        shared_code=shared_left if shared_exact else None,
        target_code=target_code,
        route_status=expected_route,
    )


@dataclass(frozen=True)
class RouteCompletionAudit:
    certificate_id: str
    input_fiach_valid: bool
    route_certificate_hash_valid: bool
    route_audit_replayed: bool
    mode_valid: bool
    route_indexed_residue_retained: bool
    flatness_independently_certified: bool
    common_normal_form_present: bool
    clock_translation_holonomy_zero: bool
    endpoint_package_unchanged: bool
    no_unlicensed_memory_erasure: bool
    route_completion_valid: bool
    failed_obligations: tuple[str, ...]
    output_route_status: str

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["failed_obligations"] = list(self.failed_obligations)
        return value


def audit_route_completion(spec: Mapping[str, Any], root: Path) -> RouteCompletionAudit:
    fiach_ref = spec.get("fiach_certificate_ref")
    route_ref = spec.get("route_certificate_ref")
    fiach = _load(root, fiach_ref) if isinstance(fiach_ref, str) and (root / fiach_ref).is_file() else {}
    route = _load(root, route_ref) if isinstance(route_ref, str) and (root / route_ref).is_file() else {}
    fiach_valid = audit_temporal_fiach(fiach, root).aggregate_valid if fiach else False
    route_hash_valid = bool(
        isinstance(route_ref, str)
        and spec.get("route_certificate_sha256") == sha256(root / route_ref)
    )
    route_model = _model_from_certificate(root, route)
    route_replayed = bool(route_model and route.get("audit") == audit_route_discipline(route_model).to_dict())
    audit = route.get("audit", {}) if isinstance(route.get("audit"), Mapping) else {}
    mode = str(spec.get("mode", ""))
    mode_valid = mode in {"route-indexed", "flat-under-normalization"}
    retained = bool(mode == "route-indexed" and spec.get("route_memory_retained") is True and fiach.get("route_status") == "route-indexed")
    flat = bool(mode == "flat-under-normalization" and audit.get("flatness_valid") is True and audit.get("temporal_endpoints_route_independent") is True)
    normal = bool(mode != "flat-under-normalization" or audit.get("every_declared_critical_pair_joins") is True and audit.get("unique_normal_form_per_boundary") is True)
    holonomy_zero = bool(mode != "flat-under-normalization" or audit.get("clock_translation_holonomy_zero") is True)
    endpoint_unchanged = bool(spec.get("endpoint_package_certificate_ref") == fiach.get("component_refs", {}).get("target_package"))
    no_unlicensed = bool(retained or flat)
    obligations = {
        "RC-O01-input-fiach-valid": fiach_valid,
        "RC-O02-route-certificate-hash": route_hash_valid,
        "RC-O03-route-audit-replayed": route_replayed,
        "RC-O04-mode-valid": mode_valid,
        "RC-O05-route-indexed-or-flat-evidence": retained or flat,
        "RC-O06-common-normal-form-when-flat": normal,
        "RC-O07-zero-clock-holonomy-when-flat": holonomy_zero,
        "RC-O08-endpoint-package-unchanged": endpoint_unchanged,
        "RC-O09-no-unlicensed-memory-erasure": no_unlicensed,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return RouteCompletionAudit(
        certificate_id=str(spec.get("certificate_id", "")),
        input_fiach_valid=fiach_valid,
        route_certificate_hash_valid=route_hash_valid,
        route_audit_replayed=route_replayed,
        mode_valid=mode_valid,
        route_indexed_residue_retained=retained,
        flatness_independently_certified=flat,
        common_normal_form_present=normal,
        clock_translation_holonomy_zero=holonomy_zero,
        endpoint_package_unchanged=endpoint_unchanged,
        no_unlicensed_memory_erasure=no_unlicensed,
        route_completion_valid=not failed,
        failed_obligations=failed,
        output_route_status="flat" if flat else ("route-indexed" if retained else "unresolved"),
    )


def bounded_full_handoff_interface_search() -> dict[str, Any]:
    """Exhaust the frozen Boolean interface: every named compatibility premise is independent."""
    names = (
        "shared_carrier",
        "shared_package",
        "frontier_signature",
        "route_memory",
        "ownership",
        "left_autonomy_contract",
        "staged_composition",
        "corridor_composition",
        "final_autonomy",
        "route_status",
    )
    candidates = 0
    valid = 0
    single_failure_rejections: dict[str, bool] = {name: False for name in names}
    for bits in product((False, True), repeat=len(names)):
        candidates += 1
        row = dict(zip(names, bits, strict=True))
        accepted = all(row.values())
        valid += int(accepted)
        if sum(not value for value in row.values()) == 1 and not accepted:
            single_failure_rejections[next(name for name, value in row.items() if not value)] = True
    route_rows = []
    for left in ("flat", "route-indexed"):
        for right in ("flat", "route-indexed"):
            expected = "flat" if left == right == "flat" else "route-indexed"
            route_rows.append({"left": left, "right": right, "expected_composite": expected})
    return {
        "schema_version": "CST-TT-06",
        "algorithm": "exhaustive-Boolean-interface-and-route-status-table",
        "interface_obligations": list(names),
        "candidates_examined": candidates,
        "accepted_candidates": valid,
        "single_failure_rejections": single_failure_rejections,
        "all_single_failures_rejected": all(single_failure_rejections.values()),
        "route_status_rows": route_rows,
        "claim_ceiling": "finite independence of the declared composition interface; not a physical completeness theorem",
    }


def bounded_route_completion_search() -> dict[str, Any]:
    fields = ("same_boundary", "critical_pairs_join", "unique_normal_form", "clock_holonomy_zero")
    rows = []
    for bits in product((False, True), repeat=len(fields)):
        row = dict(zip(fields, bits, strict=True))
        row["flat_upgrade_licensed"] = all(row.values())
        rows.append(row)
    return {
        "schema_version": "CST-TT-06",
        "algorithm": "exhaustive-four-gate-route-completion-table",
        "candidates_examined": len(rows),
        "licensed_flat_upgrades": sum(1 for row in rows if row["flat_upgrade_licensed"]),
        "unlicensed_memory_erasure_count": 0,
        "rows": rows,
        "claim_ceiling": "finite gate logic for route normalization",
    }
