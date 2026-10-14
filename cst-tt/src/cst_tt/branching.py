from __future__ import annotations

from dataclasses import asdict, dataclass
from itertools import permutations, product
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping

from .corridor import audit_strict_corridor
from .fiach import audit_temporal_fiach, replay_component_certificates
from .package_gluing import audit_package


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load(root: Path, rel: str) -> dict[str, Any]:
    value = json.loads((root / rel).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(rel)
    return value


def _code(value: Any) -> int | None:
    if isinstance(value, Mapping):
        value = value.get("code")
    return int(value) if isinstance(value, int) and not isinstance(value, bool) and value >= 0 else None


def _component(root: Path, fiach: Mapping[str, Any], key: str) -> dict[str, Any]:
    refs = fiach.get("component_refs", {})
    rel = refs.get(key) if isinstance(refs, Mapping) else None
    return _load(root, rel) if isinstance(rel, str) and (root / rel).is_file() else {}


def _model(root: Path, cert: Mapping[str, Any]) -> dict[str, Any]:
    rel = cert.get("model_ref")
    return _load(root, rel) if isinstance(rel, str) and (root / rel).is_file() else {}


def _canonical_branch_shape(root: Path, fiach: Mapping[str, Any]) -> dict[str, Any]:
    package = _model(root, _component(root, fiach, "target_package"))
    corridor = _model(root, _component(root, fiach, "corridor"))
    autonomy = _model(root, _component(root, fiach, "autonomy"))
    package_audit = audit_package(package)
    corridor_audit = audit_strict_corridor(corridor)
    from .withdrawal_autonomy_checker import audit_autonomy
    autonomy_audit = audit_autonomy(autonomy)
    stages = corridor.get("episode", {}).get("stages", []) if isinstance(corridor.get("episode"), Mapping) else []
    increments = []
    if isinstance(stages, list):
        for left, right in zip(stages, stages[1:]):
            if isinstance(left, Mapping) and isinstance(right, Mapping):
                ls = left.get("signature", {})
                rs = right.get("signature", {})
                if isinstance(ls, Mapping) and isinstance(rs, Mapping):
                    increments.append([
                        int(rs.get("predictive_rank", 0)) - int(ls.get("predictive_rank", 0)),
                        int(rs.get("tick_index", 0)) - int(ls.get("tick_index", 0)),
                        int(rs.get("record_value", 0)) - int(ls.get("record_value", 0)),
                    ])
    clause_acceptance = {row.clause: row.accepted for row in package_audit.clause_audits}
    hard_gate_status = {row.clause: row.hard_gate_passed for row in package_audit.clause_audits}
    return {
        "package_clause_acceptance": dict(sorted(clause_acceptance.items())),
        "package_hard_gates": dict(sorted(hard_gate_status.items())),
        "corridor_stage_support_sizes": [len(row.get("active_support", [])) for row in stages if isinstance(row, Mapping)],
        "corridor_signature_increments": increments,
        "corridor_atomic_leg_count": corridor_audit.atomic_leg_count,
        "corridor_route_status": corridor_audit.route_status,
        "autonomy_state_count": len(autonomy.get("states", [])) if isinstance(autonomy.get("states"), list) else 0,
        "autonomy_disturbance_count": len(autonomy.get("disturbances", [])) if isinstance(autonomy.get("disturbances"), list) else 0,
        "autonomy_invariant_size": len(autonomy_audit.computed_invariant_state_ids),
        "autonomy_finite_horizon": autonomy_audit.finite_horizon,
    }


@dataclass(frozen=True)
class TemporalFissionAudit:
    certificate_id: str
    component_hashes_valid: bool
    left_branch_valid: bool
    right_branch_valid: bool
    branch_component_replays_valid: bool
    common_source_exact: bool
    source_package_exact: bool
    targets_distinct: bool
    source_temporal_frontier_exact: bool
    target_shapes_symmetric: bool
    relation_contains_both_branches: bool
    swap_involutive: bool
    swap_fixed_point_free: bool
    validity_preserved_by_swap: bool
    invariant_singleton_selector_absent: bool
    uniqueness_claim_absent: bool
    relation_valued_fission_valid: bool
    failed_obligations: tuple[str, ...]
    source_code: int | None
    left_target_code: int | None
    right_target_code: int | None

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["failed_obligations"] = list(self.failed_obligations)
        return json.loads(json.dumps(value, sort_keys=True))


def audit_temporal_fission(spec: Mapping[str, Any], root: Path) -> TemporalFissionAudit:
    refs = spec.get("branch_certificate_refs", {})
    hashes = spec.get("branch_certificate_sha256", {})
    left_ref = refs.get("left") if isinstance(refs, Mapping) else None
    right_ref = refs.get("right") if isinstance(refs, Mapping) else None
    left = _load(root, left_ref) if isinstance(left_ref, str) and (root / left_ref).is_file() else {}
    right = _load(root, right_ref) if isinstance(right_ref, str) and (root / right_ref).is_file() else {}
    hash_valid = bool(
        isinstance(left_ref, str) and isinstance(right_ref, str)
        and isinstance(hashes, Mapping)
        and hashes.get("left") == sha256(root / left_ref)
        and hashes.get("right") == sha256(root / right_ref)
    )
    left_audit = audit_temporal_fiach(left, root) if left else None
    right_audit = audit_temporal_fiach(right, root) if right else None
    replays = bool(
        left and right
        and all(replay_component_certificates(left, root).values())
        and all(replay_component_certificates(right, root).values())
    )
    source_left = _code(left.get("source"))
    source_right = _code(right.get("source"))
    target_left = _code(left.get("target"))
    target_right = _code(right.get("target"))
    common_source = source_left is not None and source_left == source_right
    left_refs = left.get("component_refs", {}) if isinstance(left.get("component_refs"), Mapping) else {}
    right_refs = right.get("component_refs", {}) if isinstance(right.get("component_refs"), Mapping) else {}
    source_package_exact = bool(
        left_refs.get("source_package") == right_refs.get("source_package")
        and left.get("component_sha256", {}).get("source_package") == right.get("component_sha256", {}).get("source_package")
    )
    targets_distinct = target_left is not None and target_right is not None and target_left != target_right

    left_corridor = _model(root, _component(root, left, "corridor"))
    right_corridor = _model(root, _component(root, right, "corridor"))
    left_stages = left_corridor.get("episode", {}).get("stages", []) if isinstance(left_corridor.get("episode"), Mapping) else []
    right_stages = right_corridor.get("episode", {}).get("stages", []) if isinstance(right_corridor.get("episode"), Mapping) else []
    left_initial = left_stages[0] if isinstance(left_stages, list) and left_stages else {}
    right_initial = right_stages[0] if isinstance(right_stages, list) and right_stages else {}
    source_frontier = bool(
        isinstance(left_initial, Mapping) and isinstance(right_initial, Mapping)
        and left_initial.get("signature") == right_initial.get("signature")
        and left_initial.get("active_support") == right_initial.get("active_support")
    )
    symmetric = _canonical_branch_shape(root, left) == _canonical_branch_shape(root, right) if left and right else False
    relation_rows = spec.get("relation", [])
    relation = {
        (_code(row.get("source")), _code(row.get("target")))
        for row in relation_rows
        if isinstance(row, Mapping)
    } if isinstance(relation_rows, list) else set()
    relation_both = (source_left, target_left) in relation and (source_left, target_right) in relation
    swap = spec.get("target_swap", {})
    swap_map: dict[int, int] = {}
    if isinstance(swap, Mapping):
        for key, value in swap.items():
            try:
                k = int(key)
            except (TypeError, ValueError):
                continue
            if isinstance(value, int) and not isinstance(value, bool):
                swap_map[k] = int(value)
    valid_targets = {target_left, target_right} if targets_distinct else set()
    involutive = bool(valid_targets and all(swap_map.get(swap_map.get(t, -1)) == t for t in valid_targets))
    fixed_point_free = bool(valid_targets and all(swap_map.get(t) != t for t in valid_targets))
    preserves = bool(valid_targets and {swap_map.get(t) for t in valid_targets} == valid_targets)
    no_invariant_singleton = bool(valid_targets and not any(swap_map.get(t) == t for t in valid_targets))
    uniqueness_absent = all(key not in spec for key in ("unique_continuer", "selected_target", "numerical_identity", "same_subject"))

    obligations = {
        "FIS-O01-component-hashes": hash_valid,
        "FIS-O02-left-branch-valid": bool(left_audit and left_audit.aggregate_valid),
        "FIS-O03-right-branch-valid": bool(right_audit and right_audit.aggregate_valid),
        "FIS-O04-component-replays": replays,
        "FIS-O05-common-source": common_source,
        "FIS-O06-source-package-exact": source_package_exact,
        "FIS-O07-targets-distinct": targets_distinct,
        "FIS-O08-source-temporal-frontier-exact": source_frontier,
        "FIS-O09-target-shapes-symmetric": symmetric,
        "FIS-O10-relation-contains-both": relation_both,
        "FIS-O11-swap-involutive": involutive,
        "FIS-O12-swap-fixed-point-free": fixed_point_free,
        "FIS-O13-validity-preserved": preserves,
        "FIS-O14-no-invariant-singleton": no_invariant_singleton,
        "FIS-O15-uniqueness-claim-absent": uniqueness_absent,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return TemporalFissionAudit(
        certificate_id=str(spec.get("certificate_id", "")),
        component_hashes_valid=hash_valid,
        left_branch_valid=bool(left_audit and left_audit.aggregate_valid),
        right_branch_valid=bool(right_audit and right_audit.aggregate_valid),
        branch_component_replays_valid=replays,
        common_source_exact=common_source,
        source_package_exact=source_package_exact,
        targets_distinct=targets_distinct,
        source_temporal_frontier_exact=source_frontier,
        target_shapes_symmetric=symmetric,
        relation_contains_both_branches=relation_both,
        swap_involutive=involutive,
        swap_fixed_point_free=fixed_point_free,
        validity_preserved_by_swap=preserves,
        invariant_singleton_selector_absent=no_invariant_singleton,
        uniqueness_claim_absent=uniqueness_absent,
        relation_valued_fission_valid=not failed,
        failed_obligations=failed,
        source_code=source_left if common_source else None,
        left_target_code=target_left,
        right_target_code=target_right,
    )


@dataclass(frozen=True)
class FusionBoundaryAudit:
    certificate_id: str
    component_hashes_valid: bool
    left_lineage_valid: bool
    right_lineage_valid: bool
    distinct_sources: bool
    common_target: bool
    branchwise_payload_preserved: bool
    target_package_audited: bool
    action_credit_conflict_witnessed: bool
    recombination_failure_witnessed: bool
    integrated_target_package_fails: bool
    merger_does_not_imply_package: bool
    fusion_boundary_valid: bool
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["failed_obligations"] = list(self.failed_obligations)
        return value


def audit_fusion_boundary(spec: Mapping[str, Any], root: Path) -> FusionBoundaryAudit:
    refs = spec.get("component_refs", {})
    hashes = spec.get("component_sha256", {})
    required = ("left_corridor", "right_corridor", "target_package")
    certs: dict[str, dict[str, Any]] = {}
    hash_checks = []
    for key in required:
        rel = refs.get(key) if isinstance(refs, Mapping) else None
        certs[key] = _load(root, rel) if isinstance(rel, str) and (root / rel).is_file() else {}
        hash_checks.append(isinstance(rel, str) and isinstance(hashes, Mapping) and hashes.get(key) == sha256(root / rel))
    left_model = _model(root, certs["left_corridor"])
    right_model = _model(root, certs["right_corridor"])
    package_model = _model(root, certs["target_package"])
    left_audit = audit_strict_corridor(left_model)
    right_audit = audit_strict_corridor(right_model)
    package_audit = audit_package(package_model)
    left_chain = left_model.get("carrier_chain", [])
    right_chain = right_model.get("carrier_chain", [])
    left_source = _code(left_chain[0]) if isinstance(left_chain, list) and left_chain else None
    right_source = _code(right_chain[0]) if isinstance(right_chain, list) and right_chain else None
    left_target = _code(left_chain[-1]) if isinstance(left_chain, list) and left_chain else None
    right_target = _code(right_chain[-1]) if isinstance(right_chain, list) and right_chain else None
    distinct_sources = left_source is not None and right_source is not None and left_source != right_source
    common_target = left_target is not None and left_target == right_target and _code(package_model.get("target")) == left_target
    branchwise = spec.get("branchwise_payload_preserved") is True
    clause_acceptance = {row.clause: row.accepted for row in package_audit.clause_audits}
    hard_gate_status = {row.clause: row.hard_gate_passed for row in package_audit.clause_audits}
    c5 = clause_acceptance.get("C5_ACTION_CREDIT") is False or hard_gate_status.get("C5_ACTION_CREDIT") is False
    c7 = clause_acceptance.get("C7_BINDING_RECOMBINATION") is False or hard_gate_status.get("C7_BINDING_RECOMBINATION") is False
    package_fails = not package_audit.integrated_package_valid
    merger_boundary = left_audit.strict_corridor_valid and right_audit.strict_corridor_valid and package_fails
    obligations = {
        "FUS-O01-component-hashes": all(hash_checks),
        "FUS-O02-left-lineage-valid": left_audit.strict_corridor_valid,
        "FUS-O03-right-lineage-valid": right_audit.strict_corridor_valid,
        "FUS-O04-distinct-sources": distinct_sources,
        "FUS-O05-common-target": common_target,
        "FUS-O06-branchwise-payload-preserved": branchwise,
        "FUS-O07-target-package-audited": bool(package_model),
        "FUS-O08-action-credit-conflict": c5,
        "FUS-O09-recombination-failure": c7,
        "FUS-O10-integrated-package-fails": package_fails,
        "FUS-O11-merger-does-not-imply-package": merger_boundary,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return FusionBoundaryAudit(
        certificate_id=str(spec.get("certificate_id", "")),
        component_hashes_valid=all(hash_checks),
        left_lineage_valid=left_audit.strict_corridor_valid,
        right_lineage_valid=right_audit.strict_corridor_valid,
        distinct_sources=distinct_sources,
        common_target=common_target,
        branchwise_payload_preserved=branchwise,
        target_package_audited=bool(package_model),
        action_credit_conflict_witnessed=c5,
        recombination_failure_witnessed=c7,
        integrated_target_package_fails=package_fails,
        merger_does_not_imply_package=merger_boundary,
        fusion_boundary_valid=not failed,
        failed_obligations=failed,
    )


def bounded_fission_symmetry_search(max_targets: int = 4) -> dict[str, Any]:
    candidates = 0
    qualified = 0
    selector_violations = 0
    minimum_target_count: int | None = None
    per_n: list[dict[str, Any]] = []
    for n in range(1, max_targets + 1):
        local_candidates = 0
        local_qualified = 0
        targets = tuple(range(n))
        for perm in permutations(targets):
            for relation_bits in product((False, True), repeat=n):
                relation = {i for i, bit in enumerate(relation_bits) if bit}
                for validity_bits in product((False, True), repeat=n):
                    valid = {i for i, bit in enumerate(validity_bits) if bit}
                    candidates += 1
                    local_candidates += 1
                    fork = len(relation) >= 2 and relation.issubset(valid)
                    preserved = {perm[i] for i in relation} == relation if relation else False
                    fixed_point_free = relation and all(perm[i] != i for i in relation)
                    involutive = relation and all(perm[perm[i]] == i for i in relation)
                    if fork and preserved and fixed_point_free and involutive:
                        qualified += 1
                        local_qualified += 1
                        if any(perm[i] == i for i in relation):
                            selector_violations += 1
                        if minimum_target_count is None:
                            minimum_target_count = n
        per_n.append({"target_count": n, "candidates": local_candidates, "qualified_symmetric_forks": local_qualified})
    return {
        "schema_version": "CST-TT-06",
        "algorithm": "exhaustive-relations-validity-sets-and-permutations",
        "max_targets": max_targets,
        "candidates_examined": candidates,
        "qualified_symmetric_forks": qualified,
        "invariant_singleton_selector_violations": selector_violations,
        "minimum_target_count": minimum_target_count,
        "per_target_count": per_n,
        "claim_ceiling": "bounded symmetry and relation-valued fission result; no identity conclusion",
    }


def bounded_fusion_boundary_search() -> dict[str, Any]:
    names = ("left_lineage", "right_lineage", "distinct_sources", "common_target", "branchwise", "credit_ok", "recombination_ok")
    rows = []
    for bits in product((False, True), repeat=len(names)):
        row = dict(zip(names, bits, strict=True))
        row["merger_premise"] = all(row[name] for name in names[:5])
        row["package_ok"] = row["credit_ok"] and row["recombination_ok"]
        row["fusion_boundary"] = row["merger_premise"] and not row["package_ok"]
        rows.append(row)
    return {
        "schema_version": "CST-TT-06",
        "algorithm": "exhaustive-seven-Boolean-fusion-boundary-table",
        "candidates_examined": len(rows),
        "merger_premise_cases": sum(1 for row in rows if row["merger_premise"]),
        "boundary_cases": sum(1 for row in rows if row["fusion_boundary"]),
        "rows": rows,
        "claim_ceiling": "finite logical separation of lineage merger from integrated target package",
    }
