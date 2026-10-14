from __future__ import annotations

from dataclasses import asdict, dataclass
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping

from .package_gluing import audit_package, audit_staged_assembly
from .corridor import audit_strict_corridor
from .withdrawal_autonomy_checker import audit_autonomy


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def _load(root: Path, rel: str) -> dict[str, Any]:
    value = json.loads((root / rel).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"expected object at {rel}")
    return value


def _code(value: Any) -> int | None:
    if isinstance(value, Mapping):
        code = value.get("code")
        if isinstance(code, int) and not isinstance(code, bool) and code >= 0:
            return code
    if isinstance(value, int) and not isinstance(value, bool) and value >= 0:
        return value
    return None


def _certificate_component_valid(cert: Mapping[str, Any], lane: str) -> bool:
    audit = cert.get("audit", {})
    if not isinstance(audit, Mapping):
        audit = {}
    if lane == "source-package" or lane == "target-package":
        return audit.get("integrated_package_valid") is True
    if lane == "staged":
        return audit.get("staged_assembly_valid") is True
    if lane == "corridor":
        return audit.get("strict_corridor_valid") is True
    if lane == "autonomy":
        return audit.get("autonomy_valid") is True
    raise ValueError(lane)


def _model_ref(cert: Mapping[str, Any], lane: str) -> str | None:
    if lane in {"source-package", "target-package", "corridor", "autonomy"}:
        value = cert.get("model_ref")
        return value if isinstance(value, str) else None
    return None


def _clause_assignment(model: Mapping[str, Any], clause: str) -> Mapping[str, Any]:
    rows = model.get("clauses", [])
    if isinstance(rows, list):
        for row in rows:
            if isinstance(row, Mapping) and row.get("clause") == clause:
                assignment = row.get("assignment", {})
                return assignment if isinstance(assignment, Mapping) else {}
    return {}


@dataclass(frozen=True)
class FIACHAudit:
    certificate_id: str
    component_hashes_valid: bool
    source_package_valid: bool
    staged_preservation_valid: bool
    target_package_valid: bool
    corridor_valid: bool
    autonomy_valid: bool
    source_target_distinct: bool
    source_endpoints_linked: bool
    target_endpoints_linked: bool
    staged_models_linked: bool
    corridor_package_temporal_frontier_linked: bool
    corridor_autonomy_handoff_linked: bool
    autonomy_package_contract_linked: bool
    route_status_linked: bool
    structural_transport_lane: bool
    structural_realization_lane: bool
    structural_lineage_lane: bool
    autonomy_lane: bool
    recognition_separate: bool
    ontology_absent: bool
    aggregate_valid: bool
    failed_obligations: tuple[str, ...]
    component_statuses: Mapping[str, bool]

    def to_dict(self) -> dict[str, Any]:
        payload = asdict(self)
        payload["component_statuses"] = dict(sorted(self.component_statuses.items()))
        return json.loads(json.dumps(payload, sort_keys=True))


def audit_temporal_fiach(spec: Mapping[str, Any], root: Path) -> FIACHAudit:
    refs = spec.get("component_refs", {})
    hashes = spec.get("component_sha256", {})
    if not isinstance(refs, Mapping):
        refs = {}
    if not isinstance(hashes, Mapping):
        hashes = {}
    required = ("source_package", "staged_assembly", "target_package", "corridor", "autonomy")
    certs: dict[str, dict[str, Any]] = {}
    hash_checks: list[bool] = []
    for key in required:
        rel = refs.get(key)
        if not isinstance(rel, str) or not (root / rel).is_file():
            certs[key] = {}
            hash_checks.append(False)
            continue
        certs[key] = _load(root, rel)
        hash_checks.append(hashes.get(key) == sha256(root / rel))

    source_package_valid = _certificate_component_valid(certs["source_package"], "source-package")
    staged_valid = _certificate_component_valid(certs["staged_assembly"], "staged")
    target_package_valid = _certificate_component_valid(certs["target_package"], "target-package")
    corridor_valid = _certificate_component_valid(certs["corridor"], "corridor")
    autonomy_valid = _certificate_component_valid(certs["autonomy"], "autonomy")

    source_code = _code(spec.get("source"))
    target_code = _code(spec.get("target"))
    source_target_distinct = source_code is not None and target_code is not None and source_code != target_code

    models: dict[str, dict[str, Any]] = {}
    for key, lane in (
        ("source_package", "source-package"),
        ("target_package", "target-package"),
        ("corridor", "corridor"),
        ("autonomy", "autonomy"),
    ):
        rel = _model_ref(certs[key], lane)
        models[key] = _load(root, rel) if isinstance(rel, str) and (root / rel).is_file() else {}
    staged_cert = certs["staged_assembly"]
    staged_assembly_ref = staged_cert.get("assembly_ref")
    staged_model = _load(root, staged_assembly_ref) if isinstance(staged_assembly_ref, str) and (root / staged_assembly_ref).is_file() else {}

    source_endpoints_linked = bool(
        source_code is not None
        and _code(models["source_package"].get("target")) == source_code
        and _code(models["corridor"].get("carrier_chain", [{}])[0] if isinstance(models["corridor"].get("carrier_chain"), list) and models["corridor"].get("carrier_chain") else None) == source_code
        and _code(models["autonomy"].get("source")) == source_code
    )
    chain = models["corridor"].get("carrier_chain", [])
    corridor_target = _code(chain[-1]) if isinstance(chain, list) and chain else None
    target_endpoints_linked = bool(
        target_code is not None
        and _code(models["target_package"].get("target")) == target_code
        and corridor_target == target_code
        and _code(models["autonomy"].get("target")) == target_code
    )

    staged_models_linked = bool(
        isinstance(staged_cert.get("source_model_ref"), str)
        and isinstance(staged_cert.get("target_model_ref"), str)
        and staged_cert.get("source_model_ref") == certs["source_package"].get("model_ref")
        and staged_cert.get("target_model_ref") == certs["target_package"].get("model_ref")
        and staged_model.get("assembly_id") == staged_cert.get("certificate_id")
    )

    stages = models["corridor"].get("episode", {}).get("stages", []) if isinstance(models["corridor"].get("episode"), Mapping) else []
    final_stage = stages[-1] if isinstance(stages, list) and stages else {}
    final_signature = final_stage.get("signature", {}) if isinstance(final_stage, Mapping) else {}
    c6 = _clause_assignment(models["target_package"], "C6_TEMPORAL_CLOSURE")
    corridor_package_linked = bool(
        isinstance(final_signature, Mapping)
        and c6.get("route_residue") == final_signature.get("route_residue")
        and c6.get("record_before") == final_signature.get("record_value")
        and c6.get("tick_phase") == final_signature.get("tick_index")
        and c6.get("maintenance_owner") == final_signature.get("maintenance_owner")
    )

    events = models["corridor"].get("episode", {}).get("events", []) if isinstance(models["corridor"].get("episode"), Mapping) else []
    final_event_ids = sorted(
        str(row.get("event_id"))
        for row in events
        if isinstance(row, Mapping)
        and row.get("stage") == final_stage.get("stage")
        and _code(row.get("owner")) == target_code
        and isinstance(row.get("event_id"), str)
    )
    autonomy_event = models["autonomy"].get("handoff_endpoint_event_id")
    corridor_autonomy_linked = isinstance(autonomy_event, str) and autonomy_event in final_event_ids

    package_contract = models["autonomy"].get("package_contract", {})
    autonomy_package_linked = bool(
        isinstance(package_contract, Mapping)
        and package_contract.get("package_certificate_ref") == refs.get("target_package")
        and package_contract.get("package_certificate_sha256") == hashes.get("target_package")
    )

    route_status = spec.get("route_status")
    corridor_route = certs["corridor"].get("audit", {}).get("route_status") if isinstance(certs["corridor"].get("audit"), Mapping) else None
    route_status_linked = route_status in {"flat", "route-indexed"} and route_status == corridor_route

    structural_transport = staged_valid
    structural_realization = target_package_valid
    structural_lineage = corridor_valid
    autonomy_lane = autonomy_valid
    recognition_separate = spec.get("recognition_status") in {"not-addressed", "assumed-interface", "externally-audited"}
    forbidden_ontology_keys = {
        "consciousness",
        "phenomenal_continuity",
        "survival",
        "numerical_identity",
        "same_subject",
    }
    ontology_absent = forbidden_ontology_keys.isdisjoint(spec)

    obligations = {
        "FIACH-O01-component-hashes": all(hash_checks),
        "FIACH-O02-source-package": source_package_valid,
        "FIACH-O03-staged-preservation": staged_valid,
        "FIACH-O04-target-package": target_package_valid,
        "FIACH-O05-strict-temporal-lineage": corridor_valid,
        "FIACH-O06-post-withdrawal-autonomy": autonomy_valid,
        "FIACH-O07-distinct-carriers": source_target_distinct,
        "FIACH-O08-source-endpoint-linking": source_endpoints_linked,
        "FIACH-O09-target-endpoint-linking": target_endpoints_linked,
        "FIACH-O10-staged-model-linking": staged_models_linked,
        "FIACH-O11-corridor-package-temporal-frontier": corridor_package_linked,
        "FIACH-O12-corridor-autonomy-handoff": corridor_autonomy_linked,
        "FIACH-O13-autonomy-package-contract": autonomy_package_linked,
        "FIACH-O14-route-status-linking": route_status_linked,
        "FIACH-O15-recognition-separate": recognition_separate,
        "FIACH-O16-ontology-absent": ontology_absent,
    }
    failed = tuple(name for name, status in obligations.items() if not status)
    statuses = {
        "S-T": structural_transport,
        "S-R": structural_realization,
        "S-L": structural_lineage,
        "A": autonomy_lane,
    }
    return FIACHAudit(
        certificate_id=str(spec.get("certificate_id", "")),
        component_hashes_valid=all(hash_checks),
        source_package_valid=source_package_valid,
        staged_preservation_valid=staged_valid,
        target_package_valid=target_package_valid,
        corridor_valid=corridor_valid,
        autonomy_valid=autonomy_valid,
        source_target_distinct=source_target_distinct,
        source_endpoints_linked=source_endpoints_linked,
        target_endpoints_linked=target_endpoints_linked,
        staged_models_linked=staged_models_linked,
        corridor_package_temporal_frontier_linked=corridor_package_linked,
        corridor_autonomy_handoff_linked=corridor_autonomy_linked,
        autonomy_package_contract_linked=autonomy_package_linked,
        route_status_linked=route_status_linked,
        structural_transport_lane=structural_transport,
        structural_realization_lane=structural_realization,
        structural_lineage_lane=structural_lineage,
        autonomy_lane=autonomy_lane,
        recognition_separate=recognition_separate,
        ontology_absent=ontology_absent,
        aggregate_valid=not failed,
        failed_obligations=failed,
        component_statuses=statuses,
    )


def replay_component_certificates(spec: Mapping[str, Any], root: Path) -> dict[str, bool]:
    """Recompute the positive component audits from their model surfaces."""

    refs = spec.get("component_refs", {})
    if not isinstance(refs, Mapping):
        return {}
    result: dict[str, bool] = {}
    for key in ("source_package", "target_package"):
        cert = _load(root, str(refs[key]))
        model = _load(root, str(cert["model_ref"]))
        result[key] = audit_package(model).to_dict() == cert.get("audit")
    staged = _load(root, str(refs["staged_assembly"]))
    assembly = _load(root, str(staged["assembly_ref"]))
    source_model = _load(root, str(staged["source_model_ref"]))
    target_model = _load(root, str(staged["target_model_ref"]))
    result["staged_assembly"] = audit_staged_assembly(assembly, source_model, target_model).to_dict() == staged.get("audit")
    corridor = _load(root, str(refs["corridor"]))
    corridor_model = _load(root, str(corridor["model_ref"]))
    result["corridor"] = audit_strict_corridor(corridor_model).to_dict() == corridor.get("audit")
    autonomy = _load(root, str(refs["autonomy"]))
    autonomy_model = _load(root, str(autonomy["model_ref"]))
    result["autonomy"] = audit_autonomy(autonomy_model).to_dict() == autonomy.get("audit")
    return result


def lane_truth_table() -> dict[str, Any]:
    rows = []
    for package in (False, True):
        for lineage in (False, True):
            for autonomy in (False, True):
                aggregate = package and lineage and autonomy
                rows.append(
                    {
                        "S-R": package,
                        "S-L": lineage,
                        "A": autonomy,
                        "aggregate": aggregate,
                    }
                )
    return {
        "schema_version": "CST-TT-05",
        "row_count": len(rows),
        "positive_row_count": sum(1 for row in rows if row["aggregate"]),
        "negative_row_count": sum(1 for row in rows if not row["aggregate"]),
        "conjunction_exact": all(row["aggregate"] == (row["S-R"] and row["S-L"] and row["A"]) for row in rows),
        "rows": rows,
    }
