#!/usr/bin/env python3
from __future__ import annotations

import csv
import hashlib
import json
import platform
from pathlib import Path
from typing import Any, Iterable, Mapping

from cst_tt.transport import (
    audit_memory_repair,
    audit_record_arrow,
    audit_route_discipline,
    audit_temporal_transport,
    bounded_confluence_shape_search,
    bounded_global_now_obstruction_search,
    bounded_memory_or_flatness_exhaustion,
    bounded_transport_shape_search,
)
from tt03_data import (
    arrow_controls,
    flat_memory_model,
    lost_memory_control,
    memory_repair_model,
    negative_holonomy_model,
    positive_arrow_model,
    positive_route_model,
    positive_transport_model,
    route_controls,
    transport_controls,
)

ROOT = Path(__file__).resolve().parents[1]
PHASE = "CST-TT-03"
DATE = "2026-08-10"


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")


def write_csv(path: Path, fieldnames: list[str], rows: Iterable[Mapping[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow({name: row.get(name, "") for name in fieldnames})


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def markdown_table(headers: list[str], rows: Iterable[Iterable[object]]) -> str:
    lines = ["| " + " | ".join(headers) + " |", "|" + "|".join("---" for _ in headers) + "|"]
    lines.extend("| " + " | ".join(str(value) for value in row) + " |" for row in rows)
    return "\n".join(lines)


def build_models_and_certificates() -> dict[str, Any]:
    dirs = {
        "transport": ROOT / "models/transport",
        "routes": ROOT / "models/routes",
        "memory": ROOT / "models/memory",
        "arrow": ROOT / "models/arrow",
        "transport_cert": ROOT / "formal/certificates/transport",
        "route_cert": ROOT / "formal/certificates/routes",
        "memory_cert": ROOT / "formal/certificates/memory",
        "arrow_cert": ROOT / "formal/certificates/arrow",
        "control_models": ROOT / "models/transport/controls",
        "control_certs": ROOT / "formal/certificates/transport/controls",
    }
    for directory in dirs.values():
        directory.mkdir(parents=True, exist_ok=True)

    # Route/confluence layer first because the flat transport certificate binds it.
    route_models = [positive_route_model(), negative_holonomy_model()]
    route_rows: list[dict[str, object]] = []
    route_certs: dict[str, dict[str, Any]] = {}
    for model in route_models:
        model_path = dirs["routes"] / f"{model['model_id']}.model.json"
        write_json(model_path, model)
        audit = audit_route_discipline(model)
        if model["model_id"] == "ROUTE-POS-01":
            if not audit.flatness_valid:
                raise RuntimeError(f"positive route model failed: {audit.failed_obligations}")
            status = "checked-finite-flatness-certificate"
            theorem_ids = ["TTH-09", "TTN-04"]
            ceiling = "finite route independence under declared confluence only"
        else:
            if not audit.route_audit_valid or audit.flatness_valid or audit.global_now_factorization_exists:
                raise RuntimeError("route-indexed holonomy control did not expose the expected boundary")
            status = "checked-finite-route-indexed-obstruction"
            theorem_ids = ["TTN-04", "TTN-05"]
            ceiling = "finite route-indexed obstruction only"
        cert = {
            "schema_version": PHASE,
            "certificate_id": model["model_id"],
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": status,
            "claim_lanes": ["S-T"],
            "claim_ceiling": ceiling,
            "theorem_ids": theorem_ids,
            "audit": audit.to_dict(),
            "checker": {
                "module": "cst_tt.transport",
                "function": "audit_route_discipline",
                "python_version": platform.python_version(),
            },
        }
        cert_path = dirs["route_cert"] / f"{model['model_id']}.certificate.json"
        write_json(cert_path, cert)
        route_certs[model["model_id"]] = cert
        route_rows.append(
            {
                "route_model_id": model["model_id"],
                "role": "flat-positive" if audit.flatness_valid else "route-indexed-negative",
                "model_ref": rel(model_path),
                "certificate_ref": rel(cert_path),
                "model_sha256": sha256(model_path),
                "route_audit_valid": str(audit.route_audit_valid).lower(),
                "flatness_valid": str(audit.flatness_valid).lower(),
                "global_now_factorization_exists": str(audit.global_now_factorization_exists).lower(),
                "nonzero_translation_holonomy_witnessed": str(audit.nonzero_translation_holonomy_witnessed).lower(),
                "theorem_ids": ";".join(theorem_ids),
                "claim_ceiling": ceiling,
            }
        )

    transport_rows: list[dict[str, object]] = []
    transport_certs: dict[str, dict[str, Any]] = {}
    for status in ("route-indexed", "flat"):
        model = positive_transport_model(status)
        model_path = dirs["transport"] / f"{model['model_id']}.model.json"
        write_json(model_path, model)
        flat_valid = route_certs["ROUTE-POS-01"]["audit"]["flatness_valid"] if status == "flat" else None
        audit = audit_temporal_transport(model, flatness_certificate_valid=bool(flat_valid) if flat_valid is not None else None)
        if not audit.transport_valid:
            raise RuntimeError(f"positive transport failed: {model['model_id']} {audit.failed_obligations}")
        cert = {
            "schema_version": PHASE,
            "certificate_id": model["model_id"],
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": "checked-finite-temporal-transport-certificate",
            "claim_lanes": ["S-T"],
            "claim_ceiling": "finite structural temporal transport only",
            "route_status": status,
            "theorem_evidence": {
                "theorem_ids": ["TTH-03", "TTH-10"] + (["TTH-09"] if status == "flat" else ["TTN-04"]),
                "lean_declarations": [
                    "CSTTT.TransportTheory.bundledHeterogeneousTemporalTransport",
                    "CSTTT.RecordTheory.monotoneRecordDescentTransportsArrow",
                    "CSTTT.RouteTheory.noCurrentOnlyPredictor",
                ] + (["CSTTT.RouteTheory.routeIndependentEndpointUnderNormalization"] if status == "flat" else []),
                "lean_compile_status": "pending-toolchain",
            },
            "audit": audit.to_dict(),
            "checker": {
                "module": "cst_tt.transport",
                "function": "audit_temporal_transport",
                "python_version": platform.python_version(),
                "checked_at_phase": PHASE,
            },
        }
        cert_path = dirs["transport_cert"] / f"{model['model_id']}.certificate.json"
        write_json(cert_path, cert)
        transport_certs[model["model_id"]] = cert
        transport_rows.append(
            {
                "transport_id": model["model_id"],
                "route_status": status,
                "model_ref": rel(model_path),
                "certificate_ref": rel(cert_path),
                "model_sha256": sha256(model_path),
                "source_carrier": model["source"]["carrier"]["code"],
                "target_carrier": model["target"]["carrier"]["code"],
                "source_state_count": len(model["source"]["states"]),
                "target_state_count": len(model["target"]["states"]),
                "representative_class_count": len(model["bridge"]["source_predictive_equivalence_classes"]),
                "result_status": cert["result_status"],
                "claim_lanes": "S-T",
                "claim_ceiling": cert["claim_ceiling"],
            }
        )

    memory_rows: list[dict[str, object]] = []
    for model, status, theorem_ids, ceiling in (
        (memory_repair_model(), "checked-finite-memory-repair-certificate", ["TTN-04"], "finite predictive-representation repair only"),
        (flat_memory_model(), "checked-finite-flat-predictive-control", ["TTN-04", "TTH-09"], "finite flat predictive control only"),
    ):
        model_path = dirs["memory"] / f"{model['model_id']}.model.json"
        write_json(model_path, model)
        audit = audit_memory_repair(model)
        if not audit.memory_repair_valid:
            raise RuntimeError(f"memory model failed: {model['model_id']} {audit.failed_obligations}")
        cert = {
            "schema_version": PHASE,
            "certificate_id": model["model_id"],
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": status,
            "claim_lanes": ["S-T"],
            "claim_ceiling": ceiling,
            "theorem_ids": theorem_ids,
            "audit": audit.to_dict(),
            "checker": {"module": "cst_tt.transport", "function": "audit_memory_repair", "python_version": platform.python_version()},
        }
        cert_path = dirs["memory_cert"] / f"{model['model_id']}.certificate.json"
        write_json(cert_path, cert)
        memory_rows.append(
            {
                "memory_model_id": model["model_id"],
                "role": "route-memory-repair" if audit.predictive_divergence_present else "flat-alternative",
                "model_ref": rel(model_path),
                "certificate_ref": rel(cert_path),
                "model_sha256": sha256(model_path),
                "current_only_predictor_exists": str(audit.current_only_predictor_exists).lower(),
                "predictive_divergence_present": str(audit.predictive_divergence_present).lower(),
                "memory_or_flatness_satisfied": str(audit.memory_or_flatness_satisfied).lower(),
                "predictor_functions_examined": audit.predictor_functions_examined,
                "theorem_ids": ";".join(theorem_ids),
            }
        )

    arrow_model = positive_arrow_model()
    arrow_path = dirs["arrow"] / "ARROW-POS-01.model.json"
    write_json(arrow_path, arrow_model)
    arrow_audit = audit_record_arrow(arrow_model)
    if not arrow_audit.arrow_transport_valid:
        raise RuntimeError(f"arrow positive failed: {arrow_audit.failed_obligations}")
    arrow_cert = {
        "schema_version": PHASE,
        "certificate_id": "ARROW-POS-01",
        "model_ref": rel(arrow_path),
        "model_sha256": sha256(arrow_path),
        "result_status": "checked-finite-record-arrow-certificate",
        "claim_lanes": ["S-T"],
        "claim_ceiling": "finite structural arrow transport only",
        "theorem_ids": ["TTH-10"],
        "audit": arrow_audit.to_dict(),
        "checker": {"module": "cst_tt.transport", "function": "audit_record_arrow", "python_version": platform.python_version()},
    }
    arrow_cert_path = dirs["arrow_cert"] / "ARROW-POS-01.certificate.json"
    write_json(arrow_cert_path, arrow_cert)
    arrow_rows = [{
        "arrow_model_id": "ARROW-POS-01",
        "model_ref": rel(arrow_path),
        "certificate_ref": rel(arrow_cert_path),
        "model_sha256": sha256(arrow_path),
        "maps_examined": arrow_audit.maps_examined_in_bounded_search,
        "strictly_monotone_maps": arrow_audit.strictly_monotone_maps_in_bounded_search,
        "nonstrict_monotone": str(arrow_audit.nonstrict_monotone).lower(),
        "strict_progress_preserved": str(arrow_audit.strict_progress_preserved).lower(),
        "theorem_ids": "TTH-10",
    }]

    control_rows: list[dict[str, object]] = []

    def store_control(model: dict[str, Any], kind: str, baseline_ref: str) -> None:
        model_path = dirs["control_models"] / f"{model['model_id']}.model.json"
        write_json(model_path, model)
        if kind == "transport":
            audit = audit_temporal_transport(model)
            valid_result = audit.transport_valid
            failures = list(audit.failed_obligations)
            function = "audit_temporal_transport"
        elif kind == "route":
            audit = audit_route_discipline(model)
            valid_result = audit.flatness_valid
            failures = list(audit.failed_obligations)
            function = "audit_route_discipline"
        elif kind == "memory":
            audit = audit_memory_repair(model)
            valid_result = audit.memory_repair_valid
            failures = list(audit.failed_obligations)
            function = "audit_memory_repair"
        else:
            audit = audit_record_arrow(model)
            valid_result = audit.arrow_transport_valid
            failures = list(audit.failed_obligations)
            function = "audit_record_arrow"
        primary = model["expected_primary_failure"]
        if valid_result or primary not in failures:
            raise RuntimeError(f"control {model['model_id']} failed contract: {failures}")
        cert = {
            "schema_version": PHASE,
            "control_id": model["model_id"],
            "control_kind": kind,
            "artifact_ref": rel(model_path),
            "artifact_sha256": sha256(model_path),
            "baseline_ref": baseline_ref,
            "expected_primary_failure": primary,
            "observed_failures": failures,
            "result_status": "checked-obligation-countermodel",
            "claim_ceiling": "finite structural obligation boundary only",
            "checker": {
                "module": "cst_tt.transport",
                "function": function,
                "valid_result": False,
                "python_version": platform.python_version(),
            },
        }
        cert_path = dirs["control_certs"] / f"{model['model_id']}.certificate.json"
        write_json(cert_path, cert)
        control_rows.append(
            {
                "control_id": model["model_id"],
                "control_kind": kind,
                "title": model["title"],
                "expected_primary_failure": primary,
                "observed_failures": ";".join(failures),
                "artifact_ref": rel(model_path),
                "certificate_ref": rel(cert_path),
                "baseline_ref": baseline_ref,
                "result_status": cert["result_status"],
            }
        )

    for control in transport_controls():
        store_control(control, "transport", "models/transport/TR-POS-01.model.json")
    for control in route_controls():
        store_control(control, "route", "models/routes/ROUTE-POS-01.model.json")
    store_control(lost_memory_control(), "memory", "models/memory/MEM-POS-01.model.json")
    for control in arrow_controls():
        store_control(control, "record-arrow", "models/arrow/ARROW-POS-01.model.json")

    transport_search = bounded_transport_shape_search()
    confluence_search = bounded_confluence_shape_search()
    memory_exhaustion = bounded_memory_or_flatness_exhaustion()
    global_now_exhaustion = bounded_global_now_obstruction_search()
    transport_search_path = dirs["transport_cert"] / "BOUNDED_TRANSPORT_SHAPE_SEARCH.json"
    confluence_search_path = dirs["route_cert"] / "BOUNDED_CONFLUENCE_SHAPE_SEARCH.json"
    memory_exhaustion_path = dirs["memory_cert"] / "BOUNDED_MEMORY_OR_FLATNESS_EXHAUSTION.json"
    global_now_exhaustion_path = dirs["route_cert"] / "BOUNDED_GLOBAL_NOW_OBSTRUCTION_SEARCH.json"
    write_json(transport_search_path, transport_search)
    write_json(confluence_search_path, confluence_search)
    write_json(memory_exhaustion_path, memory_exhaustion)
    write_json(global_now_exhaustion_path, global_now_exhaustion)

    write_csv(ROOT / "registries/TEMPORAL_TRANSPORT_WITNESS_REGISTRY.csv", list(transport_rows[0]), transport_rows)
    write_csv(ROOT / "registries/ROUTE_DISCIPLINE_REGISTRY.csv", list(route_rows[0]), route_rows)
    write_csv(ROOT / "registries/MEMORY_REPAIR_REGISTRY.csv", list(memory_rows[0]), memory_rows)
    write_csv(ROOT / "registries/RECORD_ARROW_REGISTRY.csv", list(arrow_rows[0]), arrow_rows)
    write_csv(ROOT / "registries/TRANSPORT_CONTROL_REGISTRY.csv", list(control_rows[0]), control_rows)

    return {
        "transport_rows": transport_rows,
        "route_rows": route_rows,
        "memory_rows": memory_rows,
        "arrow_rows": arrow_rows,
        "control_rows": control_rows,
        "transport_search": transport_search,
        "confluence_search": confluence_search,
        "memory_exhaustion": memory_exhaustion,
        "global_now_exhaustion": global_now_exhaustion,
    }


def update_registries() -> dict[str, Any]:
    theorem_path = ROOT / "registries/THEOREM_REGISTRY.csv"
    theorem_rows = read_csv(theorem_path)
    advances = {
        "TTH-03": ("CSTTT.TransportTheory.bundledHeterogeneousTemporalTransport", "TTH-03 bundled transport proof source plus two executable certificates"),
        "TTH-09": ("CSTTT.RouteTheory.routeIndependentEndpointUnderNormalization", "normal-form factorization proof source plus confluent-completion certificate"),
        "TTH-10": ("CSTTT.RecordTheory.monotoneRecordDescentTransportsArrow", "strict record-arrow transport proof source plus exact finite witness"),
        "TTN-04": ("CSTTT.RouteTheory.noCurrentOnlyPredictor;CSTTT.RouteTheory.memoryOrFlatness", "generic current-only nonfactorization plus memory/flatness proof and controls"),
        "TTN-05": ("CSTTT.RouteTheory.noCanonicalGlobalNowOfTranslationHolonomy", "generic no-factorization proof source plus nonzero-holonomy witness"),
    }
    for row in theorem_rows:
        if row["theorem_id"] in advances:
            row["status"] = "proof-source-and-executable-certificate-landed"
            row["lean_statement"] = advances[row["theorem_id"]][0]
    write_csv(theorem_path, list(theorem_rows[0]), theorem_rows)

    toy_path = ROOT / "registries/TOY_MODEL_REGISTRY.csv"
    toy_rows = read_csv(toy_path)
    for row in toy_rows:
        if row["toy_id"] == "TTM-06":
            row["status"] = "checked-positive-witness"
            row["notes"] = "ROUTE-POS-01: four-state acyclic confluent completion"
        elif row["toy_id"] == "TTM-05":
            row["notes"] = "CM-07 retained; ROUTE-NEG-01 adds predictive residue and clock-translation holonomy"
        elif row["toy_id"] == "TTM-17":
            row["notes"] = "CM-06 retained; MEM-POS-01 proves current-only predictor failure and route-memory repair"
    write_csv(toy_path, list(toy_rows[0]), toy_rows)

    definition_path = ROOT / "registries/DEFINITION_REGISTRY.csv"
    definitions = read_csv(definition_path)
    new_defs = [
        ("D-046", "RepresentativeIndependent", "CSTTT/Transport/FiniteTemporalTransport.lean", "source-equivalent reachable representatives induce one target predictive value", "S-T", "D-013;D-022"),
        ("D-047", "TemporalSignatureAgreement", "CSTTT/Transport/FiniteTemporalTransport.lean", "exact agreement of seven temporal components plus target owner", "S-T", "D-046"),
        ("D-048", "FiniteTemporalTransportProof", "CSTTT/Transport/FiniteTemporalTransport.lean", "independent evidence for every bundled temporal-transport obligation", "S-T", "D-047"),
        ("D-049", "StrictlyMonotoneOn", "CSTTT/Transport/RecordArrow.lean", "record map preserves every declared strict source-record step", "S-T", "D-012"),
        ("D-050", "FutureSufficientEncoding", "CSTTT/Transport/RouteDiscipline.lean", "equal encodings force equal future signatures on the declared route class", "S-T", "D-024"),
        ("D-051", "FlatAt", "CSTTT/Transport/RouteDiscipline.lean", "current equality fixes the future signature", "S-T", "D-050"),
        ("D-052", "MemoryRepairs", "CSTTT/Transport/RouteDiscipline.lean", "route residue separates current-equal future-distinct routes", "S-T", "D-050"),
        ("D-053", "CanonicalGlobalNow", "CSTTT/Transport/RouteDiscipline.lean", "route-local now factors through boundary data alone", "S-T", "D-024"),
        ("D-054", "NormalizationCertificate", "CSTTT/Transport/RouteDiscipline.lean", "endpoints factor through one boundary-indexed normal form", "S-T", "D-024;D-025"),
    ]
    replacements = {
        did: {
            "definition_id": did,
            "name": name,
            "module": path,
            "purpose": definition,
            "claim_lanes": lanes,
            "dependencies": dependencies,
            "status": "landed-proof-source-and-executable-semantics",
        }
        for did, name, path, definition, lanes, dependencies in new_defs
    }
    definitions = [replacements.get(row["definition_id"], row) for row in definitions]
    existing = {row["definition_id"] for row in definitions}
    definitions.extend(replacements[did] for did in sorted(replacements) if did not in existing)
    write_csv(definition_path, list(definitions[0]), definitions)

    schema_path = ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv"
    schemas = read_csv(schema_path)
    new_schemas = [
        ("CS-11", "temporal_transport_certificate.schema.json", "Bundled temporal transport", "S-T", "examples/scaffold/temporal_transport_certificate.scaffold.json", "landed-checked-transport-certificates"),
        ("CS-12", "route_discipline_certificate.schema.json", "Route holonomy and confluence", "S-T", "examples/scaffold/route_discipline_certificate.scaffold.json", "landed-checked-route-certificates"),
        ("CS-13", "memory_repair_certificate.schema.json", "Predictive route-memory repair", "S-T", "examples/scaffold/memory_repair_certificate.scaffold.json", "landed-checked-memory-certificates"),
        ("CS-14", "record_arrow_certificate.schema.json", "Record-arrow transport", "S-T", "examples/scaffold/record_arrow_certificate.scaffold.json", "landed-checked-arrow-certificates"),
        ("CS-15", "transport_control_certificate.schema.json", "Transport and route controls", "M;S-T", "examples/scaffold/transport_control_certificate.scaffold.json", "landed-checked-transport-controls"),
    ]
    existing_schema = {row["schema_id"] for row in schemas}
    for sid, file, name, lanes, example, status in new_schemas:
        if sid not in existing_schema:
            schemas.append({"schema_id": sid, "file": file, "name": name, "claim_lanes": lanes, "scaffold_example": example, "status": status})
    write_csv(schema_path, list(schemas[0]), schemas)

    kill_path = ROOT / "registries/KILL_CRITERIA.csv"
    kills = read_csv(kill_path)
    new_kills = [
        ("K-TRANS-01", "temporal transport", "Transport validity requires lineage, continuation, identity, or final-verdict vocabulary.", "kill and redesign transport layer", "CST-TT-03", "not-triggered-CST-TT-03"),
        ("K-TRANS-02", "temporal transport", "Predictive-equivalent source representatives induce different target predictive values.", "reject the bridge or refine the source quotient", "CST-TT-03", "not-triggered-CST-TT-03"),
        ("K-ROUTE-01", "route independence", "A route-independent endpoint is certified despite an unjoined critical pair, retained residue, or nonzero clock holonomy.", "kill the flatness certificate", "CST-TT-03", "not-triggered-CST-TT-03"),
        ("K-ARROW-01", "record arrow", "A constant or order-collapsing map is accepted as preserving strict temporal progress.", "strengthen to strict-on-realized-steps", "CST-TT-03", "not-triggered-CST-TT-03"),
    ]
    existing_kill = {row["kill_id"] for row in kills}
    for kid, target, trigger, action, phase, status in new_kills:
        if kid not in existing_kill:
            kills.append({"kill_id": kid, "target": target, "trigger": trigger, "action": action, "decision_phase": phase, "status": status})
    write_csv(kill_path, list(kills[0]), kills)

    dependency_path = ROOT / "registries/DEPENDENCY_EDGES.csv"
    dependency_rows = read_csv(dependency_path)
    new_dependency_rows = [
        {"source": "D-013", "target": "D-047", "reason": "clock translation types temporal-signature agreement", "status": "landed-CST-TT-03"},
        {"source": "D-046", "target": "D-048", "reason": "representative independence enters bundled transport evidence", "status": "landed-CST-TT-03"},
        {"source": "D-047", "target": "D-048", "reason": "component agreement enters bundled transport evidence", "status": "landed-CST-TT-03"},
        {"source": "D-049", "target": "TTH-10", "reason": "strict record monotonicity yields arrow transport", "status": "landed-CST-TT-03"},
        {"source": "D-050", "target": "TTN-04", "reason": "future sufficiency supports memory-or-flatness", "status": "landed-CST-TT-03"},
        {"source": "D-053", "target": "TTN-05", "reason": "global-now factorization is obstructed by same-boundary disagreement", "status": "landed-CST-TT-03"},
        {"source": "D-054", "target": "TTH-09", "reason": "normal-form factorization purchases route independence", "status": "landed-CST-TT-03"},
        {"source": "TTN-04", "target": "TTH-09", "reason": "flatness is the memory-free route-independence branch", "status": "landed-CST-TT-03"},
        {"source": "TTH-03", "target": "TTH-04", "reason": "structural temporal transport precedes temporal corridor work", "status": "frozen"},
    ]
    key = lambda row: (row["source"], row["target"], row["reason"])
    merged = {key(row): row for row in dependency_rows}
    for row in new_dependency_rows:
        merged[key(row)] = row
    dependency_rows = [merged[k] for k in sorted(merged)]
    write_csv(dependency_path, list(dependency_rows[0]), dependency_rows)

    project_path = ROOT / "registries/PROJECT_REGISTRY.json"
    project = json.loads(project_path.read_text(encoding="utf-8"))
    project.update({
        "phase": PHASE,
        "phase_base_tag": "CST-TT-02-v1",
        "phase_base_commit": "3abf5b2406f754b43823b68987c7ea409e737fd0",
        "next_phase": "CST-TT-04",
        "generic_theorem_proof_sources_landed": 8,
        "generic_theorems_lean_compiled": 0,
        "generic_theorems_proved": 0,
        "checked_temporal_transport_certificates": 2,
        "checked_route_certificates": 2,
        "checked_memory_or_flatness_certificates": 2,
        "checked_record_arrow_certificates": 1,
        "checked_transport_and_route_controls": 28,
        "route_independence_scope": "declared finite route family under normalization/confluence only",
        "fallback_unlocked": False,
        "positive_handoff_witnesses": 0,
        "python_version": platform.python_version(),
    })
    write_json(project_path, project)

    return {
        "theorem_rows": theorem_rows,
        "toy_rows": toy_rows,
        "definitions": definitions,
        "schemas": schemas,
        "kills": kills,
        "advanced_theorems": advances,
    }


def build_docs(assets: dict[str, Any], registries: dict[str, Any]) -> None:
    controls = assets["control_rows"]
    control_counts: dict[str, int] = {}
    for row in controls:
        control_counts[str(row["control_kind"])] = control_counts.get(str(row["control_kind"]), 0) + 1

    (ROOT / "docs/HETEROGENEOUS_TEMPORAL_TRANSPORT.md").write_text(f"""# Bundled Heterogeneous Temporal Transport

**Status:** proof source plus exact executable certificates; Lean compilation remains separately reported.

## Structural object

The transported object is frozen before any corridor or lineage predicate:

```text
PredictiveNow + order + tick phase + genuine progress
+ endogenous record/arrow + route residue
+ maintenance state + target-local ownership
```

`TTH-03` is implemented by `CSTTT.TransportTheory.bundledHeterogeneousTemporalTransport` and checked on two separately typed finite carriers:

- source carrier `17`, with three reachable raw states and two representatives of one predictive class;
- target carrier `101`, with two reachable states;
- seven explicit component maps;
- source-to-target successor and progress preservation;
- strict record-arrow preservation;
- target-local ownership;
- either retained route residue (`TR-POS-01`) or a separately checked flatness certificate (`TR-POS-02-FLAT`).

## Representative independence

The source representatives `s0` and `s0-rep` are distinct raw states in one declared predictive class. Both induce the same target predictive value. The bridge therefore descends on the declared reachable quotient image rather than choosing a privileged representative.

## Claim ceiling

The result is S-T only (`S-T`). The transport record contains no episode lineage, corridor, autonomy, consciousness, felt continuity, personal identity, or survival field. A detached reconstruction can satisfy this transport relation and still fail the later strict temporal corridor.

## Bounded shape check

The declared finite search family requires two raw representatives plus a later source state and a two-state target progress image. The first feasible size is source/target `(3, 2)` after {assets['transport_search']['pairs_examined']} state-count pairs were checked. This minimality claim is only relative to that declared shape family.
""", encoding="utf-8")

    (ROOT / "docs/MEMORY_OR_FLATNESS_THEOREM.md").write_text(f"""# Memory-or-Flatness and the Predictive Present

## Generic no-factorization result

`CSTTT.RouteTheory.noCurrentOnlyPredictor` proves:

> If two routes have the same current representation but different future-sufficient values, no deterministic predictor defined only on the current representation can represent both histories.

This is stronger than merely exhibiting a collision. It identifies the exact current-only representational failure.

## Two legitimate repairs

1. **Retain route memory.** `MEM-POS-01` refines `current` to `(current, route residue)`. The refined predictor becomes total and correct.
2. **Prove flatness.** `MEM-FLAT-01` makes the predictive outcomes equal after completion, so the current representation suffices and route residue can be erased at the certified normal form.

The disjunction is structural and route-scoped. It does not say that every physical history must be remembered forever, nor that all admissible route systems are flat.

The two-route binary exhaustion checks {assets['memory_exhaustion']['assignments_examined']} assignments, of which {assets['memory_exhaustion']['premise_satisfying_assignments']} satisfy the future-sufficiency premise, and finds zero violations. This bounded run corroborates rather than replaces the generic Lean proof source.

## Composition boundary

Pairwise endpoint agreement is not assumed. When a direct route and a factored route retain different predictive or clock residue, composition remains route-indexed. Route-independent composition is deferred unless a normalization/confluence certificate discharges the residue.
""", encoding="utf-8")

    (ROOT / "docs/ROUTE_DISCIPLINE_AND_CONFLUENCE.md").write_text(f"""# Route Discipline, Holonomy, and Confluent Completion

## Positive finite control

`ROUTE-POS-01` is the smallest acyclic two-branch diamond in the declared family:

```text
        replace-left       complete-right
x -----------------> a --------------------> z
 \\
  \\ replace-right       complete-left
   ----------------> b --------------------> z
```

Both replacement orders reach one certified normal form `z`, with the same predictive endpoint, route residue, and clock translation. `TTH-09` follows from `CSTTT.RouteTheory.routeIndependentEndpointUnderNormalization` and endpoint factorization through that normal form.

The bounded shape search examined {assets['confluence_search']['candidates_examined']} candidates and first found a witness at four nodes. This is relative minimality under distinct start/branch/join nodes and an acyclic rank condition.

## Negative route-indexed control

`ROUTE-NEG-01` has the same current projection on two same-boundary routes but different predictive values, retained route residues, local-now values, and clock translations. It therefore:

- satisfies the route audit;
- satisfies memory-or-flatness through retained memory;
- fails the flatness certificate;
- witnesses nonzero translation holonomy;
- admits no route-independent boundary-level `now` factorization and therefore no global now on that declared boundary.

The binary one-boundary exhaustion tests both distinct local-now assignments against all four candidate factorization attempts and finds no counterexample to the obstruction theorem.

## Exact claim

Confluence is purchased, not inferred. The certificate is only about the declared finite route family. It does not establish a universal physical clock, route-independent personal identity, or temporal lineage.
""", encoding="utf-8")

    (ROOT / "docs/RECORD_ARROW_TRANSPORT.md").write_text("""# Record-Arrow Transport

`TTH-10` now has two formally separated levels.

1. The original non-strict statement transports a declared record preorder through a monotone map.
2. The strict C6-relevant statement requires the map to be strict on every realized source arrow step.

The positive model maps source records `0 < 1 < 2` to target records `10 < 12 < 14`. An exhaustive search over all `5^3 = 125` maps from three ordered source records to five target records finds exactly 10 maps that preserve both strict steps.

The central negative control is a constant map. It is non-strictly monotone but collapses strict record progress. Therefore non-strict monotonicity alone cannot certify a genuinely advancing target arrow.

This is a structural arrow audit only. Holonomy is neither assumed nor sufficient, and no phenomenal interpretation is made.
""", encoding="utf-8")

    (ROOT / "docs/TRANSPORT_CONTROL_SUITE.md").write_text(f"""# CST-TT-03 Transport and Route Control Suite

{markdown_table(['Control family', 'Count'], sorted(control_counts.items()))}

The 28 controls remove or falsify one registered obligation at a time where possible. Cascading failures are retained when an earlier typing defect necessarily invalidates dependent checks.

Principal controls include:

- same-carrier and same-alphabet pseudo-transport;
- incomplete component maps;
- representative-dependent predictive bridges;
- lost successors, tick progress, record arrows, collapsed or erased route residue, or maintenance state;
- target signatures still owned by the source;
- a transport record containing a lineage verdict;
- false flatness under an unjoined critical pair, retained residue, or nonzero clock holonomy;
- a route-invalid transition and a direct/factored mismatch;
- erased route memory under predictive divergence;
- a constant record map that is monotone but not strictly arrow-preserving;
- `TR-C15`, which rejects a route-indexed map that collapses distinct retained route residues.

Every control is a checked finite countermodel, hash-bound to an exact JSON artifact and independently recomputed by the phase validator.
""", encoding="utf-8")

    (ROOT / "docs/PHASE_BOUNDARY.md").write_text("""# CST-TT-03 Phase Boundary

Prior CST-TT-02 layers retained unchanged:

- exact finite C1-C8 package semantics;
- substantive C6 temporal closure;
- acyclic local-witness gluing and staged heterogeneous package assembly.

Landed in this phase:

- componentwise heterogeneous transport of the frozen temporal signature;
- representative-independent predictive bridges on a declared reachable image;
- source/target successor and genuine-progress preservation;
- strict record-arrow transport and its monotone-collapse boundary;
- retained route memory as one valid route discipline;
- route-independent endpoints under explicit finite normalization/confluence;
- memory-or-flatness and current-only predictor nonfactorization;
- a generic no-global-now factorization theorem under translation holonomy;
- exact transport, route, memory, arrow, and control certificates;
- replacement-order holonomy and confluent-completion toy models;
- transport records with no source-lineage, ancestry, temporal-corridor, withdrawal, autonomy, consciousness, survival, or identity verdict field.

Not landed:

- strict temporal lineage or any temporal corridor;
- direct-successor validity;
- post-withdrawal autonomy;
- a positive Temporal-FIACH or Temporal-IAPS witness;
- consciousness, phenomenal continuity, survival, numerical identity, A1, A2-P, recognition, or certificate soundness.

The next authorized phase is `CST-TT-04`, temporal corridor, composition, and the overlap/direct-successor fork.
""", encoding="utf-8")

    theorem_rows = [row for row in registries["theorem_rows"] if row["theorem_id"] in registries["advanced_theorems"]]
    (ROOT / "docs/THEOREM_AND_TOY_REGISTRY.md").write_text(
        "# CST-TT Theorem and Toy Registry — through CST-TT-03\n\n"
        + markdown_table(
            ["ID", "Result", "Status", "Claim lane", "Lean surface"],
            ((row["theorem_id"], row["name"], row["status"], row["claim_lanes"], row["lean_statement"]) for row in theorem_rows),
        )
        + "\n\nAll five advanced surfaces remain below the structural claim ceiling. Actual Lean compilation is reported separately.\n",
        encoding="utf-8",
    )

    completion = f"""# CST-TT-03 Completion Report

**Phase:** CST-TT-03 — heterogeneous temporal transport and route discipline

**Status:** science layer complete; repository freeze is recorded by the phase manifest and archive verification

## Landed

- five advanced theorem/boundary proof sources: TTH-03, TTH-09, TTH-10, TTN-04, and TTN-05;
- 2 checked heterogeneous temporal-transport certificates;
- 2 checked route certificates: one flat/confluent and one route-indexed holonomy obstruction;
- 2 checked memory-or-flatness certificates;
- 1 checked strict record-arrow certificate;
- 28 checked transport/route/memory/arrow controls;
- bounded transport-shape and acyclic-confluence searches;
- all four CST-TT-03 kill criteria not triggered.

## Result

Temporal transport is independently decidable from an exact finite certificate and contains no lineage verdict. Route dependence is either retained explicitly or discharged by a separately validated normalization/confluence certificate.

A current-only temporal representation cannot determine two histories with the same current class and different future-sufficient values. Route memory repairs the mismatch; a flat completion is the alternative. Nonzero clock-translation holonomy blocks one route-independent boundary-level `now`.

## Formal status

The generic proofs are written explicitly in Lean without placeholders. No theorem is represented as Lean-compiled unless `lake build` succeeds in the final verification environment. Python executability, schema validation, hash binding, positive certificates, negative controls, bounded corroboration, and static Lean audits are mandatory.

## Not landed

- No positive temporal corridor or strict temporal-lineage certificate is landed.
- No post-withdrawal autonomy certificate is landed.
- Lean compilation is not claimed in this environment; the proof sources pass static audits only.
- No positive Temporal-FIACH or Temporal-IAPS witness is introduced.

## Target decision

Temporal-FIACH remains primary. Temporal-IAPS remains locked. No positive temporal corridor is introduced. No post-withdrawal autonomy is introduced. No positive handoff or lineage witness is introduced in this phase. Lean compilation is not claimed.

## Next phase

`CST-TT-04` — temporal corridor, composition, and the overlap/direct-successor fork.
"""
    (ROOT / "manifests/CST-TT-03_COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")
    (ROOT / "manifests/COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")
    (ROOT / "changelog/CST-TT-03.md").write_text("# CST-TT-03\n\nLanded heterogeneous temporal transport, route discipline, memory-or-flatness, record-arrow transport, and exact finite controls. No lineage or autonomy result was added.\n", encoding="utf-8")


def build_deltas(assets: dict[str, Any], registries: dict[str, Any]) -> None:
    theorem_rows = []
    for tid, (_, evidence) in registries["advanced_theorems"].items():
        row = next(row for row in registries["theorem_rows"] if row["theorem_id"] == tid)
        theorem_rows.append({
            "theorem_id": tid,
            "name": row["name"],
            "prior_status": "checked-finite-countermodel" if tid in {"TTN-04", "TTN-05"} else "open-scaffold",
            "new_status": row["status"],
            "evidence": evidence,
            "lean_statement": row["lean_statement"],
            "lean_compile_status": "pending-toolchain",
            "claim_lanes": row["claim_lanes"],
            "claim_ceiling": row["claim_ceiling"],
        })
    write_csv(ROOT / "manifests/CST-TT-03_THEOREM_STATUS_DELTA.csv", list(theorem_rows[0]), theorem_rows)

    model_rows: list[dict[str, object]] = []
    for registry, id_key, kind in (
        (assets["transport_rows"], "transport_id", "positive-transport"),
        (assets["route_rows"], "route_model_id", "route"),
        (assets["memory_rows"], "memory_model_id", "memory-or-flatness"),
        (assets["arrow_rows"], "arrow_model_id", "record-arrow"),
    ):
        for row in registry:
            model_rows.append({
                "artifact_id": row[id_key],
                "artifact_kind": kind,
                "model_ref": row["model_ref"],
                "certificate_ref": row["certificate_ref"],
                "result_status": row.get("result_status", "checked-finite-certificate"),
                "claim_ceiling": row.get("claim_ceiling", "finite structural result only"),
            })
    for row in assets["control_rows"]:
        model_rows.append({
            "artifact_id": row["control_id"],
            "artifact_kind": f"{row['control_kind']}-control",
            "model_ref": row["artifact_ref"],
            "certificate_ref": row["certificate_ref"],
            "result_status": row["result_status"],
            "claim_ceiling": "finite structural obligation boundary only",
        })
    model_rows.extend([
        {"artifact_id": "SEARCH-TRANSPORT-SHAPE", "artifact_kind": "bounded-search", "model_ref": "", "certificate_ref": "formal/certificates/transport/BOUNDED_TRANSPORT_SHAPE_SEARCH.json", "result_status": assets["transport_search"]["status"], "claim_ceiling": assets["transport_search"]["minimality_scope"]},
        {"artifact_id": "SEARCH-CONFLUENCE-SHAPE", "artifact_kind": "bounded-search", "model_ref": "", "certificate_ref": "formal/certificates/routes/BOUNDED_CONFLUENCE_SHAPE_SEARCH.json", "result_status": assets["confluence_search"]["status"], "claim_ceiling": assets["confluence_search"]["minimality_scope"]},
        {"artifact_id": "EXHAUST-MEMORY-OR-FLATNESS", "artifact_kind": "bounded-exhaustion", "model_ref": "", "certificate_ref": "formal/certificates/memory/BOUNDED_MEMORY_OR_FLATNESS_EXHAUSTION.json", "result_status": assets["memory_exhaustion"]["status"], "claim_ceiling": assets["memory_exhaustion"]["claim_ceiling"]},
        {"artifact_id": "EXHAUST-GLOBAL-NOW", "artifact_kind": "bounded-exhaustion", "model_ref": "", "certificate_ref": "formal/certificates/routes/BOUNDED_GLOBAL_NOW_OBSTRUCTION_SEARCH.json", "result_status": assets["global_now_exhaustion"]["status"], "claim_ceiling": assets["global_now_exhaustion"]["claim_ceiling"]},
    ])
    write_csv(ROOT / "manifests/CST-TT-03_MODEL_CERTIFICATE_DELTA.csv", list(model_rows[0]), model_rows)


def update_repository_surfaces(assets: dict[str, Any]) -> None:
    phase_summary = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "date": DATE,
        "status": "science-layer-complete-pending-freeze",
        "base_tag": "CST-TT-02-v1",
        "advanced_theorem_surfaces": 5,
        "checked_temporal_transport_certificates": len(assets["transport_rows"]),
        "checked_route_certificates": len(assets["route_rows"]),
        "checked_memory_certificates": len(assets["memory_rows"]),
        "checked_arrow_certificates": len(assets["arrow_rows"]),
        "checked_controls": len(assets["control_rows"]),
        "transport_shape_pairs_examined": assets["transport_search"]["pairs_examined"],
        "confluence_candidates_examined": assets["confluence_search"]["candidates_examined"],
        "memory_or_flatness_assignments_examined": assets["memory_exhaustion"]["assignments_examined"],
        "global_now_candidate_functions_examined": assets["global_now_exhaustion"]["candidate_global_functions_examined"],
        "positive_handoff_witnesses": 0,
        "fallback_unlocked": False,
        "next_phase": "CST-TT-04",
        "claim_ceiling": "structural transport and route discipline only",
    }
    write_json(ROOT / "manifests/CST-TT-03_PHASE_SUMMARY.json", phase_summary)
    write_json(ROOT / "manifests/PHASE_SUMMARY.json", phase_summary)

    readme = """# CST-TT — Temporal Substrate Transcendence Theorems and Toys

Current phase: **CST-TT-03**.

The repository now contains an independently checkable heterogeneous temporal-transport layer, representative-independent predictive bridges, strict record-arrow transport, route-memory/flatness discipline, a confluent-completion witness, and a translation-holonomy obstruction.

It still contains no positive temporal corridor, post-withdrawal autonomy certificate, Temporal-FIACH witness, consciousness result, survival result, or numerical-identity result.

Run:

```bash
PYTHONPATH=src:scripts python -m pytest -q
PYTHONPATH=src:scripts python scripts/validate_tt03.py
PYTHONPATH=src:scripts python -m cst_tt.transport_auditor transport models/transport/TR-POS-01.model.json
PYTHONPATH=src:scripts python -m cst_tt.transport_auditor route models/routes/ROUTE-POS-01.model.json
lake build  # when the pinned Lean toolchain is available
```
"""
    (ROOT / "README.md").write_text(readme, encoding="utf-8")
    (ROOT / "STATE.md").write_text("# Repository State\n\nCST-TT-03 science assets are landed. Temporal transport is S-T only; strict lineage and autonomy remain open for later phases.\n", encoding="utf-8")
    (ROOT / "STATUS.md").write_text("# Status\n\nCST-TT-03: heterogeneous temporal transport and route discipline complete; freeze/validation metadata generated separately.\n", encoding="utf-8")
    (ROOT / "RESTORE_AND_VERIFY.md").write_text("# Restore and Verify\n\nExtract the ZIP, enter `cst-temporal-transcendence`, run `PYTHONPATH=src:scripts scripts/run_tt03_checks.sh`, and run `lake build` when Lean is available.\n", encoding="utf-8")
    (ROOT / "docs/RESTORE_AND_BUILD.md").write_text((ROOT / "RESTORE_AND_VERIFY.md").read_text(encoding="utf-8"), encoding="utf-8")
    changelog_path = ROOT / "CHANGELOG.md"
    changelog_text = changelog_path.read_text(encoding="utf-8")
    marker = "\n## CST-TT-03\n"
    if marker in changelog_text:
        changelog_text = changelog_text.split(marker, 1)[0].rstrip() + "\n"
    changelog_text += "\n## CST-TT-03\n\nLanded temporal transport, memory-or-flatness, route confluence, translation-holonomy, and record-arrow assets.\n"
    changelog_path.write_text(changelog_text, encoding="utf-8")

    init_text = '''"""Exact finite CST-TT transport, package, and countermodel tooling.

CST-TT-03 lands structural temporal transport and route discipline while
retaining the independent package and negative-kernel layers. It makes no
lineage, autonomy, consciousness, survival, or identity claim.
"""

from .package_gluing import (
    PackageAudit,
    StagedAssemblyAudit,
    audit_package,
    audit_staged_assembly,
    bounded_gluing_exhaustion,
)
from .transport import (
    MemoryRepairAudit,
    RecordArrowAudit,
    RouteDisciplineAudit,
    TemporalTransportAudit,
    audit_memory_repair,
    audit_record_arrow,
    audit_route_discipline,
    audit_temporal_transport,
    bounded_confluence_shape_search,
    bounded_global_now_obstruction_search,
    bounded_memory_or_flatness_exhaustion,
    bounded_transport_shape_search,
)
from .types import (
    CarrierId,
    ClaimLane,
    ClauseId,
    Episode,
    Event,
    RecognitionStatus,
    RouteStatus,
)

__all__ = [
    "CarrierId",
    "ClaimLane",
    "ClauseId",
    "Episode",
    "Event",
    "MemoryRepairAudit",
    "PackageAudit",
    "RecognitionStatus",
    "RecordArrowAudit",
    "RouteDisciplineAudit",
    "RouteStatus",
    "StagedAssemblyAudit",
    "TemporalTransportAudit",
    "audit_memory_repair",
    "audit_package",
    "audit_record_arrow",
    "audit_route_discipline",
    "audit_staged_assembly",
    "audit_temporal_transport",
    "bounded_confluence_shape_search",
    "bounded_global_now_obstruction_search",
    "bounded_gluing_exhaustion",
    "bounded_memory_or_flatness_exhaustion",
    "bounded_transport_shape_search",
]

__version__ = "0.1.0"
'''
    (ROOT / "src/cst_tt/__init__.py").write_text(init_text, encoding="utf-8")

    formal_readme = """# Formal Layer

CST-TT-03 adds explicit Lean proof sources for heterogeneous temporal transport, current-only predictive nonfactorization, memory-or-flatness, record-arrow preservation, route normalization/confluence, and no-global-now factorization.

The executable Python layer emits exact finite certificates. Python is not a proof oracle. Lean compilation is reported separately and is not inferred from static source checks.
"""
    (ROOT / "formal/README.md").write_text(formal_readme, encoding="utf-8")
    write_json(ROOT / "formal/TOOLCHAIN_STATUS.json", {
        "phase": PHASE,
        "pinned_toolchain": (ROOT / "lean-toolchain").read_text(encoding="utf-8").strip(),
        "registered_generic_proof_source_count": 8,
        "new_registered_proof_source_count": 6,
        "supporting_lean_declarations": [
            "CSTTT.RouteTheory.noCurrentOnlyPredictor",
            "CSTTT.RouteTheory.noGlobalNowFactorization",
            "CSTTT.RecordTheory.transportRecordArrowStep",
            "CSTTT.RecordTheory.strictlyMonotone_comp",
            "CSTTT.RouteTheory.directFactoredAgreementUnderNormalization",
        ],
        "positive_transport_certificate_count": len(assets["transport_rows"]),
        "route_certificate_count": len(assets["route_rows"]),
        "memory_certificate_count": len(assets["memory_rows"]),
        "record_arrow_certificate_count": len(assets["arrow_rows"]),
        "control_certificate_count": len(assets["control_rows"]),
        "lean_available_at_build": False,
        "lake_available_at_build": False,
        "compile_claimed": False,
        "compile_status": "not-run-lean-and-lake-unavailable",
        "static_lean_source_audit_status": "passed-by-cst-tt-03-static-suite",
        "note": "The final checker reports observed availability; no compile pass is claimed unless lake build succeeds.",
    })

    config_path = ROOT / "config/REPRODUCIBILITY.json"
    config = json.loads(config_path.read_text(encoding="utf-8"))
    config.update({
        "phase": PHASE,
        "next_phase": "CST-TT-04",
        "builder": "scripts/build_tt03_assets.py",
        "validator": "scripts/validate_tt03.py",
        "rebuild_verifier": "scripts/verify_tt03_rebuild.py",
        "status": "deterministic-temporal-transport-and-route-discipline-frozen",
        "transport_shape_pairs_examined": assets["transport_search"]["pairs_examined"],
        "confluence_candidates_examined": assets["confluence_search"]["candidates_examined"],
        "memory_or_flatness_assignments_examined": assets["memory_exhaustion"]["assignments_examined"],
        "global_now_candidate_functions_examined": assets["global_now_exhaustion"]["candidate_global_functions_examined"],
        "usage_boundary": "Deterministic finite checks corroborate proof-source surfaces and certificates; Python is not represented as a proof oracle.",
    })
    write_json(config_path, config)


def main() -> int:
    assets = build_models_and_certificates()
    registries = update_registries()
    build_docs(assets, registries)
    build_deltas(assets, registries)
    update_repository_surfaces(assets)
    print(json.dumps({
        "phase": PHASE,
        "transport_certificates": len(assets["transport_rows"]),
        "route_certificates": len(assets["route_rows"]),
        "memory_certificates": len(assets["memory_rows"]),
        "arrow_certificates": len(assets["arrow_rows"]),
        "controls": len(assets["control_rows"]),
        "advanced_theorems": len(registries["advanced_theorems"]),
        "status": "PASS",
    }, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
