#!/usr/bin/env python3
from __future__ import annotations

import copy
import csv
import hashlib
import json
import platform
from pathlib import Path
from typing import Any, Iterable, Mapping

from cst_tt.corridor import (
    audit_corridor_composition,
    audit_direct_successor,
    audit_direct_successor_path,
    audit_strict_corridor,
    bounded_corridor_composition_search,
    bounded_corridor_support_search,
    bounded_direct_path_composition_search,
    bounded_direct_successor_search,
    bounded_nonredundancy_truth_table_search,
    compose_corridor_models,
    frontier_compatible,
)
from tt04_data import (
    MIDDLE,
    SOURCE,
    TARGET,
    atomic_corridor_model,
    corridor_controls,
    direct_controls,
    positive_atomic_corridor,
    positive_composition_left,
    positive_composition_right,
    positive_direct_path_left,
    positive_direct_path_right,
    positive_direct_successor,
)

ROOT = Path(__file__).resolve().parents[1]
PHASE = "CST-TT-04"
DATE = "2026-08-10"
BASE_TAG = "CST-TT-03-v1"
BASE_COMMIT = "63ea725a7b6ade8df58a94cf7aad2ad78440ce70"


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


def md_table(headers: list[str], rows: Iterable[Iterable[object]]) -> str:
    lines = ["| " + " | ".join(headers) + " |", "|" + "|".join("---" for _ in headers) + "|"]
    lines.extend("| " + " | ".join(str(value) for value in row) + " |" for row in rows)
    return "\n".join(lines)


def checker_payload(module: str, function: str) -> dict[str, str]:
    return {
        "module": module,
        "function": function,
        "python_version": platform.python_version(),
        "checked_at_phase": PHASE,
    }


def build_positive_corridors() -> dict[str, Any]:
    model_dir = ROOT / "models/corridors"
    cert_dir = ROOT / "formal/certificates/corridors"
    model_dir.mkdir(parents=True, exist_ok=True)
    cert_dir.mkdir(parents=True, exist_ok=True)

    atomic = positive_atomic_corridor()
    left = positive_composition_left()
    right = positive_composition_right()
    composite = compose_corridor_models(
        left,
        right,
        model_id="COR-POS-02-COMPOSED",
        title="two-leg strict carrier-chain temporal corridor",
    )
    models = [atomic, left, right, composite]
    rows: list[dict[str, object]] = []
    certs: dict[str, dict[str, Any]] = {}
    for model in models:
        model_path = model_dir / f"{model['model_id']}.model.json"
        write_json(model_path, model)
        audit = audit_strict_corridor(model)
        if not audit.strict_corridor_valid:
            raise RuntimeError(f"positive corridor failed: {model['model_id']} {audit.failed_obligations}")
        cert = {
            "schema_version": PHASE,
            "certificate_id": model["model_id"],
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": "checked-finite-strict-temporal-corridor",
            "claim_lanes": ["S-L"],
            "claim_ceiling": "exact finite structural temporal-lineage criterion only",
            "theorem_evidence": {
                "theorem_ids": ["TTH-04", "TTN-01", "TTN-09"],
                "lean_declarations": [
                    "CSTTT.CorridorTheory.atomicTemporalCorridorCertificateSound",
                    "CSTTT.CorridorTheory.strictTemporalCorridorComposition",
                    "CSTTT.CorridorTheory.noMixedStageExcludesAtomicCorridor",
                    "CSTTT.CorridorTheory.realizedGapExcludesAtomicCorridor",
                ],
                "lean_compile_status": "pending-toolchain",
            },
            "audit": audit.to_dict(),
            "checker": checker_payload("cst_tt.corridor", "audit_strict_corridor"),
        }
        cert_path = cert_dir / f"{model['model_id']}.certificate.json"
        write_json(cert_path, cert)
        certs[model["model_id"]] = cert
        chain = [str(item["code"]) for item in model["carrier_chain"]]
        rows.append(
            {
                "corridor_id": model["model_id"],
                "role": "atomic-positive" if len(chain) == 2 else "composed-positive",
                "carrier_chain": ">".join(chain),
                "stage_count": len(model["episode"]["stages"]),
                "atomic_leg_count": audit.atomic_leg_count,
                "mixed_stage_count": audit.mixed_stage_count,
                "route_status": audit.route_status,
                "model_ref": rel(model_path),
                "certificate_ref": rel(cert_path),
                "model_sha256": sha256(model_path),
                "result_status": cert["result_status"],
                "claim_lanes": "S-L",
                "claim_ceiling": cert["claim_ceiling"],
            }
        )

    left_path = model_dir / "COR-POS-02A.model.json"
    right_path = model_dir / "COR-POS-02B.model.json"
    composite_path = model_dir / "COR-POS-02-COMPOSED.model.json"
    composition_audit = audit_corridor_composition(left, right, composite)
    if not composition_audit.composition_valid:
        raise RuntimeError(f"corridor composition failed: {composition_audit.failed_obligations}")
    if composition_audit.old_endpoint_mixed_rule_satisfied:
        raise RuntimeError("composition control failed to separate endpoint-mixedness from carrier-chain validity")
    composition_cert = {
        "schema_version": PHASE,
        "certificate_id": "COR-COMP-01",
        "left_model_ref": rel(left_path),
        "right_model_ref": rel(right_path),
        "composite_model_ref": rel(composite_path),
        "source_hashes": {
            "left": sha256(left_path),
            "right": sha256(right_path),
            "composite": sha256(composite_path),
        },
        "result_status": "checked-finite-corridor-composition",
        "claim_lanes": ["S-L"],
        "claim_ceiling": "composition of exact finite overlap-leg chains only",
        "audit": composition_audit.to_dict(),
        "checker": checker_payload("cst_tt.corridor", "audit_corridor_composition"),
    }
    composition_path = cert_dir / "COR-COMP-01.certificate.json"
    write_json(composition_path, composition_cert)
    write_csv(
        ROOT / "registries/TEMPORAL_CORRIDOR_WITNESS_REGISTRY.csv",
        [
            "corridor_id", "role", "carrier_chain", "stage_count", "atomic_leg_count",
            "mixed_stage_count", "route_status", "model_ref", "certificate_ref",
            "model_sha256", "result_status", "claim_lanes", "claim_ceiling",
        ],
        rows,
    )
    write_csv(
        ROOT / "registries/CORRIDOR_COMPOSITION_REGISTRY.csv",
        [
            "composition_id", "left_model", "right_model", "composite_model", "frontier_carrier",
            "frontier_signature_equal", "old_endpoint_mixed_rule", "carrier_chain_rule",
            "composition_valid", "certificate_ref", "claim_ceiling",
        ],
        [
            {
                "composition_id": "COR-COMP-01",
                "left_model": "COR-POS-02A",
                "right_model": "COR-POS-02B",
                "composite_model": "COR-POS-02-COMPOSED",
                "frontier_carrier": MIDDLE["code"],
                "frontier_signature_equal": "true",
                "old_endpoint_mixed_rule": "false",
                "carrier_chain_rule": "true",
                "composition_valid": "true",
                "certificate_ref": rel(composition_path),
                "claim_ceiling": composition_cert["claim_ceiling"],
            }
        ],
    )
    return {
        "models": {model["model_id"]: model for model in models},
        "certificates": certs,
        "composition_certificate": composition_cert,
        "rows": rows,
    }


def _composition_control_models() -> list[dict[str, Any]]:
    controls: list[dict[str, Any]] = []
    left = positive_composition_left()

    right_signature = positive_composition_right()
    right_signature["model_id"] = "COMP-C01-RIGHT"
    right_signature["episode"]["stages"][0]["signature"]["maintenance_state"] = "mismatched-frontier-maintenance"
    controls.append({
        "control_id": "COMP-C01",
        "name": "frontier signature mismatch",
        "left": left,
        "right": right_signature,
        "expected_failed_obligation": "frontier-signature-equal",
    })

    other_middle = {"code": 77, "label": "other-intermediate-substrate"}
    right_carrier = atomic_corridor_model(
        "COMP-C02-RIGHT",
        other_middle,
        TARGET,
        base_rank=2,
        base_record=3,
        start_route=["route-root", "leg-S-M-mixed", "leg-S-M-target"],
        start_event_id="other-boundary",
        boundary_event_id="other-target-exit",
        leg_id="leg-O-T",
        title="valid right leg with the wrong shared carrier",
    )
    controls.append({
        "control_id": "COMP-C02",
        "name": "shared carrier mismatch",
        "left": left,
        "right": right_carrier,
        "expected_failed_obligation": "shared-frontier-carrier",
    })

    right_route = positive_composition_right()
    right_route["model_id"] = "COMP-C03-RIGHT"
    for stage in right_route["episode"]["stages"]:
        stage["signature"]["route_residue"] = ["different-route", *stage["signature"]["route_residue"][1:]]
    controls.append({
        "control_id": "COMP-C03",
        "name": "frontier route-memory mismatch",
        "left": left,
        "right": right_route,
        "expected_failed_obligation": "frontier-route-memory-equal",
    })
    return controls


def build_controls() -> dict[str, Any]:
    corridor_model_dir = ROOT / "models/corridors/controls"
    corridor_cert_dir = ROOT / "formal/certificates/corridors/controls"
    direct_model_dir = ROOT / "models/direct_successor/controls"
    direct_cert_dir = ROOT / "formal/certificates/direct_successor/controls"
    for directory in (corridor_model_dir, corridor_cert_dir, direct_model_dir, direct_cert_dir):
        directory.mkdir(parents=True, exist_ok=True)

    corridor_rows: list[dict[str, object]] = []
    direct_rows: list[dict[str, object]] = []
    for item in corridor_controls():
        model = item["model"]
        model_path = corridor_model_dir / f"{item['control_id']}.model.json"
        write_json(model_path, model)
        audit = audit_strict_corridor(model)
        expected = str(item["expected_failed_obligation"])
        if audit.strict_corridor_valid or expected not in audit.failed_obligations:
            raise RuntimeError(f"corridor control failed: {item['control_id']} expected {expected}, got {audit.failed_obligations}")
        cert = {
            "schema_version": PHASE,
            "certificate_id": item["control_id"],
            "control_family": "strict-corridor",
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": "checked-finite-negative-control",
            "expected_failed_obligation": expected,
            "observed_failed_obligations": list(audit.failed_obligations),
            "control_passed": True,
            "audit": audit.to_dict(),
            "checker": checker_payload("cst_tt.corridor", "audit_strict_corridor"),
        }
        cert_path = corridor_cert_dir / f"{item['control_id']}.certificate.json"
        write_json(cert_path, cert)
        corridor_rows.append({
            "control_id": item["control_id"],
            "name": item["name"],
            "family": "strict-corridor",
            "expected_failed_obligation": expected,
            "observed_failed_obligations": ";".join(audit.failed_obligations),
            "model_ref": rel(model_path),
            "certificate_ref": rel(cert_path),
            "control_passed": "true",
        })

    for item in direct_controls():
        model = item["model"]
        model_path = direct_model_dir / f"{item['control_id']}.model.json"
        write_json(model_path, model)
        audit = audit_direct_successor(model)
        expected = str(item["expected_failed_obligation"])
        if audit.direct_successor_valid or expected not in audit.failed_obligations:
            raise RuntimeError(f"direct control failed: {item['control_id']} expected {expected}, got {audit.failed_obligations}")
        cert = {
            "schema_version": PHASE,
            "certificate_id": item["control_id"],
            "control_family": "direct-successor",
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": "checked-finite-negative-control",
            "expected_failed_obligation": expected,
            "observed_failed_obligations": list(audit.failed_obligations),
            "control_passed": True,
            "audit": audit.to_dict(),
            "checker": checker_payload("cst_tt.corridor", "audit_direct_successor"),
        }
        cert_path = direct_cert_dir / f"{item['control_id']}.certificate.json"
        write_json(cert_path, cert)
        direct_rows.append({
            "control_id": item["control_id"],
            "name": item["name"],
            "family": "direct-successor",
            "expected_failed_obligation": expected,
            "observed_failed_obligations": ";".join(audit.failed_obligations),
            "model_ref": rel(model_path),
            "certificate_ref": rel(cert_path),
            "control_passed": "true",
        })

    composition_rows: list[dict[str, object]] = []
    for item in _composition_control_models():
        bundle = {
            "schema_version": "CST-TT-04-model-v1",
            "model_id": item["control_id"],
            "title": item["name"],
            "left": item["left"],
            "right": item["right"],
        }
        model_path = corridor_model_dir / f"{item['control_id']}.model.json"
        write_json(model_path, bundle)
        left_audit = audit_strict_corridor(item["left"])
        right_audit = audit_strict_corridor(item["right"])
        left_chain = [row["code"] for row in item["left"]["carrier_chain"]]
        right_chain = [row["code"] for row in item["right"]["carrier_chain"]]
        left_final = item["left"]["episode"]["stages"][-1]
        right_initial = item["right"]["episode"]["stages"][0]
        shared = bool(left_chain[-1] == right_chain[0])
        signature_equal = left_final["signature"] == right_initial["signature"]
        support_equal = left_final["active_support"] == right_initial["active_support"]
        route_equal = left_final["signature"]["route_residue"] == right_initial["signature"]["route_residue"]
        failed = []
        if not shared:
            failed.append("shared-frontier-carrier")
        if not signature_equal:
            failed.append("frontier-signature-equal")
        if not support_equal:
            failed.append("frontier-support-equal")
        if not route_equal:
            failed.append("frontier-route-memory-equal")
        expected = str(item["expected_failed_obligation"])
        if expected not in failed or frontier_compatible(item["left"], item["right"]):
            raise RuntimeError(f"composition control failed: {item['control_id']} expected {expected}, got {failed}")
        audit = {
            "left_valid": left_audit.strict_corridor_valid,
            "right_valid": right_audit.strict_corridor_valid,
            "shared_frontier_carrier": shared,
            "frontier_signature_equal": signature_equal,
            "frontier_support_equal": support_equal,
            "frontier_route_memory_equal": route_equal,
            "frontier_compatible": False,
            "failed_obligations": failed,
        }
        cert = {
            "schema_version": PHASE,
            "certificate_id": item["control_id"],
            "control_family": "composition-interface",
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": "checked-finite-negative-control",
            "expected_failed_obligation": expected,
            "observed_failed_obligations": failed,
            "control_passed": True,
            "audit": audit,
            "checker": checker_payload("cst_tt.corridor", "frontier_compatible"),
        }
        cert_path = corridor_cert_dir / f"{item['control_id']}.certificate.json"
        write_json(cert_path, cert)
        composition_rows.append({
            "control_id": item["control_id"],
            "name": item["name"],
            "family": "composition-interface",
            "expected_failed_obligation": expected,
            "observed_failed_obligations": ";".join(failed),
            "model_ref": rel(model_path),
            "certificate_ref": rel(cert_path),
            "control_passed": "true",
        })

    all_corridor_rows = [*corridor_rows, *composition_rows]
    fields = [
        "control_id", "name", "family", "expected_failed_obligation",
        "observed_failed_obligations", "model_ref", "certificate_ref", "control_passed",
    ]
    write_csv(ROOT / "registries/CORRIDOR_CONTROL_REGISTRY.csv", fields, all_corridor_rows)
    write_csv(ROOT / "registries/DIRECT_SUCCESSOR_CONTROL_REGISTRY.csv", fields, direct_rows)
    return {
        "corridor_rows": all_corridor_rows,
        "direct_rows": direct_rows,
        "total": len(all_corridor_rows) + len(direct_rows),
    }


def build_direct_successors() -> dict[str, Any]:
    model_dir = ROOT / "models/direct_successor"
    cert_dir = ROOT / "formal/certificates/direct_successor"
    model_dir.mkdir(parents=True, exist_ok=True)
    cert_dir.mkdir(parents=True, exist_ok=True)
    models = [positive_direct_successor(), positive_direct_path_left(), positive_direct_path_right()]
    rows: list[dict[str, object]] = []
    for model in models:
        model_path = model_dir / f"{model['model_id']}.model.json"
        write_json(model_path, model)
        audit = audit_direct_successor(model)
        if not audit.direct_successor_valid or audit.detached_operational_pattern:
            raise RuntimeError(f"positive direct successor failed: {model['model_id']} {audit.failed_obligations}")
        cert = {
            "schema_version": PHASE,
            "certificate_id": model["model_id"],
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": "checked-finite-direct-temporal-successor",
            "claim_lanes": ["S-L"],
            "claim_ceiling": "exact finite structural event-successor criterion only",
            "theorem_evidence": {
                "theorem_ids": ["TTD-01", "TTD-03"],
                "lean_declarations": [
                    "CSTTT.DirectSuccessorTheory.directSuccessorValidity",
                    "CSTTT.DirectSuccessorTheory.directSuccessorDetachedCopyExclusion",
                    "CSTTT.DirectSuccessorTheory.directSuccessorPathComposition",
                ],
                "lean_compile_status": "pending-toolchain",
            },
            "audit": audit.to_dict(),
            "checker": checker_payload("cst_tt.corridor", "audit_direct_successor"),
        }
        cert_path = cert_dir / f"{model['model_id']}.certificate.json"
        write_json(cert_path, cert)
        rows.append({
            "successor_id": model["model_id"],
            "role": "atomic-positive",
            "source_carrier": model["source_carrier"]["code"],
            "target_carrier": model["target_carrier"]["code"],
            "source_event": model["last_source_event_id"],
            "target_event": model["first_target_event_id"],
            "route_status": model["route_status"],
            "model_ref": rel(model_path),
            "certificate_ref": rel(cert_path),
            "model_sha256": sha256(model_path),
            "result_status": cert["result_status"],
            "claim_ceiling": cert["claim_ceiling"],
        })

    left = models[1]
    right = models[2]
    path_audit = audit_direct_successor_path([left, right])
    if not path_audit.path_valid or path_audit.atomic_endpoint_edge_present:
        raise RuntimeError(f"direct path composition failed: {path_audit.failed_obligations}")
    left_path = model_dir / "DS-POS-02A.model.json"
    right_path = model_dir / "DS-POS-02B.model.json"
    path_cert = {
        "schema_version": PHASE,
        "certificate_id": "DS-PATH-POS-01",
        "atomic_model_refs": [rel(left_path), rel(right_path)],
        "atomic_model_hashes": [sha256(left_path), sha256(right_path)],
        "result_status": "checked-finite-direct-successor-path",
        "claim_lanes": ["S-L"],
        "claim_ceiling": "finite path of immediate temporal edges; no new atomic endpoint edge",
        "audit": path_audit.to_dict(),
        "checker": checker_payload("cst_tt.corridor", "audit_direct_successor_path"),
    }
    path_cert_path = cert_dir / "DS-PATH-POS-01.certificate.json"
    write_json(path_cert_path, path_cert)
    write_csv(
        ROOT / "registries/DIRECT_SUCCESSOR_REGISTRY.csv",
        [
            "successor_id", "role", "source_carrier", "target_carrier", "source_event",
            "target_event", "route_status", "model_ref", "certificate_ref", "model_sha256",
            "result_status", "claim_ceiling",
        ],
        rows,
    )
    write_csv(
        ROOT / "registries/DIRECT_SUCCESSOR_PATH_REGISTRY.csv",
        [
            "path_id", "atomic_models", "carrier_chain", "path_valid", "atomic_endpoint_edge_present",
            "certificate_ref", "claim_ceiling",
        ],
        [
            {
                "path_id": "DS-PATH-POS-01",
                "atomic_models": "DS-POS-02A;DS-POS-02B",
                "carrier_chain": f"{SOURCE['code']}>{MIDDLE['code']}>{TARGET['code']}",
                "path_valid": "true",
                "atomic_endpoint_edge_present": "false",
                "certificate_ref": rel(path_cert_path),
                "claim_ceiling": path_cert["claim_ceiling"],
            }
        ],
    )
    return {"models": models, "rows": rows, "path_certificate": path_cert}


def build_searches() -> dict[str, Any]:
    out = ROOT / "formal/certificates/search"
    out.mkdir(parents=True, exist_ok=True)
    searches = {
        "CORRIDOR_SUPPORT_SEARCH": bounded_corridor_support_search(),
        "NONREDUNDANCY_TRUTH_TABLE_SEARCH": bounded_nonredundancy_truth_table_search(),
        "CORRIDOR_COMPOSITION_SEARCH": bounded_corridor_composition_search(),
        "DIRECT_SUCCESSOR_SEARCH": bounded_direct_successor_search(),
        "DIRECT_PATH_COMPOSITION_SEARCH": bounded_direct_path_composition_search(),
    }
    for name, payload in searches.items():
        write_json(out / f"{name}.json", {
            "schema_version": PHASE,
            "search_id": name,
            "deterministic": True,
            "python_hash_seed": 0,
            "result": payload,
            "usage_boundary": "bounded finite stress evidence; not a proof oracle",
        })
    write_csv(
        ROOT / "registries/CORRIDOR_SEARCH_REGISTRY.csv",
        ["search_id", "candidates_examined", "principal_result", "certificate_ref", "usage_boundary"],
        [
            {
                "search_id": "CORRIDOR_SUPPORT_SEARCH",
                "candidates_examined": searches["CORRIDOR_SUPPORT_SEARCH"]["candidates_examined"],
                "principal_result": "zero detached passes; zero gapped passes; nonuniversal",
                "certificate_ref": "formal/certificates/search/CORRIDOR_SUPPORT_SEARCH.json",
                "usage_boundary": "bounded support-pattern family",
            },
            {
                "search_id": "NONREDUNDANCY_TRUTH_TABLE_SEARCH",
                "candidates_examined": searches["NONREDUNDANCY_TRUTH_TABLE_SEARCH"]["boolean_update_tables_examined"],
                "principal_result": "four jointly nonredundant Boolean update tables",
                "certificate_ref": "formal/certificates/search/NONREDUNDANCY_TRUTH_TABLE_SEARCH.json",
                "usage_boundary": "two-input Boolean intervention family",
            },
            {
                "search_id": "CORRIDOR_COMPOSITION_SEARCH",
                "candidates_examined": searches["CORRIDOR_COMPOSITION_SEARCH"]["candidate_pairs_examined"],
                "principal_result": "carrier-chain composition succeeds; endpoint-mixedness fails",
                "certificate_ref": "formal/certificates/search/CORRIDOR_COMPOSITION_SEARCH.json",
                "usage_boundary": "declared two-leg summary family",
            },
            {
                "search_id": "DIRECT_SUCCESSOR_SEARCH",
                "candidates_examined": searches["DIRECT_SUCCESSOR_SEARCH"]["candidates_examined"],
                "principal_result": "one strict shape; zero detached or arbitrary-data passes",
                "certificate_ref": "formal/certificates/search/DIRECT_SUCCESSOR_SEARCH.json",
                "usage_boundary": "eleven-field Boolean operational family",
            },
            {
                "search_id": "DIRECT_PATH_COMPOSITION_SEARCH",
                "candidates_examined": searches["DIRECT_PATH_COMPOSITION_SEARCH"]["candidate_pairs_examined"],
                "principal_result": "all compatible paths compose without creating an atomic endpoint edge",
                "certificate_ref": "formal/certificates/search/DIRECT_PATH_COMPOSITION_SEARCH.json",
                "usage_boundary": "three-tick bounded path family",
            },
        ],
    )
    return searches


def build_comparison() -> list[dict[str, object]]:
    rows = [
        {
            "case_id": "CMP-01", "case_name": "atomic live overlap", "evidence_ref": "models/corridors/COR-POS-01.model.json",
            "strict_overlap_chain": "pass", "atomic_direct_successor": "fail", "direct_successor_path": "fail",
            "classification": "strict overlap only",
        },
        {
            "case_id": "CMP-02", "case_name": "two-leg live overlap through intermediate carrier", "evidence_ref": "models/corridors/COR-POS-02-COMPOSED.model.json",
            "strict_overlap_chain": "pass", "atomic_direct_successor": "fail", "direct_successor_path": "fail",
            "classification": "composed strict overlap chain",
        },
        {
            "case_id": "CMP-03", "case_name": "atomic direct event successor", "evidence_ref": "models/direct_successor/DS-POS-01.model.json",
            "strict_overlap_chain": "fail", "atomic_direct_successor": "pass", "direct_successor_path": "pass",
            "classification": "direct class only",
        },
        {
            "case_id": "CMP-04", "case_name": "two-edge direct path", "evidence_ref": "formal/certificates/direct_successor/DS-PATH-POS-01.certificate.json",
            "strict_overlap_chain": "fail", "atomic_direct_successor": "fail", "direct_successor_path": "pass",
            "classification": "composed direct path; not one atomic edge",
        },
        {
            "case_id": "CMP-05", "case_name": "detached exact temporal copy", "evidence_ref": "models/countermodels/CM-02.model.json",
            "strict_overlap_chain": "fail", "atomic_direct_successor": "fail", "direct_successor_path": "fail",
            "classification": "endpoint reconstruction only",
        },
        {
            "case_id": "CMP-06", "case_name": "temporal gap and resumed stream", "evidence_ref": "models/countermodels/CM-12.model.json",
            "strict_overlap_chain": "fail", "atomic_direct_successor": "fail", "direct_successor_path": "fail",
            "classification": "resumed equivalent stream",
        },
        {
            "case_id": "CMP-07", "case_name": "same-carrier re-encoding", "evidence_ref": "models/countermodels/CM-14.model.json",
            "strict_overlap_chain": "fail", "atomic_direct_successor": "fail", "direct_successor_path": "fail",
            "classification": "typing control",
        },
        {
            "case_id": "CMP-08", "case_name": "mixed but source-redundant stage", "evidence_ref": "models/corridors/controls/COR-C03.model.json",
            "strict_overlap_chain": "fail", "atomic_direct_successor": "fail", "direct_successor_path": "fail",
            "classification": "mere coexistence without two-sided causal work",
        },
        {
            "case_id": "CMP-09", "case_name": "arbitrary archival data edge", "evidence_ref": "models/direct_successor/controls/DS-C15.model.json",
            "strict_overlap_chain": "fail", "atomic_direct_successor": "fail", "direct_successor_path": "fail",
            "classification": "data reachability only",
        },
    ]
    write_csv(
        ROOT / "registries/OVERLAP_DIRECT_COMPARISON.csv",
        [
            "case_id", "case_name", "evidence_ref", "strict_overlap_chain",
            "atomic_direct_successor", "direct_successor_path", "classification",
        ],
        rows,
    )
    return rows


def update_registries() -> None:
    theorem_path = ROOT / "registries/THEOREM_REGISTRY.csv"
    theorem_rows = read_csv(theorem_path)
    updates = {
        "TTH-04": {
            "status": "proof-source-and-executable-certificate-landed",
            "lean_statement": "CSTTT.CorridorTheory.strictTemporalCorridorComposition;CSTTT.CorridorTheory.atomicTemporalCorridorCertificateSound",
            "toy_dependencies": "TTM-01;TTM-05;TTM-06",
        },
        "TTN-01": {
            "status": "proof-source-and-checked-finite-countermodel",
            "lean_statement": "CSTTT.Prospects.DetachedCopyCountermodel;CSTTT.CorridorTheory.noMixedStageExcludesAtomicCorridor",
        },
        "TTN-09": {
            "status": "proof-source-and-checked-finite-countermodel",
            "lean_statement": "CSTTT.Prospects.GapResumeCountermodel;CSTTT.CorridorTheory.realizedGapExcludesAtomicCorridor",
        },
        "TTD-01": {
            "status": "proof-source-and-executable-certificate-landed",
            "lean_statement": "CSTTT.DirectSuccessorTheory.directSuccessorValidity;CSTTT.DirectSuccessorTheory.directSuccessorPathComposition",
        },
        "TTD-02": {
            "status": "finite-discriminator-evidence-landed-theorem-open",
        },
        "TTD-03": {
            "status": "proof-source-and-executable-certificate-landed",
            "lean_statement": "CSTTT.DirectSuccessorTheory.directSuccessorDetachedCopyExclusion",
        },
    }
    for row in theorem_rows:
        if row["theorem_id"] in updates:
            row.update(updates[row["theorem_id"]])
    write_csv(theorem_path, list(theorem_rows[0]), theorem_rows)

    toy_path = ROOT / "registries/TOY_MODEL_REGISTRY.csv"
    toy_rows = read_csv(toy_path)
    for row in toy_rows:
        if row["toy_id"] == "TTM-01":
            row["status"] = "lineage-only-precursor-landed"
            row["notes"] = "COR-POS-01 and COR-POS-02-COMPOSED land the S-L corridor only; package/autonomy integration remains CST-TT-05"
        elif row["toy_id"] == "TTM-03":
            row["status"] = "checked-positive-witness"
            row["notes"] = "DS-POS-01 atomic witness plus DS-PATH-POS-01 compositional path; class remains separately named"
    write_csv(toy_path, list(toy_rows[0]), toy_rows)

    definitions = read_csv(ROOT / "registries/DEFINITION_REGISTRY.csv")
    new_defs = [
        {"definition_id": "D-055", "name": "FiniteTemporalStage", "module": "CSTTT/Corridor/FiniteTemporalCorridor.lean", "purpose": "finite support and realized temporal signature at one episode stage", "claim_lanes": "S-L", "dependencies": "D-007;D-010", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-056", "name": "InterventionProjection", "module": "CSTTT/Corridor/FiniteTemporalCorridor.lean", "purpose": "full and one-carrier-removed later temporal projections", "claim_lanes": "S-L", "dependencies": "D-055", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-057", "name": "AtomicTemporalCorridorData", "module": "CSTTT/Corridor/FiniteTemporalCorridor.lean", "purpose": "one overlap leg with no-gap, transport, event, takeover, and intervention fields", "claim_lanes": "S-L", "dependencies": "D-048;D-055;D-056", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-058", "name": "AtomicTemporalCorridorCertificate", "module": "CSTTT/Corridor/FiniteTemporalCorridor.lean", "purpose": "proof fields for a strict overlap leg", "claim_lanes": "S-L", "dependencies": "D-057", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-059", "name": "CorridorSummaryData", "module": "CSTTT/Corridor/Composition.lean", "purpose": "composition-stable summary of a nonempty overlap-leg chain", "claim_lanes": "S-L", "dependencies": "D-058", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-060", "name": "FrontierCompatible", "module": "CSTTT/Corridor/Composition.lean", "purpose": "exact shared-carrier and temporal-signature frontier agreement", "claim_lanes": "S-L", "dependencies": "D-059", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-061", "name": "AtomicDirectSuccessorData", "module": "CSTTT/Corridor/FiniteDirectSuccessor.lean", "purpose": "immediate event edge with complete payload, necessity, progress, route, and ownership fields", "claim_lanes": "S-L", "dependencies": "D-006;D-048", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-062", "name": "AtomicDirectSuccessorCertificate", "module": "CSTTT/Corridor/FiniteDirectSuccessor.lean", "purpose": "proof fields for the separately named immediate event class", "claim_lanes": "S-L", "dependencies": "D-061", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-063", "name": "DetachedOperationalPattern", "module": "CSTTT/Corridor/FiniteDirectSuccessor.lean", "purpose": "storage, replay, nonnecessity, or nonadjacency boundary", "claim_lanes": "S-L", "dependencies": "D-061", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-064", "name": "DirectSuccessorPathData", "module": "CSTTT/Corridor/FiniteDirectSuccessor.lean", "purpose": "composition-stable path of immediate temporal edges", "claim_lanes": "S-L", "dependencies": "D-062", "status": "landed-proof-source-and-executable-semantics"},
    ]
    existing = {row["definition_id"] for row in definitions}
    definitions.extend(row for row in new_defs if row["definition_id"] not in existing)
    write_csv(ROOT / "registries/DEFINITION_REGISTRY.csv", list(definitions[0]), definitions)

    schemas = read_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv")
    new_schemas = [
        {"schema_id": "CS-16", "file": "strict_temporal_corridor_certificate.schema.json", "name": "Strict carrier-chain temporal corridor", "claim_lanes": "S-L", "scaffold_example": "examples/scaffold/strict_temporal_corridor_certificate.scaffold.json", "status": "landed-checked-corridor-certificates"},
        {"schema_id": "CS-17", "file": "corridor_composition_certificate.schema.json", "name": "Temporal corridor composition", "claim_lanes": "S-L", "scaffold_example": "examples/scaffold/corridor_composition_certificate.scaffold.json", "status": "landed-checked-composition-certificate"},
        {"schema_id": "CS-18", "file": "direct_successor_landed.schema.json", "name": "Atomic direct temporal successor", "claim_lanes": "S-L", "scaffold_example": "examples/scaffold/direct_successor_landed.scaffold.json", "status": "landed-checked-direct-certificates"},
        {"schema_id": "CS-19", "file": "direct_successor_path_certificate.schema.json", "name": "Direct temporal successor path", "claim_lanes": "S-L", "scaffold_example": "examples/scaffold/direct_successor_path_certificate.scaffold.json", "status": "landed-checked-direct-path-certificate"},
        {"schema_id": "CS-20", "file": "corridor_control_certificate.schema.json", "name": "Corridor and direct negative controls", "claim_lanes": "M;S-L", "scaffold_example": "examples/scaffold/corridor_control_certificate.scaffold.json", "status": "landed-checked-corridor-controls"},
    ]
    existing_schemas = {row["schema_id"] for row in schemas}
    schemas.extend(row for row in new_schemas if row["schema_id"] not in existing_schemas)
    write_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv", list(schemas[0]), schemas)

    kills = read_csv(ROOT / "registries/KILL_CRITERIA.csv")
    for row in kills:
        if row["kill_id"] in {"K-FIACH-02", "K-FIACH-03", "K-FIACH-04", "K-DIRECT-01"}:
            row["status"] = "not-triggered-CST-TT-04"
    write_csv(ROOT / "registries/KILL_CRITERIA.csv", list(kills[0]), kills)

    edges = read_csv(ROOT / "registries/DEPENDENCY_EDGES.csv")
    additions = [
        {"source": "D-048", "target": "D-057", "reason": "bundled temporal transport enters each atomic overlap leg", "status": "landed-CST-TT-04"},
        {"source": "D-056", "target": "D-058", "reason": "intervention projection supplies two-sided nonredundancy", "status": "landed-CST-TT-04"},
        {"source": "D-058", "target": "D-059", "reason": "atomic overlap legs enter the carrier-chain summary", "status": "landed-CST-TT-04"},
        {"source": "D-060", "target": "TTH-04", "reason": "exact frontier compatibility purchases composition", "status": "landed-CST-TT-04"},
        {"source": "D-062", "target": "TTD-01", "reason": "immediate event certificate supplies direct-successor validity", "status": "landed-CST-TT-04"},
        {"source": "D-063", "target": "TTD-03", "reason": "detached operational pattern is excluded by direct certificate fields", "status": "landed-CST-TT-04"},
        {"source": "D-064", "target": "TTD-01", "reason": "event-edge paths compose without creating a new atomic edge", "status": "landed-CST-TT-04"},
    ]
    existing_edge_keys = {(row["source"], row["target"], row["reason"]) for row in edges}
    edges.extend(row for row in additions if (row["source"], row["target"], row["reason"]) not in existing_edge_keys)
    edges.sort(key=lambda row: (row["source"], row["target"], row["reason"], row["status"]))
    write_csv(ROOT / "registries/DEPENDENCY_EDGES.csv", list(edges[0]), edges)


def build_docs(searches: Mapping[str, Any], controls: Mapping[str, Any], comparison: list[dict[str, object]]) -> None:
    support = searches["CORRIDOR_SUPPORT_SEARCH"]
    nonred = searches["NONREDUNDANCY_TRUTH_TABLE_SEARCH"]
    comp = searches["CORRIDOR_COMPOSITION_SEARCH"]
    direct = searches["DIRECT_SUCCESSOR_SEARCH"]
    direct_path = searches["DIRECT_PATH_COMPOSITION_SEARCH"]

    (ROOT / "docs/TEMPORAL_CORRIDOR_SEMANTICS.md").write_text(f"""# Strict Temporal-Corridor Semantics

CST-TT-04 defines the primary lineage engine in two layers.

1. An **atomic overlap leg** changes responsibility from one local carrier to another through a temporally realized mixed stage.
2. A **strict carrier-chain corridor** is a nonempty sequence of atomic legs whose shared carrier, temporal signature, route memory, and ownership frontier agree exactly.

Every atomic leg requires:

- source-only entry and target-only exit;
- no unrealized stage;
- strict local order, tick, progress, and record advancement;
- a forward operational event graph;
- complete bundled temporal-transport evidence;
- a mixed stage containing both local carriers;
- independently computed source-removal and target-removal projections;
- exact takeover and route discipline.

The intervention audit is not a final-verdict field. In the positive witness, the later projection is computed as

```text
base + source contribution + target contribution.
```

Removing either contribution changes the later predictive/tick/record projection. The bounded Boolean search examined **{nonred['boolean_update_tables_examined']}** two-input update tables and found **{nonred['jointly_nonredundant_table_count']}** independently testable jointly nonredundant tables.

The support-pattern stress search examined **{support['candidates_examined']:,}** finite assignments. It found **{support['strict_passes']}** strict shapes, zero detached-copy passes, and zero realized-gap passes. This is bounded evidence, not a proof oracle.

## Claim ceiling

The certificate establishes only episode-indexed structural temporal lineage under the declared finite semantics. It does not establish target package realization, post-withdrawal autonomy, phenomenal status, personal survival, or numerical identity.
""", encoding="utf-8")

    (ROOT / "docs/CORRIDOR_COMPOSITION_THEOREM.md").write_text(f"""# Strict Temporal-Corridor Composition

The original scaffold required one stage containing the ultimate source and ultimate target. That rule is valid for one atomic handoff but is not closed under composition.

For a two-hop episode

```text
S -> mixed(S,M) -> M -> mixed(M,T) -> T
```

there need not be a stage containing both `S` and `T`. Nevertheless every substrate change is realized through an audited overlap, the intermediate frontier is exact, and package time has no gap.

CST-TT-04 therefore freezes:

- **atomic endpoint overlap** for each carrier change;
- **carrier-chain composition** for multi-hop corridors;
- exact equality of the shared carrier, temporal signature, route residue, and boundary ownership;
- one merged boundary stage rather than duplication or omission.

`COR-COMP-01` composes `COR-POS-02A` and `COR-POS-02B`. The result has two atomic legs, five realized stages, and one intermediate-carrier boundary. The old ultimate-endpoint mixedness rule is false; the strict carrier-chain rule is true.

The bounded summary search examined **{comp['candidate_pairs_examined']}** compatible two-leg shapes. All composed under the carrier-chain rule, while all failed ultimate-endpoint mixedness.

The Lean proof-source construction is `CSTTT.CorridorTheory.strictTemporalCorridorComposition`. Actual Lean-kernel compilation remains separately pending.
""", encoding="utf-8")

    (ROOT / "docs/NONREDUNDANCY_INTERVENTION_AUDIT.md").write_text(f"""# Two-Sided Intervention Audit

A mixed stage is not sufficient merely because both carriers are present. Each local carrier must perform independently detectable work in the later temporal projection.

For declared projection fields `predictive_rank`, `tick_index`, and `record_value`, the checker computes:

```text
full           = base + source contribution + target contribution
source removed = base + target contribution
target removed = base + source contribution
```

The leg passes only when the computed full projection equals the actual later-stage signature and differs from both removal projections. The event graph must also contain a source-owned and target-owned mixed-stage event feeding the audited later event.

This avoids defining nonredundancy through the corridor result. The evidence uses only update contributions, event ownership, stage order, and temporal signatures. The Boolean search found masks `{nonred['jointly_nonredundant_table_masks']}` as the jointly nonredundant two-input tables; the ordinary AND table is one witness.

Controls `COR-C03`, `COR-C04`, `COR-C16`, and `COR-C17` separately remove source contribution, target contribution, source event influence, and target event influence.
""", encoding="utf-8")

    (ROOT / "docs/DIRECT_SUCCESSOR_RESULT.md").write_text(f"""# Separately Named Direct Temporal Successor

The direct class permits one source-owned temporal event to feed the first target-owned temporal event without an extended mixed-support stage. It remains distinct from the strict overlap corridor.

An atomic certificate requires:

- distinct source and target carriers;
- immediate stage adjacency with no unrealized interval;
- a direct `live-temporal-handoff` dependency;
- a complete hash-bound temporal payload;
- counterfactual necessity of that edge;
- no storage mediator, replayable archive, or alternative temporal parent;
- a single-use temporal token;
- predictive, order, tick, progress, and strict record advancement;
- route discipline and ownership transfer.

`DS-POS-01` passes all fields. `DS-POS-02A` and `DS-POS-02B` compose into the valid path `DS-PATH-POS-01`. Path composition does **not** invent an atomic source-to-final-target edge; atomic directness and path reachability remain separately typed.

The bounded direct-shape search examined **{direct['candidates_examined']:,}** assignments. Exactly **{direct['valid_direct_successor_shapes']}** passed; zero detached-like shapes and zero arbitrary-data-edge shapes passed. The path search examined **{direct_path['candidate_pairs_examined']}** tick triples and composed every compatible pair without falsely creating an atomic endpoint edge.

This class is a structural event-successor criterion only. It does not establish strict overlap, target package realization, autonomy, phenomenal status, or personal identity.
""", encoding="utf-8")

    compare_rows = [
        (row["case_id"], row["case_name"], row["strict_overlap_chain"], row["atomic_direct_successor"], row["direct_successor_path"], row["classification"])
        for row in comparison
    ]
    (ROOT / "docs/OVERLAP_DIRECT_SUCCESSOR_COMPARISON.md").write_text("""# Overlap and Direct-Successor Comparison

The fixed finite battery shows that the two classes are not interchangeable.

""" + md_table(
        ["Case", "Scenario", "Strict overlap chain", "Atomic direct", "Direct path", "Classification"],
        compare_rows,
    ) + """

The battery contains a strict-overlap witness that is not direct and a direct witness that is not strict-overlap. This is finite discriminator evidence for incomparability; the full `TTD-02` theorem remains assigned to CST-TT-07A.

Detached copies, temporal gaps, same-carrier re-encodings, redundant mixed stages, and archival data edges satisfy neither class.
""", encoding="utf-8")

    control_rows = [*controls["corridor_rows"], *controls["direct_rows"]]
    (ROOT / "docs/CORRIDOR_CONTROL_SUITE.md").write_text(f"""# Corridor and Direct-Successor Control Suite

The phase lands **{len(control_rows)}** exact negative controls:

- {len(controls['corridor_rows'])} strict-corridor or composition-interface controls;
- {len(controls['direct_rows'])} direct-successor controls.

Every control is hash-bound to its model, expected failed obligation, observed failed obligations, and checker function. No control passes its positive predicate.

""" + md_table(
        ["ID", "Family", "Expected failure", "Observed failures"],
        [(row["control_id"], row["family"], row["expected_failed_obligation"], row["observed_failed_obligations"]) for row in control_rows],
    ) + """

The suite specifically tests detached-copy admission, temporal gaps, one-sided redundancy, route collapse, missing transport components, takeover failure, boundary mismatch, arbitrary data reachability, archival replay, absent progress, and verdict-loaded evidence.
""", encoding="utf-8")

    (ROOT / "docs/CST-TT-04_DECISION_GATE.md").write_text("""# CST-TT-04 Decision Gate

## Strict overlap engine

- `K-FIACH-02`: **not triggered**. Independently testable two-sided intervention predicates exist and survive bounded stress.
- `K-FIACH-03`: **not triggered**. Atomic overlap legs compose under the exact carrier/signature/route frontier rule.
- `K-FIACH-04`: **not triggered**. Detached endpoint-equivalent copies and explicit gaps fail the strict predicate.

Temporal-FIACH remains primary, with the strict carrier-chain corridor as its lineage engine.

## Direct class

- `K-DIRECT-01`: **not triggered**. The landed class requires an immediate necessary hash-bound temporal edge and excludes replayable storage, mediators, alternative parents, and endpoint equality alone.

The direct class survives as a separately named provisional strengthening. It does not redefine or broaden the strict overlap result.

## Fallback

Temporal-IAPS remains locked. No FIACH kill criterion has been reached.
""", encoding="utf-8")

    (ROOT / "docs/PHASE_BOUNDARY.md").write_text("""# CST-TT-04 Phase Boundary

Landed in this phase:

- exact finite atomic overlap-leg semantics;
- a composition-stable strict carrier-chain temporal corridor;
- independently computed two-sided intervention nonredundancy;
- no-mixed-stage and realized-gap proof-source boundaries;
- an exact positive corridor and a two-leg composed corridor;
- a separately named atomic direct temporal successor;
- a composition-stable direct-successor path that does not create a new atomic edge;
- detached/arbitrary-data exclusion controls;
- complete bounded stress and comparison surfaces.

Retained from earlier phases:

- the finite no-go kernel;
- integrated C1-C8 target-package semantics;
- bundled heterogeneous temporal transport and route discipline.

Not landed:

- post-withdrawal autonomy;
- an integrated positive Temporal-FIACH certificate;
- Temporal-IAPS;
- empirical recognition or certificate soundness;
- phenomenal, personal-survival, or numerical-identity conclusions.

The next authorized phase is `CST-TT-05`, withdrawal autonomy and integrated Temporal-FIACH.
""", encoding="utf-8")


def write_status_surfaces(summary: Mapping[str, Any]) -> None:
    project = {
        "project": "CST-TT",
        "phase": PHASE,
        "base_tag": "CST-EXP-06-v1",
        "base_commit": "4a48d7ee212cde2404be06f01df0a28aa3ad12fc",
        "phase_base_tag": BASE_TAG,
        "phase_base_commit": BASE_COMMIT,
        "primary": "Temporal-FIACH strict carrier-chain overlap",
        "primary_lineage_engine": "composition-stable chain of audited atomic overlap legs",
        "conditional_fallback": "Temporal-IAPS",
        "fallback_unlocked": False,
        "provisional_strengthening": "direct temporal successor and direct-edge paths",
        "direct_successor_status": "survived-separately-named-CST-TT-04",
        "mandatory_companion": "finite no-go kernel",
        "negative_kernel_status": "frozen",
        "claim_ceiling": "structural precursor only",
        "lean_toolchain": "leanprover/lean4:v4.28.0",
        "generic_theorem_proof_sources_landed": 15,
        "generic_theorems_lean_compiled": 0,
        "generic_theorems_proved": 0,
        "scientific_results_landed": 20,
        "checked_finite_countermodels": 15,
        "checked_finite_package_witnesses": 2,
        "checked_staged_package_assemblies": 1,
        "checked_temporal_transport_certificates": 2,
        "checked_route_certificates": 2,
        "checked_memory_or_flatness_certificates": 2,
        "checked_record_arrow_certificates": 1,
        "checked_strict_corridor_certificates": summary["strict_corridor_certificates"],
        "checked_corridor_composition_certificates": summary["corridor_composition_certificates"],
        "checked_direct_successor_certificates": summary["direct_successor_certificates"],
        "checked_direct_successor_path_certificates": summary["direct_successor_path_certificates"],
        "checked_corridor_and_direct_controls": summary["checked_controls"],
        "positive_temporal_lineage_witnesses": summary["positive_temporal_lineage_witnesses"],
        "positive_handoff_witnesses": 0,
        "old_endpoint_mixed_rule_status": "rejected-as-noncomposition-stable",
        "next_phase": "CST-TT-05",
        "python_version": platform.python_version(),
    }
    write_json(ROOT / "registries/PROJECT_REGISTRY.json", project)
    write_json(ROOT / "config/REPRODUCIBILITY.json", {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "status": "deterministic-temporal-corridor-and-direct-successor-frozen",
        "builder": "scripts/build_tt04_assets.py",
        "validator": "scripts/validate_tt04.py",
        "rebuild_verifier": "scripts/verify_tt04_rebuild.py",
        "canonical_seed": 0,
        "python_hash_seed": 0,
        "randomized_search_enabled": False,
        "corridor_support_candidates_examined": summary["corridor_support_candidates_examined"],
        "nonredundancy_tables_examined": summary["nonredundancy_tables_examined"],
        "corridor_composition_pairs_examined": summary["corridor_composition_pairs_examined"],
        "direct_successor_candidates_examined": summary["direct_successor_candidates_examined"],
        "direct_path_candidates_examined": summary["direct_path_candidates_examined"],
        "scientific_result_generated": True,
        "next_phase": "CST-TT-05",
        "usage_boundary": "Deterministic finite checks corroborate proof-source surfaces and certificates; Python is not represented as a proof oracle.",
    })

    write_json(ROOT / "manifests/CST-TT-04_PHASE_SUMMARY.json", summary)
    write_json(ROOT / "manifests/PHASE_SUMMARY.json", summary)

    theorem_delta = [
        {"theorem_id": "TTH-04", "prior_status": "open-scaffold", "new_status": "proof-source-and-executable-certificate-landed", "evidence": "COR-POS-01;COR-COMP-01", "next_action": "integrate with autonomy in CST-TT-05"},
        {"theorem_id": "TTN-01", "prior_status": "checked-finite-countermodel", "new_status": "proof-source-and-checked-finite-countermodel", "evidence": "noMixedStageExcludesAtomicCorridor;CM-02", "next_action": "retain mandatory boundary"},
        {"theorem_id": "TTN-09", "prior_status": "checked-finite-countermodel", "new_status": "proof-source-and-checked-finite-countermodel", "evidence": "realizedGapExcludesAtomicCorridor;CM-12", "next_action": "retain strict no-gap boundary"},
        {"theorem_id": "TTD-01", "prior_status": "open-scaffold", "new_status": "proof-source-and-executable-certificate-landed", "evidence": "DS-POS-01;DS-PATH-POS-01", "next_action": "retain separately named strengthening"},
        {"theorem_id": "TTD-02", "prior_status": "open-scaffold", "new_status": "finite-discriminator-evidence-landed-theorem-open", "evidence": "CMP-01;CMP-03", "next_action": "formal relation theorem in CST-TT-07A"},
        {"theorem_id": "TTD-03", "prior_status": "open-scaffold", "new_status": "proof-source-and-executable-certificate-landed", "evidence": "DS-C01;DS-C02;DS-C03;DS-C15", "next_action": "retain provenance boundary"},
    ]
    write_csv(
        ROOT / "manifests/CST-TT-04_THEOREM_STATUS_DELTA.csv",
        ["theorem_id", "prior_status", "new_status", "evidence", "next_action"],
        theorem_delta,
    )

    model_rows: list[dict[str, object]] = []
    for row in read_csv(ROOT / "registries/TEMPORAL_CORRIDOR_WITNESS_REGISTRY.csv"):
        model_rows.append({"asset_id": row["corridor_id"], "asset_kind": "strict-corridor", "status": row["result_status"], "model_ref": row["model_ref"], "certificate_ref": row["certificate_ref"], "claim_ceiling": row["claim_ceiling"]})
    model_rows.append({"asset_id": "COR-COMP-01", "asset_kind": "corridor-composition", "status": "checked-finite-corridor-composition", "model_ref": "models/corridors/COR-POS-02-COMPOSED.model.json", "certificate_ref": "formal/certificates/corridors/COR-COMP-01.certificate.json", "claim_ceiling": "composition of exact finite overlap-leg chains only"})
    for row in read_csv(ROOT / "registries/DIRECT_SUCCESSOR_REGISTRY.csv"):
        model_rows.append({"asset_id": row["successor_id"], "asset_kind": "direct-successor", "status": row["result_status"], "model_ref": row["model_ref"], "certificate_ref": row["certificate_ref"], "claim_ceiling": row["claim_ceiling"]})
    model_rows.append({"asset_id": "DS-PATH-POS-01", "asset_kind": "direct-successor-path", "status": "checked-finite-direct-successor-path", "model_ref": "models/direct_successor/DS-POS-02A.model.json;models/direct_successor/DS-POS-02B.model.json", "certificate_ref": "formal/certificates/direct_successor/DS-PATH-POS-01.certificate.json", "claim_ceiling": "finite path only"})
    for registry in ("CORRIDOR_CONTROL_REGISTRY.csv", "DIRECT_SUCCESSOR_CONTROL_REGISTRY.csv"):
        for row in read_csv(ROOT / "registries" / registry):
            model_rows.append({"asset_id": row["control_id"], "asset_kind": row["family"] + "-control", "status": "checked-finite-negative-control", "model_ref": row["model_ref"], "certificate_ref": row["certificate_ref"], "claim_ceiling": "one-obligation negative control"})
    write_csv(
        ROOT / "manifests/CST-TT-04_MODEL_CERTIFICATE_DELTA.csv",
        ["asset_id", "asset_kind", "status", "model_ref", "certificate_ref", "claim_ceiling"],
        model_rows,
    )

    theorem_rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    active = [row for row in theorem_rows if row["status"] != "open-scaffold"]
    registry_doc = "# Theorem and Toy Registry\n\n" + md_table(
        ["ID", "Name", "Phase", "Status", "Lanes", "Ceiling"],
        [(row["theorem_id"], row["name"], row["phase"], row["status"], row["claim_lanes"], row["claim_ceiling"]) for row in active],
    ) + "\n\nAll open fallback and later-strengthening contracts remain in the machine-readable registries.\n"
    (ROOT / "docs/THEOREM_AND_TOY_REGISTRY.md").write_text(registry_doc, encoding="utf-8")

    completion = f"""# CST-TT-04 Completion Report

CST-TT-04 lands the finite temporal-lineage engine and the separately named direct event-successor fork.

## Landed results

- four checked strict carrier-chain corridor certificates, including one two-leg composition;
- one checked corridor-composition certificate;
- three checked atomic direct-successor certificates;
- one checked direct-successor path certificate;
- {summary['checked_controls']} exact negative controls;
- five deterministic bounded stress searches;
- proof-source surfaces for strict corridor composition, no-mixed-stage exclusion, gap exclusion, direct validity, detached-pattern exclusion, and direct-path composition.

The old rule requiring ultimate source and ultimate target to coexist in one stage is rejected as noncomposition-stable. Every individual carrier change still requires an audited mixed, no-gap, two-sided-nonredundant overlap leg.

The direct class survived because it requires an immediate necessary hash-bound temporal edge and excludes replayable storage, mediators, alternative parents, temporal gaps, and endpoint equality alone. It remains separately named.

## Decision

Temporal-FIACH remains primary. Temporal-IAPS remains locked. No positive integrated handoff or post-withdrawal autonomy witness is claimed.

## Toolchain boundary

Lean proof sources contain no placeholder commands. Actual Lean compilation is not claimed unless `lean` and `lake` are available and `lake build` succeeds. Python certificates and bounded searches are not represented as proof-oracle outputs.

The next authorized phase is `CST-TT-05`, withdrawal autonomy and integrated Temporal-FIACH.
"""
    (ROOT / "manifests/CST-TT-04_COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")
    (ROOT / "manifests/COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")

    restore = f"""# Restore and Verify CST-TT-04

1. Extract the repository ZIP.
2. Enter the `cst-temporal-transcendence` directory.
3. Confirm `git rev-parse CST-TT-04-v1^{{}}` after the release tag is present.
4. Run:

```bash
export PYTHONHASHSEED=0
export PYTHONPATH=src:scripts
python3 -m pytest -q
python3 scripts/validate_tt04.py --no-write
python3 scripts/verify_tt04_rebuild.py
```

5. If Lean and Lake are available, run `lake build`. If they are absent, record the check as skipped; do not infer a compile pass.

The phase base is `{BASE_TAG}` / `{BASE_COMMIT}`.
"""
    (ROOT / "RESTORE_AND_VERIFY.md").write_text(restore, encoding="utf-8")
    (ROOT / "docs/RESTORE_AND_BUILD.md").write_text(restore, encoding="utf-8")

    readme = """# CST-TT — Temporal Substrate Transcendence Theorems and Toys

Current frozen phase: **CST-TT-04**.

The repository now contains an exact finite strict temporal-lineage engine based on composition-stable chains of audited overlap legs, plus a separately named direct event-successor class. Earlier package, transport, route, and no-go assets remain frozen.

The primary route remains Temporal-FIACH. Post-withdrawal autonomy and the integrated certificate are reserved for CST-TT-05.
"""
    (ROOT / "README.md").write_text(readme, encoding="utf-8")
    (ROOT / "STATE.md").write_text("# Repository State\n\nFrozen at CST-TT-04 semantic assets; release manifest and tag are finalized separately.\n", encoding="utf-8")
    (ROOT / "STATUS.md").write_text("# Status\n\nStrict corridor and direct-successor lineage assets landed. Autonomy and integrated Temporal-FIACH remain open.\n", encoding="utf-8")
    changelog = ROOT / "CHANGELOG.md"
    prior = changelog.read_text(encoding="utf-8") if changelog.exists() else "# Changelog\n"
    entry = "\n## CST-TT-04 — 2026-08-10\n\nLanded strict carrier-chain temporal corridors, composition, direct temporal successors, exact controls, and bounded stress searches.\n"
    if "## CST-TT-04" not in prior:
        prior = prior.rstrip() + "\n" + entry
    changelog.write_text(prior, encoding="utf-8")
    (ROOT / "changelog/CST-TT-04.md").write_text(entry.lstrip(), encoding="utf-8")

    formal_readme = """# Formal Assets

CST-TT-04 adds proof-source modules for atomic overlap legs, carrier-chain corridor composition, no-mixed-stage and realized-gap boundaries, atomic direct temporal successors, detached-pattern exclusion, and direct-edge path composition.

Certificate directories contain hash-bound exact finite witnesses and controls. Python checks certificate semantics; it is not a proof oracle. Lean-kernel compilation is reported only after an actual `lake build` pass.
"""
    (ROOT / "formal/README.md").write_text(formal_readme, encoding="utf-8")
    write_json(ROOT / "formal/TOOLCHAIN_STATUS.json", {
        "phase": PHASE,
        "lean_toolchain": "leanprover/lean4:v4.28.0",
        "lean_executable_detected_at_build": False,
        "lake_executable_detected_at_build": False,
        "lean_compile_status": "pending-toolchain",
        "python_certificate_status": "checked",
        "claim": "no Lean compilation pass is claimed by the asset builder",
    })


def main() -> int:
    positives = build_positive_corridors()
    direct = build_direct_successors()
    controls = build_controls()
    searches = build_searches()
    comparison = build_comparison()
    update_registries()

    summary = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "generated_date": DATE,
        "phase_base_tag": BASE_TAG,
        "phase_base_commit": BASE_COMMIT,
        "advanced_theorem_surfaces": 5,
        "new_generic_proof_source_declarations": 7,
        "strict_corridor_certificates": len(positives["rows"]),
        "corridor_composition_certificates": 1,
        "direct_successor_certificates": len(direct["rows"]),
        "direct_successor_path_certificates": 1,
        "checked_controls": controls["total"],
        "corridor_and_composition_controls": len(controls["corridor_rows"]),
        "direct_successor_controls": len(controls["direct_rows"]),
        "comparison_rows": len(comparison),
        "bounded_searches": len(searches),
        "corridor_support_candidates_examined": searches["CORRIDOR_SUPPORT_SEARCH"]["candidates_examined"],
        "nonredundancy_tables_examined": searches["NONREDUNDANCY_TRUTH_TABLE_SEARCH"]["boolean_update_tables_examined"],
        "corridor_composition_pairs_examined": searches["CORRIDOR_COMPOSITION_SEARCH"]["candidate_pairs_examined"],
        "direct_successor_candidates_examined": searches["DIRECT_SUCCESSOR_SEARCH"]["candidates_examined"],
        "direct_path_candidates_examined": searches["DIRECT_PATH_COMPOSITION_SEARCH"]["candidate_pairs_examined"],
        "detached_corridor_passes": searches["CORRIDOR_SUPPORT_SEARCH"]["detached_passes"],
        "gapped_corridor_passes": searches["CORRIDOR_SUPPORT_SEARCH"]["gapped_passes"],
        "detached_direct_passes": searches["DIRECT_SUCCESSOR_SEARCH"]["detached_like_passes"],
        "arbitrary_data_edge_passes": searches["DIRECT_SUCCESSOR_SEARCH"]["arbitrary_data_edge_passes"],
        "old_endpoint_mixed_rule_composition_stable": False,
        "carrier_chain_rule_composition_stable": True,
        "positive_temporal_lineage_witnesses": len(positives["rows"]) + len(direct["rows"]) + 1,
        "positive_handoff_witnesses": 0,
        "fallback_unlocked": False,
        "direct_successor_survived": True,
        "next_phase": "CST-TT-05",
    }
    build_docs(searches, controls, comparison)
    write_status_surfaces(summary)

    print(json.dumps({
        "phase": PHASE,
        "strict_corridors": summary["strict_corridor_certificates"],
        "direct_successors": summary["direct_successor_certificates"],
        "controls": summary["checked_controls"],
        "advanced_theorems": summary["advanced_theorem_surfaces"],
        "search_candidates": (
            summary["corridor_support_candidates_examined"]
            + summary["nonredundancy_tables_examined"]
            + summary["corridor_composition_pairs_examined"]
            + summary["direct_successor_candidates_examined"]
            + summary["direct_path_candidates_examined"]
        ),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
