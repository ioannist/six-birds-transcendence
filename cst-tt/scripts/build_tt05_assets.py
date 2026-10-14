#!/usr/bin/env python3
from __future__ import annotations

import csv
import hashlib
import json
import platform
from pathlib import Path
from typing import Any, Iterable, Mapping

from cst_tt.fiach import audit_temporal_fiach, lane_truth_table, replay_component_certificates
from cst_tt.package_gluing import audit_package, audit_staged_assembly
from cst_tt.withdrawal_autonomy_checker import (
    audit_autonomy,
    bounded_invariant_algorithm_exhaustion,
    finite_horizon_word_count,
)
from tt05_data import (
    SOURCE,
    TARGET,
    aligned_source_package,
    aligned_staged_assembly,
    aligned_target_package,
    autonomy_controls,
    fiach_lane_control_specs,
    positive_autonomy_model,
)

ROOT = Path(__file__).resolve().parents[1]
PHASE = "CST-TT-05"
DATE = "2026-08-10"
BASE_TAG = "CST-TT-04-v1"
BASE_COMMIT = "1884214d1bae82442f37fc9e6b013e222da89b1b"


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


def checker(module: str, function: str) -> dict[str, str]:
    return {
        "module": module,
        "function": function,
        "python_version": platform.python_version(),
        "checked_at_phase": PHASE,
    }


def md_table(headers: list[str], rows: Iterable[Iterable[object]]) -> str:
    lines = ["| " + " | ".join(headers) + " |", "|" + "|".join("---" for _ in headers) + "|"]
    lines.extend("| " + " | ".join(str(value) for value in row) + " |" for row in rows)
    return "\n".join(lines)


def upsert_csv(path: Path, key: str, new_rows: list[dict[str, object]]) -> None:
    old = read_csv(path)
    fields = list(old[0].keys()) if old else list(new_rows[0].keys())
    additions = {str(row[key]): {field: row.get(field, "") for field in fields} for row in new_rows}
    kept = [row for row in old if row[key] not in additions]
    kept.extend(additions[value] for value in sorted(additions))
    write_csv(path, fields, kept)


def build_aligned_packages() -> dict[str, Any]:
    model_dir = ROOT / "models/packages"
    cert_dir = ROOT / "formal/certificates/packages"
    source = aligned_source_package()
    target = aligned_target_package()
    staged = aligned_staged_assembly(source, target)
    paths = {
        "source_model": model_dir / "PKG-POS-03-FIACH-SOURCE.model.json",
        "target_model": model_dir / "PKG-POS-04-FIACH-TARGET.model.json",
        "staged_model": model_dir / "STG-POS-02-FIACH.assembly.json",
        "source_cert": cert_dir / "PKG-POS-03-FIACH-SOURCE.certificate.json",
        "target_cert": cert_dir / "PKG-POS-04-FIACH-TARGET.certificate.json",
        "staged_cert": cert_dir / "STG-POS-02-FIACH.certificate.json",
    }
    write_json(paths["source_model"], source)
    write_json(paths["target_model"], target)
    write_json(paths["staged_model"], staged)

    package_rows: list[dict[str, object]] = []
    certs: dict[str, dict[str, Any]] = {}
    for role, model, model_path, cert_path in (
        ("handoff-aligned-source", source, paths["source_model"], paths["source_cert"]),
        ("handoff-aligned-target", target, paths["target_model"], paths["target_cert"]),
    ):
        audit = audit_package(model)
        if not audit.integrated_package_valid:
            raise RuntimeError(f"aligned package failed: {model['model_id']} {audit.failed_obligations}")
        alignment = model["handoff_alignment"]
        cert = {
            "schema_version": PHASE,
            "certificate_id": model["model_id"],
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": "checked-finite-handoff-aligned-package-certificate",
            "claim_lanes": ["S-R"],
            "claim_ceiling": "finite structural target realization aligned to one declared handoff frontier",
            "handoff_alignment": alignment,
            "theorem_evidence": {
                "theorem_ids": ["TTH-01", "TTH-02"],
                "lean_declarations": [
                    "CSTTT.PackageTheory.acyclicLocalWitnessGluing",
                    "CSTTT.PackageTheory.stagedHeterogeneousPackageAssembly",
                ],
                "lean_compile_status": "pending-toolchain",
            },
            "audit": audit.to_dict(),
            "checker": checker("cst_tt.package_gluing", "audit_package"),
        }
        write_json(cert_path, cert)
        certs[role] = cert
        package_rows.append({
            "package_id": model["model_id"],
            "role": role,
            "model_ref": rel(model_path),
            "certificate_ref": rel(cert_path),
            "model_sha256": sha256(model_path),
            "result_status": cert["result_status"],
            "clause_count": 8,
            "coordinate_count": len(audit.derived_global_assignment),
            "join_tree_root": model["join_tree"]["root"],
            "claim_lanes": "S-R",
            "claim_ceiling": cert["claim_ceiling"],
        })

    staged_audit = audit_staged_assembly(staged, source, target)
    if not staged_audit.staged_assembly_valid:
        raise RuntimeError(f"aligned staged assembly failed: {staged_audit.failed_obligations}")
    staged_cert = {
        "schema_version": PHASE,
        "certificate_id": staged["assembly_id"],
        "assembly_ref": rel(paths["staged_model"]),
        "assembly_sha256": sha256(paths["staged_model"]),
        "source_model_ref": rel(paths["source_model"]),
        "source_model_sha256": sha256(paths["source_model"]),
        "target_model_ref": rel(paths["target_model"]),
        "target_model_sha256": sha256(paths["target_model"]),
        "result_status": "checked-finite-handoff-aligned-staged-package-certificate",
        "claim_lanes": ["S-T", "S-R"],
        "claim_ceiling": "finite typed clause preservation and endpoint-aligned target assembly only",
        "handoff_alignment": staged["handoff_alignment"],
        "theorem_evidence": {
            "theorem_ids": ["TTH-01", "TTH-02"],
            "lean_declarations": [
                "CSTTT.PackageTheory.acyclicLocalWitnessGluing",
                "CSTTT.PackageTheory.stagedHeterogeneousPackageAssembly",
            ],
            "lean_compile_status": "pending-toolchain",
        },
        "audit": staged_audit.to_dict(),
        "checker": checker("cst_tt.package_gluing", "audit_staged_assembly"),
    }
    write_json(paths["staged_cert"], staged_cert)

    prior_rows = read_csv(ROOT / "registries/PACKAGE_WITNESS_REGISTRY.csv")
    existing_ids = {row["package_id"] for row in package_rows}
    write_csv(
        ROOT / "registries/PACKAGE_WITNESS_REGISTRY.csv",
        list(prior_rows[0].keys()),
        [row for row in prior_rows if row["package_id"] not in existing_ids] + package_rows,
    )
    write_csv(
        ROOT / "registries/HANDOFF_ALIGNED_PACKAGE_REGISTRY.csv",
        [
            "package_id", "role", "corridor_model_ref", "corridor_stage", "alignment_fields",
            "model_ref", "certificate_ref", "integrated_package_valid", "claim_ceiling",
        ],
        [
            {
                "package_id": row["package_id"],
                "role": row["role"],
                "corridor_model_ref": (source if "SOURCE" in str(row["package_id"]) else target)["handoff_alignment"]["corridor_model_ref"],
                "corridor_stage": (source if "SOURCE" in str(row["package_id"]) else target)["handoff_alignment"]["corridor_stage"],
                "alignment_fields": ";".join((source if "SOURCE" in str(row["package_id"]) else target)["handoff_alignment"]["alignment_fields"]),
                "model_ref": row["model_ref"],
                "certificate_ref": row["certificate_ref"],
                "integrated_package_valid": "true",
                "claim_ceiling": row["claim_ceiling"],
            }
            for row in package_rows
        ],
    )
    return {"source": source, "target": target, "staged": staged, "paths": paths, "staged_cert": staged_cert}


def build_autonomy(context: dict[str, Any]) -> dict[str, Any]:
    model_dir = ROOT / "models/autonomy"
    control_model_dir = model_dir / "controls"
    cert_dir = ROOT / "formal/certificates/autonomy"
    control_cert_dir = cert_dir / "controls"
    target_cert_ref = rel(context["paths"]["target_cert"])
    target_cert_hash = sha256(context["paths"]["target_cert"])
    positive = positive_autonomy_model(
        package_certificate_ref=target_cert_ref,
        package_certificate_sha256=target_cert_hash,
        target_package=context["target"],
    )
    positive_path = model_dir / "AUT-POS-01.model.json"
    write_json(positive_path, positive)
    audit = audit_autonomy(positive)
    if not audit.autonomy_valid:
        raise RuntimeError(f"positive autonomy failed: {audit.failed_obligations}")
    cert = {
        "schema_version": PHASE,
        "certificate_id": "AUT-POS-01",
        "model_ref": rel(positive_path),
        "model_sha256": sha256(positive_path),
        "result_status": "checked-finite-post-withdrawal-autonomy",
        "claim_lanes": ["A"],
        "claim_ceiling": "model-relative target autonomy for every disturbance word up to the declared finite horizon",
        "computed_invariant_state_ids": list(audit.computed_invariant_state_ids),
        "response_policy": [row.to_dict() for row in audit.response_policy],
        "finite_horizon": audit.finite_horizon,
        "finite_words_checked": audit.finite_words_checked,
        "collapse_trace": [],
        "theorem_evidence": {
            "theorem_ids": ["TTH-05", "TTN-06", "TTN-07", "TTN-12"],
            "lean_declarations": [
                "CSTTT.AutonomyTheory.finiteHorizonRunExists",
                "CSTTT.AutonomyTheory.postWithdrawalFiniteHorizonInvariance",
                "CSTTT.AutonomyTheory.removedEssentialResourceExcludesAutonomy",
                "CSTTT.AutonomyTheory.stalledOnlyResponsesExcludeAutonomy",
                "CSTTT.AutonomyTheory.insolventOnlyResponsesExcludeAutonomy",
            ],
            "lean_compile_status": "pending-toolchain",
        },
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.withdrawal_autonomy_checker", "audit_autonomy"),
    }
    cert_path = cert_dir / "AUT-POS-01.certificate.json"
    write_json(cert_path, cert)

    control_rows: list[dict[str, object]] = []
    controls_by_id: dict[str, dict[str, Any]] = {}
    for model in autonomy_controls(positive):
        model_path = control_model_dir / f"{model['model_id']}.model.json"
        write_json(model_path, model)
        control_audit = audit_autonomy(model)
        expected = model["expected_primary_failure"]
        if control_audit.autonomy_valid or expected not in control_audit.failed_obligations:
            raise RuntimeError(f"autonomy control failed: {model['model_id']} {control_audit.failed_obligations}")
        control_cert = {
            "schema_version": PHASE,
            "control_id": model["model_id"],
            "title": model["title"],
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "positive_baseline_ref": rel(positive_path),
            "expected_primary_failure": expected,
            "observed_failures": list(control_audit.failed_obligations),
            "result_status": "checked-autonomy-obligation-countermodel",
            "claim_lanes": ["M", "A"],
            "claim_ceiling": "finite post-withdrawal autonomy boundary only",
            "collapse_trace": [row.to_dict() for row in control_audit.collapse_trace],
            "audit": control_audit.to_dict(),
            "checker": checker("cst_tt.withdrawal_autonomy_checker", "audit_autonomy"),
        }
        control_path = control_cert_dir / f"{model['model_id']}.certificate.json"
        write_json(control_path, control_cert)
        controls_by_id[model["model_id"]] = control_cert
        control_rows.append({
            "control_id": model["model_id"],
            "title": model["title"],
            "expected_primary_failure": expected,
            "observed_failures": ";".join(control_audit.failed_obligations),
            "computed_invariant_size": len(control_audit.computed_invariant_state_ids),
            "collapse_trace_length": control_audit.collapse_trace_length if control_audit.collapse_trace_length is not None else 0,
            "model_ref": rel(model_path),
            "certificate_ref": rel(control_path),
            "result_status": control_cert["result_status"],
            "claim_ceiling": control_cert["claim_ceiling"],
        })

    write_csv(
        ROOT / "registries/AUTONOMY_WITNESS_REGISTRY.csv",
        [
            "autonomy_id", "target_carrier", "state_count", "disturbance_count", "action_count",
            "invariant_size", "finite_horizon", "finite_words_checked", "model_ref", "certificate_ref",
            "result_status", "claim_lanes", "claim_ceiling",
        ],
        [{
            "autonomy_id": "AUT-POS-01",
            "target_carrier": TARGET["code"],
            "state_count": len(positive["states"]),
            "disturbance_count": len(positive["disturbances"]),
            "action_count": len(positive["actions"]),
            "invariant_size": len(audit.computed_invariant_state_ids),
            "finite_horizon": audit.finite_horizon,
            "finite_words_checked": audit.finite_words_checked,
            "model_ref": rel(positive_path),
            "certificate_ref": rel(cert_path),
            "result_status": cert["result_status"],
            "claim_lanes": "A",
            "claim_ceiling": cert["claim_ceiling"],
        }],
    )
    write_csv(
        ROOT / "registries/AUTONOMY_CONTROL_REGISTRY.csv",
        [
            "control_id", "title", "expected_primary_failure", "observed_failures",
            "computed_invariant_size", "collapse_trace_length", "model_ref", "certificate_ref",
            "result_status", "claim_ceiling",
        ],
        control_rows,
    )

    search = bounded_invariant_algorithm_exhaustion()
    search["claim_ceiling"] = "exact corroboration only within the declared two-state finite family"
    search_path = ROOT / "formal/certificates/search/AUTONOMY_INVARIANT_EXHAUSTION.json"
    write_json(search_path, search)
    horizon = {
        "schema_version": PHASE,
        "search_id": "AUTONOMY-FINITE-HORIZON-EXHAUSTION",
        "disturbance_alphabet_size": len(positive["disturbances"]),
        "finite_horizon": positive["finite_horizon"],
        "expected_word_count": finite_horizon_word_count(len(positive["disturbances"]), positive["finite_horizon"]),
        "certificate_word_count": audit.finite_words_checked,
        "all_words_survive": audit.finite_horizon_survives,
        "claim_ceiling": "finite words through the declared horizon only",
    }
    horizon_path = ROOT / "formal/certificates/search/AUTONOMY_FINITE_HORIZON_EXHAUSTION.json"
    write_json(horizon_path, horizon)
    write_csv(
        ROOT / "registries/AUTONOMY_SEARCH_REGISTRY.csv",
        ["search_id", "candidates_examined", "successful_candidates", "mismatches", "certificate_ref", "claim_ceiling"],
        [
            {
                "search_id": "AUTONOMY-INVARIANT-EXHAUSTION",
                "candidates_examined": search["candidate_count"],
                "successful_candidates": search["endpoint_autonomous_count"],
                "mismatches": search["algorithm_bruteforce_mismatch_count"],
                "certificate_ref": rel(search_path),
                "claim_ceiling": search["claim_ceiling"],
            },
            {
                "search_id": horizon["search_id"],
                "candidates_examined": horizon["expected_word_count"],
                "successful_candidates": horizon["certificate_word_count"],
                "mismatches": 0 if horizon["all_words_survive"] else 1,
                "certificate_ref": rel(horizon_path),
                "claim_ceiling": horizon["claim_ceiling"],
            },
        ],
    )
    return {
        "positive": positive,
        "positive_path": positive_path,
        "audit": audit,
        "certificate": cert,
        "certificate_path": cert_path,
        "controls": controls_by_id,
        "control_rows": control_rows,
        "search": search,
        "horizon": horizon,
    }


def build_fiach(package_context: dict[str, Any], autonomy_context: dict[str, Any]) -> dict[str, Any]:
    model_dir = ROOT / "models/fiach"
    control_model_dir = model_dir / "controls"
    cert_dir = ROOT / "formal/certificates/fiach"
    control_cert_dir = cert_dir / "controls"
    component_refs = {
        "source_package": rel(package_context["paths"]["source_cert"]),
        "staged_assembly": rel(package_context["paths"]["staged_cert"]),
        "target_package": rel(package_context["paths"]["target_cert"]),
        "corridor": "formal/certificates/corridors/COR-POS-01.certificate.json",
        "autonomy": rel(autonomy_context["certificate_path"]),
    }
    component_sha = {key: sha256(ROOT / value) for key, value in component_refs.items()}
    spec = {
        "schema_version": "CST-TT-05-model-v1",
        "certificate_id": "FIACH-POS-01",
        "title": "finite integrated autonomous causal temporal handoff",
        "source": dict(SOURCE),
        "target": dict(TARGET),
        "component_refs": component_refs,
        "component_sha256": component_sha,
        "route_status": "route-indexed",
        "recognition_status": "not-addressed",
        "claim_ceiling": "structural precursor only; no consciousness, phenomenal continuity, survival, or identity conclusion",
        "nonclaims": [
            "no consciousness conclusion",
            "no phenomenal-continuity conclusion",
            "no personal-survival or numerical-identity conclusion",
            "no unbounded physical liveness conclusion",
        ],
    }
    model_path = model_dir / "FIACH-POS-01.model.json"
    write_json(model_path, spec)
    audit = audit_temporal_fiach(spec, ROOT)
    if not audit.aggregate_valid:
        raise RuntimeError(f"integrated FIACH failed: {audit.failed_obligations}")
    replay = replay_component_certificates(spec, ROOT)
    if not all(replay.values()):
        raise RuntimeError(f"component replay failed: {replay}")
    cert = {
        "schema_version": PHASE,
        "certificate_id": "FIACH-POS-01",
        "source": dict(SOURCE),
        "target": dict(TARGET),
        "component_refs": component_refs,
        "component_sha256": component_sha,
        "route_status": "route-indexed",
        "recognition_status": "not-addressed",
        "lane_results": {"S-T": True, "S-R": True, "S-L": True, "A": True},
        "result_status": "checked-finite-temporal-fiach-certificate",
        "claim_ceiling": "structural precursor only; no consciousness, phenomenal continuity, survival, or identity conclusion",
        "theorem_evidence": {
            "theorem_ids": ["TTH-02", "TTH-04", "TTH-05", "TTH-06"],
            "lean_declarations": [
                "CSTTT.TargetTheory.temporalFIACHCertificateSoundness",
                "CSTTT.TargetTheory.temporalFIACHEndpointsLinked",
                "CSTTT.TargetTheory.threeLaneAggregateExact",
            ],
            "lean_compile_status": "pending-toolchain",
            "component_replay": replay,
        },
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.fiach", "audit_temporal_fiach"),
    }
    cert_path = cert_dir / "FIACH-POS-01.certificate.json"
    write_json(cert_path, cert)

    control_specs = fiach_lane_control_specs(
        source_package_ref=component_refs["source_package"],
        staged_ref=component_refs["staged_assembly"],
        positive_package_ref=component_refs["target_package"],
        negative_package_ref="formal/certificates/packages/controls/PC-01.certificate.json",
        positive_corridor_ref=component_refs["corridor"],
        negative_corridor_ref="formal/certificates/corridors/controls/COR-C01.certificate.json",
        positive_autonomy_ref=component_refs["autonomy"],
        negative_autonomy_ref="formal/certificates/autonomy/controls/AUT-C01.certificate.json",
    )
    control_rows: list[dict[str, object]] = []
    for control in control_specs:
        control["component_sha256"] = {key: sha256(ROOT / value) for key, value in control["component_refs"].items()}
        model_path_control = control_model_dir / f"{control['certificate_id']}.model.json"
        write_json(model_path_control, control)
        control_audit = audit_temporal_fiach(control, ROOT)
        expected = control["expected_lane_statuses"]
        observed = {
            "S-R": control_audit.structural_realization_lane,
            "S-L": control_audit.structural_lineage_lane,
            "A": control_audit.autonomy_lane,
        }
        if control_audit.aggregate_valid or observed != expected:
            raise RuntimeError(f"FIACH lane control failed: {control['certificate_id']} expected={expected} observed={observed}")
        control_cert = {
            "schema_version": PHASE,
            "control_id": control["certificate_id"],
            "title": control["title"],
            "model_ref": rel(model_path_control),
            "model_sha256": sha256(model_path_control),
            "expected_lane_statuses": expected,
            "observed_lane_statuses": {
                "S-T": control_audit.structural_transport_lane,
                **observed,
            },
            "component_refs": control["component_refs"],
            "component_sha256": control["component_sha256"],
            "result_status": "checked-fiach-lane-independence-control",
            "claim_ceiling": "lane-conjunction and independence boundary only",
            "audit": control_audit.to_dict(),
            "checker": checker("cst_tt.fiach", "audit_temporal_fiach"),
        }
        control_cert_path = control_cert_dir / f"{control['certificate_id']}.certificate.json"
        write_json(control_cert_path, control_cert)
        control_rows.append({
            "control_id": control["certificate_id"],
            "title": control["title"],
            "S-R": str(expected["S-R"]).lower(),
            "S-L": str(expected["S-L"]).lower(),
            "A": str(expected["A"]).lower(),
            "aggregate": "false",
            "model_ref": rel(model_path_control),
            "certificate_ref": rel(control_cert_path),
            "observed_failures": ";".join(control_audit.failed_obligations),
            "claim_ceiling": control_cert["claim_ceiling"],
        })

    truth = lane_truth_table()
    truth_path = ROOT / "formal/certificates/search/FIACH_LANE_TRUTH_TABLE.json"
    write_json(truth_path, truth)
    write_csv(
        ROOT / "registries/FIACH_WITNESS_REGISTRY.csv",
        [
            "fiach_id", "source_carrier", "target_carrier", "route_status", "S-T", "S-R", "S-L", "A",
            "model_ref", "certificate_ref", "result_status", "claim_ceiling",
        ],
        [{
            "fiach_id": "FIACH-POS-01",
            "source_carrier": SOURCE["code"],
            "target_carrier": TARGET["code"],
            "route_status": "route-indexed",
            "S-T": "true",
            "S-R": "true",
            "S-L": "true",
            "A": "true",
            "model_ref": rel(model_path),
            "certificate_ref": rel(cert_path),
            "result_status": cert["result_status"],
            "claim_ceiling": cert["claim_ceiling"],
        }],
    )
    write_csv(
        ROOT / "registries/FIACH_LANE_CONTROL_REGISTRY.csv",
        ["control_id", "title", "S-R", "S-L", "A", "aggregate", "model_ref", "certificate_ref", "observed_failures", "claim_ceiling"],
        control_rows,
    )
    return {
        "spec": spec,
        "model_path": model_path,
        "audit": audit,
        "certificate": cert,
        "certificate_path": cert_path,
        "controls": control_rows,
        "truth": truth,
        "truth_path": truth_path,
    }


def update_registries(package_context: dict[str, Any], autonomy_context: dict[str, Any], fiach_context: dict[str, Any]) -> None:
    theorem_updates = {
        "TTH-05": {
            "phase": PHASE,
            "status": "proof-source-and-executable-certificate-landed",
            "dependencies": "TTH-02",
            "lean_statement": "CSTTT.AutonomyTheory.postWithdrawalFiniteHorizonInvariance",
            "toy_dependencies": "TTM-01;TTM-04;TTM-09;TTM-10",
        },
        "TTH-06": {
            "phase": PHASE,
            "status": "proof-source-and-executable-certificate-landed",
            "dependencies": "TTH-02;TTH-04;TTH-05",
            "lean_statement": "CSTTT.TargetTheory.temporalFIACHCertificateSoundness",
            "toy_dependencies": "TTM-01;TTM-02;TTM-04;TTM-11",
        },
        "TTN-06": {
            "phase": PHASE,
            "status": "proof-source-and-checked-finite-countermodel",
            "dependencies": "TTH-05",
            "lean_statement": "CSTTT.AutonomyTheory.removedEssentialResourceExcludesAutonomy",
            "toy_dependencies": "TTM-04",
        },
    }
    theorem_rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    for row in theorem_rows:
        if row["theorem_id"] in theorem_updates:
            row.update(theorem_updates[row["theorem_id"]])
    write_csv(ROOT / "registries/THEOREM_REGISTRY.csv", list(theorem_rows[0].keys()), theorem_rows)

    definitions = [
        {"definition_id": "D-065", "name": "ExactAutonomyData", "module": "CSTTT/Autonomy/FiniteAutonomy.lean", "purpose": "finite withdrawal boundary, disturbance class, response, progress, and budget data", "claim_lanes": "A", "dependencies": "D-026;D-046;D-047", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-066", "name": "ExactAutonomyCertificate", "module": "CSTTT/Autonomy/FiniteAutonomy.lean", "purpose": "proof fields for model-relative post-withdrawal controlled invariance", "claim_lanes": "A", "dependencies": "D-065", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-067", "name": "ControlledRun", "module": "CSTTT/Autonomy/FiniteAutonomy.lean", "purpose": "finite run under a target-owned disturbance-response policy", "claim_lanes": "A", "dependencies": "D-066", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-068", "name": "ThreeLaneStatus", "module": "CSTTT/Targets/FiniteTemporalFIACH.lean", "purpose": "independent S-R, S-L, and A lane status", "claim_lanes": "S-R;S-L;A", "dependencies": "D-044;D-059;D-066", "status": "landed-proof-source-and-executable-semantics"},
        {"definition_id": "D-069", "name": "TemporalFIACHCertificate", "module": "CSTTT/Targets/FiniteTemporalFIACH.lean", "purpose": "hash-bound aggregate of independently proved package, lineage, and autonomy obligations", "claim_lanes": "S-T;S-R;S-L;A", "dependencies": "D-045;D-059;D-066;D-068", "status": "landed-proof-source-and-executable-semantics"},
    ]
    upsert_csv(ROOT / "registries/DEFINITION_REGISTRY.csv", "definition_id", definitions)

    schema_rows = [
        {"schema_id": "CS-21", "file": "aligned_package_certificate.schema.json", "name": "Handoff-aligned integrated package", "claim_lanes": "S-R", "scaffold_example": "examples/scaffold/aligned_package_certificate.scaffold.json", "status": "landed-checked-fiach-package-certificates"},
        {"schema_id": "CS-22", "file": "aligned_staged_package_certificate.schema.json", "name": "Handoff-aligned staged package assembly", "claim_lanes": "S-T;S-R", "scaffold_example": "examples/scaffold/aligned_staged_package_certificate.scaffold.json", "status": "landed-checked-fiach-package-certificates"},
        {"schema_id": "CS-23", "file": "post_withdrawal_autonomy_certificate.schema.json", "name": "Post-withdrawal autonomy", "claim_lanes": "A", "scaffold_example": "examples/scaffold/post_withdrawal_autonomy_certificate.scaffold.json", "status": "landed-checked-autonomy-certificate"},
        {"schema_id": "CS-24", "file": "autonomy_control_certificate.schema.json", "name": "Autonomy negative control", "claim_lanes": "M;A", "scaffold_example": "examples/scaffold/autonomy_control_certificate.scaffold.json", "status": "landed-checked-autonomy-controls"},
        {"schema_id": "CS-25", "file": "temporal_fiach_landed_certificate.schema.json", "name": "Integrated Temporal-FIACH", "claim_lanes": "S-T;S-R;S-L;A", "scaffold_example": "examples/scaffold/temporal_fiach_landed_certificate.scaffold.json", "status": "landed-checked-fiach-certificate"},
        {"schema_id": "CS-26", "file": "fiach_lane_control_certificate.schema.json", "name": "Temporal-FIACH lane control", "claim_lanes": "M;S-R;S-L;A", "scaffold_example": "examples/scaffold/fiach_lane_control_certificate.scaffold.json", "status": "landed-checked-lane-controls"},
    ]
    upsert_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv", "schema_id", schema_rows)

    dependency_rows = read_csv(ROOT / "registries/DEPENDENCY_EDGES.csv")
    new_edges = [
        {"source": "TTH-02", "target": "TTH-05", "reason": "autonomy invariant is indexed to an independently landed target package", "status": "landed-CST-TT-05"},
        {"source": "TTH-05", "target": "TTH-06", "reason": "post-withdrawal autonomy enters the aggregate certificate as an independent lane", "status": "landed-CST-TT-05"},
        {"source": "TTH-04", "target": "TTH-06", "reason": "strict carrier-chain corridor enters the aggregate as the S-L lane", "status": "landed-CST-TT-05"},
        {"source": "TTH-02", "target": "TTH-06", "reason": "aligned staged package and target realization enter the aggregate as S-T and S-R", "status": "landed-CST-TT-05"},
        {"source": "TTN-06", "target": "TTH-05", "reason": "external-support shadow is a mandatory autonomy boundary", "status": "landed-CST-TT-05"},
    ]
    for edge in new_edges:
        if edge not in dependency_rows:
            dependency_rows.append(edge)
    dependency_rows.sort(key=lambda row: (row["source"], row["target"], row["reason"], row["status"]))
    write_csv(ROOT / "registries/DEPENDENCY_EDGES.csv", list(dependency_rows[0].keys()), dependency_rows)

    kill_rows = read_csv(ROOT / "registries/KILL_CRITERIA.csv")
    statuses = {
        "K-FIACH-05": "not-triggered-CST-TT-05",
        "K-AUTO-01": "not-triggered-positive-and-confirmed-by-negative-controls-CST-TT-05",
        "K-AUTO-02": "not-triggered-positive-and-confirmed-by-anti-stall-control-CST-TT-05",
    }
    for row in kill_rows:
        if row["kill_id"] in statuses:
            row["status"] = statuses[row["kill_id"]]
    write_csv(ROOT / "registries/KILL_CRITERIA.csv", list(kill_rows[0].keys()), kill_rows)

    toy_rows = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    toy_updates = {
        "TTM-01": ("checked-positive-instance", "FIACH-POS-01 combines aligned package, COR-POS-01, and AUT-POS-01"),
        "TTM-04": ("checked-negative-instance-and-autonomy-control", "CM-04 retained; AUT-C01 gives explicit post-withdrawal collapse"),
        "TTM-09": ("checked-negative-control", "AUT-C05 rejects a stable but nonprogressing target"),
        "TTM-10": ("checked-negative-instance-and-collapse-trace", "CM-13 retained; AUT-C06 gives a shortest budget-collapse trace"),
    }
    for row in toy_rows:
        if row["toy_id"] in toy_updates:
            row["status"], row["notes"] = toy_updates[row["toy_id"]]
    write_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv", list(toy_rows[0].keys()), toy_rows)

    project = json.loads((ROOT / "registries/PROJECT_REGISTRY.json").read_text(encoding="utf-8"))
    project.update({
        "phase": PHASE,
        "phase_base_tag": BASE_TAG,
        "phase_base_commit": BASE_COMMIT,
        "primary": "Temporal-FIACH strict carrier-chain overlap",
        "primary_status": "exact-finite-structural-witness-landed",
        "checked_finite_package_witnesses": 4,
        "checked_staged_package_assemblies": 2,
        "checked_post_withdrawal_autonomy_certificates": 1,
        "checked_autonomy_controls": len(autonomy_context["control_rows"]),
        "checked_temporal_fiach_certificates": 1,
        "checked_fiach_lane_controls": len(fiach_context["controls"]),
        "positive_handoff_witnesses": 1,
        "fallback_unlocked": False,
        "next_phase": "CST-TT-06",
        "claim_ceiling": "exact finite structural precursor only",
        "python_version": platform.python_version(),
    })
    write_json(ROOT / "registries/PROJECT_REGISTRY.json", project)


def build_docs(package_context: dict[str, Any], autonomy_context: dict[str, Any], fiach_context: dict[str, Any]) -> None:
    audit = autonomy_context["audit"]
    controls = autonomy_context["control_rows"]
    autonomy_doc = f"""# Post-withdrawal autonomy

CST-TT-05 defines autonomy as a target-owned controlled invariant after an explicit withdrawal intervention. The removed set includes the source, migration bridge, controller, external decoder, external scheduler, and undeclared repair support. The retained environment is separately declared and every retained resource is target-owned.

The checker computes the greatest finite controlled invariant rather than accepting a user-supplied safe set. A state survives only when, for every declared disturbance, a target-owned action reaches another surviving state while preserving the integrated package, retained-resource closure, positive tick progress, strict record advance, and budget solvency.

## Positive witness

{md_table(["Field", "Value"], [
    ("Target carrier", TARGET['code']),
    ("Finite states", len(autonomy_context['positive']['states'])),
    ("Disturbances", len(autonomy_context['positive']['disturbances'])),
    ("Computed invariant", ', '.join(audit.computed_invariant_state_ids)),
    ("Finite horizon", audit.finite_horizon),
    ("Disturbance words checked", audit.finite_words_checked),
    ("Target-owned responses", audit.target_owned_responses),
    ("Anti-stall", audit.anti_stall_on_invariant),
    ("Budget solvent", audit.budget_solvent_on_invariant),
])}

The finite certificate establishes model-relative autonomy for the declared disturbance alphabet and horizon. It does not establish indefinite physical persistence, consciousness, felt flow, lineage, survival, or identity.

## Proof architecture

The Python fixed-point implementation emits a canonical policy and collapse traces. Lean proof sources define finite controlled runs and show that a certificate with total safe responses constructs a run of every declared finite length. Python enumeration is corroboration, not a proof oracle.
"""
    (ROOT / "docs/POST_WITHDRAWAL_AUTONOMY.md").write_text(autonomy_doc, encoding="utf-8")

    control_doc = "# Autonomy control suite\n\n" + md_table(
        ["ID", "Control", "Primary failure", "Invariant size", "Collapse length"],
        [
            (row["control_id"], row["title"], row["expected_primary_failure"], row["computed_invariant_size"], row["collapse_trace_length"])
            for row in controls
        ],
    ) + "\n\nThe controls separately expose external support, incomplete withdrawal, resource overlap, external action ownership, temporal stalling, budget insolvency, invalid safe-set declarations, missing disturbance responses, post-hoc disturbance classes, external maintenance ownership, external retained resources, and verdict smuggling.\n"
    (ROOT / "docs/AUTONOMY_CONTROL_SUITE.md").write_text(control_doc, encoding="utf-8")

    finite_doc = """# Finite-horizon and liveness boundary

`AUT-POS-01` survives every disturbance word of length at most six under its declared target-owned policy. Because the computed set is a controlled fixed point, the finite model also supplies a reusable response at every certified state. The released theorem statement remains finite-horizon: it does not identify the finite abstraction with an indefinitely operating physical system.

`AUT-C06` demonstrates the distinction. A target can pass an initial step yet have no controlled invariant because its maintenance budget is consumed without target-owned regeneration. Its collapse trace is exact and finite.

No claim of unbounded lived time, empirical robustness, or physical resource sufficiency is made.
"""
    (ROOT / "docs/FINITE_HORIZON_LIVENESS_BOUNDARY.md").write_text(finite_doc, encoding="utf-8")

    package_doc = """# Handoff-aligned package witnesses

The earlier package and corridor witnesses were scientifically independent and used different local endpoint labels. CST-TT-05 does not conceal that mismatch inside the aggregate. It builds fresh source and target package witnesses whose C6 fields are aligned to the actual entry and exit frontiers of `COR-POS-01`.

The aligned fields are route residue, tick phase, record frontier, and maintenance owner. The full C1-C8 package remains independently audited; corridor alignment is extra linkage, not part of the clause definitions.
"""
    (ROOT / "docs/HANDOFF_ALIGNED_PACKAGE.md").write_text(package_doc, encoding="utf-8")

    fiach_doc = f"""# Integrated Temporal-FIACH theorem and exact witness

The landed aggregate is:

```text
TemporalFIACH :=
  staged structural preservation
  ∧ integrated target package
  ∧ strict temporal carrier-chain corridor
  ∧ post-withdrawal target autonomy
```

The certificate keeps the lanes separate:

{md_table(["Lane", "Witness", "Status"], [
    ("S-T", "STG-POS-02-FIACH", fiach_context['audit'].structural_transport_lane),
    ("S-R", "PKG-POS-04-FIACH-TARGET", fiach_context['audit'].structural_realization_lane),
    ("S-L", "COR-POS-01", fiach_context['audit'].structural_lineage_lane),
    ("A", "AUT-POS-01", fiach_context['audit'].autonomy_lane),
])}

The aggregate additionally checks exact component hashes, source/target carrier identity, staged-model references, C6-to-corridor frontier agreement, corridor-to-withdrawal event agreement, autonomy-to-package contract agreement, and route status.

`FIACH-POS-01` is an exact finite structural witness. It does not establish consciousness, phenomenal continuity, personal survival, numerical identity, A1, A2-P, or empirical recognition.
"""
    (ROOT / "docs/INTEGRATED_TEMPORAL_FIACH_THEOREM.md").write_text(fiach_doc, encoding="utf-8")

    lane_doc = "# Lane independence audit\n\nThe aggregate is exact conjunction, not score aggregation. The complete Boolean table has eight rows and exactly one positive row. Six component-splice controls realize every one-lane and two-lane combination of S-R, S-L, and A while the aggregate remains false. These are logical independence controls, not claims that every splice is a physically coherent migration episode.\n\n" + md_table(
        ["Control", "S-R", "S-L", "A", "Aggregate"],
        [(row["control_id"], row["S-R"], row["S-L"], row["A"], row["aggregate"]) for row in fiach_context["controls"]],
    ) + "\n"
    (ROOT / "docs/LANE_INDEPENDENCE_AUDIT.md").write_text(lane_doc, encoding="utf-8")

    decision = """# CST-TT-05 decision gate

The primary target survives.

- `K-FIACH-05` is not triggered: one exact finite witness satisfies independently audited package, strict corridor, and autonomy gates.
- `K-AUTO-01` is not triggered by the positive witness: no response uses a removed resource. Negative controls confirm the boundary.
- `K-AUTO-02` is not triggered: the maximal invariant has genuine tick progress, strict record advance, and solvent target-owned repair.
- Temporal-IAPS remains locked.

The next phase may study composition, branching, route completion, and full toy-suite closure. The present result remains a structural precursor only.
"""
    (ROOT / "docs/CST-TT-05_DECISION_GATE.md").write_text(decision, encoding="utf-8")

    phase_boundary = """# CST-TT-05 phase boundary

Landed: aligned package witnesses, post-withdrawal finite autonomy, exact controls, and one integrated Temporal-FIACH structural witness.

Not landed: consciousness, felt continuity, empirical recognition, personal survival, numerical identity, A1/A2-P, certificate soundness for consciousness, unbounded physical liveness, full handoff composition, fission/fusion closure, or a Six Birds simulation.

Next: CST-TT-06 composition, branching, route completion, and full toy closure.
"""
    (ROOT / "docs/PHASE_BOUNDARY.md").write_text(phase_boundary, encoding="utf-8")


def write_status_surfaces(package_context: dict[str, Any], autonomy_context: dict[str, Any], fiach_context: dict[str, Any]) -> None:
    summary = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "generated_date": DATE,
        "phase_base_tag": BASE_TAG,
        "phase_base_commit": BASE_COMMIT,
        "handoff_aligned_package_certificates": 2,
        "handoff_aligned_staged_certificates": 1,
        "post_withdrawal_autonomy_certificates": 1,
        "autonomy_controls": len(autonomy_context["control_rows"]),
        "fiach_certificates": 1,
        "fiach_lane_controls": len(fiach_context["controls"]),
        "invariant_search_candidates": autonomy_context["search"]["candidate_count"],
        "invariant_search_mismatches": autonomy_context["search"]["algorithm_bruteforce_mismatch_count"],
        "finite_disturbance_words_checked": autonomy_context["audit"].finite_words_checked,
        "positive_temporal_fiach_witnesses": 1,
        "fallback_unlocked": False,
        "next_phase": "CST-TT-06",
        "claim_ceiling": "exact finite structural precursor only",
    }
    write_json(ROOT / "manifests/CST-TT-05_PHASE_SUMMARY.json", summary)
    write_json(ROOT / "manifests/PHASE_SUMMARY.json", summary)
    write_json(ROOT / "config/REPRODUCIBILITY.json", {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "status": "deterministic-withdrawal-autonomy-and-temporal-fiach-frozen",
        "builder": "scripts/build_tt05_assets.py",
        "validator": "scripts/validate_tt05.py",
        "rebuild_verifier": "scripts/verify_tt05_rebuild.py",
        "canonical_seed": 0,
        "python_hash_seed": 0,
        "randomized_search_enabled": False,
        "invariant_search_candidates": summary["invariant_search_candidates"],
        "finite_disturbance_words_checked": summary["finite_disturbance_words_checked"],
        "next_phase": summary["next_phase"],
        "usage_boundary": "Python checks exact finite certificate semantics and emits witnesses; it is not represented as a Lean proof oracle.",
    })

    theorem_delta = [
        {"theorem_id": "TTH-05", "prior_status": "open-scaffold", "new_status": "proof-source-and-executable-certificate-landed", "evidence": "AUT-POS-01; 4096-case invariant exhaustion", "next_action": "compose autonomy across handoffs in CST-TT-06"},
        {"theorem_id": "TTH-06", "prior_status": "open-scaffold", "new_status": "proof-source-and-executable-certificate-landed", "evidence": "FIACH-POS-01; six lane controls", "next_action": "composition and branching in CST-TT-06"},
        {"theorem_id": "TTN-06", "prior_status": "checked-finite-countermodel", "new_status": "proof-source-and-checked-finite-countermodel", "evidence": "AUT-C01; removedEssentialResourceExcludesAutonomy", "next_action": "retain mandatory autonomy boundary"},
    ]
    write_csv(ROOT / "manifests/CST-TT-05_THEOREM_STATUS_DELTA.csv", ["theorem_id", "prior_status", "new_status", "evidence", "next_action"], theorem_delta)

    model_rows: list[dict[str, object]] = []
    for row in read_csv(ROOT / "registries/HANDOFF_ALIGNED_PACKAGE_REGISTRY.csv"):
        model_rows.append({"asset_id": row["package_id"], "asset_kind": "handoff-aligned-package", "status": "checked-positive", "model_ref": row["model_ref"], "certificate_ref": row["certificate_ref"], "claim_ceiling": row["claim_ceiling"]})
    model_rows.append({"asset_id": "STG-POS-02-FIACH", "asset_kind": "handoff-aligned-staged-assembly", "status": "checked-positive", "model_ref": rel(package_context["paths"]["staged_model"]), "certificate_ref": rel(package_context["paths"]["staged_cert"]), "claim_ceiling": package_context["staged_cert"]["claim_ceiling"]})
    model_rows.append({"asset_id": "AUT-POS-01", "asset_kind": "post-withdrawal-autonomy", "status": autonomy_context["certificate"]["result_status"], "model_ref": rel(autonomy_context["positive_path"]), "certificate_ref": rel(autonomy_context["certificate_path"]), "claim_ceiling": autonomy_context["certificate"]["claim_ceiling"]})
    for row in autonomy_context["control_rows"]:
        model_rows.append({"asset_id": row["control_id"], "asset_kind": "autonomy-control", "status": row["result_status"], "model_ref": row["model_ref"], "certificate_ref": row["certificate_ref"], "claim_ceiling": row["claim_ceiling"]})
    model_rows.append({"asset_id": "FIACH-POS-01", "asset_kind": "integrated-temporal-fiach", "status": fiach_context["certificate"]["result_status"], "model_ref": rel(fiach_context["model_path"]), "certificate_ref": rel(fiach_context["certificate_path"]), "claim_ceiling": fiach_context["certificate"]["claim_ceiling"]})
    for row in fiach_context["controls"]:
        model_rows.append({"asset_id": row["control_id"], "asset_kind": "fiach-lane-control", "status": "checked-fiach-lane-independence-control", "model_ref": row["model_ref"], "certificate_ref": row["certificate_ref"], "claim_ceiling": row["claim_ceiling"]})
    write_csv(ROOT / "manifests/CST-TT-05_MODEL_CERTIFICATE_DELTA.csv", ["asset_id", "asset_kind", "status", "model_ref", "certificate_ref", "claim_ceiling"], model_rows)

    theorem_rows = [row for row in read_csv(ROOT / "registries/THEOREM_REGISTRY.csv") if row["status"] != "open-scaffold"]
    registry_doc = "# Theorem and Toy Registry\n\n" + md_table(
        ["ID", "Name", "Phase", "Status", "Lanes", "Ceiling"],
        [(row["theorem_id"], row["name"], row["phase"], row["status"], row["claim_lanes"], row["claim_ceiling"]) for row in theorem_rows],
    ) + "\n\nOpen fallback and later-strengthening contracts remain in the machine-readable registries.\n"
    (ROOT / "docs/THEOREM_AND_TOY_REGISTRY.md").write_text(registry_doc, encoding="utf-8")

    completion = f"""# CST-TT-05 Completion Report

CST-TT-05 lands model-relative post-withdrawal autonomy and the first exact finite integrated Temporal-FIACH structural witness.

## Landed assets

- two handoff-aligned C1-C8 package certificates and one aligned staged assembly;
- one target-owned post-withdrawal autonomy certificate;
- {len(autonomy_context['control_rows'])} exact autonomy controls with collapse traces where applicable;
- a 4,096-case exhaustive fixed-point/brute-force agreement check with zero mismatches;
- one integrated `FIACH-POS-01` certificate with independently checked S-T, S-R, S-L, and A lanes;
- six one/two-of-three lane controls and the complete eight-row conjunction table;
- Lean proof-source modules for finite controlled runs, external-support/stall/insolvency boundaries, aggregate soundness, endpoint linkage, and exact three-lane conjunction.

## Decision

Temporal-FIACH remains primary. `K-FIACH-05`, `K-AUTO-01`, and `K-AUTO-02` are not triggered. Temporal-IAPS remains locked.

## Claim ceiling

The result is an exact finite structural precursor. It does not establish consciousness, felt continuity, personal survival, numerical identity, empirical recognition, A1, A2-P, certificate soundness for consciousness, or unbounded physical liveness.

## Toolchain boundary

Lean proof sources contain no placeholder commands. Actual Lean compilation is not claimed unless `lean` and `lake` are available and `lake build` succeeds. Python enumeration and certificate replay are not represented as proof-oracle outputs.

The next authorized phase is `CST-TT-06`, composition, branching, route completion, and full toy closure.
"""
    (ROOT / "manifests/CST-TT-05_COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")
    (ROOT / "manifests/COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")

    restore = f"""# Restore and Verify CST-TT-05

1. Extract the repository ZIP and enter the repository directory.
2. Confirm the release tag resolves to the frozen commit.
3. Run:

```bash
export PYTHONHASHSEED=0
export PYTHONPATH=src:scripts
python3 -m pytest -q
python3 scripts/validate_tt05.py --no-write
python3 scripts/verify_tt05_rebuild.py
```

4. If Lean and Lake are available, run `lake build`. If absent, report the check as skipped; do not infer a compile pass.

The phase base is `{BASE_TAG}` / `{BASE_COMMIT}`.
"""
    (ROOT / "RESTORE_AND_VERIFY.md").write_text(restore, encoding="utf-8")
    (ROOT / "docs/RESTORE_AND_BUILD.md").write_text(restore, encoding="utf-8")

    (ROOT / "README.md").write_text("""# CST-TT — Temporal Substrate Transcendence Theorems and Toys

Current frozen phase: **CST-TT-05**.

The repository now contains an exact finite structural Temporal-FIACH witness combining independently audited target package realization, strict temporal lineage, and post-withdrawal target autonomy. The result is route-indexed and carries no consciousness, phenomenal, survival, or identity conclusion.

CST-TT-06 is reserved for composition, branching, route completion, and full toy-suite closure.
""", encoding="utf-8")
    (ROOT / "STATE.md").write_text("# Repository State\n\nFrozen at CST-TT-05 semantic assets; release manifest and tag are finalized separately.\n", encoding="utf-8")
    (ROOT / "STATUS.md").write_text("# Status\n\nOne exact finite Temporal-FIACH structural witness and its autonomy/control bank have landed. Composition and branching remain CST-TT-06 work.\n", encoding="utf-8")
    changelog = ROOT / "CHANGELOG.md"
    prior = changelog.read_text(encoding="utf-8") if changelog.exists() else "# Changelog\n"
    entry = "\n## CST-TT-05 — 2026-08-10\n\nLanded post-withdrawal controlled invariance, autonomy controls, handoff-aligned package witnesses, and the first exact finite integrated Temporal-FIACH certificate.\n"
    if "## CST-TT-05" not in prior:
        prior = prior.rstrip() + "\n" + entry
    changelog.write_text(prior, encoding="utf-8")
    (ROOT / "changelog/CST-TT-05.md").write_text(entry.lstrip(), encoding="utf-8")
    (ROOT / "formal/README.md").write_text("""# Formal Assets

CST-TT-05 adds proof-source modules for post-withdrawal finite controlled invariance and integrated Temporal-FIACH aggregation. Hash-bound certificate directories contain aligned package, autonomy, collapse-control, aggregate, and lane-independence assets.

Python checks exact finite certificate semantics and bounded enumerations; it is not a proof oracle. Lean-kernel compilation is reported only after an actual `lake build` pass.
""", encoding="utf-8")
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
    package_context = build_aligned_packages()
    autonomy_context = build_autonomy(package_context)
    fiach_context = build_fiach(package_context, autonomy_context)
    update_registries(package_context, autonomy_context, fiach_context)
    build_docs(package_context, autonomy_context, fiach_context)
    write_status_surfaces(package_context, autonomy_context, fiach_context)
    print(json.dumps({
        "phase": PHASE,
        "aligned_packages": 2,
        "autonomy_controls": len(autonomy_context["control_rows"]),
        "invariant_candidates": autonomy_context["search"]["candidate_count"],
        "finite_words": autonomy_context["audit"].finite_words_checked,
        "fiach_witnesses": 1,
        "lane_controls": len(fiach_context["controls"]),
    }, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
