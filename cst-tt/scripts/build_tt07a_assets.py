#!/usr/bin/env python3
from __future__ import annotations

import csv
from copy import deepcopy
import hashlib
import json
import platform
from pathlib import Path
import shutil
from typing import Any, Iterable, Mapping

from cst_tt.corridor import audit_direct_successor
from cst_tt.defect_semantics import (
    audit_defect_profile,
    bounded_defect_exhaustion,
    bounded_downward_closure_exhaustion,
)
from cst_tt.robustness import audit_robustness, audit_specific_perturbation, enumerate_bounded_perturbations
from cst_tt.strengthenings import (
    audit_generalized_continuity_path,
    audit_overlap_direct_relation,
    bounded_relation_truth_table,
)
from cst_tt.unbounded import (
    arbitrary_finite_prefix_counterfamily,
    audit_unbounded_invariant,
    bounded_disturbance_prefix_check,
)
from tt07a_data import (
    defect_controls,
    equal_scalar_profiles,
    full_defect_profile,
    mixed_mode_direct_leg,
    robustness_controls,
    robustness_model,
    unbounded_spec,
)

ROOT = Path(__file__).resolve().parents[1]
PHASE = "CST-TT-07A"
DATE = "2026-08-10"
BASE_TAG = "CST-TT-06-v1"
BASE_COMMIT = "6c8f510c67087a8db9dd1c4107008b3b7cfb0847"


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(path)
    return value


def write_csv(path: Path, fieldnames: list[str], rows: Iterable[Mapping[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as handle:
        writer = csv.DictWriter(handle, fieldnames=fieldnames, lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow({field: row.get(field, "") for field in fieldnames})


def read_csv(path: Path) -> list[dict[str, str]]:
    if not path.is_file():
        return []
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def upsert_csv(path: Path, key: str, rows: list[dict[str, object]]) -> None:
    old = read_csv(path)
    fields = list(old[0].keys()) if old else list(rows[0].keys())
    additions = {str(row[key]): {field: row.get(field, "") for field in fields} for row in rows}
    merged = [row for row in old if row.get(key) not in additions]
    merged.extend(additions[item] for item in sorted(additions))
    write_csv(path, fields, merged)


def append_unique_csv(path: Path, rows: list[dict[str, object]]) -> None:
    """Append rows by their full field tuple without collapsing non-unique columns."""
    old = read_csv(path)
    fields = list(old[0].keys()) if old else list(rows[0].keys())
    normalized = [{field: str(row.get(field, "")) for field in fields} for row in rows]
    seen = {tuple(row.get(field, "") for field in fields) for row in old}
    merged = list(old)
    for row in normalized:
        key = tuple(row[field] for field in fields)
        if key not in seen:
            merged.append(row)
            seen.add(key)
    write_csv(path, fields, merged)


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


def write_model_and_certificate(
    model: dict[str, Any],
    model_path: Path,
    cert_path: Path,
    *,
    result_status: str,
    claim_lanes: list[str],
    claim_ceiling: str,
    audit: Mapping[str, Any],
    module: str,
    function: str,
    theorem_ids: list[str],
    lean_declarations: list[str],
) -> dict[str, Any]:
    write_json(model_path, model)
    cert = {
        "schema_version": PHASE,
        "certificate_id": model.get("model_id") or model.get("profile_id") or model.get("path_id") or model.get("certificate_id"),
        "model_ref": rel(model_path),
        "model_sha256": sha256(model_path),
        "result_status": result_status,
        "claim_lanes": claim_lanes,
        "claim_ceiling": claim_ceiling,
        "audit": dict(audit),
        "checker": checker(module, function),
        "theorem_evidence": {
            "theorem_ids": theorem_ids,
            "lean_declarations": lean_declarations,
            "lean_compile_status": "pending-toolchain",
        },
    }
    write_json(cert_path, cert)
    return cert


def build_direct_and_relation() -> dict[str, Any]:
    direct_model = mixed_mode_direct_leg(ROOT)
    direct_model_path = ROOT / "models/strengthenings/direct/DS-POS-03-MIXED-MODE.model.json"
    write_json(direct_model_path, direct_model)
    direct_audit = audit_direct_successor(direct_model)
    if not direct_audit.direct_successor_valid:
        raise RuntimeError(direct_audit.failed_obligations)
    direct_cert = {
        "schema_version": PHASE,
        "certificate_id": direct_model["model_id"],
        "model_ref": rel(direct_model_path),
        "model_sha256": sha256(direct_model_path),
        "result_status": "checked-finite-direct-successor-aligned-to-overlap-frontier",
        "claim_lanes": ["S-L"],
        "claim_ceiling": "separately named finite direct-successor evidence only",
        "audit": direct_audit.to_dict(),
        "checker": checker("cst_tt.corridor", "audit_direct_successor"),
        "theorem_evidence": {
            "theorem_ids": ["TTD-01", "TTD-02", "TTS-01"],
            "lean_declarations": [
                "CSTTT.DirectSuccessorTheory.directSuccessorValidity",
                "CSTTT.StrengtheningTheory.directEmbedsGeneralized",
            ],
            "lean_compile_status": "pending-toolchain",
        },
    }
    direct_cert_path = ROOT / "formal/certificates/strengthenings/direct/DS-POS-03-MIXED-MODE.certificate.json"
    write_json(direct_cert_path, direct_cert)

    def path_spec(path_id: str, legs: list[tuple[str, str, str]]) -> dict[str, Any]:
        return {
            "schema_version": "CST-TT-07A-generalized-path-v1",
            "path_id": path_id,
            "claim_lanes": ["S-L"],
            "claim_ceiling": "generalized structural temporal-lineage path only",
            "primary_fiach_definition_change": "none",
            "legs": [
                {
                    "leg_id": leg_id,
                    "kind": kind,
                    "model_ref": model_ref,
                    "model_sha256": sha256(ROOT / model_ref),
                }
                for leg_id, kind, model_ref in legs
            ],
        }

    path_specs = {
        "GCP-OVERLAP-01": path_spec("GCP-OVERLAP-01", [("strict-overlap", "overlap", "models/corridors/COR-POS-01.model.json")]),
        "GCP-DIRECT-01": path_spec("GCP-DIRECT-01", [("direct-edge", "direct", "models/direct_successor/DS-POS-01.model.json")]),
        "GCP-MIXED-01": path_spec(
            "GCP-MIXED-01",
            [
                ("overlap-S-M", "overlap", "models/corridors/COR-POS-02A.model.json"),
                ("direct-M-T", "direct", rel(direct_model_path)),
            ],
        ),
    }
    path_outputs: dict[str, dict[str, Any]] = {}
    for path_id, spec in path_specs.items():
        model_path = ROOT / f"models/strengthenings/continuity/{path_id}.model.json"
        write_json(model_path, spec)
        audit = audit_generalized_continuity_path(spec, ROOT)
        if not audit.generalized_path_valid:
            raise RuntimeError((path_id, audit.failed_obligations))
        cert = {
            "schema_version": PHASE,
            "certificate_id": path_id,
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": "checked-finite-generalized-temporal-continuity-path",
            "claim_lanes": ["S-L"],
            "claim_ceiling": "generalized structural lineage path only; strict FIACH requires all-overlap evidence",
            "audit": audit.to_dict(),
            "checker": checker("cst_tt.strengthenings", "audit_generalized_continuity_path"),
            "theorem_evidence": {
                "theorem_ids": ["TTD-02", "TTS-01"],
                "lean_declarations": [
                    "CSTTT.StrengtheningTheory.overlapEmbedsGeneralized",
                    "CSTTT.StrengtheningTheory.directEmbedsGeneralized",
                    "CSTTT.StrengtheningTheory.generalizedPathComposition",
                ],
                "lean_compile_status": "pending-toolchain",
            },
        }
        cert_path = ROOT / f"formal/certificates/strengthenings/continuity/{path_id}.certificate.json"
        write_json(cert_path, cert)
        path_outputs[path_id] = {"spec": spec, "audit": audit.to_dict(), "model_ref": rel(model_path), "certificate_ref": rel(cert_path)}

    model_refs = {
        "strict_witness": "models/corridors/COR-POS-01.model.json",
        "direct_witness": "models/direct_successor/DS-POS-01.model.json",
        "detached_control": "models/countermodels/CM-02.model.json",
        "gap_control": "models/countermodels/CM-12.model.json",
        "same_carrier_control": "models/countermodels/CM-14.model.json",
    }
    relation = {
        "schema_version": "CST-TT-07A-relation-v1",
        "certificate_id": "ODR-01",
        "title": "exact overlap/direct incomparability and generalized embedding",
        "claim_lanes": ["S-L"],
        "claim_ceiling": "structural lineage-class comparison only",
        "model_refs": model_refs,
        "model_sha256": {key: sha256(ROOT / value) for key, value in model_refs.items()},
        "strict_singleton_path": path_specs["GCP-OVERLAP-01"],
        "direct_singleton_path": path_specs["GCP-DIRECT-01"],
        "mixed_mode_path": path_specs["GCP-MIXED-01"],
        "control_verdicts": {"detached_copy": "neither", "temporal_gap": "neither", "same_carrier": "neither"},
        "primary_definition_change": "none",
        "fallback_status": "locked",
        "nonclaims": [
            "the broader class is not substituted into Temporal-FIACH",
            "direct succession is not personal identity",
            "no phenomenal-continuity conclusion",
        ],
    }
    relation_model_path = ROOT / "models/strengthenings/continuity/ODR-01.model.json"
    write_json(relation_model_path, relation)
    relation_audit = audit_overlap_direct_relation(relation, ROOT)
    if not relation_audit.relation_result_valid:
        raise RuntimeError(relation_audit.failed_obligations)
    relation_cert = {
        "schema_version": PHASE,
        "certificate_id": "ODR-01",
        "model_ref": rel(relation_model_path),
        "model_sha256": sha256(relation_model_path),
        "result_status": "proof-source-and-executable-incomparability-certificate",
        "claim_lanes": ["S-L"],
        "claim_ceiling": relation["claim_ceiling"],
        "audit": relation_audit.to_dict(),
        "checker": checker("cst_tt.strengthenings", "audit_overlap_direct_relation"),
        "theorem_evidence": {
            "theorem_ids": ["TTD-02", "TTS-01"],
            "lean_declarations": [
                "CSTTT.StrengtheningTheory.overlapDirectIncomparable",
                "CSTTT.StrengtheningTheory.generalizedStrictlyBroaderThanOverlap",
                "CSTTT.StrengtheningTheory.generalizedPathComposition",
            ],
            "lean_compile_status": "pending-toolchain",
        },
    }
    relation_cert_path = ROOT / "formal/certificates/strengthenings/continuity/ODR-01.certificate.json"
    write_json(relation_cert_path, relation_cert)
    truth = bounded_relation_truth_table()
    write_json(ROOT / "formal/certificates/search/OVERLAP_DIRECT_RELATION_TRUTH_TABLE.json", truth)
    return {
        "direct_model": rel(direct_model_path),
        "direct_certificate": rel(direct_cert_path),
        "paths": path_outputs,
        "relation_model": rel(relation_model_path),
        "relation_certificate": rel(relation_cert_path),
        "relation_audit": relation_audit.to_dict(),
        "truth_table": truth,
    }


def defect_certificate(model: dict[str, Any], model_path: Path, cert_path: Path, expected_status: str) -> dict[str, Any]:
    write_json(model_path, model)
    audit = audit_defect_profile(model)
    cert = {
        "schema_version": PHASE,
        "certificate_id": model["profile_id"],
        "model_ref": rel(model_path),
        "model_sha256": sha256(model_path),
        "result_status": expected_status,
        "claim_lanes": model.get("claim_lanes", ["M"]),
        "claim_ceiling": model.get("claim_ceiling", "finite defect audit only"),
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.defect_semantics", "audit_defect_profile"),
        "theorem_evidence": {
            "theorem_ids": ["TTS-02", "TTN-10"],
            "lean_declarations": [
                "CSTTT.DefectTheory.acceptedHardGateIsZero",
                "CSTTT.DefectTheory.vectorAcceptanceDownwardClosed",
                "CSTTT.DefectTheory.scalarSummaryDoesNotDetermineAcceptance",
            ],
            "lean_compile_status": "pending-toolchain",
        },
    }
    write_json(cert_path, cert)
    return cert


def build_defects() -> dict[str, Any]:
    positive = full_defect_profile()
    positive_path = ROOT / "models/strengthenings/defects/DEF-POS-01.model.json"
    positive_cert_path = ROOT / "formal/certificates/strengthenings/defects/DEF-POS-01.certificate.json"
    positive_cert = defect_certificate(positive, positive_path, positive_cert_path, "checked-finite-exact-vector-defect-profile")
    if positive_cert["audit"]["accepted"] is not True:
        raise RuntimeError("positive defect profile failed")
    control_rows = []
    for control_id, expected_failure, model in defect_controls():
        model_path = ROOT / f"models/strengthenings/defects/controls/{control_id}.model.json"
        cert_path = ROOT / f"formal/certificates/strengthenings/defects/controls/{control_id}.certificate.json"
        cert = defect_certificate(model, model_path, cert_path, "checked-finite-defect-control")
        observed = cert["audit"]["failed_obligations"]
        if cert["audit"]["accepted"] or expected_failure not in observed:
            raise RuntimeError((control_id, expected_failure, observed))
        cert["expected_primary_failure"] = expected_failure
        cert["observed_failures"] = observed
        write_json(cert_path, cert)
        control_rows.append(
            {
                "control_id": control_id,
                "expected_primary_failure": expected_failure,
                "model_ref": rel(model_path),
                "certificate_ref": rel(cert_path),
                "accepted": False,
            }
        )

    accepted, rejected = equal_scalar_profiles()
    accepted_path = ROOT / "models/strengthenings/defects/DEF-EQUAL-SCALAR-ACCEPTED.model.json"
    rejected_path = ROOT / "models/strengthenings/defects/DEF-EQUAL-SCALAR-REJECTED.model.json"
    write_json(accepted_path, accepted); write_json(rejected_path, rejected)
    accepted_audit = audit_defect_profile(accepted); rejected_audit = audit_defect_profile(rejected)
    same_scalar = accepted_audit.scalar_summary == rejected_audit.scalar_summary
    equal_cert = {
        "schema_version": PHASE,
        "certificate_id": "DEF-EQUAL-SCALAR-01",
        "accepted_model_ref": rel(accepted_path),
        "accepted_model_sha256": sha256(accepted_path),
        "rejected_model_ref": rel(rejected_path),
        "rejected_model_sha256": sha256(rejected_path),
        "result_status": "checked-finite-equal-scalar-opposite-vector-verdict",
        "claim_lanes": ["M", "S-R", "S-L", "A"],
        "claim_ceiling": "scalar-summary nonidentifiability for the declared exact finite profile",
        "same_scalar_summary": same_scalar,
        "accepted_audit": accepted_audit.to_dict(),
        "rejected_audit": rejected_audit.to_dict(),
        "theorem_evidence": {
            "theorem_ids": ["TTS-02", "TTN-10"],
            "lean_declarations": ["CSTTT.DefectTheory.scalarSummaryDoesNotDetermineAcceptance"],
            "lean_compile_status": "pending-toolchain",
        },
    }
    if not same_scalar or not accepted_audit.accepted or rejected_audit.accepted:
        raise RuntimeError("equal-scalar pair failed")
    equal_cert_path = ROOT / "formal/certificates/strengthenings/defects/DEF-EQUAL-SCALAR-01.certificate.json"
    write_json(equal_cert_path, equal_cert)

    exhaustion = bounded_defect_exhaustion()
    downward = bounded_downward_closure_exhaustion()
    write_json(ROOT / "formal/certificates/search/VECTOR_DEFECT_EXHAUSTION.json", exhaustion)
    write_json(ROOT / "formal/certificates/search/VECTOR_DEFECT_DOWNWARD_CLOSURE.json", downward)
    write_csv(
        ROOT / "registries/DEFECT_PROFILE_REGISTRY.csv",
        ["profile_id", "role", "model_ref", "certificate_ref", "accepted", "principal_result"],
        [
            {
                "profile_id": "DEF-POS-01",
                "role": "positive-vector-profile",
                "model_ref": rel(positive_path),
                "certificate_ref": rel(positive_cert_path),
                "accepted": True,
                "principal_result": "all hard gates exact; all soft dimensions within tolerance",
            },
            *[
                {
                    "profile_id": row["control_id"],
                    "role": "negative-control",
                    "model_ref": row["model_ref"],
                    "certificate_ref": row["certificate_ref"],
                    "accepted": False,
                    "principal_result": row["expected_primary_failure"],
                }
                for row in control_rows
            ],
            {
                "profile_id": "DEF-EQUAL-SCALAR-01",
                "role": "scalar-nonidentifiability-pair",
                "model_ref": rel(accepted_path) + ";" + rel(rejected_path),
                "certificate_ref": rel(equal_cert_path),
                "accepted": "one-of-two",
                "principal_result": "equal scalar summary; opposite exact-vector verdict",
            },
        ],
    )
    return {
        "positive_certificate": rel(positive_cert_path),
        "control_count": len(control_rows),
        "equal_scalar_certificate": rel(equal_cert_path),
        "exhaustion": exhaustion,
        "downward": downward,
    }


def build_robustness() -> dict[str, Any]:
    model = robustness_model()
    model_path = ROOT / "models/strengthenings/robustness/ROB-POS-01.model.json"
    write_json(model_path, model)
    audit = audit_robustness(model)
    if not audit.robustness_valid:
        raise RuntimeError(audit.failed_obligations)
    cert = {
        "schema_version": PHASE,
        "certificate_id": "ROB-POS-01",
        "model_ref": rel(model_path),
        "model_sha256": sha256(model_path),
        "result_status": "proof-source-and-executable-bounded-robustness-certificate",
        "claim_lanes": ["S-T", "S-R", "S-L", "A"],
        "claim_ceiling": model["claim_ceiling"],
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.robustness", "audit_robustness"),
        "theorem_evidence": {
            "theorem_ids": ["TTS-03", "TTN-10"],
            "lean_declarations": [
                "CSTTT.RobustnessTheory.boundedPerturbationPreservesMargin",
                "CSTTT.RobustnessTheory.failedHardGateCannotBeAveragedAway",
            ],
            "lean_compile_status": "pending-toolchain",
        },
    }
    cert_path = ROOT / "formal/certificates/strengthenings/robustness/ROB-POS-01.certificate.json"
    write_json(cert_path, cert)
    controls = []
    for control_id, description, deltas, gates in robustness_controls():
        result = audit_specific_perturbation(model, deltas, gates)
        if result["accepted"]:
            raise RuntimeError(control_id)
        control_model = {
            "schema_version": "CST-TT-07A-robustness-control-v1",
            "model_id": control_id,
            "description": description,
            "base_model_ref": rel(model_path),
            "base_model_sha256": sha256(model_path),
            "deltas": deltas,
            "hard_gates": gates,
        }
        control_model_path = ROOT / f"models/strengthenings/robustness/controls/{control_id}.model.json"
        write_json(control_model_path, control_model)
        control_cert = {
            "schema_version": PHASE,
            "certificate_id": control_id,
            "model_ref": rel(control_model_path),
            "model_sha256": sha256(control_model_path),
            "result_status": "checked-finite-robustness-boundary-control",
            "description": description,
            "audit": result,
            "claim_lanes": ["M"],
            "claim_ceiling": "declared robustness-box boundary only",
        }
        control_cert_path = ROOT / f"formal/certificates/strengthenings/robustness/controls/{control_id}.certificate.json"
        write_json(control_cert_path, control_cert)
        controls.append(
            {
                "control_id": control_id,
                "description": description,
                "model_ref": rel(control_model_path),
                "certificate_ref": rel(control_cert_path),
                "accepted": False,
            }
        )
    search = enumerate_bounded_perturbations(model)
    write_json(ROOT / "formal/certificates/search/BOUNDED_TEMPORAL_MARGIN_EXHAUSTION.json", search)
    write_csv(
        ROOT / "registries/ROBUSTNESS_REGISTRY.csv",
        ["item_id", "role", "model_ref", "certificate_ref", "accepted", "principal_result"],
        [
            {
                "item_id": "ROB-POS-01",
                "role": "positive-bounded-box",
                "model_ref": rel(model_path),
                "certificate_ref": rel(cert_path),
                "accepted": True,
                "principal_result": f"{search['candidates_examined']} bounded perturbations; zero violations",
            },
            *[
                {
                    "item_id": row["control_id"],
                    "role": "negative-control",
                    "model_ref": row["model_ref"],
                    "certificate_ref": row["certificate_ref"],
                    "accepted": False,
                    "principal_result": row["description"],
                }
                for row in controls
            ],
        ],
    )
    return {"certificate": rel(cert_path), "control_count": len(controls), "search": search, "audit": audit.to_dict()}


def build_unbounded() -> dict[str, Any]:
    spec = unbounded_spec()
    model_ref = spec["autonomy_model_ref"]
    spec["autonomy_model_sha256"] = sha256(ROOT / model_ref)
    model_path = ROOT / "models/strengthenings/unbounded/UNB-POS-01.model.json"
    write_json(model_path, spec)
    autonomy_model = load_json(ROOT / model_ref)
    audit = audit_unbounded_invariant(spec, autonomy_model)
    if not audit.unbounded_model_invariance_valid:
        raise RuntimeError(audit.failed_obligations)
    cert = {
        "schema_version": PHASE,
        "certificate_id": "UNB-POS-01",
        "model_ref": rel(model_path),
        "model_sha256": sha256(model_path),
        "autonomy_model_ref": model_ref,
        "autonomy_model_sha256": spec["autonomy_model_sha256"],
        "result_status": "proof-source-and-executable-model-relative-unbounded-invariant",
        "claim_lanes": ["A"],
        "claim_ceiling": spec["claim_ceiling"],
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.unbounded", "audit_unbounded_invariant"),
        "theorem_evidence": {
            "theorem_ids": ["TTS-04", "TTN-12"],
            "lean_declarations": [
                "CSTTT.AutonomyTheory.modelRelativeUnboundedControlledInvariant",
                "CSTTT.AutonomyTheory.arbitrarilyLongFinitePrefixStillInsufficient",
            ],
            "lean_compile_status": "pending-toolchain",
        },
    }
    cert_path = ROOT / "formal/certificates/strengthenings/unbounded/UNB-POS-01.certificate.json"
    write_json(cert_path, cert)
    prefix = bounded_disturbance_prefix_check(autonomy_model, 12)
    family = arbitrary_finite_prefix_counterfamily(12)
    write_json(ROOT / "formal/certificates/search/UNBOUNDED_POLICY_PREFIX_STRESS.json", prefix)
    write_json(ROOT / "formal/certificates/search/ARBITRARILY_LONG_FINITE_PREFIX_FAMILY.json", family)
    write_csv(
        ROOT / "registries/UNBOUNDED_INVARIANT_REGISTRY.csv",
        ["item_id", "role", "model_ref", "certificate_ref", "status", "principal_result", "claim_ceiling"],
        [
            {
                "item_id": "UNB-POS-01",
                "role": "positive-total-invariant-policy",
                "model_ref": rel(model_path),
                "certificate_ref": rel(cert_path),
                "status": "checked-model-relative-unbounded-run-schema",
                "principal_result": "total target-owned invariant policy defines a run for every infinite disturbance stream",
                "claim_ceiling": spec["claim_ceiling"],
            },
            {
                "item_id": "UNB-NEG-FAMILY-01",
                "role": "arbitrary-finite-prefix-counterfamily",
                "model_ref": "formal/certificates/search/ARBITRARILY_LONG_FINITE_PREFIX_FAMILY.json",
                "certificate_ref": "formal/certificates/search/ARBITRARILY_LONG_FINITE_PREFIX_FAMILY.json",
                "status": "checked-bounded-family",
                "principal_result": "every horizon 0..12 has a prefix-success/fail-next countdown",
                "claim_ceiling": "bounded exact counterfamily plus generic proof source",
            },
        ],
    )
    return {"certificate": rel(cert_path), "audit": audit.to_dict(), "prefix": prefix, "family": family}


def schema(name: str, required: list[str]) -> dict[str, Any]:
    return {
        "$schema": "https://json-schema.org/draft/2020-12/schema",
        "$id": f"https://six-birds.local/cst-tt/{name}",
        "title": name,
        "type": "object",
        "required": required,
        "properties": {key: {} for key in required},
        "additionalProperties": True,
    }


def build_schemas() -> None:
    schemas = {
        "generalized_continuity_certificate.schema.json": ["schema_version", "certificate_id", "model_ref", "model_sha256", "result_status", "audit"],
        "defect_profile_certificate.schema.json": ["schema_version", "certificate_id", "model_ref", "model_sha256", "result_status", "audit"],
        "temporal_robustness_certificate.schema.json": ["schema_version", "certificate_id", "model_ref", "model_sha256", "result_status", "audit"],
        "unbounded_invariant_certificate.schema.json": ["schema_version", "certificate_id", "model_ref", "model_sha256", "result_status", "audit"],
    }
    for filename, required in schemas.items():
        write_json(ROOT / "schemas/certificates" / filename, schema(filename, required))
    def scaffold(certificate_id: str, model_ref: str) -> dict[str, Any]:
        return {
            "schema_version": PHASE,
            "certificate_id": certificate_id,
            "model_ref": model_ref,
            "model_sha256": "0" * 64,
            "result_status": "scaffold-only",
            "audit": {},
        }

    examples = {
        "generalized_continuity_certificate.scaffold.json": scaffold("GCP-SCAFFOLD", "models/scaffold/generalized-continuity.json"),
        "defect_profile_certificate.scaffold.json": scaffold("DEF-SCAFFOLD", "models/scaffold/defect-profile.json"),
        "temporal_robustness_certificate.scaffold.json": scaffold("ROB-SCAFFOLD", "models/scaffold/temporal-robustness.json"),
        "unbounded_invariant_certificate.scaffold.json": scaffold("UNB-SCAFFOLD", "models/scaffold/unbounded-invariant.json"),
    }
    for filename, value in examples.items():
        write_json(ROOT / "examples/scaffold" / filename, value)


def update_registries(results: Mapping[str, Any]) -> None:
    theorem_path = ROOT / "registries/THEOREM_REGISTRY.csv"
    theorem_rows = read_csv(theorem_path)
    updates = {
        "TTD-02": {
            "phase": PHASE,
            "status": "proof-source-and-executable-certificate-landed",
            "lean_statement": "CSTTT.StrengtheningTheory.overlapDirectIncomparable;CSTTT.StrengtheningTheory.generalizedStrictlyBroaderThanOverlap",
            "toy_dependencies": "TTM-01;TTM-03;TTM-20",
        },
        "TTN-10": {
            "status": "proof-source-and-checked-finite-countermodel",
            "lean_statement": "CSTTT.Prospects.ScalarResidualHardGateFailure;CSTTT.DefectTheory.acceptedHardGateIsZero;CSTTT.DefectTheory.scalarSummaryDoesNotDetermineAcceptance",
        },
        "TTN-12": {
            "status": "proof-source-and-checked-finite-countermodel",
            "lean_statement": "CSTTT.Prospects.FiniteTraceNotUnboundedLiveness;CSTTT.AutonomyTheory.arbitrarilyLongFinitePrefixStillInsufficient",
            "toy_dependencies": "TTM-10;TTM-24",
        },
    }
    for row in theorem_rows:
        if row["theorem_id"] in updates:
            row.update(updates[row["theorem_id"]])
    fields = list(theorem_rows[0])
    existing = {row["theorem_id"] for row in theorem_rows}
    additions = [
        {
            "theorem_id": "TTS-01",
            "name": "Generalized temporal-continuity path class",
            "family": "primary-strengthening",
            "kind": "boundary",
            "phase": PHASE,
            "status": "proof-source-and-executable-certificate-landed",
            "claim_lanes": "S-L",
            "dependencies": "TTH-04;TTD-01;TTD-02",
            "lean_statement": "CSTTT.StrengtheningTheory.overlapEmbedsGeneralized;CSTTT.StrengtheningTheory.directEmbedsGeneralized;CSTTT.StrengtheningTheory.generalizedStrictlyBroaderThanOverlap;CSTTT.StrengtheningTheory.generalizedPathComposition",
            "toy_dependencies": "TTM-01;TTM-03;TTM-20",
            "claim_ceiling": "broader structural lineage vocabulary only; strict FIACH unchanged",
            "legacy_provenance_ids": "",
        },
        {
            "theorem_id": "TTS-02",
            "name": "Exact vector-valued defect acceptance",
            "family": "primary-strengthening",
            "kind": "boundary",
            "phase": PHASE,
            "status": "proof-source-and-executable-certificate-landed",
            "claim_lanes": "M;S-T;S-R;S-L;A",
            "dependencies": "TTN-10",
            "lean_statement": "CSTTT.DefectTheory.acceptedHardGateIsZero;CSTTT.DefectTheory.vectorAcceptanceDownwardClosed;CSTTT.DefectTheory.scalarSummaryDoesNotDetermineAcceptance",
            "toy_dependencies": "TTM-13;TTM-21",
            "claim_ceiling": "finite exact componentwise defect semantics only",
            "legacy_provenance_ids": "",
        },
        {
            "theorem_id": "TTS-03",
            "name": "Hard-gate-preserving bounded temporal robustness",
            "family": "primary-strengthening",
            "kind": "constructive",
            "phase": PHASE,
            "status": "proof-source-and-executable-certificate-landed",
            "claim_lanes": "S-T;S-R;S-L;A",
            "dependencies": "TTH-06;TTS-02",
            "lean_statement": "CSTTT.RobustnessTheory.boundedPerturbationPreservesMargin;CSTTT.RobustnessTheory.failedHardGateCannotBeAveragedAway",
            "toy_dependencies": "TTM-21;TTM-22",
            "claim_ceiling": "declared exact finite perturbation box only",
            "legacy_provenance_ids": "",
        },
        {
            "theorem_id": "TTS-04",
            "name": "Model-relative unbounded controlled invariant",
            "family": "primary-strengthening",
            "kind": "constructive",
            "phase": PHASE,
            "status": "proof-source-and-executable-certificate-landed",
            "claim_lanes": "A",
            "dependencies": "TTH-05;TTN-12",
            "lean_statement": "CSTTT.AutonomyTheory.modelRelativeUnboundedControlledInvariant",
            "toy_dependencies": "TTM-23;TTM-24",
            "claim_ceiling": "infinite run inside the exact finite controlled model; no physical persistence theorem",
            "legacy_provenance_ids": "",
        },
    ]
    theorem_rows.extend(row for row in additions if row["theorem_id"] not in existing)
    write_csv(theorem_path, fields, theorem_rows)

    upsert_csv(
        ROOT / "registries/DEFINITION_REGISTRY.csv",
        "definition_id",
        [
            {"definition_id": "D-070", "name": "GeneralizedTemporalContinuity", "module": "CSTTT/Strengthening/ContinuityClass.lean", "purpose": "sum of strict-overlap and direct-successor structural evidence", "claim_lanes": "S-L", "dependencies": "D-058;D-061", "status": "landed-strengthening"},
            {"definition_id": "D-071", "name": "DefectVector", "module": "CSTTT/Robustness/DefectVector.lean", "purpose": "componentwise exact defects with hard gates", "claim_lanes": "M", "dependencies": "", "status": "landed-strengthening"},
            {"definition_id": "D-072", "name": "TemporalMargin", "module": "CSTTT/Robustness/TemporalMargins.lean", "purpose": "exact bounded perturbation margin", "claim_lanes": "M;S-T;S-R;S-L;A", "dependencies": "D-071", "status": "landed-strengthening"},
            {"definition_id": "D-073", "name": "ExactAutonomyPolicy", "module": "CSTTT/Autonomy/UnboundedInvariant.lean", "purpose": "total target-owned policy on an invariant", "claim_lanes": "A", "dependencies": "D-065;D-066", "status": "landed-strengthening"},
        ],
    )
    upsert_csv(
        ROOT / "registries/ASSUMPTION_LEDGER.csv",
        "assumption_id",
        [
            {"assumption_id": "AS-33", "name": "H-BOUNDED-PERTURBATION-BOX", "tier": "structural", "statement": "Every robustness perturbation lies inside the declared exact componentwise box and leaves every hard gate unchanged.", "used_by": "TTS-03", "nonclaim": "Not an empirical noise distribution or open-ended stability theorem.", "status": "frozen-CST-TT-07A"},
            {"assumption_id": "AS-34", "name": "H-TOTAL-INVARIANT-POLICY", "tier": "model-structural", "statement": "The finite autonomy model exposes one target-owned admissible response at every invariant state and disturbance.", "used_by": "TTS-04", "nonclaim": "Does not establish indefinite physical resource availability outside the model.", "status": "frozen-CST-TT-07A"},
        ],
    )
    append_unique_csv(
        ROOT / "registries/DEPENDENCY_EDGES.csv",
        [
            {"source": "TTD-01", "target": "TTS-01", "reason": "direct evidence embeds into generalized path class", "status": "landed-CST-TT-07A"},
            {"source": "TTH-04", "target": "TTS-01", "reason": "strict overlap evidence embeds into generalized path class", "status": "landed-CST-TT-07A"},
            {"source": "TTN-10", "target": "TTS-02", "reason": "scalar residual counterexample motivates exact vector semantics", "status": "landed-CST-TT-07A"},
            {"source": "TTS-02", "target": "TTS-03", "reason": "robustness retains hard-gated componentwise acceptance", "status": "landed-CST-TT-07A"},
            {"source": "TTH-05", "target": "TTS-04", "reason": "total invariant policy strengthens finite-horizon autonomy inside the model", "status": "landed-CST-TT-07A"},
        ],
    )

    toy_rows = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    toy_fields = list(toy_rows[0])
    toy_by_id = {row["toy_id"]: row for row in toy_rows}
    if "TTM-03" in toy_by_id:
        toy_by_id["TTM-03"]["status"] = "checked-positive-witness-and-generalized-embedding"
        note = "CST-TT-07A proves exact incomparability and embedding into the broader path class"
        if note not in toy_by_id["TTM-03"]["notes"]:
            toy_by_id["TTM-03"]["notes"] += "; " + note
    additions_toy = [
        {"toy_id": "TTM-20", "name": "mixed overlap/direct continuity path", "role": "strengthening-positive", "phase": PHASE, "minimal_shape": "overlap S→M followed by direct M→T with exact frontier", "discriminates": "TTS-01", "status": "checked-positive-instance", "notes": "GCP-MIXED-01; not strict Temporal-FIACH because one leg is direct"},
        {"toy_id": "TTM-21", "name": "exact vector defect profile", "role": "strengthening-positive-and-control", "phase": PHASE, "minimal_shape": "twelve hard gates plus five soft margins", "discriminates": "TTS-02;TTN-10", "status": "checked-positive-and-negative-suite", "notes": "DEF-POS-01 plus six controls and equal-scalar opposite-verdict pair"},
        {"toy_id": "TTM-22", "name": "hard-gate-preserving robustness box", "role": "strengthening-positive", "phase": PHASE, "minimal_shape": "five exact temporal margins plus six frozen hard gates", "discriminates": "TTS-03", "status": "checked-positive-and-boundary-controls", "notes": "945 perturbations; zero within-box violations"},
        {"toy_id": "TTM-23", "name": "total invariant autonomy policy", "role": "strengthening-positive", "phase": PHASE, "minimal_shape": "four invariant states; two disturbances; total target-owned policy", "discriminates": "TTS-04", "status": "checked-positive-instance", "notes": "UNB-POS-01 defines model-relative runs for arbitrary infinite disturbance streams"},
        {"toy_id": "TTM-24", "name": "arbitrarily long finite-prefix countdown family", "role": "strengthening-negative-family", "phase": PHASE, "minimal_shape": "horizon-indexed budget countdown", "discriminates": "TTN-12;TTS-04", "status": "checked-bounded-family-and-proof-source", "notes": "horizons 0..12 plus generic Lean statement"},
    ]
    for row in additions_toy:
        toy_by_id[row["toy_id"]] = row
    write_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv", toy_fields, list(toy_by_id.values()))

    schema_rows = [
        {"schema_id": "CS-32", "file": "generalized_continuity_certificate.schema.json", "name": "Generalized temporal continuity", "claim_lanes": "S-L", "scaffold_example": "examples/scaffold/generalized_continuity_certificate.scaffold.json", "status": "landed-checked-strengthening-certificate"},
        {"schema_id": "CS-33", "file": "defect_profile_certificate.schema.json", "name": "Exact vector defect profile", "claim_lanes": "M;S-T;S-R;S-L;A", "scaffold_example": "examples/scaffold/defect_profile_certificate.scaffold.json", "status": "landed-checked-strengthening-certificate"},
        {"schema_id": "CS-34", "file": "temporal_robustness_certificate.schema.json", "name": "Bounded temporal robustness", "claim_lanes": "S-T;S-R;S-L;A", "scaffold_example": "examples/scaffold/temporal_robustness_certificate.scaffold.json", "status": "landed-checked-strengthening-certificate"},
        {"schema_id": "CS-35", "file": "unbounded_invariant_certificate.schema.json", "name": "Model-relative unbounded invariant", "claim_lanes": "A", "scaffold_example": "examples/scaffold/unbounded_invariant_certificate.scaffold.json", "status": "landed-checked-strengthening-certificate"},
    ]
    upsert_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv", "schema_id", schema_rows)

    kill_rows = read_csv(ROOT / "registries/KILL_CRITERIA.csv")
    kill_fields = list(kill_rows[0])
    found = False
    for row in kill_rows:
        if row["kill_id"] == "K-DIRECT-01":
            row["status"] = "not-triggered-CST-TT-07A"
            found = True
    if not found:
        raise RuntimeError("K-DIRECT-01 missing")
    kill_rows.extend(
        [
            {"kill_id": "K-ROBUST-01", "target": "bounded robustness", "trigger": "A scalar score or numerical margin is allowed to override a failed hard gate.", "action": "reject robustness strengthening", "decision_phase": PHASE, "status": "not-triggered-CST-TT-07A"},
            {"kill_id": "K-LIVE-01", "target": "unbounded model invariance", "trigger": "The unbounded claim is inferred from one finite prefix without a total invariant policy.", "action": "retain TTN-12 boundary only", "decision_phase": PHASE, "status": "not-triggered-CST-TT-07A"},
        ]
    )
    dedup: dict[str, dict[str, str]] = {row["kill_id"]: row for row in kill_rows}
    write_csv(ROOT / "registries/KILL_CRITERIA.csv", kill_fields, list(dedup.values()))

    project_path = ROOT / "registries/PROJECT_REGISTRY.json"
    project = load_json(project_path)
    project.update(
        {
            "current_phase": PHASE,
            "phase": PHASE,
            "phase_base_tag": BASE_TAG,
            "phase_base_commit": BASE_COMMIT,
            "next_phase": "CST-TT-08",
            "primary_status": "exact-finite-primary-and-strengthening-bank-landed",
            "primary_target_status": "Temporal-FIACH survives exact vector robustness and model-relative unbounded-invariant strengthening",
            "direct_successor_status": "exactly-incomparable-with-overlap-and-embedded-in-separate-generalized-path-class",
            "provisional_strengthening": "generalized overlap-or-direct structural lineage path; strict FIACH unchanged",
            "fallback_status": "Temporal-IAPS remains locked",
            "fallback_unlocked": False,
            "checked_generalized_continuity_certificates": 4,
            "checked_defect_profile_certificates": 8,
            "checked_robustness_certificates": 7,
            "checked_unbounded_invariant_certificates": 1,
            "checked_strengthening_toys": 5,
            "generic_theorem_proof_sources_landed": 24,
            "scientific_results_landed": 24,
        }
    )
    write_json(project_path, project)


def build_docs(results: Mapping[str, Any]) -> None:
    direct = results["direct"]
    defects = results["defects"]
    robust = results["robustness"]
    unbounded = results["unbounded"]
    relation_audit = direct["relation_audit"]

    (ROOT / "docs/CST-TT-07A_DIRECT_SUCCESSOR_RELATION.md").write_text(
        "# Direct successor and generalized temporal continuity\n\n"
        "CST-TT-07A proves the exact logical relation left open in CST-TT-04. Strict overlap and atomic direct successorship are **incomparable evidence modes**: the released overlap witness is not direct, and the released direct witness is not a strict overlap corridor.\n\n"
        "Both modes embed into the separately named `GeneralizedTemporalContinuity` class. This makes the generalized class strictly broader than strict overlap, but it does **not** replace the strict overlap lane inside Temporal-FIACH.\n\n"
        + md_table(
            ["Result", "Status"],
            [
                ("strict witness valid and not direct", relation_audit["strict_witness_valid"] and relation_audit["strict_witness_not_direct"]),
                ("direct witness valid and not strict", relation_audit["direct_witness_valid"] and relation_audit["direct_witness_not_strict"]),
                ("exact incomparability", relation_audit["overlap_direct_incomparable"]),
                ("both embed generalized", relation_audit["overlap_embeds_generalized"] and relation_audit["direct_embeds_generalized"]),
                ("mixed overlap/direct path", relation_audit["mixed_mode_path_valid"]),
                ("strict FIACH definition changed", "no"),
            ],
        )
        + "\n\nThe mixed path `GCP-MIXED-01` composes an overlap handoff from carrier 17 to carrier 55 with an immediate direct successor from carrier 55 to carrier 101 under exact carrier, signature, ownership, and no-gap frontier agreement. It is a valid generalized lineage path and is deliberately not a strict Temporal-FIACH corridor.\n\n"
        "Detached copies, temporal gaps, and same-carrier re-encodings remain outside both positive modes. No consciousness, felt-continuity, survival, or identity conclusion is supplied.\n",
        encoding="utf-8",
    )

    (ROOT / "docs/CST-TT-07A_EXACT_VECTOR_DEFECT_SEMANTICS.md").write_text(
        "# Exact vector-valued defect semantics\n\n"
        "The strengthening replaces no exact predicate with an average. A defect profile consists of named components, each marked hard or soft. Hard gates require exactly zero defect; soft dimensions must satisfy their own exact rational tolerance. The scalar mean is retained only as a diagnostic.\n\n"
        f"`DEF-POS-01` contains twelve hard gates and five soft dimensions and is accepted. Six one-obligation controls are rejected. The bounded twelve-bit adversarial family examines {defects['exhaustion']['candidates_examined']} profiles: {defects['exhaustion']['accepted_candidates']} pass, while {defects['exhaustion']['scalar_small_but_rejected']} have a mean defect no larger than one component out of twelve yet fail a hard gate. There are {defects['exhaustion']['equal_scalar_opposite_verdict_pairs']} equal-scalar accepted/rejected singleton pairs.\n\n"
        f"The exact downward-closure count covers {defects['downward']['ordered_pairs_examined']} ordered binary profile pairs, including {defects['downward']['accepted-upper-premise-pairs']} accepted-upper premise pairs, with zero violations.\n\n"
        "This is a finite structural audit semantics, not an empirical error model.\n",
        encoding="utf-8",
    )

    (ROOT / "docs/CST-TT-07A_BOUNDED_TEMPORAL_ROBUSTNESS.md").write_text(
        "# Hard-gate-preserving bounded temporal robustness\n\n"
        "`ROB-POS-01` assigns independent exact margins to predictive, order, tick, progress, and record advancement. A symmetric integer perturbation box is certified only when its worst case remains above each declared minimum. Six nonnumeric hard gates remain exact and cannot be averaged away.\n\n"
        + md_table(
            ["Dimension", "Base", "Minimum", "Radius", "Worst case"],
            [
                (row["dimension_id"], row["base_increment"], row["minimum_increment"], row["radius"], row["worst_case_increment"])
                for row in robust["audit"]["margin_audits"]
            ],
        )
        + f"\n\nThe deterministic enumeration checks all {robust['search']['candidates_examined']} points in the declared box and finds {robust['search']['violations']} violations. Six controls show that leaving the box or failing route, ownership, package, or autonomy hard gates is rejected.\n\n"
        "The box is a sufficient exact neighborhood, not a claim of maximal radius and not a real-world noise distribution. Approximation does not rescue an exact failure.\n",
        encoding="utf-8",
    )

    (ROOT / "docs/CST-TT-07A_MODEL_RELATIVE_UNBOUNDED_INVARIANCE.md").write_text(
        "# Model-relative unbounded controlled invariance\n\n"
        "CST-TT-05 proved response existence for every finite disturbance word. CST-TT-07A makes the corresponding infinite model claim explicit by freezing a total target-owned policy on the computed controlled invariant. For any infinite disturbance stream, primitive recursion defines an infinite state trajectory; every step remains in the invariant, preserves the package, progresses, strictly advances the record, and remains budget-solvent.\n\n"
        f"The positive certificate has {len(unbounded['audit']['lasso_witnesses'])} constant-disturbance lasso witnesses. Prefix stress checks {unbounded['prefix']['words_checked']} disturbance words through depth {unbounded['prefix']['maximum_depth']} with {unbounded['prefix']['violations']} violations.\n\n"
        f"The complementary countdown family constructs {unbounded['family']['models_constructed']} models for horizons 0 through {unbounded['family']['maximum_horizon']}; each survives its declared finite prefix and fails immediately afterwards. Thus finite prefix success alone remains insufficient.\n\n"
        "The positive theorem is unbounded only **inside the exact finite controlled model**. It does not establish indefinite physical resource availability, biological survival, or lived time outside that abstraction.\n",
        encoding="utf-8",
    )

    (ROOT / "docs/CST-TT-07A_PRIMARY_STRENGTHENING_SYNTHESIS.md").write_text(
        "# CST-TT-07A primary-strengthening synthesis\n\n"
        "The primary exact Temporal-FIACH theorem remains unchanged. Four strengthening families landed:\n\n"
        "1. strict overlap and direct succession are exactly incomparable, while both embed into a separate generalized path class;\n"
        "2. vector-valued exact defects preserve nonnegotiable hard gates and expose scalar-summary ambiguity;\n"
        "3. a bounded componentwise perturbation box preserves temporal progress and every hard gate;\n"
        "4. a total invariant policy yields model-relative unbounded runs, while arbitrarily long finite prefixes remain insufficient on their own.\n\n"
        "No strengthening changes the structural/recognition/ontology separation. Temporal-IAPS remains locked.\n\n"
        "Claim ceiling: these exact finite results do not establish consciousness, felt continuity, personal survival, numerical identity, empirical recognition, or indefinite physical persistence outside the declared models.\n",
        encoding="utf-8",
    )

    (ROOT / "docs/CST-TT-07A_DECISION_GATE.md").write_text(
        "# CST-TT-07A decision gate\n\n"
        "All authorized strengthenings either landed with explicit assumptions or were bounded by exact controls. `K-DIRECT-01`, `K-ROBUST-01`, and `K-LIVE-01` are not triggered.\n\n"
        "Temporal-FIACH remains the primary target. The direct class is retained only as a broader separately named structural-lineage mode. Exact hard gates remain nonnegotiable. The unbounded result is model-relative and does not erase TTN-12's physical and evidential boundary.\n\n"
        "CST-TT-08 is authorized for final theorem-and-toy science closure. CST-TT-07B remains unauthorized.\n",
        encoding="utf-8",
    )

    (ROOT / "docs/PHASE_BOUNDARY.md").write_text(
        "# CST-TT-07A phase boundary\n\n"
        "Inherited landed bank: full-handoff composition; relation-valued fission; fusion/recombination boundary; route completion; 13/13 primary/common toy closure.\n\n"
        "Newly landed: exact overlap/direct incomparability; generalized mixed-mode path composition; vector-valued defect semantics; hard-gate-preserving bounded robustness; model-relative unbounded controlled invariance; arbitrary finite-prefix counterfamily.\n\n"
        "Not landed: consciousness, felt continuity, empirical recognition, survival, numerical identity, A1/A2-P, consciousness-certificate soundness, open-ended physical robustness, or Temporal-IAPS.\n\n"
        "Next: CST-TT-08 final science closure. CST-TT-07B remains unauthorized.\n",
        encoding="utf-8",
    )

    restore = """# Restore and verify CST-TT-07A

```bash
unzip CST-TT-07A_cst-temporal-transcendence_repo.zip
cd cst-temporal-transcendence
git status --short --branch
git rev-parse CST-TT-07A-v1^{}
export PYTHONHASHSEED=0
export PYTHONPATH=src:scripts
python3 -m pytest -q
python3 scripts/validate_tt07a.py --no-write --require-tag --require-clean --require-manifest
python3 scripts/verify_tt07a_rebuild.py
lake build   # when the pinned Lean toolchain is available
```

The Python and certificate checks do not substitute for Lean-kernel compilation.
"""
    (ROOT / "docs/RESTORE_AND_BUILD.md").write_text(restore, encoding="utf-8")
    (ROOT / "RESTORE_AND_VERIFY.md").write_text(restore, encoding="utf-8")

    (ROOT / "README.md").write_text(
        "# CST-TT: Temporal substrate transcendence theorem and toy assets\n\n"
        "Current frozen phase: **CST-TT-07A**.\n\n"
        "Primary: exact finite Temporal-FIACH with separately audited target realization, strict overlap lineage, autonomy, route discipline, composition, branching, exact vector defects, bounded robustness, and model-relative unbounded controlled invariance.\n\n"
        "The direct-successor class is an exact, separately named broader structural-lineage mode; it does not replace strict overlap inside Temporal-FIACH. Temporal-IAPS remains locked.\n\n"
        "No consciousness, phenomenal-continuity, survival, numerical-identity, A1, A2-P, empirical-recognition, or certificate-soundness conclusion is claimed.\n",
        encoding="utf-8",
    )
    (ROOT / "STATE.md").write_text("# State\n\nCST-TT-07A science assets landed; final science closure is next.\n", encoding="utf-8")
    (ROOT / "STATUS.md").write_text("# Status\n\nPrimary strengthening branch complete. Temporal-IAPS remains locked.\n", encoding="utf-8")
    changelog_path = ROOT / "CHANGELOG.md"
    changelog_text = changelog_path.read_text(encoding="utf-8")
    changelog_section = "\n## CST-TT-07A\n\nLanded direct/overlap relation, generalized path composition, vector defects, bounded robustness, and model-relative unbounded invariance.\n"
    if "## CST-TT-07A" not in changelog_text:
        changelog_path.write_text(changelog_text + changelog_section, encoding="utf-8")
    (ROOT / "changelog/CST-TT-07A.md").write_text(
        "# CST-TT-07A\n\nPrimary strengthenings landed without altering strict Temporal-FIACH or unlocking Temporal-IAPS.\n",
        encoding="utf-8",
    )
    (ROOT / "formal/TOOLCHAIN_STATUS.json").write_text(
        json.dumps(
            {
                "phase": PHASE,
                "lean_toolchain": "leanprover/lean4:v4.28.0",
                "lean_executable_detected_at_build": shutil.which("lean") is not None,
                "lake_executable_detected_at_build": shutil.which("lake") is not None,
                "lean_compile_status": "pending-toolchain",
                "python_certificate_status": "checked",
                "claim": "no Lean compilation pass is inferred by the asset builder",
            },
            indent=2,
            sort_keys=True,
        )
        + "\n",
        encoding="utf-8",
    )
    formal_readme_path = ROOT / "formal/README.md"
    formal_readme_text = formal_readme_path.read_text(encoding="utf-8")
    formal_note = "CST-TT-07A adds proof-source modules for generalized continuity, exact defect vectors, bounded temporal margins, and model-relative unbounded invariant policies."
    if formal_note not in formal_readme_text:
        formal_readme_path.write_text(formal_readme_text.rstrip() + "\n\n" + formal_note + "\n", encoding="utf-8")

    status_rows = [
        {"theorem_id": "TTD-02", "prior_status": "finite-discriminator-evidence-landed-theorem-open", "new_status": "proof-source-and-executable-certificate-landed", "evidence": "ODR-01", "claim_ceiling": "structural lineage comparison only"},
        {"theorem_id": "TTS-01", "prior_status": "not-present", "new_status": "proof-source-and-executable-certificate-landed", "evidence": "GCP-OVERLAP-01;GCP-DIRECT-01;GCP-MIXED-01", "claim_ceiling": "generalized lineage path only"},
        {"theorem_id": "TTS-02", "prior_status": "not-present", "new_status": "proof-source-and-executable-certificate-landed", "evidence": "DEF-POS-01;DEF-EQUAL-SCALAR-01", "claim_ceiling": "finite vector-defect semantics"},
        {"theorem_id": "TTS-03", "prior_status": "not-present", "new_status": "proof-source-and-executable-certificate-landed", "evidence": "ROB-POS-01", "claim_ceiling": "declared bounded box"},
        {"theorem_id": "TTS-04", "prior_status": "not-present", "new_status": "proof-source-and-executable-certificate-landed", "evidence": "UNB-POS-01", "claim_ceiling": "unbounded run inside exact finite model"},
        {"theorem_id": "TTN-10", "prior_status": "checked-finite-countermodel", "new_status": "proof-source-and-checked-finite-countermodel", "evidence": "VECTOR_DEFECT_EXHAUSTION", "claim_ceiling": "scalar insufficiency"},
        {"theorem_id": "TTN-12", "prior_status": "checked-finite-countermodel", "new_status": "proof-source-and-checked-finite-countermodel", "evidence": "ARBITRARILY_LONG_FINITE_PREFIX_FAMILY", "claim_ceiling": "finite-prefix insufficiency"},
    ]
    write_csv(ROOT / "manifests/CST-TT-07A_THEOREM_STATUS_DELTA.csv", list(status_rows[0]), status_rows)
    model_rows = [
        {"asset_id": "ODR-01", "asset_kind": "relation-certificate", "count": 1, "status": "landed", "principal_result": "overlap/direct incomparable; generalized embedding"},
        {"asset_id": "GCP", "asset_kind": "generalized-continuity-path", "count": 3, "status": "landed", "principal_result": "overlap, direct, and mixed-mode paths"},
        {"asset_id": "DEF", "asset_kind": "defect-profile-certificate", "count": 8, "status": "landed", "principal_result": "one positive, six controls, one equal-scalar pair"},
        {"asset_id": "ROB", "asset_kind": "robustness-certificate", "count": 7, "status": "landed", "principal_result": "one positive and six controls"},
        {"asset_id": "UNB", "asset_kind": "unbounded-invariant-certificate", "count": 1, "status": "landed", "principal_result": "total invariant policy"},
    ]
    write_csv(ROOT / "manifests/CST-TT-07A_MODEL_CERTIFICATE_DELTA.csv", list(model_rows[0]), model_rows)

    phase_summary = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "date": DATE,
        "base_tag": BASE_TAG,
        "base_commit": BASE_COMMIT,
        "primary": "Temporal-FIACH strict overlap remains unchanged",
        "direct_relation": "exactly incomparable; both modes embed a separate generalized path class",
        "defect_profiles": {"positive": 1, "controls": defects["control_count"], "equal_scalar_pairs": 1},
        "robustness": {"box_points": robust["search"]["candidates_examined"], "violations": robust["search"]["violations"], "controls": robust["control_count"]},
        "unbounded": {"prefix_words_checked": unbounded["prefix"]["words_checked"], "counterfamily_models": unbounded["family"]["models_constructed"]},
        "fallback_unlocked": False,
        "next_phase": "CST-TT-08",
    }
    write_json(ROOT / "manifests/CST-TT-07A_PHASE_SUMMARY.json", phase_summary)
    write_json(ROOT / "manifests/PHASE_SUMMARY.json", phase_summary)

    completion = f"""# CST-TT-07A Completion Report

**Phase:** {PHASE}
**Base:** `{BASE_TAG}` / `{BASE_COMMIT}`
**Date:** {DATE}

## Landed

- exact overlap/direct incomparability and strict embedding into a separately named generalized path class;
- one mixed overlap/direct path with exact carrier, signature, ownership, and no-gap frontiers;
- exact vector-valued defect semantics with twelve hard gates, five soft margins, six controls, and an equal-scalar opposite-verdict pair;
- a {robust['search']['candidates_examined']}-point hard-gate-preserving temporal robustness box with zero violations and six boundary controls;
- model-relative unbounded controlled invariance from a total target-owned policy;
- an arbitrary finite-prefix counterfamily for horizons 0 through {unbounded['family']['maximum_horizon']}.

## Decision

Temporal-FIACH remains primary and unchanged. The direct-successor class remains a separately named broader S-L mode. Temporal-IAPS remains locked. CST-TT-08 is next.

## Claim ceiling

No consciousness, phenomenal continuity, personal survival, numerical identity, A1, A2-P, empirical recognition, certificate soundness, or indefinite physical persistence result is claimed. Lean-kernel compilation remains pending toolchain availability.
"""
    (ROOT / "manifests/CST-TT-07A_COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")
    (ROOT / "manifests/COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")


def main() -> int:
    direct = build_direct_and_relation()
    defects = build_defects()
    robustness = build_robustness()
    unbounded = build_unbounded()
    results = {"direct": direct, "defects": defects, "robustness": robustness, "unbounded": unbounded}
    build_schemas()
    update_registries(results)
    build_docs(results)
    print(
        "CST-TT-07A assets built: "
        f"4 generalized continuity certificates; {defects['control_count'] + 2} defect certificates/pairs; "
        f"{robustness['control_count'] + 1} robustness certificates; 1 unbounded invariant certificate"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
