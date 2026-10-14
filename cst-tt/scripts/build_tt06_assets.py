#!/usr/bin/env python3
from __future__ import annotations

import csv
from copy import deepcopy
import hashlib
import json
import platform
from pathlib import Path
from typing import Any, Iterable, Mapping

from cst_tt.branching import (
    audit_fusion_boundary,
    audit_temporal_fission,
    bounded_fission_symmetry_search,
    bounded_fusion_boundary_search,
)
from cst_tt.corridor import audit_corridor_composition, audit_strict_corridor
from cst_tt.fiach import audit_temporal_fiach, replay_component_certificates
from cst_tt.handoff_composition import (
    audit_full_handoff_composition,
    audit_route_completion,
    audit_staged_composition,
    bounded_full_handoff_interface_search,
    bounded_route_completion_search,
)
from cst_tt.package_gluing import audit_package, audit_staged_assembly
from cst_tt.toy_suite import audit_toy_suite, hidden_equivalence_search
from cst_tt.withdrawal_autonomy_checker import audit_autonomy
from tt06_data import (
    FUSED,
    FUSION_LEFT,
    FUSION_RIGHT,
    LEFT,
    MIDDLE,
    RIGHT,
    SOURCE,
    TARGET,
    composition_corridors,
    composition_packages,
    fission_corridors,
    fission_packages,
    fusion_corridors,
    fusion_target_packages,
    positive_autonomy,
    staged_with_id,
    toy_feature_rows,
)

ROOT = Path(__file__).resolve().parents[1]
PHASE = "CST-TT-06"
DATE = "2026-08-10"
BASE_TAG = "CST-TT-05-v1"
BASE_COMMIT = "faaf3b714050ac6acc195d0fab0f49dae9f51a87"


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n", encoding="utf-8")


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


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def rel(path: Path) -> str:
    return path.relative_to(ROOT).as_posix()


def load_json(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise TypeError(path)
    return value


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


def upsert_csv(path: Path, key: str, rows: list[dict[str, object]]) -> None:
    old = read_csv(path)
    fields = list(old[0].keys()) if old else list(rows[0].keys())
    additions = {str(row[key]): {field: row.get(field, "") for field in fields} for row in rows}
    merged = [row for row in old if row.get(key) not in additions]
    merged.extend(additions[item] for item in sorted(additions))
    write_csv(path, fields, merged)


def package_certificate(model: dict[str, Any], model_path: Path, cert_path: Path, role: str) -> dict[str, Any]:
    audit = audit_package(model)
    cert = {
        "schema_version": PHASE,
        "certificate_id": model["model_id"],
        "model_ref": rel(model_path),
        "model_sha256": sha256(model_path),
        "result_status": "checked-finite-integrated-package" if audit.integrated_package_valid else "checked-finite-package-failure-control",
        "role": role,
        "claim_lanes": ["S-R"],
        "claim_ceiling": "finite structural package realization only",
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.package_gluing", "audit_package"),
        "theorem_evidence": {
            "theorem_ids": ["TTH-01", "TTH-02"],
            "lean_declarations": [
                "CSTTT.PackageTheory.acyclicLocalWitnessGluing",
                "CSTTT.PackageTheory.stagedHeterogeneousPackageAssembly",
            ],
            "lean_compile_status": "pending-toolchain",
        },
    }
    write_json(cert_path, cert)
    return cert


def staged_certificate(
    assembly: dict[str, Any],
    assembly_path: Path,
    source_model: dict[str, Any],
    source_model_path: Path,
    target_model: dict[str, Any],
    target_model_path: Path,
    cert_path: Path,
) -> dict[str, Any]:
    audit = audit_staged_assembly(assembly, source_model, target_model)
    if not audit.staged_assembly_valid:
        raise RuntimeError(f"staged assembly failed: {assembly['assembly_id']} {audit.failed_obligations}")
    cert = {
        "schema_version": PHASE,
        "certificate_id": assembly["assembly_id"],
        "assembly_ref": rel(assembly_path),
        "assembly_sha256": sha256(assembly_path),
        "source_model_ref": rel(source_model_path),
        "source_model_sha256": sha256(source_model_path),
        "target_model_ref": rel(target_model_path),
        "target_model_sha256": sha256(target_model_path),
        "result_status": "checked-finite-compositional-staged-package-certificate",
        "claim_lanes": ["S-T", "S-R"],
        "claim_ceiling": "finite typed clause-map preservation and target assembly only",
        "handoff_alignment": assembly.get("handoff_alignment", {}),
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.package_gluing", "audit_staged_assembly"),
        "theorem_evidence": {
            "theorem_ids": ["TTH-01", "TTH-02", "TTH-07"],
            "lean_declarations": [
                "CSTTT.PackageTheory.stagedHeterogeneousPackageAssembly",
                "CSTTT.TargetTheory.fullTemporalHandoffComposition",
            ],
            "lean_compile_status": "pending-toolchain",
        },
    }
    write_json(cert_path, cert)
    return cert


def corridor_certificate(model: dict[str, Any], model_path: Path, cert_path: Path, role: str) -> dict[str, Any]:
    audit = audit_strict_corridor(model)
    if not audit.strict_corridor_valid:
        raise RuntimeError(f"corridor failed: {model['model_id']} {audit.failed_obligations}")
    cert = {
        "schema_version": PHASE,
        "certificate_id": model["model_id"],
        "model_ref": rel(model_path),
        "model_sha256": sha256(model_path),
        "result_status": "checked-finite-strict-carrier-chain-corridor",
        "role": role,
        "claim_lanes": ["S-L"],
        "claim_ceiling": "finite structural temporal lineage criterion only",
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.corridor", "audit_strict_corridor"),
        "theorem_evidence": {
            "theorem_ids": ["TTH-04", "TTH-07", "TTH-08"],
            "lean_declarations": [
                "CSTTT.CorridorTheory.atomicTemporalCorridorCertificateSound",
                "CSTTT.CorridorTheory.strictTemporalCorridorComposition",
            ],
            "lean_compile_status": "pending-toolchain",
        },
    }
    write_json(cert_path, cert)
    return cert


def autonomy_certificate(model: dict[str, Any], model_path: Path, cert_path: Path, role: str) -> dict[str, Any]:
    audit = audit_autonomy(model)
    if not audit.autonomy_valid:
        raise RuntimeError(f"autonomy failed: {model['model_id']} {audit.failed_obligations}")
    cert = {
        "schema_version": PHASE,
        "certificate_id": model["model_id"],
        "model_ref": rel(model_path),
        "model_sha256": sha256(model_path),
        "result_status": "checked-finite-compositional-post-withdrawal-autonomy",
        "role": role,
        "claim_lanes": ["A"],
        "claim_ceiling": "model-relative post-withdrawal autonomy over the declared finite disturbance class",
        "computed_invariant_state_ids": list(audit.computed_invariant_state_ids),
        "finite_horizon": audit.finite_horizon,
        "finite_words_checked": audit.finite_words_checked,
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.withdrawal_autonomy_checker", "audit_autonomy"),
        "theorem_evidence": {
            "theorem_ids": ["TTH-05", "TTH-07"],
            "lean_declarations": ["CSTTT.AutonomyTheory.postWithdrawalFiniteHorizonInvariance"],
            "lean_compile_status": "pending-toolchain",
        },
    }
    write_json(cert_path, cert)
    return cert


def fiach_certificate(spec: dict[str, Any], model_path: Path, cert_path: Path, role: str) -> dict[str, Any]:
    spec = deepcopy(spec)
    spec["component_sha256"] = {key: sha256(ROOT / value) for key, value in spec["component_refs"].items()}
    write_json(model_path, spec)
    audit = audit_temporal_fiach(spec, ROOT)
    replay = replay_component_certificates(spec, ROOT)
    if not audit.aggregate_valid or not replay or not all(replay.values()):
        raise RuntimeError(f"FIACH failed: {spec['certificate_id']} {audit.failed_obligations} {replay}")
    cert = deepcopy(spec)
    cert.update({
        "schema_version": PHASE,
        "model_ref": rel(model_path),
        "model_sha256": sha256(model_path),
        "result_status": "checked-finite-temporal-fiach-certificate",
        "role": role,
        "claim_ceiling": "exact finite structural precursor only; no consciousness, phenomenal-continuity, survival, or identity conclusion",
        "lane_results": {"S-T": True, "S-R": True, "S-L": True, "A": True},
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.fiach", "audit_temporal_fiach"),
        "theorem_evidence": {
            "theorem_ids": ["TTH-02", "TTH-04", "TTH-05", "TTH-06", "TTH-07", "TTH-08"],
            "lean_declarations": [
                "CSTTT.TargetTheory.temporalFIACHCertificateSoundness",
                "CSTTT.TargetTheory.fullTemporalHandoffComposition",
            ],
            "component_replay": replay,
            "lean_compile_status": "pending-toolchain",
        },
    })
    write_json(cert_path, cert)
    return cert


def build_composition() -> dict[str, Any]:
    left_corridor, right_corridor, composite_corridor = composition_corridors()
    left_corridor_path = ROOT / "models/corridors/COR-POS-02A.model.json"
    right_corridor_path = ROOT / "models/corridors/COR-POS-02B.model.json"
    if load_json(left_corridor_path) != left_corridor or load_json(right_corridor_path) != right_corridor:
        raise RuntimeError("frozen CST-TT-04 corridor inputs changed")
    composite_corridor_path = ROOT / "models/corridors/COR-POS-03-FULL-COMPOSITE.model.json"
    write_json(composite_corridor_path, composite_corridor)

    left_corridor_cert_path = ROOT / "formal/certificates/corridors/COR-POS-02A.certificate.json"
    right_corridor_cert_path = ROOT / "formal/certificates/corridors/COR-POS-02B.certificate.json"
    composite_corridor_cert_path = ROOT / "formal/certificates/composition/corridors/COR-POS-03-FULL-COMPOSITE.certificate.json"
    composite_corridor_cert = corridor_certificate(composite_corridor, composite_corridor_path, composite_corridor_cert_path, "full-composite")

    source_pkg, middle_pkg, target_pkg = composition_packages(left_corridor, right_corridor, composite_corridor)
    package_models = {"source": source_pkg, "middle": middle_pkg, "target": target_pkg}
    package_paths: dict[str, Path] = {}
    package_cert_paths: dict[str, Path] = {}
    package_certs: dict[str, dict[str, Any]] = {}
    for role, model in package_models.items():
        model_path = ROOT / "models/composition/packages" / f"{model['model_id']}.model.json"
        cert_path = ROOT / "formal/certificates/composition/packages" / f"{model['model_id']}.certificate.json"
        write_json(model_path, model)
        package_paths[role] = model_path
        package_cert_paths[role] = cert_path
        package_certs[role] = package_certificate(model, model_path, cert_path, f"composition-{role}")

    staged_models = {
        "left": staged_with_id(source_pkg, middle_pkg, "STG-COMP-A"),
        "right": staged_with_id(middle_pkg, target_pkg, "STG-COMP-B"),
        "composite": staged_with_id(source_pkg, target_pkg, "STG-COMP-OUTER"),
    }
    staged_endpoints = {"left": ("source", "middle"), "right": ("middle", "target"), "composite": ("source", "target")}
    staged_paths: dict[str, Path] = {}
    staged_cert_paths: dict[str, Path] = {}
    for role, assembly in staged_models.items():
        src_role, tgt_role = staged_endpoints[role]
        model_path = ROOT / "models/composition/staged" / f"{assembly['assembly_id']}.assembly.json"
        cert_path = ROOT / "formal/certificates/composition/staged" / f"{assembly['assembly_id']}.certificate.json"
        write_json(model_path, assembly)
        staged_certificate(
            assembly, model_path,
            package_models[src_role], package_paths[src_role],
            package_models[tgt_role], package_paths[tgt_role],
            cert_path,
        )
        staged_paths[role] = model_path
        staged_cert_paths[role] = cert_path

    staged_comp_spec = {
        "schema_version": PHASE,
        "certificate_id": "STG-COMP-01",
        "component_refs": {role: rel(path) for role, path in staged_cert_paths.items()},
        "component_sha256": {role: sha256(path) for role, path in staged_cert_paths.items()},
        "claim_lanes": ["S-T", "S-R"],
        "claim_ceiling": "exact finite staged-map factorization through one audited intermediate package",
    }
    staged_comp_audit = audit_staged_composition(staged_comp_spec, ROOT)
    if not staged_comp_audit.composition_valid:
        raise RuntimeError(f"staged composition failed: {staged_comp_audit.failed_obligations}")
    staged_comp_spec.update({
        "result_status": "checked-finite-staged-package-composition",
        "audit": staged_comp_audit.to_dict(),
        "checker": checker("cst_tt.handoff_composition", "audit_staged_composition"),
    })
    staged_comp_cert_path = ROOT / "formal/certificates/composition/STG-COMP-01.certificate.json"
    write_json(staged_comp_cert_path, staged_comp_spec)

    final_events = {
        "left": "m-boundary",
        "right": "t-chain-exit",
        "composite": "t-chain-exit",
    }
    autonomy_models = {
        "left": positive_autonomy(
            model_id="AUT-COMP-A", source=SOURCE, target=MIDDLE, target_package=middle_pkg,
            package_certificate_ref=rel(package_cert_paths["middle"]),
            package_certificate_sha256=sha256(package_cert_paths["middle"]),
            handoff_endpoint_event_id=final_events["left"], prefix="comp-middle",
        ),
        "right": positive_autonomy(
            model_id="AUT-COMP-B", source=MIDDLE, target=TARGET, target_package=target_pkg,
            package_certificate_ref=rel(package_cert_paths["target"]),
            package_certificate_sha256=sha256(package_cert_paths["target"]),
            handoff_endpoint_event_id=final_events["right"], prefix="comp-target",
        ),
        "composite": positive_autonomy(
            model_id="AUT-COMP-OUTER", source=SOURCE, target=TARGET, target_package=target_pkg,
            package_certificate_ref=rel(package_cert_paths["target"]),
            package_certificate_sha256=sha256(package_cert_paths["target"]),
            handoff_endpoint_event_id=final_events["composite"], prefix="comp-target",
        ),
    }
    # The outer withdrawal must remove both the original source and the autonomous
    # intermediate.  The target controller itself remains byte-for-byte identical
    # to the final leg once provenance-only removed-resource rows are ignored.
    autonomy_models["composite"]["withdrawal"]["removed_resources"].append({
        "resource_id": "comp-target-intermediate-upstream-source",
        "owner": dict(MIDDLE),
        "role": "source",
    })
    autonomy_paths: dict[str, Path] = {}
    autonomy_cert_paths: dict[str, Path] = {}
    for role, model in autonomy_models.items():
        model_path = ROOT / "models/composition/autonomy" / f"{model['model_id']}.model.json"
        cert_path = ROOT / "formal/certificates/composition/autonomy" / f"{model['model_id']}.certificate.json"
        write_json(model_path, model)
        autonomy_certificate(model, model_path, cert_path, f"composition-{role}")
        autonomy_paths[role] = model_path
        autonomy_cert_paths[role] = cert_path

    corridor_cert_paths = {
        "left": left_corridor_cert_path,
        "right": right_corridor_cert_path,
        "composite": composite_corridor_cert_path,
    }
    endpoints = {
        "left": (SOURCE, MIDDLE, "source", "middle"),
        "right": (MIDDLE, TARGET, "middle", "target"),
        "composite": (SOURCE, TARGET, "source", "target"),
    }
    fiach_cert_paths: dict[str, Path] = {}
    fiach_model_paths: dict[str, Path] = {}
    fiach_certs: dict[str, dict[str, Any]] = {}
    for role, (source, target, source_pkg_role, target_pkg_role) in endpoints.items():
        cert_id = {"left": "FIACH-COMP-A", "right": "FIACH-COMP-B", "composite": "FIACH-COMP-OUTER"}[role]
        spec = {
            "schema_version": PHASE,
            "certificate_id": cert_id,
            "title": f"{role} exact finite Temporal-FIACH handoff for full composition",
            "source": dict(source),
            "target": dict(target),
            "component_refs": {
                "source_package": rel(package_cert_paths[source_pkg_role]),
                "staged_assembly": rel(staged_cert_paths[role]),
                "target_package": rel(package_cert_paths[target_pkg_role]),
                "corridor": rel(corridor_cert_paths[role]),
                "autonomy": rel(autonomy_cert_paths[role]),
            },
            "route_status": "route-indexed",
            "recognition_status": "not-addressed",
            "claim_ceiling": "exact finite structural precursor only",
        }
        model_path = ROOT / "models/composition/fiach" / f"{cert_id}.model.json"
        cert_path = ROOT / "formal/certificates/composition/fiach" / f"{cert_id}.certificate.json"
        fiach_model_paths[role] = model_path
        fiach_cert_paths[role] = cert_path
        fiach_certs[role] = fiach_certificate(spec, model_path, cert_path, f"composition-{role}")

    corridor_comp_audit = audit_corridor_composition(left_corridor, right_corridor, composite_corridor)
    if not corridor_comp_audit.composition_valid:
        raise RuntimeError(f"corridor composition failed: {corridor_comp_audit.failed_obligations}")
    corridor_comp_cert_path = ROOT / "formal/certificates/composition/COR-COMP-FULL-01.certificate.json"
    corridor_comp_cert = {
        "schema_version": PHASE,
        "certificate_id": "COR-COMP-FULL-01",
        "left_model_ref": rel(left_corridor_path),
        "left_model_sha256": sha256(left_corridor_path),
        "right_model_ref": rel(right_corridor_path),
        "right_model_sha256": sha256(right_corridor_path),
        "composite_model_ref": rel(composite_corridor_path),
        "composite_model_sha256": sha256(composite_corridor_path),
        "result_status": "checked-finite-corridor-composition-interface",
        "claim_lanes": ["S-L"],
        "claim_ceiling": "strict carrier-chain lineage composition only",
        "audit": corridor_comp_audit.to_dict(),
        "checker": checker("cst_tt.corridor", "audit_corridor_composition"),
    }
    write_json(corridor_comp_cert_path, corridor_comp_cert)

    full_spec = {
        "schema_version": PHASE,
        "certificate_id": "FIACH-COMP-01",
        "title": "full two-hop Temporal-FIACH structural composition",
        "component_refs": {
            "left_fiach": rel(fiach_cert_paths["left"]),
            "right_fiach": rel(fiach_cert_paths["right"]),
            "composite_fiach": rel(fiach_cert_paths["composite"]),
            "staged_composition": rel(staged_comp_cert_path),
            "corridor_composition": rel(corridor_comp_cert_path),
            "composite_corridor_certificate": rel(composite_corridor_cert_path),
        },
        "intermediate_carrier": dict(MIDDLE),
        "claim_lanes": ["S-T", "S-R", "S-L", "A"],
        "claim_ceiling": "exact finite structural handoff composition only",
        "nonclaims": [
            "no consciousness or phenomenal-continuity conclusion",
            "no unique identity or survival conclusion",
            "no empirical recognition result",
        ],
    }
    full_spec["component_sha256"] = {
        key: sha256(ROOT / value)
        for key, value in full_spec["component_refs"].items()
        if key in {"left_fiach", "right_fiach", "composite_fiach", "staged_composition", "corridor_composition"}
    }
    full_model_path = ROOT / "models/composition/FIACH-COMP-01.model.json"
    write_json(full_model_path, full_spec)
    full_audit = audit_full_handoff_composition(full_spec, ROOT)
    if not full_audit.composition_valid:
        raise RuntimeError(f"full handoff composition failed: {full_audit.failed_obligations}")
    full_cert = deepcopy(full_spec)
    full_cert.update({
        "model_ref": rel(full_model_path),
        "model_sha256": sha256(full_model_path),
        "result_status": "checked-finite-full-temporal-fiach-composition",
        "audit": full_audit.to_dict(),
        "checker": checker("cst_tt.handoff_composition", "audit_full_handoff_composition"),
        "theorem_evidence": {
            "theorem_ids": ["TTH-07"],
            "lean_declarations": [
                "CSTTT.TargetTheory.fullTemporalHandoffComposition",
                "CSTTT.TargetTheory.composedHandoffPreservesIndependentLanes",
                "CSTTT.TargetTheory.routeIndexedComponentPreventsAutomaticFlatness",
            ],
            "lean_compile_status": "pending-toolchain",
        },
    })
    full_cert_path = ROOT / "formal/certificates/composition/FIACH-COMP-01.certificate.json"
    write_json(full_cert_path, full_cert)

    interface_search = bounded_full_handoff_interface_search()
    interface_search_path = ROOT / "formal/certificates/search/FULL_HANDOFF_INTERFACE_EXHAUSTION.json"
    write_json(interface_search_path, interface_search)

    return {
        "full_cert_path": full_cert_path,
        "full_cert": full_cert,
        "full_audit": full_audit,
        "fiach_cert_paths": fiach_cert_paths,
        "package_cert_paths": package_cert_paths,
        "package_paths": package_paths,
        "staged_cert_paths": staged_cert_paths,
        "autonomy_cert_paths": autonomy_cert_paths,
        "corridor_cert_paths": corridor_cert_paths,
        "corridor_comp_cert_path": corridor_comp_cert_path,
        "staged_comp_cert_path": staged_comp_cert_path,
        "interface_search_path": interface_search_path,
        "interface_search": interface_search,
    }


def build_fission() -> dict[str, Any]:
    left_corridor, right_corridor = fission_corridors()
    corridor_models = {"left": left_corridor, "right": right_corridor}
    corridor_paths: dict[str, Path] = {}
    corridor_cert_paths: dict[str, Path] = {}
    for role, model in corridor_models.items():
        model_path = ROOT / "models/fission" / f"{model['model_id']}.model.json"
        cert_path = ROOT / "formal/certificates/fission/corridors" / f"{model['model_id']}.certificate.json"
        write_json(model_path, model)
        corridor_certificate(model, model_path, cert_path, f"fission-{role}")
        corridor_paths[role] = model_path
        corridor_cert_paths[role] = cert_path

    source_pkg, left_pkg, right_pkg = fission_packages(left_corridor, right_corridor)
    package_models = {"source": source_pkg, "left": left_pkg, "right": right_pkg}
    package_paths: dict[str, Path] = {}
    package_cert_paths: dict[str, Path] = {}
    for role, model in package_models.items():
        model_path = ROOT / "models/fission/packages" / f"{model['model_id']}.model.json"
        cert_path = ROOT / "formal/certificates/fission/packages" / f"{model['model_id']}.certificate.json"
        write_json(model_path, model)
        package_certificate(model, model_path, cert_path, f"fission-{role}")
        package_paths[role] = model_path
        package_cert_paths[role] = cert_path

    staged_cert_paths: dict[str, Path] = {}
    for role, target_pkg in (("left", left_pkg), ("right", right_pkg)):
        assembly = staged_with_id(source_pkg, target_pkg, f"STG-FIS-{role.upper()}")
        model_path = ROOT / "models/fission/staged" / f"{assembly['assembly_id']}.assembly.json"
        cert_path = ROOT / "formal/certificates/fission/staged" / f"{assembly['assembly_id']}.certificate.json"
        write_json(model_path, assembly)
        staged_certificate(assembly, model_path, source_pkg, package_paths["source"], target_pkg, package_paths[role], cert_path)
        staged_cert_paths[role] = cert_path

    target_map = {"left": LEFT, "right": RIGHT}
    autonomy_cert_paths: dict[str, Path] = {}
    for role in ("left", "right"):
        model = positive_autonomy(
            model_id=f"AUT-FIS-{role.upper()}",
            source=SOURCE,
            target=target_map[role],
            target_package=package_models[role],
            package_certificate_ref=rel(package_cert_paths[role]),
            package_certificate_sha256=sha256(package_cert_paths[role]),
            handoff_endpoint_event_id=f"fission-{role}-exit",
            prefix="fission-branch",
        )
        model_path = ROOT / "models/fission/autonomy" / f"{model['model_id']}.model.json"
        cert_path = ROOT / "formal/certificates/fission/autonomy" / f"{model['model_id']}.certificate.json"
        write_json(model_path, model)
        autonomy_certificate(model, model_path, cert_path, f"fission-{role}")
        autonomy_cert_paths[role] = cert_path

    fiach_cert_paths: dict[str, Path] = {}
    for role in ("left", "right"):
        cert_id = f"FIACH-FIS-{role.upper()}"
        spec = {
            "schema_version": PHASE,
            "certificate_id": cert_id,
            "source": dict(SOURCE),
            "target": dict(target_map[role]),
            "component_refs": {
                "source_package": rel(package_cert_paths["source"]),
                "staged_assembly": rel(staged_cert_paths[role]),
                "target_package": rel(package_cert_paths[role]),
                "corridor": rel(corridor_cert_paths[role]),
                "autonomy": rel(autonomy_cert_paths[role]),
            },
            "route_status": "route-indexed",
            "recognition_status": "not-addressed",
            "claim_ceiling": "one relation-valued structural fission branch only",
        }
        model_path = ROOT / "models/fission/fiach" / f"{cert_id}.model.json"
        cert_path = ROOT / "formal/certificates/fission/fiach" / f"{cert_id}.certificate.json"
        fiach_certificate(spec, model_path, cert_path, f"fission-{role}")
        fiach_cert_paths[role] = cert_path

    fission_spec = {
        "schema_version": PHASE,
        "certificate_id": "FISSION-POS-01",
        "branch_certificate_refs": {role: rel(path) for role, path in fiach_cert_paths.items()},
        "branch_certificate_sha256": {role: sha256(path) for role, path in fiach_cert_paths.items()},
        "relation": [
            {"source": dict(SOURCE), "target": dict(LEFT)},
            {"source": dict(SOURCE), "target": dict(RIGHT)},
        ],
        "target_swap": {str(LEFT["code"]): RIGHT["code"], str(RIGHT["code"]): LEFT["code"]},
        "claim_lanes": ["S-L", "S-R", "A"],
        "claim_ceiling": "relation-valued finite temporal fission; no unique continuer or numerical identity conclusion",
    }
    fission_model_path = ROOT / "models/fission/FISSION-POS-01.model.json"
    write_json(fission_model_path, fission_spec)
    audit = audit_temporal_fission(fission_spec, ROOT)
    if not audit.relation_valued_fission_valid:
        raise RuntimeError(f"fission failed: {audit.failed_obligations}")
    cert = deepcopy(fission_spec)
    cert.update({
        "model_ref": rel(fission_model_path),
        "model_sha256": sha256(fission_model_path),
        "result_status": "checked-finite-relation-valued-temporal-fission",
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.branching", "audit_temporal_fission"),
        "theorem_evidence": {
            "theorem_ids": ["TTH-08", "TTN-11"],
            "lean_declarations": [
                "CSTTT.CorridorTheory.relationValuedTemporalFission",
                "CSTTT.CorridorTheory.targetSwapPreservesFissionValidity",
                "CSTTT.CorridorTheory.targetSwapSymmetryNonselection",
            ],
            "lean_compile_status": "pending-toolchain",
        },
    })
    cert_path = ROOT / "formal/certificates/fission/FISSION-POS-01.certificate.json"
    write_json(cert_path, cert)

    control_rows: list[dict[str, Any]] = []
    controls = {
        "FIS-C01": ("FIS-O01-component-hashes", lambda x: x["branch_certificate_sha256"].__setitem__("left", "0" * 64)),
        "FIS-C02": ("FIS-O07-targets-distinct", lambda x: x["branch_certificate_refs"].__setitem__("right", x["branch_certificate_refs"]["left"])),
        "FIS-C03": ("FIS-O10-relation-contains-both", lambda x: x.__setitem__("relation", x["relation"][:1])),
        "FIS-C04": ("FIS-O11-swap-involutive", lambda x: x.__setitem__("target_swap", {str(LEFT["code"]): RIGHT["code"], str(RIGHT["code"]): RIGHT["code"]})),
        "FIS-C05": ("FIS-O12-swap-fixed-point-free", lambda x: x.__setitem__("target_swap", {str(LEFT["code"]): LEFT["code"], str(RIGHT["code"]): RIGHT["code"]})),
        "FIS-C06": ("FIS-O15-uniqueness-claim-absent", lambda x: x.__setitem__("selected_target", dict(LEFT))),
    }
    for control_id, (expected, mutate) in controls.items():
        model = deepcopy(fission_spec)
        model["certificate_id"] = control_id
        mutate(model)
        control_audit = audit_temporal_fission(model, ROOT)
        if control_audit.relation_valued_fission_valid or expected not in control_audit.failed_obligations:
            raise RuntimeError(f"fission control failed to discriminate: {control_id} {control_audit.failed_obligations}")
        model_path = ROOT / "models/fission/controls" / f"{control_id}.model.json"
        write_json(model_path, model)
        control_cert = {
            "schema_version": PHASE,
            "control_id": control_id,
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": "checked-fission-obligation-countermodel",
            "expected_primary_failure": expected,
            "observed_failures": list(control_audit.failed_obligations),
            "audit": control_audit.to_dict(),
            "claim_ceiling": "finite fission-interface boundary only",
        }
        control_cert_path = ROOT / "formal/certificates/fission/controls" / f"{control_id}.certificate.json"
        write_json(control_cert_path, control_cert)
        control_rows.append({
            "control_id": control_id,
            "expected_primary_failure": expected,
            "observed_failures": ";".join(control_audit.failed_obligations),
            "model_ref": rel(model_path),
            "certificate_ref": rel(control_cert_path),
        })

    search = bounded_fission_symmetry_search()
    search_path = ROOT / "formal/certificates/search/FISSION_SYMMETRY_EXHAUSTION.json"
    write_json(search_path, search)
    write_csv(
        ROOT / "registries/FISSION_CONTROL_REGISTRY.csv",
        ["control_id", "expected_primary_failure", "observed_failures", "model_ref", "certificate_ref"],
        control_rows,
    )
    return {"cert_path": cert_path, "cert": cert, "audit": audit, "search": search, "search_path": search_path, "controls": control_rows}


def build_fusion() -> dict[str, Any]:
    left_corridor, right_corridor = fusion_corridors()
    corridor_cert_paths: dict[str, Path] = {}
    for role, model in (("left", left_corridor), ("right", right_corridor)):
        model_path = ROOT / "models/fusion" / f"{model['model_id']}.model.json"
        cert_path = ROOT / "formal/certificates/fusion/corridors" / f"{model['model_id']}.certificate.json"
        write_json(model_path, model)
        corridor_certificate(model, model_path, cert_path, f"fusion-{role}")
        corridor_cert_paths[role] = cert_path

    negative_pkg, positive_pkg = fusion_target_packages(left_corridor)
    package_cert_paths: dict[str, Path] = {}
    for role, model in (("negative", negative_pkg), ("positive-control", positive_pkg)):
        model_path = ROOT / "models/fusion/packages" / f"{model['model_id']}.model.json"
        cert_path = ROOT / "formal/certificates/fusion/packages" / f"{model['model_id']}.certificate.json"
        write_json(model_path, model)
        package_certificate(model, model_path, cert_path, f"fusion-{role}")
        package_cert_paths[role] = cert_path

    spec = {
        "schema_version": PHASE,
        "certificate_id": "FUSION-BOUNDARY-01",
        "component_refs": {
            "left_corridor": rel(corridor_cert_paths["left"]),
            "right_corridor": rel(corridor_cert_paths["right"]),
            "target_package": rel(package_cert_paths["negative"]),
        },
        "branchwise_payload_preserved": True,
        "claim_lanes": ["S-L", "S-R"],
        "claim_ceiling": "finite separation of branchwise lineage merger from integrated target package",
    }
    spec["component_sha256"] = {key: sha256(ROOT / value) for key, value in spec["component_refs"].items()}
    model_path = ROOT / "models/fusion/FUSION-BOUNDARY-01.model.json"
    write_json(model_path, spec)
    audit = audit_fusion_boundary(spec, ROOT)
    if not audit.fusion_boundary_valid:
        raise RuntimeError(f"fusion boundary failed: {audit.failed_obligations}")
    cert = deepcopy(spec)
    cert.update({
        "model_ref": rel(model_path),
        "model_sha256": sha256(model_path),
        "result_status": "checked-finite-fusion-recombination-boundary",
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.branching", "audit_fusion_boundary"),
        "theorem_evidence": {
            "theorem_ids": ["TTN-14"],
            "lean_declarations": [
                "CSTTT.PackageTheory.fusionLineageDoesNotImplyIntegratedPackage",
                "CSTTT.PackageTheory.fusionBranchwiseDoesNotRepairRecombination",
            ],
            "lean_compile_status": "pending-toolchain",
        },
    })
    cert_path = ROOT / "formal/certificates/fusion/FUSION-BOUNDARY-01.certificate.json"
    write_json(cert_path, cert)

    valid_control = deepcopy(spec)
    valid_control["certificate_id"] = "FUSION-CONTROL-VALID-PACKAGE"
    valid_control["component_refs"]["target_package"] = rel(package_cert_paths["positive-control"])
    valid_control["component_sha256"]["target_package"] = sha256(package_cert_paths["positive-control"])
    valid_audit = audit_fusion_boundary(valid_control, ROOT)
    if valid_audit.fusion_boundary_valid or "FUS-O08-action-credit-conflict" not in valid_audit.failed_obligations or "FUS-O09-recombination-failure" not in valid_audit.failed_obligations:
        raise RuntimeError(f"fusion valid-package control failed: {valid_audit.failed_obligations}")
    control_path = ROOT / "formal/certificates/fusion/controls/FUSION-CONTROL-VALID-PACKAGE.certificate.json"
    write_json(control_path, {
        "schema_version": PHASE,
        "control_id": "FUSION-CONTROL-VALID-PACKAGE",
        "result_status": "checked-fusion-boundary-negative-control",
        "expected_failures": ["FUS-O08-action-credit-conflict", "FUS-O09-recombination-failure", "FUS-O10-integrated-package-fails", "FUS-O11-merger-does-not-imply-package"],
        "audit": valid_audit.to_dict(),
        "claim_ceiling": "finite logical boundary control only",
    })

    search = bounded_fusion_boundary_search()
    search_path = ROOT / "formal/certificates/search/FUSION_BOUNDARY_EXHAUSTION.json"
    write_json(search_path, search)
    return {"cert_path": cert_path, "cert": cert, "audit": audit, "search": search, "search_path": search_path, "control_path": control_path}


def build_route_completion(composition: dict[str, Any]) -> dict[str, Any]:
    route_refs = {
        "route-indexed": ROOT / "formal/certificates/routes/ROUTE-NEG-01.certificate.json",
        "flat-under-normalization": ROOT / "formal/certificates/routes/ROUTE-POS-01.certificate.json",
    }
    endpoint_ref = rel(composition["package_cert_paths"]["target"])
    specs = {
        "route-indexed": {
            "schema_version": PHASE,
            "certificate_id": "ROUTE-COMP-INDEXED-01",
            "fiach_certificate_ref": rel(composition["fiach_cert_paths"]["composite"]),
            "route_certificate_ref": rel(route_refs["route-indexed"]),
            "route_certificate_sha256": sha256(route_refs["route-indexed"]),
            "mode": "route-indexed",
            "route_memory_retained": True,
            "endpoint_package_certificate_ref": endpoint_ref,
            "claim_ceiling": "route-indexed structural handoff only",
        },
        "flat-under-normalization": {
            "schema_version": PHASE,
            "certificate_id": "ROUTE-COMP-FLAT-01",
            "fiach_certificate_ref": rel(composition["fiach_cert_paths"]["composite"]),
            "route_certificate_ref": rel(route_refs["flat-under-normalization"]),
            "route_certificate_sha256": sha256(route_refs["flat-under-normalization"]),
            "mode": "flat-under-normalization",
            "route_memory_retained": False,
            "endpoint_package_certificate_ref": endpoint_ref,
            "claim_ceiling": "route-independent endpoint only under separately certified confluence",
        },
    }
    cert_paths: dict[str, Path] = {}
    audits = {}
    for mode, spec in specs.items():
        audit = audit_route_completion(spec, ROOT)
        if not audit.route_completion_valid:
            raise RuntimeError(f"route completion failed: {mode} {audit.failed_obligations}")
        cert = deepcopy(spec)
        cert.update({
            "result_status": "checked-finite-route-completion",
            "output_route_status": audit.output_route_status,
            "audit": audit.to_dict(),
            "checker": checker("cst_tt.handoff_composition", "audit_route_completion"),
            "theorem_evidence": {
                "theorem_ids": ["TTH-09", "TTN-04", "TTN-05"],
                "lean_declarations": [
                    "CSTTT.TargetTheory.noUnlicensedRouteMemoryErasure",
                    "CSTTT.TargetTheory.retainedRouteMemoryYieldsIndexedStatus",
                    "CSTTT.TargetTheory.certifiedNormalizationYieldsFlatStatus",
                ],
                "lean_compile_status": "pending-toolchain",
            },
        })
        cert_path = ROOT / "formal/certificates/route_completion" / f"{spec['certificate_id']}.certificate.json"
        write_json(cert_path, cert)
        cert_paths[mode] = cert_path
        audits[mode] = audit

    bad = deepcopy(specs["flat-under-normalization"])
    bad["certificate_id"] = "ROUTE-COMP-C01-UNLICENSED-ERASURE"
    bad["route_certificate_ref"] = rel(route_refs["route-indexed"])
    bad["route_certificate_sha256"] = sha256(route_refs["route-indexed"])
    bad_audit = audit_route_completion(bad, ROOT)
    if bad_audit.route_completion_valid or "RC-O05-route-indexed-or-flat-evidence" not in bad_audit.failed_obligations:
        raise RuntimeError(f"route completion control failed: {bad_audit.failed_obligations}")
    bad_path = ROOT / "formal/certificates/route_completion/controls/ROUTE-COMP-C01.certificate.json"
    write_json(bad_path, {
        "schema_version": PHASE,
        "control_id": bad["certificate_id"],
        "result_status": "checked-unlicensed-route-memory-erasure-control",
        "audit": bad_audit.to_dict(),
        "claim_ceiling": "finite route-completion boundary only",
    })

    search = bounded_route_completion_search()
    search_path = ROOT / "formal/certificates/search/ROUTE_COMPLETION_EXHAUSTION.json"
    write_json(search_path, search)
    return {"cert_paths": cert_paths, "audits": audits, "control_path": bad_path, "search": search, "search_path": search_path}


def build_toy_suite(composition: dict[str, Any], fission: dict[str, Any]) -> dict[str, Any]:
    entries = [
        ("TTM-01", "positive", composition["fiach_cert_paths"]["composite"], ["TTH-06", "TTH-07"]),
        ("TTM-02", "negative", ROOT / "formal/certificates/countermodels/CM-02.certificate.json", ["TTN-01"]),
        ("TTM-03", "positive", ROOT / "formal/certificates/direct_successor/DS-POS-01.certificate.json", ["TTD-01", "TTD-03"]),
        ("TTM-04", "negative", ROOT / "formal/certificates/countermodels/CM-04.certificate.json", ["TTN-06"]),
        ("TTM-05", "boundary", ROOT / "formal/certificates/routes/ROUTE-NEG-01.certificate.json", ["TTN-04", "TTN-05"]),
        ("TTM-06", "positive", ROOT / "formal/certificates/routes/ROUTE-POS-01.certificate.json", ["TTH-09"]),
        ("TTM-07", "boundary", fission["cert_path"], ["TTH-08", "TTN-11"]),
        ("TTM-08", "negative", ROOT / "formal/certificates/countermodels/CM-12.certificate.json", ["TTN-09"]),
        ("TTM-09", "negative", ROOT / "formal/certificates/autonomy/controls/AUT-C05.certificate.json", ["TTH-05", "TTN-07"]),
        ("TTM-10", "boundary", ROOT / "formal/certificates/countermodels/CM-13.certificate.json", ["TTN-12"]),
        ("TTM-11", "negative", ROOT / "formal/certificates/countermodels/CM-08.certificate.json", ["TTN-08"]),
        ("TTM-12", "negative", ROOT / "formal/certificates/countermodels/CM-09.certificate.json", ["TTN-02"]),
        ("TTM-13", "negative", ROOT / "formal/certificates/countermodels/CM-10.certificate.json", ["TTN-10"]),
    ]
    spec = {
        "schema_version": PHASE,
        "certificate_id": "TOY-SUITE-PRIMARY-01",
        "entries": [
            {
                "toy_id": toy_id,
                "role": role,
                "evidence_ref": rel(path),
                "evidence_sha256": sha256(path),
                "theorem_ids": theorem_ids,
                "reproduction_command": "PYTHONPATH=src:scripts python3 scripts/build_tt06_assets.py",
                "claim_ceiling": "exact finite structural toy only; no empirical or phenomenal conclusion",
            }
            for toy_id, role, path, theorem_ids in entries
        ],
        "claim_ceiling": "closure of the frozen thirteen-model exact finite primary/common toy suite",
    }
    model_path = ROOT / "models/toy_suite/TOY-SUITE-PRIMARY-01.model.json"
    write_json(model_path, spec)
    audit = audit_toy_suite(spec, ROOT)
    if not audit.toy_suite_closed:
        raise RuntimeError(f"toy suite failed: {audit.failed_obligations}")
    cert = deepcopy(spec)
    cert.update({
        "model_ref": rel(model_path),
        "model_sha256": sha256(model_path),
        "result_status": "checked-finite-primary-toy-suite-closure",
        "audit": audit.to_dict(),
        "checker": checker("cst_tt.toy_suite", "audit_toy_suite"),
    })
    cert_path = ROOT / "formal/certificates/toy_suite/TOY-SUITE-PRIMARY-01.certificate.json"
    write_json(cert_path, cert)

    feature_rows = toy_feature_rows()
    feature_path = ROOT / "models/toy_suite/TOY_FEATURE_MATRIX.json"
    write_json(feature_path, {"schema_version": PHASE, "rows": feature_rows})
    search = hidden_equivalence_search(feature_rows)
    search_path = ROOT / "formal/certificates/search/TOY_HIDDEN_EQUIVALENCE_SEARCH.json"
    write_json(search_path, search)
    return {"cert_path": cert_path, "cert": cert, "audit": audit, "feature_path": feature_path, "search": search, "search_path": search_path}


def update_registries(
    composition: dict[str, Any], fission: dict[str, Any], fusion: dict[str, Any],
    route: dict[str, Any], toys: dict[str, Any],
) -> None:
    theorem_path = ROOT / "registries/THEOREM_REGISTRY.csv"
    rows = read_csv(theorem_path)
    for row in rows:
        if row["theorem_id"] == "TTH-07":
            row.update({
                "phase": PHASE,
                "status": "proof-source-and-executable-certificate-landed",
                "lean_statement": "CSTTT.TargetTheory.fullTemporalHandoffComposition;CSTTT.TargetTheory.composedHandoffPreservesIndependentLanes;CSTTT.TargetTheory.routeIndexedComponentPreventsAutomaticFlatness",
                "toy_dependencies": "TTM-01;TTM-05;TTM-06;TTM-10",
            })
        elif row["theorem_id"] == "TTH-08":
            row.update({
                "phase": PHASE,
                "status": "proof-source-and-executable-certificate-landed",
                "lean_statement": "CSTTT.CorridorTheory.relationValuedTemporalFission;CSTTT.CorridorTheory.targetSwapPreservesFissionValidity;CSTTT.CorridorTheory.targetSwapSymmetryNonselection",
                "toy_dependencies": "TTM-07",
            })
        elif row["theorem_id"] == "TTH-09":
            declaration = "CSTTT.TargetTheory.certifiedNormalizationYieldsFlatStatus"
            parts: list[str] = []
            for item in row["lean_statement"].split(";"):
                if item and item not in parts:
                    parts.append(item)
            if declaration not in parts:
                parts.append(declaration)
            row["lean_statement"] = ";".join(parts)
        elif row["theorem_id"] == "TTN-11":
            row.update({
                "phase": PHASE,
                "status": "proof-source-and-checked-finite-countermodel",
                "lean_statement": "CSTTT.CorridorTheory.targetSwapSymmetryNonselection",
                "toy_dependencies": "TTM-07",
            })
        elif row["theorem_id"] == "TTN-14":
            row.update({
                "phase": PHASE,
                "status": "proof-source-and-checked-finite-countermodel",
                "lean_statement": "CSTTT.PackageTheory.fusionLineageDoesNotImplyIntegratedPackage;CSTTT.PackageTheory.fusionBranchwiseDoesNotRepairRecombination",
                "toy_dependencies": "TTM-07;TFM-04",
            })
    write_csv(theorem_path, list(rows[0].keys()), rows)

    toy_path = ROOT / "registries/TOY_MODEL_REGISTRY.csv"
    toy_rows = read_csv(toy_path)
    for row in toy_rows:
        if row["toy_id"] == "TTM-01":
            row.update({"phase": PHASE, "status": "checked-positive-instance", "notes": "FIACH-COMP-OUTER and FIACH-COMP-01 land a nontrivial S→M→T structural handoff composition"})
        elif row["toy_id"] == "TTM-07":
            row.update({"phase": PHASE, "status": "checked-positive-witness", "notes": "FISSION-POS-01 relates one source to two symmetric autonomous targets; CM-11 remains the unique-selector no-go control"})
    write_csv(toy_path, list(toy_rows[0].keys()), toy_rows)

    schema_rows = [
        {"schema_id": "CS-27", "file": "full_handoff_composition_certificate.schema.json", "name": "Full Temporal-FIACH composition", "claim_lanes": "S-T;S-R;S-L;A", "scaffold_example": "examples/scaffold/full_handoff_composition_certificate.scaffold.json", "status": "landed-checked-composition-certificate"},
        {"schema_id": "CS-28", "file": "temporal_fission_certificate.schema.json", "name": "Relation-valued temporal fission", "claim_lanes": "S-L;S-R;A", "scaffold_example": "examples/scaffold/temporal_fission_certificate.scaffold.json", "status": "landed-checked-fission-certificate"},
        {"schema_id": "CS-29", "file": "fusion_boundary_certificate.schema.json", "name": "Fusion/recombination boundary", "claim_lanes": "S-L;S-R", "scaffold_example": "examples/scaffold/fusion_boundary_certificate.scaffold.json", "status": "landed-checked-boundary-certificate"},
        {"schema_id": "CS-30", "file": "route_completion_certificate.schema.json", "name": "Route completion", "claim_lanes": "S-T;S-L", "scaffold_example": "examples/scaffold/route_completion_certificate.scaffold.json", "status": "landed-checked-route-completion-certificates"},
        {"schema_id": "CS-31", "file": "toy_suite_closure_certificate.schema.json", "name": "Primary toy-suite closure", "claim_lanes": "M", "scaffold_example": "examples/scaffold/toy_suite_closure_certificate.scaffold.json", "status": "landed-checked-toy-suite-certificate"},
    ]
    upsert_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv", "schema_id", schema_rows)

    write_csv(ROOT / "registries/FULL_HANDOFF_COMPOSITION_REGISTRY.csv", [
        "composition_id", "left_fiach_ref", "right_fiach_ref", "composite_fiach_ref", "intermediate_carrier", "route_status", "composition_valid", "certificate_ref", "claim_ceiling",
    ], [{
        "composition_id": "FIACH-COMP-01",
        "left_fiach_ref": rel(composition["fiach_cert_paths"]["left"]),
        "right_fiach_ref": rel(composition["fiach_cert_paths"]["right"]),
        "composite_fiach_ref": rel(composition["fiach_cert_paths"]["composite"]),
        "intermediate_carrier": MIDDLE["code"],
        "route_status": composition["full_audit"].route_status,
        "composition_valid": str(composition["full_audit"].composition_valid).lower(),
        "certificate_ref": rel(composition["full_cert_path"]),
        "claim_ceiling": composition["full_cert"]["claim_ceiling"],
    }])
    write_csv(ROOT / "registries/TEMPORAL_FISSION_REGISTRY.csv", [
        "fission_id", "source", "left_target", "right_target", "relation_valued_valid", "symmetric", "unique_selector_absent", "certificate_ref", "claim_ceiling",
    ], [{
        "fission_id": "FISSION-POS-01", "source": SOURCE["code"], "left_target": LEFT["code"], "right_target": RIGHT["code"],
        "relation_valued_valid": "true", "symmetric": str(fission["audit"].target_shapes_symmetric).lower(),
        "unique_selector_absent": str(fission["audit"].invariant_singleton_selector_absent).lower(),
        "certificate_ref": rel(fission["cert_path"]), "claim_ceiling": fission["cert"]["claim_ceiling"],
    }])
    write_csv(ROOT / "registries/FUSION_BOUNDARY_REGISTRY.csv", [
        "boundary_id", "left_source", "right_source", "target", "lineages_valid", "target_package_valid", "action_credit_conflict", "recombination_failure", "certificate_ref", "claim_ceiling",
    ], [{
        "boundary_id": "FUSION-BOUNDARY-01", "left_source": FUSION_LEFT["code"], "right_source": FUSION_RIGHT["code"], "target": FUSED["code"],
        "lineages_valid": "true", "target_package_valid": "false", "action_credit_conflict": "true", "recombination_failure": "true",
        "certificate_ref": rel(fusion["cert_path"]), "claim_ceiling": fusion["cert"]["claim_ceiling"],
    }])
    write_csv(ROOT / "registries/ROUTE_COMPLETION_REGISTRY.csv", [
        "completion_id", "mode", "output_route_status", "valid", "certificate_ref", "claim_ceiling",
    ], [
        {"completion_id": "ROUTE-COMP-INDEXED-01", "mode": "route-indexed", "output_route_status": "route-indexed", "valid": "true", "certificate_ref": rel(route["cert_paths"]["route-indexed"]), "claim_ceiling": "route-indexed structural handoff only"},
        {"completion_id": "ROUTE-COMP-FLAT-01", "mode": "flat-under-normalization", "output_route_status": "flat", "valid": "true", "certificate_ref": rel(route["cert_paths"]["flat-under-normalization"]), "claim_ceiling": "route-independent endpoint only under separately certified confluence"},
    ])
    write_csv(ROOT / "registries/TT06_TOY_CLOSURE.csv", [
        "toy_id", "role", "evidence_ref", "evidence_sha256", "theorem_ids", "status",
    ], [
        {
            "toy_id": row["toy_id"], "role": row["role"], "evidence_ref": row["evidence_ref"], "evidence_sha256": row["evidence_sha256"],
            "theorem_ids": ";".join(row["theorem_ids"]), "status": "checked",
        }
        for row in toys["cert"]["entries"]
    ])

    project = load_json(ROOT / "registries/PROJECT_REGISTRY.json")
    project["phase"] = PHASE
    project["current_phase"] = PHASE
    project["phase_base_tag"] = BASE_TAG
    project["phase_base_commit"] = BASE_COMMIT
    project["phase_status"] = "science-assets-landed"
    project["next_phase"] = "CST-TT-07A"
    project["primary_target_status"] = "Temporal-FIACH survived composition and relation-valued fission closure"
    project["primary_status"] = "exact-finite-composition-and-branching-closure-landed"
    project["fallback_status"] = "Temporal-IAPS remains locked"
    project["fallback_unlocked"] = False
    project["checked_full_handoff_composition_certificates"] = 1
    project["checked_relation_valued_fission_certificates"] = 1
    project["checked_fusion_boundary_certificates"] = 1
    project["checked_route_completion_certificates"] = 2
    project["checked_primary_common_toy_suite"] = "13/13"
    project["positive_handoff_witnesses"] = 4
    project["generic_theorem_proof_sources_landed"] = 19
    write_json(ROOT / "registries/PROJECT_REGISTRY.json", project)


def write_schemas() -> None:
    specs = {
        "full_handoff_composition_certificate.schema.json": ["certificate_id", "component_refs", "component_sha256", "audit"],
        "temporal_fission_certificate.schema.json": ["certificate_id", "branch_certificate_refs", "branch_certificate_sha256", "relation", "target_swap", "audit"],
        "fusion_boundary_certificate.schema.json": ["certificate_id", "component_refs", "component_sha256", "branchwise_payload_preserved", "audit"],
        "route_completion_certificate.schema.json": ["certificate_id", "fiach_certificate_ref", "route_certificate_ref", "mode", "audit"],
        "toy_suite_closure_certificate.schema.json": ["certificate_id", "entries", "audit"],
    }
    for name, required in specs.items():
        schema = {
            "$schema": "https://json-schema.org/draft/2020-12/schema",
            "$id": f"https://six-birds.example/cst-tt/{name}",
            "title": name.removesuffix(".schema.json").replace("_", " ").title(),
            "type": "object",
            "required": required,
            "properties": {key: {} for key in required},
            "additionalProperties": True,
        }
        path = ROOT / "schemas/certificates" / name
        write_json(path, schema)
        scaffold = {"schema_version": PHASE, **{key: ({ } if key in {"component_refs", "component_sha256", "branch_certificate_refs", "branch_certificate_sha256", "target_swap", "audit"} else [] if key in {"relation", "entries"} else "SCF") for key in required}}
        write_json(ROOT / "examples/scaffold" / name.replace(".schema.json", ".scaffold.json"), scaffold)


def write_docs(
    composition: dict[str, Any], fission: dict[str, Any], fusion: dict[str, Any],
    route: dict[str, Any], toys: dict[str, Any],
) -> None:
    docs = ROOT / "docs"
    docs.mkdir(exist_ok=True)

    (docs / "FULL_HANDOFF_COMPOSITION_THEOREM.md").write_text(f"""# Full Temporal-FIACH Composition

CST-TT-06 lands a nontrivial exact finite two-hop composition:

```text
source 17  →  autonomous intermediate 55  →  autonomous target 101
```

The composition is accepted only when all of the following are exact:

1. the left target and right source are the same carrier;
2. the audited intermediate package certificate is literally shared;
3. the terminal left temporal signature equals the initial right signature;
4. route residue and temporal ownership match at the interface;
5. the intermediate is autonomously closed after the first handoff;
6. staged clause maps factor through the same intermediate values;
7. strict corridors compose into the declared carrier-chain corridor;
8. the final target controller is inherited unchanged by the outer handoff;
9. route status composes by an explicit rule rather than by endpoint resemblance.

The finite certificate `FIACH-COMP-01` passes all {len(composition['full_audit'].to_dict()) - 6} named substantive fields and all eighteen audit obligations. The exhaustive Boolean interface check examines {composition['interface_search']['candidates_examined']} assignments; exactly {composition['interface_search']['accepted_candidates']} satisfies every premise, and every one-premise deletion is rejected.

This is a structural composition theorem/certificate layer. It does not establish consciousness, phenomenal continuity, personal survival, numerical identity, or empirical recognition.
""", encoding="utf-8")

    (docs / "RELATION_VALUED_TEMPORAL_FISSION.md").write_text(f"""# Relation-Valued Temporal Fission

One source carrier is connected by two independently valid Temporal-FIACH branches to two distinct autonomous targets. The branch structures are symmetric under the target swap `201 ↔ 202`.

The result is deliberately relation-valued:

```text
          source 17
          /       \\
 target 201       target 202
```

Both ordered pairs belong to the continuation relation. The swap is involutive, fixed-point-free, and preserves validity. Therefore the audited finite structure contains no invariant singleton target selector. This is a nonselection result, not a claim that the branches are numerically identical to the source.

The bounded symmetry search examined {fission['search']['candidates_examined']} relation/validity/permutation assignments through four targets, found {fission['search']['qualified_symmetric_forks']} qualifying symmetric forks, and found {fission['search']['invariant_singleton_selector_violations']} invariant-singleton violations.

This structural relation does not establish consciousness, phenomenal continuity, personal survival, or numerical identity.
""", encoding="utf-8")

    (docs / "FUSION_RECOMBINATION_BOUNDARY.md").write_text(f"""# Fusion and Recombination Boundary

Two strict temporal lineages can terminate at one common target while the target still fails the integrated C-package audit.

The landed witness preserves the declared branchwise payload but fails:

- **C5 action credit:** the fused target does not own a coherent target-local credit assignment;
- **C7 binding/recombination:** the branchwise data do not determine one valid joint relation.

Hence lineage merger does not imply target package realization. The exhaustive seven-gate Boolean boundary table examined {fusion['search']['candidates_examined']} assignments and contains {fusion['search']['boundary_cases']} merger-with-package-failure cases.

The result is a structural local/global and provenance boundary. It does not establish consciousness, phenomenal fusion, personal survival, or numerical identity.
""", encoding="utf-8")

    (docs / "ROUTE_COMPLETION.md").write_text(f"""# Route Completion

CST-TT-06 preserves two licensed route statuses:

| Mode | Requirement | Output |
|---|---|---|
| Route-indexed | Retain nontrivial route residue | `route-indexed` |
| Flat under normalization | Independently prove joining critical pairs, a unique normal form, and zero clock-translation holonomy | `flat` |

A negative control attempts to erase memory using the nonflat holonomy witness and is rejected. The exhaustive four-gate table contains {route['search']['candidates_examined']} cases and licenses exactly {route['search']['licensed_flat_upgrades']} flat upgrade.

Route completion changes route status only. It does not add target realization, lineage, autonomy, consciousness, or identity.
""", encoding="utf-8")

    (docs / "FULL_TOY_SUITE_CLOSURE.md").write_text(f"""# Full Primary/Common Toy-Suite Closure

All thirteen frozen primary/common toy obligations now have hash-bound exact finite evidence and reproduction commands.

{md_table(['Toy', 'Role', 'Evidence'], [(row['toy_id'], row['role'], row['evidence_ref']) for row in toys['cert']['entries']])}

The suite contains positive, negative, and boundary roles. It passes {toys['audit'].passing_toy_count}/{toys['audit'].toy_count} evidence contracts. The feature-level collision search examined {toys['search']['pairs_examined']} pairs and found {toys['search']['collision_count']} pairs with the same coarse public/endpoint signature but different structural signatures.

Toy-suite closure does not establish consciousness, phenomenal continuity, personal survival, numerical identity, or empirical recognition.
""", encoding="utf-8")

    (docs / "TT06_MINIMALITY_AND_INDEPENDENCE.md").write_text(f"""# CST-TT-06 Minimality and Independence

The phase uses bounded exact searches only for declared finite families.

| Search | Candidates | Key result |
|---|---:|---|
| Full-handoff interface | {composition['interface_search']['candidates_examined']} | all single-premise deletions rejected |
| Route completion | {route['search']['candidates_examined']} | one fully licensed flat-upgrade row |
| Fission symmetry | {fission['search']['candidates_examined']} | minimum symmetric relation-valued fork has {fission['search']['minimum_target_count']} targets |
| Fusion boundary | {fusion['search']['candidates_examined']} | lineage merger separated from package success |
| Toy hidden equivalence | {toys['search']['pairs_examined']} | coarse public equality does not collapse the structural distinctions |

These are relative bounded-search statements, not absolute mathematical minimality claims and not empirical completeness results.
""", encoding="utf-8")

    (docs / "CST-TT-06_DECISION_GATE.md").write_text("""# CST-TT-06 Decision Gate

## Decision: primary survives

Temporal-FIACH remains the primary target because:

- a complete finite witness landed in CST-TT-05;
- a nontrivial two-hop full handoff now composes through one exact autonomous intermediate;
- relation-valued fission is coherent without selecting a unique branch;
- route memory is either retained or erased only under a separate flatness certificate;
- fusion correctly exposes a package/recombination boundary rather than universalizing lineage;
- all thirteen required exact toys are closed.

No FIACH kill criterion was triggered. Temporal-IAPS therefore remains locked. The authorized next branch is CST-TT-07A, primary strengthenings.
""", encoding="utf-8")

    completion = f"""# CST-TT-06 Completion Report

CST-TT-06 lands composition, branching, route completion, fusion boundaries, and full primary/common toy-suite closure for the exact finite Temporal-FIACH program.

## Landed

- one exact two-hop full Temporal-FIACH composition through autonomous carrier 55;
- three component FIACH witnesses plus exact staged-map and corridor composition certificates;
- one relation-valued symmetric temporal-fission certificate with two valid branches;
- six fission obligation controls;
- one fusion/recombination counterexample separating lineage merger from target-package realization;
- two licensed route-completion certificates and one unlicensed-erasure control;
- one 13/13 hash-bound toy-suite closure certificate;
- four bounded exhaustive searches plus one toy feature-collision search;
- Lean proof-source modules for composition, fission, fusion boundaries, and route completion.

## Decision

Temporal-FIACH remains primary. Temporal-IAPS remains locked. CST-TT-07A is authorized.

## Claim ceiling

All results are exact finite structural theorem/certificate or checked-countermodel assets. They do not establish consciousness, felt or phenomenal continuity, personal survival, numerical identity, empirical recognition, A1, A2-P, consciousness-certificate soundness, or indefinite physical liveness.

## Toolchain boundary

Lean source contains no placeholder proof commands. Actual Lean-kernel compilation is reported only after an actual `lake build`; Python replay and exhaustive enumeration are not represented as kernel proofs.
"""
    (ROOT / "manifests/CST-TT-06_COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")
    (ROOT / "manifests/COMPLETION_REPORT.md").write_text(completion, encoding="utf-8")

    (docs / "PHASE_BOUNDARY.md").write_text("""# CST-TT-06 phase boundary

Landed: exact full-handoff composition, relation-valued fission, fusion/recombination boundary, route completion, and 13/13 primary/common toy closure.

Not landed: consciousness, felt continuity, empirical recognition, survival, numerical identity, A1/A2-P, consciousness-certificate soundness, general unbounded liveness, approximation, or the fallback Temporal-IAPS theory.

Next: CST-TT-07A primary strengthenings. CST-TT-07B remains unauthorized unless a documented FIACH kill occurs.
""", encoding="utf-8")

    (ROOT / "README.md").write_text("""# CST-TT — Temporal Substrate Transcendence Theorems and Toys

Current frozen semantic phase: **CST-TT-06**.

The repository contains exact finite structural assets for integrated target realization, heterogeneous temporal transport, strict carrier-chain lineage, withdrawal autonomy, full two-hop Temporal-FIACH composition, relation-valued fission, fusion/recombination boundaries, route completion, and the complete thirteen-model primary/common toy suite.

These assets do not establish consciousness, phenomenal continuity, survival, numerical identity, or empirical substrate transfer.
""", encoding="utf-8")
    (ROOT / "STATE.md").write_text("# Repository State\n\nCST-TT-06 science assets landed; release manifest and tag are finalized separately.\n", encoding="utf-8")
    (ROOT / "STATUS.md").write_text("# Status\n\nTemporal-FIACH survives full finite composition and branching closure. Temporal-IAPS remains locked.\n", encoding="utf-8")
    (ROOT / "RESTORE_AND_VERIFY.md").write_text(f"""# Restore and Verify CST-TT-06

```bash
export PYTHONHASHSEED=0
export PYTHONPATH=src:scripts
python3 -m pytest -q
python3 scripts/validate_tt06.py --no-write
python3 scripts/verify_tt06_rebuild.py
```

If Lean and Lake are available, run `lake build`. Absence of the toolchain is a skip, not a pass. The frozen base is `{BASE_TAG}` / `{BASE_COMMIT}`.
""", encoding="utf-8")
    (docs / "RESTORE_AND_BUILD.md").write_text((ROOT / "RESTORE_AND_VERIFY.md").read_text(encoding="utf-8"), encoding="utf-8")

    changelog = ROOT / "CHANGELOG.md"
    prior = changelog.read_text(encoding="utf-8") if changelog.exists() else "# Changelog\n"
    entry = "\n## CST-TT-06 — 2026-08-10\n\nLanded full handoff composition, relation-valued fission, fusion/recombination boundary, route completion, and 13/13 primary/common toy closure.\n"
    if "## CST-TT-06" not in prior:
        prior = prior.rstrip() + "\n" + entry
    changelog.write_text(prior, encoding="utf-8")
    (ROOT / "changelog/CST-TT-06.md").write_text(entry.lstrip(), encoding="utf-8")


def write_status_surfaces(
    composition: dict[str, Any], fission: dict[str, Any], fusion: dict[str, Any],
    route: dict[str, Any], toys: dict[str, Any],
) -> None:
    theorem_rows = [row for row in read_csv(ROOT / "registries/THEOREM_REGISTRY.csv") if row["phase"] == PHASE or row["theorem_id"] in {"TTH-09", "TTN-14"}]
    write_csv(ROOT / "manifests/CST-TT-06_THEOREM_STATUS_DELTA.csv", list(theorem_rows[0].keys()), theorem_rows)

    model_rows = [
        {"asset_id": "FIACH-COMP-01", "asset_kind": "full-handoff-composition", "status": "checked-positive", "model_ref": composition["full_cert"]["model_ref"], "certificate_ref": rel(composition["full_cert_path"]), "claim_ceiling": composition["full_cert"]["claim_ceiling"]},
        {"asset_id": "FISSION-POS-01", "asset_kind": "relation-valued-fission", "status": "checked-positive", "model_ref": fission["cert"]["model_ref"], "certificate_ref": rel(fission["cert_path"]), "claim_ceiling": fission["cert"]["claim_ceiling"]},
        {"asset_id": "FUSION-BOUNDARY-01", "asset_kind": "fusion-recombination-boundary", "status": "checked-countermodel", "model_ref": fusion["cert"]["model_ref"], "certificate_ref": rel(fusion["cert_path"]), "claim_ceiling": fusion["cert"]["claim_ceiling"]},
        {"asset_id": "ROUTE-COMP-INDEXED-01", "asset_kind": "route-completion", "status": "checked-positive", "model_ref": "", "certificate_ref": rel(route["cert_paths"]["route-indexed"]), "claim_ceiling": "route-indexed structural handoff only"},
        {"asset_id": "ROUTE-COMP-FLAT-01", "asset_kind": "route-completion", "status": "checked-positive", "model_ref": "", "certificate_ref": rel(route["cert_paths"]["flat-under-normalization"]), "claim_ceiling": "route-independent endpoint under confluence only"},
        {"asset_id": "TOY-SUITE-PRIMARY-01", "asset_kind": "toy-suite-closure", "status": "checked-13-of-13", "model_ref": toys["cert"]["model_ref"], "certificate_ref": rel(toys["cert_path"]), "claim_ceiling": toys["cert"]["claim_ceiling"]},
    ]
    for row in fission["controls"]:
        model_rows.append({"asset_id": row["control_id"], "asset_kind": "fission-control", "status": "checked-negative", "model_ref": row["model_ref"], "certificate_ref": row["certificate_ref"], "claim_ceiling": "finite fission-interface boundary only"})
    write_csv(ROOT / "manifests/CST-TT-06_MODEL_CERTIFICATE_DELTA.csv", ["asset_id", "asset_kind", "status", "model_ref", "certificate_ref", "claim_ceiling"], model_rows)

    summary = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "generated_date": DATE,
        "base_tag": BASE_TAG,
        "base_commit": BASE_COMMIT,
        "full_handoff_compositions": 1,
        "fission_branches": 2,
        "fission_controls": len(fission["controls"]),
        "fusion_boundaries": 1,
        "route_completion_certificates": 2,
        "toy_suite_pass": f"{toys['audit'].passing_toy_count}/{toys['audit'].toy_count}",
        "bounded_candidates_examined": composition["interface_search"]["candidates_examined"] + fission["search"]["candidates_examined"] + fusion["search"]["candidates_examined"] + route["search"]["candidates_examined"] + toys["search"]["pairs_examined"],
        "primary_target": "Temporal-FIACH",
        "primary_target_status": "survived",
        "fallback": "Temporal-IAPS",
        "fallback_status": "locked",
    }
    write_json(ROOT / "manifests/CST-TT-06_PHASE_SUMMARY.json", summary)
    write_json(ROOT / "manifests/PHASE_SUMMARY.json", summary)

    (ROOT / "formal/README.md").write_text("""# Formal Assets

CST-TT-06 adds proof-source modules for full Temporal-FIACH composition, relation-valued fission, fusion/recombination boundaries, and licensed route completion. Hash-bound exact finite certificates and bounded searches replay the executable semantics.

Python checks and enumeration are not proof oracles. Lean-kernel compilation is claimed only after a successful actual `lake build`.
""", encoding="utf-8")
    write_json(ROOT / "formal/TOOLCHAIN_STATUS.json", {
        "phase": PHASE,
        "lean_toolchain": "leanprover/lean4:v4.28.0",
        "lean_executable_detected_at_build": False,
        "lake_executable_detected_at_build": False,
        "lean_compile_status": "pending-toolchain",
        "python_certificate_status": "checked",
        "claim": "no Lean compilation pass is inferred by the asset builder",
    })


def main() -> int:
    write_schemas()
    composition = build_composition()
    fission = build_fission()
    fusion = build_fusion()
    route = build_route_completion(composition)
    toys = build_toy_suite(composition, fission)
    update_registries(composition, fission, fusion, route, toys)
    write_docs(composition, fission, fusion, route, toys)
    write_status_surfaces(composition, fission, fusion, route, toys)
    payload = {
        "phase": PHASE,
        "composition_valid": composition["full_audit"].composition_valid,
        "fission_valid": fission["audit"].relation_valued_fission_valid,
        "fusion_boundary_valid": fusion["audit"].fusion_boundary_valid,
        "route_certificates": len(route["cert_paths"]),
        "toy_suite": f"{toys['audit'].passing_toy_count}/{toys['audit'].toy_count}",
        "bounded_candidates": composition["interface_search"]["candidates_examined"] + fission["search"]["candidates_examined"] + fusion["search"]["candidates_examined"] + route["search"]["candidates_examined"] + toys["search"]["pairs_examined"],
    }
    print(json.dumps(payload, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
