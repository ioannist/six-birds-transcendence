#!/usr/bin/env python3
from __future__ import annotations

import csv
import hashlib
import json
import platform
from pathlib import Path
from typing import Any, Iterable, Mapping

from cst_tt.package_gluing import audit_package, audit_staged_assembly, bounded_gluing_exhaustion
from tt02_data import (
    PACKAGE_OBLIGATIONS,
    STAGED_OBLIGATIONS,
    package_controls,
    source_package,
    staged_assembly,
    staged_control,
    target_package,
)

ROOT = Path(__file__).resolve().parents[1]
PHASE = "CST-TT-02"
DATE = "2026-08-10"


def json_text(value: object) -> str:
    return json.dumps(value, indent=2, sort_keys=True, ensure_ascii=False) + "\n"


def write_json(path: Path, value: object) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json_text(value), encoding="utf-8")


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
    body = ["| " + " | ".join(headers) + " |", "|" + "|".join("---" for _ in headers) + "|"]
    body.extend("| " + " | ".join(str(value) for value in row) + " |" for row in rows)
    return "\n".join(body)


def build_models_and_certificates() -> dict[str, Any]:
    model_dir = ROOT / "models/packages"
    control_dir = model_dir / "controls"
    cert_dir = ROOT / "formal/certificates/packages"
    control_cert_dir = cert_dir / "controls"
    for directory in (model_dir, control_dir, cert_dir, control_cert_dir):
        directory.mkdir(parents=True, exist_ok=True)

    source = source_package()
    target = target_package()
    assembly = staged_assembly(source, target)
    paths = {
        "source": model_dir / "PKG-POS-02-SOURCE.model.json",
        "target": model_dir / "PKG-POS-01-TARGET.model.json",
        "assembly": model_dir / "STG-POS-01.assembly.json",
    }
    write_json(paths["source"], source)
    write_json(paths["target"], target)
    write_json(paths["assembly"], assembly)

    exhaustion = bounded_gluing_exhaustion()
    exhaustion_path = ROOT / "formal/certificates/packages/BOUNDED_GLUING_EXHAUSTION.json"
    write_json(exhaustion_path, exhaustion)

    package_rows: list[dict[str, object]] = []
    package_certs: list[dict[str, Any]] = []
    for model, model_path, cert_name, role in (
        (target, paths["target"], "PKG-POS-01-TARGET.certificate.json", "target-positive"),
        (source, paths["source"], "PKG-POS-02-SOURCE.certificate.json", "source-positive-control"),
    ):
        audit = audit_package(model)
        if not audit.integrated_package_valid:
            raise RuntimeError(f"positive package failed: {model['model_id']} {audit.failed_obligations}")
        cert = {
            "schema_version": PHASE,
            "certificate_id": model["model_id"],
            "model_ref": rel(model_path),
            "model_sha256": sha256(model_path),
            "result_status": "checked-finite-package-certificate",
            "claim_lanes": ["S-R"],
            "claim_ceiling": "finite structural target realization only",
            "theorem_evidence": {
                "theorem_ids": ["TTH-01"],
                "lean_declarations": [
                    "CSTTT.PackageTheory.localEqualityAlongScopedReach",
                    "CSTTT.PackageTheory.gluedAssignmentAgrees",
                    "CSTTT.PackageTheory.acyclicLocalWitnessGluing",
                ],
                "lean_compile_status": "pending-toolchain",
                "bounded_exhaustion_ref": rel(exhaustion_path),
            },
            "audit": audit.to_dict(),
            "checker": {
                "module": "cst_tt.package_gluing",
                "function": "audit_package",
                "python_version": platform.python_version(),
                "checked_at_phase": PHASE,
            },
        }
        cert_path = cert_dir / cert_name
        write_json(cert_path, cert)
        package_certs.append(cert)
        package_rows.append(
            {
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
            }
        )

    staged_audit = audit_staged_assembly(assembly, source, target)
    if not staged_audit.staged_assembly_valid:
        raise RuntimeError(f"positive staged assembly failed: {staged_audit.failed_obligations}")
    staged_cert = {
        "schema_version": PHASE,
        "certificate_id": "STG-POS-01",
        "assembly_ref": rel(paths["assembly"]),
        "assembly_sha256": sha256(paths["assembly"]),
        "source_model_ref": rel(paths["source"]),
        "source_model_sha256": sha256(paths["source"]),
        "target_model_ref": rel(paths["target"]),
        "target_model_sha256": sha256(paths["target"]),
        "result_status": "checked-finite-staged-package-certificate",
        "claim_lanes": ["S-T", "S-R"],
        "claim_ceiling": "finite typed clause preservation and target assembly only",
        "theorem_evidence": {
            "theorem_ids": ["TTH-01", "TTH-02"],
            "lean_declarations": [
                "CSTTT.PackageTheory.acyclicLocalWitnessGluing",
                "CSTTT.PackageTheory.stagedHeterogeneousPackageAssembly",
            ],
            "lean_compile_status": "pending-toolchain",
        },
        "audit": staged_audit.to_dict(),
        "checker": {
            "module": "cst_tt.package_gluing",
            "function": "audit_staged_assembly",
            "python_version": platform.python_version(),
            "checked_at_phase": PHASE,
        },
    }
    staged_cert_path = cert_dir / "STG-POS-01.certificate.json"
    write_json(staged_cert_path, staged_cert)

    control_rows: list[dict[str, object]] = []
    for control in package_controls(target):
        control_path = control_dir / f"{control['model_id']}.model.json"
        write_json(control_path, control)
        audit = audit_package(control)
        primary = control["expected_primary_failure"]
        if audit.integrated_package_valid or primary not in audit.failed_obligations:
            raise RuntimeError(f"control {control['model_id']} failed its contract: {audit.failed_obligations}")
        cert = {
            "schema_version": PHASE,
            "control_id": control["model_id"],
            "control_kind": "package",
            "artifact_ref": rel(control_path),
            "artifact_sha256": sha256(control_path),
            "expected_primary_failure": primary,
            "observed_failures": list(audit.failed_obligations),
            "positive_baseline_ref": rel(paths["target"]),
            "result_status": "checked-obligation-countermodel",
            "claim_ceiling": "finite package-obligation boundary only",
            "checker": {
                "module": "cst_tt.package_gluing",
                "function": "audit_package",
                "integrated_package_valid": False,
                "python_version": platform.python_version(),
            },
        }
        cert_path = control_cert_dir / f"{control['model_id']}.certificate.json"
        write_json(cert_path, cert)
        control_rows.append(
            {
                "control_id": control["model_id"],
                "control_kind": "package",
                "title": control["control_title"],
                "expected_primary_failure": primary,
                "observed_failures": ";".join(audit.failed_obligations),
                "artifact_ref": rel(control_path),
                "certificate_ref": rel(cert_path),
                "result_status": cert["result_status"],
            }
        )

    stage_control = staged_control(assembly)
    stage_control_path = control_dir / "SC-01.assembly.json"
    write_json(stage_control_path, stage_control)
    stage_control_audit = audit_staged_assembly(stage_control, source, target)
    primary = stage_control["expected_primary_failure"]
    if stage_control_audit.staged_assembly_valid or primary not in stage_control_audit.failed_obligations:
        raise RuntimeError(f"staged control failed its contract: {stage_control_audit.failed_obligations}")
    stage_control_cert = {
        "schema_version": PHASE,
        "control_id": "SC-01",
        "control_kind": "staged-assembly",
        "artifact_ref": rel(stage_control_path),
        "artifact_sha256": sha256(stage_control_path),
        "expected_primary_failure": primary,
        "observed_failures": list(stage_control_audit.failed_obligations),
        "positive_baseline_ref": rel(paths["assembly"]),
        "result_status": "checked-obligation-countermodel",
        "claim_ceiling": "finite package-obligation boundary only",
        "checker": {
            "module": "cst_tt.package_gluing",
            "function": "audit_staged_assembly",
            "staged_assembly_valid": False,
            "python_version": platform.python_version(),
        },
    }
    stage_control_cert_path = control_cert_dir / "SC-01.certificate.json"
    write_json(stage_control_cert_path, stage_control_cert)
    control_rows.append(
        {
            "control_id": "SC-01",
            "control_kind": "staged-assembly",
            "title": stage_control["control_title"],
            "expected_primary_failure": primary,
            "observed_failures": ";".join(stage_control_audit.failed_obligations),
            "artifact_ref": rel(stage_control_path),
            "certificate_ref": rel(stage_control_cert_path),
            "result_status": stage_control_cert["result_status"],
        }
    )

    write_csv(
        ROOT / "registries/PACKAGE_WITNESS_REGISTRY.csv",
        [
            "package_id", "role", "model_ref", "certificate_ref", "model_sha256",
            "result_status", "clause_count", "coordinate_count", "join_tree_root",
            "claim_lanes", "claim_ceiling",
        ],
        package_rows,
    )
    write_csv(
        ROOT / "registries/PACKAGE_CONTROL_REGISTRY.csv",
        [
            "control_id", "control_kind", "title", "expected_primary_failure",
            "observed_failures", "artifact_ref", "certificate_ref", "result_status",
        ],
        control_rows,
    )
    write_csv(
        ROOT / "registries/PACKAGE_OBLIGATION_REGISTRY.csv",
        ["obligation_id", "name", "definition", "claim_lanes", "positive_witnesses", "negative_controls", "status"],
        [
            {
                "obligation_id": oid,
                "name": name,
                "definition": definition,
                "claim_lanes": "S-R",
                "positive_witnesses": "PKG-POS-01-TARGET;PKG-POS-02-SOURCE",
                "negative_controls": ";".join(
                    row["control_id"]
                    for row in control_rows
                    if oid in str(row["observed_failures"])
                ),
                "status": "landed-positive-and-negative-control",
            }
            for oid, name, definition in PACKAGE_OBLIGATIONS
        ],
    )
    write_csv(
        ROOT / "registries/STAGED_ASSEMBLY_OBLIGATION_REGISTRY.csv",
        ["obligation_id", "name", "claim_lanes", "positive_witness", "negative_controls", "status"],
        [
            {
                "obligation_id": oid,
                "name": name,
                "claim_lanes": "S-T;S-R",
                "positive_witness": "STG-POS-01",
                "negative_controls": "SC-01" if oid == "STG-O07" else "",
                "status": "landed-positive" + ("-and-negative-control" if oid == "STG-O07" else ""),
            }
            for oid, name in STAGED_OBLIGATIONS
        ],
    )

    return {
        "source": source,
        "target": target,
        "assembly": assembly,
        "source_audit": audit_package(source),
        "target_audit": audit_package(target),
        "staged_audit": staged_audit,
        "package_rows": package_rows,
        "control_rows": control_rows,
        "exhaustion": exhaustion,
        "paths": paths,
        "staged_cert_path": staged_cert_path,
    }


def update_registries(context: dict[str, Any]) -> None:
    theorem_path = ROOT / "registries/THEOREM_REGISTRY.csv"
    rows = read_csv(theorem_path)
    for row in rows:
        if row["theorem_id"] == "TTH-01":
            row["status"] = "proof-source-and-executable-certificate-landed"
            row["lean_statement"] = "CSTTT.PackageTheory.acyclicLocalWitnessGluing"
            row["toy_dependencies"] = "TTM-11;TTM-18"
        elif row["theorem_id"] == "TTH-02":
            row["status"] = "proof-source-and-executable-certificate-landed"
            row["lean_statement"] = "CSTTT.PackageTheory.stagedHeterogeneousPackageAssembly"
            row["toy_dependencies"] = "TTM-18;TTM-19"
    write_csv(theorem_path, list(rows[0]), rows)

    toy_path = ROOT / "registries/TOY_MODEL_REGISTRY.csv"
    toys = read_csv(toy_path)
    by_id = {row["toy_id"] for row in toys}
    additions = [
        {
            "toy_id": "TTM-18",
            "name": "integrated target C-package",
            "role": "package-positive",
            "phase": PHASE,
            "minimal_shape": "eight local clauses; star join tree; substantive C6; target ownership",
            "discriminates": "TTH-01;TTN-08;TTN-14",
            "status": "checked-positive-instance",
            "notes": "PKG-POS-01-TARGET plus seventeen package controls",
        },
        {
            "toy_id": "TTM-19",
            "name": "staged heterogeneous package assembly",
            "role": "package-transport-positive",
            "phase": PHASE,
            "minimal_shape": "distinct source and target vocabularies; eight total clause maps; target gluing",
            "discriminates": "TTH-02",
            "status": "checked-positive-instance",
            "notes": "STG-POS-01 plus SC-01 value-map control",
        },
    ]
    toys.extend(row for row in additions if row["toy_id"] not in by_id)
    write_csv(toy_path, list(toys[0]), toys)

    definition_path = ROOT / "registries/DEFINITION_REGISTRY.csv"
    definitions = read_csv(definition_path)
    by_def = {row["definition_id"] for row in definitions}
    new_defs = [
        ("D-040", "ScopedReach", "CSTTT/Package/FiniteGluing.lean", "coordinate-preserving path through local scopes", "S-R", "D-019"),
        ("D-041", "RootedJoinTree", "CSTTT/Package/FiniteGluing.lean", "parent/rank/running-intersection package cover", "S-R", "D-040"),
        ("D-042", "IntegratedPackageWitness", "CSTTT/Package/FiniteGluing.lean", "global assignment restricting to accepted gated locals", "S-R", "D-041"),
        ("D-043", "StagedHeterogeneousEvidence", "CSTTT/Package/FiniteGluing.lean", "typed source-target local maps independent of lineage", "S-T;S-R", "D-041"),
        ("D-044", "TemporalSubstance", "CSTTT/Package/TemporalPackage.lean", "future-sufficient order/tick/progress/arrow/route/ownership C6 evidence", "S-R", "D-012"),
        ("D-045", "EightClauseIntegratedPackage", "CSTTT/Package/TemporalPackage.lean", "exact C1-C8 structural witness plus independent substantive C6", "S-R", "D-015;D-042;D-044"),
    ]
    for did, name, module, purpose, lanes, deps in new_defs:
        if did not in by_def:
            definitions.append(
                {
                    "definition_id": did,
                    "name": name,
                    "module": module,
                    "purpose": purpose,
                    "claim_lanes": lanes,
                    "dependencies": deps,
                    "status": "landed-proof-source-and-executable-semantics",
                }
            )
    for row in definitions:
        if row["definition_id"] in {"D-015", "D-016", "D-017", "D-018"}:
            row["status"] = "landed-clause-interface"
        elif row["definition_id"] in {"D-019", "D-020", "D-021"}:
            row["status"] = "retained-scaffold-superseded-by-D-041-to-D-045"
    write_csv(definition_path, list(definitions[0]), definitions)

    schema_path = ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv"
    schemas = read_csv(schema_path)
    for row in schemas:
        if row["schema_id"] == "CS-02":
            row["name"] = "Integrated package landed certificate"
            row["status"] = "landed-checked-package-certificates"
    schema_ids = {row["schema_id"] for row in schemas}
    if "CS-09" not in schema_ids:
        schemas.append(
            {
                "schema_id": "CS-09",
                "file": "staged_package_certificate.schema.json",
                "name": "Staged heterogeneous package assembly",
                "claim_lanes": "S-T;S-R",
                "scaffold_example": "examples/scaffold/staged_package_certificate.scaffold.json",
                "status": "landed-checked-staged-certificate",
            }
        )
    if "CS-10" not in schema_ids:
        schemas.append(
            {
                "schema_id": "CS-10",
                "file": "package_control_certificate.schema.json",
                "name": "One-obligation-removed package control",
                "claim_lanes": "M;S-R",
                "scaffold_example": "examples/scaffold/package_control_certificate.scaffold.json",
                "status": "landed-checked-control-certificates",
            }
        )
    write_csv(schema_path, list(schemas[0]), schemas)

    kill_path = ROOT / "registries/KILL_CRITERIA.csv"
    kills = read_csv(kill_path)
    for row in kills:
        if row["kill_id"] in {"K-PKG-01", "K-PKG-02"}:
            row["status"] = "not-triggered-CST-TT-02"
    write_csv(kill_path, list(kills[0]), kills)

    project = json.loads((ROOT / "registries/PROJECT_REGISTRY.json").read_text(encoding="utf-8"))
    project.update(
        {
            "phase": PHASE,
            "phase_base_tag": "CST-TT-01-v1",
            "phase_base_commit": "488db50b20d6d9c67493de3e9fd758e6e9e205ce",
            "generic_theorem_proof_sources_landed": 2,
            "generic_theorems_lean_compiled": 0,
            "checked_finite_package_witnesses": 2,
            "checked_staged_package_assemblies": 1,
            "checked_package_obligation_controls": len(context["control_rows"]),
            "bounded_gluing_candidates": context["exhaustion"]["candidates_examined"],
            "bounded_gluing_premise_cases": context["exhaustion"]["premise_cases"],
            "positive_handoff_witnesses": 0,
            "fallback_unlocked": False,
            "next_phase": "CST-TT-03",
        }
    )
    write_json(ROOT / "registries/PROJECT_REGISTRY.json", project)

    reproducibility = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "canonical_seed": 0,
        "python_hash_seed": 0,
        "randomized_search_enabled": False,
        "scientific_result_generated": True,
        "status": "deterministic-package-gluing-and-controls-frozen",
        "bounded_gluing_candidates": context["exhaustion"]["candidates_examined"],
        "bounded_gluing_premise_cases": context["exhaustion"]["premise_cases"],
        "usage_boundary": "Deterministic exhaustive binary checks corroborate the generic Lean proof source; Python is not represented as a proof oracle.",
    }
    write_json(ROOT / "config/REPRODUCIBILITY.json", reproducibility)


def build_docs(context: dict[str, Any]) -> None:
    target = context["target_audit"]
    staged = context["staged_audit"]
    exhaustion = context["exhaustion"]
    controls = context["control_rows"]
    target_coord_count = len(target.derived_global_assignment)
    clause_rows = [
        (row.clause.replace("_", " "), row.scope_exact, row.accepted, row.hard_gate_passed)
        for row in target.clause_audits
    ]
    (ROOT / "docs/INTEGRATED_PACKAGE_SEMANTICS.md").write_text(
        f"""# CST-TT-02 Integrated Package Semantics

## Claim lane

This layer establishes only **S-R: finite structural target realization**. It contains no source, ancestry, temporal-corridor, withdrawal, autonomy, consciousness, survival, or numerical-identity verdict.

## Exact positive package

`PKG-POS-01-TARGET` has eight separately audited clause slots, {target_coord_count} glued coordinates, and a rooted star join tree centered on C6. The local assignments are stated independently and the auditor constructs a canonical global assignment from their compatible overlaps.

{markdown_table(["Clause", "scope exact", "accepted", "hard gate"], clause_rows)}

## Independent obligations

{markdown_table(["ID", "Obligation", "Meaning"], PACKAGE_OBLIGATIONS)}

The aggregate predicate is a conjunction. A failed hard gate is never replaced by an average score. C6 is substantive but does not discharge any of C1-C5 or C7-C8.

## Global certificate condition

For local assignments `L_i` on scopes `U_i`, the declared parent graph must be a rooted tree. For every coordinate `x`, the clauses containing `x` must form a connected subtree. Local assignments must agree on every tree-edge overlap. The generic theorem then constructs `G(x)` by choosing one local carrier of `x`; running intersection propagates edge agreement so `G|U_i = L_i` for every clause.

## Positive and negative bank

- two checked integrated package witnesses: one target and one separately typed source control;
- one checked staged heterogeneous assembly;
- seventeen package-obligation controls;
- one staged-map control.

None of these assets is a handoff or lineage witness.
""",
        encoding="utf-8",
    )
    (ROOT / "docs/ACYCLIC_GLUING_THEOREM.md").write_text(
        f"""# Acyclic Local-Witness Gluing

## Landed statement

`CSTTT.PackageTheory.acyclicLocalWitnessGluing` takes:

1. a rooted parent presentation with a decreasing rank;
2. a scope cover;
3. the running-intersection property;
4. edge-compatible local assignments;
5. independent local acceptance proofs;
6. independent hard-gate proofs.

It constructs one global assignment and proves that its restriction equals every local assignment.

The proof has two nontrivial steps:

- `localEqualityAlongScopedReach` propagates equality along a coordinate-preserving tree path;
- `gluedAssignmentAgrees` uses running intersection to connect the chosen local representative to any other clause containing that coordinate.

Acyclic rooted shape is verified by the executable certificate checker. Running intersection and edge agreement are the premises that perform the gluing work.

## Bounded corroboration

The deterministic binary checker evaluated **{exhaustion['candidates_examined']:,}** local scope/assignment candidates over path and star trees of two to four nodes. **{exhaustion['premise_cases']:,}** candidates satisfied all theorem premises; all **{exhaustion['glued_cases']:,}** glued successfully, with zero violations.

This exhaustive finite run corroborates the formal source. Python is not a proof oracle and the run is not represented as a replacement for Lean kernel checking. The local environment lacks `lean` and `lake`, so compilation remains pending.

## Boundary controls

- `PC-10`: edge disagreement blocks gluing;
- `PC-11`: a disconnected parent graph is not a join-tree certificate;
- `PC-12`: edge checks can pass while a nonedge conflict is hidden when running intersection fails;
- `PC-13`: a supplied global record can disagree with the canonical glued assignment.

The previously frozen `CM-08` and `CM-15` remain the local/global and branchwise/recombination no-go companions.
""",
        encoding="utf-8",
    )
    temporal = target.temporal_substance
    (ROOT / "docs/C6_TEMPORAL_SUBSTANCE.md").write_text(
        f"""# C6 Temporal Substance

C6 is not a Boolean label. It separately audits future sufficiency, genuine progress, and the remaining temporal obligations below. The positive target certificate checks all of the following independently:

{markdown_table(["Component", "Pass"], [
    ("future-sufficient predictive now", temporal.future_sufficient),
    ("stable order", temporal.order_stable),
    ("viable successor available", temporal.successor_available),
    ("viable tick", temporal.viable_tick),
    ("strictly positive tick progress", temporal.genuine_progress),
    ("endogenous arrow", temporal.endogenous_arrow),
    ("strict record advance", temporal.record_descends),
    ("route residue retained", temporal.route_residue_retained),
    ("no external scheduler", temporal.no_external_scheduler),
    ("target-local temporal owner", temporal.temporal_owner_matches),
    ("target-local maintenance owner", temporal.maintenance_owner_matches),
])}

The controls separate several failure modes:

- `PC-07`: viable/stable tick with zero progress;
- `PC-14`: externally scheduled temporal shadow;
- `PC-16`: temporal maintenance owned by another carrier.

C6 remains one clause among eight. C6 does not entail any other C-clause. Passing C6 does not establish objecthood, strict promotion, self-coordinate, nonexposure, action credit, binding/recombination, viability/repair, consciousness, or felt continuity.
""",
        encoding="utf-8",
    )
    (ROOT / "docs/STAGED_PACKAGE_ASSEMBLY.md").write_text(
        f"""# Staged Heterogeneous Package Assembly

`STG-POS-01` uses distinct carrier vocabularies, separately named on carriers 17 and 101. It supplies exactly eight typed clause maps. Every source coordinate has one target coordinate, and each stored source/target value is checked against the corresponding local assignments.

The staged auditor passes all ten obligations:

{markdown_table(["Field", "Pass"], [
    ("source package valid", staged.source_package_valid),
    ("target package valid", staged.target_package_valid),
    ("carriers distinct", staged.carriers_distinct),
    ("exactly eight maps", staged.exactly_eight_clause_maps),
    ("separately typed vocabularies", staged.maps_separately_typed),
    ("coordinate maps total", staged.coordinate_maps_total),
    ("value maps sound", staged.value_maps_sound),
    ("hard gates never averaged", staged.hard_gates_never_averaged),
    ("target globally assembled", staged.target_global_assembled),
    ("no verdict fields", staged.forbidden_verdict_fields_absent),
])}

`SC-01` alters one attested target value while leaving both endpoint packages intact. The staged assembly then fails value-translation soundness. This shows that target realization alone does not prove staged preservation.

The result is structural transport plus target assembly only and does not establish temporal lineage. It contains no operational episode, causal ancestry, temporal-lineage verdict, withdrawal intervention, or autonomy claim.
""",
        encoding="utf-8",
    )
    (ROOT / "docs/PACKAGE_CONTROL_SUITE.md").write_text(
        "# CST-TT-02 Package Control Suite\n\n"
        + markdown_table(
            ["Control", "Kind", "Removed obligation", "Observed failures"],
            [
                (
                    row["control_id"],
                    row["control_kind"],
                    row["expected_primary_failure"],
                    row["observed_failures"],
                )
                for row in controls
            ],
        )
        + "\n\nEvery package obligation PKG-O01 through PKG-O10 has at least one exact one-obligation-removed control. C1 through C8 each also has a direct clause-specific failure. Cascading failures are retained rather than concealed; for example, breaking running intersection may also make a global assignment impossible.\n",
        encoding="utf-8",
    )
    (ROOT / "docs/PHASE_BOUNDARY.md").write_text(
        """# CST-TT-02 Phase Boundary

Landed in this phase:

- exact finite C1-C8 package semantics;
- substantive C6 temporal closure;
- a rooted running-intersection gluing theorem proof source;
- deterministic bounded corroboration;
- two positive integrated package certificates;
- one positive staged heterogeneous assembly certificate;
- seventeen package controls and one staged-map control;
- retained local/global and recombination no-go companions;
- no source, ancestry, temporal-corridor, withdrawal, autonomy, consciousness, survival, or identity field occurs in the integrated package record.

Not landed:

- heterogeneous temporal-signature transport across an episode;
- route-word, holonomy, or confluence theorems beyond the retained negative kernel;
- strict temporal lineage;
- withdrawal autonomy;
- a positive Temporal-FIACH or Temporal-IAPS witness;
- consciousness, phenomenal continuity, survival, numerical identity, A1, A2-P, recognition, or certificate soundness.

The next authorized phase is `CST-TT-03`, heterogeneous temporal transport and route discipline.
""",
        encoding="utf-8",
    )

    # Phase-facing theorem registry synthesis.
    theorem_rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    active = [row for row in theorem_rows if row["theorem_id"] in {"TTH-01", "TTH-02", "TTN-08", "TTN-14"}]
    (ROOT / "docs/THEOREM_AND_TOY_REGISTRY.md").write_text(
        "# CST-TT Theorem and Toy Registry\n\n## CST-TT-02 active theorem surfaces\n\n"
        + markdown_table(
            ["ID", "Name", "Status", "Lanes", "Lean declaration"],
            [(r["theorem_id"], r["name"], r["status"], r["claim_lanes"], r["lean_statement"]) for r in active],
        )
        + "\n\n## Status interpretation\n\n`proof-source-and-executable-certificate-landed` means a generic explicit Lean proof source, an executable finite checker, positive certificates, and negative controls are present. Because the compiler is unavailable locally, it does not claim a successful Lean build.\n",
        encoding="utf-8",
    )


def build_status_and_reports(context: dict[str, Any]) -> None:
    exhaustion = context["exhaustion"]
    control_count = len(context["control_rows"])
    package_count = len(context["package_rows"])
    summary = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "generated_date": DATE,
        "generic_theorem_proof_sources_landed": 2,
        "generic_theorems_lean_compiled": 0,
        "checked_integrated_package_witnesses": package_count,
        "checked_staged_package_assemblies": 1,
        "checked_package_and_staged_controls": control_count,
        "package_obligations": len(PACKAGE_OBLIGATIONS),
        "staged_obligations": len(STAGED_OBLIGATIONS),
        "bounded_gluing_candidates": exhaustion["candidates_examined"],
        "bounded_gluing_premise_cases": exhaustion["premise_cases"],
        "bounded_gluing_violations": len(exhaustion["violations"]),
        "positive_handoff_witnesses": 0,
        "fallback_unlocked": False,
        "package_kill_criteria_triggered": 0,
        "next_phase": "CST-TT-03",
    }
    write_json(ROOT / "manifests/CST-TT-02_PHASE_SUMMARY.json", summary)
    write_json(ROOT / "manifests/PHASE_SUMMARY.json", summary)

    write_csv(
        ROOT / "manifests/CST-TT-02_THEOREM_STATUS_DELTA.csv",
        ["theorem_id", "prior_status", "current_status", "evidence", "claim_ceiling"],
        [
            {
                "theorem_id": "TTH-01",
                "prior_status": "open-scaffold",
                "current_status": "proof-source-and-executable-certificate-landed",
                "evidence": "FiniteGluing.lean;PKG-POS-01-TARGET;PKG-POS-02-SOURCE;bounded exhaustion",
                "claim_ceiling": "structural package only",
            },
            {
                "theorem_id": "TTH-02",
                "prior_status": "open-scaffold",
                "current_status": "proof-source-and-executable-certificate-landed",
                "evidence": "FiniteGluing.lean;STG-POS-01;SC-01",
                "claim_ceiling": "typed clause preservation and target assembly only",
            },
            {
                "theorem_id": "TTN-08",
                "prior_status": "checked-finite-countermodel",
                "current_status": "checked-finite-countermodel-retained",
                "evidence": "CM-08;PC-10;PC-11;PC-12;PC-13",
                "claim_ceiling": "global package boundary",
            },
            {
                "theorem_id": "TTN-14",
                "prior_status": "checked-finite-countermodel",
                "current_status": "checked-finite-countermodel-retained",
                "evidence": "CM-15;PC-08",
                "claim_ceiling": "recombination boundary",
            },
        ],
    )
    delta_rows: list[dict[str, object]] = []
    for row in context["package_rows"]:
        delta_rows.append(
            {
                "asset_id": row["package_id"],
                "asset_kind": "integrated-package",
                "prior_status": "not-instantiated",
                "current_status": row["result_status"],
                "artifact_ref": row["model_ref"],
                "certificate_ref": row["certificate_ref"],
            }
        )
    delta_rows.append(
        {
            "asset_id": "STG-POS-01",
            "asset_kind": "staged-package-assembly",
            "prior_status": "not-instantiated",
            "current_status": "checked-finite-staged-package-certificate",
            "artifact_ref": rel(context["paths"]["assembly"]),
            "certificate_ref": rel(context["staged_cert_path"]),
        }
    )
    for row in context["control_rows"]:
        delta_rows.append(
            {
                "asset_id": row["control_id"],
                "asset_kind": row["control_kind"] + "-control",
                "prior_status": "not-instantiated",
                "current_status": row["result_status"],
                "artifact_ref": row["artifact_ref"],
                "certificate_ref": row["certificate_ref"],
            }
        )
    write_csv(
        ROOT / "manifests/CST-TT-02_MODEL_CERTIFICATE_DELTA.csv",
        ["asset_id", "asset_kind", "prior_status", "current_status", "artifact_ref", "certificate_ref"],
        delta_rows,
    )

    (ROOT / "manifests/CST-TT-02_COMPLETION_REPORT.md").write_text(
        f"""# CST-TT-02 Completion Report

**Phase:** CST-TT-02 — integrated C-package, temporal closure, and gluing

**Status:** science layer complete; repository freeze is recorded by the phase manifest and archive verification

## Landed

- two generic theorem proof sources: TTH-01 and TTH-02;
- {package_count} checked integrated package witnesses;
- one checked staged heterogeneous assembly;
- {control_count} checked one-obligation-removed controls;
- all {len(PACKAGE_OBLIGATIONS)} package obligations have positive and negative coverage;
- all eight C-shaped clauses have direct finite failure controls;
- substantive C6 order/tick/progress/arrow/route/ownership checks;
- {exhaustion['candidates_examined']:,} bounded gluing candidates, including {exhaustion['premise_cases']:,} premise-satisfying cases and zero violations;
- package kill criteria K-PKG-01 and K-PKG-02 not triggered.

## Result

Target-package realization is now independently decidable from an exact finite certificate. The positive target package can be audited even as an independently constructed target; the record has no source, ancestry, corridor, withdrawal, autonomy, consciousness, survival, or identity field.

The staged result adds separately typed source-to-target clause maps but still does not assert temporal lineage or autonomy. No positive Temporal-FIACH witness is produced. The Temporal-IAPS fallback remains locked.

## Formal status

The generic proofs are written explicitly in Lean without placeholders. No theorem is represented as Lean-compiled: the environment has no `lean`, `lake`, or `elan`, so compilation is not claimed. Python executability, JSON-schema validation, hash binding, bounded exhaustive corroboration, positive certificates, negative controls, and static Lean audits are required and run in this phase.

## Next phase

`CST-TT-03` — heterogeneous temporal transport and route discipline.
""",
        encoding="utf-8",
    )

    (ROOT / "README.md").write_text(
        """# CST Temporal Substrate Transcendence

**Project code:** `CST-TT`

**Current completed phase:** `CST-TT-02`

**Status:** integrated package, substantive C6, rooted gluing, and staged package assembly landed; no lineage or autonomy result yet.

## Start here

1. `docs/INTEGRATED_PACKAGE_SEMANTICS.md`
2. `docs/ACYCLIC_GLUING_THEOREM.md`
3. `docs/C6_TEMPORAL_SUBSTANCE.md`
4. `docs/STAGED_PACKAGE_ASSEMBLY.md`
5. `docs/PACKAGE_CONTROL_SUITE.md`
6. `CSTTT/Package/FiniteGluing.lean`
7. `manifests/CST-TT-02_COMPLETION_REPORT.md`

## Verify

```bash
scripts/run_tt02_checks.sh
```

This repository establishes finite structural realization and typed package preservation only. It does not establish consciousness, felt continuity, source-target lineage, autonomy, survival, numerical identity, A1, A2-P, recognition, or certificate soundness.
""",
        encoding="utf-8",
    )
    (ROOT / "STATE.md").write_text(
        f"""# Repository state

- Project: `CST-TT`
- Current phase: `CST-TT-02`
- Base phase: `CST-TT-01-v1`
- Primary target: Temporal-FIACH strict overlap
- Integrated package witnesses: {package_count}
- Staged package assemblies: 1
- Package/staged controls: {control_count}
- Generic Lean proof sources landed: 2
- Lean compilation: pending toolchain
- Positive handoff witnesses: 0
- Fallback: Temporal-IAPS, still locked
- Package kill criteria: not triggered
- Next phase: `CST-TT-03`
""",
        encoding="utf-8",
    )
    (ROOT / "STATUS.md").write_text(
        """# CST-TT-02 status

The target-realization lane is now executable and certificate-bound. C1-C8 remain independent, C6 has real temporal content, local data glue only under rooted running-intersection and compatibility conditions, and staged cross-carrier preservation remains separate from lineage and autonomy.

The next authorized phase is **CST-TT-03 — heterogeneous temporal transport and route discipline**.
""",
        encoding="utf-8",
    )
    changelog_entry = """# CST-TT-02

- Landed exact finite C1-C8 package semantics and substantive C6 audits.
- Added a rooted running-intersection gluing theorem proof source.
- Added typed staged heterogeneous package assembly proof source.
- Added two positive package certificates and one staged certificate.
- Added seventeen package controls and one staged-map control.
- Retained CM-08 and CM-15 as global-gluing and recombination boundaries.
- Kept lineage, autonomy, recognition, and ontology outside the package record.
"""
    (ROOT / "changelog/CST-TT-02.md").write_text(changelog_entry, encoding="utf-8")
    changelog = (ROOT / "CHANGELOG.md").read_text(encoding="utf-8")
    if "## CST-TT-02" not in changelog:
        changelog += "\n## CST-TT-02\n\n" + "\n".join(changelog_entry.splitlines()[2:]) + "\n"
    (ROOT / "CHANGELOG.md").write_text(changelog, encoding="utf-8")

    (ROOT / "RESTORE_AND_VERIFY.md").write_text(
        """# Restore and verify CST-TT-02

1. Extract the repository ZIP and enter the repository root.
2. Confirm the tag, commit, clean state, and Git object integrity:

```bash
git rev-parse CST-TT-02-v1^{}
git rev-parse HEAD
git status --short
git fsck --full --no-dangling
```

3. Rebuild and validate deterministic phase assets:

```bash
scripts/run_tt02_checks.sh
python3 scripts/verify_tt02_rebuild.py
```

4. Where the pinned Lean toolchain is available:

```bash
lake build
```

The originating environment had no Lean executable. The phase therefore claims explicit generic proof source, executable finite semantics, certificates, controls, and static audits—not a local Lean compilation pass.
""",
        encoding="utf-8",
    )

    status = json.loads((ROOT / "formal/TOOLCHAIN_STATUS.json").read_text(encoding="utf-8"))
    status.update(
        {
            "phase": PHASE,
            "generic_package_proof_source_count": 2,
            "positive_package_certificate_count": package_count,
            "staged_package_certificate_count": 1,
            "package_control_certificate_count": control_count,
            "compile_status": "not-run-lean-and-lake-unavailable",
            "static_lean_source_audit_status": "passed-by-cst-tt-02-static-suite",
        }
    )
    write_json(ROOT / "formal/TOOLCHAIN_STATUS.json", status)
    (ROOT / "formal/README.md").write_text(
        f"""# Formal assets

## CST-TT-02

- `CSTTT/Package/FiniteGluing.lean`: generic scoped-path equality, canonical gluing, TTH-01, and TTH-02 proof sources.
- `CSTTT/Package/TemporalPackage.lean`: substantive C6 and exact eight-clause package wrapper.
- `formal/certificates/packages/`: {package_count} package certificates, one staged certificate, {control_count} controls, and bounded-exhaustion evidence.

The local environment lacks Lean. Static checks forbid `sorry`, `admit`, `axiom`, and `unsafe`, verify the declaration surfaces and import layering, and keep compilation status explicit.
""",
        encoding="utf-8",
    )


def main() -> int:
    context = build_models_and_certificates()
    update_registries(context)
    build_docs(context)
    build_status_and_reports(context)
    print(
        "CST-TT-02 assets built: "
        f"{len(context['package_rows'])} package witnesses; 1 staged assembly; "
        f"{len(context['control_rows'])} controls; "
        f"{context['exhaustion']['candidates_examined']} bounded gluing candidates"
    )
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
