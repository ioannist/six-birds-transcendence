#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import py_compile
import re
import shutil
import subprocess
import sys
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Callable, Iterable

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from cst_tt.circularity import scan_primitive_tree  # noqa: E402
from cst_tt.package_gluing import audit_package, audit_staged_assembly, bounded_gluing_exhaustion  # noqa: E402
from cst_tt.registry import duplicate_values, read_csv  # noqa: E402

PHASE = "CST-TT-02"
BASE_TAG = "CST-TT-01-v1"
BASE_COMMIT = "488db50b20d6d9c67493de3e9fd758e6e9e205ce"
PHASE_TAG = "CST-TT-02-v1"


@dataclass(frozen=True)
class Result:
    check_id: str
    category: str
    status: str
    detail: str


class Validation:
    def __init__(self) -> None:
        self.results: list[Result] = []

    def check(self, check_id: str, category: str, condition: bool, detail: str) -> None:
        self.results.append(Result(check_id, category, "PASS" if condition else "FAIL", detail))

    def skip(self, check_id: str, category: str, detail: str) -> None:
        self.results.append(Result(check_id, category, "SKIP", detail))

    def guarded(self, check_id: str, category: str, detail: str, fn: Callable[[], bool]) -> None:
        try:
            self.check(check_id, category, bool(fn()), detail)
        except Exception as exc:  # validation should record, not crash
            self.check(check_id, category, False, f"{detail}: {type(exc).__name__}: {exc}")

    @property
    def failures(self) -> list[Result]:
        return [row for row in self.results if row.status == "FAIL"]


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def split_ids(value: str) -> set[str]:
    return {item for item in value.split(";") if item}


def check_baseline(v: Validation, require_clean: bool, require_tag: bool) -> None:
    v.guarded("BASE-001", "baseline", "repository is a Git worktree", lambda: git("rev-parse", "--is-inside-work-tree") == "true")
    v.guarded("BASE-002", "baseline", "CST-TT-01 tag resolves to the frozen phase base", lambda: git("rev-parse", BASE_TAG + "^{}") == BASE_COMMIT)
    v.guarded(
        "BASE-003",
        "baseline",
        "frozen CST-TT-01 base is an ancestor of current HEAD",
        lambda: subprocess.run(["git", "merge-base", "--is-ancestor", BASE_COMMIT, "HEAD"], cwd=ROOT).returncode == 0,
    )
    v.guarded("BASE-004", "baseline", "repository has no whitespace errors", lambda: subprocess.run(["git", "diff", "--check"], cwd=ROOT, capture_output=True).returncode == 0)
    if require_clean:
        v.guarded("BASE-005", "baseline", "working tree is clean before validation", lambda: git("status", "--porcelain") == "")
    else:
        v.skip("BASE-005", "baseline", "clean-tree check not requested for this pass")
    tags = set(git("tag", "--list").splitlines())
    if require_tag:
        v.check("BASE-006", "baseline", PHASE_TAG in tags, f"phase tag {PHASE_TAG} exists")
        if PHASE_TAG in tags:
            v.check("BASE-007", "baseline", git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD"), "phase tag resolves to current HEAD")
    elif PHASE_TAG in tags:
        v.check("BASE-006", "baseline", git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD"), "existing phase tag resolves to current HEAD")
    else:
        v.skip("BASE-006", "baseline", "phase tag not required before freeze commit")


def check_toolchain(v: Validation) -> None:
    v.check("TOOL-001", "toolchain", (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.28.0", "Lean toolchain remains pinned to v4.28.0")
    pyproject = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    for index, token in enumerate((">=3.13,<3.14", "pytest==9.0.2", "jsonschema==4.26.0", "setuptools==82.0.1", 'version = "0.1.0"'), 1):
        v.check(f"TOOL-PIN-{index:02d}", "toolchain", token in pyproject, f"pyproject contains {token}")
    v.check("TOOL-007", "toolchain", sys.version_info[:2] == (3, 13), f"running Python is 3.13 (found {sys.version.split()[0]})")
    lean = shutil.which("lean")
    lake = shutil.which("lake")
    if lean and lake:
        proc = subprocess.run([lake, "build"], cwd=ROOT, text=True, capture_output=True)
        v.check("TOOL-LEAN-BUILD", "toolchain", proc.returncode == 0, "pinned Lean sources compile with lake build")
    else:
        v.skip("TOOL-LEAN-BUILD", "toolchain", "lean/lake unavailable; no compilation pass claimed")
    status = load_json(ROOT / "formal/TOOLCHAIN_STATUS.json")
    assert isinstance(status, dict)
    v.check("TOOL-STATUS-1", "toolchain", status.get("phase") == PHASE, "toolchain status names CST-TT-02")
    v.check("TOOL-STATUS-2", "toolchain", status.get("generic_package_proof_source_count") == 2, "toolchain status records two generic package proof sources")
    v.check("TOOL-STATUS-3", "toolchain", status.get("positive_package_certificate_count") == 2, "toolchain status records two positive package certificates")
    v.check("TOOL-STATUS-4", "toolchain", status.get("staged_package_certificate_count") == 1, "toolchain status records one staged certificate")
    v.check("TOOL-STATUS-5", "toolchain", status.get("package_control_certificate_count") == 18, "toolchain status records eighteen controls")
    v.check("TOOL-STATUS-6", "toolchain", status.get("compile_status") in {"not-run-lean-and-lake-unavailable", "compiled"}, "toolchain status does not overclaim compilation")
    v.check("TOOL-STATUS-7", "toolchain", status.get("static_lean_source_audit_status") == "passed-by-cst-tt-02-static-suite", "toolchain status records the CST-TT-02 static Lean audit")


def check_python(v: Validation) -> None:
    py_files = sorted([*SRC.rglob("*.py"), *(ROOT / "scripts").glob("*.py")])
    v.check("PY-001", "python", len(py_files) >= 25, f"at least twenty-five Python source files are present ({len(py_files)})")
    for index, path in enumerate(py_files, 1):
        v.guarded(f"PY-COMPILE-{index:03d}", "python", f"{path.relative_to(ROOT)} compiles", lambda p=path: (py_compile.compile(str(p), doraise=True) is not None))
    proc = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=ROOT, text=True, capture_output=True)
    detail = "full pytest suite passes"
    if proc.returncode != 0:
        detail += ": " + (proc.stdout + proc.stderr)[-1200:].replace("\n", " ")
    v.check("PY-TESTS", "python", proc.returncode == 0, detail)


def check_provenance(v: Validation) -> None:
    source_rows = (ROOT / "inputs/INPUTS.sha256").read_text(encoding="utf-8").splitlines()
    v.check("PROV-001", "provenance", len(source_rows) == 4, f"input checksum ledger retains the four frozen base inputs ({len(source_rows)})")
    for index, line in enumerate(source_rows, 1):
        parts = line.split(maxsplit=1)
        ok = len(parts) == 2
        if ok:
            expected, rel = parts
            path = ROOT / rel.strip().lstrip("*")
            ok = path.is_file() and sha256(path) == expected
        v.check(f"PROV-HASH-{index:03d}", "provenance", ok, f"input checksum row {index} resolves and matches")
    temporal_sources = sorted((ROOT / "inputs/reference_surfaces/temporal_audit").glob("*.tex"))
    v.check("PROV-TEMP-COUNT", "provenance", len(temporal_sources) == 9, "nine temporal-audit source manuscripts are retained")
    for index, path in enumerate(temporal_sources, 1):
        v.check(f"PROV-TEMP-{index:02d}", "provenance", path.stat().st_size > 1000, f"{path.name} is nonempty source provenance")
    for rel in (
        "inputs/normative/cst-tt-00/TEMPORAL_TRANSCENDENCE_AUDIT.md",
        "inputs/normative/cst-tt-00/EXECUTION_PLAN.md",
        "inputs/normative/cst-tt-00/FIACH_BASELINE_SPECIFICATION.md",
        "inputs/normative/cst-tt-00/IAPS_BASELINE_SPECIFICATION.md",
    ):
        v.check(f"PROV-NORM-{Path(rel).stem[:16]}", "provenance", (ROOT / rel).is_file(), f"{rel} is retained")


def _validate_json(schema_path: Path, instance_path: Path) -> tuple[bool, str]:
    schema = load_json(schema_path)
    instance = load_json(instance_path)
    assert isinstance(schema, dict)
    Draft202012Validator.check_schema(schema)
    errors = sorted(Draft202012Validator(schema).iter_errors(instance), key=lambda error: list(error.path))
    return not errors, "; ".join(error.message for error in errors[:4])


def check_packages(v: Validation) -> None:
    rows = read_csv(ROOT / "registries/PACKAGE_WITNESS_REGISTRY.csv")
    v.check("PKG-COUNT", "package", len(rows) == 2, "exactly two positive package witnesses are registered")
    for index, row in enumerate(rows, 1):
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        v.check(f"PKG-{index:02d}-MODEL", "package", model_path.is_file(), f"{row['package_id']} model exists")
        v.check(f"PKG-{index:02d}-CERT", "package", cert_path.is_file(), f"{row['package_id']} certificate exists")
        if not model_path.is_file() or not cert_path.is_file():
            continue
        model = load_json(model_path)
        cert = load_json(cert_path)
        assert isinstance(model, dict) and isinstance(cert, dict)
        audit = audit_package(model)
        checks = {
            "integrated": audit.integrated_package_valid,
            "coverage": audit.exact_clause_coverage and audit.unique_clause_slots,
            "locals": audit.every_scope_exact and audit.every_clause_accepted,
            "gates": audit.every_hard_gate_passed,
            "tree": audit.join_tree.valid_shape,
            "running": audit.join_tree.running_intersection,
            "edges": audit.join_tree.edge_compatible,
            "global": audit.global_constructible and audit.supplied_global_matches and audit.global_restricts_to_every_local,
            "temporal": audit.temporal_substance.valid,
            "ownership": audit.target_owned,
            "separation": audit.forbidden_field_free,
            "no-failures": audit.failed_obligations == (),
            "eight-clauses": len(audit.clause_audits) == 8,
            "forty-four-coordinates": len(audit.derived_global_assignment) == 44,
        }
        for subindex, (name, condition) in enumerate(checks.items(), 1):
            v.check(f"PKG-{index:02d}-{subindex:02d}", "package", condition, f"{row['package_id']} passes {name}")
        v.check(f"PKG-{index:02d}-HASH", "package", sha256(model_path) == row["model_sha256"] == cert.get("model_sha256"), f"{row['package_id']} model hash is bound in registry and certificate")
        v.check(f"PKG-{index:02d}-AUDIT", "package", cert.get("audit") == audit.to_dict(), f"{row['package_id']} stored audit equals independent recomputation")
        valid, message = _validate_json(ROOT / "schemas/certificates/package_certificate.schema.json", cert_path)
        v.check(f"PKG-{index:02d}-SCHEMA", "package", valid, f"{row['package_id']} certificate validates{': ' + message if message else ''}")
        v.check(f"PKG-{index:02d}-LANE", "package", cert.get("claim_lanes") == ["S-R"], f"{row['package_id']} is typed only as S-R")

    target = load_json(ROOT / "models/packages/PKG-POS-01-TARGET.model.json")
    source = load_json(ROOT / "models/packages/PKG-POS-02-SOURCE.model.json")
    assert isinstance(target, dict) and isinstance(source, dict)
    v.check("PKG-DISTINCT", "package", source.get("target", {}).get("code") != target.get("target", {}).get("code"), "source and target package carrier codes are distinct")
    temporal = audit_package(target).temporal_substance
    for index, field in enumerate((
        "future_sufficient", "order_stable", "successor_available", "viable_tick", "genuine_progress",
        "endogenous_arrow", "record_descends", "route_residue_retained", "no_external_scheduler",
        "temporal_owner_matches", "maintenance_owner_matches",
    ), 1):
        v.check(f"C6-{index:02d}", "temporal-C6", bool(getattr(temporal, field)), f"C6 satisfies {field}")


def check_staged(v: Validation) -> None:
    source_path = ROOT / "models/packages/PKG-POS-02-SOURCE.model.json"
    target_path = ROOT / "models/packages/PKG-POS-01-TARGET.model.json"
    assembly_path = ROOT / "models/packages/STG-POS-01.assembly.json"
    cert_path = ROOT / "formal/certificates/packages/STG-POS-01.certificate.json"
    source, target, assembly, cert = map(load_json, (source_path, target_path, assembly_path, cert_path))
    assert all(isinstance(value, dict) for value in (source, target, assembly, cert))
    audit = audit_staged_assembly(assembly, source, target)  # type: ignore[arg-type]
    fields = (
        "source_package_valid", "target_package_valid", "carriers_distinct", "exactly_eight_clause_maps",
        "maps_separately_typed", "coordinate_maps_total", "value_maps_sound", "hard_gates_never_averaged",
        "target_global_assembled", "forbidden_verdict_fields_absent", "staged_assembly_valid",
    )
    for index, field in enumerate(fields, 1):
        v.check(f"STG-{index:02d}", "staged-assembly", bool(getattr(audit, field)), f"staged assembly satisfies {field}")
    v.check("STG-FAILURES", "staged-assembly", audit.failed_obligations == (), "positive staged assembly has no failed obligations")
    v.check("STG-AUDIT", "staged-assembly", cert.get("audit") == audit.to_dict(), "stored staged audit equals independent recomputation")  # type: ignore[union-attr]
    v.check("STG-HASH-1", "staged-assembly", sha256(assembly_path) == cert.get("assembly_sha256"), "staged certificate binds assembly hash")  # type: ignore[union-attr]
    v.check("STG-HASH-2", "staged-assembly", sha256(source_path) == cert.get("source_model_sha256"), "staged certificate binds source model hash")  # type: ignore[union-attr]
    v.check("STG-HASH-3", "staged-assembly", sha256(target_path) == cert.get("target_model_sha256"), "staged certificate binds target model hash")  # type: ignore[union-attr]
    valid, message = _validate_json(ROOT / "schemas/certificates/staged_package_certificate.schema.json", cert_path)
    v.check("STG-SCHEMA", "staged-assembly", valid, f"staged certificate validates{': ' + message if message else ''}")
    v.check("STG-LANES", "staged-assembly", cert.get("claim_lanes") == ["S-T", "S-R"], "staged assembly is typed only as S-T and S-R")  # type: ignore[union-attr]


def check_controls(v: Validation) -> None:
    rows = read_csv(ROOT / "registries/PACKAGE_CONTROL_REGISTRY.csv")
    v.check("CTRL-COUNT", "controls", len(rows) == 18, "seventeen package controls and one staged control are registered")
    source = load_json(ROOT / "models/packages/PKG-POS-02-SOURCE.model.json")
    target = load_json(ROOT / "models/packages/PKG-POS-01-TARGET.model.json")
    assert isinstance(source, dict) and isinstance(target, dict)
    schema_path = ROOT / "schemas/certificates/package_control_certificate.schema.json"
    for index, row in enumerate(rows, 1):
        artifact_path = ROOT / row["artifact_ref"]
        cert_path = ROOT / row["certificate_ref"]
        v.check(f"CTRL-{index:02d}-ART", "controls", artifact_path.is_file(), f"{row['control_id']} artifact exists")
        v.check(f"CTRL-{index:02d}-CERT", "controls", cert_path.is_file(), f"{row['control_id']} certificate exists")
        if not artifact_path.is_file() or not cert_path.is_file():
            continue
        artifact = load_json(artifact_path)
        cert = load_json(cert_path)
        assert isinstance(artifact, dict) and isinstance(cert, dict)
        if row["control_kind"] == "package":
            audit = audit_package(artifact)
            valid_result = audit.integrated_package_valid
            failures = list(audit.failed_obligations)
        else:
            audit = audit_staged_assembly(artifact, source, target)
            valid_result = audit.staged_assembly_valid
            failures = list(audit.failed_obligations)
        v.check(f"CTRL-{index:02d}-REJECT", "controls", not valid_result, f"{row['control_id']} is rejected by its checker")
        v.check(f"CTRL-{index:02d}-PRIMARY", "controls", row["expected_primary_failure"] in failures, f"{row['control_id']} exposes its registered primary failure")
        v.check(f"CTRL-{index:02d}-EXACT", "controls", set(failures) == split_ids(row["observed_failures"]), f"{row['control_id']} failure set equals registry")
        v.check(f"CTRL-{index:02d}-STORED", "controls", cert.get("observed_failures") == failures, f"{row['control_id']} certificate stores recomputed failures")
        v.check(f"CTRL-{index:02d}-HASH", "controls", cert.get("artifact_sha256") == sha256(artifact_path), f"{row['control_id']} certificate binds exact artifact")
        valid, message = _validate_json(schema_path, cert_path)
        v.check(f"CTRL-{index:02d}-SCHEMA", "controls", valid, f"{row['control_id']} certificate validates{': ' + message if message else ''}")


def check_exhaustion(v: Validation) -> None:
    result = bounded_gluing_exhaustion()
    expected = load_json(ROOT / "formal/certificates/packages/BOUNDED_GLUING_EXHAUSTION.json")
    v.check("EXH-001", "bounded-exhaustion", result == expected, "stored exhaustion certificate equals independent rerun")
    v.check("EXH-002", "bounded-exhaustion", result.get("candidates_examined") == 1_025_416, "1,025,416 bounded candidates were examined")
    v.check("EXH-003", "bounded-exhaustion", result.get("premise_cases") == 18_972, "18,972 cases satisfy running-intersection and edge-compatibility premises")
    v.check("EXH-004", "bounded-exhaustion", result.get("glued_cases") == 18_972, "every premise-satisfying case glued")
    v.check("EXH-005", "bounded-exhaustion", result.get("violations") == [], "bounded search found no violation")
    v.check("EXH-006", "bounded-exhaustion", result.get("status") == "PASS", "bounded checker reports PASS")
    configs = result.get("configurations", [])
    v.check("EXH-007", "bounded-exhaustion", isinstance(configs, list) and len(configs) == 5, "five path/star configurations are covered")
    if isinstance(configs, list):
        for index, row in enumerate(configs, 1):
            v.check(f"EXH-CFG-{index:02d}", "bounded-exhaustion", row.get("premise_cases") == row.get("glued_cases"), f"configuration {row.get('configuration')} has no gluing failure")


def check_registries(v: Validation) -> None:
    theorem_rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    toy_rows = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    def_rows = read_csv(ROOT / "registries/DEFINITION_REGISTRY.csv")
    schema_rows = read_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv")
    pkg_obligations = read_csv(ROOT / "registries/PACKAGE_OBLIGATION_REGISTRY.csv")
    stg_obligations = read_csv(ROOT / "registries/STAGED_ASSEMBLY_OBLIGATION_REGISTRY.csv")
    v.check("REG-001", "registries", len(theorem_rows) == 35, "theorem registry retains 35 theorem/no-go surfaces")
    v.check("REG-002", "registries", len(toy_rows) == 23, "toy registry has 23 entries")
    v.check("REG-003", "registries", len(def_rows) == 45, "definition registry has 45 entries")
    v.check("REG-004", "registries", len(schema_rows) == 10, "certificate schema registry has 10 entries")
    v.check("REG-005", "registries", len(pkg_obligations) == 10, "package obligation registry has 10 entries")
    v.check("REG-006", "registries", len(stg_obligations) == 10, "staged obligation registry has 10 entries")
    for idx, (rows, key) in enumerate(((theorem_rows, "theorem_id"), (toy_rows, "toy_id"), (def_rows, "definition_id"), (schema_rows, "schema_id")), 1):
        v.check(f"REG-UNIQUE-{idx}", "registries", duplicate_values(rows, key) == set(), f"{key} values are unique")
    statuses = Counter(row["status"] for row in theorem_rows)
    v.check("REG-THM-STATUS-1", "registries", statuses == Counter({"open-scaffold": 19, "checked-finite-countermodel": 14, "proof-source-and-executable-certificate-landed": 2}), "theorem status distribution is frozen")
    for theorem_id, declaration in (
        ("TTH-01", "CSTTT.PackageTheory.acyclicLocalWitnessGluing"),
        ("TTH-02", "CSTTT.PackageTheory.stagedHeterogeneousPackageAssembly"),
    ):
        row = next(item for item in theorem_rows if item["theorem_id"] == theorem_id)
        v.check(f"REG-{theorem_id}-STATUS", "registries", row["status"] == "proof-source-and-executable-certificate-landed", f"{theorem_id} has the landed proof-source status")
        v.check(f"REG-{theorem_id}-LEAN", "registries", row["lean_statement"] == declaration, f"{theorem_id} points to its package proof source")
    v.check("REG-PKG-LANES", "registries", all(row["claim_lanes"] == "S-R" for row in pkg_obligations), "all package obligations are S-R only")
    v.check("REG-STG-LANES", "registries", all(split_ids(row["claim_lanes"]) == {"S-T", "S-R"} for row in stg_obligations), "all staged obligations are exactly S-T and S-R")
    for index, row in enumerate(pkg_obligations, 1):
        v.check(f"REG-PKG-OB-{index:02d}", "registries", row["obligation_id"] == f"PKG-O{index:02d}" and bool(row["positive_witnesses"]), f"package obligation {index} is ordered and has positive witnesses")
        v.check(f"REG-PKG-NEG-{index:02d}", "registries", bool(row["negative_controls"]), f"package obligation {index} has at least one exact negative control")
    for index, row in enumerate(stg_obligations, 1):
        v.check(f"REG-STG-OB-{index:02d}", "registries", row["obligation_id"] == f"STG-O{index:02d}" and row["positive_witness"] == "STG-POS-01", f"staged obligation {index} is ordered and has the positive assembly")
    project = load_json(ROOT / "registries/PROJECT_REGISTRY.json")
    summary = load_json(ROOT / "manifests/CST-TT-02_PHASE_SUMMARY.json")
    assert isinstance(project, dict) and isinstance(summary, dict)
    expected_project = {
        "phase": PHASE,
        "phase_base_tag": BASE_TAG,
        "phase_base_commit": BASE_COMMIT,
        "generic_theorem_proof_sources_landed": 2,
        "generic_theorems_lean_compiled": 0,
        "checked_finite_package_witnesses": 2,
        "checked_staged_package_assemblies": 1,
        "checked_package_obligation_controls": 18,
        "bounded_gluing_candidates": 1_025_416,
        "bounded_gluing_premise_cases": 18_972,
        "positive_handoff_witnesses": 0,
        "fallback_unlocked": False,
        "next_phase": "CST-TT-03",
    }
    for index, (key, value) in enumerate(expected_project.items(), 1):
        v.check(f"REG-PROJ-{index:02d}", "registries", project.get(key) == value, f"project registry freezes {key}={value!r}")
    v.check("REG-SUMMARY", "registries", summary.get("phase") == PHASE and summary.get("package_kill_criteria_triggered") == 0 and summary.get("fallback_unlocked") is False, "phase summary retains primary route and locks fallback")
    kills = {row["kill_id"]: row for row in read_csv(ROOT / "registries/KILL_CRITERIA.csv")}
    for kill_id in ("K-PKG-01", "K-PKG-02"):
        v.check(f"REG-{kill_id}", "registries", kills[kill_id]["status"] == "not-triggered-CST-TT-02", f"{kill_id} is not triggered")


def check_schemas(v: Validation) -> None:
    rows = read_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv")
    for index, row in enumerate(rows, 1):
        schema_path = ROOT / "schemas/certificates" / row["file"]
        example_path = ROOT / row["scaffold_example"]
        v.check(f"SCHEMA-{index:02d}-FILE", "schemas", schema_path.is_file(), f"schema {row['schema_id']} exists")
        v.check(f"SCHEMA-{index:02d}-EXAMPLE", "schemas", example_path.is_file(), f"schema {row['schema_id']} example exists")
        if schema_path.is_file() and example_path.is_file():
            valid, message = _validate_json(schema_path, example_path)
            v.check(f"SCHEMA-{index:02d}-VALID", "schemas", valid, f"schema {row['schema_id']} accepts its scaffold{': ' + message if message else ''}")
    theorem_schema = load_json(ROOT / "schemas/registries/theorem_registry_row.schema.json")
    assert isinstance(theorem_schema, dict)
    validator = Draft202012Validator(theorem_schema)
    for index, row in enumerate(read_csv(ROOT / "registries/THEOREM_REGISTRY.csv"), 1):
        errors = list(validator.iter_errors(row))
        v.check(f"SCHEMA-THM-{index:02d}", "schemas", not errors, f"theorem row {row['theorem_id']} validates against registry schema")


def check_lean(v: Validation) -> None:
    lean_files = sorted((ROOT / "CSTTT").rglob("*.lean"))
    v.check("LEAN-001", "lean-static", len(lean_files) >= 17, f"at least seventeen Lean modules are present ({len(lean_files)})")
    pattern = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")
    for index, path in enumerate(lean_files, 1):
        text = path.read_text(encoding="utf-8")
        v.check(f"LEAN-NOPLACE-{index:03d}", "lean-static", pattern.search(text) is None, f"{path.relative_to(ROOT)} has no proof placeholder command")
        v.check(f"LEAN-DELIM-{index:03d}", "lean-static", text.count("(") == text.count(")") and text.count("{") == text.count("}") and text.count("[") == text.count("]"), f"{path.relative_to(ROOT)} has balanced simple delimiters")
    findings = scan_primitive_tree(ROOT)
    v.check("LEAN-CIRCULARITY", "lean-static", findings == [], "primitive Lean tree passes forbidden-verdict vocabulary scan")
    finite = (ROOT / "CSTTT/Package/FiniteGluing.lean").read_text(encoding="utf-8")
    temporal = (ROOT / "CSTTT/Package/TemporalPackage.lean").read_text(encoding="utf-8")
    for index, name in enumerate((
        "ScopedReach", "RootedJoinTree", "localEqualityAlongScopedReach", "gluedAssignment",
        "gluedAssignmentAgrees", "IntegratedPackageWitness", "acyclicLocalWitnessGluing",
        "StagedHeterogeneousEvidence", "stagedHeterogeneousPackageAssembly",
    ), 1):
        v.check(f"LEAN-GLUE-{index:02d}", "lean-static", name in finite, f"finite gluing source contains {name}")
    for index, name in enumerate(("TemporalSubstance", "EightClauseIntegratedPackage"), 1):
        v.check(f"LEAN-TEMP-{index:02d}", "lean-static", name in temporal, f"temporal package source contains {name}")
    root_imports = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    v.check("LEAN-IMPORT-1", "lean-static", "import CSTTT.Package.FiniteGluing" in root_imports, "root module imports finite gluing")
    v.check("LEAN-IMPORT-2", "lean-static", "import CSTTT.Package.TemporalPackage" in root_imports, "root module imports temporal package")
    forbidden_imports = ("CSTTT.Corridor", "CSTTT.Autonomy", "CSTTT.Targets")
    for index, path in enumerate(sorted((ROOT / "CSTTT/Package").glob("*.lean")), 1):
        text = path.read_text(encoding="utf-8")
        v.check(f"LEAN-LAYER-{index:02d}", "lean-static", all(f"import {prefix}" not in text for prefix in forbidden_imports), f"{path.name} does not import later corridor/autonomy/target layers")


def check_boundaries(v: Validation) -> None:
    docs = {
        "docs/INTEGRATED_PACKAGE_SEMANTICS.md": (
            "finite structural target realization", "eight separately audited clause slots", "running intersection", "None of these assets is a handoff or lineage witness",
        ),
        "docs/ACYCLIC_GLUING_THEOREM.md": (
            "acyclicLocalWitnessGluing", "running-intersection", "Python is not a proof oracle", "1,025,416",
        ),
        "docs/C6_TEMPORAL_SUBSTANCE.md": (
            "future sufficiency", "genuine progress", "endogenous arrow", "external scheduler", "does not entail any other C-clause",
        ),
        "docs/STAGED_PACKAGE_ASSEMBLY.md": (
            "distinct carrier vocabularies", "eight typed clause maps", "does not establish temporal lineage",
        ),
        "docs/PACKAGE_CONTROL_SUITE.md": (
            "PC-01", "PC-17", "SC-01", "Every package obligation PKG-O01 through PKG-O10",
        ),
        "docs/PHASE_BOUNDARY.md": (
            "exact finite C1-C8 package semantics", "substantive C6 temporal closure", "strict temporal lineage", "withdrawal autonomy", "positive Temporal-FIACH or Temporal-IAPS witness", "CST-TT-03",
        ),
    }
    counter = 0
    for rel, phrases in docs.items():
        path = ROOT / rel
        v.check(f"DOC-{counter:02d}-EXISTS", "documentation", path.is_file(), f"{rel} exists")
        text = path.read_text(encoding="utf-8") if path.is_file() else ""
        for phrase_index, phrase in enumerate(phrases, 1):
            v.check(f"DOC-{counter:02d}-{phrase_index:02d}", "documentation", phrase in text, f"{rel} contains required phrase: {phrase}")
        counter += 1
    phase_text = (ROOT / "docs/PHASE_BOUNDARY.md").read_text(encoding="utf-8")
    v.check("BOUND-NO-HANDOFF", "boundaries", "positive Temporal-FIACH or Temporal-IAPS witness" in phase_text, "phase explicitly declines a positive handoff witness")
    completion = (ROOT / "manifests/CST-TT-02_COMPLETION_REPORT.md").read_text(encoding="utf-8")
    for index, phrase in enumerate((
        "No positive Temporal-FIACH witness", "No theorem is represented as Lean-compiled", "Temporal-IAPS fallback remains locked", "CST-TT-03",
    ), 1):
        v.check(f"BOUND-COMP-{index}", "boundaries", phrase in completion, f"completion report contains boundary phrase: {phrase}")
    for name in ("PKG-POS-01-TARGET.model.json", "PKG-POS-02-SOURCE.model.json"):
        text = (ROOT / "models/packages" / name).read_text(encoding="utf-8").lower()
        for token in ('"lineage"', '"ancestry"', '"temporal_corridor"', '"autonomy"', '"withdrawal"', '"fiach"', '"consciousness"', '"survival"', '"identity"'):
            v.check(f"BOUND-{name[:8]}-{token.strip(chr(34))}", "boundaries", token not in text, f"{name} omits verdict field {token}")


def check_manifest(v: Validation, require_manifest: bool) -> None:
    manifest_path = ROOT / "manifests/CST-TT-02_MANIFEST.json"
    checksum_path = ROOT / "manifests/CST-TT-02_SHA256SUMS"
    if not manifest_path.is_file() or not checksum_path.is_file():
        if require_manifest:
            v.check("MAN-001", "manifest", False, "CST-TT-02 manifest and checksum ledger exist")
        else:
            v.skip("MAN-001", "manifest", "phase manifest not required before finalization")
        return
    manifest = load_json(manifest_path)
    assert isinstance(manifest, dict)
    rows = manifest.get("files", [])
    v.check("MAN-001", "manifest", manifest.get("phase") == PHASE, "manifest names CST-TT-02")
    v.check("MAN-002", "manifest", manifest.get("file_count") == len(rows), "manifest file count matches rows")
    for index, row in enumerate(rows, 1):
        path = ROOT / row["path"]
        v.check(f"MAN-FILE-{index:04d}", "manifest", path.is_file() and path.stat().st_size == row["bytes"] and sha256(path) == row["sha256"], f"manifest row {row['path']} resolves and verifies")
    checksum_rows = checksum_path.read_text(encoding="utf-8").splitlines()
    v.check("MAN-003", "manifest", len(checksum_rows) >= len(rows), "checksum ledger covers manifest rows and manifest surfaces")
    for index, line in enumerate(checksum_rows, 1):
        expected, rel = line.split(maxsplit=1)
        path = ROOT / rel.strip().lstrip("*")
        v.check(f"MAN-SHA-{index:04d}", "manifest", path.is_file() and sha256(path) == expected, f"checksum row {rel.strip()} verifies")


def render(v: Validation) -> tuple[str, dict[str, object]]:
    counts = Counter(row.status for row in v.results)
    category_counts: dict[str, Counter[str]] = {}
    for row in v.results:
        category_counts.setdefault(row.category, Counter())[row.status] += 1
    payload: dict[str, object] = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "status": "PASS" if not v.failures else "FAIL",
        "checks": len(v.results),
        "passed": counts["PASS"],
        "failed": counts["FAIL"],
        "skipped": counts["SKIP"],
        "results": [asdict(row) for row in v.results],
    }
    lines = [
        "# CST-TT-02 Validation Report",
        "",
        f"**Overall status:** {payload['status']}",
        f"**Checks:** {payload['checks']} total — {payload['passed']} passed, {payload['failed']} failed, {payload['skipped']} skipped",
        "",
        "The skipped Lean-build check is not a pass. It records that the pinned compiler was unavailable in this environment.",
        "",
        "## Category summary",
        "",
        "| Category | PASS | FAIL | SKIP |",
        "|---|---:|---:|---:|",
    ]
    for category in sorted(category_counts):
        counter = category_counts[category]
        lines.append(f"| {category} | {counter['PASS']} | {counter['FAIL']} | {counter['SKIP']} |")
    lines.extend(["", "## Checks", "", "| ID | Category | Status | Detail |", "|---|---|---|---|"])
    for row in v.results:
        detail = row.detail.replace("|", "\\|").replace("\n", " ")
        lines.append(f"| `{row.check_id}` | {row.category} | **{row.status}** | {detail} |")
    return "\n".join(lines) + "\n", payload


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-clean", action="store_true")
    parser.add_argument("--require-tag", action="store_true")
    parser.add_argument("--require-manifest", action="store_true")
    parser.add_argument("--no-write", action="store_true", help="run checks without rewriting validation artifacts")
    args = parser.parse_args()

    v = Validation()
    check_baseline(v, args.require_clean, args.require_tag)
    check_toolchain(v)
    check_python(v)
    check_provenance(v)
    check_packages(v)
    check_staged(v)
    check_controls(v)
    check_exhaustion(v)
    check_registries(v)
    check_schemas(v)
    check_lean(v)
    check_boundaries(v)
    check_manifest(v, args.require_manifest)

    report, payload = render(v)
    if not args.no_write:
        (ROOT / "manifests/CST-TT-02_VALIDATION_REPORT.md").write_text(report, encoding="utf-8")
        (ROOT / "manifests/CST-TT-02_VALIDATION_RESULTS.json").write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"CST-TT-02 validation: {payload['status']} ({payload['passed']}/{payload['checks']} passed; {payload['skipped']} skipped)")
    if v.failures:
        for row in v.failures[:30]:
            print(f"FAIL {row.check_id}: {row.detail}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
