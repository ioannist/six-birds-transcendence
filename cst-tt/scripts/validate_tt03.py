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
from typing import Callable, Iterable, Mapping

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from cst_tt.circularity import scan_primitive_tree  # noqa: E402
from cst_tt.package_gluing import audit_package, audit_staged_assembly  # noqa: E402
from cst_tt.registry import duplicate_values, read_csv  # noqa: E402
from cst_tt.transport import (  # noqa: E402
    audit_memory_repair,
    audit_record_arrow,
    audit_route_discipline,
    audit_temporal_transport,
    bounded_confluence_shape_search,
    bounded_global_now_obstruction_search,
    bounded_memory_or_flatness_exhaustion,
    bounded_transport_shape_search,
)

PHASE = "CST-TT-03"
BASE_TAG = "CST-TT-02-v1"
BASE_COMMIT = "3abf5b2406f754b43823b68987c7ea409e737fd0"
PHASE_TAG = "CST-TT-03-v1"


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
        except Exception as exc:
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


def validate_instance(schema_path: Path, instance_path: Path) -> tuple[bool, str]:
    schema = load_json(schema_path)
    instance = load_json(instance_path)
    assert isinstance(schema, dict)
    Draft202012Validator.check_schema(schema)
    errors = sorted(Draft202012Validator(schema).iter_errors(instance), key=lambda e: list(e.path))
    return not errors, "; ".join(error.message for error in errors[:6])


def check_baseline(v: Validation, require_clean: bool, require_tag: bool) -> None:
    v.guarded("BASE-001", "baseline", "repository is a Git worktree", lambda: git("rev-parse", "--is-inside-work-tree") == "true")
    v.guarded("BASE-002", "baseline", "CST-TT-02 tag resolves to the frozen base", lambda: git("rev-parse", BASE_TAG + "^{}") == BASE_COMMIT)
    v.guarded(
        "BASE-003",
        "baseline",
        "frozen CST-TT-02 base is an ancestor of current HEAD",
        lambda: subprocess.run(["git", "merge-base", "--is-ancestor", BASE_COMMIT, "HEAD"], cwd=ROOT).returncode == 0,
    )
    v.guarded("BASE-004", "baseline", "repository has no whitespace errors", lambda: subprocess.run(["git", "diff", "--check"], cwd=ROOT, capture_output=True).returncode == 0)
    if require_clean:
        v.guarded("BASE-005", "baseline", "working tree is clean", lambda: git("status", "--porcelain") == "")
    else:
        v.skip("BASE-005", "baseline", "clean-tree check not requested before phase freeze")
    tags = set(git("tag", "--list").splitlines())
    if require_tag:
        v.check("BASE-006", "baseline", PHASE_TAG in tags, f"phase tag {PHASE_TAG} exists")
        if PHASE_TAG in tags:
            v.check("BASE-007", "baseline", git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD"), "phase tag resolves to current HEAD")
    elif PHASE_TAG in tags:
        v.check("BASE-006", "baseline", git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD"), "existing phase tag resolves to current HEAD")
    else:
        v.skip("BASE-006", "baseline", "phase tag not required before freeze")


def check_toolchain(v: Validation) -> None:
    v.check("TOOL-001", "toolchain", (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.28.0", "Lean toolchain remains pinned to v4.28.0")
    pyproject = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    for index, token in enumerate((">=3.13,<3.14", "pytest==9.0.2", "jsonschema==4.26.0", "setuptools==82.0.1"), 1):
        v.check(f"TOOL-PIN-{index:02d}", "toolchain", token in pyproject, f"pyproject contains {token}")
    v.check("TOOL-PY", "toolchain", sys.version_info[:2] == (3, 13), f"running Python is 3.13 (found {sys.version.split()[0]})")
    status = load_json(ROOT / "formal/TOOLCHAIN_STATUS.json")
    assert isinstance(status, dict)
    expectations = {
        "phase": PHASE,
        "pinned_toolchain": "leanprover/lean4:v4.28.0",
        "registered_generic_proof_source_count": 8,
        "new_registered_proof_source_count": 6,
        "positive_transport_certificate_count": 2,
        "route_certificate_count": 2,
        "memory_certificate_count": 2,
        "record_arrow_certificate_count": 1,
        "control_certificate_count": 28,
        "compile_claimed": False,
        "static_lean_source_audit_status": "passed-by-cst-tt-03-static-suite",
    }
    for index, (key, expected) in enumerate(expectations.items(), 1):
        v.check(f"TOOL-STATUS-{index:02d}", "toolchain", status.get(key) == expected, f"toolchain status {key}={expected!r}")
    lean = shutil.which("lean")
    lake = shutil.which("lake")
    if lean and lake:
        proc = subprocess.run([lake, "build"], cwd=ROOT, text=True, capture_output=True)
        v.check("TOOL-LEAN-BUILD", "toolchain", proc.returncode == 0, "pinned Lean sources compile with lake build")
    else:
        v.skip("TOOL-LEAN-BUILD", "toolchain", "lean/lake unavailable; no compilation pass claimed")


def check_python(v: Validation) -> None:
    py_files = sorted([*SRC.rglob("*.py"), *(ROOT / "scripts").glob("*.py")])
    v.check("PY-001", "python", len(py_files) >= 30, f"at least thirty Python source files are present ({len(py_files)})")
    for index, path in enumerate(py_files, 1):
        v.guarded(f"PY-COMPILE-{index:03d}", "python", f"{path.relative_to(ROOT)} compiles", lambda p=path: py_compile.compile(str(p), doraise=True) is not None)
    proc = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=ROOT, text=True, capture_output=True)
    detail = "full pytest suite passes"
    if proc.returncode != 0:
        detail += ": " + (proc.stdout + proc.stderr)[-1800:].replace("\n", " ")
    v.check("PY-TESTS", "python", proc.returncode == 0, detail)


def check_provenance(v: Validation) -> None:
    source_rows = (ROOT / "inputs/INPUTS.sha256").read_text(encoding="utf-8").splitlines()
    v.check("PROV-001", "provenance", len(source_rows) == 4, "four frozen top-level inputs remain hash-bound")
    for index, line in enumerate(source_rows, 1):
        parts = line.split(maxsplit=1)
        ok = len(parts) == 2
        if ok:
            expected, rel = parts
            path = ROOT / rel.strip().lstrip("*")
            ok = path.is_file() and sha256(path) == expected
        v.check(f"PROV-INPUT-{index:02d}", "provenance", ok, f"frozen input checksum row {index} verifies")
    temporal_sources = sorted((ROOT / "inputs/reference_surfaces/temporal_audit").glob("*.tex"))
    v.check("PROV-SOURCE-COUNT", "provenance", len(temporal_sources) == 9, "nine temporal SBT source manuscripts are retained")
    for index, path in enumerate(temporal_sources, 1):
        v.check(f"PROV-SOURCE-{index:02d}", "provenance", path.stat().st_size > 1000, f"{path.name} is retained and nonempty")
    inherited = {
        "CST-TT-00-v1": "65b3ab0f94564cee1d16ffb4513045319aaaf6ef",
        "CST-TT-01-v1": "488db50b20d6d9c67493de3e9fd758e6e9e205ce",
        "CST-TT-02-v1": BASE_COMMIT,
    }
    for index, (tag, commit) in enumerate(inherited.items(), 1):
        v.guarded(f"PROV-TAG-{index:02d}", "provenance", f"{tag} resolves to its frozen commit", lambda t=tag, c=commit: git("rev-parse", t + "^{}") == c)


def check_inherited_layers(v: Validation) -> None:
    countermodels = read_csv(ROOT / "registries/COUNTERMODEL_REGISTRY.csv")
    v.check("INHERIT-CM-COUNT", "inherited", len(countermodels) == 15, "the fifteen-countermodel negative kernel remains intact")
    for index, row in enumerate(countermodels, 1):
        model = ROOT / row["model_ref"]
        cert = ROOT / row["certificate_ref"]
        v.check(f"INHERIT-CM-{index:02d}-MODEL", "inherited", model.is_file(), f"{row['countermodel_id']} model remains present")
        v.check(f"INHERIT-CM-{index:02d}-CERT", "inherited", cert.is_file(), f"{row['countermodel_id']} certificate remains present")
    packages = read_csv(ROOT / "registries/PACKAGE_WITNESS_REGISTRY.csv")
    v.check("INHERIT-PKG-COUNT", "inherited", len(packages) == 2, "two integrated package witnesses remain registered")
    for index, row in enumerate(packages, 1):
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        v.check(f"INHERIT-PKG-{index:02d}-HASH", "inherited", model_path.is_file() and sha256(model_path) == row["model_sha256"], f"{row['package_id']} model hash verifies")
        if model_path.is_file() and cert_path.is_file():
            audit = audit_package(load_json(model_path))
            cert = load_json(cert_path)
            assert isinstance(cert, dict)
            v.check(f"INHERIT-PKG-{index:02d}-AUDIT", "inherited", cert.get("audit") == audit.to_dict(), f"{row['package_id']} package audit recomputes exactly")
    staged_model = ROOT / "models/packages/STG-POS-01.assembly.json"
    staged_cert = ROOT / "formal/certificates/packages/STG-POS-01.certificate.json"
    source_model = ROOT / "models/packages/PKG-POS-02-SOURCE.model.json"
    target_model = ROOT / "models/packages/PKG-POS-01-TARGET.model.json"
    v.check("INHERIT-STAGED-LINK", "inherited", all(path.is_file() for path in (staged_model, staged_cert, source_model, target_model)), "staged assembly and both typed endpoint packages remain present")
    if all(path.is_file() for path in (staged_model, staged_cert, source_model, target_model)):
        audit = audit_staged_assembly(load_json(staged_model), load_json(source_model), load_json(target_model))
        cert = load_json(staged_cert)
        assert isinstance(cert, dict)
        v.check("INHERIT-STAGED-AUDIT", "inherited", cert.get("audit") == audit.to_dict(), "staged heterogeneous package assembly recomputes exactly")


def check_routes(v: Validation) -> dict[str, dict[str, object]]:
    rows = read_csv(ROOT / "registries/ROUTE_DISCIPLINE_REGISTRY.csv")
    v.check("ROUTE-COUNT", "routes", len(rows) == 2, "exactly two route-discipline witnesses are registered")
    audits: dict[str, dict[str, object]] = {}
    schema = ROOT / "schemas/certificates/route_discipline_certificate.schema.json"
    for index, row in enumerate(rows, 1):
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        v.check(f"ROUTE-{index:02d}-MODEL", "routes", model_path.is_file(), f"{row['route_model_id']} model exists")
        v.check(f"ROUTE-{index:02d}-CERT", "routes", cert_path.is_file(), f"{row['route_model_id']} certificate exists")
        if not model_path.is_file() or not cert_path.is_file():
            continue
        cert = load_json(cert_path)
        assert isinstance(cert, dict)
        audit = audit_route_discipline(load_json(model_path)).to_dict()
        audits[row["route_model_id"]] = audit
        v.check(f"ROUTE-{index:02d}-HASH", "routes", sha256(model_path) == row["model_sha256"] == cert.get("model_sha256"), f"{row['route_model_id']} model hash matches registry and certificate")
        v.check(f"ROUTE-{index:02d}-AUDIT", "routes", cert.get("audit") == audit, f"{row['route_model_id']} audit recomputes exactly")
        ok, detail = validate_instance(schema, cert_path)
        v.check(f"ROUTE-{index:02d}-SCHEMA", "routes", ok, f"{row['route_model_id']} certificate validates: {detail or 'no schema errors'}")
        v.check(f"ROUTE-{index:02d}-LANE", "routes", cert.get("claim_lanes") == ["S-T"], f"{row['route_model_id']} remains S-T only")
    pos = audits.get("ROUTE-POS-01", {})
    neg = audits.get("ROUTE-NEG-01", {})
    v.check("ROUTE-POS-FLAT", "routes", pos.get("flatness_valid") is True and pos.get("temporal_endpoints_route_independent") is True, "confluent completion has a valid flat endpoint certificate")
    v.check("ROUTE-POS-NOHOL", "routes", pos.get("clock_translation_holonomy_zero") is True and pos.get("route_residue_trivial") is True, "confluent completion removes declared residue and translation holonomy")
    v.check("ROUTE-NEG-INDEXED", "routes", neg.get("route_audit_valid") is True and neg.get("flatness_valid") is False, "holonomy witness is well-formed but not flat")
    v.check("ROUTE-NEG-HOL", "routes", neg.get("nonzero_translation_holonomy_witnessed") is True and neg.get("global_now_factorization_exists") is False, "translation holonomy obstructs a boundary-indexed global now")
    return audits


def check_transport(v: Validation, route_audits: Mapping[str, Mapping[str, object]]) -> None:
    rows = read_csv(ROOT / "registries/TEMPORAL_TRANSPORT_WITNESS_REGISTRY.csv")
    v.check("TRANS-COUNT", "transport", len(rows) == 2, "exactly two positive temporal-transport certificates are registered")
    schema = ROOT / "schemas/certificates/temporal_transport_certificate.schema.json"
    for index, row in enumerate(rows, 1):
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        v.check(f"TRANS-{index:02d}-MODEL", "transport", model_path.is_file(), f"{row['transport_id']} model exists")
        v.check(f"TRANS-{index:02d}-CERT", "transport", cert_path.is_file(), f"{row['transport_id']} certificate exists")
        if not model_path.is_file() or not cert_path.is_file():
            continue
        cert = load_json(cert_path)
        model = load_json(model_path)
        assert isinstance(cert, dict) and isinstance(model, dict)
        flat = row["route_status"] == "flat"
        flat_valid = bool(route_audits.get("ROUTE-POS-01", {}).get("flatness_valid")) if flat else None
        audit = audit_temporal_transport(model, flatness_certificate_valid=flat_valid).to_dict()
        v.check(f"TRANS-{index:02d}-HASH", "transport", sha256(model_path) == row["model_sha256"] == cert.get("model_sha256"), f"{row['transport_id']} model hash matches registry and certificate")
        v.check(f"TRANS-{index:02d}-AUDIT", "transport", cert.get("audit") == audit, f"{row['transport_id']} audit recomputes exactly")
        v.check(f"TRANS-{index:02d}-VALID", "transport", audit.get("transport_valid") is True and audit.get("failed_obligations") == [], f"{row['transport_id']} satisfies every frozen transport obligation")
        v.check(f"TRANS-{index:02d}-CARRIERS", "transport", row["source_carrier"] == "17" and row["target_carrier"] == "101", f"{row['transport_id']} uses separately identified carriers")
        v.check(f"TRANS-{index:02d}-REP", "transport", audit.get("predictive_representative_independence") is True, f"{row['transport_id']} descends on the declared source predictive quotient")
        v.check(f"TRANS-{index:02d}-ARROW", "transport", audit.get("tick_progress_preserved") is True and audit.get("strict_record_arrow_preserved") is True, f"{row['transport_id']} preserves progress and strict record descent")
        v.check(f"TRANS-{index:02d}-OWNER", "transport", audit.get("maintenance_translated") is True and audit.get("ownership_interface_valid") is True, f"{row['transport_id']} translates maintenance and target ownership")
        ok, detail = validate_instance(schema, cert_path)
        v.check(f"TRANS-{index:02d}-SCHEMA", "transport", ok, f"{row['transport_id']} certificate validates: {detail or 'no schema errors'}")
        recursive_text = json.dumps(model).lower()
        for token_index, token in enumerate(("same_subject", "same_person", "personal_identity", "survival", "consciousness", "temporal_fiach", "continuation_verdict"), 1):
            v.check(f"TRANS-{index:02d}-BOUND-{token_index:02d}", "boundaries", f'"{token}"' not in recursive_text, f"{row['transport_id']} omits verdict key {token}")
    by_id = {row["transport_id"]: row for row in rows}
    flat_model = load_json(ROOT / by_id["TR-POS-02-FLAT"]["model_ref"])
    assert isinstance(flat_model, dict)
    flat_ref = flat_model.get("bridge", {}).get("flatness_certificate_ref") if isinstance(flat_model.get("bridge"), dict) else None
    v.check("TRANS-FLAT-REF", "transport", flat_ref == "formal/certificates/routes/ROUTE-POS-01.certificate.json", "flat transport binds the separately checked route certificate")


def check_memory_and_arrow(v: Validation) -> None:
    memory_rows = read_csv(ROOT / "registries/MEMORY_REPAIR_REGISTRY.csv")
    v.check("MEM-COUNT", "memory", len(memory_rows) == 2, "route-memory and flat alternatives are both registered")
    mem_schema = ROOT / "schemas/certificates/memory_repair_certificate.schema.json"
    mem_audits: dict[str, dict[str, object]] = {}
    for index, row in enumerate(memory_rows, 1):
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        cert = load_json(cert_path)
        assert isinstance(cert, dict)
        audit = audit_memory_repair(load_json(model_path)).to_dict()
        mem_audits[row["memory_model_id"]] = audit
        v.check(f"MEM-{index:02d}-HASH", "memory", sha256(model_path) == row["model_sha256"] == cert.get("model_sha256"), f"{row['memory_model_id']} hash verifies")
        v.check(f"MEM-{index:02d}-AUDIT", "memory", cert.get("audit") == audit, f"{row['memory_model_id']} audit recomputes exactly")
        v.check(f"MEM-{index:02d}-VALID", "memory", audit.get("memory_repair_valid") is True, f"{row['memory_model_id']} satisfies its declared memory-or-flatness branch")
        ok, detail = validate_instance(mem_schema, cert_path)
        v.check(f"MEM-{index:02d}-SCHEMA", "memory", ok, f"{row['memory_model_id']} certificate validates: {detail or 'no schema errors'}")
    pos = mem_audits.get("MEM-POS-01", {})
    flat = mem_audits.get("MEM-FLAT-01", {})
    v.check("MEM-POS-NOPRED", "memory", pos.get("current_collision_present") is True and pos.get("current_only_predictor_impossible") is True, "current equality does not determine the predictive future in the memory witness")
    v.check("MEM-POS-REPAIR", "memory", pos.get("route_memory_separates_collision") is True and pos.get("refined_predictor_correct") is True, "route residue repairs the predictive representation")
    v.check("MEM-FLAT-ALT", "memory", flat.get("flat_alternative") is True and flat.get("current_only_predictor_exists") is True, "flatness supplies the memory-free alternative")

    arrow_rows = read_csv(ROOT / "registries/RECORD_ARROW_REGISTRY.csv")
    v.check("ARROW-COUNT", "arrow", len(arrow_rows) == 1, "one positive record-arrow witness is registered")
    arrow_schema = ROOT / "schemas/certificates/record_arrow_certificate.schema.json"
    row = arrow_rows[0]
    model_path = ROOT / row["model_ref"]
    cert_path = ROOT / row["certificate_ref"]
    cert = load_json(cert_path)
    assert isinstance(cert, dict)
    audit = audit_record_arrow(load_json(model_path)).to_dict()
    v.check("ARROW-HASH", "arrow", sha256(model_path) == row["model_sha256"] == cert.get("model_sha256"), "record-arrow model hash verifies")
    v.check("ARROW-AUDIT", "arrow", cert.get("audit") == audit, "record-arrow audit recomputes exactly")
    v.check("ARROW-VALID", "arrow", audit.get("arrow_transport_valid") is True and audit.get("strict_progress_preserved") is True, "strict record descent is transported")
    v.check("ARROW-SEARCH", "arrow", audit.get("maps_examined_in_bounded_search") == 125 and audit.get("strictly_monotone_maps_in_bounded_search") == 10, "bounded map search examined 125 maps and found 10 strict maps")
    ok, detail = validate_instance(arrow_schema, cert_path)
    v.check("ARROW-SCHEMA", "arrow", ok, f"record-arrow certificate validates: {detail or 'no schema errors'}")


def check_controls(v: Validation) -> None:
    rows = read_csv(ROOT / "registries/TRANSPORT_CONTROL_REGISTRY.csv")
    v.check("CTRL-COUNT", "controls", len(rows) == 28, "exactly twenty-eight transport/route/memory/arrow controls are registered")
    counts = Counter(row["control_kind"] for row in rows)
    v.check("CTRL-FAMILIES", "controls", counts == Counter({"transport": 15, "route": 8, "record-arrow": 4, "memory": 1}), f"control-family counts are frozen ({dict(counts)})")
    schema = ROOT / "schemas/certificates/transport_control_certificate.schema.json"
    for index, row in enumerate(rows, 1):
        model_path = ROOT / row["artifact_ref"]
        cert_path = ROOT / row["certificate_ref"]
        v.check(f"CTRL-{index:02d}-MODEL", "controls", model_path.is_file(), f"{row['control_id']} model exists")
        v.check(f"CTRL-{index:02d}-CERT", "controls", cert_path.is_file(), f"{row['control_id']} certificate exists")
        if not model_path.is_file() or not cert_path.is_file():
            continue
        model = load_json(model_path)
        cert = load_json(cert_path)
        assert isinstance(cert, dict)
        if row["control_kind"] == "transport":
            audit_obj = audit_temporal_transport(model)
            valid = audit_obj.transport_valid
        elif row["control_kind"] == "route":
            audit_obj = audit_route_discipline(model)
            valid = audit_obj.flatness_valid if row["control_id"] != "ROUTE-C08" else audit_obj.route_audit_valid
        elif row["control_kind"] == "memory":
            audit_obj = audit_memory_repair(model)
            valid = audit_obj.memory_repair_valid
        else:
            audit_obj = audit_record_arrow(model)
            valid = audit_obj.arrow_transport_valid
        failures = list(audit_obj.failed_obligations)
        v.check(f"CTRL-{index:02d}-HASH", "controls", sha256(model_path) == cert.get("artifact_sha256"), f"{row['control_id']} model hash matches certificate")
        v.check(f"CTRL-{index:02d}-INVALID", "controls", valid is False, f"{row['control_id']} is rejected by its declared checker")
        v.check(f"CTRL-{index:02d}-PRIMARY", "controls", row["expected_primary_failure"] in failures, f"{row['control_id']} exposes expected failure {row['expected_primary_failure']}")
        v.check(f"CTRL-{index:02d}-FAILURES", "controls", cert.get("observed_failures") == failures == row["observed_failures"].split(";"), f"{row['control_id']} observed failures recompute exactly")
        ok, detail = validate_instance(schema, cert_path)
        v.check(f"CTRL-{index:02d}-SCHEMA", "controls", ok, f"{row['control_id']} certificate validates: {detail or 'no schema errors'}")


def check_searches(v: Validation) -> None:
    expectations = [
        ("SEARCH-TRANS", ROOT / "formal/certificates/transport/BOUNDED_TRANSPORT_SHAPE_SEARCH.json", bounded_transport_shape_search(), 12),
        ("SEARCH-CONF", ROOT / "formal/certificates/routes/BOUNDED_CONFLUENCE_SHAPE_SEARCH.json", bounded_confluence_shape_search(), 354),
        ("SEARCH-MEM", ROOT / "formal/certificates/memory/BOUNDED_MEMORY_OR_FLATNESS_EXHAUSTION.json", bounded_memory_or_flatness_exhaustion(), 64),
        ("SEARCH-NOW", ROOT / "formal/certificates/routes/BOUNDED_GLOBAL_NOW_OBSTRUCTION_SEARCH.json", bounded_global_now_obstruction_search(), 4),
    ]
    for prefix, path, expected, count in expectations:
        stored = load_json(path)
        v.check(prefix + "-EXACT", "bounded-search", stored == expected, f"{path.name} reproduces byte-equivalent semantic content")
        v.check(prefix + "-PASS", "bounded-search", isinstance(stored, dict) and stored.get("status") == "PASS", f"{path.name} reports PASS")
        numeric_values = {value for value in stored.values() if isinstance(value, int)} if isinstance(stored, dict) else set()
        v.check(prefix + "-COUNT", "bounded-search", count in numeric_values, f"{path.name} retains the declared bounded count {count}")
    transport = load_json(ROOT / "formal/certificates/transport/BOUNDED_TRANSPORT_SHAPE_SEARCH.json")
    confluence = load_json(ROOT / "formal/certificates/routes/BOUNDED_CONFLUENCE_SHAPE_SEARCH.json")
    assert isinstance(transport, dict) and isinstance(confluence, dict)
    v.check("SEARCH-TRANS-MIN", "bounded-search", transport.get("minimal_pair") == [3, 2], "first feasible transport shape is source/target (3,2) in the declared family")
    v.check("SEARCH-CONF-MIN", "bounded-search", confluence.get("minimal_node_count") == 4, "first acyclic two-branch confluence diamond has four nodes")


def check_registries(v: Validation) -> None:
    theorem_rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    toy_rows = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    def_rows = read_csv(ROOT / "registries/DEFINITION_REGISTRY.csv")
    schema_rows = read_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv")
    kill_rows = read_csv(ROOT / "registries/KILL_CRITERIA.csv")
    expectations = [
        ("REG-THM", theorem_rows, "theorem_id", 35),
        ("REG-TOY", toy_rows, "toy_id", 23),
        ("REG-DEF", def_rows, "definition_id", 54),
        ("REG-SCHEMA", schema_rows, "schema_id", 15),
        ("REG-KILL", kill_rows, "kill_id", 18),
    ]
    for prefix, rows, key, count in expectations:
        v.check(prefix + "-COUNT", "registries", len(rows) == count, f"{key} registry has {count} rows")
        v.check(prefix + "-UNIQUE", "registries", duplicate_values(rows, key) == set(), f"{key} values are unique")
    statuses = Counter(row["status"] for row in theorem_rows)
    v.check("REG-THM-STATUS", "registries", statuses == Counter({"open-scaffold": 16, "checked-finite-countermodel": 12, "proof-source-and-executable-certificate-landed": 7}), "theorem status distribution matches CST-TT-03")
    advanced = {"TTH-03", "TTH-09", "TTH-10", "TTN-04", "TTN-05"}
    by_id = {row["theorem_id"]: row for row in theorem_rows}
    for index, theorem_id in enumerate(sorted(advanced), 1):
        v.check(f"REG-ADV-{index:02d}", "registries", by_id[theorem_id]["phase"] == PHASE and by_id[theorem_id]["status"] == "proof-source-and-executable-certificate-landed", f"{theorem_id} is advanced in CST-TT-03")
    theorem_ids = set(by_id)
    toy_ids = {row["toy_id"] for row in toy_rows}
    for index, row in enumerate(theorem_rows, 1):
        v.check(f"REG-THM-{index:02d}-DEPS", "registries", split_ids(row["dependencies"]).issubset(theorem_ids), f"{row['theorem_id']} theorem dependencies resolve")
        v.check(f"REG-THM-{index:02d}-TOYS", "registries", split_ids(row["toy_dependencies"]).issubset(toy_ids), f"{row['theorem_id']} toy dependencies resolve")
        lean_surfaces = [surface.strip() for surface in row["lean_statement"].split(";") if surface.strip()]
        v.check(f"REG-THM-{index:02d}-LEAN", "registries", bool(lean_surfaces) and all(surface.startswith("CSTTT.") for surface in lean_surfaces), f"{row['theorem_id']} has one or more resolved Lean declarations")
    for index, row in enumerate(def_rows, 1):
        path = ROOT / row["module"]
        v.check(f"REG-DEF-{index:02d}-MODULE", "registries", path.is_file(), f"{row['definition_id']} module resolves")
        if path.is_file():
            v.check(f"REG-DEF-{index:02d}-NAME", "registries", row["name"] in path.read_text(encoding="utf-8"), f"{row['definition_id']} name occurs in its module")
    closed = {"K-PKG-01", "K-PKG-02", "K-TRANS-01", "K-TRANS-02", "K-ROUTE-01", "K-ARROW-01"}
    kill_by_id = {row["kill_id"]: row for row in kill_rows}
    for index, kill_id in enumerate(sorted(closed), 1):
        v.check(f"REG-KILL-{index:02d}", "registries", kill_by_id[kill_id]["status"].startswith("not-triggered-"), f"{kill_id} was tested and not triggered")
    v.check("REG-FALLBACK", "registries", load_json(ROOT / "registries/PROJECT_REGISTRY.json").get("fallback_unlocked") is False, "Temporal-IAPS fallback remains locked")


def check_schemas(v: Validation) -> None:
    schema_paths = sorted((ROOT / "schemas/certificates").glob("*.schema.json"))
    examples = sorted((ROOT / "examples/scaffold").glob("*.json"))
    v.check("SCHEMA-COUNT", "schemas", len(schema_paths) == 15 and len(examples) == 15, "fifteen certificate schemas have fifteen scaffold examples")
    examples_by_stem = {path.name.replace(".scaffold.json", ""): path for path in examples}
    for index, schema_path in enumerate(schema_paths, 1):
        schema = load_json(schema_path)
        assert isinstance(schema, dict)
        v.guarded(f"SCHEMA-{index:02d}-META", "schemas", f"{schema_path.name} is valid Draft 2020-12", lambda s=schema: (Draft202012Validator.check_schema(s) is None))
        stem = schema_path.name.replace(".schema.json", "")
        example = examples_by_stem.get(stem)
        v.check(f"SCHEMA-{index:02d}-EXAMPLE", "schemas", example is not None, f"{schema_path.name} has one matching scaffold")
        if example is not None:
            ok, detail = validate_instance(schema_path, example)
            v.check(f"SCHEMA-{index:02d}-VALID", "schemas", ok, f"{example.name} validates: {detail or 'no schema errors'}")
            instance = load_json(example)
            instance_text = json.dumps(instance).lower()
            no_landed_status = all(token not in instance_text for token in (
                '"result_status": "checked-', '"result_status": "proved', '"result_status": "certified'
            ))
            v.check(f"SCHEMA-{index:02d}-NONCLAIM", "schemas", isinstance(instance, dict) and no_landed_status, f"{example.name} does not claim landed evidence")


def check_lean(v: Validation) -> None:
    paths = [
        ROOT / "CSTTT/Transport/FiniteTemporalTransport.lean",
        ROOT / "CSTTT/Transport/RecordArrow.lean",
        ROOT / "CSTTT/Transport/RouteDiscipline.lean",
        ROOT / "CSTTT/Transport/FiniteExamples.lean",
    ]
    for index, path in enumerate(paths, 1):
        v.check(f"LEAN-{index:02d}-EXISTS", "lean-static", path.is_file(), f"{path.relative_to(ROOT)} exists")
    text = "\n".join(path.read_text(encoding="utf-8") for path in paths if path.is_file())
    declarations = (
        "RepresentativeIndependent",
        "TemporalSignatureAgreement",
        "FiniteTemporalTransportProof",
        "bundledHeterogeneousTemporalTransport",
        "StrictlyMonotoneOn",
        "monotoneRecordDescentTransportsArrow",
        "transportRecordArrowStep",
        "noCurrentOnlyPredictor",
        "memoryOrFlatness",
        "noCanonicalGlobalNowOfTranslationHolonomy",
        "noGlobalNowFactorization",
        "NormalizationCertificate",
        "routeIndependentEndpointUnderNormalization",
        "exactHeterogeneousSignatureAgreement",
        "exampleConfluentEndpoints",
    )
    for index, name in enumerate(declarations, 1):
        v.check(f"LEAN-DECL-{index:02d}", "lean-static", name in text, f"Lean declaration {name} is present")
    pattern = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")
    for index, path in enumerate(sorted((ROOT / "CSTTT").rglob("*.lean")), 1):
        source = path.read_text(encoding="utf-8")
        v.check(f"LEAN-NOPLACE-{index:03d}", "lean-static", pattern.search(source) is None, f"{path.relative_to(ROOT)} contains no unproved placeholder command")
    v.check("LEAN-CIRCULARITY", "lean-static", scan_primitive_tree(ROOT) == [], "primitive Lean tree passes verdict-vocabulary circularity scan")
    for index, path in enumerate(sorted((ROOT / "CSTTT/Transport").glob("*.lean")), 1):
        source = path.read_text(encoding="utf-8")
        v.check(f"LEAN-LAYER-{index:02d}", "lean-static", all(f"import {prefix}" not in source for prefix in ("CSTTT.Autonomy", "CSTTT.Corridor", "CSTTT.Targets")), f"{path.name} does not import later verdict layers")
    lean_text = "\n".join(path.read_text(encoding="utf-8") for path in sorted((ROOT / "CSTTT").rglob("*.lean")))
    declaration_index = 0
    for row in read_csv(ROOT / "registries/THEOREM_REGISTRY.csv"):
        for declaration in row["lean_statement"].split(";"):
            declaration_index += 1
            name = declaration.split(".")[-1]
            v.check(f"LEAN-REG-{declaration_index:02d}", "lean-static", name in lean_text, f"registered theorem declaration {name} is present")
    root_imports = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    for index, module in enumerate((
        "CSTTT.Transport.FiniteTemporalTransport",
        "CSTTT.Transport.RecordArrow",
        "CSTTT.Transport.RouteDiscipline",
        "CSTTT.Transport.FiniteExamples",
    ), 1):
        v.check(f"LEAN-ROOT-{index:02d}", "lean-static", f"import {module}" in root_imports, f"root Lean module imports {module}")


def check_boundaries(v: Validation) -> None:
    project = load_json(ROOT / "registries/PROJECT_REGISTRY.json")
    assert isinstance(project, dict)
    expectations = {
        "phase": PHASE,
        "phase_base_tag": BASE_TAG,
        "phase_base_commit": BASE_COMMIT,
        "checked_finite_countermodels": 15,
        "checked_finite_package_witnesses": 2,
        "checked_staged_package_assemblies": 1,
        "generic_theorem_proof_sources_landed": 8,
        "checked_temporal_transport_certificates": 2,
        "checked_route_certificates": 2,
        "checked_memory_or_flatness_certificates": 2,
        "checked_record_arrow_certificates": 1,
        "checked_transport_and_route_controls": 28,
        "generic_theorems_lean_compiled": 0,
        "positive_handoff_witnesses": 0,
        "fallback_unlocked": False,
        "next_phase": "CST-TT-04",
    }
    for index, (key, expected) in enumerate(expectations.items(), 1):
        v.check(f"BOUND-PROJECT-{index:02d}", "boundaries", project.get(key) == expected, f"project registry {key}={expected!r}")
    phase_text = (ROOT / "docs/PHASE_BOUNDARY.md").read_text(encoding="utf-8")
    phrases = (
        "exact finite C1-C8 package semantics",
        "substantive C6 temporal closure",
        "componentwise heterogeneous transport",
        "representative-independent predictive bridges",
        "strict record-arrow transport",
        "memory-or-flatness",
        "no-global-now factorization theorem",
        "Not landed",
        "strict temporal lineage",
        "post-withdrawal autonomy",
        "positive Temporal-FIACH or Temporal-IAPS witness",
        "CST-TT-04",
    )
    for index, phrase in enumerate(phrases, 1):
        v.check(f"BOUND-PHASE-{index:02d}", "boundaries", phrase in phase_text, f"phase boundary contains {phrase!r}")
    docs = {
        "docs/HETEROGENEOUS_TEMPORAL_TRANSPORT.md": ("S-T", "no episode lineage", "representative"),
        "docs/MEMORY_OR_FLATNESS_THEOREM.md": ("same current representation", "route residue", "flat"),
        "docs/ROUTE_DISCIPLINE_AND_CONFLUENCE.md": ("holonomy", "normal form", "boundary-level"),
        "docs/RECORD_ARROW_TRANSPORT.md": ("strict", "constant map", "arrow"),
        "docs/TRANSPORT_CONTROL_SUITE.md": ("28", "controls", "hash-bound"),
    }
    for file_index, (rel, required) in enumerate(docs.items(), 1):
        path = ROOT / rel
        v.check(f"BOUND-DOC-{file_index:02d}-EXISTS", "documentation", path.is_file(), f"{rel} exists")
        text = path.read_text(encoding="utf-8") if path.is_file() else ""
        for phrase_index, phrase in enumerate(required, 1):
            v.check(f"BOUND-DOC-{file_index:02d}-{phrase_index:02d}", "documentation", phrase.lower() in text.lower(), f"{rel} contains {phrase!r}")
    completion = (ROOT / "manifests/CST-TT-03_COMPLETION_REPORT.md").read_text(encoding="utf-8")
    for index, phrase in enumerate(("No positive temporal corridor", "No post-withdrawal autonomy", "Temporal-IAPS remains locked", "Lean compilation is not claimed", "CST-TT-04"), 1):
        v.check(f"BOUND-COMP-{index:02d}", "boundaries", phrase in completion, f"completion report contains boundary phrase {phrase!r}")


def check_manifest(v: Validation, require_manifest: bool) -> None:
    manifest_path = ROOT / "manifests/CST-TT-03_MANIFEST.json"
    checksum_path = ROOT / "manifests/CST-TT-03_SHA256SUMS"
    if not manifest_path.is_file() or not checksum_path.is_file():
        if require_manifest:
            v.check("MAN-001", "manifest", False, "CST-TT-03 manifest and checksum ledger exist")
        else:
            v.skip("MAN-001", "manifest", "phase manifest not required before finalization")
        return
    manifest = load_json(manifest_path)
    assert isinstance(manifest, dict)
    rows = manifest.get("files", [])
    v.check("MAN-001", "manifest", manifest.get("phase") == PHASE, "manifest names CST-TT-03")
    v.check("MAN-002", "manifest", manifest.get("file_count") == len(rows), "manifest file count matches rows")
    for index, row in enumerate(rows, 1):
        path = ROOT / row["path"]
        v.check(f"MAN-FILE-{index:04d}", "manifest", path.is_file() and path.stat().st_size == row["bytes"] and sha256(path) == row["sha256"], f"manifest row {row['path']} verifies")
    checksum_rows = checksum_path.read_text(encoding="utf-8").splitlines()
    v.check("MAN-003", "manifest", len(checksum_rows) >= len(rows), "checksum ledger covers manifest rows")
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
        "# CST-TT-03 Validation Report",
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
    parser.add_argument("--no-write", action="store_true")
    args = parser.parse_args()

    v = Validation()
    check_baseline(v, args.require_clean, args.require_tag)
    check_toolchain(v)
    check_python(v)
    check_provenance(v)
    check_inherited_layers(v)
    route_audits = check_routes(v)
    check_transport(v, route_audits)
    check_memory_and_arrow(v)
    check_controls(v)
    check_searches(v)
    check_registries(v)
    check_schemas(v)
    check_lean(v)
    check_boundaries(v)
    check_manifest(v, args.require_manifest)

    report, payload = render(v)
    if not args.no_write:
        (ROOT / "manifests/CST-TT-03_VALIDATION_REPORT.md").write_text(report, encoding="utf-8")
        (ROOT / "manifests/CST-TT-03_VALIDATION_RESULTS.json").write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        (ROOT / "manifests/VALIDATION_REPORT.md").write_text(report, encoding="utf-8")
        (ROOT / "manifests/VALIDATION_RESULTS.json").write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"CST-TT-03 validation: {payload['status']} ({payload['passed']}/{payload['checks']} passed; {payload['skipped']} skipped)")
    if v.failures:
        for row in v.failures[:40]:
            print(f"FAIL {row.check_id}: {row.detail}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
