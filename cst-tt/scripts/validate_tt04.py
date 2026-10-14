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
from typing import Any, Callable, Mapping

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from cst_tt.circularity import scan_primitive_tree  # noqa: E402
from cst_tt.corridor import (  # noqa: E402
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
from cst_tt.registry import duplicate_values, read_csv  # noqa: E402

PHASE = "CST-TT-04"
BASE_TAG = "CST-TT-03-v1"
BASE_COMMIT = "63ea725a7b6ade8df58a94cf7aad2ad78440ce70"
PHASE_TAG = "CST-TT-04-v1"


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
        except Exception as exc:  # pragma: no cover - failure reporting path
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


def load_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def validate_json(schema_path: Path, instance_path: Path) -> tuple[bool, str]:
    schema = load_json(schema_path)
    instance = load_json(instance_path)
    Draft202012Validator.check_schema(schema)
    errors = sorted(Draft202012Validator(schema).iter_errors(instance), key=lambda err: list(err.path))
    return not errors, "; ".join(error.message for error in errors[:5])


def check_baseline(v: Validation, require_clean: bool, require_tag: bool) -> None:
    v.guarded("BASE-001", "baseline", "repository is a Git worktree", lambda: git("rev-parse", "--is-inside-work-tree") == "true")
    v.guarded("BASE-002", "baseline", f"{BASE_TAG} resolves to frozen base", lambda: git("rev-parse", BASE_TAG + "^{}") == BASE_COMMIT)
    v.guarded(
        "BASE-003",
        "baseline",
        "frozen base is an ancestor of current HEAD",
        lambda: subprocess.run(["git", "merge-base", "--is-ancestor", BASE_COMMIT, "HEAD"], cwd=ROOT).returncode == 0,
    )
    v.guarded("BASE-004", "baseline", "repository has no whitespace errors", lambda: subprocess.run(["git", "diff", "--check"], cwd=ROOT, capture_output=True).returncode == 0)
    if require_clean:
        v.guarded("BASE-005", "baseline", "working tree is clean", lambda: git("status", "--porcelain") == "")
    else:
        v.skip("BASE-005", "baseline", "clean-tree check not requested before freeze")
    tags = set(git("tag", "--list").splitlines())
    if require_tag:
        v.check("BASE-006", "baseline", PHASE_TAG in tags, f"phase tag {PHASE_TAG} exists")
        if PHASE_TAG in tags:
            v.check("BASE-007", "baseline", git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD"), "phase tag resolves to HEAD")
    elif PHASE_TAG in tags:
        v.check("BASE-006", "baseline", git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD"), "existing phase tag resolves to HEAD")
    else:
        v.skip("BASE-006", "baseline", "phase tag not required before freeze")


def check_toolchain(v: Validation) -> None:
    v.check("TOOL-001", "toolchain", (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.28.0", "Lean toolchain remains pinned")
    pyproject = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    for index, token in enumerate((">=3.13,<3.14", "pytest==9.0.2", "jsonschema==4.26.0", "setuptools==82.0.1"), 1):
        v.check(f"TOOL-PIN-{index:02d}", "toolchain", token in pyproject, f"pyproject contains {token}")
    v.check("TOOL-PY", "toolchain", sys.version_info[:2] == (3, 13), f"Python 3.13 is running ({sys.version.split()[0]})")
    status = load_json(ROOT / "formal/TOOLCHAIN_STATUS.json")
    for index, (key, expected) in enumerate(
        {
            "phase": PHASE,
            "lean_toolchain": "leanprover/lean4:v4.28.0",
            "lean_compile_status": "pending-toolchain",
            "python_certificate_status": "checked",
        }.items(),
        1,
    ):
        v.check(f"TOOL-STATUS-{index:02d}", "toolchain", status.get(key) == expected, f"toolchain status {key}={expected!r}")
    lean = shutil.which("lean")
    lake = shutil.which("lake")
    if lean and lake:
        proc = subprocess.run([lake, "build"], cwd=ROOT, text=True, capture_output=True)
        v.check("TOOL-LEAN-BUILD", "toolchain", proc.returncode == 0, "pinned Lean sources compile with lake build")
    else:
        v.skip("TOOL-LEAN-BUILD", "toolchain", "lean/lake unavailable; no compilation pass claimed")


def check_python(v: Validation) -> None:
    py_files = sorted([*SRC.rglob("*.py"), *(ROOT / "scripts").glob("*.py"), *(ROOT / "tests").glob("*.py")])
    v.check("PY-001", "python", len(py_files) >= 50, f"at least fifty Python files are present ({len(py_files)})")
    for index, path in enumerate(py_files, 1):
        v.guarded(f"PY-COMPILE-{index:03d}", "python", f"{path.relative_to(ROOT)} compiles", lambda p=path: py_compile.compile(str(p), doraise=True) is not None)
    proc = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=ROOT, text=True, capture_output=True, env={**dict(__import__('os').environ), "PYTHONPATH": "src:scripts", "PYTHONHASHSEED": "0"})
    detail = "full pytest suite passes"
    if proc.returncode != 0:
        detail += ": " + (proc.stdout + proc.stderr)[-2000:].replace("\n", " ")
    v.check("PY-TESTS", "python", proc.returncode == 0, detail)


def check_provenance(v: Validation) -> None:
    lines = (ROOT / "inputs/INPUTS.sha256").read_text(encoding="utf-8").splitlines()
    v.check("PROV-001", "provenance", len(lines) == 4, "four frozen top-level inputs remain hash-bound")
    for index, line in enumerate(lines, 1):
        parts = line.split(maxsplit=1)
        ok = len(parts) == 2
        if ok:
            expected, rel = parts
            path = ROOT / rel.strip().lstrip("*")
            ok = path.is_file() and sha256(path) == expected
        v.check(f"PROV-INPUT-{index:02d}", "provenance", ok, f"input checksum row {index} verifies")
    sources = sorted((ROOT / "inputs/reference_surfaces/temporal_audit").glob("*.tex"))
    v.check("PROV-SOURCE-COUNT", "provenance", len(sources) == 9, "nine temporal SBT source manuscripts are retained")
    for index, path in enumerate(sources, 1):
        v.check(f"PROV-SOURCE-{index:02d}", "provenance", path.stat().st_size > 1000, f"{path.name} is retained")
    inherited = {
        "CST-TT-00-v1": "65b3ab0f94564cee1d16ffb4513045319aaaf6ef",
        "CST-TT-01-v1": "488db50b20d6d9c67493de3e9fd758e6e9e205ce",
        "CST-TT-02-v1": "3abf5b2406f754b43823b68987c7ea409e737fd0",
        BASE_TAG: BASE_COMMIT,
    }
    for index, (tag, commit) in enumerate(inherited.items(), 1):
        v.guarded(f"PROV-TAG-{index:02d}", "provenance", f"{tag} resolves to its frozen commit", lambda t=tag, c=commit: git("rev-parse", t + "^{}") == c)


def check_inherited_assets(v: Validation) -> None:
    expectations = {
        "COUNTERMODEL_REGISTRY.csv": 15,
        "PACKAGE_WITNESS_REGISTRY.csv": 2,
        "PACKAGE_CONTROL_REGISTRY.csv": 18,
        "TEMPORAL_TRANSPORT_WITNESS_REGISTRY.csv": 2,
        "ROUTE_DISCIPLINE_REGISTRY.csv": 2,
        "MEMORY_REPAIR_REGISTRY.csv": 2,
        "RECORD_ARROW_REGISTRY.csv": 1,
        "TRANSPORT_CONTROL_REGISTRY.csv": 28,
    }
    for index, (name, count) in enumerate(expectations.items(), 1):
        rows = read_csv(ROOT / "registries" / name)
        v.check(f"INHERIT-COUNT-{index:02d}", "inherited", len(rows) == count, f"{name} retains {count} rows")
    countermodels = read_csv(ROOT / "registries/COUNTERMODEL_REGISTRY.csv")
    for index, row in enumerate(countermodels, 1):
        for kind in ("model_ref", "certificate_ref"):
            path = ROOT / row[kind]
            v.check(f"INHERIT-CM-{index:02d}-{kind}", "inherited", path.is_file(), f"{row['countermodel_id']} {kind} exists")
    package_rows = read_csv(ROOT / "registries/PACKAGE_WITNESS_REGISTRY.csv")
    for index, row in enumerate(package_rows, 1):
        model = ROOT / row["model_ref"]
        v.check(f"INHERIT-PKG-{index:02d}-HASH", "inherited", model.is_file() and sha256(model) == row["model_sha256"], f"{row['package_id']} model hash verifies")


def check_schema_bank(v: Validation) -> None:
    schemas = sorted((ROOT / "schemas/certificates").glob("*.schema.json"))
    examples = sorted((ROOT / "examples/scaffold").glob("*.json"))
    v.check("SCHEMA-COUNT", "schemas", len(schemas) == 20, "twenty certificate schemas are present")
    v.check("EXAMPLE-COUNT", "schemas", len(examples) == 20, "twenty scaffold examples are present")
    for index, schema_path in enumerate(schemas, 1):
        schema = load_json(schema_path)
        try:
            Draft202012Validator.check_schema(schema)
            valid_schema = True
        except Exception:
            valid_schema = False
        v.check(f"SCHEMA-VALID-{index:02d}", "schemas", valid_schema, f"{schema_path.name} is a valid Draft 2020-12 schema")
        stem = schema_path.name.removesuffix(".schema.json")
        example_path = ROOT / "examples/scaffold" / f"{stem}.scaffold.json"
        v.check(f"SCHEMA-EXAMPLE-{index:02d}-EXISTS", "schemas", example_path.is_file(), f"{stem} has one scaffold example")
        if example_path.is_file() and valid_schema:
            ok, detail = validate_json(schema_path, example_path)
            v.check(f"SCHEMA-EXAMPLE-{index:02d}-VALID", "schemas", ok, f"{example_path.name} validates{(': ' + detail) if detail else ''}")
            text = example_path.read_text(encoding="utf-8")
            v.check(f"SCHEMA-EXAMPLE-{index:02d}-NONCLAIM", "schemas", '"result_status": "checked-' not in text and '"result_status": "proved"' not in text, f"{example_path.name} does not claim landed evidence")


def check_corridors(v: Validation) -> None:
    rows = read_csv(ROOT / "registries/TEMPORAL_CORRIDOR_WITNESS_REGISTRY.csv")
    v.check("COR-COUNT", "corridor", len(rows) == 4, "four strict corridor witnesses are registered")
    v.check("COR-UNIQUE", "corridor", duplicate_values(rows, "corridor_id") == set(), "corridor IDs are unique")
    schema = ROOT / "schemas/certificates/strict_temporal_corridor_certificate.schema.json"
    for index, row in enumerate(rows, 1):
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        v.check(f"COR-{index:02d}-MODEL", "corridor", model_path.is_file(), f"{row['corridor_id']} model exists")
        v.check(f"COR-{index:02d}-CERT", "corridor", cert_path.is_file(), f"{row['corridor_id']} certificate exists")
        if not model_path.is_file() or not cert_path.is_file():
            continue
        model = load_json(model_path)
        cert = load_json(cert_path)
        audit = audit_strict_corridor(model)
        checks = {
            "hash-row": sha256(model_path) == row["model_sha256"],
            "hash-cert": sha256(model_path) == cert.get("model_sha256"),
            "valid": audit.strict_corridor_valid,
            "no-failures": not audit.failed_obligations,
            "replay": audit.to_dict() == cert.get("audit"),
            "lane": cert.get("claim_lanes") == ["S-L"],
            "status": cert.get("result_status") == "checked-finite-strict-temporal-corridor",
            "chain": audit.atomic_leg_count == int(row["atomic_leg_count"]),
            "mixed": audit.mixed_stage_count == int(row["mixed_stage_count"]),
            "route": audit.route_status == row["route_status"],
        }
        for offset, (name, ok) in enumerate(checks.items(), 1):
            v.check(f"COR-{index:02d}-{offset:02d}", "corridor", ok, f"{row['corridor_id']} {name}")
        ok, detail = validate_json(schema, cert_path)
        v.check(f"COR-{index:02d}-SCHEMA", "corridor", ok, f"{row['corridor_id']} certificate validates{(': ' + detail) if detail else ''}")
        for stage_index, stage in enumerate(model["episode"]["stages"]):
            v.check(f"COR-{index:02d}-STAGE-{stage_index:02d}-REAL", "corridor", stage.get("temporal_realized") is True, f"{row['corridor_id']} stage {stage_index} realizes time")
            v.check(f"COR-{index:02d}-STAGE-{stage_index:02d}-SUPPORT", "corridor", bool(stage.get("active_support")), f"{row['corridor_id']} stage {stage_index} has support")
    composed = load_json(ROOT / "models/corridors/COR-POS-02-COMPOSED.model.json")
    source = composed["carrier_chain"][0]["code"]
    target = composed["carrier_chain"][-1]["code"]
    endpoint_mixed = any(
        source in [carrier["code"] for carrier in stage["active_support"]]
        and target in [carrier["code"] for carrier in stage["active_support"]]
        for stage in composed["episode"]["stages"]
    )
    v.check("COR-COMPOSED-NO-ENDPOINT-MIX", "corridor", not endpoint_mixed, "two-leg corridor has no ultimate source/target mixed stage")
    v.check("COR-COMPOSED-VALID", "corridor", audit_strict_corridor(composed).strict_corridor_valid, "two-leg carrier-chain corridor remains valid")


def check_composition(v: Validation) -> None:
    rows = read_csv(ROOT / "registries/CORRIDOR_COMPOSITION_REGISTRY.csv")
    v.check("COMP-COUNT", "composition", len(rows) == 1, "one composition certificate is registered")
    row = rows[0]
    left_path = ROOT / "models/corridors/COR-POS-02A.model.json"
    right_path = ROOT / "models/corridors/COR-POS-02B.model.json"
    composite_path = ROOT / "models/corridors/COR-POS-02-COMPOSED.model.json"
    left, right, composite = map(load_json, (left_path, right_path, composite_path))
    rebuilt = compose_corridor_models(left, right, model_id="COR-POS-02-COMPOSED", title="two-leg strict carrier-chain temporal corridor")
    audit = audit_corridor_composition(left, right, composite)
    checks = {
        "frontier-compatible": frontier_compatible(left, right),
        "rebuild-exact": rebuilt == composite,
        "composition-valid": audit.composition_valid,
        "chain-rule": audit.chain_rule_satisfied,
        "old-rule-fails": not audit.old_endpoint_mixed_rule_satisfied,
        "leg-additive": audit.leg_count_additive,
        "boundary-once": audit.boundary_merged_once,
        "registry-valid": row["composition_valid"] == "true",
        "registry-old-false": row["old_endpoint_mixed_rule"] == "false",
        "registry-chain-true": row["carrier_chain_rule"] == "true",
    }
    for index, (name, ok) in enumerate(checks.items(), 1):
        v.check(f"COMP-{index:02d}", "composition", ok, name)
    cert_path = ROOT / row["certificate_ref"]
    cert = load_json(cert_path)
    v.check("COMP-CERT-REPLAY", "composition", cert.get("audit") == audit.to_dict(), "composition certificate audit replays")
    ok, detail = validate_json(ROOT / "schemas/certificates/corridor_composition_certificate.schema.json", cert_path)
    v.check("COMP-CERT-SCHEMA", "composition", ok, f"composition certificate validates{(': ' + detail) if detail else ''}")
    for key, path in (("left", left_path), ("right", right_path), ("composite", composite_path)):
        v.check(f"COMP-HASH-{key}", "composition", cert["source_hashes"][key] == sha256(path), f"composition {key} hash verifies")


def check_direct(v: Validation) -> None:
    rows = read_csv(ROOT / "registries/DIRECT_SUCCESSOR_REGISTRY.csv")
    v.check("DS-COUNT", "direct", len(rows) == 3, "three atomic direct successor witnesses are registered")
    v.check("DS-UNIQUE", "direct", duplicate_values(rows, "successor_id") == set(), "direct successor IDs are unique")
    schema = ROOT / "schemas/certificates/direct_successor_landed.schema.json"
    models: dict[str, Mapping[str, Any]] = {}
    for index, row in enumerate(rows, 1):
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        model = load_json(model_path)
        models[row["successor_id"]] = model
        cert = load_json(cert_path)
        audit = audit_direct_successor(model)
        checks = {
            "hash-row": sha256(model_path) == row["model_sha256"],
            "hash-cert": sha256(model_path) == cert.get("model_sha256"),
            "valid": audit.direct_successor_valid,
            "not-detached": not audit.detached_operational_pattern,
            "no-failures": not audit.failed_obligations,
            "replay": cert.get("audit") == audit.to_dict(),
            "status": cert.get("result_status") == "checked-finite-direct-temporal-successor",
            "lane": cert.get("claim_lanes") == ["S-L"],
        }
        for offset, (name, ok) in enumerate(checks.items(), 1):
            v.check(f"DS-{index:02d}-{offset:02d}", "direct", ok, f"{row['successor_id']} {name}")
        ok, detail = validate_json(schema, cert_path)
        v.check(f"DS-{index:02d}-SCHEMA", "direct", ok, f"{row['successor_id']} certificate validates{(': ' + detail) if detail else ''}")
    path_rows = read_csv(ROOT / "registries/DIRECT_SUCCESSOR_PATH_REGISTRY.csv")
    v.check("DS-PATH-COUNT", "direct", len(path_rows) == 1, "one direct-successor path is registered")
    path_row = path_rows[0]
    path_models = [models[identifier] for identifier in path_row["atomic_models"].split(";")]
    audit = audit_direct_successor_path(path_models)
    cert_path = ROOT / path_row["certificate_ref"]
    cert = load_json(cert_path)
    checks = {
        "path-valid": audit.path_valid,
        "no-atomic-endpoint": not audit.atomic_endpoint_edge_present,
        "replay": cert.get("audit") == audit.to_dict(),
        "registry-path": path_row["path_valid"] == "true",
        "registry-no-edge": path_row["atomic_endpoint_edge_present"] == "false",
        "hashes": cert.get("atomic_model_hashes") == [sha256(ROOT / rel) for rel in cert.get("atomic_model_refs", [])],
    }
    for index, (name, ok) in enumerate(checks.items(), 1):
        v.check(f"DS-PATH-{index:02d}", "direct", ok, name)
    ok, detail = validate_json(ROOT / "schemas/certificates/direct_successor_path_certificate.schema.json", cert_path)
    v.check("DS-PATH-SCHEMA", "direct", ok, f"direct path certificate validates{(': ' + detail) if detail else ''}")


def check_controls(v: Validation) -> None:
    schema = ROOT / "schemas/certificates/corridor_control_certificate.schema.json"
    corridor_rows = read_csv(ROOT / "registries/CORRIDOR_CONTROL_REGISTRY.csv")
    direct_rows = read_csv(ROOT / "registries/DIRECT_SUCCESSOR_CONTROL_REGISTRY.csv")
    v.check("CTRL-COR-COUNT", "controls", len(corridor_rows) == 25, "twenty-five corridor/composition controls are registered")
    v.check("CTRL-DS-COUNT", "controls", len(direct_rows) == 16, "sixteen direct-successor controls are registered")
    for index, row in enumerate(corridor_rows, 1):
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        model = load_json(model_path)
        cert = load_json(cert_path)
        expected = row["expected_failed_obligation"]
        if row["family"] == "strict-corridor":
            audit = audit_strict_corridor(model)
            invalid = not audit.strict_corridor_valid
            failed = audit.failed_obligations
            replay = cert.get("audit") == audit.to_dict()
        else:
            left, right = model["left"], model["right"]
            invalid = not frontier_compatible(left, right)
            failed = tuple(cert.get("observed_failed_obligations", []))
            replay = expected in failed
        checks = {
            "invalid": invalid,
            "expected-failed": expected in failed,
            "control-passed": cert.get("control_passed") is True and row["control_passed"] == "true",
            "hash": cert.get("model_sha256") == sha256(model_path),
            "replay": replay,
        }
        for offset, (name, ok) in enumerate(checks.items(), 1):
            v.check(f"CTRL-COR-{index:02d}-{offset:02d}", "controls", ok, f"{row['control_id']} {name}")
        ok, detail = validate_json(schema, cert_path)
        v.check(f"CTRL-COR-{index:02d}-SCHEMA", "controls", ok, f"{row['control_id']} schema{(': ' + detail) if detail else ''}")
    for index, row in enumerate(direct_rows, 1):
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        model = load_json(model_path)
        cert = load_json(cert_path)
        audit = audit_direct_successor(model)
        expected = row["expected_failed_obligation"]
        checks = {
            "invalid": not audit.direct_successor_valid,
            "expected-failed": expected in audit.failed_obligations,
            "control-passed": cert.get("control_passed") is True and row["control_passed"] == "true",
            "hash": cert.get("model_sha256") == sha256(model_path),
            "replay": cert.get("audit") == audit.to_dict(),
        }
        for offset, (name, ok) in enumerate(checks.items(), 1):
            v.check(f"CTRL-DS-{index:02d}-{offset:02d}", "controls", ok, f"{row['control_id']} {name}")
        ok, detail = validate_json(schema, cert_path)
        v.check(f"CTRL-DS-{index:02d}-SCHEMA", "controls", ok, f"{row['control_id']} schema{(': ' + detail) if detail else ''}")


def check_searches(v: Validation) -> None:
    expected = {
        "CORRIDOR_SUPPORT_SEARCH": bounded_corridor_support_search(),
        "NONREDUNDANCY_TRUTH_TABLE_SEARCH": bounded_nonredundancy_truth_table_search(),
        "CORRIDOR_COMPOSITION_SEARCH": bounded_corridor_composition_search(),
        "DIRECT_SUCCESSOR_SEARCH": bounded_direct_successor_search(),
        "DIRECT_PATH_COMPOSITION_SEARCH": bounded_direct_path_composition_search(),
    }
    rows = read_csv(ROOT / "registries/CORRIDOR_SEARCH_REGISTRY.csv")
    v.check("SEARCH-COUNT", "search", len(rows) == 5, "five bounded search registries are present")
    for index, row in enumerate(rows, 1):
        search_id = row["search_id"]
        path = ROOT / row["certificate_ref"]
        payload = load_json(path)
        replay = expected[search_id]
        v.check(f"SEARCH-{index:02d}-EXISTS", "search", path.is_file(), f"{search_id} certificate exists")
        v.check(f"SEARCH-{index:02d}-REPLAY", "search", payload.get("result") == replay, f"{search_id} replays exactly")
        candidates = replay.get("candidates_examined", replay.get("boolean_update_tables_examined", replay.get("candidate_pairs_examined")))
        v.check(f"SEARCH-{index:02d}-COUNT", "search", int(row["candidates_examined"]) == int(candidates), f"{search_id} count matches registry")
    support = expected["CORRIDOR_SUPPORT_SEARCH"]
    v.check("SEARCH-DETACHED", "search", support["detached_passes"] == 0, "bounded corridor family admits no detached pass")
    v.check("SEARCH-GAP", "search", support["gapped_passes"] == 0, "bounded corridor family admits no gapped pass")
    comp = expected["CORRIDOR_COMPOSITION_SEARCH"]
    v.check("SEARCH-CHAIN-COMP", "search", comp["carrier_chain_composition_failures"] == 0, "carrier-chain rule composes across the bounded family")
    v.check("SEARCH-OLD-RULE", "search", comp["old_endpoint_mixed_rule_failures"] == comp["frontier_compatible_pairs"], "old endpoint-mixedness rule fails every bounded compatible pair")
    direct = expected["DIRECT_SUCCESSOR_SEARCH"]
    v.check("SEARCH-DIRECT-DETACHED", "search", direct["detached_like_passes"] == 0, "direct criterion excludes detached shapes")
    v.check("SEARCH-DIRECT-DATA", "search", direct["arbitrary_data_edge_passes"] == 0, "direct criterion excludes arbitrary data edges")


def check_registries(v: Validation) -> None:
    theorem_rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    toy_rows = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    definitions = read_csv(ROOT / "registries/DEFINITION_REGISTRY.csv")
    kills = read_csv(ROOT / "registries/KILL_CRITERIA.csv")
    v.check("REG-THEOREM-COUNT", "registries", len(theorem_rows) == 35, "theorem registry retains 35 contracts")
    v.check("REG-THEOREM-UNIQUE", "registries", duplicate_values(theorem_rows, "theorem_id") == set(), "theorem IDs are unique")
    expected_statuses = Counter({
        "open-scaffold": 12,
        "proof-source-and-executable-certificate-landed": 10,
        "checked-finite-countermodel": 10,
        "proof-source-and-checked-finite-countermodel": 2,
        "finite-discriminator-evidence-landed-theorem-open": 1,
    })
    v.check("REG-THEOREM-STATUS", "registries", Counter(row["status"] for row in theorem_rows) == expected_statuses, "theorem status distribution matches phase freeze")
    by_theorem = {row["theorem_id"]: row for row in theorem_rows}
    for index, (theorem_id, status) in enumerate({
        "TTH-04": "proof-source-and-executable-certificate-landed",
        "TTN-01": "proof-source-and-checked-finite-countermodel",
        "TTN-09": "proof-source-and-checked-finite-countermodel",
        "TTD-01": "proof-source-and-executable-certificate-landed",
        "TTD-02": "finite-discriminator-evidence-landed-theorem-open",
        "TTD-03": "proof-source-and-executable-certificate-landed",
        "TTH-05": "open-scaffold",
        "TTH-06": "open-scaffold",
    }.items(), 1):
        v.check(f"REG-THEOREM-{index:02d}", "registries", by_theorem[theorem_id]["status"] == status, f"{theorem_id} status is {status}")
    theorem_schema = ROOT / "schemas/registries/theorem_registry_row.schema.json"
    schema = load_json(theorem_schema)
    validator = Draft202012Validator(schema)
    for index, row in enumerate(theorem_rows, 1):
        errors = list(validator.iter_errors(row))
        v.check(f"REG-THEOREM-SCHEMA-{index:02d}", "registries", not errors, f"{row['theorem_id']} matches theorem schema")
    v.check("REG-TOY-COUNT", "registries", len(toy_rows) == 23, "toy registry retains 23 models")
    v.check("REG-TOY-UNIQUE", "registries", duplicate_values(toy_rows, "toy_id") == set(), "toy IDs are unique")
    v.check("REG-DEF-COUNT", "registries", len(definitions) == 64, "definition registry contains 64 typed entries")
    v.check("REG-DEF-UNIQUE", "registries", duplicate_values(definitions, "definition_id") == set(), "definition IDs are unique")
    names = {row["name"] for row in definitions}
    for index, name in enumerate(("FiniteTemporalStage", "InterventionProjection", "AtomicTemporalCorridorData", "CorridorSummaryData", "FrontierCompatible", "AtomicDirectSuccessorData", "DetachedOperationalPattern", "DirectSuccessorPathData"), 1):
        v.check(f"REG-DEF-{index:02d}", "registries", name in names, f"definition {name} is registered")
    v.check("REG-KILL-COUNT", "registries", len(kills) == 18, "kill register retains eighteen criteria")
    by_kill = {row["kill_id"]: row["status"] for row in kills}
    for index, kill_id in enumerate(("K-FIACH-02", "K-FIACH-03", "K-FIACH-04", "K-DIRECT-01"), 1):
        v.check(f"REG-KILL-{index:02d}", "registries", by_kill[kill_id] == "not-triggered-CST-TT-04", f"{kill_id} is closed not triggered")
    v.check("REG-FALLBACK-LOCK", "registries", load_json(ROOT / "registries/PROJECT_REGISTRY.json").get("fallback_unlocked") is False, "Temporal-IAPS remains locked")


def check_lean(v: Validation) -> None:
    modules = [
        ROOT / "CSTTT/Corridor/FiniteTemporalCorridor.lean",
        ROOT / "CSTTT/Corridor/Composition.lean",
        ROOT / "CSTTT/Corridor/FiniteDirectSuccessor.lean",
    ]
    root_imports = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    corpus = ""
    for index, path in enumerate(modules, 1):
        text = path.read_text(encoding="utf-8")
        corpus += "\n" + text
        module = path.relative_to(ROOT).with_suffix("").as_posix().replace("/", ".")
        v.check(f"LEAN-{index:02d}-EXISTS", "lean", path.is_file(), f"{path.name} exists")
        v.check(f"LEAN-{index:02d}-IMPORT", "lean", f"import {module}" in root_imports, f"{module} is imported")
        v.check(f"LEAN-{index:02d}-PLACEHOLDER", "lean", not re.search(r"\b(sorry|admit|axiom|unsafe)\b", text), f"{path.name} has no forbidden placeholder command")
        v.check(f"LEAN-{index:02d}-DELIM", "lean", text.count("(") == text.count(")") and text.count("{") == text.count("}"), f"{path.name} has balanced simple delimiters")
    declarations = (
        "atomicTemporalCorridorCertificateSound",
        "noMixedStageExcludesAtomicCorridor",
        "realizedGapExcludesAtomicCorridor",
        "strictTemporalCorridorComposition",
        "directSuccessorValidity",
        "directSuccessorDetachedCopyExclusion",
        "directSuccessorPathComposition",
    )
    for index, declaration in enumerate(declarations, 1):
        v.check(f"LEAN-DECL-{index:02d}", "lean", declaration in corpus, f"Lean declaration {declaration} is present")
    findings = scan_primitive_tree(ROOT)
    v.check("LEAN-CIRCULARITY", "lean", not findings, f"primitive circularity scan is empty ({len(findings)} findings)")


def check_boundaries(v: Validation) -> None:
    phase = (ROOT / "docs/PHASE_BOUNDARY.md").read_text(encoding="utf-8")
    decision = (ROOT / "docs/CST-TT-04_DECISION_GATE.md").read_text(encoding="utf-8")
    completion = (ROOT / "manifests/CST-TT-04_COMPLETION_REPORT.md").read_text(encoding="utf-8")
    for index, phrase in enumerate((
        "composition-stable strict carrier-chain temporal corridor",
        "post-withdrawal autonomy",
        "positive Temporal-FIACH",
        "Temporal-IAPS",
        "phenomenal, personal-survival, or numerical-identity conclusions",
        "CST-TT-05",
    ), 1):
        v.check(f"BOUND-{index:02d}", "boundaries", phrase in phase, f"phase boundary contains {phrase}")
    for index, phrase in enumerate((
        "K-FIACH-02",
        "K-FIACH-03",
        "K-FIACH-04",
        "K-DIRECT-01",
        "Temporal-FIACH remains primary",
        "Temporal-IAPS remains locked",
    ), 1):
        v.check(f"DECISION-{index:02d}", "boundaries", phrase in decision, f"decision gate contains {phrase}")
    v.check("BOUND-COMPLETE-NO-HANDOFF", "boundaries", "No positive integrated handoff" in completion, "completion report does not overclaim integrated handoff")
    v.check("BOUND-COMPLETE-NO-LEAN", "boundaries", "Actual Lean compilation is not claimed" in completion, "completion report does not overclaim Lean compilation")
    comparison = read_csv(ROOT / "registries/OVERLAP_DIRECT_COMPARISON.csv")
    v.check("BOUND-COMPARE-COUNT", "boundaries", len(comparison) == 9, "nine comparison cases distinguish the two lineage classes")
    by_case = {row["case_id"]: row for row in comparison}
    v.check("BOUND-CMP-01", "boundaries", by_case["CMP-01"]["strict_overlap_chain"] == "pass" and by_case["CMP-01"]["atomic_direct_successor"] == "fail", "atomic overlap is not silently classified as direct")
    v.check("BOUND-CMP-03", "boundaries", by_case["CMP-03"]["strict_overlap_chain"] == "fail" and by_case["CMP-03"]["atomic_direct_successor"] == "pass", "atomic direct successor is not silently classified as overlap")
    v.check("BOUND-CMP-05", "boundaries", all(by_case["CMP-05"][key] == "fail" for key in ("strict_overlap_chain", "atomic_direct_successor", "direct_successor_path")), "detached exact copy fails both lineage classes")


def check_manifest(v: Validation, require_manifest: bool) -> None:
    manifest_path = ROOT / "manifests/CST-TT-04_MANIFEST.json"
    checksum_path = ROOT / "manifests/CST-TT-04_SHA256SUMS"
    if not manifest_path.is_file() or not checksum_path.is_file():
        if require_manifest:
            v.check("MANIFEST-EXISTS", "manifest", False, "frozen manifest and checksum ledger exist")
        else:
            v.skip("MANIFEST-EXISTS", "manifest", "manifest not required before final freeze")
        return
    manifest = load_json(manifest_path)
    rows = manifest.get("files", [])
    v.check("MANIFEST-PHASE", "manifest", manifest.get("phase") == PHASE, "manifest phase is CST-TT-04")
    v.check("MANIFEST-COUNT", "manifest", manifest.get("file_count") == len(rows) and len(rows) >= 900, f"manifest records all files ({len(rows)})")
    for index, row in enumerate(rows, 1):
        path = ROOT / row["path"]
        v.check(f"MANIFEST-{index:04d}-EXISTS", "manifest", path.is_file(), f"{row['path']} exists")
        if path.is_file():
            v.check(f"MANIFEST-{index:04d}-SIZE", "manifest", path.stat().st_size == row["bytes"], f"{row['path']} byte count verifies")
            v.check(f"MANIFEST-{index:04d}-HASH", "manifest", sha256(path) == row["sha256"], f"{row['path']} hash verifies")
    checksum_rows = checksum_path.read_text(encoding="utf-8").splitlines()
    v.check("CHECKSUM-COUNT", "manifest", len(checksum_rows) == len(rows) + 2, "checksum ledger includes files plus both manifest aliases")
    for index, line in enumerate(checksum_rows, 1):
        parts = line.split(maxsplit=1)
        ok = len(parts) == 2
        if ok:
            expected, rel = parts
            path = ROOT / rel.strip().lstrip("*")
            ok = path.is_file() and sha256(path) == expected
        v.check(f"CHECKSUM-{index:04d}", "manifest", ok, f"checksum row {index} verifies")


def write_report(v: Validation) -> None:
    counts = Counter(row.status for row in v.results)
    payload = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "generated_date": "2026-08-10",
        "status": "PASS" if not v.failures else "FAIL",
        "total": len(v.results),
        "passed": counts["PASS"],
        "failed": counts["FAIL"],
        "skipped": counts["SKIP"],
        "results": [asdict(row) for row in v.results],
    }
    out_json = ROOT / "manifests/CST-TT-04_VALIDATION_RESULTS.json"
    out_md = ROOT / "manifests/CST-TT-04_VALIDATION_REPORT.md"
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    categories = Counter(row.category for row in v.results)
    lines = [
        "# CST-TT-04 Validation Report",
        "",
        f"**Status:** {payload['status']}",
        f"**Total checks:** {payload['total']}",
        f"**Passed:** {payload['passed']}",
        f"**Failed:** {payload['failed']}",
        f"**Skipped:** {payload['skipped']}",
        "",
        "## Coverage",
        "",
    ]
    lines.extend(f"- **{name}:** {count}" for name, count in sorted(categories.items()))
    lines.extend([
        "",
        "The sole expected skip in this environment is the Lean compilation check when `lean` and `lake` are absent. Static source checks, executable finite certificates, and Python tests do not substitute for Lean-kernel compilation.",
    ])
    if v.failures:
        lines.extend(["", "## Failures", ""])
        lines.extend(f"- `{row.check_id}` ({row.category}): {row.detail}" for row in v.failures)
    out_md.write_text("\n".join(lines) + "\n", encoding="utf-8")
    (ROOT / "manifests/VALIDATION_RESULTS.json").write_text(out_json.read_text(encoding="utf-8"), encoding="utf-8")
    (ROOT / "manifests/VALIDATION_REPORT.md").write_text(out_md.read_text(encoding="utf-8"), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--no-write", action="store_true", help="run checks without rewriting validation reports")
    parser.add_argument("--require-clean", action="store_true")
    parser.add_argument("--require-tag", action="store_true")
    parser.add_argument("--require-manifest", action="store_true")
    args = parser.parse_args()

    v = Validation()
    check_baseline(v, args.require_clean, args.require_tag)
    check_toolchain(v)
    check_python(v)
    check_provenance(v)
    check_inherited_assets(v)
    check_schema_bank(v)
    check_corridors(v)
    check_composition(v)
    check_direct(v)
    check_controls(v)
    check_searches(v)
    check_registries(v)
    check_lean(v)
    check_boundaries(v)
    check_manifest(v, args.require_manifest)

    counts = Counter(row.status for row in v.results)
    if not args.no_write:
        write_report(v)
    print(json.dumps({"phase": PHASE, "status": "PASS" if not v.failures else "FAIL", "total": len(v.results), "passed": counts["PASS"], "failed": counts["FAIL"], "skipped": counts["SKIP"]}, sort_keys=True))
    if v.failures:
        for row in v.failures[:30]:
            print(f"FAIL {row.check_id}: {row.detail}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
