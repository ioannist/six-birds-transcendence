#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import py_compile
import shutil
import subprocess
import sys
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from cst_tt.fiach import audit_temporal_fiach, lane_truth_table, replay_component_certificates  # noqa: E402
from cst_tt.package_gluing import audit_package, audit_staged_assembly  # noqa: E402
from cst_tt.registry import duplicate_values, read_csv  # noqa: E402
from cst_tt.withdrawal_autonomy_checker import (  # noqa: E402
    audit_autonomy,
    bounded_invariant_algorithm_exhaustion,
    finite_horizon_word_count,
)

PHASE = "CST-TT-05"
BASE_TAG = "CST-TT-04-v1"
BASE_COMMIT = "1884214d1bae82442f37fc9e6b013e222da89b1b"
PHASE_TAG = "CST-TT-05-v1"


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
        except Exception as exc:  # pragma: no cover
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


def validate_json(schema_name: str, instance: Path) -> tuple[bool, str]:
    schema = load_json(ROOT / "schemas/certificates" / schema_name)
    Draft202012Validator.check_schema(schema)
    errors = sorted(Draft202012Validator(schema).iter_errors(load_json(instance)), key=lambda error: list(error.path))
    return not errors, "; ".join(error.message for error in errors[:5])


def check_baseline(v: Validation, require_clean: bool, require_tag: bool) -> None:
    v.guarded("BASE-001", "baseline", "repository is a Git worktree", lambda: git("rev-parse", "--is-inside-work-tree") == "true")
    v.guarded("BASE-002", "baseline", f"{BASE_TAG} resolves to frozen base", lambda: git("rev-parse", BASE_TAG + "^{}") == BASE_COMMIT)
    v.guarded("BASE-003", "baseline", "frozen base is ancestor of HEAD", lambda: subprocess.run(["git", "merge-base", "--is-ancestor", BASE_COMMIT, "HEAD"], cwd=ROOT).returncode == 0)
    v.guarded("BASE-004", "baseline", "repository has no whitespace errors", lambda: subprocess.run(["git", "diff", "--check"], cwd=ROOT, capture_output=True).returncode == 0)
    if require_clean:
        v.guarded("BASE-005", "baseline", "working tree is clean", lambda: git("status", "--porcelain") == "")
    else:
        v.check("BASE-005", "baseline", True, "clean-tree check deferred until release verification")
    tags = set(git("tag", "--list").splitlines())
    if require_tag:
        v.check("BASE-006", "baseline", PHASE_TAG in tags, f"phase tag {PHASE_TAG} exists")
        if PHASE_TAG in tags:
            v.check("BASE-007", "baseline", git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD"), "phase tag resolves to HEAD")
    else:
        v.check("BASE-006", "baseline", PHASE_TAG not in tags or git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD"), "phase tag absent before freeze or already resolves to HEAD")


def check_toolchain(v: Validation) -> None:
    v.check("TOOL-001", "toolchain", (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.28.0", "Lean toolchain remains pinned")
    pyproject = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    for index, token in enumerate((">=3.13,<3.14", "pytest==9.0.2", "jsonschema==4.26.0", "setuptools==82.0.1"), 1):
        v.check(f"TOOL-PIN-{index:02d}", "toolchain", token in pyproject, f"pyproject contains {token}")
    v.check("TOOL-PY", "toolchain", sys.version_info[:2] == (3, 13), f"Python 3.13 is running ({sys.version.split()[0]})")
    status = load_json(ROOT / "formal/TOOLCHAIN_STATUS.json")
    v.check("TOOL-STATUS-PHASE", "toolchain", status.get("phase") == PHASE, "toolchain status is phase-current")
    v.check("TOOL-STATUS-LEAN", "toolchain", status.get("lean_compile_status") == "pending-toolchain", "Lean compile status is not overclaimed")
    v.check("TOOL-STATUS-PY", "toolchain", status.get("python_certificate_status") == "checked", "Python certificates are checked")
    lean, lake = shutil.which("lean"), shutil.which("lake")
    if lean and lake:
        proc = subprocess.run([lake, "build"], cwd=ROOT, text=True, capture_output=True)
        v.check("TOOL-LEAN-BUILD", "toolchain", proc.returncode == 0, "pinned Lean sources compile with lake build")
    else:
        v.skip("TOOL-LEAN-BUILD", "toolchain", "lean/lake unavailable; no compilation pass claimed")


def check_python(v: Validation) -> None:
    files = sorted([*SRC.rglob("*.py"), *(ROOT / "scripts").glob("*.py"), *(ROOT / "tests").glob("*.py")])
    v.check("PY-COUNT", "python", len(files) >= 60, f"at least sixty Python files are present ({len(files)})")
    for index, path in enumerate(files, 1):
        v.guarded(f"PY-COMPILE-{index:03d}", "python", f"{path.relative_to(ROOT)} compiles", lambda p=path: py_compile.compile(str(p), doraise=True) is not None)
    proc = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=ROOT, text=True, capture_output=True, env={**__import__("os").environ, "PYTHONPATH": "src:scripts", "PYTHONHASHSEED": "0"})
    detail = "full pytest suite passes"
    if proc.returncode != 0:
        detail += ": " + (proc.stdout + proc.stderr)[-3000:].replace("\n", " ")
    v.check("PY-TESTS", "python", proc.returncode == 0, detail)


def check_provenance(v: Validation) -> None:
    inherited = {
        "CST-TT-00-v1": "65b3ab0f94564cee1d16ffb4513045319aaaf6ef",
        "CST-TT-01-v1": "488db50b20d6d9c67493de3e9fd758e6e9e205ce",
        "CST-TT-02-v1": "3abf5b2406f754b43823b68987c7ea409e737fd0",
        "CST-TT-03-v1": "63ea725a7b6ade8df58a94cf7aad2ad78440ce70",
        BASE_TAG: BASE_COMMIT,
    }
    for index, (tag, commit) in enumerate(inherited.items(), 1):
        v.guarded(f"PROV-TAG-{index:02d}", "provenance", f"{tag} resolves to frozen commit", lambda t=tag, c=commit: git("rev-parse", t + "^{}") == c)
    checksum_file = ROOT / "inputs/normative/cst-tt-00/IMPORTED_SHA256SUMS.txt"
    rows = checksum_file.read_text(encoding="utf-8").splitlines()
    for index, line in enumerate(rows, 1):
        digest, rel = line.split(maxsplit=1)
        path = ROOT / rel.lstrip("*")
        v.check(f"PROV-INPUT-{index:03d}", "provenance", path.is_file() and sha256(path) == digest, f"imported surface {rel} is hash-bound")
    sources = sorted((ROOT / "inputs/reference_surfaces/temporal_audit").glob("*.tex"))
    v.check("PROV-SOURCES", "provenance", len(sources) == 9, "nine temporal SBT manuscripts are retained")


def check_schemas(v: Validation) -> None:
    schemas = sorted((ROOT / "schemas/certificates").glob("*.schema.json"))
    examples = sorted((ROOT / "examples/scaffold").glob("*.json"))
    v.check("SCHEMA-COUNT", "schemas", len(schemas) == 26, "twenty-six certificate schemas are present")
    v.check("EXAMPLE-COUNT", "schemas", len(examples) == 26, "twenty-six scaffold examples are present")
    registry = read_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv")
    v.check("SCHEMA-REGISTRY-COUNT", "schemas", len(registry) == 26, "schema registry has twenty-six rows")
    for index, row in enumerate(registry, 1):
        schema_path = ROOT / "schemas/certificates" / row["file"]
        example_path = ROOT / row["scaffold_example"]
        v.check(f"SCHEMA-FILE-{index:02d}", "schemas", schema_path.is_file(), f"schema {row['schema_id']} exists")
        v.check(f"SCHEMA-EXAMPLE-{index:02d}", "schemas", example_path.is_file(), f"scaffold {row['schema_id']} exists")
        if schema_path.is_file() and example_path.is_file():
            try:
                schema = load_json(schema_path)
                Draft202012Validator.check_schema(schema)
                errors = list(Draft202012Validator(schema).iter_errors(load_json(example_path)))
                v.check(f"SCHEMA-VALID-{index:02d}", "schemas", not errors, f"{row['schema_id']} schema and scaffold validate")
            except Exception as exc:
                v.check(f"SCHEMA-VALID-{index:02d}", "schemas", False, f"{row['schema_id']} failed: {exc}")


def check_aligned_packages(v: Validation) -> None:
    rows = read_csv(ROOT / "registries/HANDOFF_ALIGNED_PACKAGE_REGISTRY.csv")
    v.check("PKG-ALIGNED-COUNT", "packages", len(rows) == 2, "two handoff-aligned package witnesses exist")
    corridor = load_json(ROOT / "models/corridors/COR-POS-01.model.json")
    stages = {int(row["stage"]): row for row in corridor["episode"]["stages"]}
    for index, row in enumerate(rows, 1):
        model_path, cert_path = ROOT / row["model_ref"], ROOT / row["certificate_ref"]
        v.check(f"PKG-FILES-{index:02d}", "packages", model_path.is_file() and cert_path.is_file(), f"{row['package_id']} files exist")
        if not model_path.is_file() or not cert_path.is_file():
            continue
        cert = load_json(cert_path)
        model = load_json(model_path)
        valid, detail = validate_json("aligned_package_certificate.schema.json", cert_path)
        v.check(f"PKG-SCHEMA-{index:02d}", "packages", valid, f"{row['package_id']} schema validates: {detail}")
        v.check(f"PKG-HASH-{index:02d}", "packages", sha256(model_path) == cert.get("model_sha256"), f"{row['package_id']} model hash binds")
        audit = audit_package(model)
        v.check(f"PKG-AUDIT-{index:02d}", "packages", audit.integrated_package_valid and cert.get("audit") == audit.to_dict(), f"{row['package_id']} package replay passes")
        alignment = cert["handoff_alignment"]
        stage = stages[int(alignment["corridor_stage"])]
        c6 = next(item["assignment"] for item in model["clauses"] if item["clause"] == "C6_TEMPORAL_CLOSURE")
        v.check(f"PKG-ROUTE-{index:02d}", "packages", c6["route_residue"] == stage["signature"]["route_residue"], f"{row['package_id']} route frontier aligns")
        v.check(f"PKG-TICK-{index:02d}", "packages", c6["tick_phase"] == stage["signature"]["tick_index"], f"{row['package_id']} tick frontier aligns")
        v.check(f"PKG-RECORD-{index:02d}", "packages", c6["record_before"] == stage["signature"]["record_value"], f"{row['package_id']} record frontier aligns")
        v.check(f"PKG-OWNER-{index:02d}", "packages", c6["maintenance_owner"] == stage["signature"]["maintenance_owner"], f"{row['package_id']} owner frontier aligns")
    staged_path = ROOT / "formal/certificates/packages/STG-POS-02-FIACH.certificate.json"
    valid, detail = validate_json("aligned_staged_package_certificate.schema.json", staged_path)
    v.check("PKG-STAGED-SCHEMA", "packages", valid, f"aligned staged certificate validates: {detail}")
    cert = load_json(staged_path)
    assembly = load_json(ROOT / cert["assembly_ref"])
    source = load_json(ROOT / cert["source_model_ref"])
    target = load_json(ROOT / cert["target_model_ref"])
    audit = audit_staged_assembly(assembly, source, target)
    v.check("PKG-STAGED-AUDIT", "packages", audit.staged_assembly_valid and cert["audit"] == audit.to_dict(), "aligned staged assembly replays")


def check_autonomy(v: Validation) -> None:
    cert_path = ROOT / "formal/certificates/autonomy/AUT-POS-01.certificate.json"
    valid, detail = validate_json("post_withdrawal_autonomy_certificate.schema.json", cert_path)
    v.check("AUT-SCHEMA", "autonomy", valid, f"positive autonomy certificate validates: {detail}")
    cert = load_json(cert_path)
    model_path = ROOT / cert["model_ref"]
    v.check("AUT-HASH", "autonomy", model_path.is_file() and sha256(model_path) == cert["model_sha256"], "autonomy model is hash-bound")
    model = load_json(model_path)
    audit = audit_autonomy(model)
    v.check("AUT-VALID", "autonomy", audit.autonomy_valid, "positive autonomy witness passes")
    v.check("AUT-REPLAY", "autonomy", cert["audit"] == audit.to_dict(), "autonomy audit replays byte-semantically")
    obligations = {
        "withdrawal": audit.withdrawal_complete,
        "retained-owner": audit.retained_resources_target_owned,
        "endpoint": audit.endpoint_inside,
        "package": audit.package_inside,
        "resource-closure": audit.resource_closed_on_invariant,
        "response": audit.target_owned_responses,
        "anti-stall": audit.anti_stall_on_invariant,
        "budget": audit.budget_solvent_on_invariant,
        "finite-horizon": audit.finite_horizon_survives,
        "verdict-separation": audit.forbidden_verdict_fields_absent,
    }
    for index, (name, status) in enumerate(obligations.items(), 1):
        v.check(f"AUT-OBL-{index:02d}", "autonomy", status, f"autonomy obligation {name} passes")
    v.check("AUT-WORDS", "autonomy", audit.finite_words_checked == finite_horizon_word_count(2, 6) == 127, "all 127 finite disturbance words are checked")
    rows = read_csv(ROOT / "registries/AUTONOMY_CONTROL_REGISTRY.csv")
    v.check("AUT-CONTROL-COUNT", "autonomy", len(rows) == 12, "twelve autonomy controls exist")
    for index, row in enumerate(rows, 1):
        control_path = ROOT / row["certificate_ref"]
        valid, detail = validate_json("autonomy_control_certificate.schema.json", control_path)
        v.check(f"AUT-CONTROL-SCHEMA-{index:02d}", "autonomy", valid, f"{row['control_id']} schema validates: {detail}")
        control = load_json(control_path)
        model_path = ROOT / row["model_ref"]
        control_audit = audit_autonomy(load_json(model_path))
        v.check(f"AUT-CONTROL-FAIL-{index:02d}", "autonomy", not control_audit.autonomy_valid and row["expected_primary_failure"] in control_audit.failed_obligations, f"{row['control_id']} fails expected obligation")
        v.check(f"AUT-CONTROL-REPLAY-{index:02d}", "autonomy", control["audit"] == control_audit.to_dict(), f"{row['control_id']} replay matches")
        v.check(f"AUT-CONTROL-HASH-{index:02d}", "autonomy", sha256(model_path) == control["model_sha256"], f"{row['control_id']} model hash binds")
    search = bounded_invariant_algorithm_exhaustion()
    frozen = load_json(ROOT / "formal/certificates/search/AUTONOMY_INVARIANT_EXHAUSTION.json")
    for index, key in enumerate(("candidate_count", "endpoint_autonomous_count", "algorithm_bruteforce_mismatch_count", "all_candidates_verified"), 1):
        v.check(f"AUT-SEARCH-{index:02d}", "autonomy", frozen[key] == search[key], f"autonomy search field {key} reproduces")
    v.check("AUT-SEARCH-ZERO", "autonomy", search["candidate_count"] == 4096 and search["algorithm_bruteforce_mismatch_count"] == 0, "4,096-case fixed-point exhaustion has zero mismatches")


def check_fiach(v: Validation) -> None:
    cert_path = ROOT / "formal/certificates/fiach/FIACH-POS-01.certificate.json"
    model_path = ROOT / "models/fiach/FIACH-POS-01.model.json"
    valid, detail = validate_json("temporal_fiach_landed_certificate.schema.json", cert_path)
    v.check("FIACH-SCHEMA", "fiach", valid, f"positive FIACH certificate validates: {detail}")
    cert, spec = load_json(cert_path), load_json(model_path)
    audit = audit_temporal_fiach(spec, ROOT)
    v.check("FIACH-VALID", "fiach", audit.aggregate_valid, "FIACH aggregate passes")
    v.check("FIACH-REPLAY", "fiach", cert["audit"] == audit.to_dict(), "FIACH aggregate replay matches")
    v.check("FIACH-LANES", "fiach", cert["lane_results"] == {"S-T": True, "S-R": True, "S-L": True, "A": True}, "all four structural lanes are independently positive")
    components = replay_component_certificates(spec, ROOT)
    for index, (name, status) in enumerate(sorted(components.items()), 1):
        v.check(f"FIACH-COMPONENT-{index:02d}", "fiach", status, f"component {name} replays")
    links = {
        "hashes": audit.component_hashes_valid,
        "distinct": audit.source_target_distinct,
        "source": audit.source_endpoints_linked,
        "target": audit.target_endpoints_linked,
        "staged": audit.staged_models_linked,
        "temporal-frontier": audit.corridor_package_temporal_frontier_linked,
        "handoff-event": audit.corridor_autonomy_handoff_linked,
        "package-contract": audit.autonomy_package_contract_linked,
        "route": audit.route_status_linked,
        "recognition": audit.recognition_separate,
        "ontology": audit.ontology_absent,
    }
    for index, (name, status) in enumerate(links.items(), 1):
        v.check(f"FIACH-LINK-{index:02d}", "fiach", status, f"FIACH linkage {name} passes")
    rows = read_csv(ROOT / "registries/FIACH_LANE_CONTROL_REGISTRY.csv")
    v.check("FIACH-CONTROL-COUNT", "fiach", len(rows) == 6, "six one/two-lane controls exist")
    patterns: set[tuple[bool, bool, bool]] = set()
    for index, row in enumerate(rows, 1):
        control_path = ROOT / row["certificate_ref"]
        valid, detail = validate_json("fiach_lane_control_certificate.schema.json", control_path)
        v.check(f"FIACH-CONTROL-SCHEMA-{index:02d}", "fiach", valid, f"{row['control_id']} schema validates: {detail}")
        control = load_json(control_path)
        control_spec = load_json(ROOT / row["model_ref"])
        control_audit = audit_temporal_fiach(control_spec, ROOT)
        pattern = (control_audit.structural_realization_lane, control_audit.structural_lineage_lane, control_audit.autonomy_lane)
        patterns.add(pattern)
        expected = (row["S-R"] == "true", row["S-L"] == "true", row["A"] == "true")
        v.check(f"FIACH-CONTROL-PATTERN-{index:02d}", "fiach", pattern == expected and not control_audit.aggregate_valid, f"{row['control_id']} realizes only its declared lanes")
        v.check(f"FIACH-CONTROL-REPLAY-{index:02d}", "fiach", control["audit"] == control_audit.to_dict(), f"{row['control_id']} replay matches")
    expected_patterns = {(True, False, False), (False, True, False), (False, False, True), (True, True, False), (True, False, True), (False, True, True)}
    v.check("FIACH-PATTERNS", "fiach", patterns == expected_patterns, "all one/two-lane patterns are represented")
    truth = lane_truth_table()
    v.check("FIACH-TRUTH", "fiach", truth == load_json(ROOT / "formal/certificates/search/FIACH_LANE_TRUTH_TABLE.json") and truth["positive_row_count"] == 1, "eight-row exact conjunction table reproduces")


def check_registries(v: Validation) -> None:
    theorem = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    v.check("REG-THEOREM-COUNT", "registries", len(theorem) == 35, "theorem registry retains 35 contracts")
    v.check("REG-THEOREM-UNIQUE", "registries", duplicate_values(theorem, "theorem_id") == set(), "theorem IDs are unique")
    statuses = Counter(row["status"] for row in theorem)
    expected = Counter({"proof-source-and-executable-certificate-landed": 12, "open-scaffold": 10, "checked-finite-countermodel": 9, "proof-source-and-checked-finite-countermodel": 3, "finite-discriminator-evidence-landed-theorem-open": 1})
    v.check("REG-THEOREM-STATUS", "registries", statuses == expected, "theorem status accounting is exact")
    by_id = {row["theorem_id"]: row for row in theorem}
    for index, theorem_id in enumerate(("TTH-05", "TTH-06", "TTN-06"), 1):
        v.check(f"REG-ADVANCED-{index:02d}", "registries", by_id[theorem_id]["phase"] == PHASE and "proof-source" in by_id[theorem_id]["status"], f"{theorem_id} advanced in CST-TT-05")
    definitions = read_csv(ROOT / "registries/DEFINITION_REGISTRY.csv")
    v.check("REG-DEF-COUNT", "registries", len(definitions) == 69, "definition registry has 69 rows")
    v.check("REG-DEF-UNIQUE", "registries", duplicate_values(definitions, "definition_id") == set(), "definition IDs are unique")
    toys = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    v.check("REG-TOY-COUNT", "registries", len(toys) == 23, "toy registry retains 23 rows")
    package = read_csv(ROOT / "registries/PACKAGE_WITNESS_REGISTRY.csv")
    v.check("REG-PKG-COUNT", "registries", len(package) == 4, "package registry has legacy and aligned witnesses")
    project = load_json(ROOT / "registries/PROJECT_REGISTRY.json")
    expected_project = {
        "phase": PHASE,
        "phase_base_tag": BASE_TAG,
        "phase_base_commit": BASE_COMMIT,
        "checked_post_withdrawal_autonomy_certificates": 1,
        "checked_autonomy_controls": 12,
        "checked_temporal_fiach_certificates": 1,
        "checked_fiach_lane_controls": 6,
        "positive_handoff_witnesses": 1,
        "fallback_unlocked": False,
        "next_phase": "CST-TT-06",
    }
    for index, (key, value) in enumerate(expected_project.items(), 1):
        v.check(f"REG-PROJECT-{index:02d}", "registries", project.get(key) == value, f"project registry {key}={value!r}")
    kills = {row["kill_id"]: row for row in read_csv(ROOT / "registries/KILL_CRITERIA.csv")}
    v.check("REG-KILL-FIACH", "registries", kills["K-FIACH-05"]["status"] == "not-triggered-CST-TT-05", "positive witness prevents FIACH kill")
    v.check("REG-KILL-AUTO1", "registries", kills["K-AUTO-01"]["status"].endswith("CST-TT-05"), "removed-resource autonomy kill is not triggered")
    v.check("REG-KILL-AUTO2", "registries", kills["K-AUTO-02"]["status"].endswith("CST-TT-05"), "stall autonomy kill is not triggered")


def check_lean_static(v: Validation) -> None:
    files = [ROOT / "CSTTT/Autonomy/FiniteAutonomy.lean", ROOT / "CSTTT/Targets/FiniteTemporalFIACH.lean"]
    aggregate = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    for index, path in enumerate(files, 1):
        text = path.read_text(encoding="utf-8")
        lowered = text.lower()
        v.check(f"LEAN-FILE-{index:02d}", "lean-static", path.stat().st_size > 1000, f"{path.relative_to(ROOT)} is substantive")
        for j, forbidden in enumerate(("sorry", "admit", "axiom", "unsafe"), 1):
            v.check(f"LEAN-PLACEHOLDER-{index:02d}-{j:02d}", "lean-static", forbidden not in lowered, f"{path.name} contains no {forbidden}")
        v.check(f"LEAN-NAMESPACE-{index:02d}", "lean-static", text.count("namespace ") == text.count("end CSTTT."), f"{path.name} namespace delimiters balance")
        v.check(f"LEAN-IMPORT-{index:02d}", "lean-static", f"import {path.relative_to(ROOT).with_suffix('').as_posix().replace('/', '.')}" in aggregate, f"aggregate imports {path.name}")
    declarations = {
        "finiteHorizonRunExists": files[0],
        "postWithdrawalFiniteHorizonInvariance": files[0],
        "removedEssentialResourceExcludesAutonomy": files[0],
        "stalledOnlyResponsesExcludeAutonomy": files[0],
        "insolventOnlyResponsesExcludeAutonomy": files[0],
        "temporalFIACHCertificateSoundness": files[1],
        "temporalFIACHEndpointsLinked": files[1],
        "threeLaneAggregateExact": files[1],
    }
    for index, (name, path) in enumerate(declarations.items(), 1):
        v.check(f"LEAN-DECL-{index:02d}", "lean-static", name in path.read_text(encoding="utf-8"), f"Lean declaration {name} exists")
    lines = aggregate.splitlines()
    v.check("LEAN-LAYERING", "lean-static", lines.index("import CSTTT.Autonomy.FiniteAutonomy") < lines.index("import CSTTT.Targets.FiniteTemporalFIACH"), "autonomy module precedes aggregate target module")


def check_claim_boundaries(v: Validation) -> None:
    docs = [
        ROOT / "docs/POST_WITHDRAWAL_AUTONOMY.md",
        ROOT / "docs/INTEGRATED_TEMPORAL_FIACH_THEOREM.md",
        ROOT / "docs/PHASE_BOUNDARY.md",
        ROOT / "manifests/CST-TT-05_COMPLETION_REPORT.md",
    ]
    for index, path in enumerate(docs, 1):
        text = path.read_text(encoding="utf-8").lower()
        v.check(f"BOUNDARY-DOC-{index:02d}", "boundaries", "consciousness" in text and ("does not" in text or "not landed" in text or "no consciousness" in text), f"{path.name} states the consciousness nonclaim")
    fiach = load_json(ROOT / "formal/certificates/fiach/FIACH-POS-01.certificate.json")
    v.check("BOUNDARY-RECOGNITION", "boundaries", fiach["recognition_status"] == "not-addressed", "recognition remains separate")
    v.check("BOUNDARY-ONTOLOGY", "boundaries", fiach["audit"]["ontology_absent"] is True, "ontology fields are absent")
    v.check("BOUNDARY-FALLBACK", "boundaries", load_json(ROOT / "registries/PROJECT_REGISTRY.json")["fallback_unlocked"] is False, "Temporal-IAPS remains locked")


def check_manifest(v: Validation) -> None:
    manifest_path = ROOT / "manifests/CST-TT-05_MANIFEST.json"
    sums_path = ROOT / "manifests/CST-TT-05_SHA256SUMS"
    if not manifest_path.is_file() or not sums_path.is_file():
        v.check("MANIFEST-PREFREEZE", "manifest", True, "phase manifest not required before finalization")
        return
    manifest = load_json(manifest_path)
    v.check("MANIFEST-PHASE", "manifest", manifest.get("phase") == PHASE, "manifest phase is current")
    rows = manifest.get("files", [])
    v.check("MANIFEST-COUNT", "manifest", manifest.get("file_count") == len(rows) and len(rows) >= 900, f"manifest lists {len(rows)} files")
    for index, row in enumerate(rows, 1):
        path = ROOT / row["path"]
        v.check(f"MANIFEST-FILE-{index:04d}", "manifest", path.is_file() and path.stat().st_size == row["bytes"] and sha256(path) == row["sha256"], f"manifest row {row['path']} verifies")
    lines = sums_path.read_text(encoding="utf-8").splitlines()
    v.check("MANIFEST-SUM-COUNT", "manifest", len(lines) == len(rows) + 2, "checksum ledger includes files and both manifests")
    for index, line in enumerate(lines, 1):
        digest, rel = line.split(maxsplit=1)
        path = ROOT / rel.strip().lstrip("*")
        v.check(f"MANIFEST-SUM-{index:04d}", "manifest", path.is_file() and sha256(path) == digest, f"checksum row {rel} verifies")


def write_report(v: Validation) -> None:
    counts = Counter(row.status for row in v.results)
    payload = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "status": "PASS" if not v.failures else "FAIL",
        "total": len(v.results),
        "passed": counts["PASS"],
        "failed": counts["FAIL"],
        "skipped": counts["SKIP"],
        "results": [row.__dict__ for row in v.results],
    }
    out_json = ROOT / "manifests/CST-TT-05_VALIDATION_RESULTS.json"
    out_md = ROOT / "manifests/CST-TT-05_VALIDATION_REPORT.md"
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    lines = [
        "# CST-TT-05 Validation Report",
        "",
        f"**Status:** {payload['status']}",
        f"**Total:** {payload['total']}",
        f"**Passed:** {payload['passed']}",
        f"**Failed:** {payload['failed']}",
        f"**Skipped:** {payload['skipped']}",
        "",
        "| Check | Category | Status | Detail |",
        "|---|---|---|---|",
    ]
    lines.extend(f"| {row.check_id} | {row.category} | {row.status} | {row.detail.replace('|', '/')} |" for row in v.results)
    out_md.write_text("\n".join(lines) + "\n", encoding="utf-8")
    (ROOT / "manifests/VALIDATION_RESULTS.json").write_text(out_json.read_text(encoding="utf-8"), encoding="utf-8")
    (ROOT / "manifests/VALIDATION_REPORT.md").write_text(out_md.read_text(encoding="utf-8"), encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--no-write", action="store_true")
    parser.add_argument("--require-clean", action="store_true")
    parser.add_argument("--require-tag", action="store_true")
    args = parser.parse_args()
    v = Validation()
    check_baseline(v, args.require_clean, args.require_tag)
    check_toolchain(v)
    check_python(v)
    check_provenance(v)
    check_schemas(v)
    check_aligned_packages(v)
    check_autonomy(v)
    check_fiach(v)
    check_registries(v)
    check_lean_static(v)
    check_claim_boundaries(v)
    check_manifest(v)
    counts = Counter(row.status for row in v.results)
    print(f"CST-TT-05 validation: {'PASS' if not v.failures else 'FAIL'} — {counts['PASS']} passed, {counts['FAIL']} failed, {counts['SKIP']} skipped ({len(v.results)} total)")
    if v.failures:
        for row in v.failures[:30]:
            print(f"FAIL {row.check_id}: {row.detail}", file=sys.stderr)
    if not args.no_write:
        write_report(v)
    return 1 if v.failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
