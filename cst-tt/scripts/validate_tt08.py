#!/usr/bin/env python3
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import py_compile
import re
import shutil
import subprocess
import sys
from collections import Counter
from dataclasses import asdict, dataclass
from pathlib import Path
from typing import Any, Callable

import networkx as nx
from jsonschema import Draft202012Validator

from tt08_data import ALLOWED_FINAL_STATUSES, REJECTED_CONSTRUCTIONS
from tt08_surfaces import FIXED_GENERATED_SURFACES, LEGACY_DRAFT_SURFACES, generated_paths

ROOT = Path(__file__).resolve().parents[1]
PHASE = "CST-TT-08"
PHASE_TAG = "CST-TT-08-v1"
BASE_TAG = "CST-TT-07A-v1"
BASE_COMMIT = "7ba9167d39e6751706a7ad7152911c61f77af6af"
EXPECTED_STATUSES = Counter({"conditional": 19, "checked finite countermodel": 12, "open": 8})
INHERITED_TAGS = {
    "CST-TT-00-v1": "65b3ab0f94564cee1d16ffb4513045319aaaf6ef",
    "CST-TT-01-v1": "488db50b20d6d9c67493de3e9fd758e6e9e205ce",
    "CST-TT-02-v1": "3abf5b2406f754b43823b68987c7ea409e737fd0",
    "CST-TT-03-v1": "63ea725a7b6ade8df58a94cf7aad2ad78440ce70",
    "CST-TT-04-v1": "1884214d1bae82442f37fc9e6b013e222da89b1b",
    "CST-TT-05-v1": "faaf3b714050ac6acc195d0fab0f49dae9f51a87",
    "CST-TT-06-v1": "6c8f510c67087a8db9dd1c4107008b3b7cfb0847",
    BASE_TAG: BASE_COMMIT,
}


@dataclass(frozen=True)
class Check:
    check_id: str
    category: str
    status: str
    detail: str


class Audit:
    def __init__(self) -> None:
        self.checks: list[Check] = []

    def add(self, check_id: str, category: str, condition: bool, detail: str) -> None:
        self.checks.append(Check(check_id, category, "PASS" if condition else "FAIL", detail))

    def skip(self, check_id: str, category: str, detail: str) -> None:
        self.checks.append(Check(check_id, category, "SKIP", detail))

    def guarded(self, check_id: str, category: str, detail: str, fn: Callable[[], bool]) -> None:
        try:
            self.add(check_id, category, bool(fn()), detail)
        except Exception as exc:  # pragma: no cover - failure reporting path
            self.add(check_id, category, False, f"{detail}: {type(exc).__name__}: {exc}")

    @property
    def failures(self) -> list[Check]:
        return [row for row in self.checks if row.status == "FAIL"]


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def read_json(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def semis(value: str) -> list[str]:
    return [item for item in value.split(";") if item]


def check_git(audit: Audit, require_clean: bool, require_tag: bool) -> None:
    audit.guarded("GIT-001", "git", "repository is a Git worktree", lambda: git("rev-parse", "--is-inside-work-tree") == "true")
    audit.guarded("GIT-002", "git", f"{BASE_TAG} resolves to frozen base", lambda: git("rev-parse", BASE_TAG + "^{}") == BASE_COMMIT)
    audit.guarded(
        "GIT-003",
        "git",
        "frozen base is an ancestor of HEAD",
        lambda: subprocess.run(["git", "merge-base", "--is-ancestor", BASE_COMMIT, "HEAD"], cwd=ROOT).returncode == 0,
    )
    audit.guarded("GIT-004", "git", "no whitespace errors", lambda: subprocess.run(["git", "diff", "--check"], cwd=ROOT, capture_output=True).returncode == 0)
    audit.guarded("GIT-005", "git", "Git object database passes fsck", lambda: subprocess.run(["git", "fsck", "--full", "--no-dangling"], cwd=ROOT, capture_output=True).returncode == 0)
    for index, (tag, commit) in enumerate(INHERITED_TAGS.items(), 1):
        audit.guarded(f"GIT-HIST-{index:02d}", "git", f"{tag} resolves to {commit}", lambda t=tag, c=commit: git("rev-parse", t + "^{}") == c)
    tags = set(git("tag", "--list").splitlines())
    if require_tag:
        audit.add("GIT-TAG-001", "git", PHASE_TAG in tags, f"{PHASE_TAG} exists")
        if PHASE_TAG in tags:
            audit.add("GIT-TAG-002", "git", git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD"), "phase tag resolves to HEAD")
    else:
        valid = PHASE_TAG not in tags or git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD")
        audit.add("GIT-TAG-001", "git", valid, "phase tag absent before freeze or already points at HEAD")
    if require_clean:
        audit.guarded("GIT-CLEAN", "git", "working tree is clean", lambda: git("status", "--porcelain") == "")
    else:
        audit.add("GIT-CLEAN", "git", True, "clean-tree gate deferred until release replay")


def check_toolchain(audit: Audit) -> None:
    audit.add("TOOL-001", "toolchain", (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.28.0", "Lean toolchain is pinned")
    audit.add("TOOL-002", "toolchain", sys.version_info[:2] == (3, 13), f"Python 3.13 is active ({sys.version.split()[0]})")
    pyproject = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    lock = (ROOT / "requirements-lock.txt").read_text(encoding="utf-8")
    audit.add("TOOL-003", "toolchain", 'networkx==3.6.1' in pyproject and "networkx==3.6.1" in lock, "networkx dependency is pinned")
    audit.add("TOOL-004", "toolchain", 'jsonschema==4.26.0' in pyproject and "jsonschema==4.26.0" in lock, "jsonschema dependency is pinned")
    status = read_json(ROOT / "formal/TOOLCHAIN_STATUS.json")
    audit.add("TOOL-005", "toolchain", status.get("phase") == PHASE, "toolchain report is phase-current")
    audit.add("TOOL-006", "toolchain", status.get("lean_compile_status") in {"not-run-toolchain-unavailable", "passed"}, "Lean status is explicit")
    lean, lake = shutil.which("lean"), shutil.which("lake")
    if lean and lake:
        proc = subprocess.run([lake, "build"], cwd=ROOT, text=True, capture_output=True, timeout=1200)
        detail = "pinned Lean sources compile under lake build"
        if proc.returncode != 0:
            detail += ": " + (proc.stdout + proc.stderr)[-5000:].replace("\n", " ")
        audit.add("TOOL-LEAN-BUILD", "toolchain", proc.returncode == 0, detail)
    else:
        audit.skip("TOOL-LEAN-BUILD", "toolchain", "lean/lake unavailable; no kernel pass and no promotion to proved")


def check_generated_surfaces(audit: Audit) -> None:
    for index, rel in enumerate(FIXED_GENERATED_SURFACES, 1):
        audit.add(f"SURFACE-{index:03d}", "generated", (ROOT / rel).is_file(), f"authoritative generated surface exists: {rel}")
    for index, rel in enumerate(LEGACY_DRAFT_SURFACES, 1):
        audit.add(f"NO-LEGACY-{index:03d}", "generated", not (ROOT / rel).exists(), f"contradictory draft surface absent: {rel}")
    archive_files = sorted(path for path in (ROOT / "archive/rejected").rglob("*") if path.is_file())
    audit.add("SURFACE-ARCHIVE-COUNT", "generated", len(archive_files) == 16, f"rejected archive has 16 deterministic files ({len(archive_files)})")


def check_python(audit: Audit) -> None:
    python_files = sorted([*(ROOT / "src").rglob("*.py"), *(ROOT / "scripts").glob("*.py"), *(ROOT / "tests").glob("*.py")])
    audit.add("PY-COUNT", "python", len(python_files) >= 85, f"Python source/test bank contains {len(python_files)} files")
    for index, path in enumerate(python_files, 1):
        audit.guarded(f"PY-COMPILE-{index:03d}", "python", f"{path.relative_to(ROOT)} compiles", lambda p=path: py_compile.compile(str(p), doraise=True) is not None)
    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "-q"],
        cwd=ROOT,
        env={**os.environ, "PYTHONPATH": "src:scripts", "PYTHONHASHSEED": "0"},
        text=True,
        capture_output=True,
        timeout=1800,
    )
    detail = "full Python test suite passes"
    if proc.returncode != 0:
        detail += ": " + (proc.stdout + proc.stderr)[-7000:].replace("\n", " ")
    audit.add("PY-TEST", "python", proc.returncode == 0, detail)


def check_json_and_schemas(audit: Audit) -> None:
    json_paths = sorted(
        set(
            [
                *(ROOT / "models").rglob("*.json"),
                *(ROOT / "formal/certificates").rglob("*.json"),
                *(ROOT / "schemas").rglob("*.json"),
                *(ROOT / "registries").glob("*.json"),
                *(ROOT / "manifests").glob("*.json"),
                *(ROOT / "archive/rejected").glob("*.json"),
            ]
        )
    )
    audit.add("JSON-COUNT", "json", len(json_paths) >= 535, f"JSON bank contains {len(json_paths)} files")
    for index, path in enumerate(json_paths, 1):
        audit.guarded(f"JSON-{index:04d}", "json", f"{path.relative_to(ROOT)} parses", lambda p=path: isinstance(read_json(p), (dict, list)))
    schemas = sorted((ROOT / "schemas/certificates").glob("*.schema.json"))
    examples = sorted((ROOT / "examples/scaffold").glob("*.scaffold.json"))
    audit.add("SCHEMA-COUNT", "schema", len(schemas) == 35, f"35 certificate schemas remain ({len(schemas)})")
    audit.add("EXAMPLE-COUNT", "schema", len(examples) == 35, f"35 scaffold examples remain ({len(examples)})")
    by_stem = {path.name.replace(".scaffold.json", ""): path for path in examples}
    for index, schema_path in enumerate(schemas, 1):
        schema = read_json(schema_path)
        audit.guarded(f"SCHEMA-VALID-{index:03d}", "schema", f"{schema_path.name} is a valid Draft 2020-12 schema", lambda s=schema: Draft202012Validator.check_schema(s) is None)
        stem = schema_path.name.replace(".schema.json", "")
        example = by_stem.get(stem)
        audit.add(f"SCHEMA-PAIR-{index:03d}", "schema", example is not None, f"{stem} has a scaffold example")
        if example is not None:
            errors = list(Draft202012Validator(schema).iter_errors(read_json(example)))
            audit.add(f"SCHEMA-EXAMPLE-{index:03d}", "schema", not errors, f"{example.name} validates against {schema_path.name}")


def check_theorem_bank(audit: Audit) -> None:
    final_rows = read_csv(ROOT / "registries/FINAL_THEOREM_STATUS.csv")
    source_rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    final_by_id = {row["theorem_id"]: row for row in final_rows}
    theorem_ids = {row["theorem_id"] for row in source_rows}
    toy_ids = {row["toy_id"] for row in read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")}
    assumption_ids = {row["assumption_id"] for row in read_csv(ROOT / "registries/ASSUMPTION_LEDGER.csv")}
    evidence_paths = {row["path"] for row in read_csv(ROOT / "registries/FINAL_CERTIFICATE_INDEX.csv")}

    audit.add("THEOREM-COUNT", "theorem", len(final_rows) == len(source_rows) == 39, "all 39 theorem/boundary contracts are finalized")
    audit.add("THEOREM-ID-SET", "theorem", set(final_by_id) == theorem_ids, "final and source theorem ID sets agree")
    audit.add("THEOREM-STATUS-SET", "theorem", {row["final_status"] for row in final_rows} <= ALLOWED_FINAL_STATUSES, "only frozen status vocabulary is used")
    audit.add("THEOREM-STATUS-COUNTS", "theorem", Counter(row["final_status"] for row in final_rows) == EXPECTED_STATUSES, f"status split is {dict(EXPECTED_STATUSES)}")
    audit.add("THEOREM-NO-PROVED", "theorem", all(row["final_status"] != "proved" for row in final_rows), "no result is overpromoted without Lean")
    audit.add("THEOREM-TTN05", "theorem", final_by_id["TTN-05"]["final_status"] == "conditional", "clock-translation holonomy retains its generic proof-source status with an exact finite witness")

    for index, row in enumerate(final_rows, 1):
        prefix = f"THEOREM-{index:03d}"
        theorem_id = row["theorem_id"]
        audit.add(prefix + "-STATEMENT", "theorem", bool(row["exact_statement"].strip()), f"{theorem_id} has an exact statement")
        audit.add(prefix + "-DECL", "theorem", row["declarations_found"] == "true" and row["missing_declarations"] == "", f"{theorem_id} declarations are located")
        audit.add(prefix + "-PLACEHOLDER", "theorem", row["placeholder_free_repository"] == "true", f"{theorem_id} reports placeholder-free Lean source")
        refs = semis(row["declaration_refs"])
        audit.add(prefix + "-DECL-REFS", "theorem", len(refs) == len(set(refs)) and bool(refs), f"{theorem_id} declaration references are nonempty and unique")
        for subindex, ref in enumerate(refs, 1):
            path_text, line_text = ref.rsplit(":", 1)
            path = ROOT / path_text
            valid = path.is_file() and line_text.isdigit() and 1 <= int(line_text) <= len(path.read_text(encoding="utf-8").splitlines())
            audit.add(f"{prefix}-DECL-REF-{subindex:02d}", "theorem", valid, f"{theorem_id} declaration reference resolves: {ref}")
        deps = semis(row["dependencies"])
        toys = semis(row["toy_dependencies"])
        assumptions = semis(row["assumption_ids"])
        audit.add(prefix + "-DEPS", "theorem", set(deps) <= theorem_ids, f"{theorem_id} theorem dependencies resolve")
        audit.add(prefix + "-TOYS", "theorem", set(toys) <= toy_ids, f"{theorem_id} toy dependencies resolve")
        audit.add(prefix + "-ASSUMPTIONS", "theorem", set(assumptions) <= assumption_ids, f"{theorem_id} assumptions resolve")
        evidence = semis(row["evidence_refs"])
        audit.add(prefix + "-EVIDENCE-COUNT", "theorem", int(row["evidence_count"]) == len(set(evidence)), f"{theorem_id} evidence count matches unique references")
        audit.add(prefix + "-EVIDENCE-RESOLVE", "theorem", set(evidence) <= evidence_paths, f"{theorem_id} evidence references resolve")
        if row["final_status"] == "open":
            audit.add(prefix + "-OPEN", "theorem", not evidence and "CST-TT-07B" in row["promotion_condition"], f"{theorem_id} remains an evidence-free locked fallback prospect")
        else:
            audit.add(prefix + "-LANDED", "theorem", bool(evidence), f"{theorem_id} has exact finite evidence")
        if row["final_status"] == "conditional":
            audit.add(prefix + "-CONDITIONAL", "theorem", "lake build" in row["promotion_condition"], f"{theorem_id} has an explicit kernel promotion gate")
        if row["final_status"] == "checked finite countermodel":
            audit.add(prefix + "-COUNTERMODEL", "theorem", "countermodel" in row["status_basis"].lower(), f"{theorem_id} records finite-countermodel scope")
        audit.add(prefix + "-CEILING", "theorem", bool(row["claim_ceiling"]), f"{theorem_id} has an explicit claim ceiling")

    payload = read_json(ROOT / "registries/FINAL_THEOREM_STATUS.json")
    audit.add("THEOREM-JSON-PHASE", "theorem", payload.get("phase") == PHASE, "theorem JSON is phase-current")
    audit.add("THEOREM-JSON-COUNT", "theorem", len(payload.get("rows", [])) == 39, "theorem JSON contains 39 rows")
    audit.add("THEOREM-JSON-STATUS", "theorem", Counter(payload.get("status_counts", {})) == Counter(EXPECTED_STATUSES), "theorem JSON status counts agree")
    audit.add("LEAN-PLACEHOLDER-FREE", "theorem", payload.get("lean_placeholder_free") is True, "global Lean placeholder audit passes")
    audit.add("LEAN-DECL-COUNT", "theorem", int(payload.get("lean_declaration_count", 0)) >= 300, f"Lean declaration index contains {payload.get('lean_declaration_count')} declarations")


def check_models_certificates_and_toys(audit: Audit) -> None:
    model_rows = read_csv(ROOT / "registries/FINAL_MODEL_INDEX.csv")
    cert_rows = read_csv(ROOT / "registries/FINAL_CERTIFICATE_INDEX.csv")
    toy_rows = read_csv(ROOT / "registries/FINAL_TOY_CATALOG.csv")
    actual_models = {path.relative_to(ROOT).as_posix() for path in (ROOT / "models").rglob("*.json")}
    actual_certs = {path.relative_to(ROOT).as_posix() for path in (ROOT / "formal/certificates").rglob("*.json")}
    audit.add("MODEL-COUNT", "evidence", len(model_rows) == len(actual_models) == 203, "203 model JSON files are indexed")
    audit.add("MODEL-PATH-SET", "evidence", {row["path"] for row in model_rows} == actual_models, "model index path set is complete")
    audit.add("CERT-COUNT", "evidence", len(cert_rows) == len(actual_certs) == 233, "233 certificate/search JSON files are indexed")
    audit.add("CERT-PATH-SET", "evidence", {row["path"] for row in cert_rows} == actual_certs, "certificate index path set is complete")
    for index, row in enumerate(model_rows, 1):
        path = ROOT / row["path"]
        audit.add(f"MODEL-{index:04d}", "evidence", path.is_file() and sha256(path) == row["sha256"] and path.stat().st_size == int(row["bytes"]), f"model is hash/size bound: {row['path']}")
        linked = semis(row["linked_certificates"])
        audit.add(f"MODEL-LINK-{index:04d}", "evidence", len(linked) == int(row["linked_certificate_count"]) and set(linked) <= actual_certs, f"model certificate links resolve: {row['model_id']}")
    for index, row in enumerate(cert_rows, 1):
        path = ROOT / row["path"]
        audit.add(f"CERT-{index:04d}", "evidence", path.is_file() and sha256(path) == row["sha256"] and path.stat().st_size == int(row["bytes"]), f"evidence is hash/size bound: {row['path']}")
        if row["model_ref"]:
            audit.add(f"CERT-MODEL-{index:04d}", "evidence", row["model_ref"] in actual_models and row["model_hash_valid"] == "true", f"evidence model reference resolves: {row['evidence_id']}")
    source_toys = {row["toy_id"] for row in read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")}
    audit.add("TOY-COUNT", "evidence", len(toy_rows) == 28, "28 canonical toy contracts are finalized")
    audit.add("TOY-ID-SET", "evidence", {row["toy_id"] for row in toy_rows} == source_toys, "final and source toy ID sets agree")
    for index, row in enumerate(toy_rows, 1):
        refs = semis(row["canonical_model_refs"]) + semis(row["canonical_certificate_refs"])
        audit.add(f"TOY-{index:03d}", "evidence", all((ROOT / ref).is_file() for ref in refs), f"toy references resolve: {row['toy_id']}")
        bound = row["minimality_or_bound_ref"]
        if bound and ("/" in bound or bound.endswith((".json", ".csv", ".md"))):
            audit.add(f"TOY-BOUND-{index:03d}", "evidence", (ROOT / bound).is_file(), f"toy bound/minimality reference resolves: {row['toy_id']}")


def check_dependency_and_claim_boundaries(audit: Audit) -> None:
    dag = read_json(ROOT / "registries/FINAL_DEPENDENCY_DAG.json")
    nodes = read_csv(ROOT / "registries/FINAL_DEPENDENCY_NODES.csv")
    edges = read_csv(ROOT / "registries/FINAL_DEPENDENCY_EDGES.csv")
    node_ids = {row["node_id"] for row in nodes}
    graph = nx.DiGraph()
    graph.add_nodes_from(node_ids)
    graph.add_edges_from((row["source"], row["target"]) for row in edges)
    audit.add("DAG-COUNT-N", "dependency", dag.get("node_count") == len(nodes) == len(dag.get("nodes", [])) == 174, "DAG has 174 nodes")
    audit.add("DAG-COUNT-E", "dependency", dag.get("edge_count") == len(edges) == len(dag.get("edges", [])) == 288, "DAG has 288 edges")
    audit.add("DAG-ENDPOINTS", "dependency", all(row["source"] in node_ids and row["target"] in node_ids for row in edges), "all DAG edge endpoints resolve")
    audit.add("DAG-ACYCLIC", "dependency", dag.get("acyclic") is True and nx.is_directed_acyclic_graph(graph), "dependency graph is acyclic")
    audit.add("DAG-ORDER", "dependency", set(dag.get("topological_order", [])) == node_ids and len(dag.get("topological_order", [])) == len(node_ids), "topological order covers every node exactly once")
    audit.add("DAG-DOT", "dependency", (ROOT / "handoff/FINAL_DEPENDENCY_DAG.dot").is_file(), "Graphviz source exists")
    audit.add("DAG-SVG", "dependency", (ROOT / "handoff/FINAL_DEPENDENCY_DAG.svg").is_file(), "dependency SVG exists")

    theorem_ids = {row["theorem_id"] for row in read_csv(ROOT / "registries/FINAL_THEOREM_STATUS.csv")}
    assumption_ids = {row["assumption_id"] for row in read_csv(ROOT / "registries/ASSUMPTION_LEDGER.csv")}
    ledger = read_csv(ROOT / "registries/FINAL_CLAIM_ASSUMPTION_NONCLAIM_LEDGER.csv")
    audit.add("CLAIM-COUNT", "claim", len(ledger) == 10, "ten independent claim areas are frozen")
    audit.add("CLAIM-STATUS", "claim", Counter(row["status"] for row in ledger) == Counter({"conditional": 7, "open": 3}), "claim-area status split is frozen")
    for index, row in enumerate(ledger, 1):
        audit.add(f"CLAIM-THEOREMS-{index:02d}", "claim", set(semis(row["theorem_ids"])) <= theorem_ids, f"claim-area theorem references resolve: {row['claim_area']}")
        audit.add(f"CLAIM-ASSUMPTIONS-{index:02d}", "claim", set(semis(row["assumption_ids"])) <= assumption_ids, f"claim-area assumptions resolve: {row['claim_area']}")
        audit.add(f"CLAIM-BOUNDARY-{index:02d}", "claim", bool(row["permitted_claim"] and row["nonclaim"] and row["bridge_needed"]), f"claim area has claim, nonclaim, and bridge fields: {row['claim_area']}")
    claim_text = "\n".join(" ".join((row["permitted_claim"], row["nonclaim"], row["bridge_needed"])).lower() for row in ledger)
    for index, token in enumerate(("consciousness", "phenomenal continuity", "personal survival", "numerical identity", "empirical recognition", "a2-p", "certificate soundness", "physical resource"), 1):
        audit.add(f"CLAIM-CEILING-{index:02d}", "claim", token in claim_text, f"claim ceiling explicitly addresses {token}")


def check_provenance_and_rejections(audit: Audit) -> None:
    provenance = read_csv(ROOT / "registries/FINAL_SBT_PROVENANCE.csv")
    audit.add("PROV-COUNT", "provenance", len(provenance) == 19, "19 statement-level SBT imports are frozen")
    audit.add("PROV-UNIQUE", "provenance", len({row["statement_id"] for row in provenance}) == 19, "SBT statement IDs are unique")
    source_root = ROOT / "inputs/reference_surfaces"
    for index, row in enumerate(provenance, 1):
        matches = list(source_root.rglob(row["source_file"]))
        valid_file = len(matches) == 1
        audit.add(f"PROV-FILE-{index:03d}", "provenance", valid_file, f"source resolves uniquely: {row['source_file']}")
        valid_lines = False
        if valid_file:
            line_count = len(matches[0].read_text(encoding="utf-8").splitlines())
            spans = re.findall(r"(\d+)(?:-(\d+))?", row["source_lines"])
            valid_lines = bool(spans) and all(1 <= int(start) <= int(end or start) <= line_count for start, end in spans)
        audit.add(f"PROV-LINES-{index:03d}", "provenance", valid_lines, f"source line spans resolve: {row['statement_id']}")
        audit.add(f"PROV-SCOPE-{index:03d}", "provenance", bool(row["scope_note"] and row["provenance_role"]), f"scope and role are explicit: {row['statement_id']}")

    rows = read_csv(ROOT / "archive/rejected/REJECTED_CONSTRUCTIONS.csv")
    audit.add("REJECT-COUNT", "rejected", len(rows) == len(REJECTED_CONSTRUCTIONS) == 12, "twelve failed/inactive constructions are preserved")
    audit.add("REJECT-STATUS", "rejected", Counter(row["status"] for row in rows) == Counter({"killed": 11, "open": 1}), "rejected archive has eleven killed and one open fallback")
    audit.add("REJECT-DATA", "rejected", rows == [{key: str(value) for key, value in row.items()} for row in REJECTED_CONSTRUCTIONS], "archive CSV matches declarative frozen data")
    aggregate = read_json(ROOT / "archive/rejected/REJECTED_CONSTRUCTIONS.json")
    audit.add("REJECT-JSON", "rejected", aggregate.get("phase") == PHASE and aggregate.get("rows") == REJECTED_CONSTRUCTIONS, "aggregate rejected JSON matches frozen data")
    for index, row in enumerate(rows, 1):
        path = ROOT / "archive/rejected" / f"{row['rejected_id']}.json"
        data = read_json(path) if path.is_file() else {}
        audit.add(f"REJECT-{index:02d}", "rejected", data.get("rejected_id") == row["rejected_id"] and data.get("phase") == PHASE, f"individual rejected record is preserved: {row['rejected_id']}")


def check_project_and_handoff(audit: Audit) -> None:
    project = read_json(ROOT / "registries/PROJECT_REGISTRY.json")
    summary = read_json(ROOT / "manifests/CST-TT-08_PHASE_SUMMARY.json")
    generic_summary = read_json(ROOT / "manifests/PHASE_SUMMARY.json")
    audit.add("PROJECT-PHASE", "project", project.get("phase") == project.get("current_phase") == PHASE, "project registry is phase-current")
    audit.add("PROJECT-CLOSED", "project", project.get("science_program_closed") is True and project.get("next_phase") == "none-science-program-closed", "science program is explicitly closed")
    audit.add("PROJECT-BRANCH", "project", project.get("final_branch_outcome") == "preferred-Temporal-FIACH-plus-no-go-kernel", "preferred branch is frozen")
    audit.add("PROJECT-FALLBACK", "project", project.get("fallback_unlocked") is False and "unauthorized" in project.get("fallback_status", ""), "Temporal-IAPS fallback remains locked")
    audit.add("PROJECT-COUNTS", "project", Counter(project.get("final_theorem_status_counts", {})) == EXPECTED_STATUSES, "project theorem counts match normative status table")
    audit.add("SUMMARY-EQUAL", "project", summary == generic_summary, "phase-specific and canonical summaries agree")
    audit.add("SUMMARY-PHASE", "project", summary.get("phase") == PHASE and summary.get("base_tag") == BASE_TAG and summary.get("base_commit") == BASE_COMMIT, "phase summary provenance is exact")
    audit.add("SUMMARY-COUNTS", "project", Counter(summary.get("theorem_status_counts", {})) == EXPECTED_STATUSES, "phase summary theorem counts agree")
    audit.add("SUMMARY-EVIDENCE", "project", summary.get("model_index_count") == 203 and summary.get("certificate_and_search_index_count") == 233 and summary.get("toy_contract_count") == 28, "phase summary evidence counts agree")
    audit.add("SUMMARY-DAG", "project", summary.get("dependency_dag") == {"nodes": 174, "edges": 288, "acyclic": True}, "phase summary DAG counts agree")
    matrix = read_csv(ROOT / "registries/FINAL_REBUILD_MATRIX.csv")
    audit.add("REBUILD-MATRIX", "project", len(matrix) == 8 and all(row["status"] == "PASS" for row in matrix), "all eight inherited phase rebuild reports remain PASS")
    handoff = (ROOT / "handoff/CST-TT-08_SCIENCE_HANDOFF.md").read_text(encoding="utf-8")
    for index, phrase in enumerate((
        "Temporal-FIACH plus the mandatory no-go kernel",
        "Temporal-IAPS was not activated",
        "integrated finite C1-C8-shaped target package",
        "composition-stable chain of live overlap handoffs",
        "no theorem is marked `proved`",
        "route-indexed",
        "relation-valued",
        "does **not** establish consciousness",
        "First external formal action",
    ), 1):
        audit.add(f"HANDOFF-{index:02d}", "project", phrase in handoff, f"science handoff contains: {phrase}")


def verify_manifest(audit: Audit) -> None:
    phase_path = ROOT / "manifests/CST-TT-08_MANIFEST.json"
    generic_path = ROOT / "manifests/MANIFEST.json"
    audit.add("MANIFEST-EXISTS", "manifest", phase_path.is_file() and generic_path.is_file(), "phase and canonical manifests exist")
    if not phase_path.is_file() or not generic_path.is_file():
        return
    phase = read_json(phase_path)
    generic = read_json(generic_path)
    audit.add("MANIFEST-EQUAL", "manifest", phase == generic, "phase and canonical manifests are identical")
    audit.add("MANIFEST-PHASE", "manifest", phase.get("phase") == PHASE, "manifest is phase-current")
    files = phase.get("files", [])
    audit.add("MANIFEST-COUNT", "manifest", phase.get("file_count") == len(files), "manifest file count agrees")
    for index, row in enumerate(files, 1):
        path = ROOT / row["path"]
        audit.add(f"MANIFEST-{index:04d}", "manifest", path.is_file() and path.stat().st_size == int(row["bytes"]) and sha256(path) == row["sha256"], f"manifest entry verifies: {row['path']}")
    for name in ("CST-TT-08_SHA256SUMS", "SHA256SUMS"):
        path = ROOT / "manifests" / name
        audit.add(f"SUMS-{name}-EXISTS", "manifest", path.is_file(), f"{name} exists")
        if path.is_file():
            lines = [line for line in path.read_text(encoding="utf-8").splitlines() if line]
            all_valid = True
            for line in lines:
                digest, rel = line.split(maxsplit=1)
                rel = rel.strip().lstrip("*")
                target = ROOT / rel
                if not target.is_file() or sha256(target) != digest:
                    all_valid = False
                    break
            audit.add(f"SUMS-{name}-VALID", "manifest", all_valid, f"all {len(lines)} rows in {name} verify")


def render_report(audit: Audit) -> tuple[dict[str, Any], str]:
    counts = Counter(row.status for row in audit.checks)
    payload = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "status": "PASS" if not audit.failures else "FAIL",
        "counts": dict(counts),
        "total": len(audit.checks),
        "checks": [asdict(row) for row in audit.checks],
    }
    lines = [
        "# CST-TT-08 Validation Report",
        "",
        f"**Status:** {payload['status']}",
        f"**Total checks:** {len(audit.checks)}",
        f"**Passed:** {counts.get('PASS', 0)}",
        f"**Failed:** {counts.get('FAIL', 0)}",
        f"**Skipped:** {counts.get('SKIP', 0)}",
        "",
        "The sole expected skip in an environment without `lean` and `lake` is the actual Lean-kernel build. A skip is not counted as a pass and no theorem is promoted to `proved` on that basis.",
        "",
        "## Category summary",
        "",
        "| Category | Pass | Fail | Skip |",
        "|---|---:|---:|---:|",
    ]
    categories = sorted({row.category for row in audit.checks})
    for category in categories:
        counter = Counter(row.status for row in audit.checks if row.category == category)
        lines.append(f"| {category} | {counter.get('PASS', 0)} | {counter.get('FAIL', 0)} | {counter.get('SKIP', 0)} |")
    if audit.failures:
        lines.extend(["", "## Failures", ""])
        lines.extend(f"- `{row.check_id}` ({row.category}): {row.detail}" for row in audit.failures)
    return payload, "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--no-write", action="store_true", help="do not write validation reports")
    parser.add_argument("--require-clean", action="store_true")
    parser.add_argument("--require-tag", action="store_true")
    parser.add_argument("--require-manifest", action="store_true")
    args = parser.parse_args()

    audit = Audit()
    check_git(audit, args.require_clean, args.require_tag)
    check_toolchain(audit)
    check_generated_surfaces(audit)
    check_python(audit)
    check_json_and_schemas(audit)
    check_theorem_bank(audit)
    check_models_certificates_and_toys(audit)
    check_dependency_and_claim_boundaries(audit)
    check_provenance_and_rejections(audit)
    check_project_and_handoff(audit)
    if args.require_manifest:
        verify_manifest(audit)

    payload, report = render_report(audit)
    if not args.no_write:
        manifest_dir = ROOT / "manifests"
        manifest_dir.mkdir(parents=True, exist_ok=True)
        text = json.dumps(payload, indent=2, sort_keys=True) + "\n"
        (manifest_dir / "CST-TT-08_VALIDATION_RESULTS.json").write_text(text, encoding="utf-8")
        (manifest_dir / "CST-TT-08_VALIDATION_REPORT.md").write_text(report, encoding="utf-8")
        (manifest_dir / "VALIDATION_RESULTS.json").write_text(text, encoding="utf-8")
        (manifest_dir / "VALIDATION_REPORT.md").write_text(report, encoding="utf-8")

    counts = Counter(row.status for row in audit.checks)
    print(f"CST-TT-08 validation: {payload['status']} ({counts.get('PASS', 0)} passed, {counts.get('FAIL', 0)} failed, {counts.get('SKIP', 0)} skipped; {len(audit.checks)} total)")
    if audit.failures:
        for row in audit.failures[:30]:
            print(f"FAIL {row.check_id}: {row.detail}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
