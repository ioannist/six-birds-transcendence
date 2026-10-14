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
from dataclasses import dataclass
from pathlib import Path
from typing import Any, Callable, Mapping

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from cst_tt.branching import (  # noqa: E402
    audit_fusion_boundary,
    audit_temporal_fission,
    bounded_fission_symmetry_search,
    bounded_fusion_boundary_search,
)
from cst_tt.handoff_composition import (  # noqa: E402
    audit_full_handoff_composition,
    audit_route_completion,
    audit_staged_composition,
    bounded_full_handoff_interface_search,
    bounded_route_completion_search,
)
from cst_tt.registry import duplicate_values, read_csv  # noqa: E402
from cst_tt.toy_suite import audit_toy_suite, hidden_equivalence_search  # noqa: E402

PHASE = "CST-TT-06"
BASE_TAG = "CST-TT-05-v1"
BASE_COMMIT = "faaf3b714050ac6acc195d0fab0f49dae9f51a87"
PHASE_TAG = "CST-TT-06-v1"


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
        except Exception as exc:  # pragma: no cover - reported as a failed validation
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


def check_baseline(v: Validation, require_clean: bool, require_tag: bool) -> None:
    v.guarded("BASE-001", "baseline", "repository is a Git worktree", lambda: git("rev-parse", "--is-inside-work-tree") == "true")
    v.guarded("BASE-002", "baseline", f"{BASE_TAG} resolves to its frozen commit", lambda: git("rev-parse", BASE_TAG + "^{}") == BASE_COMMIT)
    v.guarded("BASE-003", "baseline", "frozen base is an ancestor of HEAD", lambda: subprocess.run(["git", "merge-base", "--is-ancestor", BASE_COMMIT, "HEAD"], cwd=ROOT).returncode == 0)
    v.guarded("BASE-004", "baseline", "repository has no whitespace errors", lambda: subprocess.run(["git", "diff", "--check"], cwd=ROOT, capture_output=True).returncode == 0)
    if require_clean:
        v.guarded("BASE-005", "baseline", "working tree is clean", lambda: git("status", "--porcelain") == "")
    else:
        v.check("BASE-005", "baseline", True, "clean-tree gate deferred until release verification")
    tags = set(git("tag", "--list").splitlines())
    if require_tag:
        v.check("BASE-006", "baseline", PHASE_TAG in tags, f"phase tag {PHASE_TAG} exists")
        if PHASE_TAG in tags:
            v.check("BASE-007", "baseline", git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD"), "phase tag resolves to HEAD")
    else:
        valid = PHASE_TAG not in tags or git("rev-parse", PHASE_TAG + "^{}") == git("rev-parse", "HEAD")
        v.check("BASE-006", "baseline", valid, "phase tag is absent before freeze or already resolves to HEAD")


def check_toolchain(v: Validation) -> None:
    v.check("TOOL-001", "toolchain", (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.28.0", "Lean toolchain remains pinned")
    pyproject = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    for index, token in enumerate((">=3.13,<3.14", "pytest==9.0.2", "jsonschema==4.26.0", "setuptools==82.0.1"), 1):
        v.check(f"TOOL-PIN-{index:02d}", "toolchain", token in pyproject, f"pyproject contains {token}")
    v.check("TOOL-PY", "toolchain", sys.version_info[:2] == (3, 13), f"Python 3.13 is running ({sys.version.split()[0]})")
    status = load_json(ROOT / "formal/TOOLCHAIN_STATUS.json")
    v.check("TOOL-STATUS-PHASE", "toolchain", status.get("phase") == PHASE, "toolchain status is phase-current")
    v.check("TOOL-STATUS-LEAN", "toolchain", status.get("lean_compile_status") == "pending-toolchain", "Lean compile status is not overclaimed")
    v.check("TOOL-STATUS-PY", "toolchain", status.get("python_certificate_status") == "checked", "Python certificate status is checked")
    lean, lake = shutil.which("lean"), shutil.which("lake")
    if lean and lake:
        proc = subprocess.run([lake, "build"], cwd=ROOT, text=True, capture_output=True, timeout=600)
        v.check("TOOL-LEAN-BUILD", "toolchain", proc.returncode == 0, "pinned Lean sources compile with lake build")
    else:
        v.skip("TOOL-LEAN-BUILD", "toolchain", "lean/lake unavailable; no Lean-kernel compilation pass is claimed")


def check_python(v: Validation) -> None:
    files = sorted([*SRC.rglob("*.py"), *(ROOT / "scripts").glob("*.py"), *(ROOT / "tests").glob("*.py")])
    v.check("PY-COUNT", "python", len(files) >= 70, f"at least seventy Python files are present ({len(files)})")
    for index, path in enumerate(files, 1):
        v.guarded(f"PY-COMPILE-{index:03d}", "python", f"{path.relative_to(ROOT)} compiles", lambda p=path: py_compile.compile(str(p), doraise=True) is not None)
    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "-q"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=600,
        env={**os.environ, "PYTHONPATH": "src:scripts", "PYTHONHASHSEED": "0"},
    )
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
        "CST-TT-04-v1": "1884214d1bae82442f37fc9e6b013e222da89b1b",
        BASE_TAG: BASE_COMMIT,
    }
    for index, (tag, commit) in enumerate(inherited.items(), 1):
        v.guarded(f"PROV-TAG-{index:02d}", "provenance", f"{tag} resolves to its frozen commit", lambda t=tag, c=commit: git("rev-parse", t + "^{}") == c)
    checksum_file = ROOT / "inputs/normative/cst-tt-00/IMPORTED_SHA256SUMS.txt"
    for index, line in enumerate(checksum_file.read_text(encoding="utf-8").splitlines(), 1):
        digest, rel = line.split(maxsplit=1)
        path = ROOT / rel.lstrip("*")
        v.check(f"PROV-INPUT-{index:03d}", "provenance", path.is_file() and sha256(path) == digest, f"imported surface {rel} is hash-bound")
    v.check("PROV-SOURCES", "provenance", len(list((ROOT / "inputs/reference_surfaces/temporal_audit").glob("*.tex"))) == 9, "nine temporal SBT manuscripts remain present")


def check_json_tree(v: Validation) -> None:
    roots = [ROOT / "models", ROOT / "formal/certificates", ROOT / "schemas", ROOT / "examples/scaffold", ROOT / "registries"]
    paths: list[Path] = []
    for root in roots:
        paths.extend(root.rglob("*.json"))
    paths = sorted(set(paths))
    v.check("JSON-COUNT", "json", len(paths) >= 350, f"at least 350 JSON surfaces are present ({len(paths)})")
    for index, path in enumerate(paths, 1):
        v.guarded(f"JSON-PARSE-{index:04d}", "json", f"{path.relative_to(ROOT)} parses", lambda p=path: isinstance(load_json(p), (dict, list)))


def check_schemas(v: Validation) -> None:
    schemas = sorted((ROOT / "schemas/certificates").glob("*.schema.json"))
    examples = sorted((ROOT / "examples/scaffold").glob("*.json"))
    registry = read_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv")
    v.check("SCHEMA-COUNT", "schemas", len(schemas) == 31, "thirty-one certificate schemas are present")
    v.check("EXAMPLE-COUNT", "schemas", len(examples) == 31, "thirty-one scaffold examples are present")
    v.check("SCHEMA-REGISTRY-COUNT", "schemas", len(registry) == 31, "schema registry has thirty-one rows")
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
    landed_pairs = {
        "full_handoff_composition_certificate.schema.json": "formal/certificates/composition/FIACH-COMP-01.certificate.json",
        "temporal_fission_certificate.schema.json": "formal/certificates/fission/FISSION-POS-01.certificate.json",
        "fusion_boundary_certificate.schema.json": "formal/certificates/fusion/FUSION-BOUNDARY-01.certificate.json",
        "route_completion_certificate.schema.json": "formal/certificates/route_completion/ROUTE-COMP-FLAT-01.certificate.json",
        "toy_suite_closure_certificate.schema.json": "formal/certificates/toy_suite/TOY-SUITE-PRIMARY-01.certificate.json",
    }
    for index, (schema_name, cert_rel) in enumerate(landed_pairs.items(), 1):
        schema = load_json(ROOT / "schemas/certificates" / schema_name)
        errors = list(Draft202012Validator(schema).iter_errors(load_json(ROOT / cert_rel)))
        v.check(f"SCHEMA-LANDED-{index:02d}", "schemas", not errors, f"{schema_name} accepts the landed certificate")


def check_composition(v: Validation) -> None:
    full_path = ROOT / "formal/certificates/composition/FIACH-COMP-01.certificate.json"
    full = load_json(full_path)
    audit = audit_full_handoff_composition(full, ROOT)
    v.check("COMP-FULL-REPLAY", "composition", audit.to_dict() == full.get("audit"), "full handoff audit replays byte-semantically")
    for index, (name, value) in enumerate(audit.to_dict().items(), 1):
        if isinstance(value, bool):
            expected = True if name not in {"ontology_present"} else False
            v.check(f"COMP-FULL-{index:02d}", "composition", value is expected, f"full composition field {name} has the licensed value")
    v.check("COMP-ENDPOINTS", "composition", (audit.source_code, audit.shared_code, audit.target_code) == (17, 55, 101), "composition endpoints are source 17, intermediate 55, target 101")
    v.check("COMP-ROUTE", "composition", audit.route_status == "route-indexed", "nonflat component route data remain route-indexed")
    v.check("COMP-UPSTREAM", "composition", audit.all_upstream_support_withdrawn, "outer autonomy withdraws all upstream supports")

    for index, name in enumerate(("STG-COMP-01",), 1):
        cert = load_json(ROOT / f"formal/certificates/composition/{name}.certificate.json")
        staged = audit_staged_composition(cert, ROOT)
        v.check(f"COMP-STAGED-{index:02d}", "composition", staged.to_dict() == cert.get("audit") and staged.composition_valid, f"{name} staged package maps compose exactly")

    search = load_json(ROOT / "formal/certificates/search/FULL_HANDOFF_INTERFACE_EXHAUSTION.json")
    recomputed = bounded_full_handoff_interface_search()
    v.check("COMP-SEARCH-EXACT", "composition", search == recomputed, "full-handoff interface exhaustion reproduces exactly")
    v.check("COMP-SEARCH-COUNT", "composition", search.get("candidates_examined") == 1024 and search.get("accepted_candidates") == 1, "all 2^10 interfaces are checked and exactly one passes")
    v.check("COMP-SINGLE-FAIL", "composition", search.get("all_single_failures_rejected") is True, "every one-premise deletion is rejected")

    model = load_json(ROOT / "models/composition/autonomy/AUT-COMP-OUTER.model.json")
    removed = model.get("withdrawal", {}).get("removed_resources", [])
    owners = {row.get("owner", {}).get("code") for row in removed if row.get("role") == "source"}
    v.check("COMP-OUTER-WITHDRAW", "composition", owners == {17, 55}, "outer controller removes source and intermediate substrate")


def check_branching(v: Validation) -> None:
    fission_path = ROOT / "formal/certificates/fission/FISSION-POS-01.certificate.json"
    fission = load_json(fission_path)
    audit = audit_temporal_fission(fission, ROOT)
    v.check("FIS-REPLAY", "fission", audit.to_dict() == fission.get("audit"), "fission audit replays exactly")
    v.check("FIS-VALID", "fission", audit.relation_valued_fission_valid, "relation-valued fission is valid")
    v.check("FIS-ENDPOINTS", "fission", (audit.source_code, audit.left_target_code, audit.right_target_code) == (17, 201, 202), "source and branch targets are exact")
    for field in ("target_shapes_symmetric", "relation_contains_both_branches", "swap_involutive", "swap_fixed_point_free", "validity_preserved_by_swap", "invariant_singleton_selector_absent", "uniqueness_claim_absent"):
        v.check(f"FIS-{field.upper().replace('_','-')}", "fission", getattr(audit, field) is True, f"fission obligation {field} passes")
    controls = sorted((ROOT / "formal/certificates/fission/controls").glob("*.certificate.json"))
    v.check("FIS-CONTROL-COUNT", "fission", len(controls) == 6, "six fission controls exist")
    for index, path in enumerate(controls, 1):
        cert = load_json(path)
        observed = cert.get("observed_failures", [])
        v.check(f"FIS-CONTROL-{index:02d}", "fission", cert.get("audit", {}).get("relation_valued_fission_valid") is False and cert.get("expected_primary_failure") in observed, f"{path.name} breaks its named obligation")
    search = load_json(ROOT / "formal/certificates/search/FISSION_SYMMETRY_EXHAUSTION.json")
    v.check("FIS-SEARCH-EXACT", "fission", search == bounded_fission_symmetry_search(4), "fission symmetry exhaustion reproduces exactly")
    v.check("FIS-SEARCH-COUNT", "fission", search.get("candidates_examined") == 6564 and search.get("minimum_target_count") == 2, "bounded symmetry search has the frozen count and minimum")
    v.check("FIS-NO-SELECTOR", "fission", search.get("invariant_singleton_selector_violations") == 0, "no invariant singleton selector appears")

    fusion_path = ROOT / "formal/certificates/fusion/FUSION-BOUNDARY-01.certificate.json"
    fusion = load_json(fusion_path)
    faudit = audit_fusion_boundary(fusion, ROOT)
    v.check("FUS-REPLAY", "fusion", faudit.to_dict() == fusion.get("audit"), "fusion boundary audit replays exactly")
    v.check("FUS-VALID", "fusion", faudit.fusion_boundary_valid, "fusion/recombination boundary is valid")
    for field in ("left_lineage_valid", "right_lineage_valid", "common_target", "branchwise_payload_preserved", "action_credit_conflict_witnessed", "recombination_failure_witnessed", "integrated_target_package_fails", "merger_does_not_imply_package"):
        v.check(f"FUS-{field.upper().replace('_','-')}", "fusion", getattr(faudit, field) is True, f"fusion obligation {field} passes")
    fsearch = load_json(ROOT / "formal/certificates/search/FUSION_BOUNDARY_EXHAUSTION.json")
    v.check("FUS-SEARCH-EXACT", "fusion", fsearch == bounded_fusion_boundary_search(), "fusion boundary exhaustion reproduces exactly")
    v.check("FUS-SEARCH-COUNT", "fusion", fsearch.get("candidates_examined") == 128 and fsearch.get("boundary_cases") == 3, "fusion Boolean boundary has frozen counts")


def check_routes_and_toys(v: Validation) -> None:
    route_paths = [
        ROOT / "formal/certificates/route_completion/ROUTE-COMP-INDEXED-01.certificate.json",
        ROOT / "formal/certificates/route_completion/ROUTE-COMP-FLAT-01.certificate.json",
    ]
    outputs: set[str] = set()
    for index, path in enumerate(route_paths, 1):
        cert = load_json(path)
        audit = audit_route_completion(cert, ROOT)
        outputs.add(audit.output_route_status)
        v.check(f"ROUTE-REPLAY-{index:02d}", "routes", audit.to_dict() == cert.get("audit") and audit.route_completion_valid, f"{path.name} replays and passes")
        v.check(f"ROUTE-MEMORY-LAW-{index:02d}", "routes", audit.no_unlicensed_memory_erasure, f"{path.name} satisfies memory-or-flatness")
    v.check("ROUTE-MODES", "routes", outputs == {"flat", "route-indexed"}, "both licensed route modes are represented")
    controls = sorted((ROOT / "formal/certificates/route_completion/controls").glob("*.certificate.json"))
    v.check("ROUTE-CONTROL-COUNT", "routes", len(controls) == 1, "one minimal unlicensed-erasure route control exists")
    for index, path in enumerate(controls, 1):
        cert = load_json(path)
        v.check(f"ROUTE-CONTROL-{index:02d}", "routes", cert.get("audit", {}).get("route_completion_valid") is False, f"{path.name} is rejected")
    search = load_json(ROOT / "formal/certificates/search/ROUTE_COMPLETION_EXHAUSTION.json")
    v.check("ROUTE-SEARCH-EXACT", "routes", search == bounded_route_completion_search(), "route-completion exhaustion reproduces exactly")
    v.check("ROUTE-SEARCH-COUNT", "routes", search.get("candidates_examined") == 16 and search.get("licensed_flat_upgrades") == 1 and search.get("unlicensed_memory_erasure_count") == 0, "route-completion Boolean table is exact")

    toy_path = ROOT / "formal/certificates/toy_suite/TOY-SUITE-PRIMARY-01.certificate.json"
    toy = load_json(toy_path)
    taudit = audit_toy_suite(toy, ROOT)
    v.check("TOY-REPLAY", "toys", taudit.to_dict() == toy.get("audit"), "toy-suite audit replays exactly")
    v.check("TOY-CLOSED", "toys", taudit.toy_suite_closed and taudit.toy_count == 13 and taudit.passing_toy_count == 13, "all 13 primary/common toys pass")
    for index, row in enumerate(toy.get("entries", []), 1):
        ref = row.get("evidence_ref")
        ok = isinstance(ref, str) and (ROOT / ref).is_file() and row.get("evidence_sha256") == sha256(ROOT / ref)
        v.check(f"TOY-HASH-{index:02d}", "toys", ok, f"{row.get('toy_id')} evidence is hash-bound")
    features = load_json(ROOT / "models/toy_suite/TOY_FEATURE_MATRIX.json").get("rows", [])
    search = load_json(ROOT / "formal/certificates/search/TOY_HIDDEN_EQUIVALENCE_SEARCH.json")
    v.check("TOY-SEARCH-EXACT", "toys", search == hidden_equivalence_search(features), "hidden-equivalence search reproduces exactly")
    v.check("TOY-SEARCH-COUNT", "toys", search.get("pairs_examined") == 78 and search.get("collision_count", 0) > 0, "all toy pairs are checked and structural collisions are exposed")


def check_registries(v: Validation) -> None:
    theorem = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    v.check("REG-THEOREM-COUNT", "registries", len(theorem) == 35, "theorem registry retains 35 contracts")
    v.check("REG-THEOREM-UNIQUE-ID", "registries", duplicate_values(theorem, "theorem_id") == set(), "theorem IDs are unique")
    v.check("REG-THEOREM-UNIQUE-LEAN", "registries", duplicate_values(theorem, "lean_statement") == set(), "Lean declaration bundles are unique")
    statuses = Counter(row["status"] for row in theorem)
    expected = Counter({
        "proof-source-and-executable-certificate-landed": 14,
        "open-scaffold": 8,
        "checked-finite-countermodel": 7,
        "proof-source-and-checked-finite-countermodel": 5,
        "finite-discriminator-evidence-landed-theorem-open": 1,
    })
    v.check("REG-THEOREM-STATUS", "registries", statuses == expected, "theorem status accounting is exact")
    by_id = {row["theorem_id"]: row for row in theorem}
    for index, theorem_id in enumerate(("TTH-07", "TTH-08", "TTH-09", "TTN-11", "TTN-14"), 1):
        row = by_id[theorem_id]
        v.check(f"REG-ADVANCED-{index:02d}", "registries", "proof-source" in row["status"] and (row["phase"] == PHASE or theorem_id == "TTH-09"), f"{theorem_id} has its landed proof-source status")
    v.check("REG-FALLBACK-OPEN", "registries", all(by_id[f"TTF-{i:02d}"]["status"] == "open-scaffold" for i in range(1, 9)), "all Temporal-IAPS fallback theorem contracts remain open")

    toys = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    v.check("REG-TOY-COUNT", "registries", len(toys) == 23 and duplicate_values(toys, "toy_id") == set(), "toy registry retains 23 unique assets")
    v.check("REG-TOY-FISSION", "registries", next(row for row in toys if row["toy_id"] == "TTM-07")["phase"] == PHASE, "temporal fission toy advances in CST-TT-06")
    closure = read_csv(ROOT / "registries/TT06_TOY_CLOSURE.csv")
    v.check("REG-TOY-CLOSURE", "registries", len(closure) == 13 and all(row["status"] == "checked" for row in closure), "13 toy closure rows are checked")

    expected_counts = {
        "FULL_HANDOFF_COMPOSITION_REGISTRY.csv": 1,
        "TEMPORAL_FISSION_REGISTRY.csv": 1,
        "FUSION_BOUNDARY_REGISTRY.csv": 1,
        "ROUTE_COMPLETION_REGISTRY.csv": 2,
        "FISSION_CONTROL_REGISTRY.csv": 6,
    }
    for index, (name, count) in enumerate(expected_counts.items(), 1):
        rows = read_csv(ROOT / "registries" / name)
        v.check(f"REG-TT06-{index:02d}", "registries", len(rows) == count, f"{name} has {count} rows")

    project = load_json(ROOT / "registries/PROJECT_REGISTRY.json")
    expected_project = {
        "phase": PHASE,
        "phase_base_tag": BASE_TAG,
        "phase_base_commit": BASE_COMMIT,
        "checked_full_handoff_composition_certificates": 1,
        "checked_relation_valued_fission_certificates": 1,
        "checked_fusion_boundary_certificates": 1,
        "checked_route_completion_certificates": 2,
        "checked_primary_common_toy_suite": "13/13",
        "positive_handoff_witnesses": 4,
        "fallback_unlocked": False,
        "next_phase": "CST-TT-07A",
    }
    for index, (key, value) in enumerate(expected_project.items(), 1):
        v.check(f"REG-PROJECT-{index:02d}", "registries", project.get(key) == value, f"project registry {key}={value!r}")


def check_lean_static(v: Validation) -> None:
    files = sorted((ROOT / "CSTTT").rglob("*.lean"))
    placeholder = re.compile(r"\b(sorry|admit|axiom|unsafe)\b", re.IGNORECASE)
    v.check("LEAN-COUNT", "lean-static", len(files) >= 25, f"at least 25 Lean files are present ({len(files)})")
    aggregate = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    for index, path in enumerate(files, 1):
        text = path.read_text(encoding="utf-8")
        v.check(f"LEAN-PLACEHOLDER-{index:03d}", "lean-static", placeholder.search(text) is None, f"{path.relative_to(ROOT)} has no prohibited proof placeholder")
    required = {
        "CSTTT/Targets/Composition.lean": ("fullTemporalHandoffComposition", "composedHandoffPreservesIndependentLanes", "routeIndexedComponentPreventsAutomaticFlatness"),
        "CSTTT/Corridor/Fission.lean": ("relationValuedTemporalFission", "targetSwapPreservesFissionValidity", "targetSwapSymmetryNonselection"),
        "CSTTT/Package/FusionBoundary.lean": ("fusionLineageDoesNotImplyIntegratedPackage", "fusionBranchwiseDoesNotRepairRecombination"),
        "CSTTT/Targets/RouteCompletion.lean": ("noUnlicensedRouteMemoryErasure", "retainedRouteMemoryYieldsIndexedStatus", "certifiedNormalizationYieldsFlatStatus"),
    }
    for index, (rel, declarations) in enumerate(required.items(), 1):
        path = ROOT / rel
        text = path.read_text(encoding="utf-8")
        module = rel.removesuffix(".lean").replace("/", ".")
        v.check(f"LEAN-IMPORT-{index:02d}", "lean-static", f"import {module}" in aggregate, f"aggregate imports {module}")
        for j, declaration in enumerate(declarations, 1):
            v.check(f"LEAN-DECL-{index:02d}-{j:02d}", "lean-static", f"theorem {declaration}" in text, f"Lean declaration {declaration} exists")
    forbidden = {
        "CSTTT/Temporal": ("CSTTT.Corridor", "CSTTT.Targets"),
        "CSTTT/Package": ("CSTTT.Corridor", "CSTTT.Autonomy", "CSTTT.Targets"),
        "CSTTT/Transport": ("CSTTT.Corridor", "CSTTT.Targets"),
        "CSTTT/Corridor": ("CSTTT.Targets",),
        "CSTTT/Autonomy": ("CSTTT.Corridor", "CSTTT.Targets"),
    }
    violations: list[str] = []
    for directory, prefixes in forbidden.items():
        for path in (ROOT / directory).rglob("*.lean"):
            text = path.read_text(encoding="utf-8")
            for prefix in prefixes:
                if f"import {prefix}" in text:
                    violations.append(f"{path.relative_to(ROOT)} -> {prefix}")
    v.check("LEAN-LAYERING", "lean-static", not violations, "primitive import graph does not reverse layers" + (f": {violations}" if violations else ""))


def check_claim_boundaries(v: Validation) -> None:
    docs = [
        ROOT / "docs/FULL_HANDOFF_COMPOSITION_THEOREM.md",
        ROOT / "docs/RELATION_VALUED_TEMPORAL_FISSION.md",
        ROOT / "docs/FUSION_RECOMBINATION_BOUNDARY.md",
        ROOT / "docs/FULL_TOY_SUITE_CLOSURE.md",
        ROOT / "docs/PHASE_BOUNDARY.md",
        ROOT / "manifests/CST-TT-06_COMPLETION_REPORT.md",
    ]
    for index, path in enumerate(docs, 1):
        text = path.read_text(encoding="utf-8").lower()
        v.check(f"BOUNDARY-DOC-{index:02d}", "boundaries", "consciousness" in text and any(token in text for token in ("does not", "not establish", "not landed", "no consciousness")), f"{path.name} states the consciousness nonclaim")
    project = load_json(ROOT / "registries/PROJECT_REGISTRY.json")
    v.check("BOUNDARY-FALLBACK", "boundaries", project.get("fallback_unlocked") is False, "Temporal-IAPS remains locked")
    full = load_json(ROOT / "formal/certificates/composition/FIACH-COMP-01.certificate.json")
    text = json.dumps(full).lower()
    forbidden_true = ('"consciousness": true', '"survival": true', '"numerical_identity": true', '"same_subject": true')
    v.check("BOUNDARY-CERT", "boundaries", all(token not in text for token in forbidden_true), "full composition certificate contains no ontological positive verdict")
    v.check("BOUNDARY-CEILING", "boundaries", project.get("claim_ceiling") == "exact finite structural precursor only", "project claim ceiling remains structural")


def check_manifest(v: Validation) -> None:
    manifest_path = ROOT / "manifests/CST-TT-06_MANIFEST.json"
    sums_path = ROOT / "manifests/CST-TT-06_SHA256SUMS"
    if not manifest_path.is_file() or not sums_path.is_file():
        v.check("MANIFEST-PREFREEZE", "manifest", True, "phase manifest is not required before finalization")
        return
    manifest = load_json(manifest_path)
    v.check("MANIFEST-PHASE", "manifest", manifest.get("phase") == PHASE, "manifest phase is current")
    rows = manifest.get("files", [])
    v.check("MANIFEST-COUNT", "manifest", manifest.get("file_count") == len(rows) and len(rows) >= 1000, f"manifest lists {len(rows)} files")
    for index, row in enumerate(rows, 1):
        path = ROOT / row["path"]
        ok = path.is_file() and path.stat().st_size == row["bytes"] and sha256(path) == row["sha256"]
        v.check(f"MANIFEST-FILE-{index:04d}", "manifest", ok, f"manifest row {row['path']} verifies")
    lines = sums_path.read_text(encoding="utf-8").splitlines()
    v.check("MANIFEST-SUM-COUNT", "manifest", len(lines) == len(rows) + 2, "checksum ledger includes repository files and both manifests")
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
    out_json = ROOT / "manifests/CST-TT-06_VALIDATION_RESULTS.json"
    out_md = ROOT / "manifests/CST-TT-06_VALIDATION_REPORT.md"
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    lines = [
        "# CST-TT-06 Validation Report",
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
    check_json_tree(v)
    check_schemas(v)
    check_composition(v)
    check_branching(v)
    check_routes_and_toys(v)
    check_registries(v)
    check_lean_static(v)
    check_claim_boundaries(v)
    check_manifest(v)
    counts = Counter(row.status for row in v.results)
    status = "PASS" if not v.failures else "FAIL"
    print(f"CST-TT-06 validation: {status} — {counts['PASS']} passed, {counts['FAIL']} failed, {counts['SKIP']} skipped ({len(v.results)} total)")
    if v.failures:
        for row in v.failures[:50]:
            print(f"FAIL {row.check_id}: {row.detail}", file=sys.stderr)
    if not args.no_write:
        write_report(v)
    return 1 if v.failures else 0


if __name__ == "__main__":
    raise SystemExit(main())
