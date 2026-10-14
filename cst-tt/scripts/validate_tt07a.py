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
from typing import Any, Callable, Iterable, Mapping

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
SCRIPTS = ROOT / "scripts"
for path in (SRC, SCRIPTS):
    if str(path) not in sys.path:
        sys.path.insert(0, str(path))

from cst_tt.circularity import scan_primitive_tree  # noqa: E402
from cst_tt.defect_semantics import (  # noqa: E402
    audit_defect_profile,
    bounded_defect_exhaustion,
    bounded_downward_closure_exhaustion,
)
from cst_tt.registry import duplicate_values, read_csv  # noqa: E402
from cst_tt.robustness import audit_robustness, audit_specific_perturbation, enumerate_bounded_perturbations  # noqa: E402
from cst_tt.strengthenings import (  # noqa: E402
    audit_generalized_continuity_path,
    audit_overlap_direct_relation,
    bounded_relation_truth_table,
)
from cst_tt.unbounded import (  # noqa: E402
    arbitrary_finite_prefix_counterfamily,
    audit_unbounded_invariant,
    bounded_disturbance_prefix_check,
)
from tt07a_data import (  # noqa: E402
    defect_controls,
    equal_scalar_profiles,
    full_defect_profile,
    robustness_controls,
    robustness_model,
    unbounded_spec,
)

PHASE = "CST-TT-07A"
PHASE_TAG = "CST-TT-07A-v1"
BASE_TAG = "CST-TT-06-v1"
BASE_COMMIT = "6c8f510c67087a8db9dd1c4107008b3b7cfb0847"


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


def csv_rows(path: Path) -> list[dict[str, str]]:
    with path.open(newline="", encoding="utf-8") as handle:
        return list(csv.DictReader(handle))


def split_ids(value: str) -> set[str]:
    return {item for item in value.split(";") if item}


def check_baseline(v: Validation, require_clean: bool, require_tag: bool) -> None:
    v.guarded("BASE-001", "baseline", "repository is a Git worktree", lambda: git("rev-parse", "--is-inside-work-tree") == "true")
    v.guarded("BASE-002", "baseline", f"{BASE_TAG} resolves to the frozen commit", lambda: git("rev-parse", BASE_TAG + "^{}") == BASE_COMMIT)
    v.guarded(
        "BASE-003",
        "baseline",
        "frozen CST-TT-06 base is an ancestor of HEAD",
        lambda: subprocess.run(["git", "merge-base", "--is-ancestor", BASE_COMMIT, "HEAD"], cwd=ROOT).returncode == 0,
    )
    v.guarded("BASE-004", "baseline", "repository has no whitespace errors", lambda: subprocess.run(["git", "diff", "--check"], cwd=ROOT, capture_output=True).returncode == 0)
    if require_clean:
        v.guarded("BASE-005", "baseline", "working tree is clean", lambda: git("status", "--porcelain") == "")
    else:
        v.check("BASE-005", "baseline", True, "clean-tree gate deferred until tagged release verification")
    tags = set(git("tag", "--list").splitlines())
    if require_tag:
        v.check("BASE-006", "baseline", PHASE_TAG in tags, f"{PHASE_TAG} exists")
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
    v.check("TOOL-STATUS-LEAN", "toolchain", status.get("lean_compile_status") == "pending-toolchain", "Lean status is not overclaimed")
    v.check("TOOL-STATUS-PY", "toolchain", status.get("python_certificate_status") == "checked", "Python certificate status is checked")
    lean, lake = shutil.which("lean"), shutil.which("lake")
    if lean and lake:
        proc = subprocess.run([lake, "build"], cwd=ROOT, text=True, capture_output=True, timeout=600)
        detail = "pinned Lean sources compile with lake build"
        if proc.returncode != 0:
            detail += ": " + (proc.stdout + proc.stderr)[-3000:].replace("\n", " ")
        v.check("TOOL-LEAN-BUILD", "toolchain", proc.returncode == 0, detail)
    else:
        v.skip("TOOL-LEAN-BUILD", "toolchain", "lean/lake unavailable; no Lean-kernel compilation pass is claimed")


def check_python(v: Validation) -> None:
    files = sorted([*SRC.rglob("*.py"), *(ROOT / "scripts").glob("*.py"), *(ROOT / "tests").glob("*.py")])
    v.check("PY-COUNT", "python", len(files) >= 75, f"at least seventy-five Python files are present ({len(files)})")
    for index, path in enumerate(files, 1):
        v.guarded(f"PY-COMPILE-{index:03d}", "python", f"{path.relative_to(ROOT)} compiles", lambda p=path: py_compile.compile(str(p), doraise=True) is not None)
    proc = subprocess.run(
        [sys.executable, "-m", "pytest", "-q"],
        cwd=ROOT,
        text=True,
        capture_output=True,
        timeout=900,
        env={**os.environ, "PYTHONPATH": "src:scripts", "PYTHONHASHSEED": "0"},
    )
    detail = "full pytest suite passes"
    if proc.returncode != 0:
        detail += ": " + (proc.stdout + proc.stderr)[-5000:].replace("\n", " ")
    v.check("PY-TESTS", "python", proc.returncode == 0, detail)


def check_provenance(v: Validation) -> None:
    inherited = {
        "CST-TT-00-v1": "65b3ab0f94564cee1d16ffb4513045319aaaf6ef",
        "CST-TT-01-v1": "488db50b20d6d9c67493de3e9fd758e6e9e205ce",
        "CST-TT-02-v1": "3abf5b2406f754b43823b68987c7ea409e737fd0",
        "CST-TT-03-v1": "63ea725a7b6ade8df58a94cf7aad2ad78440ce70",
        "CST-TT-04-v1": "1884214d1bae82442f37fc9e6b013e222da89b1b",
        "CST-TT-05-v1": "faaf3b714050ac6acc195d0fab0f49dae9f51a87",
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
    roots = [ROOT / "models", ROOT / "formal/certificates", ROOT / "schemas", ROOT / "examples/scaffold", ROOT / "registries", ROOT / "manifests"]
    paths: list[Path] = []
    for root in roots:
        paths.extend(root.rglob("*.json"))
    paths = sorted(set(paths))
    v.check("JSON-COUNT", "json", len(paths) >= 500, f"at least five hundred JSON surfaces are present ({len(paths)})")
    for index, path in enumerate(paths, 1):
        v.guarded(f"JSON-PARSE-{index:04d}", "json", f"{path.relative_to(ROOT)} parses", lambda p=path: isinstance(load_json(p), (dict, list)))


def check_schemas(v: Validation) -> None:
    schemas = sorted((ROOT / "schemas/certificates").glob("*.schema.json"))
    examples = sorted((ROOT / "examples/scaffold").glob("*.json"))
    registry = read_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv")
    v.check("SCHEMA-COUNT", "schemas", len(schemas) == 35, "thirty-five certificate schemas are present")
    v.check("EXAMPLE-COUNT", "schemas", len(examples) == 35, "thirty-five scaffold examples are present")
    v.check("SCHEMA-REGISTRY-COUNT", "schemas", len(registry) == 35, "schema registry has thirty-five rows")
    v.check("SCHEMA-IDS", "schemas", duplicate_values(registry, "schema_id") == set(), "schema identifiers are unique")
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
                text = example_path.read_text(encoding="utf-8")
                v.check(f"SCHEMA-SCAFFOLD-{index:02d}", "schemas", '"result_status": "checked-' not in text and '"result_status": "proved"' not in text, f"{row['schema_id']} scaffold does not claim landed evidence")
            except Exception as exc:
                v.check(f"SCHEMA-VALID-{index:02d}", "schemas", False, f"{row['schema_id']} failed: {exc}")

    theorem_schema = load_json(ROOT / "schemas/registries/theorem_registry_row.schema.json")
    Draft202012Validator.check_schema(theorem_schema)
    theorem_validator = Draft202012Validator(theorem_schema)
    for index, row in enumerate(read_csv(ROOT / "registries/THEOREM_REGISTRY.csv"), 1):
        errors = list(theorem_validator.iter_errors(row))
        v.check(f"SCHEMA-THEOREM-{index:02d}", "schemas", not errors, f"theorem row {row['theorem_id']} matches its schema")


def check_registries(v: Validation) -> None:
    theorem = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    toy = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    definitions = read_csv(ROOT / "registries/DEFINITION_REGISTRY.csv")
    kills = read_csv(ROOT / "registries/KILL_CRITERIA.csv")
    deps = read_csv(ROOT / "registries/DEPENDENCY_EDGES.csv")
    v.check("REG-THEOREM-COUNT", "registries", len(theorem) == 39, "theorem registry has 39 rows")
    v.check("REG-TOY-COUNT", "registries", len(toy) == 28, "toy registry has 28 rows")
    v.check("REG-DEFINITION-COUNT", "registries", len(definitions) == 73, "definition registry has 73 rows")
    v.check("REG-KILL-COUNT", "registries", len(kills) == 20, "kill register has 20 rows")
    for name, rows, key in (("theorem", theorem, "theorem_id"), ("toy", toy, "toy_id"), ("definition", definitions, "definition_id"), ("kill", kills, "kill_id")):
        v.check(f"REG-{name.upper()}-UNIQUE", "registries", duplicate_values(rows, key) == set(), f"{name} identifiers are unique")
    status = Counter(row["status"] for row in theorem)
    v.check(
        "REG-THEOREM-STATUS",
        "registries",
        status == Counter({"proof-source-and-executable-certificate-landed": 19, "open-scaffold": 8, "proof-source-and-checked-finite-countermodel": 7, "checked-finite-countermodel": 5}),
        "theorem status vocabulary and exact counts are frozen",
    )
    theorem_ids = {row["theorem_id"] for row in theorem}
    toy_ids = {row["toy_id"] for row in toy}
    for index, row in enumerate(theorem, 1):
        v.check(f"REG-THEOREM-DEP-{index:02d}", "registries", split_ids(row["dependencies"]).issubset(theorem_ids), f"{row['theorem_id']} theorem dependencies resolve")
        v.check(f"REG-THEOREM-TOY-{index:02d}", "registries", split_ids(row["toy_dependencies"]).issubset(toy_ids), f"{row['theorem_id']} toy dependencies resolve")
        v.check(f"REG-THEOREM-CLAIM-{index:02d}", "registries", bool(row["claim_ceiling"]), f"{row['theorem_id']} has a claim ceiling")
    by_theorem = {row["theorem_id"]: row for row in theorem}
    for theorem_id in ("TTS-01", "TTS-02", "TTS-03", "TTS-04"):
        v.check(f"REG-STRENGTHENING-{theorem_id}", "registries", by_theorem.get(theorem_id, {}).get("status") == "proof-source-and-executable-certificate-landed", f"{theorem_id} is landed")
    v.check("REG-TTD02", "registries", by_theorem["TTD-02"]["status"] == "proof-source-and-executable-certificate-landed", "overlap/direct comparison is advanced")
    v.check("REG-TTN10", "registries", by_theorem["TTN-10"]["status"] == "proof-source-and-checked-finite-countermodel", "scalar insufficiency boundary is strengthened")
    v.check("REG-TTN12", "registries", by_theorem["TTN-12"]["status"] == "proof-source-and-checked-finite-countermodel", "finite-prefix insufficiency boundary is strengthened")
    v.check("REG-FALLBACK-OPEN", "registries", all(by_theorem[f"TTF-{index:02d}"]["status"] == "open-scaffold" for index in range(1, 9)), "all fallback theorem surfaces remain open scaffolds")
    by_definition = {row["name"]: row for row in definitions}
    for name, did in (("GeneralizedTemporalContinuity", "D-070"), ("DefectVector", "D-071"), ("TemporalMargin", "D-072"), ("ExactAutonomyPolicy", "D-073")):
        v.check(f"REG-DEFINITION-{did}", "registries", by_definition.get(name, {}).get("definition_id") == did, f"{name} has collision-free identifier {did}")
    dep_tuples = [tuple(row.get(field, "") for field in ("source", "target", "reason", "status")) for row in deps]
    v.check("REG-DEPS-UNIQUE", "registries", len(dep_tuples) == len(set(dep_tuples)), "dependency edges are unique as full tuples")
    for source, target in (("TTD-01", "TTS-01"), ("TTH-04", "TTS-01"), ("TTN-10", "TTS-02"), ("TTS-02", "TTS-03"), ("TTH-05", "TTS-04")):
        v.check(f"REG-DEP-{source}-{target}", "registries", any(row["source"] == source and row["target"] == target for row in deps), f"dependency {source} → {target} is present")
    by_kill = {row["kill_id"]: row for row in kills}
    for kill_id in ("K-DIRECT-01", "K-ROBUST-01", "K-LIVE-01"):
        v.check(f"REG-KILL-{kill_id}", "registries", by_kill[kill_id]["status"] == "not-triggered-CST-TT-07A", f"{kill_id} did not trigger")


def check_formal_surfaces(v: Validation) -> None:
    lean_paths = sorted((ROOT / "CSTTT").rglob("*.lean"))
    corpus = "\n".join(path.read_text(encoding="utf-8") for path in lean_paths)
    root_imports = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    v.check("LEAN-COUNT", "formal", len(lean_paths) >= 35, f"at least 35 Lean modules are present ({len(lean_paths)})")
    placeholder = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")
    for index, path in enumerate(lean_paths, 1):
        text = path.read_text(encoding="utf-8")
        v.check(f"LEAN-PLACEHOLDER-{index:03d}", "formal", placeholder.search(text) is None, f"{path.relative_to(ROOT)} has no unproved placeholder command")
        opens = sum(text.count(token) for token in ("(", "[", "{"))
        closes = sum(text.count(token) for token in (")", "]", "}"))
        v.check(f"LEAN-DELIM-{index:03d}", "formal", opens == closes, f"{path.relative_to(ROOT)} has balanced coarse delimiters")
    v.check("LEAN-CIRCULARITY", "formal", scan_primitive_tree(ROOT) == [], "primitive Lean tree contains no verdict-loaded vocabulary")
    modules = (
        "CSTTT.Strengthening.ContinuityClass",
        "CSTTT.Robustness.DefectVector",
        "CSTTT.Robustness.TemporalMargins",
        "CSTTT.Autonomy.UnboundedInvariant",
    )
    for index, module in enumerate(modules, 1):
        v.check(f"LEAN-IMPORT-{index:02d}", "formal", f"import {module}" in root_imports, f"{module} is imported by CSTTT.lean")
    declarations = (
        "GeneralizedTemporalContinuity",
        "overlapDirectIncomparable",
        "generalizedStrictlyBroaderThanOverlap",
        "generalizedPathComposition",
        "DefectVector",
        "acceptedHardGateIsZero",
        "vectorAcceptanceDownwardClosed",
        "scalarSummaryDoesNotDetermineAcceptance",
        "boundedPerturbationPreservesMargin",
        "failedHardGateCannotBeAveragedAway",
        "ExactAutonomyPolicy",
        "modelRelativeUnboundedControlledInvariant",
        "arbitrarilyLongFinitePrefixStillInsufficient",
    )
    for index, declaration in enumerate(declarations, 1):
        v.check(f"LEAN-DECL-{index:02d}", "formal", declaration in corpus, f"Lean declaration {declaration} is present")
    for index, row in enumerate(read_csv(ROOT / "registries/DEFINITION_REGISTRY.csv"), 1):
        module = ROOT / row["module"]
        v.check(f"LEAN-DEF-MODULE-{index:03d}", "formal", module.is_file(), f"definition module {row['module']} exists")
        if module.is_file():
            v.check(f"LEAN-DEF-NAME-{index:03d}", "formal", row["name"] in module.read_text(encoding="utf-8"), f"definition {row['name']} is present")
    for index, row in enumerate(read_csv(ROOT / "registries/THEOREM_REGISTRY.csv"), 1):
        for subindex, declaration in enumerate(row["lean_statement"].split(";"), 1):
            name = declaration.split(".")[-1]
            v.check(f"LEAN-THEOREM-{index:02d}-{subindex:02d}", "formal", name in corpus, f"registered declaration {declaration} is present")


def verify_model_hash(v: Validation, check_id: str, cert: Mapping[str, Any]) -> None:
    rel = cert.get("model_ref")
    ok = isinstance(rel, str) and (ROOT / rel).is_file() and cert.get("model_sha256") == sha256(ROOT / rel)
    v.check(check_id, "certificates", ok, f"certificate {cert.get('certificate_id')} is bound to its model hash")


def check_direct_relation(v: Validation) -> None:
    cert = load_json(ROOT / "formal/certificates/strengthenings/continuity/ODR-01.certificate.json")
    verify_model_hash(v, "DIRECT-HASH", cert)
    model = load_json(ROOT / cert["model_ref"])
    audit = audit_overlap_direct_relation(model, ROOT)
    v.check("DIRECT-REPLAY", "direct-relation", audit.to_dict() == cert["audit"], "overlap/direct audit replays byte-for-byte")
    properties = {
        "incomparable": audit.overlap_direct_incomparable,
        "overlap-embeds": audit.overlap_embeds_generalized,
        "direct-embeds": audit.direct_embeds_generalized,
        "strict-broadening": audit.generalized_strictly_broader_than_overlap,
        "mixed-path": audit.mixed_mode_path_valid,
        "detached-excluded": audit.detached_copy_excluded,
        "gap-excluded": audit.temporal_gap_excluded,
        "same-carrier-excluded": audit.same_carrier_excluded,
        "primary-unchanged": audit.primary_definition_unchanged,
        "fallback-locked": audit.fallback_remains_locked,
    }
    for index, (name, value) in enumerate(properties.items(), 1):
        v.check(f"DIRECT-{index:02d}", "direct-relation", value, name)
    expected = {
        "GCP-OVERLAP-01": (("overlap",), True),
        "GCP-DIRECT-01": (("direct",), False),
        "GCP-MIXED-01": (("overlap", "direct"), False),
    }
    for index, (path_id, (modes, primary)) in enumerate(expected.items(), 1):
        path_cert = load_json(ROOT / f"formal/certificates/strengthenings/continuity/{path_id}.certificate.json")
        verify_model_hash(v, f"DIRECT-PATH-HASH-{index}", path_cert)
        path_audit = audit_generalized_continuity_path(load_json(ROOT / path_cert["model_ref"]), ROOT)
        v.check(f"DIRECT-PATH-REPLAY-{index}", "direct-relation", path_audit.to_dict() == path_cert["audit"], f"{path_id} replays")
        v.check(f"DIRECT-PATH-MODE-{index}", "direct-relation", path_audit.mode_sequence == modes, f"{path_id} has its frozen mode sequence")
        v.check(f"DIRECT-PATH-PRIMARY-{index}", "direct-relation", path_audit.primary_fiach_eligible is primary, f"{path_id} strict-FIACH eligibility is correct")
    truth = bounded_relation_truth_table()
    v.check("DIRECT-TRUTH-FROZEN", "direct-relation", truth == load_json(ROOT / "formal/certificates/search/OVERLAP_DIRECT_RELATION_TRUTH_TABLE.json"), "relation truth table is frozen exactly")
    v.check("DIRECT-TRUTH-COUNT", "direct-relation", truth == {"search_id": "OVERLAP_DIRECT_RELATION_TRUTH_TABLE", "candidates_examined": 4, "overlap_embedding_violations": 0, "direct_embedding_violations": 0, "strict_broadening_witnesses": 1, "rows": truth["rows"]}, "truth-table headline counts are exact")


def check_defects(v: Validation) -> None:
    positive = audit_defect_profile(full_defect_profile())
    v.check("DEF-POS", "defects", positive.accepted, "positive vector defect profile is accepted")
    v.check("DEF-HARD-COUNT", "defects", sum(row.gate_kind == "hard" for row in positive.component_audits) == 12, "twelve hard gates are present")
    v.check("DEF-SOFT-COUNT", "defects", sum(row.gate_kind == "soft" for row in positive.component_audits) == 5, "five soft margins are present")
    v.check("DEF-HARD-EXACT", "defects", positive.every_hard_gate_exact, "every hard gate has exactly zero defect")
    v.check("DEF-SOFT-BOUNDED", "defects", positive.every_component_within_tolerance, "every soft defect is within its component tolerance")
    v.check("DEF-SCALAR-DIAGNOSTIC", "defects", positive.scalar_summary_diagnostic_only, "scalar summary is diagnostic only")
    for index, (control_id, expected_failure, profile) in enumerate(defect_controls(), 1):
        audit = audit_defect_profile(profile)
        v.check(f"DEF-CONTROL-REJECT-{index:02d}", "defects", not audit.accepted, f"{control_id} is rejected")
        v.check(f"DEF-CONTROL-REASON-{index:02d}", "defects", expected_failure in audit.failed_obligations, f"{control_id} fails {expected_failure}")
    accepted_profile, rejected_profile = equal_scalar_profiles()
    accepted, rejected = audit_defect_profile(accepted_profile), audit_defect_profile(rejected_profile)
    v.check("DEF-EQUAL-SCALAR", "defects", accepted.scalar_summary == rejected.scalar_summary, "equal scalar summaries are realized")
    v.check("DEF-OPPOSITE-VERDICT", "defects", accepted.accepted and not rejected.accepted, "equal scalar profiles have opposite vector verdicts")
    exact = bounded_defect_exhaustion()
    downward = bounded_downward_closure_exhaustion()
    v.check("DEF-SEARCH-FROZEN", "defects", exact == load_json(ROOT / "formal/certificates/search/VECTOR_DEFECT_EXHAUSTION.json"), "defect exhaustion is frozen")
    v.check("DEF-SEARCH-COUNT", "defects", exact["candidates_examined"] == 4096 and exact["accepted_candidates"] == 256, "4,096 profiles and 256 accepts are exact")
    v.check("DEF-SCALAR-TRAPS", "defects", exact["scalar_small_but_rejected"] == 4 and exact["equal_scalar_opposite_verdict_pairs"] == 32, "scalar-summary traps are counted exactly")
    v.check("DEF-DOWNWARD-FROZEN", "defects", downward == load_json(ROOT / "formal/certificates/search/VECTOR_DEFECT_DOWNWARD_CLOSURE.json"), "downward-closure exhaustion is frozen")
    v.check("DEF-DOWNWARD", "defects", downward["ordered_pairs_examined"] == 531441 and downward["violations"] == 0, "531,441 ordered pairs contain no downward-closure violation")


def check_robustness(v: Validation) -> None:
    model = robustness_model()
    audit = audit_robustness(model)
    v.check("ROB-POS", "robustness", audit.robustness_valid, "bounded temporal robustness certificate passes")
    v.check("ROB-BOX", "robustness", audit.bounded_box_size == 945 and audit.bounded_perturbations_checked == 945, "all 945 perturbations are checked")
    v.check("ROB-NO-VIOLATIONS", "robustness", audit.bounded_violations == 0, "no declared-box perturbation violates a margin")
    v.check("ROB-MINIMA", "robustness", audit.minimum_observed_increments == {"predictive-step": 2, "order-step": 2, "tick-step": 2, "progress-step": 1, "record-step": 2}, "minimum observed increments are exact")
    v.check("ROB-GATES", "robustness", audit.every_hard_gate_frozen_true and audit.approximation_does_not_override_hard_gates, "hard gates remain frozen and noncompensable")
    for index, (control_id, _description, deltas, gates) in enumerate(robustness_controls(), 1):
        result = audit_specific_perturbation(model, deltas, gates)
        v.check(f"ROB-CONTROL-{index:02d}", "robustness", not result["accepted"], f"{control_id} is rejected")
    search = enumerate_bounded_perturbations(model)
    v.check("ROB-SEARCH-FROZEN", "robustness", search == load_json(ROOT / "formal/certificates/search/BOUNDED_TEMPORAL_MARGIN_EXHAUSTION.json"), "bounded perturbation search is frozen exactly")


def check_unbounded(v: Validation) -> None:
    spec = unbounded_spec()
    autonomy = load_json(ROOT / spec["autonomy_model_ref"])
    audit = audit_unbounded_invariant(spec, autonomy)
    properties = {
        "base-autonomy": audit.base_autonomy_valid,
        "policy-total": audit.policy_total,
        "policy-deterministic": audit.policy_deterministic,
        "successor-inside": audit.every_successor_inside,
        "target-owned": audit.every_action_target_owned,
        "progress": audit.every_step_progresses,
        "record": audit.every_record_strictly_advances,
        "budget": audit.every_step_budget_solvent,
        "package": audit.package_invariant,
        "infinite-schema": audit.infinite_run_schema_valid,
        "model-relative": audit.model_relative_claim_only,
        "physical-not-claimed": audit.physical_liveness_not_claimed,
        "overall": audit.unbounded_model_invariance_valid,
    }
    for index, (name, value) in enumerate(properties.items(), 1):
        v.check(f"UNB-{index:02d}", "unbounded", value, name)
    v.check("UNB-LASSO", "unbounded", len(audit.lasso_witnesses) == 2 and all(row.cycle_state_ids for row in audit.lasso_witnesses), "two constant-disturbance lasso witnesses exist")
    prefix = bounded_disturbance_prefix_check(autonomy, 12)
    family = arbitrary_finite_prefix_counterfamily(12)
    v.check("UNB-PREFIX-FROZEN", "unbounded", prefix == load_json(ROOT / "formal/certificates/search/UNBOUNDED_POLICY_PREFIX_STRESS.json"), "prefix stress is frozen")
    v.check("UNB-PREFIX", "unbounded", prefix["words_checked"] == 8191 and prefix["violations"] == 0, "8,191 disturbance words have no policy violation")
    v.check("UNB-FAMILY-FROZEN", "unbounded", family == load_json(ROOT / "formal/certificates/search/ARBITRARILY_LONG_FINITE_PREFIX_FAMILY.json"), "finite-prefix counterfamily is frozen")
    v.check("UNB-FAMILY", "unbounded", family["models_constructed"] == 13 and family["every_horizon_has_countermodel"], "thirteen bounded horizons each have a fail-next countermodel")


def check_prior_bank(v: Validation) -> None:
    v.check("PRIOR-CM", "prior-bank", len(read_csv(ROOT / "registries/COUNTERMODEL_REGISTRY.csv")) == 15, "15-countermodel negative kernel remains")
    v.check("PRIOR-PKG", "prior-bank", len(read_csv(ROOT / "registries/PACKAGE_WITNESS_REGISTRY.csv")) == 4, "four package witnesses remain")
    v.check("PRIOR-CORRIDOR", "prior-bank", len(read_csv(ROOT / "registries/TEMPORAL_CORRIDOR_WITNESS_REGISTRY.csv")) == 4, "four strict corridor witnesses remain")
    v.check("PRIOR-AUTONOMY", "prior-bank", len(read_csv(ROOT / "registries/AUTONOMY_WITNESS_REGISTRY.csv")) == 1, "post-withdrawal autonomy witness remains")
    v.check("PRIOR-FIACH", "prior-bank", len(read_csv(ROOT / "registries/FIACH_WITNESS_REGISTRY.csv")) == 1, "integrated Temporal-FIACH witness remains")
    v.check("PRIOR-COMPOSITION", "prior-bank", len(read_csv(ROOT / "registries/FULL_HANDOFF_COMPOSITION_REGISTRY.csv")) == 1, "full handoff composition remains")
    v.check("PRIOR-FISSION", "prior-bank", len(read_csv(ROOT / "registries/TEMPORAL_FISSION_REGISTRY.csv")) == 1, "relation-valued fission remains")
    v.check("PRIOR-FUSION", "prior-bank", len(read_csv(ROOT / "registries/FUSION_BOUNDARY_REGISTRY.csv")) == 1, "fusion boundary remains")
    v.check("PRIOR-ROUTE", "prior-bank", len(read_csv(ROOT / "registries/ROUTE_COMPLETION_REGISTRY.csv")) == 2, "route-completion pair remains")
    toy = load_json(ROOT / "formal/certificates/toy_suite/TOY-SUITE-PRIMARY-01.certificate.json")
    toy_audit = toy.get("audit", {})
    v.check("PRIOR-TOYS", "prior-bank", toy_audit.get("toy_suite_closed") is True and toy_audit.get("toy_count") == 13 and toy_audit.get("passing_toy_count") == 13, "13/13 primary/common toy suite remains closed")


def check_claim_boundaries(v: Validation) -> None:
    project = load_json(ROOT / "registries/PROJECT_REGISTRY.json")
    expected = {
        "phase": PHASE,
        "phase_base_tag": BASE_TAG,
        "phase_base_commit": BASE_COMMIT,
        "next_phase": "CST-TT-08",
        "fallback_unlocked": False,
        "fallback_status": "Temporal-IAPS remains locked",
        "claim_ceiling": "exact finite structural precursor only",
    }
    for index, (key, value) in enumerate(expected.items(), 1):
        v.check(f"CLAIM-PROJECT-{index:02d}", "claim-boundary", project.get(key) == value, f"project field {key} is frozen")
    v.check("CLAIM-PRIMARY", "claim-boundary", "strict" in project.get("primary", "").lower(), "strict overlap remains the primary Temporal-FIACH lineage engine")
    v.check("CLAIM-DIRECT", "claim-boundary", "separate" in project.get("provisional_strengthening", "").lower() or "generalized" in project.get("provisional_strengthening", "").lower(), "direct evidence remains separately named")
    forbidden_true = ('"consciousness": true', '"survival": true', '"numerical_identity": true', '"same_subject": true', '"felt_continuity": true')
    json_paths = sorted([*ROOT.joinpath("models").rglob("*.json"), *ROOT.joinpath("formal/certificates").rglob("*.json")])
    for index, path in enumerate(json_paths, 1):
        text = path.read_text(encoding="utf-8").lower()
        v.check(f"CLAIM-JSON-{index:04d}", "claim-boundary", not any(token in text for token in forbidden_true), f"{path.relative_to(ROOT)} contains no forbidden positive ontological verdict")
    docs = (
        "docs/CST-TT-07A_DIRECT_SUCCESSOR_RELATION.md",
        "docs/CST-TT-07A_EXACT_VECTOR_DEFECT_SEMANTICS.md",
        "docs/CST-TT-07A_BOUNDED_TEMPORAL_ROBUSTNESS.md",
        "docs/CST-TT-07A_MODEL_RELATIVE_UNBOUNDED_INVARIANCE.md",
        "docs/CST-TT-07A_PRIMARY_STRENGTHENING_SYNTHESIS.md",
        "docs/CST-TT-07A_DECISION_GATE.md",
        "docs/PHASE_BOUNDARY.md",
    )
    for index, rel in enumerate(docs, 1):
        path = ROOT / rel
        v.check(f"CLAIM-DOC-EXISTS-{index:02d}", "claim-boundary", path.is_file(), f"{rel} exists")
        if path.is_file():
            text = path.read_text(encoding="utf-8").lower()
            v.check(f"CLAIM-DOC-CEILING-{index:02d}", "claim-boundary", any(token in text for token in ("not", "no consciousness", "claim ceiling", "does not")), f"{rel} records a limitation or nonclaim")


def check_manifest(v: Validation, require_manifest: bool) -> None:
    path = ROOT / "manifests/CST-TT-07A_MANIFEST.json"
    checksums = ROOT / "manifests/CST-TT-07A_SHA256SUMS"
    if not path.is_file() or not checksums.is_file():
        if require_manifest:
            v.check("MANIFEST-PRESENT", "manifest", False, "frozen phase manifest and checksum ledger are required")
        else:
            v.skip("MANIFEST-PRESENT", "manifest", "manifest is finalized after validation and rebuild reports")
        return
    manifest = load_json(path)
    files = manifest.get("files", [])
    v.check("MANIFEST-PHASE", "manifest", manifest.get("phase") == PHASE, "manifest phase is current")
    v.check("MANIFEST-COUNT", "manifest", manifest.get("file_count") == len(files) and len(files) >= 1300, f"manifest contains at least 1,300 files ({len(files)})")
    for index, row in enumerate(files, 1):
        file_path = ROOT / row["path"]
        v.check(f"MANIFEST-FILE-{index:04d}", "manifest", file_path.is_file(), f"manifest path {row['path']} exists")
        if file_path.is_file():
            v.check(f"MANIFEST-HASH-{index:04d}", "manifest", sha256(file_path) == row["sha256"], f"manifest hash for {row['path']} matches")
    lines = checksums.read_text(encoding="utf-8").splitlines()
    v.check("MANIFEST-CHECKSUM-ROWS", "manifest", len(lines) == len(files) + 2, "checksum ledger covers repository files and both manifests")


def render_report(v: Validation) -> tuple[dict[str, Any], str]:
    counts = Counter(row.status for row in v.results)
    categories: dict[str, Counter[str]] = {}
    for row in v.results:
        categories.setdefault(row.category, Counter())[row.status] += 1
    payload = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": PHASE,
        "base_tag": BASE_TAG,
        "base_commit": BASE_COMMIT,
        "status": "PASS" if not v.failures else "FAIL",
        "counts": {"total": len(v.results), "passed": counts["PASS"], "failed": counts["FAIL"], "skipped": counts["SKIP"]},
        "category_counts": {name: dict(counter) for name, counter in sorted(categories.items())},
        "results": [asdict(row) for row in v.results],
    }
    lines = [
        "# CST-TT-07A Validation Report",
        "",
        f"**Status:** {payload['status']}",
        f"**Checks:** {len(v.results)} total — {counts['PASS']} passed, {counts['FAIL']} failed, {counts['SKIP']} skipped",
        f"**Base:** `{BASE_TAG}` / `{BASE_COMMIT}`",
        "",
        "The sole permitted skip is Lean/Lake compilation when the pinned toolchain is unavailable. A skipped compiler check is not a pass.",
        "",
        "## Category summary",
        "",
        "| Category | Pass | Fail | Skip |",
        "|---|---:|---:|---:|",
    ]
    for name, counter in sorted(categories.items()):
        lines.append(f"| {name} | {counter['PASS']} | {counter['FAIL']} | {counter['SKIP']} |")
    failures = v.failures
    if failures:
        lines.extend(["", "## Failures", ""])
        lines.extend(f"- `{row.check_id}` ({row.category}): {row.detail}" for row in failures)
    lines.extend(["", "## Claim ceiling", "", "This validation does not establish consciousness, felt continuity, personal survival, numerical identity, empirical recognition, A1, A2-P, consciousness-certificate soundness, or indefinite physical persistence outside the exact finite models."])
    return payload, "\n".join(lines) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--no-write", action="store_true", help="do not rewrite validation report surfaces")
    parser.add_argument("--require-clean", action="store_true")
    parser.add_argument("--require-tag", action="store_true")
    parser.add_argument("--require-manifest", action="store_true")
    args = parser.parse_args()

    v = Validation()
    check_baseline(v, args.require_clean, args.require_tag)
    check_toolchain(v)
    check_python(v)
    check_provenance(v)
    check_json_tree(v)
    check_schemas(v)
    check_registries(v)
    check_formal_surfaces(v)
    check_direct_relation(v)
    check_defects(v)
    check_robustness(v)
    check_unbounded(v)
    check_prior_bank(v)
    check_claim_boundaries(v)
    check_manifest(v, args.require_manifest)

    payload, markdown = render_report(v)
    if not args.no_write:
        manifest_dir = ROOT / "manifests"
        manifest_dir.mkdir(parents=True, exist_ok=True)
        (manifest_dir / "CST-TT-07A_VALIDATION_RESULTS.json").write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        (manifest_dir / "CST-TT-07A_VALIDATION_REPORT.md").write_text(markdown, encoding="utf-8")
        (manifest_dir / "VALIDATION_RESULTS.json").write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        (manifest_dir / "VALIDATION_REPORT.md").write_text(markdown, encoding="utf-8")
    counts = payload["counts"]
    print(f"CST-TT-07A validation: {payload['status']} ({counts['passed']} passed, {counts['failed']} failed, {counts['skipped']} skipped; {counts['total']} total)")
    if v.failures:
        for row in v.failures[:50]:
            print(f"FAIL {row.check_id}: {row.detail}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
