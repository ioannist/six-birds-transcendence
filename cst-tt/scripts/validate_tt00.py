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
from typing import Callable

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from cst_tt.circularity import scan_primitive_tree  # noqa: E402
from cst_tt.registry import duplicate_values, read_csv  # noqa: E402

PHASE = "CST-TT-00"
BASE_COMMIT = "4a48d7ee212cde2404be06f01df0a28aa3ad12fc"
BASE_TAG = "CST-EXP-06-v1"


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

    @property
    def failures(self) -> list[Result]:
        return [r for r in self.results if r.status == "FAIL"]

    def guarded(self, check_id: str, category: str, detail: str, fn: Callable[[], bool]) -> None:
        try:
            self.check(check_id, category, bool(fn()), detail)
        except Exception as exc:  # validation should report, not crash silently
            self.check(check_id, category, False, f"{detail}: {type(exc).__name__}: {exc}")


def sha256(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def git(*args: str) -> str:
    return subprocess.check_output(["git", *args], cwd=ROOT, text=True).strip()


def split_ids(value: str) -> set[str]:
    return {item for item in value.split(";") if item}


def load_json(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def check_baseline(v: Validation, require_clean: bool) -> None:
    v.guarded("BASE-001", "baseline", "repository is a Git worktree", lambda: git("rev-parse", "--is-inside-work-tree") == "true")
    v.guarded("BASE-002", "baseline", "CST-EXP-06 tag resolves to frozen base", lambda: git("rev-parse", BASE_TAG + "^{}") == BASE_COMMIT)
    v.guarded("BASE-003", "baseline", "frozen base is an ancestor of current HEAD", lambda: subprocess.run(["git", "merge-base", "--is-ancestor", BASE_COMMIT, "HEAD"], cwd=ROOT).returncode == 0)
    v.guarded("BASE-004", "baseline", "repository has no whitespace errors", lambda: subprocess.run(["git", "diff", "--check"], cwd=ROOT, capture_output=True).returncode == 0)
    if require_clean:
        v.guarded("BASE-005", "baseline", "working tree is clean", lambda: git("status", "--porcelain") == "")
    else:
        v.skip("BASE-005", "baseline", "clean-tree requirement not requested for this validation pass")


def check_imported_sources(v: Validation) -> None:
    checksum_path = ROOT / "inputs/normative/cst-tt-00/IMPORTED_SHA256SUMS.txt"
    v.check("SRC-001", "provenance", checksum_path.is_file(), "imported-source checksum ledger exists")
    if not checksum_path.is_file():
        return
    rows = []
    for line in checksum_path.read_text(encoding="utf-8").splitlines():
        digest, rel = line.split(maxsplit=1)
        rows.append((digest, rel.lstrip("*")))
    v.check("SRC-002", "provenance", len(rows) == 17, f"checksum ledger contains 17 imported surfaces (found {len(rows)})")
    for idx, (digest, rel) in enumerate(rows, 1):
        path = ROOT / rel
        v.check(f"SRC-FILE-{idx:03d}", "provenance", path.is_file(), f"imported surface exists: {rel}")
        if path.is_file():
            v.check(f"SRC-HASH-{idx:03d}", "provenance", sha256(path) == digest, f"imported surface hash matches: {rel}")
    tex = sorted((ROOT / "inputs/reference_surfaces/temporal_audit").glob("*.tex"))
    v.check("SRC-003", "provenance", len(tex) == 9, f"nine time/holonomy/consciousness source manuscripts imported (found {len(tex)})")
    required_fragments = ["Time_as_a_Theory_Artifact", "Holonomy_with_Memory", "Protocol_Trap", "Critical_Pairs_Holonomy", "Consciousness"]
    names = "\n".join(p.name for p in tex)
    for idx, fragment in enumerate(required_fragments, 1):
        v.check(f"SRC-TOPIC-{idx:02d}", "provenance", fragment in names, f"source set includes {fragment}")


def check_toolchains(v: Validation) -> None:
    v.check("TOOL-001", "toolchain", (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.28.0", "Lean toolchain is pinned to v4.28.0")
    pyproject = (ROOT / "pyproject.toml").read_text(encoding="utf-8")
    for idx, token in enumerate((">=3.13,<3.14", "pytest==9.0.2", "jsonschema==4.26.0", "setuptools==82.0.1"), 1):
        v.check(f"TOOL-PIN-{idx:02d}", "toolchain", token in pyproject, f"pyproject pins {token}")
    v.check("TOOL-006", "toolchain", sys.version_info[:2] == (3, 13), f"running Python is 3.13 (found {sys.version.split()[0]})")
    lean = shutil.which("lean")
    lake = shutil.which("lake")
    if lean and lake:
        proc = subprocess.run([lake, "build"], cwd=ROOT, text=True, capture_output=True)
        v.check("TOOL-LEAN-BUILD", "toolchain", proc.returncode == 0, "pinned Lean scaffold compiles with lake build")
    else:
        v.skip("TOOL-LEAN-BUILD", "toolchain", "lean/lake unavailable in execution container; external build remains required")
    status = load_json(ROOT / "formal/TOOLCHAIN_STATUS.json")
    v.check("TOOL-STATUS-001", "toolchain", status["lean_toolchain"] == "leanprover/lean4:v4.28.0", "toolchain status records pinned Lean version")
    v.check("TOOL-STATUS-002", "toolchain", status["compile_status"] == "not-run-lean-and-lake-unavailable", "toolchain status does not misreport a Lean build")


def check_lean_surface(v: Validation) -> None:
    modules = sorted((ROOT / "CSTTT").rglob("*.lean"))
    v.check("LEAN-001", "lean-static", len(modules) == 15, f"fifteen Lean modules exist below CSTTT (found {len(modules)})")
    v.check("LEAN-002", "lean-static", (ROOT / "CSTTT.lean").is_file(), "Lean library root exists")
    root_text = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    for idx, module in enumerate(modules, 1):
        rel = module.relative_to(ROOT).with_suffix("")
        import_name = ".".join(rel.parts)
        v.check(f"LEAN-IMPORT-{idx:03d}", "lean-static", f"import {import_name}" in root_text, f"root imports {import_name}")
        text = module.read_text(encoding="utf-8")
        v.check(f"LEAN-NAMESPACE-{idx:03d}", "lean-static", "namespace CSTTT" in text, f"module uses CSTTT namespace: {rel}")
        v.check(f"LEAN-END-{idx:03d}", "lean-static", text.rstrip().endswith(("end CSTTT", "end CSTTT.Prospects")), f"module closes namespace: {rel}")
        v.check(f"LEAN-BALANCE-{idx:03d}", "lean-static", text.count("(") == text.count(")") and text.count("[") == text.count("]"), f"delimiter counts balance: {rel}")
    forbidden_proof = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")
    all_text = "\n".join(path.read_text(encoding="utf-8") for path in modules)
    v.check("LEAN-003", "lean-static", forbidden_proof.search(all_text) is None, "Lean scaffold contains no sorry/admit/axiom/unsafe placeholder")
    findings = scan_primitive_tree(ROOT)
    v.check("LEAN-004", "circularity", findings == [], f"primitive circularity scan has no findings (found {len(findings)})")

    definitions = read_csv(ROOT / "registries/DEFINITION_REGISTRY.csv")
    for idx, row in enumerate(definitions, 1):
        module = ROOT / row["module"]
        v.check(f"LEAN-DEF-FILE-{idx:03d}", "lean-static", module.is_file(), f"registered definition module exists: {row['definition_id']}")
        if module.is_file():
            v.check(f"LEAN-DEF-NAME-{idx:03d}", "lean-static", row["name"] in module.read_text(encoding="utf-8"), f"registered definition appears in source: {row['definition_id']}")

    statements_text = (ROOT / "CSTTT/Prospects/Statements.lean").read_text(encoding="utf-8")
    for idx, row in enumerate(read_csv(ROOT / "registries/THEOREM_REGISTRY.csv"), 1):
        name = row["lean_statement"].split(".")[-1]
        v.check(f"LEAN-STMT-{idx:03d}", "lean-static", name in statements_text, f"registered statement interface exists: {row['theorem_id']}")

    import_rules = {
        "CSTTT/Temporal": ("CSTTT.Corridor", "CSTTT.Targets"),
        "CSTTT/Package": ("CSTTT.Corridor", "CSTTT.Autonomy", "CSTTT.Targets"),
        "CSTTT/Transport": ("CSTTT.Corridor", "CSTTT.Targets"),
        "CSTTT/Corridor": ("CSTTT.Targets",),
        "CSTTT/Autonomy": ("CSTTT.Corridor", "CSTTT.Targets"),
    }
    counter = 0
    for directory, forbidden_imports in import_rules.items():
        for module in sorted((ROOT / directory).rglob("*.lean")):
            text = module.read_text(encoding="utf-8")
            for forbidden in forbidden_imports:
                counter += 1
                v.check(f"LEAN-LAYER-{counter:03d}", "typing", f"import {forbidden}" not in text, f"{module.relative_to(ROOT)} does not reverse-import {forbidden}")


def check_python(v: Validation) -> None:
    py_files = sorted((ROOT / "src/cst_tt").glob("*.py"))
    v.check("PY-001", "python", len(py_files) >= 12, f"Python scaffold has at least twelve modules (found {len(py_files)})")
    for idx, path in enumerate(py_files, 1):
        try:
            py_compile.compile(str(path), doraise=True)
            ok = True
        except py_compile.PyCompileError:
            ok = False
        v.check(f"PY-COMPILE-{idx:03d}", "python", ok, f"Python source compiles: {path.relative_to(ROOT)}")
    proc = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=ROOT, text=True, capture_output=True, env={**os.environ, "PYTHONPATH": str(SRC)})
    detail = "pytest suite passes"
    if proc.returncode != 0:
        detail += f"; stdout={proc.stdout[-2000:]}; stderr={proc.stderr[-2000:]}"
    v.check("PY-TESTS", "python", proc.returncode == 0, detail)


def check_registries(v: Validation) -> None:
    expected = {
        "CLAIM_LANE_REGISTRY.csv": 7,
        "DEFINITION_REGISTRY.csv": 39,
        "THEOREM_REGISTRY.csv": 35,
        "TEMPORAL_AMENDMENT_MAP.csv": 20,
        "TOY_MODEL_REGISTRY.csv": 21,
        "CERTIFICATE_SCHEMA_REGISTRY.csv": 8,
        "ASSUMPTION_LEDGER.csv": 32,
        "KILL_CRITERIA.csv": 14,
        "DEPENDENCY_EDGES.csv": 28,
    }
    registry_rows: dict[str, list[dict[str, str]]] = {}
    for idx, (name, count) in enumerate(expected.items(), 1):
        path = ROOT / "registries" / name
        v.check(f"REG-FILE-{idx:02d}", "registry", path.is_file(), f"registry exists: {name}")
        if path.is_file():
            rows = read_csv(path)
            registry_rows[name] = rows
            v.check(f"REG-COUNT-{idx:02d}", "registry", len(rows) == count, f"{name} has frozen row count {count} (found {len(rows)})")

    theorem_rows = registry_rows.get("THEOREM_REGISTRY.csv", [])
    toy_rows = registry_rows.get("TOY_MODEL_REGISTRY.csv", [])
    theorem_ids = {r["theorem_id"] for r in theorem_rows}
    toy_ids = {r["toy_id"] for r in toy_rows}
    v.check("REG-TH-UNIQUE", "registry", duplicate_values(theorem_rows, "theorem_id") == set(), "theorem identifiers are unique")
    v.check("REG-TH-STMT-UNIQUE", "registry", duplicate_values(theorem_rows, "lean_statement") == set(), "every theorem/no-go row has its own Lean proposition interface")
    v.check("REG-TOY-UNIQUE", "registry", duplicate_values(toy_rows, "toy_id") == set(), "toy identifiers are unique")
    th_pattern = re.compile(r"^(TTH|TTN|TTD|TTF)-\d{2}$")
    toy_pattern = re.compile(r"^(TTM|TFM)-\d{2}$")
    for idx, row in enumerate(theorem_rows, 1):
        v.check(f"REG-TH-ID-{idx:03d}", "registry", bool(th_pattern.match(row["theorem_id"])), f"theorem ID well formed: {row['theorem_id']}")
        v.check(f"REG-TH-STATUS-{idx:03d}", "no-results", row["status"] == "open-scaffold", f"theorem remains open scaffold: {row['theorem_id']}")
        v.check(f"REG-TH-DEPS-{idx:03d}", "registry", split_ids(row["dependencies"]).issubset(theorem_ids), f"theorem dependencies resolve: {row['theorem_id']}")
        v.check(f"REG-TH-TOYS-{idx:03d}", "registry", split_ids(row["toy_dependencies"]).issubset(toy_ids), f"theorem toy links resolve: {row['theorem_id']}")
        v.check(f"REG-TH-CEILING-{idx:03d}", "claim-ceiling", bool(row["claim_ceiling"].strip()), f"theorem has explicit claim ceiling: {row['theorem_id']}")
        legacy_ids = split_ids(row.get("legacy_provenance_ids", ""))
        v.check(
            f"REG-TH-LEGACY-{idx:03d}", "provenance",
            all(re.fullmatch(r"(?:PTH|FTH)-\d{2}", legacy_id) for legacy_id in legacy_ids),
            f"legacy provenance identifiers are well formed: {row['theorem_id']}",
        )
    for idx, row in enumerate(toy_rows, 1):
        v.check(f"REG-TOY-ID-{idx:03d}", "registry", bool(toy_pattern.match(row["toy_id"])), f"toy ID well formed: {row['toy_id']}")
        v.check(f"REG-TOY-STATUS-{idx:03d}", "no-results", row["status"] == "specified-not-implemented", f"toy remains unimplemented: {row['toy_id']}")
        v.check(f"REG-TOY-LINK-{idx:03d}", "registry", split_ids(row["discriminates"]).issubset(theorem_ids), f"toy theorem links resolve: {row['toy_id']}")

    amendment_rows = registry_rows.get("TEMPORAL_AMENDMENT_MAP.csv", [])
    expected_legacy_ids = {f"PTH-{i:02d}" for i in range(1, 13)} | {f"FTH-{i:02d}" for i in range(1, 9)}
    amendment_legacy_ids = {row["legacy_id"] for row in amendment_rows}
    v.check("REG-AMEND-UNIQUE", "provenance", duplicate_values(amendment_rows, "legacy_id") == set(), "legacy theorem identifiers occur once in the amendment map")
    v.check("REG-AMEND-COMPLETE", "provenance", amendment_legacy_ids == expected_legacy_ids, "all twelve PTH and eight FTH provenance identifiers are mapped")
    source_legacy_path = ROOT / "synthesis/FROZEN_THEOREM_FAMILY.csv"
    source_legacy_ids = {row["theorem_id"] for row in read_csv(source_legacy_path)} if source_legacy_path.is_file() else set()
    v.check("REG-AMEND-SOURCE", "provenance", source_legacy_ids == expected_legacy_ids, "the frozen CST-EXP-06 theorem family supplies the same twenty legacy IDs")
    mapped_pairs: set[tuple[str, str]] = set()
    for idx, row in enumerate(amendment_rows, 1):
        mapped = split_ids(row["temporal_ids"])
        v.check(f"REG-AMEND-TARGET-{idx:03d}", "provenance", bool(mapped) and mapped.issubset(theorem_ids), f"temporal amendment targets resolve: {row['legacy_id']}")
        v.check(f"REG-AMEND-STATUS-{idx:03d}", "provenance", row["status"] == "frozen-provenance-map", f"temporal amendment row is frozen: {row['legacy_id']}")
        v.check(f"REG-AMEND-TEXT-{idx:03d}", "provenance", bool(row["temporal_amendment"].strip()), f"temporal amendment is explicit: {row['legacy_id']}")
        mapped_pairs.update((row["legacy_id"], theorem_id) for theorem_id in mapped)
    theorem_legacy_pairs = {
        (legacy_id, row["theorem_id"])
        for row in theorem_rows
        for legacy_id in split_ids(row.get("legacy_provenance_ids", ""))
    }
    v.check("REG-AMEND-CROSSWALK", "provenance", theorem_legacy_pairs == mapped_pairs, "the theorem registry and amendment map encode the same legacy crosswalk")

    lanes = registry_rows.get("CLAIM_LANE_REGISTRY.csv", [])
    v.check("REG-LANES", "claim-ceiling", {r["lane_id"] for r in lanes} == {"S-T", "S-R", "S-L", "A", "R", "O", "M"}, "all seven claim lanes are frozen")
    for idx, row in enumerate(lanes, 1):
        v.check(f"REG-LANE-INHERIT-{idx:02d}", "claim-ceiling", row["inherits_from"] == "none", f"claim lane does not inherit: {row['lane_id']}")

    defs = registry_rows.get("DEFINITION_REGISTRY.csv", [])
    def_ids = {r["definition_id"] for r in defs}
    v.check("REG-DEF-UNIQUE", "registry", duplicate_values(defs, "definition_id") == set(), "definition identifiers are unique")
    for idx, row in enumerate(defs, 1):
        v.check(f"REG-DEF-DEPS-{idx:03d}", "registry", split_ids(row["dependencies"]).issubset(def_ids), f"definition dependencies resolve: {row['definition_id']}")
        v.check(f"REG-DEF-STATUS-{idx:03d}", "registry", row["status"] == "frozen-scaffold", f"definition status frozen: {row['definition_id']}")

    assumptions = registry_rows.get("ASSUMPTION_LEDGER.csv", [])
    by_name = {r["name"]: r for r in assumptions}
    for idx, name in enumerate(("H-FELT-TIME", "H-CONT-TIME", "A1", "A2-P", "H-CERT-SOUND", "H-RECOGNITION", "H-PERSONAL-IDENTITY"), 1):
        v.check(f"REG-ASSUME-{idx:02d}", "claim-ceiling", name in by_name, f"separately priced assumption present: {name}")
    if "H-FELT-TIME" in by_name:
        v.check("REG-ASSUME-TIME-1", "claim-ceiling", by_name["H-FELT-TIME"]["tier"] == "interpretive", "H-FELT-TIME is interpretive")
    if "H-CONT-TIME" in by_name:
        v.check("REG-ASSUME-TIME-2", "claim-ceiling", by_name["H-CONT-TIME"]["tier"] == "interpretive", "H-CONT-TIME is interpretive")

    kills = registry_rows.get("KILL_CRITERIA.csv", [])
    for idx, row in enumerate(kills, 1):
        v.check(f"REG-KILL-{idx:03d}", "kill-policy", row["status"] == "armed", f"kill criterion armed: {row['kill_id']}")

    project = load_json(ROOT / "registries/PROJECT_REGISTRY.json")
    v.check("REG-PROJECT-1", "no-results", project["scientific_results_landed"] == 0, "project registry records zero landed scientific results")
    v.check("REG-PROJECT-2", "claim-ceiling", project["claim_ceiling"] == "structural precursor only", "project claim ceiling is structural precursor only")


def check_schemas(v: Validation) -> None:
    rows = read_csv(ROOT / "registries/CERTIFICATE_SCHEMA_REGISTRY.csv")
    for idx, row in enumerate(rows, 1):
        schema_path = ROOT / "schemas/certificates" / row["file"]
        example_path = ROOT / row["scaffold_example"]
        v.check(f"SCHEMA-FILE-{idx:02d}", "schema", schema_path.is_file(), f"schema exists: {row['schema_id']}")
        v.check(f"SCHEMA-EXAMPLE-{idx:02d}", "schema", example_path.is_file(), f"scaffold example exists: {row['schema_id']}")
        if schema_path.is_file() and example_path.is_file():
            schema = load_json(schema_path)
            try:
                Draft202012Validator.check_schema(schema)
                schema_ok = True
            except Exception:
                schema_ok = False
            v.check(f"SCHEMA-VALID-{idx:02d}", "schema", schema_ok, f"JSON Schema is Draft 2020-12 valid: {row['schema_id']}")
            errors = list(Draft202012Validator(schema).iter_errors(load_json(example_path))) if schema_ok else [object()]
            v.check(f"SCHEMA-DATA-{idx:02d}", "schema", errors == [], f"scaffold example validates: {row['schema_id']}")
            text = example_path.read_text(encoding="utf-8")
            v.check(f"SCHEMA-NO-CERT-{idx:02d}", "no-results", '"certified"' not in text and '"checked-finite-countermodel"' not in text, f"example makes no landed claim: {row['schema_id']}")
    aggregate = load_json(ROOT / "examples/scaffold/temporal_fiach_certificate.scaffold.json")
    v.check("SCHEMA-AGG-1", "claim-ceiling", aggregate["claim_ceiling"] == "structural-precursor-only", "aggregate certificate has structural claim ceiling")
    v.check("SCHEMA-AGG-2", "no-results", aggregate["route_status"] == "unresolved", "aggregate scaffold does not prefill route status")
    autonomy = load_json(ROOT / "examples/scaffold/autonomy_certificate.scaffold.json")
    removed_flags = [autonomy[k] for k in ("source_removed", "bridge_removed", "migration_controller_removed", "external_decoder_removed", "external_scheduler_removed", "undeclared_repair_removed")]
    v.check("SCHEMA-AUTO-1", "no-results", not any(removed_flags), "autonomy scaffold does not preclaim withdrawal success")


def check_docs_and_boundaries(v: Validation) -> None:
    docs = {
        "TARGET_FREEZE.md": ["TemporalFIACH_e", "TemporalSignature", "DirectSuccessorCertificate", "H-FELT-TIME", "H-CONT-TIME"],
        "FORMALIZATION_CONTRACT.md": ["Python is intended to enumerate", "Python enumeration is never a proof oracle", "Temporal", "Corridor", "Targets"],
        "THEOREM_AND_TOY_REGISTRY.md": ["open-scaffold", "specified-not-implemented"],
        "TEMPORAL_AMENDMENT_MAP.md": ["PTH-01", "PTH-12", "FTH-01", "FTH-08", "split"],
        "ASSUMPTION_AND_CLAIM_CEILING.md": ["H-FELT-TIME", "H-CONT-TIME", "H-PERSONAL-IDENTITY"],
        "CIRCULARITY_AND_TYPING_POLICY.md": ["Holonomy is not an endogenous arrow", "Direct successor is not silently identified"],
        "PHASE_BOUNDARY.md": ["no proved scientific theorem", "no positive Temporal-FIACH or IAPS witness"],
        "RESTORE_AND_BUILD.md": ["lake build", "validate_tt00.py"],
    }
    counter = 0
    for name, phrases in docs.items():
        path = ROOT / "docs" / name
        counter += 1
        v.check(f"DOC-FILE-{counter:02d}", "documentation", path.is_file(), f"documentation exists: {name}")
        if path.is_file():
            text = path.read_text(encoding="utf-8")
            for phrase in phrases:
                counter += 1
                v.check(f"DOC-CONTENT-{counter:03d}", "documentation", phrase in text, f"{name} contains required boundary: {phrase}")
    target_text = (ROOT / "docs/TARGET_FREEZE.md").read_text(encoding="utf-8")
    v.check("DOC-TARGET-1", "typing", target_text.index("## Temporal object frozen before lineage") < target_text.index("## Overlap and direct-successor classes"), "target freeze presents signature before corridor")
    v.check("DOC-TARGET-2", "claim-ceiling", "personal survival" in target_text and "numerical identity" in target_text, "target freeze states identity nonclaims")
    root_restore = ROOT / "RESTORE_AND_VERIFY.md"
    v.check("DOC-ROOT-RESTORE-1", "documentation", root_restore.is_file(), "root restore-and-verify instructions exist")
    if root_restore.is_file():
        restore_text = root_restore.read_text(encoding="utf-8")
        v.check("DOC-ROOT-RESTORE-2", "documentation", "CST-TT-00-v1" in restore_text and "lake build" in restore_text, "root restore instructions name the phase tag and external Lean build")
    repro_path = ROOT / "config/REPRODUCIBILITY.json"
    v.check("REPRO-001", "reproducibility", repro_path.is_file(), "fixed reproducibility policy exists")
    if repro_path.is_file():
        repro = load_json(repro_path)
        v.check("REPRO-002", "reproducibility", repro["canonical_seed"] == 0, "canonical enumeration seed is zero")
        v.check("REPRO-003", "reproducibility", repro["python_hash_seed"] == 0, "Python hash seed is frozen to zero")
        v.check("REPRO-004", "reproducibility", repro["randomized_search_enabled"] is False, "randomized search is disabled in phase zero")
        v.check("REPRO-005", "no-results", repro["scientific_result_generated"] is False, "reproducibility policy records no generated scientific result")


def check_no_results(v: Validation) -> None:
    forbidden_dirs = [ROOT / "results", ROOT / "certificates/landed", ROOT / "toys/generated"]
    for idx, path in enumerate(forbidden_dirs, 1):
        v.check(f"NORES-DIR-{idx:02d}", "no-results", not path.exists(), f"no landed-result directory exists: {path.relative_to(ROOT)}")
    status = load_json(ROOT / "formal/TOOLCHAIN_STATUS.json")
    v.check("NORES-LEAN", "no-results", status["compile_status"].startswith("not-run"), "Lean compilation is not misreported")
    all_registry_text = "\n".join(path.read_text(encoding="utf-8") for path in (ROOT / "registries").glob("*" ) if path.is_file())
    for idx, token in enumerate(("proved-scientific", "checked-finite-countermodel,", "positive-witness-landed"), 1):
        v.check(f"NORES-TOKEN-{idx:02d}", "no-results", token not in all_registry_text, f"no landed-result token appears in registries: {token}")


def write_reports(v: Validation) -> None:
    counts = Counter(r.status for r in v.results)
    categories: dict[str, Counter[str]] = {}
    for result in v.results:
        categories.setdefault(result.category, Counter())[result.status] += 1
    payload = {
        "phase": PHASE,
        "date": "2026-08-10",
        "status": "PASS" if not v.failures else "FAIL",
        "counts": dict(sorted(counts.items())),
        "category_counts": {k: dict(sorted(c.items())) for k, c in sorted(categories.items())},
        "lean_compile": "SKIP: lean/lake unavailable" if shutil.which("lean") is None or shutil.which("lake") is None else "attempted",
        "results": [asdict(r) for r in v.results],
    }
    (ROOT / "manifests/CST-TT-00_VALIDATION_RESULTS.json").write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")

    lines = [
        "# CST-TT-00 Validation Report",
        "",
        f"**Overall:** {payload['status']}",
        f"**Checks:** {counts.get('PASS', 0)} passed; {counts.get('FAIL', 0)} failed; {counts.get('SKIP', 0)} skipped",
        "",
        "## Category summary",
        "",
        "| Category | PASS | FAIL | SKIP |",
        "|---|---:|---:|---:|",
    ]
    for category, c in sorted(categories.items()):
        lines.append(f"| {category} | {c.get('PASS', 0)} | {c.get('FAIL', 0)} | {c.get('SKIP', 0)} |")
    lines.extend(["", "## Environment-dependent check", ""])
    if shutil.which("lean") and shutil.which("lake"):
        lines.append("The pinned Lean build was attempted; see the toolchain category above.")
    else:
        lines.append("`lean` and `lake` were unavailable in the execution container. No Lean compilation pass is claimed. The repository pins Lean 4.28.0, contains an external `lake build` command, and passed the static source, import-layer, circularity, schema, Python, and registry checks.")
    skipped = [r for r in v.results if r.status == "SKIP"]
    if skipped:
        lines.extend(["", "## Skipped checks", ""])
        for result in skipped:
            lines.append(f"- `{result.check_id}` — {result.detail}")
    if v.failures:
        lines.extend(["", "## Failures", ""])
        for result in v.failures:
            lines.append(f"- `{result.check_id}` — {result.detail}")
    else:
        lines.extend(["", "## Exit assessment", "", "All environment-independent CST-TT-00 gates pass. The only unperformed gate is actual Lean compilation because the executable was unavailable; this is explicitly deferred and not counted as a pass."])
    (ROOT / "manifests/CST-TT-00_VALIDATION_REPORT.md").write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--require-clean", action="store_true")
    args = parser.parse_args()
    v = Validation()
    check_baseline(v, args.require_clean)
    check_imported_sources(v)
    check_toolchains(v)
    check_lean_surface(v)
    check_python(v)
    check_registries(v)
    check_schemas(v)
    check_docs_and_boundaries(v)
    check_no_results(v)
    write_reports(v)
    counts = Counter(r.status for r in v.results)
    print(f"{PHASE}: {counts.get('PASS', 0)} passed, {counts.get('FAIL', 0)} failed, {counts.get('SKIP', 0)} skipped")
    if v.failures:
        for result in v.failures[:20]:
            print(f"FAIL {result.check_id}: {result.detail}")
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
