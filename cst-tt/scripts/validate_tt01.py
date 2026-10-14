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
from typing import Callable

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "src"
if str(SRC) not in sys.path:
    sys.path.insert(0, str(SRC))

from cst_tt.circularity import scan_primitive_tree  # noqa: E402
from cst_tt.countermodels import enumerate_all, recheck  # noqa: E402
from cst_tt.registry import duplicate_values, read_csv  # noqa: E402

PHASE = "CST-TT-01"
BASE_TAG = "CST-TT-00-v1"
BASE_COMMIT = "65b3ab0f94564cee1d16ffb4513045319aaaf6ef"
PHASE_TAG = "CST-TT-01-v1"


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


def check_baseline(v: Validation, require_clean: bool, require_tag: bool) -> None:
    v.guarded("BASE-001", "baseline", "repository is a Git worktree", lambda: git("rev-parse", "--is-inside-work-tree") == "true")
    v.guarded("BASE-002", "baseline", "CST-TT-00 tag resolves to frozen base", lambda: git("rev-parse", BASE_TAG + "^{}") == BASE_COMMIT)
    v.guarded(
        "BASE-003",
        "baseline",
        "frozen CST-TT-00 base is an ancestor of current HEAD",
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
    pins = (">=3.13,<3.14", "pytest==9.0.2", "jsonschema==4.26.0", "setuptools==82.0.1", 'version = "0.1.0"')
    for index, token in enumerate(pins, 1):
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
    v.check("TOOL-STATUS-1", "toolchain", status.get("phase") == PHASE, "toolchain status names CST-TT-01")
    v.check("TOOL-STATUS-2", "toolchain", status.get("explicit_countermodel_proof_source_count") == 15, "toolchain status records fifteen proof surfaces")
    v.check("TOOL-STATUS-3", "toolchain", status.get("compile_status") in {"not-run-lean-and-lake-unavailable", "compiled"}, "toolchain status does not overclaim compilation")
    v.check("TOOL-STATUS-4", "toolchain", status.get("static_lean_source_audit_status") == "passed-by-cst-tt-01-static-suite", "toolchain status records the static Lean audit")


def check_python(v: Validation) -> None:
    py_files = sorted([*SRC.rglob("*.py"), *Path(ROOT / "scripts").glob("*.py")])
    v.check("PY-001", "python", len(py_files) >= 30, f"Python source/script bank present ({len(py_files)} files)")
    for index, path in enumerate(py_files, 1):
        try:
            py_compile.compile(str(path), doraise=True)
            ok = True
        except py_compile.PyCompileError:
            ok = False
        v.check(f"PY-COMPILE-{index:03d}", "python", ok, f"Python compiles: {path.relative_to(ROOT)}")
    proc = subprocess.run([sys.executable, "-m", "pytest", "-q"], cwd=ROOT, env={**dict(__import__("os").environ), "PYTHONPATH": "src"}, text=True, capture_output=True)
    detail = "pytest suite passes"
    if proc.returncode != 0:
        detail += f": {proc.stdout[-1000:]} {proc.stderr[-1000:]}"
    v.check("PY-TESTS", "python", proc.returncode == 0, detail)


def check_provenance(v: Validation) -> None:
    ledger = ROOT / "inputs/normative/cst-tt-00/IMPORTED_SHA256SUMS.txt"
    v.check("PROV-001", "provenance", ledger.is_file(), "frozen temporal-audit source checksum ledger exists")
    if ledger.is_file():
        rows = []
        for line in ledger.read_text(encoding="utf-8").splitlines():
            digest, rel = line.split(maxsplit=1)
            rows.append((digest, rel.lstrip("*")))
        v.check("PROV-002", "provenance", len(rows) == 17, f"seventeen frozen imported surfaces listed (found {len(rows)})")
        for index, (digest, rel) in enumerate(rows, 1):
            path = ROOT / rel
            v.check(f"PROV-FILE-{index:03d}", "provenance", path.is_file(), f"imported surface exists: {rel}")
            if path.is_file():
                v.check(f"PROV-HASH-{index:03d}", "provenance", sha256(path) == digest, f"imported surface hash matches: {rel}")


def check_countermodels(v: Validation) -> None:
    outcomes = enumerate_all()
    v.check("CM-COUNT", "countermodels", len(outcomes) == 15, f"fifteen countermodel families enumerate (found {len(outcomes)})")
    v.check("CM-CANDIDATES", "countermodels", sum(row.candidates_explored for row in outcomes) == 3657, "total bounded candidates explored is 3,657")
    ids = tuple(row.spec.countermodel_id for row in outcomes)
    v.check("CM-IDS", "countermodels", ids == tuple(f"CM-{i:02d}" for i in range(1, 16)), "countermodel identifiers are complete and ordered")
    for index, outcome in enumerate(outcomes, 1):
        prefix = f"CM-{index:02d}"
        v.check(f"{prefix}-QUAL", "countermodels", outcome.check.qualifies, f"{prefix} satisfies every declared premise and failed-conclusion check")
        v.check(f"{prefix}-MIN", "countermodels", outcome.minimality_status == "proved-by-exhaustive-bounded-search", f"{prefix} carries bounded relative-minimality result")
        v.check(f"{prefix}-RECHECK", "countermodels", recheck(prefix, outcome.witness.model) == outcome.check, f"{prefix} independently rechecks")
        v.check(f"{prefix}-SMALLER", "countermodels", outcome.smaller_candidates_explored >= 0, f"{prefix} reports smaller candidates")
        v.check(f"{prefix}-SAME", "countermodels", outcome.same_size_qualifying_candidates >= 1, f"{prefix} has a canonical qualifying witness at minimal size")
    detached = next(row for row in outcomes if row.spec.countermodel_id == "CM-02")
    model = detached.witness.model
    v.check("KILL-FIACH-04-1", "kill-criteria", model["exact_temporal_copy"] is True and model["target_package_pass"] is True and model["target_post_copy_autonomous"] is True, "detached exact copy passes endpoint package/autonomy premises")
    v.check("KILL-FIACH-04-2", "kill-criteria", model["strict_overlap_corridor"] is False, "detached exact copy fails strict overlap corridor")
    v.check("KILL-FIACH-04-3", "kill-criteria", model["mixed_stage_count"] == 0, "detached copy is excluded for the intended mixed-stage reason")


def check_certificates(v: Validation) -> None:
    schema_path = ROOT / "schemas/certificates/countermodel_certificate.schema.json"
    schema = load_json(schema_path)
    assert isinstance(schema, dict)
    try:
        Draft202012Validator.check_schema(schema)
        schema_ok = True
    except Exception:
        schema_ok = False
    v.check("CERT-SCHEMA", "certificates", schema_ok, "countermodel certificate schema is valid Draft 2020-12")
    validator = Draft202012Validator(schema)
    rows = read_csv(ROOT / "registries/COUNTERMODEL_REGISTRY.csv")
    v.check("CERT-REG-COUNT", "certificates", len(rows) == 15, f"countermodel registry has fifteen rows (found {len(rows)})")
    v.check("CERT-REG-UNIQUE", "certificates", duplicate_values(rows, "countermodel_id") == set(), "countermodel IDs are unique")
    kernel = (ROOT / "CSTTT/Countermodels/Kernel.lean").read_text(encoding="utf-8")
    for index, row in enumerate(rows, 1):
        cm_id = row["countermodel_id"]
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        card_path = ROOT / row["model_card_ref"]
        v.check(f"CERT-MODEL-{index:02d}", "certificates", model_path.is_file(), f"{cm_id} finite model exists")
        v.check(f"CERT-CARD-{index:02d}", "certificates", card_path.is_file(), f"{cm_id} human-readable model card exists")
        v.check(f"CERT-FILE-{index:02d}", "certificates", cert_path.is_file(), f"{cm_id} certificate exists")
        if not model_path.is_file() or not cert_path.is_file() or not card_path.is_file():
            continue
        model = load_json(model_path)
        cert = load_json(cert_path)
        assert isinstance(model, dict) and isinstance(cert, dict)
        errors = sorted(validator.iter_errors(cert), key=lambda e: list(e.path))
        v.check(f"CERT-VALID-{index:02d}", "certificates", errors == [], f"{cm_id} certificate validates against schema")
        v.check(f"CERT-HASH-{index:02d}", "certificates", cert.get("finite_model_sha256") == sha256(model_path), f"{cm_id} certificate binds exact model bytes")
        v.check(f"CERT-STATUS-{index:02d}", "certificates", cert.get("result_status") == "checked-finite-countermodel", f"{cm_id} result status is checked finite countermodel")
        v.check(f"CERT-CEILING-{index:02d}", "certificates", cert.get("claim_ceiling") == "structural-boundary-only", f"{cm_id} retains structural claim ceiling")
        declaration = row["lean_declaration"].split(".")[-1]
        v.check(f"CERT-LEAN-{index:02d}", "certificates", f"theorem {declaration}" in kernel, f"{cm_id} Lean theorem source exists")
        check = recheck(cm_id, model["model"])
        v.check(f"CERT-RECHECK-{index:02d}", "certificates", check.qualifies, f"{cm_id} stored model independently rechecks")


def check_registries(v: Validation) -> None:
    theorem_rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    v.check("REG-THEOREM-COUNT", "registries", len(theorem_rows) == 35, "theorem registry retains 35 rows")
    statuses = Counter(row["status"] for row in theorem_rows)
    v.check("REG-THEOREM-STATUS", "registries", statuses == Counter({"open-scaffold": 21, "checked-finite-countermodel": 14}), f"theorem status split is 21 open / 14 checked ({dict(statuses)})")
    for index, row in enumerate(theorem_rows, 1):
        expected = "checked-finite-countermodel" if row["theorem_id"].startswith("TTN-") else "open-scaffold"
        v.check(f"REG-THEOREM-{index:02d}", "registries", row["status"] == expected, f"{row['theorem_id']} has correct phase-one status")
    toy_rows = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    toy_status = Counter(row["status"] for row in toy_rows)
    v.check("REG-TOY-COUNT", "registries", len(toy_rows) == 21, "toy registry retains 21 rows")
    v.check("REG-TOY-STATUS", "registries", toy_status == Counter({"checked-negative-instance": 14, "specified-not-implemented": 7}), f"toy status split is 14 checked negative / 7 unimplemented ({dict(toy_status)})")
    project = load_json(ROOT / "registries/PROJECT_REGISTRY.json")
    assert isinstance(project, dict)
    project_expectations = {
        "phase": PHASE,
        "phase_base_tag": BASE_TAG,
        "phase_base_commit": BASE_COMMIT,
        "scientific_results_landed": 15,
        "checked_finite_countermodels": 15,
        "generic_theorems_proved": 0,
        "positive_handoff_witnesses": 0,
        "negative_kernel_status": "frozen",
    }
    for index, (key, value) in enumerate(project_expectations.items(), 1):
        v.check(f"REG-PROJECT-{index:02d}", "registries", project.get(key) == value, f"project registry {key}={value!r}")
    minimality_rows = read_csv(ROOT / "registries/MINIMALITY_LEDGER.csv")
    v.check("REG-MIN-COUNT", "registries", len(minimality_rows) == 15, "minimality ledger has fifteen rows")
    v.check("REG-MIN-IDS", "registries", {row["countermodel_id"] for row in minimality_rows} == {f"CM-{i:02d}" for i in range(1, 16)}, "minimality ledger covers every countermodel")
    for index, row in enumerate(minimality_rows, 1):
        v.check(f"REG-MIN-STATUS-{index:02d}", "registries", row["minimality_status"] == "proved-by-exhaustive-bounded-search", f"{row['countermodel_id']} has bounded minimality status")
        v.check(f"REG-MIN-SMALL-{index:02d}", "registries", row["smaller_qualifying_candidates"] == "0", f"{row['countermodel_id']} has no smaller qualifying generated candidate")
    kill_rows = read_csv(ROOT / "registries/KILL_CRITERIA.csv")
    v.check("REG-KILL", "registries", len(kill_rows) == 14 and all(row["status"] == "armed" for row in kill_rows), "all fourteen kill criteria remain armed")
    amendment = read_csv(ROOT / "registries/TEMPORAL_AMENDMENT_MAP.csv")
    expected_legacy = {f"PTH-{i:02d}" for i in range(1, 13)} | {f"FTH-{i:02d}" for i in range(1, 9)}
    v.check("REG-AMEND", "registries", len(amendment) == 20 and {row["legacy_id"] for row in amendment} == expected_legacy, "all 20 frozen PTH/FTH prospects remain mapped")


def check_lean(v: Validation) -> None:
    modules = sorted((ROOT / "CSTTT").rglob("*.lean"))
    v.check("LEAN-COUNT", "lean-static", len(modules) == 16, f"sixteen Lean modules exist under CSTTT (found {len(modules)})")
    root_text = (ROOT / "CSTTT.lean").read_text(encoding="utf-8")
    for index, module in enumerate(modules, 1):
        import_name = ".".join(module.relative_to(ROOT).with_suffix("").parts)
        v.check(f"LEAN-IMPORT-{index:02d}", "lean-static", f"import {import_name}" in root_text, f"root imports {import_name}")
        text = module.read_text(encoding="utf-8")
        v.check(f"LEAN-NS-{index:02d}", "lean-static", "namespace CSTTT" in text, f"{import_name} uses CSTTT namespace")
        v.check(f"LEAN-DELIM-{index:02d}", "lean-static", text.count("(") == text.count(")") and text.count("[") == text.count("]"), f"{import_name} delimiter counts balance")
    all_text = "\n".join(path.read_text(encoding="utf-8") for path in modules)
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe)\b")
    v.check("LEAN-NO-HOLES", "lean-static", forbidden.search(all_text) is None, "Lean sources contain no sorry/admit/axiom/unsafe placeholder")
    findings = scan_primitive_tree(ROOT)
    v.check("LEAN-CIRC", "circularity", findings == [], f"primitive verdict-vocabulary scan has no findings (found {len(findings)})")
    kernel = ROOT / "CSTTT/Countermodels/Kernel.lean"
    v.check("LEAN-KERNEL", "lean-static", kernel.is_file() and kernel.stat().st_size > 10_000, "explicit countermodel kernel source is present")
    if kernel.is_file():
        text = kernel.read_text(encoding="utf-8")
        for index in range(1, 16):
            v.check(f"LEAN-CM-{index:02d}", "lean-static", f"cm{index:02d}_" in text, f"kernel contains CM-{index:02d} theorem surface")
        for token in ("sameSubject", "personalIdentity", "survivesAs", "isConscious"):
            v.check(f"LEAN-NONCLAIM-{token}", "claim-ceiling", token not in text, f"kernel excludes verdict primitive {token}")


def check_docs(v: Validation) -> None:
    docs = {
        "docs/NEGATIVE_KERNEL.md": ("fifteen deterministic finite countermodels", "None establishes or refutes consciousness"),
        "docs/COUNTERMODEL_MINIMALITY.md": ("Minimality is always relative", "No claim of absolute minimality"),
        "docs/PHASE_BOUNDARY.md": ("no positive Temporal-FIACH", "CST-TT-02"),
        "README.md": ("CST-TT-01", "no positive Temporal-FIACH witness"),
        "STATE.md": ("Checked finite countermodels: 15", "Detached-copy kill criterion: not triggered"),
        "manifests/CST-TT-01_COMPLETION_REPORT.md": ("3,657 deterministic finite candidates", "Temporal-IAPS remains locked"),
        "RESTORE_AND_VERIFY.md": ("CST-TT-01-v1", "lake build"),
    }
    counter = 0
    for rel, phrases in docs.items():
        path = ROOT / rel
        counter += 1
        v.check(f"DOC-FILE-{counter:02d}", "documentation", path.is_file(), f"documentation exists: {rel}")
        if path.is_file():
            text = path.read_text(encoding="utf-8")
            for phrase_index, phrase in enumerate(phrases, 1):
                v.check(f"DOC-CONTENT-{counter:02d}-{phrase_index}", "documentation", phrase in text, f"{rel} contains required phrase: {phrase}")
    negative = (ROOT / "docs/NEGATIVE_KERNEL.md").read_text(encoding="utf-8")
    for index in range(1, 16):
        v.check(f"DOC-CM-{index:02d}", "documentation", f"### CM-{index:02d}" in negative, f"negative-kernel document contains CM-{index:02d} card")


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
        "# CST-TT-01 Validation Report",
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
    parser.add_argument("--no-write", action="store_true", help="run checks without rewriting validation artifacts")
    args = parser.parse_args()

    v = Validation()
    check_baseline(v, args.require_clean, args.require_tag)
    check_toolchain(v)
    check_python(v)
    check_provenance(v)
    check_countermodels(v)
    check_certificates(v)
    check_registries(v)
    check_lean(v)
    check_docs(v)
    report, payload = render(v)
    if not args.no_write:
        manifest_dir = ROOT / "manifests"
        manifest_dir.mkdir(parents=True, exist_ok=True)
        (manifest_dir / "CST-TT-01_VALIDATION_REPORT.md").write_text(report, encoding="utf-8")
        (manifest_dir / "CST-TT-01_VALIDATION_RESULTS.json").write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(f"CST-TT-01 validation: {payload['status']} — {payload['passed']} passed, {payload['failed']} failed, {payload['skipped']} skipped")
    return 0 if not v.failures else 1


if __name__ == "__main__":
    raise SystemExit(main())
