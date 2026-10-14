#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE_TAG = "CST-TT-01-v1"
PHASE_TAG = "CST-TT-02-v1"

INPUT_FILES = [
    "CSTTT.lean",
    "CSTTT/Package/FiniteGluing.lean",
    "CSTTT/Package/TemporalPackage.lean",
    "examples/scaffold/package_certificate.scaffold.json",
    "examples/scaffold/package_control_certificate.scaffold.json",
    "examples/scaffold/staged_package_certificate.scaffold.json",
    "schemas/certificates/package_certificate.schema.json",
    "schemas/certificates/package_control_certificate.schema.json",
    "schemas/certificates/staged_package_certificate.schema.json",
    "schemas/registries/theorem_registry_row.schema.json",
    "src/cst_tt/__init__.py",
    "src/cst_tt/package_auditor.py",
    "src/cst_tt/package_gluing.py",
    "scripts/build_tt02_assets.py",
    "scripts/tt02_data.py",
    "scripts/validate_tt02.py",
]


def generated_paths(root: Path) -> list[str]:
    fixed = [
        "CHANGELOG.md",
        "README.md",
        "RESTORE_AND_VERIFY.md",
        "STATE.md",
        "STATUS.md",
        "changelog/CST-TT-02.md",
        "config/REPRODUCIBILITY.json",
        "docs/ACYCLIC_GLUING_THEOREM.md",
        "docs/C6_TEMPORAL_SUBSTANCE.md",
        "docs/INTEGRATED_PACKAGE_SEMANTICS.md",
        "docs/PACKAGE_CONTROL_SUITE.md",
        "docs/PHASE_BOUNDARY.md",
        "docs/STAGED_PACKAGE_ASSEMBLY.md",
        "docs/THEOREM_AND_TOY_REGISTRY.md",
        "formal/README.md",
        "formal/TOOLCHAIN_STATUS.json",
        "formal/certificates/packages/BOUNDED_GLUING_EXHAUSTION.json",
        "formal/certificates/packages/PKG-POS-01-TARGET.certificate.json",
        "formal/certificates/packages/PKG-POS-02-SOURCE.certificate.json",
        "formal/certificates/packages/STG-POS-01.certificate.json",
        "manifests/CST-TT-02_COMPLETION_REPORT.md",
        "manifests/CST-TT-02_MODEL_CERTIFICATE_DELTA.csv",
        "manifests/CST-TT-02_PHASE_SUMMARY.json",
        "manifests/CST-TT-02_THEOREM_STATUS_DELTA.csv",
        "manifests/PHASE_SUMMARY.json",
        "models/packages/PKG-POS-01-TARGET.model.json",
        "models/packages/PKG-POS-02-SOURCE.model.json",
        "models/packages/STG-POS-01.assembly.json",
        "registries/CERTIFICATE_SCHEMA_REGISTRY.csv",
        "registries/DEFINITION_REGISTRY.csv",
        "registries/KILL_CRITERIA.csv",
        "registries/PACKAGE_CONTROL_REGISTRY.csv",
        "registries/PACKAGE_OBLIGATION_REGISTRY.csv",
        "registries/PACKAGE_WITNESS_REGISTRY.csv",
        "registries/PROJECT_REGISTRY.json",
        "registries/STAGED_ASSEMBLY_OBLIGATION_REGISTRY.csv",
        "registries/THEOREM_REGISTRY.csv",
        "registries/TOY_MODEL_REGISTRY.csv",
    ]
    dynamic = [
        *(f"models/packages/controls/PC-{i:02d}.model.json" for i in range(1, 18)),
        "models/packages/controls/SC-01.assembly.json",
        *(f"formal/certificates/packages/controls/PC-{i:02d}.certificate.json" for i in range(1, 18)),
        "formal/certificates/packages/controls/SC-01.certificate.json",
    ]
    paths = fixed + dynamic
    missing = [rel for rel in paths if not (root / rel).is_file()]
    if missing:
        raise FileNotFoundError(f"missing generated surfaces under {root}: {missing}")
    return paths


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def copy_inputs(clone: Path) -> None:
    for rel in INPUT_FILES:
        source = ROOT / rel
        target = clone / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    target_tests = clone / "tests"
    if target_tests.exists():
        shutil.rmtree(target_tests)
    shutil.copytree(ROOT / "tests", target_tests, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))


def run(command: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    env.update({"PYTHONHASHSEED": "0", "PYTHONPATH": "src:scripts"})
    return subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)


def main() -> int:
    baseline_paths = generated_paths(ROOT)
    baseline = {rel: digest(ROOT / rel) for rel in baseline_paths}
    build: subprocess.CompletedProcess[str]
    tests: subprocess.CompletedProcess[str] | None = None
    validation: subprocess.CompletedProcess[str] | None = None
    rebuilt: dict[str, str] = {}
    with tempfile.TemporaryDirectory(prefix="cst-tt-02-rebuild-") as tmp:
        clone = Path(tmp) / "repo"
        subprocess.run(["git", "clone", "--quiet", "--no-hardlinks", str(ROOT), str(clone)], check=True, text=True)
        subprocess.run(["git", "checkout", "--quiet", BASE_TAG], cwd=clone, check=True)
        subprocess.run(["git", "tag", "-d", PHASE_TAG], cwd=clone, check=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        copy_inputs(clone)
        build = run([sys.executable, "scripts/build_tt02_assets.py"], clone)
        if build.returncode == 0:
            tests = run([sys.executable, "-m", "pytest", "-q"], clone)
        if tests is not None and tests.returncode == 0:
            validation = run([sys.executable, "scripts/validate_tt02.py", "--no-write"], clone)
        if validation is not None and validation.returncode == 0:
            rebuilt = {rel: digest(clone / rel) for rel in baseline_paths if (clone / rel).is_file()}

    mismatches = [rel for rel in baseline_paths if baseline.get(rel) != rebuilt.get(rel)]
    status = (
        build.returncode == 0
        and tests is not None and tests.returncode == 0
        and validation is not None and validation.returncode == 0
        and not mismatches
    )
    payload = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": "CST-TT-02",
        "base_tag": BASE_TAG,
        "status": "PASS" if status else "FAIL",
        "generated_surface_count": len(baseline_paths),
        "byte_identical_surface_count": len(baseline_paths) - len(mismatches),
        "builder_returncode": build.returncode,
        "pytest_returncode": tests.returncode if tests is not None else None,
        "validator_returncode": validation.returncode if validation is not None else None,
        "mismatches": mismatches,
        "surfaces": [
            {"path": rel, "sha256": baseline[rel], "reproduced": baseline.get(rel) == rebuilt.get(rel)}
            for rel in baseline_paths
        ],
    }
    out_json = ROOT / "manifests/CST-TT-02_REBUILD_VERIFICATION.json"
    out_md = ROOT / "manifests/CST-TT-02_REBUILD_VERIFICATION.md"
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    lines = [
        "# CST-TT-02 Portable Rebuild Verification",
        "",
        f"**Status:** {payload['status']}",
        f"**Base:** `{BASE_TAG}`",
        f"**Generated surfaces:** {len(baseline_paths)}",
        f"**Byte-identical reproductions:** {payload['byte_identical_surface_count']}/{len(baseline_paths)}",
        f"**Builder / tests / validator return codes:** {payload['builder_returncode']} / {payload['pytest_returncode']} / {payload['validator_returncode']}",
        "",
        "The verifier cloned the frozen CST-TT-01 base, overlaid only the CST-TT-02 semantic, schema, Lean, builder, validator, and test inputs, rebuilt the phase, reran tests and validation, and compared every deterministic generated surface byte-for-byte.",
    ]
    if mismatches:
        lines.extend(["", "## Mismatches", ""] + [f"- `{rel}`" for rel in mismatches])
    out_md.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"CST-TT-02 rebuild: {payload['status']} ({payload['byte_identical_surface_count']}/{len(baseline_paths)})")
    if not status:
        if build.returncode != 0:
            print((build.stdout + build.stderr)[-3000:], file=sys.stderr)
        if tests is not None and tests.returncode != 0:
            print((tests.stdout + tests.stderr)[-3000:], file=sys.stderr)
        if validation is not None and validation.returncode != 0:
            print((validation.stdout + validation.stderr)[-3000:], file=sys.stderr)
        if mismatches:
            print("mismatches: " + ", ".join(mismatches), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
