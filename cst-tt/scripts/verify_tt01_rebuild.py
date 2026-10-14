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
BASE_TAG = "CST-TT-00-v1"
PHASE_TAG = "CST-TT-01-v1"

INPUT_FILES = [
    "CSTTT.lean",
    "CSTTT/Countermodels/Kernel.lean",
    "pyproject.toml",
    "schemas/certificates/countermodel_certificate.schema.json",
    "schemas/registries/theorem_registry_row.schema.json",
    "src/cst_tt/__init__.py",
    "src/cst_tt/countermodels.py",
    "scripts/build_tt01_assets.py",
    "scripts/validate_tt01.py",
]


def generated_paths(root: Path) -> list[str]:
    fixed = [
        "registries/COUNTERMODEL_REGISTRY.csv",
        "registries/MINIMALITY_LEDGER.csv",
        "registries/THEOREM_REGISTRY.csv",
        "registries/TOY_MODEL_REGISTRY.csv",
        "registries/CERTIFICATE_SCHEMA_REGISTRY.csv",
        "registries/PROJECT_REGISTRY.json",
        "config/REPRODUCIBILITY.json",
        "docs/NEGATIVE_KERNEL.md",
        "docs/COUNTERMODEL_MINIMALITY.md",
        "docs/THEOREM_AND_TOY_REGISTRY.md",
        "docs/PHASE_BOUNDARY.md",
        "formal/README.md",
        "formal/TOOLCHAIN_STATUS.json",
        "README.md",
        "STATE.md",
        "STATUS.md",
        "CHANGELOG.md",
        "changelog/CST-TT-01.md",
        "RESTORE_AND_VERIFY.md",
        "manifests/CST-TT-01_SEARCH_SUMMARY.json",
        "manifests/CST-TT-01_PHASE_SUMMARY.json",
        "manifests/PHASE_SUMMARY.json",
        "manifests/CST-TT-01_THEOREM_STATUS_DELTA.csv",
        "manifests/CST-TT-01_MODEL_CERTIFICATE_DELTA.csv",
        "manifests/CST-TT-01_COMPLETION_REPORT.md",
        "models/countermodels/INDEX.md",
        "formal/certificates/countermodels/INDEX.md",
    ]
    dynamic = [
        *(f"models/countermodels/CM-{i:02d}.model.json" for i in range(1, 16)),
        *(f"models/countermodels/CM-{i:02d}.md" for i in range(1, 16)),
        *(f"formal/certificates/countermodels/CM-{i:02d}.certificate.json" for i in range(1, 16)),
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
    env.update({"PYTHONHASHSEED": "0", "PYTHONPATH": "src"})
    return subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True)


def main() -> int:
    baseline_paths = generated_paths(ROOT)
    baseline = {rel: digest(ROOT / rel) for rel in baseline_paths}
    with tempfile.TemporaryDirectory(prefix="cst-tt-01-rebuild-") as tmp:
        clone = Path(tmp) / "repo"
        subprocess.run(
            ["git", "clone", "--quiet", "--no-hardlinks", str(ROOT), str(clone)],
            check=True,
            text=True,
        )
        subprocess.run(["git", "checkout", "--quiet", BASE_TAG], cwd=clone, check=True)
        # The source repository may already carry the final phase tag.  A clean-base
        # replay intentionally reconstructs the phase before that tag exists, so remove
        # the cloned local phase tag rather than asking the validator to compare it with
        # the frozen base checkout.
        subprocess.run(
            ["git", "tag", "-d", PHASE_TAG],
            cwd=clone,
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        copy_inputs(clone)
        build = run([sys.executable, "scripts/build_tt01_assets.py"], clone)
        tests = run([sys.executable, "-m", "pytest", "-q"], clone) if build.returncode == 0 else None
        validation = run([sys.executable, "scripts/validate_tt01.py"], clone) if tests and tests.returncode == 0 else None
        rebuilt: dict[str, str] = {}
        if validation and validation.returncode == 0:
            rebuilt = {rel: digest(clone / rel) for rel in baseline_paths if (clone / rel).is_file()}

    mismatches = [rel for rel in baseline_paths if baseline.get(rel) != rebuilt.get(rel)]
    payload = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": "CST-TT-01",
        "base_tag": BASE_TAG,
        "status": "PASS"
        if build.returncode == 0 and tests is not None and tests.returncode == 0 and validation is not None and validation.returncode == 0 and not mismatches
        else "FAIL",
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
    out_json = ROOT / "manifests/CST-TT-01_REBUILD_VERIFICATION.json"
    out_md = ROOT / "manifests/CST-TT-01_REBUILD_VERIFICATION.md"
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    lines = [
        "# CST-TT-01 Portable Rebuild Verification",
        "",
        f"**Status:** {payload['status']}",
        f"**Base:** `{BASE_TAG}`",
        f"**Generated surfaces:** {len(baseline_paths)}",
        f"**Byte-identical reproductions:** {payload['byte_identical_surface_count']}/{len(baseline_paths)}",
        f"**Builder / tests / validator return codes:** {payload['builder_returncode']} / {payload['pytest_returncode']} / {payload['validator_returncode']}",
        "",
        "The verifier cloned the frozen CST-TT-00 base, overlaid only the CST-TT-01 source, schema, Lean, builder, validator, and test inputs, rebuilt the phase, reran tests and validation, and compared every deterministic generated surface byte-for-byte.",
    ]
    if mismatches:
        lines.extend(["", "## Mismatches", ""] + [f"- `{rel}`" for rel in mismatches])
    out_md.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(
        f"CST-TT-01 rebuild: {payload['status']} "
        f"({payload['byte_identical_surface_count']}/{len(baseline_paths)})"
    )
    if payload["status"] != "PASS":
        if build.returncode != 0:
            print(build.stdout[-2000:] + build.stderr[-2000:], file=sys.stderr)
        if tests is not None and tests.returncode != 0:
            print(tests.stdout[-2000:] + tests.stderr[-2000:], file=sys.stderr)
        if validation is not None and validation.returncode != 0:
            print(validation.stdout[-2000:] + validation.stderr[-2000:], file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
