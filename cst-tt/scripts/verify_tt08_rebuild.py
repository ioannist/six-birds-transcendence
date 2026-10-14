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

from tt08_surfaces import generated_paths

ROOT = Path(__file__).resolve().parents[1]
BASE_TAG = "CST-TT-07A-v1"
BASE_COMMIT = "7ba9167d39e6751706a7ad7152911c61f77af6af"
PHASE_TAG = "CST-TT-08-v1"

INPUT_FILES = (
    "pyproject.toml",
    "requirements-lock.txt",
    "scripts/tt08_data.py",
    "scripts/tt08_surfaces.py",
    "scripts/build_tt08_assets.py",
    "scripts/validate_tt08.py",
    "scripts/verify_tt08_rebuild.py",
    "scripts/finalize_tt08_manifest.py",
    "scripts/run_tt08_checks.sh",
    "scripts/rebuild_tt08.py",
)

INPUT_DIRECTORIES = (
    "inputs/reference_surfaces/additional_sbt",
)


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def copy_file(source: Path, target: Path) -> None:
    if not source.is_file():
        raise FileNotFoundError(source)
    target.parent.mkdir(parents=True, exist_ok=True)
    shutil.copy2(source, target)


def copy_inputs(clone: Path) -> None:
    for rel in INPUT_FILES:
        copy_file(ROOT / rel, clone / rel)
    for rel in INPUT_DIRECTORIES:
        source = ROOT / rel
        target = clone / rel
        if not source.is_dir():
            raise FileNotFoundError(source)
        if target.exists():
            shutil.rmtree(target)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copytree(source, target, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))
    target_tests = clone / "tests"
    if target_tests.exists():
        shutil.rmtree(target_tests)
    shutil.copytree(ROOT / "tests", target_tests, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))


def run(command: list[str], cwd: Path, timeout: int = 1800) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    env.update({"PYTHONHASHSEED": "0", "PYTHONPATH": "src:scripts", "TERM": "dumb"})
    return subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True, timeout=timeout)


def main() -> int:
    baseline_paths = [path.relative_to(ROOT).as_posix() for path in generated_paths(ROOT)]
    missing_baseline = [rel for rel in baseline_paths if not (ROOT / rel).is_file()]
    if missing_baseline:
        raise FileNotFoundError(f"missing baseline generated surfaces: {missing_baseline}")
    baseline = {rel: digest(ROOT / rel) for rel in baseline_paths}

    build: subprocess.CompletedProcess[str] | None = None
    tests: subprocess.CompletedProcess[str] | None = None
    validation: subprocess.CompletedProcess[str] | None = None
    rebuilt: dict[str, str] = {}
    base_resolved = ""

    with tempfile.TemporaryDirectory(prefix="cst-tt-08-rebuild-") as tmp:
        clone = Path(tmp) / "repo"
        subprocess.run(["git", "clone", "--quiet", "--no-hardlinks", str(ROOT), str(clone)], check=True, text=True)
        subprocess.run(["git", "checkout", "--quiet", BASE_TAG], cwd=clone, check=True)
        subprocess.run(
            ["git", "tag", "-d", PHASE_TAG],
            cwd=clone,
            check=False,
            stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL,
        )
        base_resolved = subprocess.run(
            ["git", "rev-parse", BASE_TAG + "^{}"],
            cwd=clone,
            check=True,
            text=True,
            capture_output=True,
        ).stdout.strip()
        copy_inputs(clone)

        build = run([sys.executable, "scripts/build_tt08_assets.py"], clone)
        if build.returncode == 0:
            tests = run([sys.executable, "-m", "pytest", "-q"], clone)
        if tests is not None and tests.returncode == 0:
            validation = run([sys.executable, "scripts/validate_tt08.py", "--no-write"], clone)
        if validation is not None and validation.returncode == 0:
            rebuilt = {rel: digest(clone / rel) for rel in baseline_paths if (clone / rel).is_file()}

    mismatches = [rel for rel in baseline_paths if baseline.get(rel) != rebuilt.get(rel)]
    status = bool(
        base_resolved == BASE_COMMIT
        and build is not None
        and build.returncode == 0
        and tests is not None
        and tests.returncode == 0
        and validation is not None
        and validation.returncode == 0
        and not mismatches
    )
    payload = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": "CST-TT-08",
        "base_tag": BASE_TAG,
        "base_commit": BASE_COMMIT,
        "base_resolved": base_resolved,
        "status": "PASS" if status else "FAIL",
        "generated_surface_count": len(baseline_paths),
        "byte_identical_surface_count": len(baseline_paths) - len(mismatches),
        "builder_returncode": build.returncode if build is not None else None,
        "pytest_returncode": tests.returncode if tests is not None else None,
        "validator_returncode": validation.returncode if validation is not None else None,
        "mismatches": mismatches,
        "surfaces": [
            {"path": rel, "sha256": baseline[rel], "reproduced": baseline.get(rel) == rebuilt.get(rel)}
            for rel in baseline_paths
        ],
    }
    out_json = ROOT / "manifests/CST-TT-08_REBUILD_VERIFICATION.json"
    out_md = ROOT / "manifests/CST-TT-08_REBUILD_VERIFICATION.md"
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    lines = [
        "# CST-TT-08 Portable Rebuild Verification",
        "",
        f"**Status:** {payload['status']}",
        f"**Base:** `{BASE_TAG}` / `{BASE_COMMIT}`",
        f"**Generated surfaces:** {len(baseline_paths)}",
        f"**Byte-identical reproductions:** {payload['byte_identical_surface_count']}/{len(baseline_paths)}",
        f"**Builder / tests / validator return codes:** {payload['builder_returncode']} / {payload['pytest_returncode']} / {payload['validator_returncode']}",
        "",
        "The verifier cloned the frozen CST-TT-07A base, overlaid only the CST-TT-08 declarative data, deterministic builder, final validator, release utilities, pinned Python dependencies, additional SBT provenance sources, and final tests, then regenerated the complete authoritative release surface. It reran the full Python test suite and CST-TT-08 phase validator and compared every deterministic generated surface byte-for-byte.",
        "",
        "No Lean compilation pass is inferred from this rebuild. Compiler availability and theorem promotion remain separately reported; all generic proof-source results retain `conditional` status until the pinned Lean build succeeds.",
    ]
    if mismatches:
        lines.extend(["", "## Mismatches", ""] + [f"- `{rel}`" for rel in mismatches])
    out_md.write_text("\n".join(lines) + "\n", encoding="utf-8")
    (ROOT / "manifests/REBUILD_VERIFICATION.json").write_text(out_json.read_text(encoding="utf-8"), encoding="utf-8")
    (ROOT / "manifests/REBUILD_VERIFICATION.md").write_text(out_md.read_text(encoding="utf-8"), encoding="utf-8")
    print(f"CST-TT-08 rebuild: {payload['status']} ({payload['byte_identical_surface_count']}/{len(baseline_paths)})")

    if not status:
        for name, proc in (("builder", build), ("pytest", tests), ("validator", validation)):
            if proc is not None and proc.returncode != 0:
                print(f"\n{name} output:\n{(proc.stdout + proc.stderr)[-20000:]}", file=sys.stderr)
        if mismatches:
            print("mismatches: " + ", ".join(mismatches), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
