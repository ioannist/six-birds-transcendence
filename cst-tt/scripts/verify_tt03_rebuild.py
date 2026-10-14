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
BASE_TAG = "CST-TT-02-v1"
BASE_COMMIT = "3abf5b2406f754b43823b68987c7ea409e737fd0"
PHASE_TAG = "CST-TT-03-v1"

INPUT_FILES = [
    "CSTTT.lean",
    "CSTTT/Transport/FiniteExamples.lean",
    "CSTTT/Transport/FiniteTemporalTransport.lean",
    "CSTTT/Transport/RecordArrow.lean",
    "CSTTT/Transport/RouteDiscipline.lean",
    "examples/scaffold/memory_repair_certificate.scaffold.json",
    "examples/scaffold/record_arrow_certificate.scaffold.json",
    "examples/scaffold/route_discipline_certificate.scaffold.json",
    "examples/scaffold/temporal_transport_certificate.scaffold.json",
    "examples/scaffold/transport_control_certificate.scaffold.json",
    "schemas/certificates/memory_repair_certificate.schema.json",
    "schemas/certificates/record_arrow_certificate.schema.json",
    "schemas/certificates/route_discipline_certificate.schema.json",
    "schemas/certificates/temporal_transport_certificate.schema.json",
    "schemas/certificates/transport_control_certificate.schema.json",
    "src/cst_tt/__init__.py",
    "src/cst_tt/transport.py",
    "src/cst_tt/transport_auditor.py",
    "scripts/build_tt03_assets.py",
    "scripts/tt03_data.py",
    "scripts/validate_tt03.py",
]

FIXED_GENERATED = [
    "CHANGELOG.md",
    "README.md",
    "RESTORE_AND_VERIFY.md",
    "STATE.md",
    "STATUS.md",
    "changelog/CST-TT-03.md",
    "config/REPRODUCIBILITY.json",
    "docs/HETEROGENEOUS_TEMPORAL_TRANSPORT.md",
    "docs/MEMORY_OR_FLATNESS_THEOREM.md",
    "docs/RECORD_ARROW_TRANSPORT.md",
    "docs/RESTORE_AND_BUILD.md",
    "docs/ROUTE_DISCIPLINE_AND_CONFLUENCE.md",
    "docs/TRANSPORT_CONTROL_SUITE.md",
    "docs/PHASE_BOUNDARY.md",
    "docs/THEOREM_AND_TOY_REGISTRY.md",
    "formal/README.md",
    "formal/TOOLCHAIN_STATUS.json",
    "manifests/CST-TT-03_COMPLETION_REPORT.md",
    "manifests/CST-TT-03_MODEL_CERTIFICATE_DELTA.csv",
    "manifests/CST-TT-03_PHASE_SUMMARY.json",
    "manifests/CST-TT-03_THEOREM_STATUS_DELTA.csv",
    "manifests/COMPLETION_REPORT.md",
    "manifests/PHASE_SUMMARY.json",
    "registries/CERTIFICATE_SCHEMA_REGISTRY.csv",
    "registries/DEFINITION_REGISTRY.csv",
    "registries/DEPENDENCY_EDGES.csv",
    "registries/KILL_CRITERIA.csv",
    "registries/MEMORY_REPAIR_REGISTRY.csv",
    "registries/PROJECT_REGISTRY.json",
    "registries/RECORD_ARROW_REGISTRY.csv",
    "registries/ROUTE_DISCIPLINE_REGISTRY.csv",
    "registries/TEMPORAL_TRANSPORT_WITNESS_REGISTRY.csv",
    "registries/THEOREM_REGISTRY.csv",
    "registries/TOY_MODEL_REGISTRY.csv",
    "registries/TRANSPORT_CONTROL_REGISTRY.csv",
    "src/cst_tt/__init__.py",
]

GENERATED_DIRS = [
    "models/transport",
    "models/routes",
    "models/memory",
    "models/arrow",
    "formal/certificates/transport",
    "formal/certificates/routes",
    "formal/certificates/memory",
    "formal/certificates/arrow",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def generated_paths(root: Path) -> list[str]:
    paths = set(FIXED_GENERATED)
    for rel_dir in GENERATED_DIRS:
        directory = root / rel_dir
        if not directory.is_dir():
            raise FileNotFoundError(f"missing generated directory: {rel_dir}")
        paths.update(
            path.relative_to(root).as_posix()
            for path in directory.rglob("*")
            if path.is_file() and "__pycache__" not in path.parts and path.suffix != ".pyc"
        )
    missing = [rel for rel in sorted(paths) if not (root / rel).is_file()]
    if missing:
        raise FileNotFoundError(f"missing generated surfaces under {root}: {missing}")
    return sorted(paths)


def copy_inputs(clone: Path) -> None:
    for rel in INPUT_FILES:
        source = ROOT / rel
        if not source.is_file():
            raise FileNotFoundError(source)
        target = clone / rel
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(source, target)
    target_tests = clone / "tests"
    if target_tests.exists():
        shutil.rmtree(target_tests)
    shutil.copytree(ROOT / "tests", target_tests, ignore=shutil.ignore_patterns("__pycache__", "*.pyc"))


def run(command: list[str], cwd: Path, timeout: int = 300) -> subprocess.CompletedProcess[str]:
    env = dict(os.environ)
    env.update({"PYTHONHASHSEED": "0", "PYTHONPATH": "src:scripts", "TERM": "dumb"})
    return subprocess.run(command, cwd=cwd, env=env, text=True, capture_output=True, timeout=timeout)


def main() -> int:
    baseline_paths = generated_paths(ROOT)
    baseline = {rel: digest(ROOT / rel) for rel in baseline_paths}
    build: subprocess.CompletedProcess[str] | None = None
    tests: subprocess.CompletedProcess[str] | None = None
    validation: subprocess.CompletedProcess[str] | None = None
    rebuilt: dict[str, str] = {}
    base_resolved = ""

    with tempfile.TemporaryDirectory(prefix="cst-tt-03-rebuild-") as tmp:
        clone = Path(tmp) / "repo"
        subprocess.run(["git", "clone", "--quiet", "--no-hardlinks", str(ROOT), str(clone)], check=True, text=True)
        subprocess.run(["git", "checkout", "--quiet", BASE_TAG], cwd=clone, check=True)
        subprocess.run(["git", "tag", "-d", PHASE_TAG], cwd=clone, check=False, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        base_resolved = subprocess.run(
            ["git", "rev-parse", BASE_TAG + "^{}"], cwd=clone, check=True, text=True, capture_output=True
        ).stdout.strip()
        copy_inputs(clone)
        build = run([sys.executable, "scripts/build_tt03_assets.py"], clone)
        if build.returncode == 0:
            tests = run([sys.executable, "-m", "pytest", "-q"], clone)
        if tests is not None and tests.returncode == 0:
            validation = run([sys.executable, "scripts/validate_tt03.py", "--no-write"], clone)
        if validation is not None and validation.returncode == 0:
            rebuilt = {rel: digest(clone / rel) for rel in baseline_paths if (clone / rel).is_file()}

    mismatches = [rel for rel in baseline_paths if baseline.get(rel) != rebuilt.get(rel)]
    status = bool(
        base_resolved == BASE_COMMIT
        and build is not None and build.returncode == 0
        and tests is not None and tests.returncode == 0
        and validation is not None and validation.returncode == 0
        and not mismatches
    )
    payload = {
        "schema_version": "1.0",
        "project": "CST-TT",
        "phase": "CST-TT-03",
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
    out_json = ROOT / "manifests/CST-TT-03_REBUILD_VERIFICATION.json"
    out_md = ROOT / "manifests/CST-TT-03_REBUILD_VERIFICATION.md"
    out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    lines = [
        "# CST-TT-03 Portable Rebuild Verification",
        "",
        f"**Status:** {payload['status']}",
        f"**Base:** `{BASE_TAG}` / `{BASE_COMMIT}`",
        f"**Generated surfaces:** {len(baseline_paths)}",
        f"**Byte-identical reproductions:** {payload['byte_identical_surface_count']}/{len(baseline_paths)}",
        f"**Builder / tests / validator return codes:** {payload['builder_returncode']} / {payload['pytest_returncode']} / {payload['validator_returncode']}",
        "",
        "The verifier cloned the frozen CST-TT-02 base, overlaid only the CST-TT-03 semantic, schema, Lean, builder, validator, and test inputs, rebuilt the phase, reran the full Python suite and phase validator, and compared every deterministic generated surface byte-for-byte.",
        "",
        "No Lean compilation pass is inferred from this rebuild; compiler availability remains a separately reported check.",
    ]
    if mismatches:
        lines.extend(["", "## Mismatches", ""] + [f"- `{rel}`" for rel in mismatches])
    out_md.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"CST-TT-03 rebuild: {payload['status']} ({payload['byte_identical_surface_count']}/{len(baseline_paths)})")

    if not status:
        for name, proc in (("builder", build), ("pytest", tests), ("validator", validation)):
            if proc is not None and proc.returncode != 0:
                print(f"\n{name} output:\n{(proc.stdout + proc.stderr)[-6000:]}", file=sys.stderr)
        if mismatches:
            print("mismatches: " + ", ".join(mismatches), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
