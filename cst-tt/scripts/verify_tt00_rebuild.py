#!/usr/bin/env python3
from __future__ import annotations

import hashlib
import json
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
GENERATED = [
    "registries/CLAIM_LANE_REGISTRY.csv",
    "registries/DEFINITION_REGISTRY.csv",
    "registries/THEOREM_REGISTRY.csv",
    "registries/TEMPORAL_AMENDMENT_MAP.csv",
    "registries/TOY_MODEL_REGISTRY.csv",
    "registries/CERTIFICATE_SCHEMA_REGISTRY.csv",
    "registries/ASSUMPTION_LEDGER.csv",
    "registries/KILL_CRITERIA.csv",
    "registries/DEPENDENCY_EDGES.csv",
    "registries/PROJECT_REGISTRY.json",
    "docs/TARGET_FREEZE.md",
    "docs/FORMALIZATION_CONTRACT.md",
    "docs/THEOREM_AND_TOY_REGISTRY.md",
    "docs/TEMPORAL_AMENDMENT_MAP.md",
    "docs/ASSUMPTION_AND_CLAIM_CEILING.md",
    "docs/CIRCULARITY_AND_TYPING_POLICY.md",
    "docs/PHASE_BOUNDARY.md",
    "docs/RESTORE_AND_BUILD.md",
    "manifests/TT00_ASSET_SUMMARY.json",
    "manifests/CST-TT-00_THEOREM_STATUS_DELTA.csv",
    "manifests/CST-TT-00_MODEL_CERTIFICATE_DELTA.csv",
]


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main() -> int:
    baseline = {rel: digest(ROOT / rel) for rel in GENERATED}
    with tempfile.TemporaryDirectory(prefix="cst-tt-00-rebuild-") as tmp:
        clone = Path(tmp) / "repo"
        shutil.copytree(
            ROOT,
            clone,
            ignore=shutil.ignore_patterns(".git", ".pytest_cache", "__pycache__", "*.pyc", ".lake"),
        )
        for rel in GENERATED:
            (clone / rel).unlink(missing_ok=True)
        proc = subprocess.run(
            [sys.executable, "scripts/build_tt00_assets.py"],
            cwd=clone,
            text=True,
            capture_output=True,
        )
        rebuilt = {rel: digest(clone / rel) for rel in GENERATED if (clone / rel).is_file()}
    mismatches = [rel for rel in GENERATED if baseline.get(rel) != rebuilt.get(rel)]
    payload = {
        "phase": "CST-TT-00",
        "status": "PASS" if proc.returncode == 0 and not mismatches else "FAIL",
        "generated_surface_count": len(GENERATED),
        "builder_returncode": proc.returncode,
        "mismatches": mismatches,
        "surfaces": [
            {"path": rel, "sha256": baseline[rel], "reproduced": baseline.get(rel) == rebuilt.get(rel)}
            for rel in GENERATED
        ],
    }
    (ROOT / "manifests/CST-TT-00_REBUILD_VERIFICATION.json").write_text(
        json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8"
    )
    lines = [
        "# CST-TT-00 Portable Rebuild Verification",
        "",
        f"**Status:** {payload['status']}",
        f"**Generated surfaces:** {len(GENERATED)}",
        f"**Byte-identical reproductions:** {sum(1 for row in payload['surfaces'] if row['reproduced'])}/{len(GENERATED)}",
        "",
        "The verification copied the repository without `.git` or caches, deleted every deterministic CST-TT-00 registry/document surface, reran `scripts/build_tt00_assets.py`, and compared SHA-256 hashes.",
    ]
    if mismatches:
        lines.extend(["", "## Mismatches", ""] + [f"- `{rel}`" for rel in mismatches])
    (ROOT / "manifests/CST-TT-00_REBUILD_VERIFICATION.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"CST-TT-00 rebuild: {payload['status']} ({len(GENERATED)-len(mismatches)}/{len(GENERATED)})")
    return 0 if payload["status"] == "PASS" else 1


if __name__ == "__main__":
    raise SystemExit(main())
