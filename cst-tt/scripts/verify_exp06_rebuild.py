#!/usr/bin/env python3
"""Rebuild CST-EXP-06 from the frozen CST-EXP-05 tag and compare generated surfaces."""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE_REF = "CST-EXP-05-v1"


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for block in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(block)
    return h.hexdigest()


def surfaces() -> list[str]:
    return sorted({
        "CHANGELOG.md",
        "README.md",
        "STATE.md",
        "STATUS.md",
        "changelog/CST-EXP-06.md",
        "manifests/EXP06_ASSET_SUMMARY.json",
        "ledgers/DECISION_LOG.md",
        "ledgers/REJECTED_DEFAULTS.md",
        "ledgers/UNRESOLVED_QUESTIONS.md",
        "ledgers/decision_log.csv",
        "synthesis/COPY_VS_CONTINUATION_AUDIT.md",
        "synthesis/EXPLORATION_DOSSIER.md",
        "synthesis/FALLBACK_TARGET_SPECIFICATION.md",
        "synthesis/FINALIST_COMPARISON.md",
        "synthesis/FROZEN_THEOREM_FAMILY.csv",
        "synthesis/FROZEN_WITNESS_SUITE.csv",
        "synthesis/LATER_LANDING_HANDOFF.md",
        "synthesis/PRIMARY_TARGET_SPECIFICATION.md",
        "synthesis/README.md",
        "synthesis/TARGET_REGISTRY.json",
        "synthesis/TARGET_SCENARIO_VERDICTS.csv",
        "synthesis/TARGET_SELECTION_SCORECARD.csv",
        "synthesis/frozen_target_architecture.dot",
        "synthesis/frozen_target_architecture.png",
        "synthesis/frozen_target_architecture.svg",
    })


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=ROOT)
    args = ap.parse_args()
    root = args.root.resolve()

    with tempfile.TemporaryDirectory(prefix="cst-exp06-rebuild-") as td_raw:
        td = Path(td_raw)
        base = td / "repo"
        base.mkdir()

        p1 = subprocess.Popen(["git", "-C", str(root), "archive", BASE_REF], stdout=subprocess.PIPE)
        p2 = subprocess.run(["tar", "-x", "-C", str(base)], stdin=p1.stdout, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        assert p1.stdout is not None
        p1.stdout.close()
        rc = p1.wait()
        if rc or p2.returncode:
            raise RuntimeError(f"git archive/tar failed: {rc}/{p2.returncode}: {p2.stderr.decode()}")
        subprocess.run(["git", "-C", str(base), "init", "-q"], check=True)

        supplied = [
            "scripts/exp06_data.py",
            "scripts/build_exp06_assets.py",
            "scripts/validate_exp06.py",
            "manifests/CST-EXP-05_MANIFEST.json",
        ]
        for rel in supplied:
            dst = base / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(root / rel, dst)

        build = subprocess.run(
            ["python", str(base / "scripts/build_exp06_assets.py"), "--root", str(base)],
            capture_output=True, text=True,
        )
        val = subprocess.run(
            ["python", str(base / "scripts/validate_exp06.py"), "--root", str(base), "--skip-manifest", "--no-write"],
            capture_output=True, text=True,
        )

        files = surfaces()
        missing: list[str] = []
        different: list[dict[str, str]] = []
        for rel in files:
            expected = root / rel
            rebuilt = base / rel
            if not rebuilt.is_file():
                missing.append(rel)
            elif expected.read_bytes() != rebuilt.read_bytes():
                different.append({"path": rel, "expected": sha(expected), "rebuilt": sha(rebuilt)})

        ok = build.returncode == 0 and val.returncode == 0 and not missing and not different
        base_commit = subprocess.check_output(
            ["git", "-C", str(root), "rev-parse", BASE_REF + "^{commit}"], text=True
        ).strip()
        result = {
            "schema_version": "1.0",
            "project": "CST-EXP",
            "phase": "CST-EXP-06",
            "status": "pass" if ok else "fail",
            "base_ref": BASE_REF,
            "base_commit": base_commit,
            "method": (
                "git archive of the frozen CST-EXP-05 tag plus only the phase-06 data, builder, "
                "validator, and prior-manifest pin; regenerate and compare every declared phase surface byte-for-byte"
            ),
            "supplied_files": supplied,
            "surfaces_compared": len(files),
            "missing": missing,
            "different": different,
            "rebuilt_build_returncode": build.returncode,
            "rebuilt_build_stdout": build.stdout.strip(),
            "rebuilt_build_stderr": build.stderr.strip(),
            "rebuilt_prevalidation_returncode": val.returncode,
            "rebuilt_prevalidation_stdout": val.stdout.strip(),
            "rebuilt_prevalidation_stderr": val.stderr.strip(),
        }
        (root / "manifests/REBUILD_VERIFICATION.json").write_text(
            json.dumps(result, indent=2, sort_keys=True) + "\n", encoding="utf-8"
        )

        lines = [
            "# CST-EXP-06 Portable Rebuild Verification",
            "",
            f"**Result:** {'PASS' if ok else 'FAIL'}",
            "",
            f"- Base ref: `{BASE_REF}`",
            f"- Base commit: `{base_commit}`",
            f"- Deterministic surfaces compared: {len(files)}",
            f"- Missing: {len(missing)}",
            f"- Byte differences: {len(different)}",
            f"- Rebuilt builder: return code `{build.returncode}`; `{build.stdout.strip()}`",
            f"- Rebuilt pre-validation: `{val.stdout.strip()}`",
            "",
            (
                "The rebuild began from the committed CST-EXP-05 tree, added only the four declared phase-06 "
                "inputs, regenerated the target-freeze bank, and compared every generated phase surface byte-for-byte."
            ),
        ]
        if missing:
            lines += ["", "## Missing", "", *[f"- `{x}`" for x in missing]]
        if different:
            lines += [
                "", "## Differences", "",
                *[f"- `{x['path']}` expected `{x['expected']}`, rebuilt `{x['rebuilt']}`" for x in different],
            ]
        if build.stderr.strip() or val.stderr.strip():
            lines += ["", "## Tool stderr", "", "```text", build.stderr.strip(), val.stderr.strip(), "```"]
        (root / "manifests/REBUILD_VERIFICATION.md").write_text("\n".join(lines) + "\n", encoding="utf-8")

        print(("PASS" if ok else "FAIL"), len(files), "surfaces")
        if not ok:
            print("build:", build.stdout, build.stderr)
            print("validation:", val.stdout, val.stderr)
            print("missing:", missing)
            print("different:", different[:20])
        return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
