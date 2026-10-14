#!/usr/bin/env python3
"""Rebuild CST-EXP-05 from the frozen CST-EXP-04 Git tree and compare deterministic surfaces."""
from __future__ import annotations

import argparse
import hashlib
import json
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE_REF = "CST-EXP-04-v1"


def sha(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda: fh.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def surfaces(root: Path) -> list[str]:
    out = [
        "CHANGELOG.md",
        "README.md",
        "STATE.md",
        "STATUS.md",
        "changelog/CST-EXP-05.md",
        "manifests/EXP05_ASSET_SUMMARY.json",
    ]
    for p in (root / "feasibility").rglob("*"):
        if p.is_file() and p.name != ".gitkeep":
            out.append(str(p.relative_to(root)))
    out.extend(
        [
            "ledgers/DECISION_LOG.md",
            "ledgers/REJECTED_DEFAULTS.md",
            "ledgers/UNRESOLVED_QUESTIONS.md",
            "ledgers/decision_log.csv",
            "ledgers/model_registry.csv",
            "ledgers/model_candidate_discrimination.csv",
            "ledgers/toy_program_registry.csv",
            "ledgers/theorem_dependency_and_risk.csv",
            "ledgers/formalization_surface.csv",
            "ledgers/family_assumption_ladder.csv",
            "ledgers/family_feasibility_registry.csv",
            "ledgers/landing_bundle_registry.csv",
            "ledgers/model_theorem_program_crosswalk.csv",
            "ledgers/no_go_refinement_map.csv",
        ]
    )
    return sorted(set(out))


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=ROOT)
    args = ap.parse_args()
    root = args.root.resolve()

    with tempfile.TemporaryDirectory(prefix="cst-exp05-rebuild-") as td_raw:
        td = Path(td_raw)
        base = td / "repo"
        base.mkdir()

        # Recover the exact committed CST-EXP-04 tree without copying any phase-05 output.
        p1 = subprocess.Popen(["git", "-C", str(root), "archive", BASE_REF], stdout=subprocess.PIPE)
        p2 = subprocess.run(["tar", "-x", "-C", str(base)], stdin=p1.stdout, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        assert p1.stdout is not None
        p1.stdout.close()
        rc = p1.wait()
        if rc or p2.returncode:
            raise RuntimeError(f"git archive/tar failed: {rc}/{p2.returncode}: {p2.stderr.decode()}")
        # The validator checks that an extracted snapshot remains a Git repository.  A local
        # initialization supplies metadata without importing any phase-05 content.
        subprocess.run(["git", "-C", str(base), "init", "-q"], check=True)

        # Supply only the phase-05 generator/validator and the frozen phase-04 manifest pin.
        supplied = [
            "scripts/exp05_data.py",
            "scripts/build_exp05_assets.py",
            "scripts/validate_exp05.py",
            "manifests/CST-EXP-04_MANIFEST.json",
        ]
        for rel in supplied:
            dst = base / rel
            dst.parent.mkdir(parents=True, exist_ok=True)
            shutil.copy2(root / rel, dst)

        build = subprocess.run(
            ["python", str(base / "scripts/build_exp05_assets.py"), "--root", str(base)],
            capture_output=True,
            text=True,
        )
        val = subprocess.run(
            ["python", str(base / "scripts/validate_exp05.py"), "--root", str(base), "--skip-manifest", "--no-write"],
            capture_output=True,
            text=True,
        )

        files = surfaces(root)
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
        result = {
            "schema_version": "1.0",
            "project": "CST-EXP",
            "phase": "CST-EXP-05",
            "status": "pass" if ok else "fail",
            "base_ref": BASE_REF,
            "base_commit": subprocess.check_output(
                ["git", "-C", str(root), "rev-parse", BASE_REF + "^{commit}"], text=True
            ).strip(),
            "method": (
                "git archive of frozen CST-EXP-04 tag plus only the phase-05 data/builder/validator "
                "and frozen prior-manifest pin; regenerate and compare every phase-generated surface byte-for-byte"
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
            "# CST-EXP-05 Portable Rebuild Verification",
            "",
            f"**Result:** {'PASS' if ok else 'FAIL'}",
            "",
            f"- Base ref: `{result['base_ref']}`",
            f"- Base commit: `{result['base_commit']}`",
            f"- Deterministic surfaces compared: {len(files)}",
            f"- Missing: {len(missing)}",
            f"- Byte differences: {len(different)}",
            f"- Rebuilt builder: return code `{build.returncode}`; `{build.stdout.strip()}`",
            f"- Rebuilt pre-validation: `{val.stdout.strip()}`",
            "",
            (
                "The rebuild began from the committed CST-EXP-04 tree, added only the four declared phase-05 inputs, "
                "regenerated the full reconnaissance bank, and compared every generated phase surface byte-for-byte."
            ),
        ]
        if missing:
            lines += ["", "## Missing", "", *[f"- `{x}`" for x in missing]]
        if different:
            lines += [
                "",
                "## Differences",
                "",
                *[
                    f"- `{x['path']}` expected `{x['expected']}`, rebuilt `{x['rebuilt']}`"
                    for x in different
                ],
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
