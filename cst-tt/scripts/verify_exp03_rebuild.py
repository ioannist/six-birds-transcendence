#!/usr/bin/env python3
"""Run a portable deterministic rebuild check for CST-EXP-03."""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import shutil
import subprocess
import tempfile
from pathlib import Path


def sha(path: Path) -> str:
    h=hashlib.sha256()
    with path.open("rb") as fh:
        for chunk in iter(lambda:fh.read(1024*1024),b""):
            h.update(chunk)
    return h.hexdigest()


def generated_surfaces(root: Path) -> list[str]:
    paths=[
        "README.md","STATE.md","STATUS.md","CHANGELOG.md","changelog/CST-EXP-03.md",
        "candidates/TRANSPORTED_OBJECT_ATLAS.md","candidates/transported_object_registry.csv",
        "candidates/INVARIANT_ATLAS.md","candidates/invariant_registry.csv",
        "candidates/BRIDGE_DESIGN_SPACE.md","candidates/bridge_registry.csv",
        "candidates/CANDIDATE_REGISTRY.json","candidates/CANDIDATE_COMPARISON_GUIDE.md",
        "candidates/EXIT_GATE_AUDIT.md","candidates/candidate_design_space.dot",
        "candidates/candidate_design_space.svg","candidates/candidate_design_space.png",
        "candidates/brainstorms/INDEX.md","candidates/brainstorms/BRAINSTORM_FREEZE.sha256",
        "candidates/target_schemas/INDEX.md",
        "ledgers/candidate_feature_matrix.csv","ledgers/new_primitive_register.csv",
        "ledgers/candidate_scenario_verdicts.csv","ledgers/candidate_question_responses.csv",
        "ledgers/candidate_anti_conflation_audit.csv","ledgers/candidate_asset_crosswalk.csv",
        "ledgers/candidate_assumption_matrix.csv","ledgers/candidate_discriminator_crosswalk.csv",
        "ledgers/candidate_divergence_matrix.csv","ledgers/decision_log.csv","ledgers/DECISION_LOG.md",
        "ledgers/REJECTED_DEFAULTS.md","ledgers/UNRESOLVED_QUESTIONS.md",
        "manifests/EXP03_ASSET_SUMMARY.json","synthesis/CST-EXP-03_CANDIDATE_GENERATION_SYNTHESIS.md",
    ]
    paths += [f"candidates/brainstorms/{x}" for x in [
        "01_quotient_algebraic.md","02_dynamical_process.md","03_error_correcting_logical_object.md",
        "04_closure_realization.md","05_viability_agent.md","06_branching_philosophical.md","07_wild_hybrid.md",
    ]]
    paths += [f"candidates/target_schemas/TS-{i:02d}.md" for i in range(1,11)]
    return paths


def copy_repo(src: Path, dst: Path) -> None:
    def ignore(path: str, names: list[str]):
        drop={".git","__pycache__"}
        return [n for n in names if n in drop or n.endswith(".pyc")]
    shutil.copytree(src,dst,ignore=ignore)


def run(cmd: list[str], cwd: Path) -> subprocess.CompletedProcess[str]:
    env=os.environ.copy(); env["PYTHONDONTWRITEBYTECODE"]="1"
    return subprocess.run(cmd,cwd=cwd,env=env,text=True,stdout=subprocess.PIPE,stderr=subprocess.STDOUT,check=False)


def main() -> None:
    ap=argparse.ArgumentParser(); ap.add_argument("--repo",default="."); args=ap.parse_args()
    root=Path(args.repo).resolve(); surfaces=generated_surfaces(root)
    missing=[x for x in surfaces if not (root/x).is_file()]
    if missing: raise SystemExit(f"missing baseline surfaces: {missing}")
    baseline={x:sha(root/x) for x in surfaces}
    with tempfile.TemporaryDirectory(prefix="cst_exp03_rebuild_") as td:
        rebuilt=Path(td)/"cst-exploration"; copy_repo(root,rebuilt)
        commands=[]
        commands.append(run(["python","scripts/build_exp03_assets.py","--repo",".","--stage","all"],rebuilt))
        if shutil.which("dot"):
            commands.append(run(["dot","-Tsvg","candidates/candidate_design_space.dot","-o","candidates/candidate_design_space.svg"],rebuilt))
            commands.append(run(["dot","-Tpng","candidates/candidate_design_space.dot","-o","candidates/candidate_design_space.png"],rebuilt))
        # Remove caches before validation.
        for p in rebuilt.rglob("__pycache__"): shutil.rmtree(p,ignore_errors=True)
        for p in rebuilt.rglob("*.pyc"): p.unlink(missing_ok=True)
        commands.append(run(["python","scripts/validate_exp03.py","--repo",".","--skip-manifest"],rebuilt))
        rc=[c.returncode for c in commands]
        rebuilt_hash={x:sha(rebuilt/x) if (rebuilt/x).is_file() else "MISSING" for x in surfaces}
        mismatches=[x for x in surfaces if baseline[x] != rebuilt_hash[x]]
        val=json.loads((rebuilt/"manifests/VALIDATION_RESULTS.json").read_text(encoding="utf-8"))
        status="pass" if not any(rc) and not mismatches and val.get("status") == "pass" else "fail"
        record={
            "project":"CST-EXP","phase":"CST-EXP-03","date":"2026-08-09","status":status,
            "method":"copy repository without .git/cache; regenerate all phase-03 deterministic assets; regenerate diagrams when Graphviz is available; run validator with manifest checks skipped; compare SHA-256 against baseline",
            "surface_count":len(surfaces),"identical_surface_count":len(surfaces)-len(mismatches),
            "mismatches":mismatches,"command_return_codes":rc,
            "validator_status":val.get("status"),"validator_checks_passed":val.get("checks_passed"),"validator_checks_total":val.get("checks_total"),
            "graphviz_used":bool(shutil.which("dot")),
        }
        (root/"manifests/REBUILD_VERIFICATION.json").write_text(json.dumps(record,indent=2)+"\n",encoding="utf-8")
        md=f"""# CST-EXP-03 Portable-Rebuild Verification

**Status:** {status.upper()}  
**Date:** 2026-08-09  
**Deterministic surfaces compared:** {len(surfaces)}  
**Byte-identical surfaces:** {len(surfaces)-len(mismatches)}/{len(surfaces)}  
**Rebuilt validator:** {val.get('checks_passed')}/{val.get('checks_total')} {str(val.get('status')).upper()}  
**Graphviz regeneration used:** {'yes' if shutil.which('dot') else 'no; retained binaries were compared'}

## Method

A clean temporary copy was made without Git metadata or Python caches. The CST-EXP-03 builder regenerated every phase text/CSV/JSON surface. Candidate design-space SVG and PNG files were regenerated when Graphviz was available. The rebuilt copy then ran `scripts/validate_exp03.py --skip-manifest`. SHA-256 hashes for all declared deterministic surfaces were compared against the source snapshot.

## Result

{'All declared deterministic surfaces reproduced byte-for-byte, and the rebuilt validator passed.' if status == 'pass' else 'The rebuild did not reproduce cleanly; see the JSON record for return codes and mismatches.'}

Mismatches: {', '.join(mismatches) if mismatches else 'none'}.

This verifies deterministic repository reconstruction and internal validation. It does not establish the scientific correctness of any candidate schema.
"""
        (root/"manifests/REBUILD_VERIFICATION.md").write_text(md,encoding="utf-8")
        print(f"CST-EXP-03 portable rebuild: {status.upper()} ({len(surfaces)-len(mismatches)}/{len(surfaces)} identical; validator {val.get('checks_passed')}/{val.get('checks_total')})")
        if status != "pass":
            for c in commands:
                if c.returncode: print(c.stdout)
            raise SystemExit(1)


if __name__ == "__main__":
    main()
