#!/usr/bin/env python3
"""Rebuild CST-EXP-04 from the frozen CST-EXP-03 Git tree and compare deterministic surfaces."""
from __future__ import annotations
import argparse, hashlib, json, shutil, subprocess, tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
BASE_REF='CST-EXP-03-v1'

def sha(p:Path)->str:
    h=hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(1024*1024),b''): h.update(b)
    return h.hexdigest()

def surfaces(root:Path)->list[str]:
    out=['CHANGELOG.md','README.md','STATE.md','STATUS.md','manifests/EXP04_ASSET_SUMMARY.json']
    for p in (root/'challenges').rglob('*'):
        if p.is_file() and p.name!='.gitkeep': out.append(str(p.relative_to(root)))
    for rel in [
      'ledgers/DECISION_LOG.md','ledgers/REJECTED_DEFAULTS.md','ledgers/UNRESOLVED_QUESTIONS.md','ledgers/decision_log.csv',
      'ledgers/assumption_exposure.csv','ledgers/candidate_hard_case_stress.csv','ledgers/candidate_internal_lens_audit.csv',
      'ledgers/candidate_verdicts_by_scenario.csv','ledgers/external_literature_crosswalk.csv','ledgers/no_go_register.csv',
      'ledgers/rejection_and_salvage_log.csv','ledgers/survivor_composition_matrix.csv','ledgers/survivor_family_registry.csv']:
        out.append(rel)
    return sorted(set(out))

def main()->int:
    ap=argparse.ArgumentParser(); ap.add_argument('--root',type=Path,default=ROOT); args=ap.parse_args(); root=args.root.resolve()
    with tempfile.TemporaryDirectory(prefix='cst-exp04-rebuild-') as td:
        td=Path(td); base=td/'repo'; base.mkdir()
        # Recover the exact committed CST-EXP-03 tree.
        p1=subprocess.Popen(['git','-C',str(root),'archive',BASE_REF],stdout=subprocess.PIPE)
        p2=subprocess.run(['tar','-x','-C',str(base)],stdin=p1.stdout,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
        assert p1.stdout is not None; p1.stdout.close(); rc=p1.wait()
        if rc or p2.returncode: raise RuntimeError(f'git archive/tar failed: {rc}/{p2.returncode}: {p2.stderr.decode()}')
        # Supply only the new deterministic builder/validator and inherited manifest pin.
        for rel in ['scripts/exp04_data.py','scripts/build_exp04_assets.py','scripts/validate_exp04.py','manifests/CST-EXP-03_MANIFEST.json']:
            dst=base/rel; dst.parent.mkdir(parents=True,exist_ok=True); shutil.copy2(root/rel,dst)
        subprocess.run(['python',str(base/'scripts/build_exp04_assets.py'),'--root',str(base)],check=True)
        val=subprocess.run(['python',str(base/'scripts/validate_exp04.py'),'--root',str(base),'--skip-manifest','--no-write'],capture_output=True,text=True)
        files=surfaces(root); missing=[]; different=[]
        for rel in files:
            a=root/rel; b=base/rel
            if not b.is_file(): missing.append(rel)
            elif a.read_bytes()!=b.read_bytes(): different.append({'path':rel,'expected':sha(a),'rebuilt':sha(b)})
        ok=val.returncode==0 and not missing and not different
        result={
          'schema_version':'1.0','project':'CST-EXP','phase':'CST-EXP-04','status':'pass' if ok else 'fail',
          'base_ref':BASE_REF,
          'base_commit':subprocess.check_output(['git','-C',str(root),'rev-parse',BASE_REF+'^{commit}'],text=True).strip(),
          'method':'git archive of frozen CST-EXP-03 tag + phase-04 builder/data/validator; compare all generated phase surfaces byte-for-byte',
          'surfaces_compared':len(files),'missing':missing,'different':different,
          'rebuilt_prevalidation_returncode':val.returncode,'rebuilt_prevalidation_stdout':val.stdout.strip(),'rebuilt_prevalidation_stderr':val.stderr.strip(),
        }
        (root/'manifests/REBUILD_VERIFICATION.json').write_text(json.dumps(result,indent=2,sort_keys=True)+'\n',encoding='utf-8')
        lines=['# CST-EXP-04 Portable Rebuild Verification','',f"**Result:** {'PASS' if ok else 'FAIL'}",'',f"- Base ref: `{result['base_ref']}`",f"- Base commit: `{result['base_commit']}`",f"- Deterministic surfaces compared: {len(files)}",f"- Missing: {len(missing)}",f"- Byte differences: {len(different)}",f"- Rebuilt pre-validation: `{val.stdout.strip()}`",'',"The rebuild began from the committed CST-EXP-03 tree, added only the CST-EXP-04 builder/data/validator and inherited manifest pin, regenerated the phase, and compared every phase-generated surface byte-for-byte."]
        if missing: lines += ['', '## Missing', '', *[f'- `{x}`' for x in missing]]
        if different: lines += ['', '## Differences', '', *[f"- `{x['path']}` expected `{x['expected']}`, rebuilt `{x['rebuilt']}`" for x in different]]
        (root/'manifests/REBUILD_VERIFICATION.md').write_text('\n'.join(lines)+'\n',encoding='utf-8')
        print(('PASS' if ok else 'FAIL'),len(files),'surfaces')
        if not ok:
            print('validation:',val.stdout,val.stderr); print('missing:',missing); print('different:',different[:20])
        return 0 if ok else 1
if __name__=='__main__': raise SystemExit(main())
