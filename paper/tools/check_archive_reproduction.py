#!/usr/bin/env python3
"""Test a commit-equivalent working-tree export without Git or sibling repos.

No commit, stash, index mutation, or network request is used. The default
starts without a build cache. A tooling-only retry may explicitly reuse the
cache built in the prior isolated export after checking every Lean input.
The export contains tracked files plus nonignored additions ready for review.
The Lean toolchain and Python/LaTeX tools must already be installed.
"""
from concurrent.futures import ThreadPoolExecutor
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import subprocess
import shutil
import sys
import tarfile
import tempfile

ROOT = Path(__file__).resolve().parents[2]


def export_tree(destination):
    listing = subprocess.check_output(['git','ls-files','--cached','--others','--exclude-standard','-z'],cwd=ROOT)
    names = sorted(set(os.fsdecode(p) for p in listing.split(b'\0') if p))
    archive = destination.parent/'source.tar'
    digests = []
    with tarfile.open(archive,'w') as output:
        for name in names:
            path = ROOT/name
            if not path.exists() and not path.is_symlink(): continue
            if '.git' in Path(name).parts: raise ValueError('Git internals in export')
            payload = os.readlink(path).encode() if path.is_symlink() else path.read_bytes()
            digests.append(name+':'+hashlib.sha256(payload).hexdigest())
            output.add(path,arcname=name,recursive=False)
    destination.mkdir()
    with tarfile.open(archive) as source: source.extractall(destination,filter='data')
    return dict(files=len(digests),sha256=hashlib.sha256('\n'.join(digests).encode()).hexdigest(),
                definition='Tracked working-tree files plus nonignored additions; symlinks preserved; no .git or ignored build artifacts.')


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--reuse-archive',type=Path,help='After tooling-only fixes, re-export into a prior standalone build; reject any changed Lean input')
    args=parser.parse_args()
    if args.reuse_archive:
        root=args.reuse_archive.resolve();scratch=root.parent
        if root==ROOT or root.name!='source' or not scratch.name.startswith('W19b-archive-') or (root/'.git').exists():
            parser.error('--reuse-archive must name a prior isolated export')
        inputs=[*sorted((ROOT/'lean').rglob('*.lean'))]
        inputs=[p for p in inputs if '.lake' not in p.parts and '.validate-logs' not in p.parts]
        inputs += [ROOT/'lean'/name for name in ['lean-toolchain','lakefile.toml','lake-manifest.json']]
        for path in inputs:
            archived=root/path.relative_to(ROOT)
            if not archived.is_file() or archived.read_bytes()!=path.read_bytes():
                parser.error('Lean input changed; perform a fresh export/build: '+str(path.relative_to(ROOT)))
        cache=scratch/'verified-archive-cache'
        (root/'lean/.lake').rename(cache)
        shutil.rmtree(root)
        snapshot=export_tree(root)
        cache.rename(root/'lean/.lake')
        if (scratch/'report.json').exists():
            shutil.copyfile(scratch/'report.json',scratch/'report-before-tooling-fix.json')
    else:
        scratch=Path(tempfile.mkdtemp(prefix='W19b-archive-'))
        root=scratch/'source';snapshot=export_tree(root)
    missing=scratch/'absent-siblings'
    env={**os.environ,'SIXBIRDS_SIBLING_ROOT':str(missing),'PYTHONHASHSEED':'0'}
    assert not missing.exists() and not (root/'.git').exists()
    if not args.reuse_archive: assert not (root/'lean/.lake').exists()
    logs=scratch/('logs-final' if args.reuse_archive else 'logs');logs.mkdir(exist_ok=True)
    print(json.dumps({'archive_root':str(root),'snapshot':snapshot,'sibling_root':str(missing),
                      'git_directory':False,'preexisting_lean_cache':bool(args.reuse_archive),
                      'cache_provenance':'prior cold build of byte-identical archived Lean inputs' if args.reuse_archive else 'none'}),flush=True)

    def run(item):
        identifier,cwd,command,expected=item
        path=logs/(identifier+'.log')
        print('RUN '+identifier+': '+' '.join(command)+' (cwd '+cwd+')',flush=True)
        with path.open('w') as output:
            code=subprocess.run(command,cwd=root/cwd,env=env,stdout=output,stderr=subprocess.STDOUT).returncode
        result=dict(id=identifier,command=command,cwd=cwd,exit_code=code,expected_exit=expected,
                    status='pass' if code==expected else 'fail',log_path=str(path),
                    log_sha256=hashlib.sha256(path.read_bytes()).hexdigest())
        print(json.dumps(result),flush=True)
        return result

    records=[run(('lean_build','lean',['lake','build','CSTTT'],0))]
    if records[0]['status']=='pass':
        checks=[('import_map','.',['python3','paper/tools/build_import_map.py','--check'],0),
                ('live_mode_absent_siblings','.',['python3','paper/tools/build_import_map.py','--live','--check'],1),
                ('evidence_map','.',['python3','paper/tools/build_evidence_map.py','--check'],0),
                ('snapshot','.',['python3','paper/tools/export_results.py','--check'],0),
                ('correspondence','.',['python3','paper/tools/build_correspondence.py','--check'],0),
                ('index','.',['python3','paper/tools/render_index.py','--check'],0),
                ('figure_data','.',['python3','paper/tools/render_figure_data.py','--check'],0),
                ('release_counts','.',['python3','paper/tools/build_release_counts.py','--check'],0),
                ('style','.',['python3','paper/tools/style_lint.py','--strict'],0),
                ('manuscript','.',['python3','paper/tools/check_manuscript.py'],0),
                ('package','.',['python3','paper/prewriting/validate_package.py'],0)]
        with ThreadPoolExecutor(max_workers=2) as pool: records.extend(pool.map(run,checks))
        records.append(run(('paper_tests','.',['python3','-m','pytest','-q','paper/tests'],0)))
    report=dict(recorded_at=datetime.now(timezone.utc).isoformat(timespec='seconds'),
                archive_root=str(root),snapshot=snapshot,environment={'SIXBIRDS_SIBLING_ROOT':str(missing),'PYTHONHASHSEED':'0'},
                lean_cache=dict(reused=bool(args.reuse_archive),provenance='prior cold build of byte-identical archived Lean inputs' if args.reuse_archive else 'none'),
                commands=records,status='pass' if all(r['status']=='pass' for r in records) else 'fail')
    (scratch/'report.json').write_text(json.dumps(report,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'archive_reproduction':report['status'],'report':str(scratch/'report.json')}),flush=True)
    return 0 if report['status']=='pass' else 1


if __name__=='__main__':raise SystemExit(main())
