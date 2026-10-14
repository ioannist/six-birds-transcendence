#!/usr/bin/env python3
"""Run a release check, saving its exact command, exit code and log receipt.

Receipts are run evidence, not predictions. --capture-existing records a check
already run by the release engineer; its exit code must be supplied explicitly.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
RECEIPTS = ROOT / 'paper/data/release_receipts'


class MissingMetrics(ValueError):
    """The run produced no complete count summary."""


def tail_summary(text):
    return '\n'.join(text.splitlines()[-5:])[-1600:]


def consistent_counts(counts, exit_code):
    if any(not isinstance(n, int) or n < 0 for n in counts.values()):
        raise ValueError('Invalid test count')
    failed = counts.get('failed', 0) + counts.get('errors', 0)
    if (exit_code == 0) != (failed == 0):
        raise ValueError('Inconsistent exit code and test summary')


def metrics(kind, text, exit_code):
    if kind == 'pytest':
        lines = [line for line in text.splitlines() if re.search(r'\d+ (?:passed|failed|errors?|skipped|xfailed|xpassed).*\bin \d', line)]
        if not lines: raise MissingMetrics('No completed pytest summary; no test counts extracted')
        summary = lines[-1]
        counts = {('errors' if key in {'error','errors'} else key): int(value) for value,key in
                  re.findall(r'(\d+) (passed|failed|errors?\b|skipped|xfailed|xpassed|deselected)', summary)}
        counts.setdefault('passed', 0)
        consistent_counts(counts, exit_code)
        failures=re.findall(r'(?m)^FAILED .+$',text)
        return counts, '\n'.join([summary,*failures])
    if kind == 'lean_build':
        matches = re.findall(r'Build completed successfully \((\d+) jobs\)', text)
        if exit_code:
            if matches: raise ValueError('Inconsistent exit code and successful Lean build summary')
            return {}, tail_summary(text)
        if not matches: raise MissingMetrics('No successful Lean build/job summary')
        return {'jobs':int(matches[-1])}, 'Build completed successfully ('+matches[-1]+' jobs).'
    if kind == 'selftest':
        tagged = re.search(r'Counts:\s*(\{[^\n]+\})', text)
        fraction = re.search(r'(\d+)/(\d+) CAUGHT', text)
        rows = re.findall(r'(?m)^\|.*\|\s*(CAUGHT|MISSED|ERROR)\s*\|\s*$', text)
        if tagged:
            obj=json.loads(tagged[1]);counts={'passed':obj['CAUGHT'],'failed':obj['MISSED']+obj['ERROR']}
            consistent_counts(counts, exit_code);return counts,tagged[0]
        if fraction:
            counts={'passed':int(fraction[1]),'failed':int(fraction[2])-int(fraction[1])}
            if counts['failed'] < 0: raise ValueError('Invalid caught/total summary')
            consistent_counts(counts, exit_code);return counts,fraction[0]
        if rows:
            matched=re.findall(r'(?m)^\|.*\|\s*(?:CAUGHT|MISSED|ERROR)\s*\|\s*$',text)
            counts={'passed':rows.count('CAUGHT'),'failed':len(rows)-rows.count('CAUGHT')}
            consistent_counts(counts, exit_code);return counts,'\n'.join(matched)
        passes=re.findall(r'(?m)^PASS .+$',text)
        if passes:
            counts={'passed':len(passes)};consistent_counts(counts, exit_code)
            return counts,'\n'.join(passes)
        raise MissingMetrics('No recognized self-test summary')
    return {}, tail_summary(text)


def measurement(kind, text, exit_code):
    """Preserve observed runs even when counts are unavailable or inconsistent."""
    try:
        counts, summary = metrics(kind, text, exit_code)
        return dict(metrics=counts, summary=summary, metrics_status='valid', metrics_note='')
    except MissingMetrics as exc:
        status = 'unavailable' if exit_code else 'invalid'
        return dict(metrics={}, summary=tail_summary(text), metrics_status=status, metrics_note=str(exc))
    except (ValueError, KeyError, TypeError) as exc:
        return dict(metrics={}, summary=tail_summary(text), metrics_status='invalid', metrics_note=str(exc))


def receipt(identifier, kind, command, cwd, log, exit_code, env=None):
    data = log.read_bytes(); text=data.decode('utf-8',errors='replace')
    return dict(id=identifier, kind=kind, recorded_at=datetime.now(timezone.utc).isoformat(timespec='seconds'),
                command=command, cwd=cwd.relative_to(ROOT).as_posix() or '.', environment=env or {},
                exit_code=exit_code, status='pass' if exit_code==0 else 'fail',
                log_path=log.relative_to(ROOT).as_posix(), log_sha256=hashlib.sha256(data).hexdigest(),
                **measurement(kind,text,exit_code))


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--id',required=True);p.add_argument('--kind',choices=['check','pytest','selftest','lean_build','diagnostic'],default='check')
    p.add_argument('--cwd',default='.');p.add_argument('--log',required=True)
    p.add_argument('--capture-existing',action='store_true');p.add_argument('--exit-code',type=int)
    p.add_argument('--env',action='append',default=[]);p.add_argument('command',nargs=argparse.REMAINDER)
    a=p.parse_args();command=a.command[1:] if a.command[:1]==['--'] else a.command
    if not re.fullmatch(r'[a-z][a-z0-9_]*',a.id) or not command:p.error('Valid id and exact command required')
    cwd=(ROOT/a.cwd).resolve();log=(ROOT/a.log).resolve()
    if not cwd.is_relative_to(ROOT) or not log.is_relative_to(ROOT):p.error('Paths must be within repository')
    env=dict(value.split('=',1) for value in a.env)
    if a.capture_existing:
        if a.exit_code is None:p.error('--capture-existing requires --exit-code')
        code=a.exit_code
    else:
        import os
        log.parent.mkdir(parents=True,exist_ok=True)
        with log.open('w') as out:
            try:
                code=subprocess.run(command,cwd=cwd,env={**os.environ,**env},stdout=out,stderr=subprocess.STDOUT).returncode
            except OSError as exc:
                out.write('Command could not start: '+str(exc)+'\n');code=127
    record=receipt(a.id,a.kind,command,cwd,log,code,env)
    RECEIPTS.mkdir(parents=True,exist_ok=True)
    # Replace the old receipt even when parsing fails, atomically.
    target=RECEIPTS/(a.id+'.json');temporary=target.with_suffix('.json.tmp')
    temporary.write_text(json.dumps(record,indent=2,sort_keys=True)+'\n');temporary.replace(target)
    print(json.dumps({'id':a.id,'status':record['status'],'metrics':record['metrics'],
                      'metrics_status':record['metrics_status'],'metrics_note':record['metrics_note']}))
    if record['metrics_status']=='invalid': return 2
    return code


if __name__=='__main__':raise SystemExit(main())
