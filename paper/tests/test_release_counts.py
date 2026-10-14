"""W19 offline count reproducibility; failed run receipts remain failed."""
import importlib.util
import json
from pathlib import Path
import subprocess
import sys

from jsonschema import Draft202012Validator
import pytest

ROOT=Path(__file__).resolve().parents[2]
TOOLS=ROOT/'paper/tools'


def load(name):
    if str(TOOLS) not in sys.path:sys.path.insert(0,str(TOOLS))
    spec=importlib.util.spec_from_file_location('w19_'+name,TOOLS/(name+'.py'))
    module=importlib.util.module_from_spec(spec);spec.loader.exec_module(module);return module


def test_release_counts_schema_and_offline_check():
    data=json.loads((ROOT/'paper/data/release_counts.json').read_text())
    Draft202012Validator(json.loads((ROOT/'paper/data/release_counts.schema.json').read_text())).validate(data)
    result=subprocess.run([sys.executable,str(TOOLS/'build_release_counts.py'),'--check'],cwd=ROOT,capture_output=True,text=True)
    assert result.returncode==0,result.stdout+result.stderr


def test_static_counts_are_recomputed_not_constants():
    tool=load('build_release_counts')
    data=json.loads(tool.OUTPUT.read_text())
    assert data['static']==tool.static_counts()
    assert data['static']['modules']['under_csttt_directory']==len(list((ROOT/'lean/CSTTT').rglob('*.lean')))
    assert data['static']['model_specs']['count']==len(data['static']['model_specs']['files'])


def test_run_receipts_reproduce_counts_and_keep_failures():
    tool=load('build_release_counts');data=tool.build()
    assert data['run_recorded']['commands']==tool.run_records()
    failures=[r for r in data['run_recorded']['commands'] if r['exit_code']]
    assert data['verification_status']==('fail' if failures else 'pass')
    for r in failures:assert r['status']=='fail'


def test_job_and_test_counts_require_actual_summaries():
    tool=load('record_release_check')
    assert tool.metrics('lean_build','Build completed successfully (799 jobs).',0)[0]=={'jobs':799}
    assert tool.metrics('pytest','6 failed, 130 passed in 4.61s',1)[0]=={'failed':6,'passed':130}
    with pytest.raises(ValueError):tool.metrics('lean_build','no jobs recorded',0)
    with pytest.raises(ValueError):tool.metrics('pytest','3 errors during collection',2)


@pytest.mark.parametrize('kind,text',[('selftest','PASS first\nPASS second\n'),
    ('selftest','| case | probe | CAUGHT |\n'),('selftest','3/3 CAUGHT'),
    ('selftest','Counts: {"CAUGHT": 5, "MISSED": 0, "ERROR": 0}')])
def test_selftest_summaries_round_trip_offline(kind,text):
    tool=load('record_release_check');counts,summary=tool.metrics(kind,text,0)
    assert tool.metrics(kind,summary,0)[0]==counts


def test_release_count_drift_fails_without_writing(tmp_path,monkeypatch):
    tool=load('build_release_counts');output=tmp_path/'counts.json'
    output.write_text(tool.OUTPUT.read_text()+'\n')
    before=output.read_bytes();monkeypatch.setattr(tool,'OUTPUT',output)
    monkeypatch.setattr(sys,'argv',['build_release_counts.py','--check'])
    assert tool.main()==1 and output.read_bytes()==before


@pytest.mark.parametrize('kind,success,failure,code,expected',[
    ('lean_build','Build completed successfully (799 jobs).','error: failed Lean build',1,{}),
    ('pytest','1 passed in 0.01s','2 failed in 0.01s',1,{'passed':0,'failed':2}),
    ('pytest','1 passed in 0.01s','3 errors during collection',2,{})])
def test_failed_rerun_always_replaces_old_pass(tmp_path,monkeypatch,kind,success,failure,code,expected):
    tool=load('record_release_check')
    monkeypatch.setattr(tool,'ROOT',tmp_path);monkeypatch.setattr(tool,'RECEIPTS',tmp_path/'receipts')
    def run(text,exit_code):
        command=[sys.executable,'-c',f'print({text!r});raise SystemExit({exit_code})']
        monkeypatch.setattr(sys,'argv',['record_release_check.py','--id','fixture','--kind',kind,
                                      '--log','run.log','--',*command])
        return tool.main()
    assert run(success,0)==0
    path=tmp_path/'receipts/fixture.json';before=path.read_bytes()
    assert run(failure,code)==code
    record=json.loads(path.read_text())
    assert path.read_bytes()!=before and record['status']=='fail' and record['exit_code']==code
    assert record['metrics']==expected and record['metrics_status']!='invalid'


@pytest.mark.parametrize('kind,text,code',[
    ('pytest','2 failed in 0.01s',0),('pytest','3 passed in 0.01s',1),
    ('lean_build','Build completed successfully (799 jobs).',1),
    ('selftest','Counts: {"CAUGHT": 5, "MISSED": 1, "ERROR": 0}',0)])
def test_inconsistent_summary_and_exit_is_rejected(kind,text,code):
    tool=load('record_release_check')
    with pytest.raises(ValueError,match='Inconsistent'):tool.metrics(kind,text,code)


def test_inconsistent_observed_run_is_written_then_rejected(tmp_path,monkeypatch):
    tool=load('record_release_check');monkeypatch.setattr(tool,'ROOT',tmp_path)
    monkeypatch.setattr(tool,'RECEIPTS',tmp_path/'receipts')
    tool.RECEIPTS.mkdir();path=tool.RECEIPTS/'fixture.json';path.write_text('{"status":"pass"}')
    command=[sys.executable,'-c',"print('2 failed in 0.01s')"]
    monkeypatch.setattr(sys,'argv',['record_release_check.py','--id','fixture','--kind','pytest',
                                  '--log','run.log','--',*command])
    assert tool.main()==2
    record=json.loads(path.read_text())
    assert record['exit_code']==0 and record['metrics_status']=='invalid'
    counts=load('build_release_counts');monkeypatch.setattr(counts,'ROOT',tmp_path)
    monkeypatch.setattr(counts,'RECEIPTS',tool.RECEIPTS)
    with pytest.raises(ValueError,match='Invalid receipt measurement'):counts.run_records()


def fixture_log_receipt(tmp_path,monkeypatch):
    runner=load('record_release_check');monkeypatch.setattr(runner,'ROOT',tmp_path)
    log=tmp_path/'observed.log';log.write_text('174 passed in 208.20s\n')
    record=runner.receipt('fixture','pytest',['pytest'],tmp_path,log,0)
    receipts=tmp_path/'receipts';receipts.mkdir()
    path=receipts/'fixture.json';path.write_text(json.dumps(record))
    counts=load('build_release_counts');monkeypatch.setattr(counts,'ROOT',tmp_path)
    monkeypatch.setattr(counts,'RECEIPTS',receipts)
    return counts,path,log,record


@pytest.mark.parametrize('mutation',['metrics_and_summary','summary_only'])
def test_full_log_is_authoritative_not_editable_receipt(tmp_path,monkeypatch,mutation):
    counts,path,_,record=fixture_log_receipt(tmp_path,monkeypatch)
    record['summary']=record['summary'].replace('174','175')
    if mutation=='metrics_and_summary':record['metrics']['passed']=175
    path.write_text(json.dumps(record))
    with pytest.raises(ValueError,match='Full log/receipt .* mismatch'):counts.run_records()


def test_archive_fallback_is_explicit_and_preserves_record(tmp_path,monkeypatch):
    counts,_,log,record=fixture_log_receipt(tmp_path,monkeypatch)
    evidence={};assert counts.run_records(evidence)==[record]
    assert evidence=={'full_logs_verified':['fixture']}
    log.unlink();evidence={};assert counts.run_records(evidence)==[record]
    assert evidence=={'summary_only_ids':['fixture']}


def test_archive_log_tail_with_final_blank_line_is_preserved(tmp_path,monkeypatch):
    runner=load('record_release_check');monkeypatch.setattr(runner,'ROOT',tmp_path)
    log=tmp_path/'run.log';log.write_text('one\ntwo\nthree\nfour\nfive\n\n')
    record=runner.receipt('fixture','check',['checker'],tmp_path,log,0)
    assert record['summary'].endswith('\n')
    receipts=tmp_path/'receipts';receipts.mkdir();(receipts/'fixture.json').write_text(json.dumps(record))
    counts=load('build_release_counts');monkeypatch.setattr(counts,'ROOT',tmp_path)
    monkeypatch.setattr(counts,'RECEIPTS',receipts)
    log.unlink();evidence={}
    assert counts.run_records(evidence)==[record] and evidence=={'summary_only_ids':['fixture']}


def test_failed_lean_build_has_no_previous_job_count(tmp_path,monkeypatch):
    tool=load('build_release_counts');records=tool.run_records()
    for record in records:
        if record['id']=='lean_build':
            record.update(exit_code=1,status='fail',metrics={},summary='error: failed build')
    monkeypatch.setattr(tool,'run_records',lambda evidence=None:records)
    data=tool.build()
    assert data['run_recorded']['lean_build_jobs'] is None and data['verification_status']=='fail'
    assert r'\newcommand{\relLeanBuildJobs}' not in tool.tex_macros(data)


def test_generated_report_explains_both_retained_failures():
    tool=load('build_release_counts');text=tool.report(tool.build())
    assert '`cst_tt`' in text and '`ba3e5dd`' in text and 'historical-builder idempotence' in text
    assert '`cst_tt_initial_setup`' in text and 'collection' in text and 'PYTHONPATH=src:scripts' in text
    assert 'Overall recorded status: **FAIL**' in text
