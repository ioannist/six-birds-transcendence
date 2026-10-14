"""W19 DOI publication overrides use authored evidence offline, without guessing."""
import importlib.util
import json
from pathlib import Path

import pytest

ROOT=Path(__file__).resolve().parents[2]


def load():
    spec=importlib.util.spec_from_file_location('w19_doi',ROOT/'paper/tools/build_import_map.py')
    m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m);return m


def fixture_record():
    return dict(schema_version='1.0',verified_by='agent_live',verification_date='2026-10-13',
                method='HTTPS GET doi.org redirect and Zenodo API published status/title/date',
                records=[dict(paper_id='P07',doi='10.5281/zenodo.23120470',doi_http_status=302,
                              api_http_status=200,api_status='published',api_record_id=23120470,
                              api_url='https://zenodo.org/api/records/23120470',title='Exact title',publication_date='2026-10-03')])


def test_publication_record_is_offline_and_discloses_date_and_method(tmp_path,monkeypatch):
    m=load();monkeypatch.setattr(m,'OUTPUT',tmp_path)
    (tmp_path/'corpus_doi_verification.json').write_text(json.dumps(fixture_record()))
    import urllib.request
    monkeypatch.setattr(urllib.request,'urlopen',lambda *a,**k:pytest.fail('Offline DOI checks must not hit the network'))
    records=m.publication_verifications()
    result=m.apply_publication_verification('P07','10.5281/zenodo.23120470','Exact title','reserved','metadata','old scope',records)
    assert result[0]=='published' and result[3]=='2026-10-13'
    assert 'agent_live' in result[4] and result[5]=='2026-10-03'
    for pid in ['P05','P18']:
        assert m.apply_publication_verification(pid,'','Title','none','','unchanged',records)==('none','','unchanged','','','')


@pytest.mark.parametrize('field,value',[('api_status','draft'),('doi_http_status',200),
    ('api_record_id',1),('paper_id','P05')])
def test_invalid_publication_evidence_is_rejected(tmp_path,monkeypatch,field,value):
    m=load();record=fixture_record();record['records'][0][field]=value
    (tmp_path/'corpus_doi_verification.json').write_text(json.dumps(record));monkeypatch.setattr(m,'OUTPUT',tmp_path)
    with pytest.raises(ValueError):m.publication_verifications()


def test_title_mismatch_is_not_silently_overridden(tmp_path,monkeypatch):
    m=load();monkeypatch.setattr(m,'OUTPUT',tmp_path)
    (tmp_path/'corpus_doi_verification.json').write_text(json.dumps(fixture_record()))
    with pytest.raises(ValueError,match='differs'):
        m.apply_publication_verification('P07','10.5281/zenodo.23120470','Different work','reserved','','',m.publication_verifications())
