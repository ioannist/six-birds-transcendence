#!/usr/bin/env python3
"""Live DOI/API verification; write no publication record unless all checks pass.

This is the online acquisition step. build_import_map.py --check is offline.
P05's successor reservation and P18's absent DOI are deliberately excluded.
"""
from datetime import datetime, timezone
import json
import urllib.error
import urllib.request

from build_import_map import OUTPUT, read_csv, normalized


class NoRedirect(urllib.request.HTTPRedirectHandler):
    def redirect_request(self, req, fp, code, msg, headers, newurl): return None


def main():
    rows={r['paper_id']:r for r in read_csv(OUTPUT/'sibling_import_map.csv')}
    opener=urllib.request.build_opener(NoRedirect)
    records=[];failures=[]
    for pid,row in sorted(rows.items()):
        if pid in {'P05','P18'}:continue
        doi=row['doi'];number=int(doi.rsplit('.',1)[1]);errors=[]
        doi_code=None
        try:
            with opener.open('https://doi.org/'+doi,timeout=20) as response:doi_code=response.status
        except urllib.error.HTTPError as error:doi_code=error.code
        except OSError as error:errors.append('doi.org: '+str(error))
        api=None;api_code=None;url='https://zenodo.org/api/records/'+str(number)
        try:
            with urllib.request.urlopen(url,timeout=20) as response:
                api_code=response.status;api=json.load(response)
        except (OSError,ValueError) as error:errors.append('Zenodo API: '+str(error))
        if doi_code!=302:errors.append('No observed HTTP 302 DOI response')
        if api is not None:
            from build_import_map import locate,title_text
            title=title_text(locate(row['source_file']).read_text())
            if api_code!=200 or api.get('status')!='published' or api.get('id')!=number:
                errors.append('API is not the matching published record')
            if normalized(api.get('metadata',{}).get('title',''))!=normalized(title):errors.append('API/source title mismatch')
            if not api.get('metadata',{}).get('publication_date'):errors.append('No publication date')
        if errors:failures.append({'paper_id':pid,'doi':doi,'errors':errors});continue
        records.append(dict(paper_id=pid,doi=doi,doi_http_status=doi_code,api_http_status=api_code,
                            api_status=api['status'],api_record_id=api['id'],api_url=url,
                            title=api['metadata']['title'],publication_date=api['metadata']['publication_date']))
    if failures:
        print(json.dumps({'status':'blocked','failures':failures,'verification_record_written':False}));return 1
    record=dict(schema_version='1.0',verified_by='agent_live',verification_date=datetime.now(timezone.utc).date().isoformat(),
                method='HTTPS GET doi.org (302, redirects disabled) and Zenodo records API (200; published status, record id, title and date)',records=records)
    (OUTPUT/'corpus_doi_verification.json').write_text(json.dumps(record,indent=2,sort_keys=True)+'\n')
    print(json.dumps({'status':'pass','published_records':len(records)}));return 0


if __name__=='__main__':raise SystemExit(main())
