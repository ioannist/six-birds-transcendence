#!/usr/bin/env bash
# Archive only committed HEAD. No external corpus copies or working-tree edits.
# Usage: scripts/make_review_zip.sh [vNN]
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
ver="${1:-}"
if [[ -z "$ver" ]]; then
  shopt -s nullglob
  candidates=(review_requests/external_review_request_v*.md)
  shopt -u nullglob
  if (( ${#candidates[@]} )); then
    ver="$(printf '%s\n' "${candidates[@]}" | sed -nE 's#.*external_review_request_(v[0-9]+)\.md#\1#p' | sort -V | tail -1)"
  fi
fi
if [[ ! "$ver" =~ ^v[0-9]+$ ]]; then
  echo 'ERROR: supply vNN or create review_requests/external_review_request_vNN.md' >&2
  exit 2
fi
mkdir -p review_requests
out="review_requests/six-birds-transcendence_${ver}.zip"
if [[ -n "$(git status --porcelain)" ]]; then
  echo 'WARNING: uncommitted files are excluded; archive contains HEAD only.' >&2
fi
archive_tmp="$(mktemp "${out}.tmp.XXXXXX")"
trap 'rm -f "$archive_tmp"' EXIT
trap 'exit 129' HUP
trap 'exit 130' INT
trap 'exit 143' TERM
git archive --format=zip -o "$archive_tmp" HEAD
python3 - "$archive_tmp" <<'PY'
import sys
from pathlib import PurePosixPath
import zipfile
with zipfile.ZipFile(sys.argv[1]) as archive:
    names=[n for n in archive.namelist() if not n.endswith('/')]
    pdfs=sorted(n for n in names if n.endswith('.pdf'))
    if 'paper/main.pdf' not in pdfs:
        raise SystemExit('ERROR: paper/main.pdf is not tracked in HEAD')
    cruft=[n for n in names if any(p in {'.lake','__pycache__','.venv'} for p in PurePosixPath(n).parts)
           or n.endswith(('.olean','.ilean')) or n.startswith('paper/build/')
           or (n.startswith('review_requests/') and n.endswith('.zip'))]
    if cruft: raise SystemExit(f'ERROR: {len(cruft)} build/cache/archive files in HEAD')
    print(f'Files: {len(names)}; PDFs: {len(pdfs)}; forbidden build/cache files: {len(cruft)}')
    for name in pdfs: print('PDF: '+name)
PY
mv -f "$archive_tmp" "$out"
echo "Built $out ($(wc -c < "$out") bytes; HEAD=$(git rev-parse --short HEAD))"
