#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PYTHONDONTWRITEBYTECODE=1

find . -path '*/__pycache__' -type d -prune -exec rm -rf {} +
find . -name '*.pyc' -type f -delete

python scripts/build_exp02_assets.py --repo .
if command -v dot >/dev/null 2>&1; then
  dot -Tsvg scenarios/neutral_transfer_frame.dot -o scenarios/neutral_transfer_frame.svg
  dot -Tpng scenarios/neutral_transfer_frame.dot -o scenarios/neutral_transfer_frame.png
else
  printf '%s\n' 'warning: Graphviz dot not available; retained neutral-frame diagram binaries were not regenerated' >&2
fi
find . -path '*/__pycache__' -type d -prune -exec rm -rf {} +
find . -name '*.pyc' -type f -delete
python scripts/validate_exp02.py --repo . --skip-manifest
python scripts/finalize_exp02_manifest.py --repo .
python scripts/validate_exp02.py --repo .
python scripts/finalize_exp02_manifest.py --repo .
python scripts/validate_exp02.py --repo .

printf '%s\n' 'CST-EXP-02 rebuild and validation complete.'
