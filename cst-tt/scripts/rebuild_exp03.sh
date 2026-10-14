#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PYTHONDONTWRITEBYTECODE=1

cleanup_caches() {
  find . -path '*/__pycache__' -type d -prune -exec rm -rf {} +
  find . -name '*.pyc' -type f -delete
}

cleanup_caches
python -B scripts/build_exp03_assets.py --repo . --stage all
if command -v dot >/dev/null 2>&1; then
  dot -Tsvg candidates/candidate_design_space.dot -o candidates/candidate_design_space.svg
  dot -Tpng candidates/candidate_design_space.dot -o candidates/candidate_design_space.png
else
  printf '%s
' 'warning: Graphviz dot unavailable; retained diagram binaries were not regenerated' >&2
fi

cleanup_caches
python -B scripts/validate_exp03.py --repo . --skip-manifest
python -B scripts/verify_exp03_rebuild.py --repo .
cleanup_caches
python -B scripts/finalize_exp03_manifest.py --repo .
cleanup_caches
python -B scripts/validate_exp03.py --repo .
cleanup_caches
python -B scripts/finalize_exp03_manifest.py --repo .
cleanup_caches
python -B scripts/validate_exp03.py --repo .
cleanup_caches
printf '%s
' 'CST-EXP-03 rebuild and validation complete.'
