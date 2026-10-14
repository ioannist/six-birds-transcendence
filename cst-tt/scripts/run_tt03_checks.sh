#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
export PYTHONHASHSEED=0
export PYTHONPATH=src:scripts
export TERM=dumb
python3 scripts/build_tt03_assets.py >/dev/null
python3 -m pytest -q
python3 scripts/validate_tt03.py --no-write
python3 scripts/verify_tt03_rebuild.py
if command -v lake >/dev/null 2>&1 && command -v lean >/dev/null 2>&1; then
  lake build
else
  printf '%s\n' 'LEAN_BUILD_SKIPPED: lean/lake unavailable; no compilation pass claimed.'
fi
