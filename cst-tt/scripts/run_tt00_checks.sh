#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
python3 scripts/build_tt00_assets.py >/dev/null
PYTHONHASHSEED=0 PYTHONPATH=src python3 -m pytest -q
python3 scripts/validate_tt00.py
if command -v lake >/dev/null 2>&1 && command -v lean >/dev/null 2>&1; then
  lake build
else
  printf '%s\n' 'LEAN_BUILD_SKIPPED: lean/lake unavailable; no compilation pass claimed.'
fi
