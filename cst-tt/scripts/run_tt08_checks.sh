#!/usr/bin/env bash
set -euo pipefail
export PYTHONHASHSEED=0
export PYTHONPATH=src:scripts
python3 -m pytest -q
python3 scripts/validate_tt08.py --no-write
if command -v lean >/dev/null 2>&1 && command -v lake >/dev/null 2>&1; then
  lake build
else
  echo 'SKIP: lean/lake unavailable; no Lean-kernel pass is claimed.'
fi
