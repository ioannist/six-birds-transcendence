#!/usr/bin/env bash
set -euo pipefail
export PYTHONHASHSEED=0
export PYTHONPATH=src:scripts
python3 -m pytest -q
python3 scripts/validate_tt06.py --no-write "$@"
if command -v lake >/dev/null 2>&1; then
  lake build
else
  echo "Lean/Lake unavailable: compilation check skipped, not passed."
fi
