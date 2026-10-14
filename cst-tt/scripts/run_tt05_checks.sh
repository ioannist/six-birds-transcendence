#!/usr/bin/env bash
set -euo pipefail
export PYTHONHASHSEED=0
export PYTHONPATH="src:scripts"
python3 scripts/build_tt05_assets.py
python3 -m pytest -q
python3 scripts/validate_tt05.py --no-write
