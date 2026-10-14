#!/usr/bin/env bash
set -euo pipefail
export PYTHONHASHSEED=0
export PYTHONPATH=src:scripts
python3 scripts/build_tt07a_assets.py
python3 -m pytest -q
python3 scripts/validate_tt07a.py --no-write
