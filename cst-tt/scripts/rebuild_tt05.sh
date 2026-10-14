#!/usr/bin/env bash
set -euo pipefail
export PYTHONHASHSEED=0
export PYTHONPATH="src:scripts"
python3 scripts/build_tt05_assets.py
