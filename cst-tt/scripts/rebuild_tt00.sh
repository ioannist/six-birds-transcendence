#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
python3 scripts/build_tt00_assets.py
python3 scripts/validate_tt00.py
PYTHONPATH=src python3 -m pytest -q
