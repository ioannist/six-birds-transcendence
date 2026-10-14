#!/usr/bin/env bash
set -euo pipefail
ROOT="${1:-$(cd "$(dirname "$0")/.." && pwd)}"
python "$ROOT/scripts/build_exp04_assets.py" --root "$ROOT"
python "$ROOT/scripts/validate_exp04.py" --root "$ROOT" --skip-manifest --no-write
