#!/usr/bin/env python3
from __future__ import annotations

import os
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
ENV = {**os.environ, "PYTHONPATH": "src:scripts", "PYTHONHASHSEED": "0"}


def main() -> int:
    subprocess.run([sys.executable, "scripts/build_tt08_assets.py"], cwd=ROOT, env=ENV, check=True)
    print("CST-TT-08 deterministic assets rebuilt")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
