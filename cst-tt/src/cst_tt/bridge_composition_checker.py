from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from .corridor import (
    audit_corridor_composition,
    audit_direct_successor_path,
    compose_corridor_models,
)


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("model must be a JSON object")
    return value


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit corridor or direct-edge path composition.")
    parser.add_argument("left", type=Path)
    parser.add_argument("right", type=Path)
    parser.add_argument("--mode", choices=("corridor", "direct-path"), default="corridor")
    args = parser.parse_args()
    left = load(args.left)
    right = load(args.right)
    if args.mode == "corridor":
        composite = compose_corridor_models(left, right, model_id="CLI-COMPOSITE")
        payload = {
            "mode": args.mode,
            "audit": audit_corridor_composition(left, right, composite).to_dict(),
            "composite": composite,
        }
    else:
        payload = {
            "mode": args.mode,
            "audit": audit_direct_successor_path([left, right]).to_dict(),
        }
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
