from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from .corridor import audit_direct_successor, audit_strict_corridor


def load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError("model must be a JSON object")
    return value


def main() -> int:
    parser = argparse.ArgumentParser(description="Audit strict overlap-chain and direct event-successor models.")
    parser.add_argument("model", type=Path)
    parser.add_argument("--mode", choices=("corridor", "direct", "compare"), default="compare")
    args = parser.parse_args()
    model = load(args.model)
    payload: dict[str, object] = {"model": str(args.model), "mode": args.mode}
    if args.mode in {"corridor", "compare"}:
        payload["strict_corridor"] = audit_strict_corridor(model).to_dict()
    if args.mode in {"direct", "compare"}:
        payload["direct_successor"] = audit_direct_successor(model).to_dict()
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
