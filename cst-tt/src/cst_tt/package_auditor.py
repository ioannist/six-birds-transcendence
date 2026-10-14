from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from .package_gluing import audit_package, audit_staged_assembly, bounded_gluing_exhaustion


def _load(path: Path) -> dict[str, Any]:
    value = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(f"{path} does not contain a JSON object")
    return value


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="package_gluing_auditor")
    sub = parser.add_subparsers(dest="command", required=True)
    package = sub.add_parser("package", help="audit one integrated package model")
    package.add_argument("model", type=Path)
    staged = sub.add_parser("staged", help="audit one staged heterogeneous assembly")
    staged.add_argument("assembly", type=Path)
    staged.add_argument("source", type=Path)
    staged.add_argument("target", type=Path)
    sub.add_parser("exhaust", help="run the bounded gluing corroboration")
    args = parser.parse_args(argv)
    if args.command == "package":
        payload = audit_package(_load(args.model)).to_dict()
        ok = payload["integrated_package_valid"]
    elif args.command == "staged":
        payload = audit_staged_assembly(_load(args.assembly), _load(args.source), _load(args.target)).to_dict()
        ok = payload["staged_assembly_valid"]
    else:
        payload = bounded_gluing_exhaustion()
        ok = payload["status"] == "PASS"
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
