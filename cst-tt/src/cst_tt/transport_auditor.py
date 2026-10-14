from __future__ import annotations

import argparse
import json
from pathlib import Path
from typing import Any

from .transport import (
    audit_memory_repair,
    audit_record_arrow,
    audit_route_discipline,
    audit_temporal_transport,
    bounded_confluence_shape_search,
    bounded_global_now_obstruction_search,
    bounded_memory_or_flatness_exhaustion,
    bounded_transport_shape_search,
)


def _load(path: Path) -> dict[str, Any]:
    payload = json.loads(path.read_text(encoding="utf-8"))
    if not isinstance(payload, dict):
        raise ValueError(f"{path} must contain a JSON object")
    return payload


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="temporal_transport_checker")
    sub = parser.add_subparsers(dest="command", required=True)
    transport = sub.add_parser("transport", help="audit a heterogeneous temporal transport model")
    transport.add_argument("model", type=Path)
    transport.add_argument("--flatness-certificate", type=Path)
    route = sub.add_parser("route", help="audit route holonomy and confluence")
    route.add_argument("model", type=Path)
    memory = sub.add_parser("memory", help="audit current-only prediction and route-memory repair")
    memory.add_argument("model", type=Path)
    arrow = sub.add_parser("arrow", help="audit monotone record-arrow transport")
    arrow.add_argument("model", type=Path)
    sub.add_parser("exhaust", help="run bounded transport and confluence shape searches")
    args = parser.parse_args(argv)

    if args.command == "transport":
        flat_valid = None
        if args.flatness_certificate is not None:
            flat_payload = _load(args.flatness_certificate)
            flat_valid = bool(flat_payload.get("audit", {}).get("flatness_valid"))
        audit = audit_temporal_transport(_load(args.model), flatness_certificate_valid=flat_valid)
        payload = audit.to_dict()
        ok = audit.transport_valid
    elif args.command == "route":
        audit = audit_route_discipline(_load(args.model))
        payload = audit.to_dict()
        ok = audit.route_audit_valid
    elif args.command == "memory":
        audit = audit_memory_repair(_load(args.model))
        payload = audit.to_dict()
        ok = audit.memory_repair_valid
    elif args.command == "arrow":
        audit = audit_record_arrow(_load(args.model))
        payload = audit.to_dict()
        ok = audit.arrow_transport_valid
    else:
        payload = {
            "transport_shape": bounded_transport_shape_search(),
            "confluence_shape": bounded_confluence_shape_search(),
            "memory_or_flatness": bounded_memory_or_flatness_exhaustion(),
            "global_now_obstruction": bounded_global_now_obstruction_search(),
        }
        ok = all(value["status"] == "PASS" for value in payload.values())
    print(json.dumps(payload, indent=2, sort_keys=True))
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
