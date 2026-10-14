from __future__ import annotations

import csv
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from cst_tt.transport import (
    audit_memory_repair,
    audit_record_arrow,
    audit_route_discipline,
    audit_temporal_transport,
    bounded_confluence_shape_search,
    bounded_transport_shape_search,
)

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def test_all_registered_controls_fail_their_primary_obligation() -> None:
    rows = list(csv.DictReader((ROOT / "registries/TRANSPORT_CONTROL_REGISTRY.csv").open()))
    assert len(rows) == 28
    for row in rows:
        model = load(ROOT / row["artifact_ref"])
        if row["control_kind"] == "transport":
            audit = audit_temporal_transport(model)
            valid = audit.transport_valid
        elif row["control_kind"] == "route":
            audit = audit_route_discipline(model)
            valid = audit.flatness_valid
        elif row["control_kind"] == "memory":
            audit = audit_memory_repair(model)
            valid = audit.memory_repair_valid
        else:
            audit = audit_record_arrow(model)
            valid = audit.arrow_transport_valid
        assert not valid
        assert row["expected_primary_failure"] in audit.failed_obligations
        assert set(row["observed_failures"].split(";")) == set(audit.failed_obligations)


def test_all_control_certificates_validate() -> None:
    schema = load(ROOT / "schemas/certificates/transport_control_certificate.schema.json")
    validator = Draft202012Validator(schema)
    paths = sorted((ROOT / "formal/certificates/transport/controls").glob("*.certificate.json"))
    assert len(paths) == 28
    for path in paths:
        assert not list(validator.iter_errors(load(path)))


def test_bounded_shape_searches_are_reproducible() -> None:
    transport = bounded_transport_shape_search()
    confluence = bounded_confluence_shape_search()
    assert transport == load(ROOT / "formal/certificates/transport/BOUNDED_TRANSPORT_SHAPE_SEARCH.json")
    assert confluence == load(ROOT / "formal/certificates/routes/BOUNDED_CONFLUENCE_SHAPE_SEARCH.json")
    assert transport["minimal_pair"] == [3, 2]
    assert transport["pairs_examined"] == 12
    assert confluence["minimal_node_count"] == 4
    assert confluence["candidates_examined"] == 354
