from __future__ import annotations

import csv
import json
from pathlib import Path

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]


def test_every_theorem_registry_row_matches_its_json_schema() -> None:
    schema = json.loads((ROOT / "schemas/registries/theorem_registry_row.schema.json").read_text(encoding="utf-8"))
    Draft202012Validator.check_schema(schema)
    validator = Draft202012Validator(schema)
    with (ROOT / "registries/THEOREM_REGISTRY.csv").open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    for row in rows:
        errors = sorted(validator.iter_errors(row), key=lambda error: list(error.path))
        assert errors == [], (row["theorem_id"], [error.message for error in errors])
