from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from cst_tt.corridor import audit_strict_corridor

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_all_strict_corridor_certificates_are_hash_bound_and_replay() -> None:
    schema = load(ROOT / "schemas/certificates/strict_temporal_corridor_certificate.schema.json")
    validator = Draft202012Validator(schema)
    with (ROOT / "registries/TEMPORAL_CORRIDOR_WITNESS_REGISTRY.csv").open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    assert len(rows) == 4
    for row in rows:
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        model = load(model_path)
        cert = load(cert_path)
        assert list(validator.iter_errors(cert)) == []
        assert digest(model_path) == row["model_sha256"] == cert["model_sha256"]
        audit = audit_strict_corridor(model)
        assert audit.strict_corridor_valid
        assert audit.failed_obligations == ()
        assert audit.to_dict() == cert["audit"]
        assert cert["claim_lanes"] == ["S-L"]
        assert "autonomy" not in json.dumps(cert).lower()


def test_composed_corridor_has_two_atomic_legs_without_endpoint_mixedness() -> None:
    model = load(ROOT / "models/corridors/COR-POS-02-COMPOSED.model.json")
    audit = audit_strict_corridor(model)
    assert audit.strict_corridor_valid
    assert audit.atomic_leg_count == 2
    assert audit.mixed_stage_count == 2
    source = model["carrier_chain"][0]["code"]
    target = model["carrier_chain"][-1]["code"]
    assert not any(
        source in [item["code"] for item in stage["active_support"]]
        and target in [item["code"] for item in stage["active_support"]]
        for stage in model["episode"]["stages"]
    )
