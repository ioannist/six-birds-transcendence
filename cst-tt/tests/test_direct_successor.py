from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from cst_tt.corridor import audit_direct_successor, audit_direct_successor_path

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_atomic_direct_successor_certificates_replay_and_exclude_detached_patterns() -> None:
    schema = load(ROOT / "schemas/certificates/direct_successor_landed.schema.json")
    validator = Draft202012Validator(schema)
    with (ROOT / "registries/DIRECT_SUCCESSOR_REGISTRY.csv").open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    assert len(rows) == 3
    for row in rows:
        model_path = ROOT / row["model_ref"]
        cert = load(ROOT / row["certificate_ref"])
        audit = audit_direct_successor(load(model_path))
        assert audit.direct_successor_valid
        assert not audit.detached_operational_pattern
        assert audit.failed_obligations == ()
        assert cert["audit"] == audit.to_dict()
        assert cert["model_sha256"] == row["model_sha256"] == digest(model_path)
        assert list(validator.iter_errors(cert)) == []


def test_direct_successor_path_composes_without_creating_atomic_endpoint_edge() -> None:
    first = load(ROOT / "models/direct_successor/DS-POS-02A.model.json")
    second = load(ROOT / "models/direct_successor/DS-POS-02B.model.json")
    audit = audit_direct_successor_path([first, second])
    assert audit.path_valid
    assert not audit.atomic_endpoint_edge_present
    cert = load(ROOT / "formal/certificates/direct_successor/DS-PATH-POS-01.certificate.json")
    schema = load(ROOT / "schemas/certificates/direct_successor_path_certificate.schema.json")
    assert list(Draft202012Validator(schema).iter_errors(cert)) == []
    assert cert["audit"] == audit.to_dict()
    assert cert["atomic_model_hashes"] == [
        digest(ROOT / rel) for rel in cert["atomic_model_refs"]
    ]


def test_all_direct_successor_controls_fail_the_registered_gate() -> None:
    schema = load(ROOT / "schemas/certificates/corridor_control_certificate.schema.json")
    validator = Draft202012Validator(schema)
    with (ROOT / "registries/DIRECT_SUCCESSOR_CONTROL_REGISTRY.csv").open(newline="", encoding="utf-8") as handle:
        rows = list(csv.DictReader(handle))
    assert len(rows) == 16
    for row in rows:
        model = load(ROOT / row["model_ref"])
        audit = audit_direct_successor(model)
        assert not audit.direct_successor_valid
        assert row["expected_failed_obligation"] in audit.failed_obligations
        cert = load(ROOT / row["certificate_ref"])
        assert cert["control_passed"] is True
        assert list(validator.iter_errors(cert)) == []
