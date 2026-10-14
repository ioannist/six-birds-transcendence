from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from cst_tt.transport import audit_temporal_transport

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_two_positive_temporal_transport_certificates_recompute() -> None:
    rows = list(csv.DictReader((ROOT / "registries/TEMPORAL_TRANSPORT_WITNESS_REGISTRY.csv").open()))
    assert len(rows) == 2
    flat_cert = load(ROOT / "formal/certificates/routes/ROUTE-POS-01.certificate.json")
    for row in rows:
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        model = load(model_path)
        cert = load(cert_path)
        flat_valid = bool(flat_cert["audit"]["flatness_valid"]) if row["route_status"] == "flat" else None
        audit = audit_temporal_transport(model, flatness_certificate_valid=flat_valid)
        assert audit.transport_valid
        assert audit.to_dict() == cert["audit"]
        assert cert["model_sha256"] == digest(model_path)
        assert cert["claim_lanes"] == ["S-T"]
        assert cert["route_status"] == row["route_status"]


def test_temporal_transport_certificates_validate_against_schema() -> None:
    schema = load(ROOT / "schemas/certificates/temporal_transport_certificate.schema.json")
    validator = Draft202012Validator(schema)
    for path in sorted((ROOT / "formal/certificates/transport").glob("TR-POS-*.certificate.json")):
        assert not list(validator.iter_errors(load(path)))


def test_route_indexed_transport_retains_noncollapsed_residue() -> None:
    cert = load(ROOT / "formal/certificates/transport/TR-POS-01.certificate.json")
    assert cert["audit"]["route_status"] == "route-indexed"
    assert cert["audit"]["route_residue_retention_noncollapsing"] is True


def test_flat_transport_is_bound_to_separate_route_certificate() -> None:
    model = load(ROOT / "models/transport/TR-POS-02-FLAT.model.json")
    assert model["bridge"]["flatness_certificate_ref"] == "formal/certificates/transport/ROUTE-POS-01.certificate.json" or model["bridge"]["flatness_certificate_ref"] == "formal/certificates/transport/ROUTE-POS-01.certificate.json".replace("transport", "routes", 1)
    route = load(ROOT / "formal/certificates/routes/ROUTE-POS-01.certificate.json")
    assert route["audit"]["flatness_valid"] is True
