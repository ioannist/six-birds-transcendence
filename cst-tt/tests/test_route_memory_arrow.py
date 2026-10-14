from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from cst_tt.transport import audit_memory_repair, audit_record_arrow, audit_route_discipline

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict:
    value = json.loads(path.read_text(encoding="utf-8"))
    assert isinstance(value, dict)
    return value


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_confluent_route_positive_and_holonomy_negative() -> None:
    positive = audit_route_discipline(load(ROOT / "models/routes/ROUTE-POS-01.model.json"))
    negative = audit_route_discipline(load(ROOT / "models/routes/ROUTE-NEG-01.model.json"))
    assert positive.flatness_valid
    assert positive.global_now_factorization_exists
    assert not positive.nonzero_translation_holonomy_witnessed
    assert negative.route_audit_valid
    assert not negative.flatness_valid
    assert not negative.global_now_factorization_exists
    assert negative.nonzero_translation_holonomy_witnessed
    assert negative.memory_or_flatness_satisfied


def test_route_certificates_validate_and_hash_bind() -> None:
    schema = load(ROOT / "schemas/certificates/route_discipline_certificate.schema.json")
    validator = Draft202012Validator(schema)
    rows = list(csv.DictReader((ROOT / "registries/ROUTE_DISCIPLINE_REGISTRY.csv").open()))
    assert len(rows) == 2
    for row in rows:
        cert_path = ROOT / row["certificate_ref"]
        model_path = ROOT / row["model_ref"]
        cert = load(cert_path)
        assert not list(validator.iter_errors(cert))
        assert cert["model_sha256"] == digest(model_path)
        assert cert["audit"] == audit_route_discipline(load(model_path)).to_dict()


def test_memory_repair_and_flat_alternative() -> None:
    memory = audit_memory_repair(load(ROOT / "models/memory/MEM-POS-01.model.json"))
    flat = audit_memory_repair(load(ROOT / "models/memory/MEM-FLAT-01.model.json"))
    assert memory.current_only_predictor_impossible
    assert memory.route_memory_separates_collision
    assert memory.refined_predictor_correct
    assert memory.predictor_functions_examined == 2
    assert flat.flat_alternative
    assert flat.current_only_predictor_exists
    assert flat.predictor_functions_examined == 1


def test_memory_certificates_validate() -> None:
    schema = load(ROOT / "schemas/certificates/memory_repair_certificate.schema.json")
    validator = Draft202012Validator(schema)
    for path in sorted((ROOT / "formal/certificates/memory").glob("*.certificate.json")):
        cert = load(path)
        assert not list(validator.iter_errors(cert))
        model = load(ROOT / cert["model_ref"])
        assert cert["audit"] == audit_memory_repair(model).to_dict()


def test_strict_record_arrow_and_constant_map_boundary() -> None:
    positive = audit_record_arrow(load(ROOT / "models/arrow/ARROW-POS-01.model.json"))
    constant = audit_record_arrow(load(ROOT / "models/transport/controls/ARROW-C01.model.json"))
    assert positive.arrow_transport_valid
    assert positive.maps_examined_in_bounded_search == 125
    assert positive.strictly_monotone_maps_in_bounded_search == 10
    assert constant.nonstrict_monotone
    assert not constant.strict_progress_preserved


def test_arrow_certificate_validates() -> None:
    schema = load(ROOT / "schemas/certificates/record_arrow_certificate.schema.json")
    cert = load(ROOT / "formal/certificates/arrow/ARROW-POS-01.certificate.json")
    assert not list(Draft202012Validator(schema).iter_errors(cert))
    assert cert["model_sha256"] == digest(ROOT / cert["model_ref"])
