from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from cst_tt.corridor import (
    audit_corridor_composition,
    audit_strict_corridor,
    compose_corridor_models,
    frontier_compatible,
)

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict:
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def test_corridor_composition_certificate_replays_exactly() -> None:
    left = load(ROOT / "models/corridors/COR-POS-02A.model.json")
    right = load(ROOT / "models/corridors/COR-POS-02B.model.json")
    expected = load(ROOT / "models/corridors/COR-POS-02-COMPOSED.model.json")
    composed = compose_corridor_models(left, right, model_id="COR-POS-02-COMPOSED", title="two-leg strict carrier-chain temporal corridor")
    assert composed == expected
    audit = audit_corridor_composition(left, right, expected)
    assert audit.composition_valid
    assert audit.chain_rule_satisfied
    assert not audit.old_endpoint_mixed_rule_satisfied
    assert audit.failed_obligations == ()
    cert = load(ROOT / "formal/certificates/corridors/COR-COMP-01.certificate.json")
    schema = load(ROOT / "schemas/certificates/corridor_composition_certificate.schema.json")
    assert list(Draft202012Validator(schema).iter_errors(cert)) == []
    assert cert["audit"] == audit.to_dict()
    for key, rel in (("left", cert["left_model_ref"]), ("right", cert["right_model_ref"]), ("composite", cert["composite_model_ref"])):
        assert cert["source_hashes"][key] == digest(ROOT / rel)


def test_all_composition_interface_controls_fail_the_registered_frontier_gate() -> None:
    with (ROOT / "registries/CORRIDOR_CONTROL_REGISTRY.csv").open(newline="", encoding="utf-8") as handle:
        rows = [row for row in csv.DictReader(handle) if row["family"] == "composition-interface"]
    assert {row["control_id"] for row in rows} == {"COMP-C01", "COMP-C02", "COMP-C03"}
    for row in rows:
        bundle = load(ROOT / row["model_ref"])
        assert audit_strict_corridor(bundle["left"]).strict_corridor_valid
        assert audit_strict_corridor(bundle["right"]).strict_corridor_valid
        assert not frontier_compatible(bundle["left"], bundle["right"])
        cert = load(ROOT / row["certificate_ref"])
        assert row["expected_failed_obligation"] in cert["observed_failed_obligations"]
        assert cert["control_passed"] is True
