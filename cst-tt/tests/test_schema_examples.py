from __future__ import annotations

import json
from pathlib import Path

from jsonschema import Draft202012Validator

ROOT = Path(__file__).resolve().parents[1]
MAPPING = {
    "temporal_signature.schema.json": "temporal_signature.scaffold.json",
    "package_certificate.schema.json": "package_certificate.scaffold.json",
    "temporal_corridor.schema.json": "temporal_corridor.scaffold.json",
    "direct_successor.schema.json": "direct_successor.scaffold.json",
    "autonomy_certificate.schema.json": "autonomy_certificate.scaffold.json",
    "temporal_fiach_certificate.schema.json": "temporal_fiach_certificate.scaffold.json",
    "ancestry_certificate.schema.json": "ancestry_certificate.scaffold.json",
    "countermodel_certificate.schema.json": "countermodel_certificate.scaffold.json",
    "staged_package_certificate.schema.json": "staged_package_certificate.scaffold.json",
    "package_control_certificate.schema.json": "package_control_certificate.scaffold.json",
    "temporal_transport_certificate.schema.json": "temporal_transport_certificate.scaffold.json",
    "route_discipline_certificate.schema.json": "route_discipline_certificate.scaffold.json",
    "memory_repair_certificate.schema.json": "memory_repair_certificate.scaffold.json",
    "record_arrow_certificate.schema.json": "record_arrow_certificate.scaffold.json",
    "transport_control_certificate.schema.json": "transport_control_certificate.scaffold.json",
    "strict_temporal_corridor_certificate.schema.json": "strict_temporal_corridor_certificate.scaffold.json",
    "corridor_composition_certificate.schema.json": "corridor_composition_certificate.scaffold.json",
    "direct_successor_landed.schema.json": "direct_successor_landed.scaffold.json",
    "direct_successor_path_certificate.schema.json": "direct_successor_path_certificate.scaffold.json",
    "corridor_control_certificate.schema.json": "corridor_control_certificate.scaffold.json",
    "aligned_package_certificate.schema.json": "aligned_package_certificate.scaffold.json",
    "aligned_staged_package_certificate.schema.json": "aligned_staged_package_certificate.scaffold.json",
    "post_withdrawal_autonomy_certificate.schema.json": "post_withdrawal_autonomy_certificate.scaffold.json",
    "autonomy_control_certificate.schema.json": "autonomy_control_certificate.scaffold.json",
    "temporal_fiach_landed_certificate.schema.json": "temporal_fiach_landed_certificate.scaffold.json",
    "fiach_lane_control_certificate.schema.json": "fiach_lane_control_certificate.scaffold.json",
    "full_handoff_composition_certificate.schema.json": "full_handoff_composition_certificate.scaffold.json",
    "temporal_fission_certificate.schema.json": "temporal_fission_certificate.scaffold.json",
    "fusion_boundary_certificate.schema.json": "fusion_boundary_certificate.scaffold.json",
    "route_completion_certificate.schema.json": "route_completion_certificate.scaffold.json",
    "toy_suite_closure_certificate.schema.json": "toy_suite_closure_certificate.scaffold.json",
    "generalized_continuity_certificate.schema.json": "generalized_continuity_certificate.scaffold.json",
    "defect_profile_certificate.schema.json": "defect_profile_certificate.scaffold.json",
    "temporal_robustness_certificate.schema.json": "temporal_robustness_certificate.scaffold.json",
    "unbounded_invariant_certificate.schema.json": "unbounded_invariant_certificate.scaffold.json",
}


def load(path: Path) -> object:
    return json.loads(path.read_text(encoding="utf-8"))


def test_every_certificate_schema_is_valid_and_has_one_scaffold_example() -> None:
    assert set(MAPPING) == {p.name for p in (ROOT / "schemas/certificates").glob("*.schema.json")}
    assert set(MAPPING.values()) == {p.name for p in (ROOT / "examples/scaffold").glob("*.json")}
    for schema_name, example_name in MAPPING.items():
        schema = load(ROOT / "schemas/certificates" / schema_name)
        Draft202012Validator.check_schema(schema)
        validator = Draft202012Validator(schema)
        errors = sorted(validator.iter_errors(load(ROOT / "examples/scaffold" / example_name)), key=lambda e: list(e.path))
        assert errors == [], [error.message for error in errors]


def test_scaffold_examples_do_not_claim_landed_evidence() -> None:
    for path in (ROOT / "examples/scaffold").glob("*.json"):
        text = path.read_text(encoding="utf-8")
        assert '"result_status": "checked-' not in text
        assert '"result_status": "proved"' not in text
        assert '"result_status": "certified"' not in text
    countermodel = load(ROOT / "examples/scaffold/countermodel_certificate.scaffold.json")
    assert countermodel["result_status"] == "scaffold-only"
