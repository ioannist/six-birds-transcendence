from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from cst_tt.fiach import audit_temporal_fiach, lane_truth_table, replay_component_certificates

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def schema(name: str) -> Draft202012Validator:
    payload = load(ROOT / "schemas/certificates" / name)
    Draft202012Validator.check_schema(payload)
    return Draft202012Validator(payload)


def test_integrated_temporal_fiach_certificate_rechecks_all_links() -> None:
    cert = load(ROOT / "formal/certificates/fiach/FIACH-POS-01.certificate.json")
    assert list(schema("temporal_fiach_landed_certificate.schema.json").iter_errors(cert)) == []
    spec = load(ROOT / "models/fiach/FIACH-POS-01.model.json")
    audit = audit_temporal_fiach(spec, ROOT)
    assert audit.aggregate_valid
    assert cert["audit"] == audit.to_dict()
    assert cert["lane_results"] == {"S-T": True, "S-R": True, "S-L": True, "A": True}
    assert all(replay_component_certificates(spec, ROOT).values())
    for key, ref in cert["component_refs"].items():
        assert digest(ROOT / ref) == cert["component_sha256"][key]
    assert audit.corridor_package_temporal_frontier_linked
    assert audit.corridor_autonomy_handoff_linked
    assert audit.autonomy_package_contract_linked
    assert audit.route_status_linked
    assert audit.recognition_separate
    assert audit.ontology_absent


def test_one_and_two_lane_controls_never_aggregate() -> None:
    rows = list(csv.DictReader((ROOT / "registries/FIACH_LANE_CONTROL_REGISTRY.csv").open(newline="", encoding="utf-8")))
    assert len(rows) == 6
    validator = schema("fiach_lane_control_certificate.schema.json")
    observed_patterns: set[tuple[bool, bool, bool]] = set()
    for row in rows:
        cert = load(ROOT / row["certificate_ref"])
        assert list(validator.iter_errors(cert)) == []
        spec = load(ROOT / row["model_ref"])
        audit = audit_temporal_fiach(spec, ROOT)
        assert not audit.aggregate_valid
        assert cert["audit"] == audit.to_dict()
        pattern = (audit.structural_realization_lane, audit.structural_lineage_lane, audit.autonomy_lane)
        observed_patterns.add(pattern)
        assert pattern == (row["S-R"] == "true", row["S-L"] == "true", row["A"] == "true")
    assert observed_patterns == {
        (True, False, False), (False, True, False), (False, False, True),
        (True, True, False), (True, False, True), (False, True, True),
    }


def test_lane_truth_table_is_exact_conjunction() -> None:
    result = lane_truth_table()
    frozen = load(ROOT / "formal/certificates/search/FIACH_LANE_TRUTH_TABLE.json")
    assert result == frozen
    assert result["row_count"] == 8
    assert result["positive_row_count"] == 1
    assert result["negative_row_count"] == 7
    assert result["conjunction_exact"] is True
