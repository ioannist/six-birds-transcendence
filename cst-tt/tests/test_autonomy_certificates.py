from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from cst_tt.withdrawal_autonomy_checker import (
    audit_autonomy,
    bounded_invariant_algorithm_exhaustion,
    finite_horizon_word_count,
)

ROOT = Path(__file__).resolve().parents[1]


def load(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validator(name: str) -> Draft202012Validator:
    schema = load(ROOT / "schemas/certificates" / name)
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_positive_autonomy_certificate_rechecks_and_is_hash_bound() -> None:
    cert_path = ROOT / "formal/certificates/autonomy/AUT-POS-01.certificate.json"
    cert = load(cert_path)
    assert list(validator("post_withdrawal_autonomy_certificate.schema.json").iter_errors(cert)) == []
    model_path = ROOT / cert["model_ref"]
    assert digest(model_path) == cert["model_sha256"]
    audit = audit_autonomy(load(model_path))
    assert audit.autonomy_valid
    assert cert["audit"] == audit.to_dict()
    assert tuple(cert["computed_invariant_state_ids"]) == audit.computed_invariant_state_ids
    assert cert["finite_horizon"] == 6
    assert cert["finite_words_checked"] == finite_horizon_word_count(2, 6) == 127
    assert cert["claim_lanes"] == ["A"]
    assert audit.withdrawal_complete
    assert audit.retained_resources_target_owned
    assert audit.target_owned_responses
    assert audit.anti_stall_on_invariant
    assert audit.budget_solvent_on_invariant


def test_autonomy_controls_recheck_expected_failures_and_collapse_traces() -> None:
    rows = list(csv.DictReader((ROOT / "registries/AUTONOMY_CONTROL_REGISTRY.csv").open(newline="", encoding="utf-8")))
    assert len(rows) == 12
    schema = validator("autonomy_control_certificate.schema.json")
    for row in rows:
        cert = load(ROOT / row["certificate_ref"])
        assert list(schema.iter_errors(cert)) == []
        model_path = ROOT / row["model_ref"]
        assert digest(model_path) == cert["model_sha256"]
        audit = audit_autonomy(load(model_path))
        assert not audit.autonomy_valid
        assert cert["audit"] == audit.to_dict()
        assert row["expected_primary_failure"] in audit.failed_obligations
        assert cert["collapse_trace"] == [step.to_dict() for step in audit.collapse_trace]
    by_id = {row["control_id"]: row for row in rows}
    assert int(by_id["AUT-C01"]["computed_invariant_size"]) == 0
    assert int(by_id["AUT-C05"]["computed_invariant_size"]) == 0
    assert int(by_id["AUT-C06"]["collapse_trace_length"]) == 2


def test_invariant_algorithm_matches_bruteforce_over_declared_family() -> None:
    result = bounded_invariant_algorithm_exhaustion()
    frozen = load(ROOT / "formal/certificates/search/AUTONOMY_INVARIANT_EXHAUSTION.json")
    assert result["candidate_count"] == 4_096
    assert result["algorithm_bruteforce_mismatch_count"] == 0
    assert result["endpoint_autonomous_count"] == 76
    for key, value in result.items():
        assert frozen[key] == value
