from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from cst_tt.countermodels import recheck

ROOT = Path(__file__).resolve().parents[1]


def load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_every_countermodel_certificate_validates_and_binds_exact_model() -> None:
    schema = load_json(ROOT / "schemas/certificates/countermodel_certificate.schema.json")
    Draft202012Validator.check_schema(schema)
    validator = Draft202012Validator(schema)
    rows = list(csv.DictReader((ROOT / "registries/COUNTERMODEL_REGISTRY.csv").open(newline="", encoding="utf-8")))
    assert len(rows) == 15
    kernel = (ROOT / "CSTTT/Countermodels/Kernel.lean").read_text(encoding="utf-8")
    for row in rows:
        model_path = ROOT / row["model_ref"]
        certificate_path = ROOT / row["certificate_ref"]
        card_path = ROOT / row["model_card_ref"]
        assert model_path.is_file()
        assert certificate_path.is_file()
        assert card_path.is_file()
        model = load_json(model_path)
        certificate = load_json(certificate_path)
        errors = sorted(validator.iter_errors(certificate), key=lambda error: list(error.path))
        assert errors == [], (row["countermodel_id"], [error.message for error in errors])
        assert hashlib.sha256(model_path.read_bytes()).hexdigest() == certificate["finite_model_sha256"]
        assert certificate["finite_model_ref"] == row["model_ref"]
        assert certificate["countermodel_id"] == row["countermodel_id"]
        assert certificate["result_status"] == "checked-finite-countermodel"
        assert certificate["claim_ceiling"] == "structural-boundary-only"
        assert certificate["checker"]["lean_compile_status"] == "pending-toolchain"
        lean_name = row["lean_declaration"].split(".")[-1]
        assert lean_name in kernel
        check = recheck(row["countermodel_id"], model["model"])
        assert check.qualifies
        assert dict(sorted(check.premises.items())) == model["premise_checks"]
        assert dict(sorted(check.conclusion_failures.items())) == model["conclusion_failure_checks"]


def test_minimality_certificates_report_no_smaller_qualifying_candidate() -> None:
    for path in sorted((ROOT / "formal/certificates/countermodels").glob("CM-*.certificate.json")):
        certificate = load_json(path)
        search = certificate["search"]
        assert search["algorithm"] == "deterministic-exhaustive-enumeration"
        assert search["minimality_result"] == "proved-by-exhaustive-bounded-search"
        assert search["smaller_candidates_explored"] >= 0
        assert search["same_size_candidates_explored"] >= search["same_size_qualifying_candidates"] >= 1
        assert search["candidates_explored"] >= search["qualifying_candidates"] >= 1
        assert search["lower_bound_argument"]
