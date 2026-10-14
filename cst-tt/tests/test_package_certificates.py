from __future__ import annotations

import csv
import hashlib
import json
from pathlib import Path

from jsonschema import Draft202012Validator

from cst_tt.package_gluing import audit_package, audit_staged_assembly

ROOT = Path(__file__).resolve().parents[1]


def load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def digest(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def schema_validator(name: str) -> Draft202012Validator:
    schema = load_json(ROOT / "schemas/certificates" / name)
    Draft202012Validator.check_schema(schema)
    return Draft202012Validator(schema)


def test_package_certificates_validate_bind_models_and_recheck() -> None:
    validator = schema_validator("package_certificate.schema.json")
    rows = list(
        csv.DictReader(
            (ROOT / "registries/PACKAGE_WITNESS_REGISTRY.csv").open(newline="", encoding="utf-8")
        )
    )
    assert len(rows) == 4
    legacy_rows = [row for row in rows if row["result_status"] == "checked-finite-package-certificate"]
    assert len(legacy_rows) == 2
    lean_text = "\n".join(
        path.read_text(encoding="utf-8") for path in sorted((ROOT / "CSTTT/Package").glob("*.lean"))
    )
    for row in legacy_rows:
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        model = load_json(model_path)
        cert = load_json(cert_path)
        errors = sorted(validator.iter_errors(cert), key=lambda error: list(error.path))
        assert errors == [], (row["package_id"], [error.message for error in errors])
        assert digest(model_path) == row["model_sha256"] == cert["model_sha256"]
        assert cert["model_ref"] == row["model_ref"]
        assert cert["certificate_id"] == row["package_id"]
        assert cert["claim_lanes"] == ["S-R"]
        assert cert["result_status"] == "checked-finite-package-certificate"
        audit = audit_package(model)
        assert audit.integrated_package_valid
        assert cert["audit"] == audit.to_dict()
        for declaration in cert["theorem_evidence"]["lean_declarations"]:
            assert declaration.split(".")[-1] in lean_text


def test_staged_certificate_validates_binds_all_three_artifacts_and_rechecks() -> None:
    validator = schema_validator("staged_package_certificate.schema.json")
    cert = load_json(ROOT / "formal/certificates/packages/STG-POS-01.certificate.json")
    errors = sorted(validator.iter_errors(cert), key=lambda error: list(error.path))
    assert errors == [], [error.message for error in errors]
    assembly_path = ROOT / cert["assembly_ref"]
    source_path = ROOT / cert["source_model_ref"]
    target_path = ROOT / cert["target_model_ref"]
    assert digest(assembly_path) == cert["assembly_sha256"]
    assert digest(source_path) == cert["source_model_sha256"]
    assert digest(target_path) == cert["target_model_sha256"]
    assert cert["claim_lanes"] == ["S-T", "S-R"]
    audit = audit_staged_assembly(load_json(assembly_path), load_json(source_path), load_json(target_path))
    assert audit.staged_assembly_valid
    assert cert["audit"] == audit.to_dict()


def test_all_control_certificates_validate_bind_and_match_recomputed_failures() -> None:
    validator = schema_validator("package_control_certificate.schema.json")
    source = load_json(ROOT / "models/packages/PKG-POS-02-SOURCE.model.json")
    target = load_json(ROOT / "models/packages/PKG-POS-01-TARGET.model.json")
    rows = list(
        csv.DictReader(
            (ROOT / "registries/PACKAGE_CONTROL_REGISTRY.csv").open(newline="", encoding="utf-8")
        )
    )
    assert len(rows) == 18
    for row in rows:
        artifact_path = ROOT / row["artifact_ref"]
        cert = load_json(ROOT / row["certificate_ref"])
        errors = sorted(validator.iter_errors(cert), key=lambda error: list(error.path))
        assert errors == [], (row["control_id"], [error.message for error in errors])
        assert digest(artifact_path) == cert["artifact_sha256"]
        assert cert["artifact_ref"] == row["artifact_ref"]
        assert cert["control_id"] == row["control_id"]
        assert cert["expected_primary_failure"] == row["expected_primary_failure"]
        if row["control_kind"] == "package":
            audit = audit_package(load_json(artifact_path))
            observed = list(audit.failed_obligations)
            assert not audit.integrated_package_valid
        else:
            audit = audit_staged_assembly(load_json(artifact_path), source, target)
            observed = list(audit.failed_obligations)
            assert not audit.staged_assembly_valid
        assert cert["observed_failures"] == observed
        assert row["expected_primary_failure"] in observed


def test_obligation_registries_are_complete_and_independently_typed() -> None:
    package_rows = list(
        csv.DictReader(
            (ROOT / "registries/PACKAGE_OBLIGATION_REGISTRY.csv").open(newline="", encoding="utf-8")
        )
    )
    staged_rows = list(
        csv.DictReader(
            (ROOT / "registries/STAGED_ASSEMBLY_OBLIGATION_REGISTRY.csv").open(newline="", encoding="utf-8")
        )
    )
    assert [row["obligation_id"] for row in package_rows] == [f"PKG-O{i:02d}" for i in range(1, 11)]
    assert [row["obligation_id"] for row in staged_rows] == [f"STG-O{i:02d}" for i in range(1, 11)]
    assert all(row["claim_lanes"] == "S-R" for row in package_rows)
    assert all(set(row["claim_lanes"].split(";")) <= {"S-T", "S-R"} for row in staged_rows)
    forbidden = {"S-L", "A", "O"}
    assert all(forbidden.isdisjoint(row["claim_lanes"].split(";")) for row in package_rows + staged_rows)


def test_positive_package_records_have_no_verdict_loaded_keys() -> None:
    forbidden = {
        "source",
        "source_carrier",
        "source_state",
        "source_package",
        "ancestry",
        "lineage",
        "corridor",
        "temporal_corridor",
        "fiach",
        "autonomy",
        "withdrawal",
        "consciousness",
        "survival",
        "identity",
        "phenomenal",
    }

    def walk(value: object) -> list[str]:
        hits: list[str] = []
        if isinstance(value, dict):
            for key, child in value.items():
                if str(key).lower().replace("-", "_") in forbidden:
                    hits.append(str(key))
                hits.extend(walk(child))
        elif isinstance(value, list):
            for child in value:
                hits.extend(walk(child))
        return hits

    for name in ("PKG-POS-01-TARGET.model.json", "PKG-POS-02-SOURCE.model.json"):
        assert walk(load_json(ROOT / "models/packages" / name)) == []


def test_handoff_aligned_package_certificates_validate_and_match_corridor_frontiers() -> None:
    validator = schema_validator("aligned_package_certificate.schema.json")
    rows = list(csv.DictReader((ROOT / "registries/HANDOFF_ALIGNED_PACKAGE_REGISTRY.csv").open(newline="", encoding="utf-8")))
    assert len(rows) == 2
    corridor = load_json(ROOT / "models/corridors/COR-POS-01.model.json")
    stages = {int(row["stage"]): row for row in corridor["episode"]["stages"]}
    for row in rows:
        model_path = ROOT / row["model_ref"]
        cert_path = ROOT / row["certificate_ref"]
        model = load_json(model_path)
        cert = load_json(cert_path)
        errors = sorted(validator.iter_errors(cert), key=lambda error: list(error.path))
        assert errors == [], (row["package_id"], [error.message for error in errors])
        assert digest(model_path) == cert["model_sha256"]
        audit = audit_package(model)
        assert audit.integrated_package_valid
        assert cert["audit"] == audit.to_dict()
        alignment = cert["handoff_alignment"]
        stage = stages[int(alignment["corridor_stage"])]
        c6 = next(item["assignment"] for item in model["clauses"] if item["clause"] == "C6_TEMPORAL_CLOSURE")
        assert c6["route_residue"] == stage["signature"]["route_residue"]
        assert c6["tick_phase"] == stage["signature"]["tick_index"]
        assert c6["record_before"] == stage["signature"]["record_value"]
        assert c6["maintenance_owner"] == stage["signature"]["maintenance_owner"]


def test_handoff_aligned_staged_certificate_rechecks() -> None:
    validator = schema_validator("aligned_staged_package_certificate.schema.json")
    cert = load_json(ROOT / "formal/certificates/packages/STG-POS-02-FIACH.certificate.json")
    assert list(validator.iter_errors(cert)) == []
    assembly = load_json(ROOT / cert["assembly_ref"])
    source = load_json(ROOT / cert["source_model_ref"])
    target = load_json(ROOT / cert["target_model_ref"])
    audit = audit_staged_assembly(assembly, source, target)
    assert audit.staged_assembly_valid
    assert cert["audit"] == audit.to_dict()
