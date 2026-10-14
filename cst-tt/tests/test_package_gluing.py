from __future__ import annotations

import csv
import json
from pathlib import Path

from cst_tt.package_gluing import audit_package, audit_staged_assembly, bounded_gluing_exhaustion

ROOT = Path(__file__).resolve().parents[1]


def load_json(path: Path) -> dict[str, object]:
    return json.loads(path.read_text(encoding="utf-8"))


def test_positive_source_and_target_are_independently_integrated() -> None:
    source = load_json(ROOT / "models/packages/PKG-POS-02-SOURCE.model.json")
    target = load_json(ROOT / "models/packages/PKG-POS-01-TARGET.model.json")
    source_audit = audit_package(source)
    target_audit = audit_package(target)
    assert source_audit.integrated_package_valid
    assert target_audit.integrated_package_valid
    assert source["target"]["code"] != target["target"]["code"]
    for audit in (source_audit, target_audit):
        assert audit.exact_clause_coverage
        assert audit.unique_clause_slots
        assert audit.every_scope_exact
        assert audit.every_clause_accepted
        assert audit.every_hard_gate_passed
        assert audit.join_tree.valid_shape
        assert audit.join_tree.running_intersection
        assert audit.join_tree.edge_compatible
        assert audit.global_constructible
        assert audit.supplied_global_matches
        assert audit.global_restricts_to_every_local
        assert audit.target_owned
        assert audit.forbidden_field_free
        assert audit.failed_obligations == ()
        assert len(audit.clause_audits) == 8
        assert len(audit.derived_global_assignment) == 44


def test_c6_has_substantive_internal_time_and_does_not_replace_other_clauses() -> None:
    model = load_json(ROOT / "models/packages/PKG-POS-01-TARGET.model.json")
    audit = audit_package(model)
    temporal = audit.temporal_substance
    assert temporal.valid
    assert temporal.future_sufficient
    assert temporal.order_stable
    assert temporal.successor_available
    assert temporal.viable_tick
    assert temporal.genuine_progress
    assert temporal.endogenous_arrow
    assert temporal.record_descends
    assert temporal.route_residue_retained
    assert temporal.no_external_scheduler
    assert temporal.temporal_owner_matches
    assert temporal.maintenance_owner_matches
    assert {row.clause for row in audit.clause_audits} == {
        "C1_OBJECTHOOD",
        "C2_STRICT_PROMOTION",
        "C3_REFLEXIVE_SELF_COORDINATE",
        "C4_INTERFACE_NONEXPOSURE",
        "C5_ACTION_CREDIT",
        "C6_TEMPORAL_CLOSURE",
        "C7_BINDING_RECOMBINATION",
        "C8_VIABILITY_REPAIR",
    }


def test_every_package_control_fails_its_registered_primary_obligation() -> None:
    rows = list(
        csv.DictReader(
            (ROOT / "registries/PACKAGE_CONTROL_REGISTRY.csv").open(newline="", encoding="utf-8")
        )
    )
    package_rows = [row for row in rows if row["control_kind"] == "package"]
    assert len(package_rows) == 17
    for row in package_rows:
        model = load_json(ROOT / row["artifact_ref"])
        audit = audit_package(model)
        assert not audit.integrated_package_valid, row["control_id"]
        assert row["expected_primary_failure"] in audit.failed_obligations, row["control_id"]
        assert set(audit.failed_obligations) == set(filter(None, row["observed_failures"].split(";")))


def test_staged_heterogeneous_assembly_is_valid_but_does_not_assert_lineage() -> None:
    source = load_json(ROOT / "models/packages/PKG-POS-02-SOURCE.model.json")
    target = load_json(ROOT / "models/packages/PKG-POS-01-TARGET.model.json")
    assembly = load_json(ROOT / "models/packages/STG-POS-01.assembly.json")
    audit = audit_staged_assembly(assembly, source, target)
    assert audit.staged_assembly_valid
    assert audit.source_package_valid
    assert audit.target_package_valid
    assert audit.carriers_distinct
    assert audit.exactly_eight_clause_maps
    assert audit.maps_separately_typed
    assert audit.coordinate_maps_total
    assert audit.value_maps_sound
    assert audit.hard_gates_never_averaged
    assert audit.target_global_assembled
    assert audit.forbidden_verdict_fields_absent
    assert audit.failed_obligations == ()
    serialized = json.dumps(assembly).lower()
    for forbidden in (
        '"lineage"',
        '"ancestry"',
        '"temporal_corridor"',
        '"autonomy"',
        '"fiach"',
        '"survival"',
        '"identity"',
        '"consciousness"',
    ):
        assert forbidden not in serialized


def test_staged_value_map_control_is_rejected() -> None:
    source = load_json(ROOT / "models/packages/PKG-POS-02-SOURCE.model.json")
    target = load_json(ROOT / "models/packages/PKG-POS-01-TARGET.model.json")
    assembly = load_json(ROOT / "models/packages/controls/SC-01.assembly.json")
    audit = audit_staged_assembly(assembly, source, target)
    assert not audit.staged_assembly_valid
    assert audit.failed_obligations == ("STG-O07-value-translation-soundness",)


def test_bounded_gluing_exhaustion_has_no_violation() -> None:
    result = bounded_gluing_exhaustion()
    assert result["candidates_examined"] == 1_025_416
    assert result["premise_cases"] == 18_972
    assert result["glued_cases"] == 18_972
    assert result["violations"] == []
    assert result["status"] == "PASS"
    assert len(result["configurations"]) == 5
