from __future__ import annotations

from collections import Counter
from pathlib import Path

from cst_tt.registry import duplicate_values, read_csv

ROOT = Path(__file__).resolve().parents[1]


def split_ids(value: str) -> set[str]:
    return {item for item in value.split(";") if item}


def test_theorem_registry_statuses_and_cross_references() -> None:
    rows = read_csv(ROOT / "registries/THEOREM_REGISTRY.csv")
    assert len(rows) == 39
    assert duplicate_values(rows, "theorem_id") == set()
    assert duplicate_values(rows, "lean_statement") == set()
    theorem_ids = {row["theorem_id"] for row in rows}
    toy_ids = {row["toy_id"] for row in read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")}
    statuses = Counter(row["status"] for row in rows)
    assert statuses == Counter(
        {
            "open-scaffold": 8,
            "proof-source-and-executable-certificate-landed": 19,
            "checked-finite-countermodel": 5,
            "proof-source-and-checked-finite-countermodel": 7,
        }
    )
    by_id = {row["theorem_id"]: row for row in rows}
    assert by_id["TTH-01"]["lean_statement"] == "CSTTT.PackageTheory.acyclicLocalWitnessGluing"
    assert by_id["TTH-02"]["lean_statement"] == "CSTTT.PackageTheory.stagedHeterogeneousPackageAssembly"
    for row in rows:
        assert row["phase"].startswith("CST-TT-")
        assert row["lean_statement"].startswith("CSTTT.")
        assert split_ids(row["dependencies"]).issubset(theorem_ids)
        assert split_ids(row["toy_dependencies"]).issubset(toy_ids)
        assert row["claim_ceiling"]
        for legacy_id in split_ids(row["legacy_provenance_ids"]):
            assert legacy_id.startswith(("PTH-", "FTH-"))


def test_countermodel_registry_remains_frozen() -> None:
    rows = read_csv(ROOT / "registries/COUNTERMODEL_REGISTRY.csv")
    assert len(rows) == 15
    assert duplicate_values(rows, "countermodel_id") == set()
    assert {row["countermodel_id"] for row in rows} == {f"CM-{i:02d}" for i in range(1, 16)}
    assert all(row["result_status"] == "checked-finite-countermodel" for row in rows)


def test_toy_registry_preserves_prior_assets_and_adds_strengthenings() -> None:
    rows = read_csv(ROOT / "registries/TOY_MODEL_REGISTRY.csv")
    assert len(rows) == 28
    assert duplicate_values(rows, "toy_id") == set()
    by_id = {row["toy_id"]: row for row in rows}
    assert by_id["TTM-18"]["phase"] == "CST-TT-02"
    assert by_id["TTM-19"]["phase"] == "CST-TT-02"
    assert by_id["TTM-01"]["status"] == "checked-positive-instance"
    assert by_id["TTM-03"]["status"] == "checked-positive-witness-and-generalized-embedding"
    assert "CST-TT-07A proves exact incomparability" in by_id["TTM-03"]["notes"]
    assert {f"TTM-{index:02d}" for index in range(20, 25)}.issubset(by_id)
    assert by_id["TTM-20"]["phase"] == "CST-TT-07A"
    assert by_id["TTM-21"]["discriminates"] == "TTS-02;TTN-10"
    assert by_id["TTM-22"]["status"] == "checked-positive-and-boundary-controls"
    assert by_id["TTM-23"]["status"] == "checked-positive-instance"
    assert by_id["TTM-24"]["status"] == "checked-bounded-family-and-proof-source"


def test_definition_registry_preserves_layer_order_and_adds_corridor_theory() -> None:
    rows = read_csv(ROOT / "registries/DEFINITION_REGISTRY.csv")
    assert len(rows) == 73
    assert duplicate_values(rows, "definition_id") == set()
    by_name = {row["name"]: row for row in rows}
    assert by_name["TemporalSignature"]["definition_id"] < by_name["TemporalCorridorData"]["definition_id"]
    assert by_name["IntegratedPackageCertificate"]["claim_lanes"] == "S-R"
    assert by_name["RootedJoinTree"]["module"] == "CSTTT/Package/FiniteGluing.lean"
    assert by_name["TemporalSubstance"]["module"] == "CSTTT/Package/TemporalPackage.lean"
    assert by_name["EightClauseIntegratedPackage"]["claim_lanes"] == "S-R"
    assert by_name["RepresentativeIndependent"]["module"] == "CSTTT/Transport/FiniteTemporalTransport.lean"
    assert by_name["NormalizationCertificate"]["module"] == "CSTTT/Transport/RouteDiscipline.lean"
    assert by_name["StrictlyMonotoneOn"]["claim_lanes"] == "S-T"
    assert by_name["AtomicTemporalCorridorData"]["module"] == "CSTTT/Corridor/FiniteTemporalCorridor.lean"
    assert by_name["CorridorSummaryData"]["module"] == "CSTTT/Corridor/Composition.lean"
    assert by_name["AtomicDirectSuccessorData"]["module"] == "CSTTT/Corridor/FiniteDirectSuccessor.lean"
    assert by_name["DirectSuccessorPathData"]["claim_lanes"] == "S-L"
    assert by_name["ExactAutonomyData"]["module"] == "CSTTT/Autonomy/FiniteAutonomy.lean"
    assert by_name["ExactAutonomyCertificate"]["claim_lanes"] == "A"
    assert by_name["TemporalFIACHCertificate"]["claim_lanes"] == "S-T;S-R;S-L;A"
    assert by_name["GeneralizedTemporalContinuity"]["definition_id"] == "D-070"
    assert by_name["DefectVector"]["definition_id"] == "D-071"
    assert by_name["TemporalMargin"]["definition_id"] == "D-072"
    assert by_name["ExactAutonomyPolicy"]["definition_id"] == "D-073"


def test_package_registries_cover_every_obligation() -> None:
    witnesses = read_csv(ROOT / "registries/PACKAGE_WITNESS_REGISTRY.csv")
    controls = read_csv(ROOT / "registries/PACKAGE_CONTROL_REGISTRY.csv")
    obligations = read_csv(ROOT / "registries/PACKAGE_OBLIGATION_REGISTRY.csv")
    staged = read_csv(ROOT / "registries/STAGED_ASSEMBLY_OBLIGATION_REGISTRY.csv")
    assert len(witnesses) == 4
    assert {row["result_status"] for row in witnesses} == {
        "checked-finite-package-certificate",
        "checked-finite-handoff-aligned-package-certificate",
    }
    assert len(controls) == 18
    assert all(row["result_status"] == "checked-obligation-countermodel" for row in controls)
    assert len(obligations) == 10
    assert all(row["negative_controls"] for row in obligations)
    assert all(row["status"] == "landed-positive-and-negative-control" for row in obligations)
    assert len(staged) == 10
    assert next(row for row in staged if row["obligation_id"] == "STG-O07")["negative_controls"] == "SC-01"


def test_claim_lanes_never_inherit() -> None:
    rows = read_csv(ROOT / "registries/CLAIM_LANE_REGISTRY.csv")
    assert len(rows) == 7
    assert {row["lane_id"] for row in rows} == {"S-T", "S-R", "S-L", "A", "R", "O", "M"}
    assert all(row["inherits_from"] == "none" for row in rows)


def test_package_transport_and_strengthening_kill_criteria_are_closed_not_triggered() -> None:
    rows = read_csv(ROOT / "registries/KILL_CRITERIA.csv")
    assert len(rows) == 20
    assert duplicate_values(rows, "kill_id") == set()
    by_id = {row["kill_id"]: row for row in rows}
    phase02 = {"K-PKG-01", "K-PKG-02"}
    phase03 = {"K-TRANS-01", "K-TRANS-02", "K-ROUTE-01", "K-ARROW-01"}
    for kill_id in phase02:
        assert by_id[kill_id]["status"] == "not-triggered-CST-TT-02"
    for kill_id in phase03:
        assert by_id[kill_id]["status"] == "not-triggered-CST-TT-03"
    phase04 = {"K-FIACH-02", "K-FIACH-03", "K-FIACH-04"}
    for kill_id in phase04:
        assert by_id[kill_id]["status"] == "not-triggered-CST-TT-04"
    assert by_id["K-DIRECT-01"]["status"] == "not-triggered-CST-TT-07A"
    for kill_id in {"K-FIACH-05", "K-AUTO-01", "K-AUTO-02"}:
        assert by_id[kill_id]["status"].endswith("CST-TT-05")
    assert by_id["K-ROBUST-01"]["status"] == "not-triggered-CST-TT-07A"
    assert by_id["K-LIVE-01"]["status"] == "not-triggered-CST-TT-07A"
    closed = phase02 | phase03 | phase04 | {"K-DIRECT-01", "K-FIACH-05", "K-AUTO-01", "K-AUTO-02", "K-ROBUST-01", "K-LIVE-01"}
    assert all(row["status"] == "armed" for row in rows if row["kill_id"] not in closed)


def test_temporal_amendment_map_preserves_all_frozen_pth_fth_ids() -> None:
    rows = read_csv(ROOT / "registries/TEMPORAL_AMENDMENT_MAP.csv")
    expected = {f"PTH-{index:02d}" for index in range(1, 13)} | {f"FTH-{index:02d}" for index in range(1, 9)}
    assert len(rows) == 20
    assert duplicate_values(rows, "legacy_id") == set()
    assert {row["legacy_id"] for row in rows} == expected


def test_tt03_transport_registries_are_complete() -> None:
    transport = read_csv(ROOT / "registries/TEMPORAL_TRANSPORT_WITNESS_REGISTRY.csv")
    routes = read_csv(ROOT / "registries/ROUTE_DISCIPLINE_REGISTRY.csv")
    memory = read_csv(ROOT / "registries/MEMORY_REPAIR_REGISTRY.csv")
    arrows = read_csv(ROOT / "registries/RECORD_ARROW_REGISTRY.csv")
    controls = read_csv(ROOT / "registries/TRANSPORT_CONTROL_REGISTRY.csv")
    assert len(transport) == 2
    assert {row["route_status"] for row in transport} == {"flat", "route-indexed"}
    assert len(routes) == 2
    assert {row["role"] for row in routes} == {"flat-positive", "route-indexed-negative"}
    assert len(memory) == 2
    assert len(arrows) == 1
    assert len(controls) == 28
    assert all(row["result_status"] == "checked-obligation-countermodel" for row in controls)


def test_tt04_corridor_and_direct_successor_registries_are_complete() -> None:
    corridors = read_csv(ROOT / "registries/TEMPORAL_CORRIDOR_WITNESS_REGISTRY.csv")
    composition = read_csv(ROOT / "registries/CORRIDOR_COMPOSITION_REGISTRY.csv")
    corridor_controls = read_csv(ROOT / "registries/CORRIDOR_CONTROL_REGISTRY.csv")
    direct = read_csv(ROOT / "registries/DIRECT_SUCCESSOR_REGISTRY.csv")
    paths = read_csv(ROOT / "registries/DIRECT_SUCCESSOR_PATH_REGISTRY.csv")
    direct_controls = read_csv(ROOT / "registries/DIRECT_SUCCESSOR_CONTROL_REGISTRY.csv")
    searches = read_csv(ROOT / "registries/CORRIDOR_SEARCH_REGISTRY.csv")
    comparison = read_csv(ROOT / "registries/OVERLAP_DIRECT_COMPARISON.csv")
    assert len(corridors) == 4
    assert {row["corridor_id"] for row in corridors} == {"COR-POS-01", "COR-POS-02A", "COR-POS-02B", "COR-POS-02-COMPOSED"}
    assert len(composition) == 1 and composition[0]["composition_valid"] == "true"
    assert composition[0]["old_endpoint_mixed_rule"] == "false"
    assert len(corridor_controls) == 25
    assert all(row["control_passed"] == "true" for row in corridor_controls)
    assert len(direct) == 3
    assert len(paths) == 1 and paths[0]["path_valid"] == "true"
    assert paths[0]["atomic_endpoint_edge_present"] == "false"
    assert len(direct_controls) == 16
    assert all(row["control_passed"] == "true" for row in direct_controls)
    assert len(searches) == 5
    assert len(comparison) == 9


def test_tt05_autonomy_and_fiach_registries_are_complete() -> None:
    autonomy = read_csv(ROOT / "registries/AUTONOMY_WITNESS_REGISTRY.csv")
    controls = read_csv(ROOT / "registries/AUTONOMY_CONTROL_REGISTRY.csv")
    searches = read_csv(ROOT / "registries/AUTONOMY_SEARCH_REGISTRY.csv")
    fiach = read_csv(ROOT / "registries/FIACH_WITNESS_REGISTRY.csv")
    lane_controls = read_csv(ROOT / "registries/FIACH_LANE_CONTROL_REGISTRY.csv")
    aligned = read_csv(ROOT / "registries/HANDOFF_ALIGNED_PACKAGE_REGISTRY.csv")
    assert len(aligned) == 2
    assert len(autonomy) == 1 and autonomy[0]["autonomy_id"] == "AUT-POS-01"
    assert autonomy[0]["finite_words_checked"] == "127"
    assert len(controls) == 12
    assert {row["control_id"] for row in controls} == {f"AUT-C{i:02d}" for i in range(1, 13)}
    assert len(searches) == 2
    assert next(row for row in searches if row["search_id"] == "AUTONOMY-INVARIANT-EXHAUSTION")["mismatches"] == "0"
    assert len(fiach) == 1 and fiach[0]["fiach_id"] == "FIACH-POS-01"
    assert all(fiach[0][lane] == "true" for lane in ("S-T", "S-R", "S-L", "A"))
    assert len(lane_controls) == 6
    assert all(row["aggregate"] == "false" for row in lane_controls)


def test_tt07a_strengthening_registries_are_complete() -> None:
    defects = read_csv(ROOT / "registries/DEFECT_PROFILE_REGISTRY.csv")
    robustness = read_csv(ROOT / "registries/ROBUSTNESS_REGISTRY.csv")
    unbounded = read_csv(ROOT / "registries/UNBOUNDED_INVARIANT_REGISTRY.csv")
    dependencies = read_csv(ROOT / "registries/DEPENDENCY_EDGES.csv")
    assert len(defects) == 8
    assert len(robustness) == 7
    assert len(unbounded) == 2
    assert duplicate_values(defects, "profile_id") == set()
    assert duplicate_values(robustness, "item_id") == set()
    assert duplicate_values(unbounded, "item_id") == set()
    assert any(row["profile_id"] == "DEF-EQUAL-SCALAR-01" for row in defects)
    assert any(row["item_id"] == "ROB-POS-01" and row["accepted"] == "True" for row in robustness)
    assert any(row["item_id"] == "UNB-POS-01" for row in unbounded)
    full_edges = [tuple(row.values()) for row in dependencies]
    assert len(full_edges) == len(set(full_edges))
    for source, target in (("TTD-01", "TTS-01"), ("TTH-04", "TTS-01"), ("TTN-10", "TTS-02"), ("TTS-02", "TTS-03"), ("TTH-05", "TTS-04")):
        assert any(row["source"] == source and row["target"] == target for row in dependencies)
