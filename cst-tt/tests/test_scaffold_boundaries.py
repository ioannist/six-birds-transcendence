from __future__ import annotations

from cst_tt.autonomy import AutonomyScaffold, ResponseRowScaffold, WithdrawalSpec
from cst_tt.corridor import (
    CounterfactualAuditScaffold,
    DirectSuccessorScaffold,
    TemporalCorridorScaffold,
)
from cst_tt.package import (
    ClauseBundleScaffold,
    ClauseWitnessScaffold,
    IntegratedPackageScaffold,
)
from cst_tt.targets import TemporalFIACHScaffold
from cst_tt.temporal import (
    ClockTranslationScaffold,
    PredictiveNow,
    TemporalClosureScaffold,
    TemporalSignature,
    TemporalTransportScaffold,
)
from cst_tt.types import (
    CarrierId,
    ClaimLane,
    ClauseId,
    Dependency,
    Episode,
    Event,
    EvidenceStatus,
    RecognitionStatus,
    RouteStatus,
)


def closure(carrier: CarrierId, state_id: str) -> TemporalClosureScaffold:
    return TemporalClosureScaffold(
        carrier=carrier,
        state_id=state_id,
        signature=TemporalSignature(
            predictive_now=PredictiveNow("P?", "R?"),
            order_state="O?",
            tick_phase="T?",
            progress_state="G?",
            arrow_record="A?",
            maintenance_state="M?",
            owner=carrier,
        ),
        successor_relation_id=f"succ-{carrier.code}",
        record_order_id=f"record-{carrier.code}",
    )


def translation() -> ClockTranslationScaffold:
    return ClockTranslationScaffold(
        source_alphabet_id="src-time",
        target_alphabet_id="dst-time",
        component_maps={
            "predictive-now": "map-p",
            "order": "map-o",
            "tick-phase": "map-t",
            "progress": "map-g",
            "arrow-record": "map-a",
            "route-memory": "map-r",
            "maintenance": "map-m",
        },
    )


def strict_episode(source: CarrierId, target: CarrierId) -> Episode:
    return Episode(
        source=source,
        target=target,
        final_stage=2,
        events=(
            Event("source-start", source, 0),
            Event("mixed-target", target, 1),
            Event("target-end", target, 2),
        ),
        dependencies=(
            Dependency("source-start", "mixed-target"),
            Dependency("mixed-target", "target-end"),
        ),
        active_support={0: (source,), 1: (source, target), 2: (target,)},
    )


def package(target: CarrierId) -> IntegratedPackageScaffold:
    temporal = closure(target, "target-state")
    witnesses = {
        clause: ClauseWitnessScaffold(
            clause=clause,
            scope=(f"scope-{clause.value}",),
            assignment_id=f"assignment-{clause.value}",
        )
        for clause in ClauseId
    }
    return IntegratedPackageScaffold(
        target=target,
        global_assignment_id="global-assignment-placeholder",
        clauses=ClauseBundleScaffold(witnesses=witnesses, temporal_substance=temporal),
        join_tree_id="join-tree-placeholder",
    )


def autonomy(target: CarrierId) -> AutonomyScaffold:
    return AutonomyScaffold(
        target=target,
        endpoint_state_id="target-state",
        invariant_state_ids=("target-state",),
        disturbance_ids=("d0",),
        response_rows=(
            ResponseRowScaffold(
                state_id="target-state",
                disturbance_id="d0",
                action_id="a0",
                successor_state_id="target-state",
                action_owner=target,
            ),
        ),
        withdrawal=WithdrawalSpec(
            target=target,
            removed_resources=("source", "bridge", "scheduler"),
            retained_resources=("target-core",),
            source_removed=False,
            bridge_removed=False,
            migration_controller_removed=False,
            external_decoder_removed=False,
            external_scheduler_removed=False,
            undeclared_repair_removed=False,
        ),
    )


def test_strict_corridor_shape_is_independent_of_evidence_status() -> None:
    source = CarrierId(0, "source")
    target = CarrierId(1, "target")
    corridor = TemporalCorridorScaffold(
        episode=strict_episode(source, target),
        temporal_realization_status_by_stage=(EvidenceStatus.NOT_EVALUATED,) * 3,
        transport_status_by_stage=(EvidenceStatus.NOT_EVALUATED,) * 3,
        counterfactual=CounterfactualAuditScaffold(mixed_stage=1, later_stage=2),
        takeover_stage=2,
    )
    assert corridor.shape_errors() == []
    assert all(status is EvidenceStatus.NOT_EVALUATED for status in corridor.lineage_statuses())


def test_strict_corridor_rejects_source_after_takeover() -> None:
    source = CarrierId(0, "source")
    target = CarrierId(1, "target")
    episode = Episode(
        source=source,
        target=target,
        final_stage=2,
        events=(),
        dependencies=(),
        active_support={0: (source,), 1: (source, target), 2: (target,)},
    )
    corridor = TemporalCorridorScaffold(
        episode=episode,
        temporal_realization_status_by_stage=(EvidenceStatus.NOT_EVALUATED,) * 3,
        transport_status_by_stage=(EvidenceStatus.NOT_EVALUATED,) * 3,
        counterfactual=CounterfactualAuditScaffold(mixed_stage=1, later_stage=2),
        takeover_stage=1,
    )
    assert "source remains active" in "; ".join(corridor.shape_errors())


def test_temporal_transport_is_separately_typed_and_has_all_maps() -> None:
    source = CarrierId(0, "source")
    target = CarrierId(1, "target")
    transport = TemporalTransportScaffold(closure(source, "s"), closure(target, "t"), translation())
    assert transport.shape_errors() == []
    bad = TemporalTransportScaffold(closure(source, "s"), closure(source, "t"), translation())
    assert "distinct source and target" in "; ".join(bad.shape_errors())


def test_direct_successor_requires_declared_forward_operational_edge() -> None:
    source = CarrierId(0, "source")
    target = CarrierId(1, "target")
    episode = Episode(
        source=source,
        target=target,
        final_stage=1,
        events=(Event("s-last", source, 0), Event("t-first", target, 1)),
        dependencies=(Dependency("s-last", "t-first"),),
        active_support={0: (source,), 1: (target,)},
    )
    direct = DirectSuccessorScaffold(
        episode=episode,
        last_source_event_id="s-last",
        first_target_event_id="t-first",
        transport=TemporalTransportScaffold(closure(source, "s"), closure(target, "t"), translation()),
    )
    assert direct.shape_errors() == []


def test_package_layer_contains_no_source_lineage_or_autonomy_field() -> None:
    target = CarrierId(1, "target")
    pkg = package(target)
    assert pkg.shape_errors() == []
    assert not hasattr(pkg, "source")
    assert not hasattr(pkg, "corridor")
    assert not hasattr(pkg, "autonomy")


def test_autonomy_shape_requires_complete_target_owned_response_table() -> None:
    target = CarrierId(1, "target")
    cert = autonomy(target)
    assert cert.shape_errors() == []
    assert not cert.withdrawal.intervention_is_complete()
    incomplete = AutonomyScaffold(
        target=target,
        endpoint_state_id="x",
        invariant_state_ids=("x",),
        disturbance_ids=("d",),
        response_rows=(),
        withdrawal=cert.withdrawal,
    )
    assert "misses 1" in "; ".join(incomplete.shape_errors())


def test_aggregate_returns_all_lanes_without_inheritance() -> None:
    source = CarrierId(0, "source")
    target = CarrierId(1, "target")
    corridor = TemporalCorridorScaffold(
        episode=strict_episode(source, target),
        temporal_realization_status_by_stage=(EvidenceStatus.NOT_EVALUATED,) * 3,
        transport_status_by_stage=(EvidenceStatus.NOT_EVALUATED,) * 3,
        counterfactual=CounterfactualAuditScaffold(mixed_stage=1, later_stage=2),
        takeover_stage=2,
    )
    aggregate = TemporalFIACHScaffold(
        source=source,
        target=target,
        source_package_status=EvidenceStatus.NOT_EVALUATED,
        staged_clause_preservation_status=EvidenceStatus.NOT_EVALUATED,
        package=package(target),
        corridor=corridor,
        autonomy=autonomy(target),
        route_status=RouteStatus.UNRESOLVED,
        recognition_status=RecognitionStatus.NOT_ADDRESSED,
    )
    assert aggregate.shape_errors() == []
    assert set(aggregate.lane_status()) == set(ClaimLane)
    assert all(status is EvidenceStatus.NOT_EVALUATED for status in aggregate.lane_status().values())
