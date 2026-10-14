from __future__ import annotations

import pytest

from cst_tt.ancestry import AncestryInterfaceScaffold, OperationalEdge, OperationalEdgeKind
from cst_tt.types import CarrierId, ClauseId, Dependency, Episode, Event


def test_clause_enum_has_exactly_eight_independent_slots() -> None:
    assert len(ClauseId) == 8
    assert {item.value[:2] for item in ClauseId} == {f"C{i}" for i in range(1, 9)}


def test_episode_accepts_strictly_forward_operational_graph() -> None:
    source = CarrierId(0, "source")
    target = CarrierId(1, "target")
    episode = Episode(
        source=source,
        target=target,
        final_stage=2,
        events=(Event("s", source, 0), Event("m", target, 1), Event("t", target, 2)),
        dependencies=(Dependency("s", "m"), Dependency("m", "t")),
        active_support={0: (source,), 1: (source, target), 2: (target,)},
    )
    assert episode.is_mixed(1)
    assert episode.shape_errors() == []


def test_episode_rejects_empty_support() -> None:
    source = CarrierId(0, "source")
    target = CarrierId(1, "target")
    with pytest.raises(ValueError, match="empty operational support"):
        Episode(
            source=source,
            target=target,
            final_stage=1,
            events=(),
            dependencies=(),
            active_support={0: (source,), 1: ()},
        )


def test_episode_rejects_nonforward_dependency() -> None:
    source = CarrierId(0, "source")
    target = CarrierId(1, "target")
    with pytest.raises(ValueError, match="strictly forward"):
        Episode(
            source=source,
            target=target,
            final_stage=1,
            events=(Event("a", source, 1), Event("b", target, 0)),
            dependencies=(Dependency("a", "b"),),
            active_support={0: (source,), 1: (target,)},
        )


def test_ancestry_scaffold_computes_operational_reachability_only() -> None:
    graph = AncestryInterfaceScaffold(
        nodes=("s", "r", "t", "twin"),
        seed_edges=(
            OperationalEdge("s", "r", OperationalEdgeKind.SOURCE_TO_RECORD),
            OperationalEdge("r", "t", OperationalEdgeKind.RECORD_TO_TARGET),
        ),
        closure_rule_ids=("transitive-placeholder",),
        no_ex_nihilo_rule_id="no-ex-nihilo-placeholder",
    )
    assert graph.shape_errors() == []
    assert graph.graph_reachable("s") == {"s", "r", "t"}
    assert "twin" not in graph.graph_reachable("s")
