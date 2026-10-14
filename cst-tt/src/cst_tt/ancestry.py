from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Iterable


class OperationalEdgeKind(str, Enum):
    SOURCE_TO_RECORD = "source-to-record"
    RECORD_TO_TARGET = "record-to-target"
    LIVE_DEPENDENCY = "live-dependency"
    GUARDED_FISSION = "guarded-fission"
    GUARDED_FUSION = "guarded-fusion"


@dataclass(frozen=True)
class OperationalEdge:
    source_node: str
    target_node: str
    kind: OperationalEdgeKind


@dataclass(frozen=True)
class AncestryInterfaceScaffold:
    nodes: tuple[str, ...]
    seed_edges: tuple[OperationalEdge, ...]
    closure_rule_ids: tuple[str, ...]
    no_ex_nihilo_rule_id: str

    def shape_errors(self) -> list[str]:
        errors: list[str] = []
        node_set = set(self.nodes)
        if len(node_set) != len(self.nodes):
            errors.append("ancestry node identifiers must be unique")
        for edge in self.seed_edges:
            if edge.source_node not in node_set or edge.target_node not in node_set:
                errors.append("every seed edge endpoint must be a declared node")
        if not self.no_ex_nihilo_rule_id.strip():
            errors.append("no-ex-nihilo rule must be named")
        return errors

    def graph_reachable(self, source: str) -> set[str]:
        """Operational reachability only; this is not the frozen ancestry closure."""
        reached = {source}
        changed = True
        while changed:
            changed = False
            for edge in self.seed_edges:
                if edge.source_node in reached and edge.target_node not in reached:
                    reached.add(edge.target_node)
                    changed = True
        return reached


def all_edge_kinds(edges: Iterable[OperationalEdge]) -> set[OperationalEdgeKind]:
    return {edge.kind for edge in edges}
