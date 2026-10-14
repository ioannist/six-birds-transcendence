from __future__ import annotations

from dataclasses import dataclass
from enum import Enum
from typing import Mapping


class ClauseId(str, Enum):
    C1_OBJECTHOOD = "C1_OBJECTHOOD"
    C2_STRICT_PROMOTION = "C2_STRICT_PROMOTION"
    C3_REFLEXIVE_SELF_COORDINATE = "C3_REFLEXIVE_SELF_COORDINATE"
    C4_INTERFACE_NONEXPOSURE = "C4_INTERFACE_NONEXPOSURE"
    C5_ACTION_CREDIT = "C5_ACTION_CREDIT"
    C6_TEMPORAL_CLOSURE = "C6_TEMPORAL_CLOSURE"
    C7_BINDING_RECOMBINATION = "C7_BINDING_RECOMBINATION"
    C8_VIABILITY_REPAIR = "C8_VIABILITY_REPAIR"


class ClaimLane(str, Enum):
    STRUCTURAL_TRANSPORT = "S-T"
    STRUCTURAL_REALIZATION = "S-R"
    STRUCTURAL_LINEAGE = "S-L"
    AUTONOMY = "A"
    RECOGNITION = "R"
    ONTOLOGY = "O"
    METHODOLOGY = "M"


class RouteStatus(str, Enum):
    FLAT = "flat"
    ROUTE_INDEXED = "route-indexed"
    UNRESOLVED = "unresolved"


class RecognitionStatus(str, Enum):
    NOT_ADDRESSED = "not-addressed"
    ASSUMED_INTERFACE = "assumed-interface"
    EXTERNALLY_AUDITED = "externally-audited"


class EvidenceStatus(str, Enum):
    NOT_EVALUATED = "not-evaluated"
    CERTIFIED = "certified"
    FAILED = "failed"


@dataclass(frozen=True, order=True)
class CarrierId:
    code: int
    label: str

    def __post_init__(self) -> None:
        if self.code < 0:
            raise ValueError("carrier code must be nonnegative")
        if not self.label.strip():
            raise ValueError("carrier label must be nonempty")


@dataclass(frozen=True)
class Event:
    event_id: str
    owner: CarrierId
    stage: int

    def __post_init__(self) -> None:
        if not self.event_id.strip():
            raise ValueError("event_id must be nonempty")
        if self.stage < 0:
            raise ValueError("event stage must be nonnegative")


@dataclass(frozen=True)
class Dependency:
    parent_event_id: str
    child_event_id: str

    def __post_init__(self) -> None:
        if self.parent_event_id == self.child_event_id:
            raise ValueError("a dependency cannot be reflexive")


@dataclass(frozen=True)
class Episode:
    source: CarrierId
    target: CarrierId
    final_stage: int
    events: tuple[Event, ...]
    dependencies: tuple[Dependency, ...]
    active_support: Mapping[int, tuple[CarrierId, ...]]

    def __post_init__(self) -> None:
        errors = self.shape_errors()
        if errors:
            raise ValueError("; ".join(errors))

    def shape_errors(self) -> list[str]:
        errors: list[str] = []
        if self.source == self.target:
            errors.append("source and target carriers must be distinct")
        if self.final_stage < 0:
            errors.append("final_stage must be nonnegative")
        expected_stages = set(range(self.final_stage + 1))
        if set(self.active_support) != expected_stages:
            errors.append("active_support must name every stage exactly once")
        for stage, support in self.active_support.items():
            if not support:
                errors.append(f"stage {stage} has an empty operational support")
            if len(set(support)) != len(support):
                errors.append(f"stage {stage} repeats a carrier token")
        by_id = {event.event_id: event for event in self.events}
        if len(by_id) != len(self.events):
            errors.append("event identifiers must be unique")
        for event in self.events:
            if event.stage > self.final_stage:
                errors.append(f"event {event.event_id} lies after final_stage")
        for edge in self.dependencies:
            parent = by_id.get(edge.parent_event_id)
            child = by_id.get(edge.child_event_id)
            if parent is None or child is None:
                errors.append("each dependency endpoint must name a declared event")
            elif parent.stage >= child.stage:
                errors.append("operational dependencies must point strictly forward")
        return errors

    def is_mixed(self, stage: int) -> bool:
        support = self.active_support[stage]
        return self.source in support and self.target in support

# Executable finite surrogate types used only for phase-zero predicate unit tests.
# They are intentionally simple and do not replace the richer certificate dataclasses.

@dataclass(frozen=True)
class Carrier:
    carrier_id: int
    name: str


@dataclass(frozen=True)
class TickState:
    phase: int
    progress: int
    viable: bool


@dataclass(frozen=True)
class RecordState:
    value: int
    endogenous: bool


@dataclass(frozen=True)
class TemporalOwnership:
    order_owner: int
    tick_owner: int
    record_owner: int
    predictive_owner: int
    maintenance_owner: int
    externally_scheduled: bool


@dataclass(frozen=True)
class PredictiveNow:
    current_class: int
    continuation_signature: tuple[int, ...]
    route_memory: tuple[int, ...]


@dataclass(frozen=True)
class TemporalSignature:
    predictive: PredictiveNow
    order_class: int
    tick: TickState
    record: RecordState
    route_memory: tuple[int, ...]
    ownership: TemporalOwnership


@dataclass(frozen=True)
class ClauseProfile:
    c1_objecthood: bool
    c2_strict_promotion: bool
    c3_reflexive_self_coordinate: bool
    c4_interface_nonexposure: bool
    c5_action_credit: bool
    c6_temporal_closure: bool
    c7_binding_recombination: bool
    c8_viability_repair: bool

    def all_pass(self) -> bool:
        return all(
            (
                self.c1_objecthood,
                self.c2_strict_promotion,
                self.c3_reflexive_self_coordinate,
                self.c4_interface_nonexposure,
                self.c5_action_credit,
                self.c6_temporal_closure,
                self.c7_binding_recombination,
                self.c8_viability_repair,
            )
        )


@dataclass(frozen=True)
class HardGateProfile:
    package_gate: bool
    temporal_progress_gate: bool
    arrow_gate: bool
    ownership_gate: bool
    viability_gate: bool

    def all_pass(self) -> bool:
        return all(
            (
                self.package_gate,
                self.temporal_progress_gate,
                self.arrow_gate,
                self.ownership_gate,
                self.viability_gate,
            )
        )


@dataclass(frozen=True)
class PackageCertificate:
    schema_version: int
    carrier: Carrier
    state_id: int
    clauses: ClauseProfile
    temporal: TemporalSignature
    global_gluing: bool
    hard_gates: HardGateProfile
    owner_carrier_id: int
