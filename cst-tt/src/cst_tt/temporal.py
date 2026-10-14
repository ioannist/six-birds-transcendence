from __future__ import annotations

from dataclasses import dataclass
from typing import Hashable, Mapping

from .types import CarrierId, EvidenceStatus, RouteStatus

Token = Hashable


@dataclass(frozen=True)
class PredictiveNow:
    """Future-sufficient current class plus explicit route residue."""

    predictive_class: Token
    route_residue: Token
    future_sufficiency_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED


@dataclass(frozen=True)
class TemporalSignature:
    """The temporal object frozen before any corridor or lineage predicate."""

    predictive_now: PredictiveNow
    order_state: Token
    tick_phase: Token
    progress_state: Token
    arrow_record: Token
    maintenance_state: Token
    owner: CarrierId


@dataclass(frozen=True)
class TemporalClosureScaffold:
    carrier: CarrierId
    state_id: str
    signature: TemporalSignature
    successor_relation_id: str
    record_order_id: str
    tick_viability_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    genuine_progress_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    endogenous_arrow_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    maintenance_ownership_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED

    def shape_errors(self) -> list[str]:
        errors: list[str] = []
        if self.signature.owner != self.carrier:
            errors.append("temporal signature owner must match the carrier")
        for label, value in (
            ("state_id", self.state_id),
            ("successor_relation_id", self.successor_relation_id),
            ("record_order_id", self.record_order_id),
        ):
            if not value.strip():
                errors.append(f"{label} must be nonempty")
        return errors

    def temporal_statuses(self) -> tuple[EvidenceStatus, ...]:
        return (
            self.signature.predictive_now.future_sufficiency_status,
            self.tick_viability_status,
            self.genuine_progress_status,
            self.endogenous_arrow_status,
            self.maintenance_ownership_status,
        )


@dataclass(frozen=True)
class ClockTranslationScaffold:
    source_alphabet_id: str
    target_alphabet_id: str
    component_maps: Mapping[str, str]
    successor_compatibility: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    progress_compatibility: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    record_monotonicity: EvidenceStatus = EvidenceStatus.NOT_EVALUATED

    REQUIRED_COMPONENTS = frozenset(
        {
            "predictive-now",
            "order",
            "tick-phase",
            "progress",
            "arrow-record",
            "route-memory",
            "maintenance",
        }
    )

    def shape_errors(self) -> list[str]:
        errors: list[str] = []
        if not self.source_alphabet_id.strip():
            errors.append("source_alphabet_id must be nonempty")
        if not self.target_alphabet_id.strip():
            errors.append("target_alphabet_id must be nonempty")
        missing = self.REQUIRED_COMPONENTS.difference(self.component_maps)
        errors.extend(f"missing temporal component map: {name}" for name in sorted(missing))
        empty = sorted(name for name, map_id in self.component_maps.items() if not str(map_id).strip())
        errors.extend(f"empty temporal component map identifier: {name}" for name in empty)
        return errors

    def compatibility_statuses(self) -> tuple[EvidenceStatus, ...]:
        return (
            self.successor_compatibility,
            self.progress_compatibility,
            self.record_monotonicity,
        )


@dataclass(frozen=True)
class TemporalTransportScaffold:
    source: TemporalClosureScaffold
    target: TemporalClosureScaffold
    clock_translation: ClockTranslationScaffold
    representative_independence: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    predictive_preservation: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    order_preservation: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    tick_preservation: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    progress_preservation: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    record_descent: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    route_residue_status: RouteStatus = RouteStatus.UNRESOLVED
    maintenance_translation: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    ownership_interface: EvidenceStatus = EvidenceStatus.NOT_EVALUATED

    def shape_errors(self) -> list[str]:
        errors: list[str] = []
        if self.source.carrier == self.target.carrier:
            errors.append("temporal transport requires distinct source and target carriers")
        errors.extend(f"source: {error}" for error in self.source.shape_errors())
        errors.extend(f"target: {error}" for error in self.target.shape_errors())
        errors.extend(self.clock_translation.shape_errors())
        return errors

    def transport_statuses(self) -> tuple[EvidenceStatus, ...]:
        return (
            self.representative_independence,
            self.predictive_preservation,
            self.order_preservation,
            self.tick_preservation,
            self.progress_preservation,
            self.record_descent,
            self.maintenance_translation,
            self.ownership_interface,
            *self.clock_translation.compatibility_statuses(),
        )
