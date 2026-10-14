from __future__ import annotations

from dataclasses import dataclass
from typing import Iterable, Mapping

from .autonomy import AutonomyScaffold
from .corridor import TemporalCorridorScaffold
from .package import IntegratedPackageScaffold
from .types import CarrierId, ClaimLane, EvidenceStatus, RecognitionStatus, RouteStatus


def aggregate_evidence(statuses: Iterable[EvidenceStatus]) -> EvidenceStatus:
    """Conservative conjunction for a lane; it never borrows evidence from another lane."""

    values = tuple(statuses)
    if any(status is EvidenceStatus.FAILED for status in values):
        return EvidenceStatus.FAILED
    if values and all(status is EvidenceStatus.CERTIFIED for status in values):
        return EvidenceStatus.CERTIFIED
    return EvidenceStatus.NOT_EVALUATED


@dataclass(frozen=True)
class TemporalFIACHScaffold:
    source: CarrierId
    target: CarrierId
    source_package_status: EvidenceStatus
    staged_clause_preservation_status: EvidenceStatus
    package: IntegratedPackageScaffold
    corridor: TemporalCorridorScaffold
    autonomy: AutonomyScaffold
    route_status: RouteStatus
    recognition_status: RecognitionStatus = RecognitionStatus.NOT_ADDRESSED

    def lane_status(self) -> Mapping[ClaimLane, EvidenceStatus]:
        clause_statuses: list[EvidenceStatus] = []
        for witness in self.package.clauses.witnesses.values():
            clause_statuses.extend((witness.acceptance_status, witness.hard_gate_status))
        realization = aggregate_evidence(
            (
                *clause_statuses,
                self.package.overlap_compatibility,
                self.package.global_witness_status,
                self.package.all_hard_gates_status,
                self.package.target_ownership_status,
                *self.package.clauses.temporal_substance.temporal_statuses(),
            )
        )
        transport = aggregate_evidence(
            (
                self.staged_clause_preservation_status,
                *self.corridor.transport_status_by_stage,
            )
        )
        lineage = aggregate_evidence(self.corridor.lineage_statuses())
        autonomy = aggregate_evidence(self.autonomy.autonomy_statuses())
        return {
            ClaimLane.STRUCTURAL_TRANSPORT: transport,
            ClaimLane.STRUCTURAL_REALIZATION: realization,
            ClaimLane.STRUCTURAL_LINEAGE: lineage,
            ClaimLane.AUTONOMY: autonomy,
            ClaimLane.RECOGNITION: EvidenceStatus.NOT_EVALUATED,
            ClaimLane.ONTOLOGY: EvidenceStatus.NOT_EVALUATED,
            ClaimLane.METHODOLOGY: EvidenceStatus.NOT_EVALUATED,
        }

    def shape_errors(self) -> list[str]:
        errors: list[str] = []
        if self.source == self.target:
            errors.append("source and target must be distinct")
        if self.package.target != self.target:
            errors.append("package target mismatch")
        if self.autonomy.target != self.target:
            errors.append("autonomy target mismatch")
        if self.corridor.episode.source != self.source:
            errors.append("corridor source mismatch")
        if self.corridor.episode.target != self.target:
            errors.append("corridor target mismatch")
        if self.route_status != self.corridor.route_status:
            errors.append("aggregate route status must match corridor route status")
        errors.extend(self.package.shape_errors())
        errors.extend(self.corridor.shape_errors())
        errors.extend(self.autonomy.shape_errors())
        return errors
