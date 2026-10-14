from __future__ import annotations

from dataclasses import dataclass
from typing import Mapping

from .temporal import TemporalClosureScaffold
from .types import CarrierId, ClauseId, EvidenceStatus


@dataclass(frozen=True)
class ClauseWitnessScaffold:
    clause: ClauseId
    scope: tuple[str, ...]
    assignment_id: str
    acceptance_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    hard_gate_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    essential_resources: tuple[str, ...] = ()

    def shape_errors(self) -> list[str]:
        errors: list[str] = []
        if not self.scope:
            errors.append(f"{self.clause.value} has an empty declared scope")
        if not self.assignment_id.strip():
            errors.append(f"{self.clause.value} has no assignment identifier")
        return errors


@dataclass(frozen=True)
class ClauseBundleScaffold:
    witnesses: Mapping[ClauseId, ClauseWitnessScaffold]
    temporal_substance: TemporalClosureScaffold

    def shape_errors(self) -> list[str]:
        errors: list[str] = []
        expected = set(ClauseId)
        actual = set(self.witnesses)
        if actual != expected:
            missing = expected.difference(actual)
            extra = actual.difference(expected)
            if missing:
                errors.append("missing clauses: " + ", ".join(sorted(x.value for x in missing)))
            if extra:
                errors.append("unexpected clauses: " + ", ".join(sorted(x.value for x in extra)))
        for key, witness in self.witnesses.items():
            if witness.clause != key:
                errors.append(f"clause key/witness mismatch for {key.value}")
            errors.extend(witness.shape_errors())
        errors.extend(self.temporal_substance.shape_errors())
        return errors


@dataclass(frozen=True)
class IntegratedPackageScaffold:
    target: CarrierId
    global_assignment_id: str
    clauses: ClauseBundleScaffold
    join_tree_id: str
    overlap_compatibility: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    global_witness_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    all_hard_gates_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    target_ownership_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED

    def shape_errors(self) -> list[str]:
        errors = self.clauses.shape_errors()
        if self.clauses.temporal_substance.carrier != self.target:
            errors.append("C6 temporal substance must be target-local")
        if not self.global_assignment_id.strip():
            errors.append("global_assignment_id must be nonempty")
        if not self.join_tree_id.strip():
            errors.append("join_tree_id must be nonempty")
        return errors
