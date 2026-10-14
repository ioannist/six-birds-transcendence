from __future__ import annotations

from dataclasses import dataclass

from .types import CarrierId, EvidenceStatus


@dataclass(frozen=True)
class WithdrawalSpec:
    target: CarrierId
    removed_resources: tuple[str, ...]
    retained_resources: tuple[str, ...]
    source_removed: bool
    bridge_removed: bool
    migration_controller_removed: bool
    external_decoder_removed: bool
    external_scheduler_removed: bool
    undeclared_repair_removed: bool

    def shape_errors(self) -> list[str]:
        errors: list[str] = []
        overlap = set(self.removed_resources).intersection(self.retained_resources)
        if overlap:
            errors.append("removed and retained resources overlap: " + ", ".join(sorted(overlap)))
        if len(set(self.removed_resources)) != len(self.removed_resources):
            errors.append("removed resource identifiers must be unique")
        if len(set(self.retained_resources)) != len(self.retained_resources):
            errors.append("retained resource identifiers must be unique")
        if any(not resource.strip() for resource in (*self.removed_resources, *self.retained_resources)):
            errors.append("resource identifiers must be nonempty")
        return errors

    def intervention_is_complete(self) -> bool:
        return all(
            (
                self.source_removed,
                self.bridge_removed,
                self.migration_controller_removed,
                self.external_decoder_removed,
                self.external_scheduler_removed,
                self.undeclared_repair_removed,
            )
        )


@dataclass(frozen=True)
class ResponseRowScaffold:
    state_id: str
    disturbance_id: str
    action_id: str
    successor_state_id: str
    action_owner: CarrierId


@dataclass(frozen=True)
class AutonomyScaffold:
    target: CarrierId
    endpoint_state_id: str
    invariant_state_ids: tuple[str, ...]
    disturbance_ids: tuple[str, ...]
    response_rows: tuple[ResponseRowScaffold, ...]
    withdrawal: WithdrawalSpec
    package_inside_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    anti_stall_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    budget_solvency_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED
    maintenance_ownership_status: EvidenceStatus = EvidenceStatus.NOT_EVALUATED

    def shape_errors(self) -> list[str]:
        errors = self.withdrawal.shape_errors()
        if self.withdrawal.target != self.target:
            errors.append("withdrawal target must match autonomy target")
        if not self.invariant_state_ids:
            errors.append("invariant region must be nonempty")
        if len(set(self.invariant_state_ids)) != len(self.invariant_state_ids):
            errors.append("invariant state identifiers must be unique")
        if len(set(self.disturbance_ids)) != len(self.disturbance_ids):
            errors.append("disturbance identifiers must be unique")
        if self.endpoint_state_id not in self.invariant_state_ids:
            errors.append("endpoint state must lie in the declared invariant region")
        covered_pairs: set[tuple[str, str]] = set()
        for row in self.response_rows:
            if row.action_owner != self.target:
                errors.append("every retained response action must be target-owned")
            if row.state_id not in self.invariant_state_ids:
                errors.append("response row starts outside the invariant region")
            if row.successor_state_id not in self.invariant_state_ids:
                errors.append("response row leaves the invariant region")
            if row.disturbance_id not in self.disturbance_ids:
                errors.append("response row uses an undeclared disturbance")
            pair = (row.state_id, row.disturbance_id)
            if pair in covered_pairs:
                errors.append("response table repeats a state/disturbance pair")
            covered_pairs.add(pair)
        required_pairs = {
            (state_id, disturbance_id)
            for state_id in self.invariant_state_ids
            for disturbance_id in self.disturbance_ids
        }
        missing = required_pairs.difference(covered_pairs)
        if missing:
            errors.append(f"response table misses {len(missing)} invariant state/disturbance pairs")
        return errors

    def autonomy_statuses(self) -> tuple[EvidenceStatus, ...]:
        return (
            self.package_inside_status,
            self.anti_stall_status,
            self.budget_solvency_status,
            self.maintenance_ownership_status,
        )
