from __future__ import annotations

from .types import PackageCertificate, TemporalSignature


def temporal_closure(carrier_id: int, signature: TemporalSignature) -> bool:
    """Evaluate only the frozen finite surrogate for order/tick/arrow ownership.

    This predicate is a phase-zero semantics smoke test, not a theorem that the
    structure is consciousness-relevant.
    """
    owners = signature.ownership
    return all(
        (
            signature.tick.viable,
            signature.tick.progress > 0,
            signature.record.endogenous,
            owners.order_owner == carrier_id,
            owners.tick_owner == carrier_id,
            owners.record_owner == carrier_id,
            owners.predictive_owner == carrier_id,
            owners.maintenance_owner == carrier_id,
            not owners.externally_scheduled,
        )
    )


def integrated_package_valid(cert: PackageCertificate) -> bool:
    """Evaluate the phase-zero package surrogate independently of lineage/autonomy."""
    return all(
        (
            cert.schema_version == 1,
            cert.carrier.carrier_id == cert.owner_carrier_id,
            cert.clauses.all_pass(),
            cert.global_gluing,
            cert.hard_gates.all_pass(),
            temporal_closure(cert.carrier.carrier_id, cert.temporal),
        )
    )
