"""Exact finite CST-TT package, transport, lineage, and autonomy tooling.

CST-TT-05 lands one exact finite structural Temporal-FIACH witness by
combining independently audited target realization, strict temporal lineage,
and post-withdrawal target autonomy. It makes no phenomenal, personal-status,
or ontological claim.
"""

from .corridor import (
    CorridorCompositionAudit,
    DirectSuccessorAudit,
    DirectSuccessorPathAudit,
    StrictCorridorAudit,
    audit_corridor_composition,
    audit_direct_successor,
    audit_direct_successor_path,
    audit_strict_corridor,
    bounded_corridor_composition_search,
    bounded_corridor_support_search,
    bounded_direct_path_composition_search,
    bounded_direct_successor_search,
    bounded_nonredundancy_truth_table_search,
    compose_corridor_models,
)
from .fiach import FIACHAudit, audit_temporal_fiach, lane_truth_table, replay_component_certificates
from .package_gluing import (
    PackageAudit,
    StagedAssemblyAudit,
    audit_package,
    audit_staged_assembly,
    bounded_gluing_exhaustion,
)
from .transport import (
    MemoryRepairAudit,
    RecordArrowAudit,
    RouteDisciplineAudit,
    TemporalTransportAudit,
    audit_memory_repair,
    audit_record_arrow,
    audit_route_discipline,
    audit_temporal_transport,
    bounded_confluence_shape_search,
    bounded_global_now_obstruction_search,
    bounded_memory_or_flatness_exhaustion,
    bounded_transport_shape_search,
)
from .types import CarrierId, ClaimLane, ClauseId, Episode, Event, RecognitionStatus, RouteStatus
from .withdrawal_autonomy_checker import (
    AutonomyAudit,
    CollapseStep,
    ResponseChoice,
    audit_autonomy,
    bounded_invariant_algorithm_exhaustion,
    finite_horizon_word_count,
)

__all__ = [
    "AutonomyAudit",
    "CarrierId",
    "ClaimLane",
    "ClauseId",
    "CollapseStep",
    "CorridorCompositionAudit",
    "DirectSuccessorAudit",
    "DirectSuccessorPathAudit",
    "Episode",
    "Event",
    "FIACHAudit",
    "MemoryRepairAudit",
    "PackageAudit",
    "RecognitionStatus",
    "RecordArrowAudit",
    "ResponseChoice",
    "RouteDisciplineAudit",
    "RouteStatus",
    "StagedAssemblyAudit",
    "StrictCorridorAudit",
    "TemporalTransportAudit",
    "audit_autonomy",
    "audit_corridor_composition",
    "audit_direct_successor",
    "audit_direct_successor_path",
    "audit_memory_repair",
    "audit_package",
    "audit_record_arrow",
    "audit_route_discipline",
    "audit_staged_assembly",
    "audit_strict_corridor",
    "audit_temporal_fiach",
    "audit_temporal_transport",
    "bounded_confluence_shape_search",
    "bounded_corridor_composition_search",
    "bounded_corridor_support_search",
    "bounded_direct_path_composition_search",
    "bounded_direct_successor_search",
    "bounded_global_now_obstruction_search",
    "bounded_gluing_exhaustion",
    "bounded_invariant_algorithm_exhaustion",
    "bounded_memory_or_flatness_exhaustion",
    "bounded_nonredundancy_truth_table_search",
    "bounded_transport_shape_search",
    "compose_corridor_models",
    "finite_horizon_word_count",
    "lane_truth_table",
    "replay_component_certificates",
]

__version__ = "0.3.0"
