from __future__ import annotations

from dataclasses import asdict, dataclass
from hashlib import sha256
from itertools import product
import json
from pathlib import Path
from typing import Any, Mapping, Sequence

from .corridor import audit_direct_successor, audit_strict_corridor


def _load(root: Path, rel: str) -> dict[str, Any]:
    value = json.loads((root / rel).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(rel)
    return value


def _hash(root: Path, rel: str) -> str:
    return sha256((root / rel).read_bytes()).hexdigest()


def _carrier_code(value: object) -> int | None:
    if isinstance(value, Mapping):
        value = value.get("code")
    return int(value) if isinstance(value, int) and not isinstance(value, bool) else None


def _stages(model: Mapping[str, Any]) -> list[Mapping[str, Any]]:
    episode = model.get("episode", {})
    rows = episode.get("stages", []) if isinstance(episode, Mapping) else []
    return [row for row in rows if isinstance(row, Mapping)] if isinstance(rows, list) else []


def _signature(row: Mapping[str, Any]) -> Mapping[str, Any]:
    value = row.get("signature", {})
    return value if isinstance(value, Mapping) else {}


def _endpoints(kind: str, model: Mapping[str, Any]) -> tuple[int | None, int | None]:
    if kind == "overlap":
        chain = model.get("carrier_chain", [])
        if isinstance(chain, list) and chain:
            return _carrier_code(chain[0]), _carrier_code(chain[-1])
        return None, None
    return _carrier_code(model.get("source_carrier")), _carrier_code(model.get("target_carrier"))


def _frontiers(model: Mapping[str, Any]) -> tuple[Mapping[str, Any], Mapping[str, Any]]:
    rows = _stages(model)
    if not rows:
        return {}, {}
    return _signature(rows[0]), _signature(rows[-1])


def _realized(model: Mapping[str, Any]) -> bool:
    rows = _stages(model)
    return bool(rows) and all(row.get("temporal_realized") is True for row in rows)


@dataclass(frozen=True)
class ContinuityLegAudit:
    leg_id: str
    kind: str
    model_ref: str
    hash_valid: bool
    evidence_valid: bool
    source_code: int | None
    target_code: int | None
    entry_signature: Mapping[str, Any]
    exit_signature: Mapping[str, Any]
    temporally_realized: bool
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["entry_signature"] = dict(self.entry_signature)
        value["exit_signature"] = dict(self.exit_signature)
        value["failed_obligations"] = list(self.failed_obligations)
        return json.loads(json.dumps(value, sort_keys=True))


@dataclass(frozen=True)
class GeneralizedContinuityPathAudit:
    path_id: str
    nonempty: bool
    leg_hashes_valid: bool
    every_leg_valid: bool
    exact_carrier_frontiers: bool
    exact_signature_frontiers: bool
    exact_ownership_frontiers: bool
    no_temporal_gap: bool
    endpoint_distinct: bool
    mode_sequence: tuple[str, ...]
    strict_overlap_only: bool
    contains_direct_successor: bool
    primary_fiach_eligible: bool
    generalized_path_valid: bool
    source_code: int | None
    target_code: int | None
    leg_audits: tuple[ContinuityLegAudit, ...]
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["mode_sequence"] = list(self.mode_sequence)
        value["leg_audits"] = [row.to_dict() for row in self.leg_audits]
        value["failed_obligations"] = list(self.failed_obligations)
        return json.loads(json.dumps(value, sort_keys=True))


def audit_generalized_continuity_path(spec: Mapping[str, Any], root: Path) -> GeneralizedContinuityPathAudit:
    raw_legs = spec.get("legs", [])
    legs = [row for row in raw_legs if isinstance(row, Mapping)] if isinstance(raw_legs, list) else []
    audits: list[ContinuityLegAudit] = []
    for index, row in enumerate(legs):
        kind = str(row.get("kind", ""))
        rel = str(row.get("model_ref", ""))
        expected_hash = row.get("model_sha256")
        model = _load(root, rel) if rel and (root / rel).is_file() else {}
        if kind == "overlap":
            audit = audit_strict_corridor(model)
            valid = audit.strict_corridor_valid
            failures = audit.failed_obligations
        elif kind == "direct":
            audit = audit_direct_successor(model)
            valid = audit.direct_successor_valid
            failures = audit.failed_obligations
        else:
            valid = False
            failures = ("recognized-kind",)
        source, target = _endpoints(kind, model)
        entry, exit = _frontiers(model)
        audits.append(
            ContinuityLegAudit(
                leg_id=str(row.get("leg_id", f"leg-{index}")),
                kind=kind,
                model_ref=rel,
                hash_valid=bool(rel and (root / rel).is_file() and expected_hash == _hash(root, rel)),
                evidence_valid=valid,
                source_code=source,
                target_code=target,
                entry_signature=entry,
                exit_signature=exit,
                temporally_realized=_realized(model),
                failed_obligations=tuple(failures),
            )
        )

    nonempty = bool(audits)
    leg_hashes_valid = nonempty and all(row.hash_valid for row in audits)
    every_leg_valid = nonempty and all(row.evidence_valid for row in audits)
    exact_carrier_frontiers = all(left.target_code == right.source_code for left, right in zip(audits, audits[1:]))
    exact_signature_frontiers = all(dict(left.exit_signature) == dict(right.entry_signature) for left, right in zip(audits, audits[1:]))
    exact_ownership_frontiers = all(
        left.target_code is not None
        and left.exit_signature.get("maintenance_owner") == left.target_code
        and right.entry_signature.get("maintenance_owner") == right.source_code
        and left.target_code == right.source_code
        for left, right in zip(audits, audits[1:])
    )
    no_temporal_gap = nonempty and all(row.temporally_realized for row in audits)
    source = audits[0].source_code if audits else None
    target = audits[-1].target_code if audits else None
    endpoint_distinct = source is not None and target is not None and source != target
    mode_sequence = tuple(row.kind for row in audits)
    strict_overlap_only = nonempty and all(kind == "overlap" for kind in mode_sequence)
    contains_direct = any(kind == "direct" for kind in mode_sequence)
    # The broader path is an S-L class. Only an all-overlap path can discharge the
    # strict lineage lane of the already frozen Temporal-FIACH target.
    primary_fiach_eligible = strict_overlap_only
    obligations = {
        "nonempty": nonempty,
        "leg-hashes-valid": leg_hashes_valid,
        "every-leg-valid": every_leg_valid,
        "exact-carrier-frontiers": exact_carrier_frontiers,
        "exact-signature-frontiers": exact_signature_frontiers,
        "exact-ownership-frontiers": exact_ownership_frontiers,
        "no-temporal-gap": no_temporal_gap,
        "endpoint-distinct": endpoint_distinct,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return GeneralizedContinuityPathAudit(
        path_id=str(spec.get("path_id", "")),
        nonempty=nonempty,
        leg_hashes_valid=leg_hashes_valid,
        every_leg_valid=every_leg_valid,
        exact_carrier_frontiers=exact_carrier_frontiers,
        exact_signature_frontiers=exact_signature_frontiers,
        exact_ownership_frontiers=exact_ownership_frontiers,
        no_temporal_gap=no_temporal_gap,
        endpoint_distinct=endpoint_distinct,
        mode_sequence=mode_sequence,
        strict_overlap_only=strict_overlap_only,
        contains_direct_successor=contains_direct,
        primary_fiach_eligible=primary_fiach_eligible,
        generalized_path_valid=not failed,
        source_code=source,
        target_code=target,
        leg_audits=tuple(audits),
        failed_obligations=failed,
    )


@dataclass(frozen=True)
class OverlapDirectRelationAudit:
    certificate_id: str
    strict_witness_valid: bool
    strict_witness_not_direct: bool
    direct_witness_valid: bool
    direct_witness_not_strict: bool
    overlap_direct_incomparable: bool
    overlap_embeds_generalized: bool
    direct_embeds_generalized: bool
    generalized_strictly_broader_than_overlap: bool
    mixed_mode_path_valid: bool
    detached_copy_excluded: bool
    temporal_gap_excluded: bool
    same_carrier_excluded: bool
    primary_definition_unchanged: bool
    fallback_remains_locked: bool
    claim_lane_only_structural_lineage: bool
    relation_result_valid: bool
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["failed_obligations"] = list(self.failed_obligations)
        return value


def audit_overlap_direct_relation(spec: Mapping[str, Any], root: Path) -> OverlapDirectRelationAudit:
    refs = spec.get("model_refs", {})
    hashes = spec.get("model_sha256", {})
    refs = refs if isinstance(refs, Mapping) else {}
    hashes = hashes if isinstance(hashes, Mapping) else {}

    def read(name: str) -> dict[str, Any]:
        rel = refs.get(name)
        if not isinstance(rel, str) or not (root / rel).is_file() or hashes.get(name) != _hash(root, rel):
            return {}
        return _load(root, rel)

    strict = read("strict_witness")
    direct = read("direct_witness")
    detached = read("detached_control")
    gap = read("gap_control")
    same = read("same_carrier_control")
    strict_audit = audit_strict_corridor(strict)
    strict_as_direct = audit_direct_successor(strict)
    direct_audit = audit_direct_successor(direct)
    direct_as_strict = audit_strict_corridor(direct)

    strict_path_spec = spec.get("strict_singleton_path", {})
    direct_path_spec = spec.get("direct_singleton_path", {})
    mixed_path_spec = spec.get("mixed_mode_path", {})
    strict_path = audit_generalized_continuity_path(strict_path_spec, root) if isinstance(strict_path_spec, Mapping) else None
    direct_path = audit_generalized_continuity_path(direct_path_spec, root) if isinstance(direct_path_spec, Mapping) else None
    mixed_path = audit_generalized_continuity_path(mixed_path_spec, root) if isinstance(mixed_path_spec, Mapping) else None

    strict_witness_valid = strict_audit.strict_corridor_valid
    strict_witness_not_direct = not strict_as_direct.direct_successor_valid
    direct_witness_valid = direct_audit.direct_successor_valid
    direct_witness_not_strict = not direct_as_strict.strict_corridor_valid
    incomparable = strict_witness_valid and strict_witness_not_direct and direct_witness_valid and direct_witness_not_strict
    overlap_embeds = bool(strict_path and strict_path.generalized_path_valid and strict_path.strict_overlap_only)
    direct_embeds = bool(direct_path and direct_path.generalized_path_valid and direct_path.contains_direct_successor)
    broader = overlap_embeds and direct_embeds and direct_witness_not_strict

    # These three controls were frozen earlier as exact countermodels. Their
    # comparison verdicts are hash-bound here rather than reinterpreted as one
    # of the positive episode schemas.
    controls = spec.get("control_verdicts", {})
    controls = controls if isinstance(controls, Mapping) else {}
    detached_excluded = bool(detached) and controls.get("detached_copy") == "neither"
    gap_excluded = bool(gap) and controls.get("temporal_gap") == "neither"
    same_excluded = bool(same) and controls.get("same_carrier") == "neither"
    primary_unchanged = spec.get("primary_definition_change") == "none"
    fallback_locked = spec.get("fallback_status") == "locked"
    lineage_only = spec.get("claim_lanes") == ["S-L"]
    mixed_valid = bool(mixed_path and mixed_path.generalized_path_valid and mixed_path.mode_sequence == ("overlap", "direct"))

    obligations = {
        "strict-witness-valid": strict_witness_valid,
        "strict-witness-not-direct": strict_witness_not_direct,
        "direct-witness-valid": direct_witness_valid,
        "direct-witness-not-strict": direct_witness_not_strict,
        "overlap-direct-incomparable": incomparable,
        "overlap-embeds-generalized": overlap_embeds,
        "direct-embeds-generalized": direct_embeds,
        "generalized-strictly-broader-than-overlap": broader,
        "mixed-mode-path-valid": mixed_valid,
        "detached-copy-excluded": detached_excluded,
        "temporal-gap-excluded": gap_excluded,
        "same-carrier-excluded": same_excluded,
        "primary-definition-unchanged": primary_unchanged,
        "fallback-remains-locked": fallback_locked,
        "claim-lane-only-structural-lineage": lineage_only,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return OverlapDirectRelationAudit(
        certificate_id=str(spec.get("certificate_id", "")),
        strict_witness_valid=strict_witness_valid,
        strict_witness_not_direct=strict_witness_not_direct,
        direct_witness_valid=direct_witness_valid,
        direct_witness_not_strict=direct_witness_not_strict,
        overlap_direct_incomparable=incomparable,
        overlap_embeds_generalized=overlap_embeds,
        direct_embeds_generalized=direct_embeds,
        generalized_strictly_broader_than_overlap=broader,
        mixed_mode_path_valid=mixed_valid,
        detached_copy_excluded=detached_excluded,
        temporal_gap_excluded=gap_excluded,
        same_carrier_excluded=same_excluded,
        primary_definition_unchanged=primary_unchanged,
        fallback_remains_locked=fallback_locked,
        claim_lane_only_structural_lineage=lineage_only,
        relation_result_valid=not failed,
        failed_obligations=failed,
    )


def bounded_relation_truth_table() -> dict[str, Any]:
    rows: list[dict[str, Any]] = []
    for overlap, direct in product((False, True), repeat=2):
        broad = overlap or direct
        rows.append({"overlap": overlap, "direct": direct, "generalized": broad})
    return {
        "search_id": "OVERLAP_DIRECT_RELATION_TRUTH_TABLE",
        "candidates_examined": len(rows),
        "rows": rows,
        "overlap_embedding_violations": sum(1 for row in rows if row["overlap"] and not row["generalized"]),
        "direct_embedding_violations": sum(1 for row in rows if row["direct"] and not row["generalized"]),
        "strict_broadening_witnesses": sum(1 for row in rows if row["generalized"] and not row["overlap"]),
    }
