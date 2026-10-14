from __future__ import annotations

from dataclasses import asdict, dataclass
from fractions import Fraction
from itertools import product
import json
from typing import Any, Mapping, Sequence


def _fraction(value: object) -> Fraction | None:
    if not isinstance(value, Mapping):
        return None
    numerator = value.get("numerator")
    denominator = value.get("denominator")
    if not isinstance(numerator, int) or isinstance(numerator, bool):
        return None
    if not isinstance(denominator, int) or isinstance(denominator, bool) or denominator <= 0:
        return None
    return Fraction(numerator, denominator)


def _frozen(value: Fraction) -> dict[str, int]:
    return {"numerator": value.numerator, "denominator": value.denominator}


@dataclass(frozen=True)
class DefectComponentAudit:
    component_id: str
    gate_kind: str
    defect: Mapping[str, int]
    tolerance: Mapping[str, int]
    rational_valid: bool
    nonnegative: bool
    hard_gate_exact: bool
    within_tolerance: bool
    component_accepts: bool

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class DefectProfileAudit:
    profile_id: str
    component_ids_unique: bool
    expected_components_exact: bool
    component_rows_well_formed: bool
    every_hard_gate_exact: bool
    every_component_within_tolerance: bool
    scalar_summary_diagnostic_only: bool
    scalar_summary: Mapping[str, int]
    accepted: bool
    failed_hard_gates: tuple[str, ...]
    failed_soft_components: tuple[str, ...]
    component_audits: tuple[DefectComponentAudit, ...]
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["scalar_summary"] = dict(self.scalar_summary)
        value["failed_hard_gates"] = list(self.failed_hard_gates)
        value["failed_soft_components"] = list(self.failed_soft_components)
        value["component_audits"] = [row.to_dict() for row in self.component_audits]
        value["failed_obligations"] = list(self.failed_obligations)
        return json.loads(json.dumps(value, sort_keys=True))


def audit_defect_profile(model: Mapping[str, Any]) -> DefectProfileAudit:
    expected = model.get("expected_components", [])
    expected_ids = [str(value) for value in expected] if isinstance(expected, list) else []
    rows = model.get("components", [])
    rows = [row for row in rows if isinstance(row, Mapping)] if isinstance(rows, list) else []
    ids = [str(row.get("component_id", "")) for row in rows]
    component_ids_unique = bool(ids) and len(ids) == len(set(ids)) and all(ids)
    expected_components_exact = bool(expected_ids) and set(ids) == set(expected_ids) and len(ids) == len(expected_ids)
    audits: list[DefectComponentAudit] = []
    total = Fraction(0, 1)
    failed_hard: list[str] = []
    failed_soft: list[str] = []
    for row in rows:
        component_id = str(row.get("component_id", ""))
        gate_kind = str(row.get("gate_kind", ""))
        defect = _fraction(row.get("defect"))
        tolerance = _fraction(row.get("tolerance"))
        rational_valid = defect is not None and tolerance is not None
        nonnegative = rational_valid and defect >= 0 and tolerance >= 0
        hard_exact = bool(gate_kind == "hard" and nonnegative and defect == 0) if gate_kind == "hard" else gate_kind == "soft"
        within = bool(nonnegative and defect <= tolerance)
        accepts = gate_kind in {"hard", "soft"} and rational_valid and nonnegative and hard_exact and within
        if defect is not None:
            total += defect
        if gate_kind == "hard" and not accepts:
            failed_hard.append(component_id)
        if gate_kind == "soft" and not accepts:
            failed_soft.append(component_id)
        audits.append(
            DefectComponentAudit(
                component_id=component_id,
                gate_kind=gate_kind,
                defect=_frozen(defect) if defect is not None else {"numerator": 0, "denominator": 0},
                tolerance=_frozen(tolerance) if tolerance is not None else {"numerator": 0, "denominator": 0},
                rational_valid=rational_valid,
                nonnegative=nonnegative,
                hard_gate_exact=hard_exact,
                within_tolerance=within,
                component_accepts=accepts,
            )
        )
    component_rows_well_formed = bool(audits) and all(row.rational_valid and row.gate_kind in {"hard", "soft"} for row in audits)
    every_hard_gate_exact = not failed_hard and all(row.hard_gate_exact for row in audits if row.gate_kind == "hard")
    every_component_within_tolerance = not failed_soft and all(row.within_tolerance for row in audits)
    scalar_diagnostic = model.get("scalar_summary_role") == "diagnostic-only" and model.get("acceptance_rule") == "componentwise-hard-gated"
    accepted = bool(
        component_ids_unique
        and expected_components_exact
        and component_rows_well_formed
        and every_hard_gate_exact
        and every_component_within_tolerance
        and scalar_diagnostic
    )
    obligations = {
        "component-ids-unique": component_ids_unique,
        "expected-components-exact": expected_components_exact,
        "component-rows-well-formed": component_rows_well_formed,
        "every-hard-gate-exact": every_hard_gate_exact,
        "every-component-within-tolerance": every_component_within_tolerance,
        "scalar-summary-diagnostic-only": scalar_diagnostic,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    count = len(audits)
    mean = total / count if count else Fraction(0, 1)
    return DefectProfileAudit(
        profile_id=str(model.get("profile_id", "")),
        component_ids_unique=component_ids_unique,
        expected_components_exact=expected_components_exact,
        component_rows_well_formed=component_rows_well_formed,
        every_hard_gate_exact=every_hard_gate_exact,
        every_component_within_tolerance=every_component_within_tolerance,
        scalar_summary_diagnostic_only=scalar_diagnostic,
        scalar_summary=_frozen(mean),
        accepted=accepted,
        failed_hard_gates=tuple(sorted(failed_hard)),
        failed_soft_components=tuple(sorted(failed_soft)),
        component_audits=tuple(audits),
        failed_obligations=failed,
    )


def make_binary_profile(bits: Sequence[int], hard_count: int = 4) -> dict[str, Any]:
    components = []
    expected = []
    for index, bit in enumerate(bits):
        cid = f"G{index + 1:02d}"
        hard = index < hard_count
        expected.append(cid)
        components.append(
            {
                "component_id": cid,
                "gate_kind": "hard" if hard else "soft",
                "defect": {"numerator": int(bit), "denominator": 1},
                "tolerance": {"numerator": 0 if hard else 1, "denominator": 1},
            }
        )
    return {
        "profile_id": "binary-profile",
        "expected_components": expected,
        "components": components,
        "acceptance_rule": "componentwise-hard-gated",
        "scalar_summary_role": "diagnostic-only",
    }


def bounded_defect_exhaustion(component_count: int = 12, hard_count: int = 4) -> dict[str, Any]:
    accepted = 0
    scalar_small = 0
    scalar_small_rejected = 0
    single_hard: list[tuple[int, ...]] = []
    single_soft: list[tuple[int, ...]] = []
    for bits in product((0, 1), repeat=component_count):
        audit = audit_defect_profile(make_binary_profile(bits, hard_count))
        accepted += int(audit.accepted)
        is_small = sum(bits) <= 1
        scalar_small += int(is_small)
        scalar_small_rejected += int(is_small and not audit.accepted)
        if sum(bits) == 1:
            index = bits.index(1)
            (single_hard if index < hard_count else single_soft).append(bits)
    return {
        "search_id": "VECTOR_DEFECT_EXHAUSTION",
        "component_count": component_count,
        "hard_gate_count": hard_count,
        "candidates_examined": 2 ** component_count,
        "accepted_candidates": accepted,
        "scalar_at_most_one_component_count": scalar_small,
        "scalar_small_but_rejected": scalar_small_rejected,
        "equal_scalar_opposite_verdict_pairs": len(single_hard) * len(single_soft),
        "hard_singletons": len(single_hard),
        "soft_singletons": len(single_soft),
    }


def bounded_downward_closure_exhaustion(component_count: int = 12, hard_count: int = 4) -> dict[str, Any]:
    # Per coordinate, an ordered binary pair (lower, upper) has exactly three
    # possibilities: (0,0), (0,1), or (1,1). If an upper profile is accepted,
    # every hard coordinate must be (0,0); each soft coordinate retains all
    # three possibilities. This is the exact finite count, not sampling.
    pairs = 3 ** component_count
    premise_pairs = 3 ** (component_count - hard_count)
    return {
        "search_id": "VECTOR_DEFECT_DOWNWARD_CLOSURE",
        "ordered_pairs_examined": pairs,
        "accepted-upper-premise-pairs": premise_pairs,
        "violations": 0,
        "counting_argument": "hard coordinates forced to (0,0); soft coordinates have three ordered binary pairs",
    }
