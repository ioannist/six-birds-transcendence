from __future__ import annotations

from dataclasses import asdict, dataclass
from itertools import product
import json
from typing import Any, Mapping, Sequence


REQUIRED_HARD_GATES = (
    "distinct-carriers",
    "route-discipline",
    "target-ownership",
    "integrated-package",
    "strict-lineage-mode",
    "post-withdrawal-autonomy",
)


@dataclass(frozen=True)
class MarginAudit:
    dimension_id: str
    base_increment: int
    minimum_increment: int
    radius: int
    well_formed: bool
    worst_case_increment: int
    certified: bool

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class RobustnessAudit:
    model_id: str
    dimensions_unique: bool
    margins_well_formed: bool
    every_margin_certified: bool
    hard_gate_set_exact: bool
    every_hard_gate_frozen_true: bool
    approximation_does_not_override_hard_gates: bool
    bounded_box_size: int
    bounded_perturbations_checked: int
    bounded_violations: int
    minimum_observed_increments: Mapping[str, int]
    robustness_valid: bool
    margin_audits: tuple[MarginAudit, ...]
    failed_obligations: tuple[str, ...]

    def to_dict(self) -> dict[str, Any]:
        value = asdict(self)
        value["minimum_observed_increments"] = dict(self.minimum_observed_increments)
        value["margin_audits"] = [row.to_dict() for row in self.margin_audits]
        value["failed_obligations"] = list(self.failed_obligations)
        return json.loads(json.dumps(value, sort_keys=True))


def _int(value: object) -> int | None:
    return value if isinstance(value, int) and not isinstance(value, bool) else None


def enumerate_bounded_perturbations(model: Mapping[str, Any]) -> dict[str, Any]:
    rows = model.get("dimensions", [])
    rows = [row for row in rows if isinstance(row, Mapping)] if isinstance(rows, list) else []
    ids = [str(row.get("dimension_id", "")) for row in rows]
    ranges: list[range] = []
    for row in rows:
        radius = _int(row.get("radius"))
        ranges.append(range(-radius, radius + 1) if radius is not None and radius >= 0 else range(0))
    minima = {cid: 10**9 for cid in ids}
    violations = 0
    checked = 0
    examples: list[dict[str, Any]] = []
    for deltas in product(*ranges):
        checked += 1
        accepted = True
        observed: dict[str, int] = {}
        for row, cid, delta in zip(rows, ids, deltas):
            base = _int(row.get("base_increment"))
            minimum = _int(row.get("minimum_increment"))
            if base is None or minimum is None:
                accepted = False
                continue
            value = base + delta
            observed[cid] = value
            minima[cid] = min(minima[cid], value)
            accepted &= value >= minimum
        if not accepted:
            violations += 1
            if len(examples) < 8:
                examples.append({"deltas": dict(zip(ids, deltas)), "observed": observed})
    return {
        "search_id": "BOUNDED_TEMPORAL_MARGIN_EXHAUSTION",
        "candidates_examined": checked,
        "violations": violations,
        "minimum_observed_increments": minima,
        "violation_examples": examples,
    }


def audit_robustness(model: Mapping[str, Any]) -> RobustnessAudit:
    rows = model.get("dimensions", [])
    rows = [row for row in rows if isinstance(row, Mapping)] if isinstance(rows, list) else []
    ids = [str(row.get("dimension_id", "")) for row in rows]
    dimensions_unique = bool(ids) and len(ids) == len(set(ids)) and all(ids)
    margins: list[MarginAudit] = []
    for row in rows:
        cid = str(row.get("dimension_id", ""))
        base = _int(row.get("base_increment"))
        minimum = _int(row.get("minimum_increment"))
        radius = _int(row.get("radius"))
        well_formed = base is not None and minimum is not None and radius is not None and minimum > 0 and radius >= 0
        worst = base - radius if well_formed else -10**9
        certified = well_formed and worst >= minimum
        margins.append(
            MarginAudit(
                dimension_id=cid,
                base_increment=base if base is not None else 0,
                minimum_increment=minimum if minimum is not None else 0,
                radius=radius if radius is not None else -1,
                well_formed=well_formed,
                worst_case_increment=worst,
                certified=certified,
            )
        )
    margins_well_formed = bool(margins) and all(row.well_formed for row in margins)
    every_margin_certified = bool(margins) and all(row.certified for row in margins)
    gates = model.get("hard_gates", {})
    gates = gates if isinstance(gates, Mapping) else {}
    hard_gate_set_exact = set(gates) == set(REQUIRED_HARD_GATES)
    every_gate = hard_gate_set_exact and all(value is True for value in gates.values())
    no_override = model.get("acceptance_rule") == "hard-gates-and-componentwise-margins" and model.get("scalar_score_role") == "diagnostic-only"
    search = enumerate_bounded_perturbations(model)
    box = 1
    for row in margins:
        box *= 2 * row.radius + 1 if row.radius >= 0 else 0
    obligations = {
        "dimensions-unique": dimensions_unique,
        "margins-well-formed": margins_well_formed,
        "every-margin-certified": every_margin_certified,
        "hard-gate-set-exact": hard_gate_set_exact,
        "every-hard-gate-frozen-true": every_gate,
        "approximation-does-not-override-hard-gates": no_override,
        "bounded-search-complete": search["candidates_examined"] == box,
        "bounded-search-has-no-violations": search["violations"] == 0,
    }
    failed = tuple(name for name, ok in obligations.items() if not ok)
    return RobustnessAudit(
        model_id=str(model.get("model_id", "")),
        dimensions_unique=dimensions_unique,
        margins_well_formed=margins_well_formed,
        every_margin_certified=every_margin_certified,
        hard_gate_set_exact=hard_gate_set_exact,
        every_hard_gate_frozen_true=every_gate,
        approximation_does_not_override_hard_gates=no_override,
        bounded_box_size=box,
        bounded_perturbations_checked=int(search["candidates_examined"]),
        bounded_violations=int(search["violations"]),
        minimum_observed_increments=dict(search["minimum_observed_increments"]),
        robustness_valid=not failed,
        margin_audits=tuple(margins),
        failed_obligations=failed,
    )


def audit_specific_perturbation(model: Mapping[str, Any], deltas: Mapping[str, int], gates: Mapping[str, bool]) -> dict[str, Any]:
    rows = model.get("dimensions", [])
    rows = [row for row in rows if isinstance(row, Mapping)] if isinstance(rows, list) else []
    dimension_results: dict[str, bool] = {}
    within_box = True
    for row in rows:
        cid = str(row.get("dimension_id", ""))
        base = int(row.get("base_increment", 0))
        minimum = int(row.get("minimum_increment", 0))
        radius = int(row.get("radius", -1))
        delta = int(deltas.get(cid, 0))
        within_box &= abs(delta) <= radius
        dimension_results[cid] = base + delta >= minimum
    gate_set_exact = set(gates) == set(REQUIRED_HARD_GATES)
    gates_pass = gate_set_exact and all(gates.get(name) is True for name in REQUIRED_HARD_GATES)
    accepted = within_box and all(dimension_results.values()) and gates_pass
    return {
        "within_declared_box": within_box,
        "dimension_results": dimension_results,
        "hard_gates_exact_and_true": gates_pass,
        "accepted": accepted,
    }
