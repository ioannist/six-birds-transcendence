from __future__ import annotations

from copy import deepcopy
from typing import Any, Callable


def _signature(
    state_id: str,
    predictive: str,
    order: str,
    tick: str,
    progress: str,
    record: str,
    route: str,
    maintenance: str,
    owner: int,
) -> dict[str, Any]:
    return {
        "state_id": state_id,
        "predictive_class": predictive,
        "order_state": order,
        "tick_phase": tick,
        "progress_state": progress,
        "arrow_record": record,
        "route_residue": route,
        "maintenance_state": maintenance,
        "owner": owner,
    }


def positive_route_model() -> dict[str, Any]:
    return {
        "schema_version": "CST-TT-03",
        "model_id": "ROUTE-POS-01",
        "title": "acyclic confluent completion of a replacement-order critical pair",
        "claim_lanes": ["S-T"],
        "claim_ceiling": "finite route independence under declared confluence only",
        "states": [
            {"state_id": "x", "current": "C-start", "predictive": "P-start", "route_residue": "R0", "local_now": "N0"},
            {"state_id": "a", "current": "C-a", "predictive": "P-a", "route_residue": "R-a", "local_now": "N1"},
            {"state_id": "b", "current": "C-b", "predictive": "P-b", "route_residue": "R-b", "local_now": "N1"},
            {"state_id": "z", "current": "C-z", "predictive": "P-z", "route_residue": "R-normal", "local_now": "N2"},
        ],
        "transitions": [
            {"from": "x", "action": "replace-left", "to": "a"},
            {"from": "x", "action": "replace-right", "to": "b"},
            {"from": "a", "action": "complete-right", "to": "z"},
            {"from": "b", "action": "complete-left", "to": "z"},
        ],
        "routes": [
            {
                "route_id": "left-then-complete",
                "boundary": "x-to-complete",
                "start_state": "x",
                "actions": ["replace-left", "complete-right"],
                "expected_endpoint": "z",
                "clock_translation": 2,
            },
            {
                "route_id": "right-then-complete",
                "boundary": "x-to-complete",
                "start_state": "x",
                "actions": ["replace-right", "complete-left"],
                "expected_endpoint": "z",
                "clock_translation": 2,
            },
        ],
        "critical_pairs": [
            {
                "left_route": "left-then-complete",
                "right_route": "right-then-complete",
                "normal_form": "z",
            }
        ],
        "direct_factored_pairs": [
            {"direct_route": "left-then-complete", "factored_route": "right-then-complete"}
        ],
        "interpretation": {
            "flatness_scope": "the two declared replacement orders only",
            "route_residue_policy": "erased only after both routes reach the certified normal form",
            "no_lineage_verdict": True,
        },
    }


def negative_holonomy_model() -> dict[str, Any]:
    return {
        "schema_version": "CST-TT-03",
        "model_id": "ROUTE-NEG-01",
        "title": "same-current replacement routes with predictive, residue, and clock holonomy",
        "claim_lanes": ["S-T"],
        "claim_ceiling": "finite route-indexed obstruction only",
        "states": [
            {"state_id": "x", "current": "C-start", "predictive": "P-start", "route_residue": "R-start", "local_now": "N-start"},
            {"state_id": "p0", "current": "C-same", "predictive": "P-left", "route_residue": "R-left", "local_now": "N0"},
            {"state_id": "p1", "current": "C-same", "predictive": "P-right", "route_residue": "R-right", "local_now": "N1"},
        ],
        "transitions": [
            {"from": "x", "action": "left-order", "to": "p0"},
            {"from": "x", "action": "right-order", "to": "p1"},
        ],
        "routes": [
            {
                "route_id": "left-order-route",
                "boundary": "same-declared-boundary",
                "start_state": "x",
                "actions": ["left-order"],
                "expected_endpoint": "p0",
                "clock_translation": 0,
            },
            {
                "route_id": "right-order-route",
                "boundary": "same-declared-boundary",
                "start_state": "x",
                "actions": ["right-order"],
                "expected_endpoint": "p1",
                "clock_translation": 1,
            },
        ],
        "critical_pairs": [
            {
                "left_route": "left-order-route",
                "right_route": "right-order-route",
                "normal_form": "p0",
            }
        ],
        "direct_factored_pairs": [],
        "interpretation": {
            "current_projection_agrees": True,
            "predictive_route_residue_retained": True,
            "global_now_claim_rejected": True,
            "no_lineage_verdict": True,
        },
    }


def positive_transport_model(route_status: str = "route-indexed") -> dict[str, Any]:
    model = {
        "schema_version": "CST-TT-03",
        "model_id": "TR-POS-01" if route_status == "route-indexed" else "TR-POS-02-FLAT",
        "title": "representative-independent bundled temporal transport",
        "claim_lanes": ["S-T"],
        "claim_ceiling": "finite structural temporal transport only",
        "source": {
            "carrier": {"code": 17, "label": "source-substrate"},
            "alphabet_id": "temporal-alphabet-S",
            "states": [
                _signature("s0", "P0", "O0", "K0", "G0", "3", "RS0", "MS0", 17),
                _signature("s0-rep", "P0", "O0", "K0", "G0", "3", "RS0", "MS0", 17),
                _signature("s1", "P1", "O1", "K1", "G1", "4", "RS1", "MS1", 17),
            ],
            "successor_edges": [["s0", "s1"], ["s0-rep", "s1"]],
            "tick_progress_edges": [["s0", "s1"], ["s0-rep", "s1"]],
            "record_strict_edges": [["3", "4"]],
            "temporal_witness": {
                "state_id": "s0",
                "future_sufficient": True,
                "order_stable": True,
                "successor_available": True,
                "tick_viable": True,
                "genuine_progress": True,
                "endogenous_arrow": True,
                "record_advances": True,
                "maintenance_owned": True,
                "no_external_scheduler": True,
            },
        },
        "target": {
            "carrier": {"code": 101, "label": "target-substrate"},
            "alphabet_id": "temporal-alphabet-T",
            "states": [
                _signature("t0", "Q0", "TO0", "TK0", "TG0", "30", "RT0", "MT0", 101),
                _signature("t1", "Q1", "TO1", "TK1", "TG1", "40", "RT1", "MT1", 101),
            ],
            "successor_edges": [["t0", "t1"]],
            "tick_progress_edges": [["t0", "t1"]],
            "record_strict_edges": [["30", "40"]],
            "temporal_witness": {
                "state_id": "t0",
                "future_sufficient": True,
                "order_stable": True,
                "successor_available": True,
                "tick_viable": True,
                "genuine_progress": True,
                "endogenous_arrow": True,
                "record_advances": True,
                "maintenance_owned": True,
                "no_external_scheduler": True,
            },
        },
        "bridge": {
            "source_reachable_states": ["s0", "s0-rep", "s1"],
            "state_map": {"s0": "t0", "s0-rep": "t0", "s1": "t1"},
            "source_predictive_equivalence_classes": [["s0", "s0-rep"], ["s1"]],
            "component_maps": {
                "predictive_class": {"P0": "Q0", "P1": "Q1"},
                "order_state": {"O0": "TO0", "O1": "TO1"},
                "tick_phase": {"K0": "TK0", "K1": "TK1"},
                "progress_state": {"G0": "TG0", "G1": "TG1"},
                "arrow_record": {"3": "30", "4": "40"},
                "route_residue": {"RS0": "RT0", "RS1": "RT1"},
                "maintenance_state": {"MS0": "MT0", "MS1": "MT1"},
            },
            "route_status": route_status,
            "route_residue_retained": route_status == "route-indexed",
            "flatness_certificate_ref": "formal/certificates/routes/ROUTE-POS-01.certificate.json" if route_status == "flat" else "",
            "ownership_interface_valid": True,
            "representative_scope": "declared reachable image only",
        },
        "nonclaims": [
            "no temporal lineage verdict",
            "no autonomy verdict",
            "no consciousness or phenomenal claim",
            "no personal-identity or survival claim",
        ],
    }
    return model


def memory_repair_model() -> dict[str, Any]:
    return {
        "schema_version": "CST-TT-03",
        "model_id": "MEM-POS-01",
        "title": "route memory repairs a current-equal predictive collision",
        "claim_lanes": ["S-T"],
        "observations": [
            {"route": "left", "current": "C0", "predictive": "P0", "route_residue": "R0"},
            {"route": "right", "current": "C0", "predictive": "P1", "route_residue": "R1"},
        ],
        "refined_predictor": {"C0|R0": "P0", "C0|R1": "P1"},
        "claim_ceiling": "finite predictive-representation repair only",
    }


def flat_memory_model() -> dict[str, Any]:
    return {
        "schema_version": "CST-TT-03",
        "model_id": "MEM-FLAT-01",
        "title": "flat predictive completion removes the need for route memory",
        "claim_lanes": ["S-T"],
        "observations": [
            {"route": "left", "current": "C0", "predictive": "PZ", "route_residue": "R-normal"},
            {"route": "right", "current": "C0", "predictive": "PZ", "route_residue": "R-normal"},
        ],
        "refined_predictor": {"C0|R-normal": "PZ"},
        "claim_ceiling": "finite flat predictive control only",
    }


def lost_memory_control() -> dict[str, Any]:
    model = memory_repair_model()
    model["model_id"] = "MEM-C01"
    model["title"] = "predictive collision with route residue erased"
    model["observations"][1]["route_residue"] = "R0"
    model["refined_predictor"] = {"C0|R0": "P0"}
    model["expected_primary_failure"] = "route-memory-separates-collision"
    return model


def positive_arrow_model() -> dict[str, Any]:
    return {
        "schema_version": "CST-TT-03",
        "model_id": "ARROW-POS-01",
        "title": "strict record progress preserved by a monotone cross-carrier map",
        "claim_lanes": ["S-T"],
        "source_records": [0, 1, 2],
        "target_records": [10, 12, 14],
        "record_map": {"0": 10, "1": 12, "2": 14},
        "source_arrow_steps": [[0, 1], [1, 2]],
        "claim_ceiling": "finite structural arrow transport only",
    }


def _mutated(base: dict[str, Any], model_id: str, title: str, primary: str, mutate: Callable[[dict[str, Any]], None]) -> dict[str, Any]:
    model = deepcopy(base)
    model["model_id"] = model_id
    model["title"] = title
    model["expected_primary_failure"] = primary
    mutate(model)
    return model


def transport_controls() -> list[dict[str, Any]]:
    base = positive_transport_model()
    return [
        _mutated(base, "TR-C01", "same carrier on both sides", "carriers-distinct", lambda m: m["target"]["carrier"].update(code=17)),
        _mutated(base, "TR-C02", "one temporal component map is absent", "component-maps-complete", lambda m: m["bridge"]["component_maps"].pop("order_state")),
        _mutated(base, "TR-C03", "predictive-equivalent representatives map differently", "predictive-representative-independence", lambda m: m["bridge"]["state_map"].update({"s0-rep": "t1"})),
        _mutated(base, "TR-C04", "predictive class map disagrees with target", "mapped-signature-agreement", lambda m: m["bridge"]["component_maps"]["predictive_class"].update({"P0": "Q1"})),
        _mutated(base, "TR-C05", "source successor has no target successor", "successor-preserved", lambda m: m["target"].update(successor_edges=[])),
        _mutated(base, "TR-C06", "tick progress edge is not transported", "tick-progress-preserved", lambda m: m["target"].update(tick_progress_edges=[])),
        _mutated(base, "TR-C07", "strict record edge is lost", "strict-record-arrow-preserved", lambda m: m["target"].update(record_strict_edges=[])),
        _mutated(base, "TR-C08", "route residue is discarded without flatness", "route-discipline-satisfied", lambda m: m["bridge"].update(route_residue_retained=False)),
        _mutated(base, "TR-C09", "maintenance state map disagrees", "maintenance-translated", lambda m: m["bridge"]["component_maps"]["maintenance_state"].update({"MS0": "MT1"})),
        _mutated(base, "TR-C10", "target signatures remain source-foreign owned", "ownership-interface-valid", lambda m: [row.update(owner=17) for row in m["target"]["states"]]),
        _mutated(base, "TR-C11", "transport record contains a lineage verdict", "forbidden-verdict-fields-absent", lambda m: m.update(lineage=True)),
        _mutated(base, "TR-C12", "target temporal witness is externally scheduled", "target-temporal-witness-valid", lambda m: m["target"]["temporal_witness"].update(no_external_scheduler=False)),
        _mutated(base, "TR-C13", "source and target reuse one temporal alphabet", "alphabets-distinct", lambda m: m["target"].update(alphabet_id="temporal-alphabet-S")),
        _mutated(base, "TR-C14", "flat route status lacks a flatness certificate", "route-discipline-satisfied", lambda m: m["bridge"].update(route_status="flat", route_residue_retained=False, flatness_certificate_ref="")),
        _mutated(base, "TR-C15", "route-indexed map collapses distinct route residues", "route-residue-retention-noncollapsing", lambda m: m["bridge"]["component_maps"]["route_residue"].update({"RS1": "RT0"})),
    ]


def route_controls() -> list[dict[str, Any]]:
    base = positive_route_model()
    controls = [
        _mutated(base, "ROUTE-C01", "critical pair does not join at the declared normal form", "every-declared-critical-pair-joins", lambda m: m["critical_pairs"][0].update(normal_form="a")),
        _mutated(base, "ROUTE-C02", "one branch ends with a distinct retained residue", "route-residue-trivial", lambda m: (m["states"].append({"state_id": "z2", "current": "C-z", "predictive": "P-z", "route_residue": "R-other", "local_now": "N2"}), m["transitions"][3].update(to="z2"), m["routes"][1].update(expected_endpoint="z2"))),
        _mutated(base, "ROUTE-C03", "same-boundary routes carry unequal clock translations", "clock-translation-holonomy-zero", lambda m: m["routes"][1].update(clock_translation=3)),
        _mutated(base, "ROUTE-C04", "one route uses an undeclared transition", "all-routes-valid", lambda m: m["transitions"].pop(2)),
        _mutated(base, "ROUTE-C05", "critical-pair registry supplies incompatible normal forms", "unique-normal-form-per-boundary", lambda m: m["critical_pairs"].append({"left_route": "left-then-complete", "right_route": "right-then-complete", "normal_form": "a"})),
        _mutated(base, "ROUTE-C06", "direct/factored audit names a missing route", "direct-factored-agreement", lambda m: m.update(direct_factored_pairs=[{"direct_route": "missing", "factored_route": "right-then-complete"}])),
        _mutated(base, "ROUTE-C07", "route certificate contains an identity verdict", "forbidden-verdict-fields-absent", lambda m: m.update(same_person=True)),
    ]
    lost = deepcopy(negative_holonomy_model())
    lost["model_id"] = "ROUTE-C08"
    lost["title"] = "predictive disagreement after route memory is erased"
    lost["expected_primary_failure"] = "memory-or-flatness-satisfied"
    lost["states"][2]["route_residue"] = "R-left"
    controls.append(lost)
    return controls


def arrow_controls() -> list[dict[str, Any]]:
    base = positive_arrow_model()
    return [
        _mutated(base, "ARROW-C01", "constant map is nonstrictly monotone but erases strict progress", "strict-progress-preserved", lambda m: m.update(record_map={"0": 10, "1": 10, "2": 10}, target_records=[10])),
        _mutated(base, "ARROW-C02", "order-reversing map", "nonstrict-monotone", lambda m: m.update(record_map={"0": 14, "1": 12, "2": 10})),
        _mutated(base, "ARROW-C03", "partial record map", "map-total", lambda m: m["record_map"].pop("2")),
        _mutated(base, "ARROW-C04", "no strict source arrow steps", "source-has-strict-arrow", lambda m: m.update(source_arrow_steps=[])),
    ]
