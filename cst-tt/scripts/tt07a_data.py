from __future__ import annotations

from copy import deepcopy
from fractions import Fraction
import hashlib
import json
from pathlib import Path
from typing import Any, Mapping

PHASE = "CST-TT-07A"
SOURCE = {"code": 17, "label": "source-substrate"}
MIDDLE = {"code": 55, "label": "intermediate-substrate"}
TARGET = {"code": 101, "label": "target-substrate"}


def canonical_hash(value: object) -> str:
    payload = json.dumps(value, sort_keys=True, separators=(",", ":"), ensure_ascii=False).encode("utf-8")
    return hashlib.sha256(payload).hexdigest()


def load(root: Path, rel: str) -> dict[str, Any]:
    value = json.loads((root / rel).read_text(encoding="utf-8"))
    if not isinstance(value, dict):
        raise ValueError(rel)
    return value


def mixed_mode_direct_leg(root: Path) -> dict[str, Any]:
    overlap = load(root, "models/corridors/COR-POS-02A.model.json")
    base = load(root, "models/direct_successor/DS-POS-01.model.json")
    source_sig = deepcopy(overlap["episode"]["stages"][-1]["signature"])
    target_sig = deepcopy(source_sig)
    for field in ("predictive_rank", "order_rank", "tick_index", "progress_rank"):
        target_sig[field] += 1
    target_sig["record_value"] += 2
    target_sig["route_residue"] = [*source_sig["route_residue"], "mixed-mode-direct-M-T"]
    target_sig["maintenance_owner"] = TARGET["code"]
    target_sig["maintenance_state"] = "mixed-mode-direct-target-maint"
    payload = {key: deepcopy(value) for key, value in target_sig.items() if key != "maintenance_owner"}
    model = deepcopy(base)
    model.update(
        {
            "schema_version": "CST-TT-07A-model-v1",
            "model_id": "DS-POS-03-MIXED-MODE",
            "title": "direct temporal successor aligned to an overlap frontier",
            "source_carrier": MIDDLE,
            "target_carrier": TARGET,
            "last_source_event_id": "mixed-mode-middle-final",
            "first_target_event_id": "mixed-mode-target-first",
            "operational_dependency_id": "mixed-mode-direct-edge",
            "nonclaims": [
                "not a strict overlap leg",
                "not by itself a Temporal-FIACH certificate",
                "no phenomenal continuity or identity conclusion",
            ],
        }
    )
    model["episode"] = {
        "stages": [
            {"stage": 0, "active_support": [MIDDLE], "temporal_realized": True, "signature": source_sig},
            {"stage": 1, "active_support": [TARGET], "temporal_realized": True, "signature": target_sig},
        ],
        "events": [
            {
                "event_id": "mixed-mode-middle-final",
                "event_kind": "temporal-update",
                "owner": MIDDLE,
                "stage": 0,
                "output_payload": payload,
            },
            {
                "event_id": "mixed-mode-target-first",
                "event_kind": "temporal-update",
                "owner": TARGET,
                "stage": 1,
                "input_payload": payload,
                "output_payload": payload,
            },
        ],
        "dependencies": [
            {
                "dependency_id": "mixed-mode-direct-edge",
                "parent_event_id": "mixed-mode-middle-final",
                "child_event_id": "mixed-mode-target-first",
                "dependency_kind": "live-temporal-handoff",
                "payload": payload,
                "payload_sha256": canonical_hash(payload),
                "counterfactually_necessary": True,
                "storage_mediator": False,
                "replayable_archive": False,
                "alternative_temporal_parent": False,
                "single_use_temporal_token": True,
            }
        ],
    }
    return model


def full_defect_profile() -> dict[str, Any]:
    hard_ids = [
        "H01-distinct-carriers",
        "H02-C1-objecthood",
        "H03-C2-strict-promotion",
        "H04-C3-reflexive-coordinate",
        "H05-C4-nonexposure",
        "H06-C5-action-credit",
        "H07-C6-temporal-closure",
        "H08-C7-binding",
        "H09-C8-viability",
        "H10-route-discipline",
        "H11-strict-lineage",
        "H12-post-withdrawal-autonomy",
    ]
    soft = [
        ("S01-predictive-margin", Fraction(1, 10), Fraction(1, 2)),
        ("S02-order-margin", Fraction(1, 5), Fraction(1, 2)),
        ("S03-tick-margin", Fraction(1, 4), Fraction(1, 2)),
        ("S04-progress-margin", Fraction(0, 1), Fraction(1, 2)),
        ("S05-record-margin", Fraction(1, 3), Fraction(1, 2)),
    ]
    components = [
        {
            "component_id": cid,
            "gate_kind": "hard",
            "defect": {"numerator": 0, "denominator": 1},
            "tolerance": {"numerator": 0, "denominator": 1},
        }
        for cid in hard_ids
    ]
    components.extend(
        {
            "component_id": cid,
            "gate_kind": "soft",
            "defect": {"numerator": defect.numerator, "denominator": defect.denominator},
            "tolerance": {"numerator": tolerance.numerator, "denominator": tolerance.denominator},
        }
        for cid, defect, tolerance in soft
    )
    return {
        "schema_version": "CST-TT-07A-defect-v1",
        "profile_id": "DEF-POS-01",
        "title": "exact vector defect profile with nonnegotiable hard gates",
        "expected_components": [*hard_ids, *(cid for cid, _, _ in soft)],
        "components": components,
        "acceptance_rule": "componentwise-hard-gated",
        "scalar_summary_role": "diagnostic-only",
        "claim_lanes": ["M", "S-T", "S-R", "S-L", "A"],
        "claim_ceiling": "exact finite defect and robustness audit only",
        "nonclaims": ["no scalar score licenses a failed hard gate", "no empirical noise model", "no consciousness conclusion"],
    }


def defect_controls() -> list[tuple[str, str, dict[str, Any]]]:
    base = full_defect_profile()
    controls: list[tuple[str, str, dict[str, Any]]] = []

    m = deepcopy(base); m["profile_id"] = "DEF-C01"; m["components"][6]["defect"] = {"numerator": 1, "denominator": 1000}
    controls.append(("DEF-C01", "every-hard-gate-exact", m))
    m = deepcopy(base); m["profile_id"] = "DEF-C02"; m["components"][-2]["defect"] = {"numerator": 3, "denominator": 4}
    controls.append(("DEF-C02", "every-component-within-tolerance", m))
    m = deepcopy(base); m["profile_id"] = "DEF-C03"; m["components"] = m["components"][:-1]
    controls.append(("DEF-C03", "expected-components-exact", m))
    m = deepcopy(base); m["profile_id"] = "DEF-C04"; m["components"][-1]["component_id"] = m["components"][-2]["component_id"]
    controls.append(("DEF-C04", "component-ids-unique", m))
    m = deepcopy(base); m["profile_id"] = "DEF-C05"; m["components"][-1]["defect"] = {"numerator": 1, "denominator": 0}
    controls.append(("DEF-C05", "component-rows-well-formed", m))
    m = deepcopy(base); m["profile_id"] = "DEF-C06"; m["scalar_summary_role"] = "authoritative"
    controls.append(("DEF-C06", "scalar-summary-diagnostic-only", m))
    return controls


def equal_scalar_profiles() -> tuple[dict[str, Any], dict[str, Any]]:
    accepted = full_defect_profile()
    rejected = full_defect_profile()
    accepted["profile_id"] = "DEF-EQUAL-SCALAR-ACCEPTED"
    rejected["profile_id"] = "DEF-EQUAL-SCALAR-REJECTED"
    for row in accepted["components"]:
        row["defect"] = {"numerator": 0, "denominator": 1}
    for row in rejected["components"]:
        row["defect"] = {"numerator": 0, "denominator": 1}
    accepted["components"][-1]["defect"] = {"numerator": 1, "denominator": 1}
    accepted["components"][-1]["tolerance"] = {"numerator": 1, "denominator": 1}
    rejected["components"][0]["defect"] = {"numerator": 1, "denominator": 1}
    return accepted, rejected


def robustness_model() -> dict[str, Any]:
    return {
        "schema_version": "CST-TT-07A-robustness-v1",
        "model_id": "ROB-POS-01",
        "title": "hard-gate-preserving temporal margin box",
        "dimensions": [
            {"dimension_id": "predictive-step", "base_increment": 4, "minimum_increment": 1, "radius": 2},
            {"dimension_id": "order-step", "base_increment": 3, "minimum_increment": 1, "radius": 1},
            {"dimension_id": "tick-step", "base_increment": 3, "minimum_increment": 1, "radius": 1},
            {"dimension_id": "progress-step", "base_increment": 2, "minimum_increment": 1, "radius": 1},
            {"dimension_id": "record-step", "base_increment": 5, "minimum_increment": 1, "radius": 3},
        ],
        "hard_gates": {
            "distinct-carriers": True,
            "route-discipline": True,
            "target-ownership": True,
            "integrated-package": True,
            "strict-lineage-mode": True,
            "post-withdrawal-autonomy": True,
        },
        "acceptance_rule": "hard-gates-and-componentwise-margins",
        "scalar_score_role": "diagnostic-only",
        "claim_lanes": ["S-T", "S-R", "S-L", "A"],
        "claim_ceiling": "bounded exact perturbation box inside the finite structural model",
        "nonclaims": ["not an empirical noise model", "not a robustness theorem outside the declared box", "not consciousness stability"],
    }


def robustness_controls() -> list[tuple[str, str, dict[str, int], dict[str, bool]]]:
    gates = robustness_model()["hard_gates"]
    assert isinstance(gates, dict)
    rows = [
        ("ROB-C01", "progress margin leaves box and stalls", {"progress-step": -2}, dict(gates)),
        ("ROB-C02", "record margin leaves box and loses strict advance", {"record-step": -5}, dict(gates)),
        ("ROB-C03", "route hard gate fails", {}, {**gates, "route-discipline": False}),
        ("ROB-C04", "ownership hard gate fails", {}, {**gates, "target-ownership": False}),
        ("ROB-C05", "package hard gate fails", {}, {**gates, "integrated-package": False}),
        ("ROB-C06", "autonomy hard gate fails", {}, {**gates, "post-withdrawal-autonomy": False}),
    ]
    return rows


def unbounded_spec() -> dict[str, Any]:
    return {
        "schema_version": "CST-TT-07A-unbounded-v1",
        "certificate_id": "UNB-POS-01",
        "autonomy_model_ref": "models/autonomy/AUT-POS-01.model.json",
        "claim_scope": "unbounded run existence inside the exact finite controlled model",
        "physical_liveness_status": "not-established",
        "claim_lanes": ["A"],
        "claim_ceiling": "model-relative unbounded controlled invariance only",
        "nonclaims": [
            "no indefinite physical persistence outside the finite abstraction",
            "no finite resource sufficiency beyond the declared regenerative model",
            "no consciousness, felt continuity, survival, or identity conclusion",
        ],
    }
