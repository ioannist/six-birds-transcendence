#!/usr/bin/env python3
"""Compare evaluated Lean POS-04 raw data with the frozen declaration.

The Lean snapshot is obtained from a fresh probe under /tmp. This script does
not modify the declaration, the Lean files, or the sibling T1 source.
"""

from __future__ import annotations

import ast
import copy
import json
import subprocess
import tempfile
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "audit/proposed_models/FIACH-POS-04.model.json"


def lean_snapshot() -> dict:
    with tempfile.TemporaryDirectory(prefix="pos04-lean-") as directory:
        probe = Path(directory) / "Snapshot.lean"
        probe.write_text("import CSTTT.POS04.Export\n#eval CSTTT.POS04.snapshot.compress\n")
        result = subprocess.run(
            ["lake", "env", "lean", str(probe)],
            cwd=ROOT / "lean", check=True, capture_output=True, text=True,
        )
    # Lean prints the compressed JSON as a quoted string.
    return json.loads(json.loads(result.stdout.strip()))


def compare(label: str, lean_value: object, declared_value: object) -> None:
    if lean_value != declared_value:
        raise AssertionError(
            f"{label}: Lean/JSON mismatch\n"
            f"  Lean: {str(lean_value)[:600]}\n"
            f"  JSON: {str(declared_value)[:600]}"
        )
    print(f"PASS {label}")


def select(record: dict, *fields: str) -> dict:
    return {key: record[key] for key in fields}


def exact_scaled(entry: str, scale: int, label: str) -> int:
    value = Fraction(entry) * scale
    if value.denominator != 1:
        raise AssertionError(f"{label}: nonintegral after scale {scale}: {entry}")
    return value.numerator


def fractions(value: object) -> object:
    """Normalize only a declared rational-valued tree, without float arithmetic."""
    if isinstance(value, dict):
        return {key: fractions(item) for key, item in value.items()}
    if isinstance(value, list):
        return [fractions(item) for item in value]
    return Fraction(value)


def compare_p(carrier: dict, entries: list[list[str]]) -> list[list[int]]:
    scaled = [[exact_scaled(entry, 4, f"T1 P[{i}][{j}]")
               for j, entry in enumerate(row)] for i, row in enumerate(entries)]
    compare("T1 P all 100 exact entries", carrier["p_num"], scaled)
    return scaled


def compare_route_readout(got: dict, model: dict) -> None:
    compare("corridor.future_route_readout",
            got["corridor"]["future_route_readout"],
            model["new_data"]["corridor"]["future_route_readout"])


def main() -> None:
    model = json.loads(MODEL.read_text())
    new = model["new_data"]
    t1 = model["t1_import"]
    got = lean_snapshot()
    carrier = got["carrier"]
    compare("carrier.tags", carrier["tags"], model["carrier"]["tags"])
    compare("T1 K order", carrier["kernel"], t1["kernel_order"])
    compare("T1 CORE", carrier["core"], t1["core"])
    compare("T1 ambient states in declared order", carrier["ambient_states"],
            t1["ambient_states"])
    compare("T1 public position", carrier["public_f"], t1["public_f"])
    compare("T1 canonical policy", carrier["canonical_policy"],
            t1["canonical_policy"])
    p_num = compare_p(carrier, t1["P"])
    planted = copy.deepcopy(t1["P"])
    changed = next((i, j) for i, row in enumerate(planted)
                   for j, value in enumerate(row) if Fraction(value) == Fraction(1, 4))
    planted[changed[0]][changed[1]] = "3/8"
    try:
        compare_p(carrier, planted)
    except AssertionError as error:
        if "nonintegral after scale 4" not in str(error):
            raise AssertionError(f"planted drift rejected for wrong reason: {error}") from error
        print(f"PASS planted P drift 1/4 -> 3/8 rejected at {changed}: {error}")
    else:
        raise AssertionError("planted P drift 1/4 -> 3/8 escaped exact comparison")
    classes: dict[str, int] = {}
    m_ids = [classes.setdefault(label, len(classes)) for label in t1["M_class_labels"]]
    compare("T1 M classes", carrier["m_classes"], m_ids)
    inputs = got["t1_inputs"]
    compare("T1 C separately, all 70 entries", inputs["C"], t1["C"])
    compare("T1 U separately, all 70 exact entries", fractions(inputs["U"]),
            fractions(t1["U"]))
    cu = [[sum(Fraction(t1["C"][i][k]) * Fraction(t1["U"][k][j])
               for k in range(len(t1["C"][i]))) for j in range(10)]
          for i in range(10)]
    compare("T1 C U all 100 exact entries", fractions(carrier["cu_num"]),
            [[entry * 2 for entry in row] for row in cu])
    compare("T1 hazards", inputs["hazards"], t1["hazards"])
    compare("T1 hazard rule on all 12 ambient states", inputs["hazard_flags"],
            {state: int(state[1]) in t1["hazards"]
             and int(state[3]) == int(state[1]) % 2
             for state in t1["ambient_states"]})
    for name in ("slip_hold", "slip_advance"):
        compare(f"T1 {name}", Fraction(inputs[name]), Fraction(t1[name]))
    for name in ("tau", "epsilon", "retention_threshold", "published_pi",
                 "published_core_mass", "published_tv", "published_defect"):
        observed = inputs["C1"][name]
        expected = t1["C1"][name]
        if name != "tau":
            observed, expected = fractions(observed), fractions(expected)
        compare(f"T1 C1.{name}", observed, expected)
    compare("T1 all action distributions, exact", fractions(got["raw_inputs"]["source"]["action_distributions"]),
            fractions(t1["all_action_distributions"]))
    for tag in carrier["tags"]:
        compare(f"{tag} tagged P all 100 exact entries", carrier["tagged_p_num"][tag], p_num)

    action_rows = got["raw_inputs"]["source"]["action_distributions"]
    actions = t1["actions"]
    computed_labels = []
    for index, state in enumerate(carrier["kernel"]):
        action_labels = tuple((action, tuple(sorted(
            "lethal" if int(destination[1]) in inputs["hazards"]
            and int(destination[3]) == int(destination[1]) % 2 else "safe"
            for destination in action_rows[state][action]
        ))) for action in actions)
        computed_labels.append((carrier["public_f"][index], action_labels))
    compare("T1 raw M labels from Lean action rows, f, hazards",
            computed_labels, [ast.literal_eval(label) for label in t1["M_class_labels"]])

    for field in ("histories", "bridge_frontier", "strict_source_edge",
                  "same_class_pair", "different_class_pair"):
        compare(field, got[field], new[field])
    compare("recognition_status", got["recognition_status"],
            new["recognition_status"])

    corridor_fields = ("stages", "events", "paths", "content_counterfactuals",
                       "interventions", "realized_stages")
    for field in corridor_fields:
        compare(f"corridor.{field}", got["corridor"][field], new["corridor"][field])
    compare_route_readout(got, model)
    changed_rule = copy.deepcopy(model)
    changed_rule["new_data"]["corridor"]["future_route_readout"]["rule"] = (
        "phase of last source WheelState in retained raw route tuple after one funded target step"
    )
    try:
        compare_route_readout(got, changed_rule)
    except AssertionError as error:
        if "corridor.future_route_readout" not in str(error):
            raise AssertionError(f"route-rule drift rejected for wrong reason: {error}") from error
        print("PASS planted future_route_readout.rule drift rejected")
    else:
        raise AssertionError("planted future_route_readout.rule drift escaped comparison")
    expected_register = {
        route["id"]: {
            "source_history": new["histories"][route["source_history"]],
            "events": route["events"],
        }
        for route in new["corridor"]["paths"]
    }
    compare("raw route register", got["route_register"], expected_register)

    for section, fields in {
        "latent_target": ("factor_state", "funded_receiver", "initial_budget_tokens"),
        "activation": ("source_present", "target_receiver_funded", "mixed_event_required"),
        "content": ("position_rule", "phase_rule", "history_overrides"),
        "route_register_write": ("rule",),
    }.items():
        compare(f"receiver.{section}", got["receiver"][section],
                select(new["receiver"][section], *fields))

    for field in ("owner_by_tag", "action_cost_tokens", "recharge_tokens_per_action",
                  "initial_budget_tokens", "source_available_after_withdrawal"):
        compare(f"maintenance.{field}", got["maintenance"][field],
                new["maintenance"][field])
    for section, fields in {
        "c4": ("current_channels", "candidate_connector_history",
               "candidate_hidden_pair", "expanded_channel"),
        "c5": ("vertices", "history_anchor", "protocols"),
        "c6": ("future_alphabet", "candidate_merged_pair", "route_record_owner",
               "future_interface"),
    }.items():
        for field in fields:
            compare(f"{section}.{field}", got[section][field], new[section][field])

    for tag in carrier["tags"]:
        for field in ("assemblages", "joint_observables", "reassembly", "branches",
                      "admissible_couplings"):
            compare(f"c7.{tag}.{field}", got["c7"][tag][field],
                    new["c7"]["by_tag"][tag][field])
        for field in ("action_distributions", "public_channel_rule", "tick_increment",
                      "record_writer_available", "resources"):
            actual = got["raw_inputs"][tag][field]
            expected = new["raw_inputs"]["by_tag"][tag][field]
            if field == "action_distributions":
                actual, expected = fractions(actual), fractions(expected)
            compare(f"raw_inputs.{tag}.{field}", actual, expected)

    compare("all 160 local assignments", got["local_assignments"],
            new["local_assignments"])
    for assignment in new["local_assignments"]:
        for pointer in assignment["primitive_refs"]:
            current = model
            for segment in pointer.strip("/").split("/"):
                if isinstance(current, list):
                    current = current[int(segment)]
                else:
                    current = current[segment]
    print("PASS all local primitive references resolve in the frozen JSON")
    expected_map = [select(row, "clause", "source_ref", "target_ref")
                    for row in new["staged_clause_map"]]
    compare("all 8 staged clause-map rows", got["staged_clause_map"], expected_map)
    print("COVERAGE: exact T1 K/CORE/ambient order, public f, canonical policy, P (100), "
          "separate C (70) and U (70), CU (100), hazards and 12 hazard-rule outputs, "
          "slip rates, C1 tau/epsilon/"
          "threshold/published values, all action rows, and raw M labels; both tagged P "
          "tables (100 each); all represented POS-04 histories, corridor including readout rule, "
          "receiver, ledger, "
          "C4-C7 coordinates, per-tag raw inputs, recognition status, 160 local assignments, "
          "8 staged-map rows, and every local primitive reference. Prose rules, grades, "
          "mutations, and predicate contracts are outside this data-transcription check.")
    print("PASS POS-04 Lean transcription: covered raw fields match the frozen JSON")


if __name__ == "__main__":
    main()
