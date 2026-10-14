#!/usr/bin/env python3
"""Read-only exact comparison of Lean-evaluated COR-POS-02 tables and JSON."""
from __future__ import annotations
from copy import deepcopy
import hashlib
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
FILES = {"left": "COR-POS-02A", "right": "COR-POS-02B", "composed": "COR-POS-02-COMPOSED"}


def lean_snapshot():
    with tempfile.TemporaryDirectory(prefix="g4-corridor-", dir="/tmp") as folder:
        probe = Path(folder) / "Probe.lean"
        probe.write_text("import CSTTT.Corridor.AtomicExport\n#eval CSTTT.CorridorTheory.AtomicChain.Models.atomicSnapshot.compress\n")
        result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean",
                                capture_output=True, text=True, check=True)
    return json.loads(json.loads(result.stdout.strip()))


def episode(m):
    e = m["episode"]
    return {"stages": [{"stage": s["stage"], "active_support": [c["code"] for c in s["active_support"]],
                        "temporal_realized": s["temporal_realized"], "signature": s["signature"]}
                       for s in e["stages"]],
            "events": [{"event_id": ev["event_id"], "owner": ev["owner"]["code"], "stage": ev["stage"]}
                       for ev in e["events"]],
            "dependencies": [[d["parent_event_id"], d["child_event_id"]] for d in e["dependencies"]],
            "carrier_chain": [c["code"] for c in m["carrier_chain"]]}


def leg(m):
    l = m["legs"][0]
    c = l["counterfactual"]
    assert c["projection_fields"] == ["predictive_rank", "tick_index", "record_value"]
    out = {k: c[k] for k in ("base_projection", "source_contribution", "target_contribution", "full_projection",
                             "source_removed_projection", "target_removed_projection")}
    out.update(l["audit_event_ids"])
    out.update(intervention_mode="additive", source=l["source_carrier"]["code"], target=l["target_carrier"]["code"],
               start_stage=l["start_stage"], end_stage=l["end_stage"])
    stages = m["episode"]["stages"]
    assert l["audit_later_stage"] == l["takeover_stage"] == l["end_stage"]
    audit = {e["event_id"]: e for e in m["episode"]["events"]}
    assert audit[l["audit_event_ids"]["source_mixed_event"]]["stage"] == l["mixed_stage"]
    assert audit[l["audit_event_ids"]["target_mixed_event"]]["stage"] == l["mixed_stage"]
    updates = []
    for a, b in zip(stages, stages[1:]):
        f, g = a["signature"], b["signature"]
        assert g["route_residue"][:len(f["route_residue"])] == f["route_residue"]
        u = {out_name: g[src_name] - f[src_name] for out_name, src_name in (
            ("predictiveAdvance", "predictive_rank"), ("orderAdvance", "order_rank"),
            ("tickAdvance", "tick_index"), ("progressAdvance", "progress_rank"), ("recordAdvance", "record_value"))}
        u.update(appendResidue=g["route_residue"][len(f["route_residue"]):],
                 nextMaintenance=g["maintenance_state"], nextOwner=g["maintenance_owner"])
        updates.append(u)
    out["updates"] = updates
    return out


def compare(got, models):
    for name, m in models.items():
        assert all(e["event_kind"] == "temporal-update" for e in m["episode"]["events"])
        assert all(d["dependency_kind"] in ("temporal-step", "mixed-update") for d in m["episode"]["dependencies"])
        assert got[name] == episode(m), f"{name}: operative episode differs"
    for name in ("left", "right"):
        assert got[name + "_leg"] == leg(models[name]), f"{name}: operative leg differs"
    # Event order is irrelevant to the graph; COMPOSED stores it lexically.
    built = deepcopy(got["constructed"])
    built["events"].sort(key=lambda e: e["event_id"])
    declared = episode(models["composed"])
    declared["events"].sort(key=lambda e: e["event_id"])
    assert built == declared, "constructed concatenation differs from COMPOSED"
    # Composed leg descriptors are exactly the atomic inputs with shifted ordinal references.
    for i, name in enumerate(("left", "right")):
        expected = deepcopy(models[name]["legs"][0])
        for k in ("start_stage", "end_stage", "mixed_stage", "takeover_stage", "audit_later_stage"):
            expected[k] += 2 * i
        assert models["composed"]["legs"][i] == expected, "COMPOSED leg descriptor drift"


def main():
    paths = {k: ROOT / f"cst-tt/models/corridors/{v}.model.json" for k, v in FILES.items()}
    models = {k: json.loads(p.read_text()) for k, p in paths.items()}
    got = lean_snapshot()
    compare(got, models)
    for name, mutate in (
        ("snapshot", lambda m: m["left"]["episode"]["stages"][1]["signature"].update(progress_rank=0)),
        ("event", lambda m: m["left"]["episode"]["events"][1].update(stage=2)),
        ("intervention", lambda m: m["left"]["legs"][0]["counterfactual"].update(source_contribution=[0,0,0])),
    ):
        changed = deepcopy(models)
        mutate(changed)
        try:
            compare(got, changed)
        except AssertionError:
            print(f"Planted {name} drift: CAUGHT (in memory)")
        else:
            raise AssertionError(f"Missed {name} drift")
    print("PASS: Lean-evaluated stages (all eight frontier fields, support, realization), events/owners/ordinals, dependencies, carrier chain, additive inputs and computed removal projections, audit references, derived updates; constructed COMPOSED stages/event graph/leg descriptors.")
    print("Non-evidence: stored transport booleans and route-status labels; descriptive labels/metadata are not operative inputs.")
    for name, p in paths.items():
        print(f"{FILES[name]} sha256 {hashlib.sha256(p.read_bytes()).hexdigest()}")


if __name__ == "__main__":
    main()
