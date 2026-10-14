#!/usr/bin/env python3
"""Check interpreted stage globals, namespace reads, and exact bridge probes."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "audit/proposed_models/TTH07-STAGED-ASSIGNMENT-SPAN.model.json"
PROBE = r"""
import Lean
import CSTTT.Targets.GenericHandoff.StagedAssignmentSpanModels
open CSTTT.TargetTheory.GenericHandoff
open RegisterInterpreter CellReindex StagedAssignmentSpanModels
example (a : Assignment Unit (fun _ => Nat)) :
    output a = (a ()).map (fun n => (n+StageCompositionModels.increment)+(n+StageCompositionModels.increment)*StageCompositionModels.multiplier) :=
  output_equation a
example : ¬ ∀ a : Assignment Unit (fun _ => Nat), output a = shortcut a := same_context_not_equivalent
example (a : CSTTT.POS04.Assigned.Assignment) :
    ExecutionBridge.Valid nativeBridge (nativeSpan a) ↔ ExecutionBridge.Valid POS04ExecutionBridge.raw a := native_valid_iff a
example (a : CSTTT.POS04.Assigned.Assignment) :
    ExecutionBridge.SemanticReadout nativeBridge (nativeSpan a) ↔
      ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw a := native_semantic_iff a
example : ExecutionBridge.Valid nativeBridge (nativeSpan CSTTT.POS04.Assigned.canonical) := native_positive
example (a : CSTTT.POS04.Assigned.Assignment) : ¬ ExecutionBridge.SemanticReadout nativeBridge
    (nativeSpan (CSTTT.POS04.Assigned.put a .eventTable none)) := native_deleted_atomic_no_readout a
def label : Sum Unit Unit → String | .inl _ => "middle" | .inr _ => "final"
#eval IO.println (Lean.Json.compress (Lean.Json.mkObj [
  ("increment", Lean.toJson StageCompositionModels.increment),
  ("multiplier", Lean.toJson StageCompositionModels.multiplier),
  ("positiveSource", Lean.toJson (positive ())),
  ("coverIndices", Lean.toJson StageCompositionModels.cover.indices.length),
  ("scopeLength", Lean.toJson (StageCompositionModels.cover.scopes ()).length),
  ("middle", Lean.toJson (span positive (.inl ()))),
  ("final", Lean.toJson (span positive (.inr ()))),
  ("bothReads", Lean.toJson (readBoth.dependencies.map label)),
  ("shortcutReads", Lean.toJson (sameContext.dependencies.map label)),
  ("output", Lean.toJson (output positive)), ("shortcut", Lean.toJson (shortcut positive)),
  ("missing", Lean.toJson (output (fun _ => none))),
  ("rightCut", Lean.toJson (rightCutOutput positive)),
  ("limit", Lean.toJson limit), ("rejectedSource", Lean.toJson (rejectedSource ())),
  ("rejected", Lean.toJson (partialOutput rejectedSource)),
  ("partialPositive", Lean.toJson (partialOutput positive)),
  ("nativeAtomicBranch", Lean.toJson (decide (nativeBridge.source.acquisition.events.cell = Sum.inr CSTTT.POS04.Assigned.Cell.eventTable)))
]))
"""


def compare(model: dict, observed: dict) -> None:
    fixed = {
        "cell_type_each": "Unit", "value_type_each": "Nat",
        "cover_indices_each": ["unit"], "cover_scope_each": ["unit"],
        "span_expression": "cell inl unit + cell inr unit",
        "same_context_control": "cell inl unit + cell inl unit",
        "native_package_stages": "existing POS04DispatchedStage.raw twice",
        "native_bridge": "POS04ExecutionBridge.raw reindexed into final Sum.inr branch",
    }
    for key, value in fixed.items():
        if model[key] != value:
            raise ValueError(f"raw namespace/model mismatch: {key}")
    stages, controls = model["raw_stages"], model["controls"]
    if stages["first"] != "add" or stages["second"] != "multiply":
        raise ValueError("raw stage operation mismatch")
    expected_controls = {
        "source_missing": None, "right_arrow_missing": "second unit unit = none",
        "partial_first_instruction": "reject values above limit, otherwise add increment",
        "native_atomic_missing": "Assigned.put original eventTable none",
    }
    for key, value in expected_controls.items():
        if controls[key] != value:
            raise ValueError(f"raw control mismatch: {key}")
    n, inc, mul = model["positive_source"], stages["increment"], stages["multiplier"]
    mid, final = n + inc, (n + inc) * mul
    rejected = controls["rejected_source"]
    rejected_out = None if rejected > controls["limit"] else (rejected + inc) * (1 + mul)
    partial_positive = None if n > controls["limit"] else mid + final
    expected = {
        "increment": inc, "multiplier": mul, "positiveSource": n,
        "coverIndices": len(model["cover_indices_each"]), "scopeLength": len(model["cover_scope_each"]),
        "middle": mid, "final": final, "bothReads": ["middle", "final"], "shortcutReads": ["middle", "middle"],
        "output": mid + final, "shortcut": mid + mid, "missing": None, "rightCut": None,
        "limit": controls["limit"], "rejectedSource": rejected, "rejected": rejected_out,
        "partialPositive": partial_positive, "nativeAtomicBranch": True,
    }
    if expected != observed:
        raise ValueError(f"interpreted stage/span mismatch: expected {expected}, observed {observed}")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="tth07-staged-span-") as directory:
        path = Path(directory) / "Span.lean"
        path.write_text(PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean", capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
        observed = json.loads(run.stdout.strip())
    model = json.loads(MODEL.read_text())
    compare(model, observed)
    mutations = [
        ("first instruction", lambda m: m["raw_stages"].__setitem__("increment", m["raw_stages"]["increment"] + 1)),
        ("second instruction", lambda m: m["raw_stages"].__setitem__("multiplier", m["raw_stages"]["multiplier"] + 1)),
        ("reused cell namespace", lambda m: m.__setitem__("span_expression", m["same_context_control"])),
        ("partial instruction threshold", lambda m: m["controls"].__setitem__("limit", 4)),
    ]
    for label, mutate in mutations:
        drift = copy.deepcopy(model)
        mutate(drift)
        try:
            compare(drift, observed)
        except ValueError:
            print(f"CAUGHT planted {label} drift")
        else:
            raise AssertionError(f"missed planted {label} drift")
    print("PASS raw staged assignment span: actual distinct globals, namespace reads, partial rejection and native all-partial bridge/semantic adapters; four planted drifts caught")
    print("Scope: program/assignment transport; physical middle compatibility, supported next acquisition and full Temporal-FIACH composition remain")


if __name__ == "__main__":
    main()
