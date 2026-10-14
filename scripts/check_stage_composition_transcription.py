#!/usr/bin/env python3
"""Check the declared primitive composition witness against interpreted Lean data."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "audit/proposed_models/TTH07-STAGE-COMPOSITION.model.json"
PROBE = r"""
import Lean
import CSTTT.Targets.GenericHandoff.StageCompositionModels
open CSTTT.TargetTheory.GenericHandoff StageCompositionModels
example (a : Assignment Unit (fun _ => Nat)) :
    output a = (a ()).map (fun n => (n + increment) * multiplier) := output_equation a
example (a : Assignment Unit (fun _ => Nat)) : absentScopeOutput a = none := scope_missing a
example (a : Assignment Unit (fun _ => Nat)) : absentRightOutput a = none := right_arrow_missing a
#eval IO.println (Lean.Json.compress (Lean.Json.mkObj [
  ("increment", Lean.toJson increment), ("multiplier", Lean.toJson multiplier),
  ("positiveValue", Lean.toJson positiveValue),
  ("scopeLength", Lean.toJson (scopes ()).length),
  ("indicesLength", Lean.toJson cover.indices.length),
  ("adjacent", Lean.toJson (cover.adjacent () ())),
  ("output", Lean.toJson (output (fun _ => some positiveValue))),
  ("global", Lean.toJson (globalOutput (fun _ => some positiveValue))),
  ("scopeMissing", Lean.toJson (absentScopeOutput (fun _ => some positiveValue))),
  ("rightMissing", Lean.toJson (absentRightOutput (fun _ => some positiveValue))),
  ("sourceMissing", Lean.toJson (output (fun _ => none))),
  ("changed", Lean.toJson (changedOutput (fun _ => some positiveValue))) ]))
"""


def compare(model: dict, observed: dict) -> None:
    for field in ("source_cell_type", "middle_cell_type", "target_cell_type", "index_type"):
        if model[field] != "Unit":
            raise ValueError(f"{field}: typed cell/index mismatch")
    if model["value_type_each"] != "Nat":
        raise ValueError("value_type_each: value type mismatch")
    if (model["left_instruction"]["operation"], model["right_instruction"]["operation"]) != ("add", "multiply"):
        raise ValueError("raw operation mismatch")
    if model["scope_each"] != ["unit"] or model["cover_indices_each"] != ["unit"]:
        raise ValueError("raw scope/cover mismatch")
    controls = model["controls"]
    if controls["missing_source"] != "source unit = none" or controls["missing_intermediate_scope"] != []:
        raise ValueError("raw absence control mismatch")
    if controls["missing_right_arrow"] != "right unit unit = none" or controls["changed_left_instruction"]["operation"] != "add":
        raise ValueError("raw instruction control mismatch")
    inc, mul, value = model["left_instruction"]["parameter"], model["right_instruction"]["parameter"], model["positive_source_value"]
    expected = {"increment": inc, "multiplier": mul, "positiveValue": value,
        "scopeLength": len(model["scope_each"]), "indicesLength": len(model["cover_indices_each"]),
        "adjacent": model["cover_adjacency_each"], "output": (value + inc) * mul,
        "global": (value + inc) * mul, "scopeMissing": None, "rightMissing": None,
        "sourceMissing": None, "changed": (value + controls["changed_left_instruction"]["parameter"]) * mul}
    if expected != observed:
        raise ValueError(f"interpreted raw data/readout mismatch: expected {expected}, observed {observed}")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="tth07-stage-") as directory:
        path = Path(directory) / "Stage.lean"
        path.write_text(PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean", capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
        observed = json.loads(run.stdout.strip())
    model = json.loads(MODEL.read_text())
    compare(model, observed)
    mutations = [("increment", "left_instruction", "parameter"),
                 ("multiplier", "right_instruction", "parameter"),
                 ("changed instruction", "controls", "changed_left_instruction")]
    for label, outer, inner in mutations:
        drift = copy.deepcopy(model)
        if outer == "controls":
            drift[outer][inner]["parameter"] += 1
        else:
            drift[outer][inner] += 1
        try:
            compare(drift, observed)
        except ValueError:
            print(f"CAUGHT planted {label} drift")
        else:
            raise AssertionError(f"missed planted {label} drift")
    drift = copy.deepcopy(model)
    drift["scope_each"] = []
    try:
        compare(drift, observed)
    except ValueError:
        print("CAUGHT planted intermediate scope drift")
    else:
        raise AssertionError("missed planted intermediate scope drift")
    print("PASS typed primitive-map witness: raw parameters/cover and actual sequential outputs; all-partial absence equations kernel-checked")
    print("Scope: primitive algebra only; no full Temporal-FIACH composition or two-hop model claim")


if __name__ == "__main__":
    main()
