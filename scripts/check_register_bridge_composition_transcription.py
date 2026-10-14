#!/usr/bin/env python3
"""Compare predeclared raw register instructions with their actual interpreter."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "audit/proposed_models/TTH07-REGISTER-BRIDGE-COMPOSITION.model.json"
PROBE = r"""
import Lean
import CSTTT.Targets.GenericHandoff.RegisterCompositionModels
open CSTTT.TargetTheory.GenericHandoff
open RegisterInterpreter RegisterSubstitution RegisterCompositionModels
example (a : Assignment Bool CellValue) :
    output a = (a false).map (fun n => (sourceValue + n) * multiplier) := output_equation a
example (a : Assignment Bool CellValue) :
    Ready (program first second) a ↔ a false ≠ none := ready_iff a
example : ¬ Ready first unusedCut := unused_prefix_not_ready
example : Ready (program first second) unusedCut := unused_composite_ready
example : ExecutionBridge.Valid bridge CSTTT.POS04.Assigned.canonical := bridge_positive
example : eagerOutput unusedCut = none := eager_missing
def firstShape : Bool :=
  (match first false with
   | .map _ (.pair (.register _) (.cell k)) => k == false
   | _ => false) &&
  (match first true with | .map _ (.cell k) => k == true | _ => false)
def secondShape : Bool :=
  match second () with | .map _ (.register r) => r == false | _ => false
def eagerShape : Bool :=
  match eager with
  | .choose c yes no =>
      evalPartial positive (fun _ => none) () c == some true &&
      reads c == [] && reads yes == [false] && reads no == [true]
  | _ => false
#eval IO.println (Lean.Json.compress (Lean.Json.mkObj [
  ("firstShape", Lean.toJson firstShape), ("secondShape", Lean.toJson secondShape),
  ("eagerShape", Lean.toJson eagerShape),
  ("source", Lean.toJson sourceValue), ("multiplier", Lean.toJson multiplier),
  ("positiveFalse", Lean.toJson (positive false)), ("positiveTrue", Lean.toJson (positive true)),
  ("consumedFalse", Lean.toJson (consumedCut false)), ("consumedTrue", Lean.toJson (consumedCut true)),
  ("unusedFalse", Lean.toJson (unusedCut false)), ("unusedTrue", Lean.toJson (unusedCut true)),
  ("changedFalse", Lean.toJson (changed false)), ("changedTrue", Lean.toJson (changed true)),
  ("firstFalse", Lean.toJson ((first false).eval positive (fun _ => sourceValue) ())),
  ("firstTrue", Lean.toJson ((first true).eval positive (fun _ => sourceValue) ())),
  ("readsSecond", Lean.toJson (reads (second ()))),
  ("compositeDependencies", Lean.toJson ((program first second ()).dependencies)),
  ("positive", Lean.toJson (output positive)), ("consumed", Lean.toJson (output consumedCut)),
  ("unused", Lean.toJson (output unusedCut)), ("changed", Lean.toJson (output changed)),
  ("eagerPositive", Lean.toJson (eagerOutput positive)), ("eagerCut", Lean.toJson (eagerOutput unusedCut))
]))
"""


def compare(model: dict, observed: dict) -> None:
    fixed = {
        "cell_type": "Bool", "cell_values": "Nat", "source_register_type": "Unit",
        "middle_register_type": "Bool", "middle_values": {"false": "Nat", "true": "Bool"},
        "target_register_type": "Unit",
        "first": {"false": "source unit + cell false", "true": "cell true > 0"},
        "bridge_fixture": "existing POS04ExecutionBridge followed by identity of POS04ReceiverFrontier",
    }
    for key, value in fixed.items():
        if model[key] != value:
            raise ValueError(f"raw typed instruction/interface mismatch: {key}")
    if model["second"]["unit"] != "middle false * multiplier":
        raise ValueError("second raw instruction mismatch")
    controls = model["controls"]
    if controls["eager"] != "choose literal true, register false, bool-to-nat register true":
        raise ValueError("raw eager instruction mismatch")
    s, mul = model["source_register_value"], model["second"]["multiplier"]
    a, c, u, changed = model["positive_assignment"], controls["missing_consumed"], controls["missing_unused"], controls["changed_cell"]
    def out(values):
        n = values["false"]
        return None if n is None else (s + n) * mul
    expected = {
        "firstShape": True, "secondShape": True, "eagerShape": True,
        "source": s, "multiplier": mul,
        "positiveFalse": a["false"], "positiveTrue": a["true"],
        "consumedFalse": c["false"], "consumedTrue": c["true"],
        "unusedFalse": u["false"], "unusedTrue": u["true"],
        "changedFalse": changed["false"], "changedTrue": changed["true"],
        "firstFalse": s + a["false"], "firstTrue": a["true"] > 0,
        "readsSecond": [False], "compositeDependencies": [False],
        "positive": out(a), "consumed": out(c), "unused": out(u), "changed": out(changed),
        "eagerPositive": s + a["false"],
        "eagerCut": None if u["true"] is None or u["false"] is None else s + u["false"],
    }
    if expected != observed:
        raise ValueError(f"interpreted instruction/readout mismatch: expected {expected}, observed {observed}")


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="tth07-register-bridge-") as directory:
        path = Path(directory) / "RegisterBridge.lean"
        path.write_text(PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean", capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
        observed = json.loads(run.stdout.strip())
    model = json.loads(MODEL.read_text())
    compare(model, observed)
    changes = [
        ("source register", lambda m: m.__setitem__("source_register_value", m["source_register_value"] + 1)),
        ("second instruction", lambda m: m["second"].__setitem__("multiplier", m["second"]["multiplier"] + 1)),
        ("positive cell", lambda m: m["positive_assignment"].__setitem__("false", m["positive_assignment"]["false"] + 1)),
        ("unused-register cut", lambda m: m["controls"]["missing_unused"].__setitem__("true", 1)),
    ]
    for label, mutate in changes:
        drift = copy.deepcopy(model)
        mutate(drift)
        try:
            compare(drift, observed)
        except ValueError:
            print(f"CAUGHT planted {label} drift")
        else:
            raise AssertionError(f"missed planted {label} drift")
    print("PASS typed raw substitution: actual consumed/unused/eager/changed readouts; all-partial equation and shared-frame bridge positive kernel-checked")
    print("Scope: immutable shared assignment and exact middle raw frame; identity continuation is not a new physical hop")


if __name__ == "__main__":
    main()
