#!/usr/bin/env python3
"""Check raw cover selection and the derived POS04 package pipeline."""
import copy
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "audit/proposed_models/TTH07-GLOBAL-PACKAGE-COMPOSITION.model.json"
PROBE = r"""
import Lean
import CSTTT.Targets.GenericHandoff.GlobalStageCompositionModels
import CSTTT.Targets.GenericHandoff.POS04DispatchedComposition
open CSTTT.TargetTheory.GenericHandoff GlobalStageCompositionModels
example (a : Assignment Unit (fun _ => Nat)) :
    output a = (a ()).map (fun n => (n + StageCompositionModels.increment) * StageCompositionModels.multiplier) := output_equation a
example (a : Assignment Unit (fun _ => Nat)) : shadowOutput a = none := shadow_output a
example (a : CSTTT.POS04.Assigned.Assignment) : DispatchedPackage.global POS04DispatchedComposition.raw a = a :=
  POS04DispatchedComposition.target_equation a
example (a : CSTTT.POS04.Assigned.Assignment) : DispatchedPackage.Valid POS04DispatchedComposition.raw a ↔
    CSTTT.POS04.Assigned.Complete CSTTT.POS04.Assigned.primitiveCells a ∧ CSTTT.POS04.Assigned.AssignedPackagePass a .target :=
  POS04DispatchedComposition.valid_iff a
example : DispatchedPackage.Valid POS04DispatchedComposition.raw CSTTT.POS04.Assigned.canonical := POS04DispatchedComposition.positive
example : ¬ StageComposition.ScopeLink POS04DispatchedStage.raw.language POS04DispatchedStage.raw.stage
    POS04DispatchedStage.cover.scopes POS04DispatchedStage.cover.scopes := POS04DispatchedComposition.same_clause_scope_link_false
example : ¬ POS04DispatchedComposition.raw.clauses.accept
    (DispatchedPackage.global POS04DispatchedComposition.raw
      (CSTTT.POS04.Assigned.put CSTTT.POS04.Assigned.canonical .publishedC none)) := POS04DispatchedComposition.deleted_C_no_target_readout
def clauseName : ClauseDispatcher.Kind → String
  | .c1 => "c1" | .c2 => "c2" | .c3 => "c3" | .c4 => "c4"
  | .c5 => "c5" | .c6 => "c6" | .c7 => "c7" | .c8 => "c8"
#eval IO.println (Lean.Json.compress (Lean.Json.mkObj [
  ("increment", Lean.toJson StageCompositionModels.increment),
  ("multiplier", Lean.toJson StageCompositionModels.multiplier),
  ("positiveValue", Lean.toJson StageCompositionModels.positiveValue),
  ("indices", Lean.toJson cover.indices),
  ("falseScope", Lean.toJson (cover.scopes false).length),
  ("trueScope", Lean.toJson (cover.scopes true).length),
  ("falseArrow", Lean.toJson (first false ()).isSome),
  ("trueArrow", Lean.toJson (first true ()).isSome),
  ("adjacent", Lean.toJson (cover.adjacent false true)),
  ("shadowFalseScope", Lean.toJson (shadowCover.scopes false).length),
  ("output", Lean.toJson (output (fun _ => some StageCompositionModels.positiveValue))),
  ("shadow", Lean.toJson (shadowOutput (fun _ => some StageCompositionModels.positiveValue))),
  ("sourceMissing", Lean.toJson (output (fun _ => none))),
  ("posIndices", Lean.toJson (POS04DispatchedStage.cover.indices.map clauseName)),
  ("posSelectorC1", Lean.toJson
    (firstCover POS04DispatchedStage.cover.scopes (CSTTT.POS04.Assigned.Cell.rows .source)
      POS04DispatchedStage.cover.indices == some ClauseDispatcher.Kind.c1)),
  ("posRowPresent", Lean.toJson (mappedLocal POS04DispatchedComposition.raw.language CSTTT.POS04.Assigned.canonical
    POS04DispatchedComposition.raw.stage POS04DispatchedComposition.raw.cover.scopes .c2 (.rows .target)).isSome),
  ("posSameClauseRowPresent", Lean.toJson (mappedLocal
    (StageComposition.language POS04DispatchedStage.raw.language POS04DispatchedStage.raw.language) CSTTT.POS04.Assigned.canonical
    (StageComposition.stage POS04DispatchedStage.raw.language POS04DispatchedStage.raw.language
      POS04DispatchedStage.raw.stage POS04DispatchedStage.raw.stage POS04DispatchedStage.cover.scopes)
    POS04DispatchedStage.cover.scopes .c2 (.rows .target)).isSome) ]))
"""


def selected_output(model: dict, primitive: dict, shadow: bool = False):
    scopes = dict(model["prefix_scopes"])
    if shadow:
        scopes["false"] = model["shadow_control"]["false_scope"]
    for index in model["prefix_indices"]:
        key = str(index).lower()
        if "unit" in scopes[key]:
            if not model["prefix_arrows_present"][key]:
                return None
            return (primitive["positive_source_value"] + primitive["left_instruction"]["parameter"]) * primitive["right_instruction"]["parameter"]
    return None


def compare(model: dict, primitive: dict, observed: dict) -> None:
    shape = {"left_index_type": "Bool", "right_index_type": "Unit", "cell_type_each": "Unit", "value_type_each": "Nat"}
    if any(model[k] != v for k, v in shape.items()) or model["right_scope"] != ["unit"]:
        raise ValueError("typed index/cell/scope mismatch")
    expected = {"increment": primitive["left_instruction"]["parameter"],
        "multiplier": primitive["right_instruction"]["parameter"], "positiveValue": primitive["positive_source_value"],
        "indices": model["prefix_indices"], "falseScope": len(model["prefix_scopes"]["false"]),
        "trueScope": len(model["prefix_scopes"]["true"]), "falseArrow": model["prefix_arrows_present"]["false"],
        "trueArrow": model["prefix_arrows_present"]["true"], "adjacent": model["prefix_adjacency"],
        "shadowFalseScope": len(model["shadow_control"]["false_scope"]),
        "output": selected_output(model, primitive), "shadow": selected_output(model, primitive, True),
        "sourceMissing": None, "posIndices": model["POS04_pipeline"]["cover_indices"],
        "posSelectorC1": True, "posRowPresent": True, "posSameClauseRowPresent": False}
    if expected != observed:
        raise ValueError(f"raw selector/actual output mismatch: expected {expected}, observed {observed}")


def main() -> None:
    model = json.loads(MODEL.read_text())
    primitive = json.loads(MODEL.with_name(model["primitive_source"]).read_text())
    with tempfile.TemporaryDirectory(prefix="tth07-global-") as directory:
        path = Path(directory) / "Global.lean"
        path.write_text(PROBE)
        run = subprocess.run(["lake", "env", "lean", str(path)], cwd=ROOT / "lean", capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
        observed = json.loads(run.stdout.strip())
    compare(model, primitive, observed)
    for label in ("prefix ordering", "prefix scope", "selected arrow", "shadow scope"):
        drift = copy.deepcopy(model)
        if label == "prefix ordering": drift["prefix_indices"].reverse()
        elif label == "prefix scope": drift["prefix_scopes"]["false"] = ["unit"]
        elif label == "selected arrow": drift["prefix_arrows_present"]["false"] = True
        else: drift["shadow_control"]["false_scope"] = []
        try:
            compare(drift, primitive, observed)
        except ValueError:
            print(f"CAUGHT planted {label} drift")
        else:
            raise AssertionError(f"missed planted {label} drift")
    print("PASS cover-selected raw composition: typed index/cover/arrow data, actual outputs, no fallback; all-partial POS04 target/package adapters and direct controls kernel-checked")
    print("Scope: closed structural package pipeline at existing POS04 clause grades; full Temporal-FIACH composition remains open")


if __name__ == "__main__":
    main()
