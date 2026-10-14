#!/usr/bin/env python3
"""Check raw repaired publication instructions and semantic composition probes."""
import copy
import itertools
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "audit/proposed_models/TTH07-NATIVE-PUBLICATION-COMPOSITION.model.json"
PROBE = r'''
import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationReturn
open CSTTT.TargetTheory CSTTT.TargetTheory.GenericHandoff
open NativeComposition RegisterInterpreter RegisterInitialization PublicationReplay
open CSTTT.CorridorTheory.AtomicChain
example : PublicationComposition.Readout NativePackageBundle.canonical := PublicationComposition.canonical_readout
example (h : Factor) : Nonempty (FullHandoffCertificate (composeFullHandoffData
 (PublicationReturn.summary NativePackageBundle.canonical PublicationComposition.canonical_ready true h)
 (PublicationReturn.summary NativePackageBundle.canonical PublicationComposition.canonical_ready false h))) :=
 PublicationReturn.native_full_temporal_composition h
example (a : Assignment Owner NativePackageBundle.Value) (cell : Owner) :
 ¬ PublicationComposition.Readout (PublicationComposition.cutReceiver cell a) := PublicationComposition.cut_receiver_no_readout cell a
example (a : Assignment Owner NativePackageBundle.Value) (hm : a false=none) :
 ¬ PublicationComposition.Readout (PublicationMaps.exposure a) := PublicationComposition.exposed_missing a hm
example (cell o : Owner) (a : Assignment Owner NativePackageBundle.Value) :
 (PublicationComposition.cutReceiver cell a o).map Prod.snd=(a o).map Prod.snd := PublicationComposition.cut_receiver_copied_source cell o a
abbrev Run := ModeExecution.State
abbrev Assign := Assignment Owner MemoryValue
def fold (cell : Owner) (a : Assign) : Run → List (Unit × Bool × Factor) → Option Run
 | x, [] => some x
 | x, (d,act,o)::rest =>
   if SupportedAcquisitionSequence.stepCheck (raw cell) a (ModeExecution.pack x) d act o then do
     let next ← ((raw cell).execution.program ()).eval a (ModeExecution.pack x) (d,act,o)
     fold cell a next rest
   else none
def execute (cell : Owner) (a : Assign) (h : Factor) : Option (Run × Run × Run × Run) := do
 let p ← a cell
 if PublicationReceiver.active cell p then
   let routes ← (raw cell).routes.read a
   let path := (routes h).path
   if PublicationCorridor.recipeGuard cell p path then
     let first ← path.head?
     let last ← path.getLast?
     if PublicationCorridor.eventGuard cell p first last then
       let hs ← (raw cell).histories.read a
       let initialized ← ((raw cell).initializer ()).eval a noRegisters (routes h).history
       let terminal ← fold cell a initialized (hs (routes h).history)
       let arrived ← ((raw cell).receive ()).eval a (ModeExecution.pack terminal) ((routes h).history,h)
       let da ← (raw cell).arrivalResponse.eval a (ModeExecution.pack arrived) ((routes h).history,h)
       if SupportedAcquisitionSequence.stepCheck (raw cell) a (ModeExecution.pack arrived) da.1 da.2 h then
         let exited ← ((raw cell).execution.program ()).eval a (ModeExecution.pack arrived) (da.1,da.2,h)
         pure (initialized,terminal,arrived,exited)
       else none
     else none
   else none
 else none
def listRuns (p : Run × Run × Run × Run) : List Run := [p.1,p.2.1,p.2.2.1,p.2.2.2]
def runData (cell : Owner) (a : Assign) (x : Run) : Lean.Json := Lean.Json.mkObj [
 ("factor",Lean.toJson [x.1.factor.1,x.1.factor.2.1,x.1.factor.2.2]),
 ("time",Lean.toJson x.1.counter),("ticks",Lean.toJson x.1.ticks),
 ("past",Lean.toJson (x.1.residue.1.map (fun h => [h.1,h.2.1,h.2.2]))),
 ("path",Lean.toJson x.1.residue.2),("funded",Lean.toJson x.1.funded),("mode",Lean.toJson x.2),
 ("owner",Lean.toJson (((PublicationPhysical.ownerExpr cell).eval a (ModeExecution.pack x) ()).map (fun c => c.code))),
 ("sourcePresent",Lean.toJson ((PublicationResources.runtime cell).sourcePresent.eval a (ModeExecution.pack x) ())),
 ("record",Lean.toJson ((PublicationResources.runtime cell).record.eval a (ModeExecution.pack x) ()))]
def legFromRuns (cell : Owner) (a : Assign) (seed : List String)
    (rs : Run × Run × Run × Run) : Option FiniteAtomicLeg := do
 let p ← a cell
 let f0 ← PublicationCorridor.frontier cell a (ModeExecution.pack rs.1) seed
 let f1 ← PublicationCorridor.frontier cell a (ModeExecution.pack rs.2.1) (seed++[PublicationCorridor.eventName cell false])
 let f2 ← PublicationCorridor.frontier cell a (ModeExecution.pack rs.2.2.2)
   (seed++[PublicationCorridor.eventName cell false,PublicationCorridor.eventName cell true])
 pure (PublicationCorridor.construct cell p (ModeExecution.pack rs.1) (ModeExecution.pack rs.2.1)
   (ModeExecution.pack rs.2.2.2) false true f0 f1 f2)
def observed (h : Factor) : Lean.Json :=
 let a := PublicationExecution.nativeAssignment
 let first := execute true a h
 let second := execute false a h
 let legs := do
   let leftRuns ← first
   let rightRuns ← second
   if leftRuns.2.2.2=rightRuns.1 then
     let left ← legFromRuns true a (leftRuns.1.1.residue.1.map PublicationCorridor.seedName) leftRuns
     let right ← legFromRuns false a (exit left).frontier.residue rightRuns
     pure [left,right]
   else none
 Lean.Json.mkObj [
 ("factor",Lean.toJson [h.1,h.2.1,h.2.2]),
 ("runs",Lean.Json.arr #[(first.map (fun r => Lean.Json.arr ((listRuns r).map (runData true a)).toArray)).getD Lean.Json.null,
   (second.map (fun r => Lean.Json.arr ((listRuns r).map (runData false a)).toArray)).getD Lean.Json.null]),
 ("legChecks",Lean.toJson (legs.map (fun ls => ls.map AtomicLegCheck))),
 ("seam",Lean.toJson (legs.bind (fun ls => do
   let left ← ls.head?
   let right ← ls.getLast?
   pure (AdjacentFrontierCheck left right)))),
 ("lastLog",Lean.toJson (legs.bind (fun ls => ls.getLast?.map (fun l => (exit l).frontier.residue)))),
 ("sourceCuts",Lean.toJson ([true,false].map (fun cell => (execute cell (PublicationReceiver.cutAt cell a) h).isSome))),
 ("flagCuts",Lean.toJson ([true,false].flatMap (fun atomic => [true,false].map (fun cell =>
   (execute cell (PublicationCorridor.eraseFlagAt atomic cell a) h).isSome)))),
 ("probeRow",Lean.toJson (((raw true).execution.row.eval a
   (PublicationExecution.snapshot h 2 0 false) ((),true)).map (fun rs => rs.map (fun e => ([e.1.1,e.1.2.1,e.1.2.2],[e.2.num,e.2.den])))))]
#eval IO.println (Lean.Json.compress (Lean.Json.arr (factors.map observed).toArray))
'''


def compare(model, observed):
    factors = list(itertools.product((False, True), repeat=model["factor_bits"]))
    expected = []
    for h in factors:
        legs = []
        for i in range(2):
            runs = []
            for j in range(4):
                time = model["physical_times"][i][j]
                runs.append({"factor": list(h), "time": time, "ticks": time,
                             "past": [list(h)] * model["history_copies"][i][j],
                             "path": model["stored_path"], "funded": True,
                             "mode": model["modes"][i][j],
                             "owner": model["physical_owners"][i][j],
                             "sourcePresent": model["source_presence"][i][j], "record": time})
            legs.append(runs)
        seed = "past-" + "".join("1" if bit else "0" for bit in h)
        destination = [not h[0], h[1], h[2]]
        expected.append({"factor": list(h), "runs": legs, "legChecks": [True, True], "seam": True,
                         "lastLog": [seed, seed] + model["executed_event_names"],
                         "sourceCuts": [False, False], "flagCuts": [False] * 4,
                         "probeRow": [[destination, [1, 1]]] if h[1] else []})
    if expected != observed:
        raise ValueError("raw publication/runtime/corridor transcription drift")
    if model["controller"] != "same constant false history strategy at middle and final":
        raise ValueError("controller transcription drift")


def main():
    with tempfile.TemporaryDirectory(prefix="native-publication-composition-") as directory:
        probe = Path(directory) / "Probe.lean"
        probe.write_text(PROBE)
        run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean", capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
        observed = json.loads(run.stdout.strip().splitlines()[-1])
    model = json.loads(MODEL.read_text())
    compare(model, observed)
    mutations = [
        ("physical clock", lambda m: m["physical_times"][1].__setitem__(1, 4)),
        ("owner", lambda m: m["physical_owners"][1].__setitem__(2, 55)),
        ("full incoming past", lambda m: m["history_copies"][1].__setitem__(2, 4)),
        ("runtime source presence", lambda m: m["source_presence"][0].__setitem__(2, True)),
        ("event log", lambda m: m["executed_event_names"].__setitem__(2, "first-source")),
        ("stored path", lambda m: m.__setitem__("stored_path", [False])),
        ("controller", lambda m: m.__setitem__("controller", "true")),
    ]
    for label, mutate in mutations:
        changed = copy.deepcopy(model)
        mutate(changed)
        try:
            compare(changed, observed)
        except ValueError:
            print(f"CAUGHT planted {label} drift")
        else:
            raise AssertionError(f"missed planted {label} drift")
    print("PASS all8 raw repaired episodes, physical/memory/owner/presence seams, actual corridor checks and source/event cuts; full readout/certificate kernel probes; seven planted drifts")


if __name__ == "__main__":
    main()
