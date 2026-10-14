#!/usr/bin/env python3
"""Check the named fork against actual raw native execution and kernel probes."""
import copy
import itertools
import json
from pathlib import Path
import subprocess
import tempfile

from check_native_publication_composition_transcription import PROBE as PARENT_PROBE

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "audit/proposed_models/TTH08-NATIVE-FISSION.model.json"
PROBE = "import CSTTT.Targets.GenericHandoff.NativeComposition.FissionControls\n" + PARENT_PROBE.rsplit("#eval IO.println", 1)[0] + r'''
namespace FissionProbe
example (r : NativeComposition.NativeFission.Raw) : NativeComposition.NativeFission.decoded r=some (NativeComposition.NativeFission.assignment r) ↔ NativeComposition.NativeFission.Ready r := NativeComposition.NativeFission.decoded_iff r
example (branch : Bool) (h : Factor) : FullHandoffCertificate (NativeComposition.NativeFission.summary NativeComposition.NativeFission.canonicalRaw NativeComposition.NativeFission.canonical_ready branch h) :=
 NativeComposition.NativeFission.canonical_certificate branch h
example (r : NativeComposition.NativeFission.Raw) : ¬NativeComposition.NativeFission.InvariantSingleton r := NativeComposition.NativeFission.no_invariant_singleton r
example (branch : Bool) : ¬NativeComposition.NativeFission.Readout (NativeComposition.NativeFission.cutRaw branch) := NativeComposition.NativeFission.cut_raw_no_readout branch
example (branch : Bool) : ¬NativeComposition.NativeFission.Readout (NativeComposition.NativeFission.missingRaw branch) := NativeComposition.NativeFission.missing_raw_no_readout branch
example : ¬NativeComposition.NativeFission.Readout NativeComposition.NativeFission.brokenCreditRaw := NativeComposition.NativeFission.broken_credit_no_readout
example : ¬NativeComposition.NativeFission.Readout NativeComposition.NativeFission.brokenJointRaw := NativeComposition.NativeFission.broken_joint_no_readout
example : ∃ selected : Fin 3,
 CSTTT.CorridorTheory.FissionClosure.oldFork.related () selected ∧
 CSTTT.CorridorTheory.FissionClosure.oldFork.valid selected ∧
 CSTTT.CorridorTheory.FissionClosure.oldFork.swap selected=selected :=
 CSTTT.CorridorTheory.FissionClosure.old_certificate_allows_an_invariant_continuer
def observed (branch : Bool) (h : Factor) : Lean.Json :=
 let a := PublicationExecution.nativeAssignment
 let actual := execute true a h
 let mappedLeg := do
   let rs ← actual
   let l ← legFromRuns true a (rs.1.1.residue.1.map PublicationCorridor.seedName) rs
   pure (NativeComposition.NativeFission.renameLeg branch l)
 Lean.Json.mkObj [
 ("branch",Lean.toJson branch),("factor",Lean.toJson [h.1,h.2.1,h.2.2]),
 ("physicalOwners",Lean.toJson (actual.map (fun rs => (listRuns rs).map (fun x =>
   ((NativeComposition.NativeFission.resourceOwnerExpr branch).eval a (ModeExecution.pack x) ()).map (fun c => c.code))))),
 ("futureOwners",Lean.toJson (actual.map (fun rs => (listRuns rs).map (fun x =>
   (NativeComposition.NativeFission.targetRaw branch).readouts.owner.eval NativePackageBundle.canonical (Frame.pack x.1) () |>.map (fun c => c.code))))),
 ("accountOwners",Lean.toJson (actual.map (fun rs => (listRuns rs).map (fun x =>
   ((NativeComposition.NativeFission.namedRuntime branch).accounts.eval a (ModeExecution.pack x) ()).bind
     (fun accounts => (accounts true).owner.map (fun c => c.code)))))),
 ("chargeOwners",Lean.toJson (actual.map (fun rs => (listRuns rs).map (fun x =>
   ((NativeComposition.NativeFission.namedRuntime branch).charge.eval a (ModeExecution.pack x) ((),false)).map (fun c => c.owner.code))))),
 ("sourcePast",Lean.toJson (actual.map (fun rs => rs.1.1.residue.1.map (fun h => [h.1,h.2.1,h.2.2])))),
 ("targetPast",Lean.toJson (actual.map (fun rs => rs.2.2.2.1.residue.1.map (fun h => [h.1,h.2.1,h.2.2])))),
 ("legOwners",Lean.toJson (mappedLeg.map (fun l => l.stages.map (fun s => s.frontier.owner)))),
 ("legSupports",Lean.toJson (mappedLeg.map (fun l => l.stages.map (fun s => s.support)))),
 ("eventOwners",Lean.toJson (mappedLeg.map (fun l => l.events.map (fun e => e.owner)))),
 ("updateOwners",Lean.toJson (mappedLeg.map (fun l => l.updates.map (fun u => u.nextOwner)))),
 ("legPass",Lean.toJson (mappedLeg.map AtomicLegCheck)),
 ("sourceNames",Lean.toJson ([false,true].map (fun o => (names true o).code))),
 ("targetNames",Lean.toJson ([false,true].map (fun o => (NativeComposition.NativeFission.branchNames branch o).code)))]
#eval IO.println (Lean.Json.compress (Lean.Json.arr ([false,true].flatMap (fun b => factors.map (observed b))).toArray))
end FissionProbe
'''


def compare(model, observed):
    source = model["source_carrier"]
    reference = model["reference_target"]
    expected = []
    for branch, target in zip((False, True), model["target_carriers"], strict=True):
        for factor in itertools.product((False, True), repeat=3):
            expected.append({"branch": branch, "factor": list(factor),
                             "physicalOwners": [source, source, target, target],
                             "futureOwners": [target] * 4,
                             "accountOwners": [source, source, target, target],
                             "chargeOwners": [source, source, target, target],
                             "sourcePast": [list(factor)] * 2, "targetPast": [list(factor)] * 4,
                             "legOwners": [source, source, target],
                             "legSupports": [[source], [source, target], [target]],
                             "eventOwners": [source, source, target, target],
                             "updateOwners": [source, target], "legPass": True,
                             "sourceNames": [source, reference], "targetNames": [source, target]})
    if expected != observed:
        raise ValueError("named raw fork execution/owner/corridor transcription drift")
    if model["branch_coordinate"] != "Bool" or model["recognition_status"] != "notAddressed":
        raise ValueError("fork scope transcription drift")


def main():
    with tempfile.TemporaryDirectory(prefix="native-fission-") as directory:
        probe = Path(directory) / "Probe.lean"
        probe.write_text(PROBE)
        run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean", capture_output=True, text=True)
        if run.returncode:
            raise RuntimeError(run.stdout + run.stderr)
        observed = json.loads(run.stdout.strip().splitlines()[-1])
    model = json.loads(MODEL.read_text())
    compare(model, observed)
    mutations = [
        ("source", lambda m: m.__setitem__("source_carrier", 18)),
        ("shared source namespace", lambda m: m.__setitem__("reference_target", 201)),
        ("left target", lambda m: m["target_carriers"].__setitem__(0, 55)),
        ("right target", lambda m: m["target_carriers"].__setitem__(1, 201)),
        ("branch order", lambda m: m["target_carriers"].reverse()),
        ("branch coordinate", lambda m: m.__setitem__("branch_coordinate", "Unit")),
        ("recognition", lambda m: m.__setitem__("recognition_status", "addressed")),
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
    print("PASS all16 raw branch episodes, owner expressions, full past, corridor/support/event/update coordinates; full certificates and actual-readout control kernel probes; seven planted drifts")


if __name__ == "__main__":
    main()
