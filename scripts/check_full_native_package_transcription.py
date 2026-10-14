#!/usr/bin/env python3
"""G27 shared-world readouts; finite transcription supplements universal Lean proofs.

Reconstruct the actual source/copy/two-cycle account and receipt chain from the
G17 frozen rows. Reuse G21's independent rational matrix construction for C1.
No finite check purports to enumerate arbitrary histories or invariant sets.
"""
from __future__ import annotations

from copy import deepcopy
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import subprocess

from check_full_native_objecthood_transcription import expected as objecthood_reference

ROOT = Path(__file__).resolve().parents[1]
BITS = (False, True)
STATES = list(product(BITS, repeat=5))
ROOT_STATE = (False,) * 5


def reference():
    frozen = json.loads((ROOT / "audit/proposed_models/G17-full-native-package.model.json").read_text())
    weights = frozen["primitive_dynamics"]["inside_maintenance_weights"]

    def rows(s, a):
        out, u, v, replica, phase = s
        if a:
            return [((True, u, v, replica, not phase), 16)]
        ws = [2] * 4 if out else weights[2 * int(u) + int(v)]
        return [((False, x, y, r, not phase), ws[k])
                for k, (x, y) in enumerate(product(BITS, repeat=2)) for r in BITS]

    def probability(s, t):
        return sum((F(n, 16) for q, n in rows(s, False) if q == t), F(0))

    def advance(x, a, target, weight, renew=True):
        y = deepcopy(x)
        o = x["owner"]
        serial = 4 * x["cursor"][o] + o
        y["receipts"].insert(0, [o, o, serial, list(x["state"]), list(target), a, weight, renew])
        y["state"] = target
        y["cursor"][o] += 1
        y["charge"][o] = renew
        return y

    def verdict(x):
        rs = x["receipts"]
        if not x["installed"] or not rs or rs[0][4] != rs[-1][3]:
            return "rejected"
        if any(r[3] != s[4] for r, s in zip(rs, rs[1:])):
            return "rejected"
        if any(r[5] or not r[7] or x["allocation"][r[1]] != r[0] or
               (tuple(r[4]), r[6]) not in rows(tuple(r[3]), False) for r in rs):
            return "rejected"
        forward = reverse = F(1)
        for r in rs:
            forward *= probability(tuple(r[3]), tuple(r[4]))
            reverse *= probability(tuple(r[4]), tuple(r[3]))
        if forward == reverse:
            return "neutral"
        return "self" if all(r[0] == x["owner"] for r in rs) else "other"

    def encode(x):
        s = x["state"]
        count = len(x["receipts"])
        code = 8 * int(s[0]) + 4 * int(s[1]) + 2 * int(s[2]) + int(s[4])
        return [list(s), x["owner"], x["owner"], count, count, x["roots"], x["serials"],
                x["cursor"], x["charge"], x["allocation"], x["installed"], x["receipts"],
                verdict(x), [0 if not s[0] else 1 + 4 * int(s[1]) + 2 * int(s[2]) + int(s[4]),
                             16 if x["installed"] and x["charge"][x["owner"]] and
                             x["allocation"][x["owner"]] == x["owner"] else 0,
                             16 if x["installed"] and x["charge"][x["owner"]] and
                             x["allocation"][x["owner"]] == x["owner"] else 0],
                code, [probability(s, t) if x["installed"] and x["charge"][x["owner"]] and
                        x["allocation"][x["owner"]] == x["owner"] else F(0) for t in STATES]]

    cycle = [ROOT_STATE, (False, False, True, False, True),
             (False, True, True, False, False), (False, False, False, False, True),
             (False, False, True, False, False), (False, True, True, False, True)]
    plan = cycle[1:] + cycle[:1]

    def run(x):
        for t in plan:
            n = next(n for s, n in rows(x["state"], False) if s == t)
            x = advance(x, False, t, n)
        return x

    source = run(dict(state=ROOT_STATE, owner=0, cursor=[0]*4, charge=[True]*4,
                      allocation=[0, None, None, 3], receipts=[], roots=[], serials=[], installed=True))
    targets = [dict(state=source["state"], owner=o, cursor=source["cursor"][:],
                    charge=[True]*4, allocation=[0, 1, 2, 3], receipts=[], roots=[list(source["state"])],
                    serials=[source["receipts"][0][2]], installed=True) for o in (1, 2)]
    first = run(targets[0])
    targets[1]["cursor"] = first["cursor"][:]
    second = run(targets[1])
    first["cursor"] = second["cursor"][:]
    endpoints = [source, first, second]
    entries = []
    for x in endpoints:
        entries.append([encode(x), [[ [encode(advance(x, a, t, n)), n] for t, n in rows(x["state"], a)]
                                   for a in BITS]])
    absent = []
    returns = []
    for x in endpoints:
        t, n = rows(x["state"], False)[0]
        y = advance(x, False, t, n, False)
        absent.append([encode(y), [0, 0]])
        y = deepcopy(x)
        for _ in range(2):
            t = (*y["state"][:4], not y["state"][4])
            y = advance(y, False, t, next(n for s, n in rows(y["state"], False) if s == t))
        returns.append(encode(y))
    # Separate ablations of the actual source; each loses the native row gate.
    ablations = []
    for kind in ("program", "account", "charge"):
        x = deepcopy(source)
        if kind == "program": x["installed"] = False
        if kind == "account": x["allocation"][0] = None
        if kind == "charge": x["charge"][0] = False
        ablations.append([encode(x), [0, 0]])
    oh = objecthood_reference()
    c1 = [oh[6], oh[8], oh[9], oh[10], oh[11], oh[12]]
    controls = ["other", "rejected", "neutral", "rejected", [0, 0, 0, 0], 8,
                [F(1, 10), F(1, 100)], [1, 0]]
    return [entries, absent, returns, ablations, [None, None], c1, controls]


PROBE = r"""
import Lean
import CSTTT.FullNative.OriginalPackage
open CSTTT CSTTT.FullNative AccountExecution PhysicalExecution SnapshotExecution SharedPackage OriginalPackage
set_option maxRecDepth 8192
set_option maxHeartbeats 16000000
def encode (s : State) : List Bool := [s.outside,s.u,s.v,s.replica,s.phase]
def rat (x : Rat) : Lean.Json := Lean.toJson (toString x)
def label : Credit.CreditVerdict → String
  | .self => "self" | .other => "other" | .neutral => "neutral" | .rejected => "rejected"
def issuer : Actor → Nat | .localGenerator o => o.val | .bridge => 3
def receipt (r : Receipt) : Lean.Json := Lean.Json.arr #[
  Lean.toJson (issuer r.issuer),Lean.toJson r.token.val,Lean.toJson r.serial,
  Lean.toJson (encode r.before),Lean.toJson (encode r.after),Lean.toJson r.action,
  Lean.toJson r.weight,Lean.toJson r.energy.isSome]
def data (x : Execution) : Lean.Json := Lean.Json.arr #[
  Lean.toJson (encode x.resident.current),Lean.toJson x.resident.owner.val,Lean.toJson x.resident.token.val,
  Lean.toJson (frame x).context.order,Lean.toJson (frame x).context.localRecords,
  Lean.toJson (x.resident.rootedRoute.1.map encode),Lean.toJson x.resident.rootedRoute.2,
  Lean.toJson ((List.finRange 4).map x.accounts.portCursor),Lean.toJson ((List.finRange 4).map x.accounts.charge),
  Lean.toJson ((List.finRange 4).map fun t => (x.accounts.allocation t).map issuer),
  Lean.toJson x.resident.installed.isSome,Lean.toJson (x.resident.receipts.map receipt),
  Lean.toJson (label (credit x)),Lean.toJson [(Binding.actualCurrent x).1,
    (Binding.actualCurrent x).2.1,(Binding.actualCurrent x).2.2],
  Lean.toJson (classes model x.resident.current),Lean.toJson (states.map fun t => rat (Objecthood.actualP x t))]
def endpoints : List Execution := [TemporalTransport.sourceAtCopy,targetExecution false,targetExecution true]
def endpoint (x : Execution) : Lean.Json := Lean.Json.arr #[data x,
  Lean.toJson (bits.map fun a => (rawRows renewable x a).map fun e => Lean.Json.arr #[data e.1,Lean.toJson e.2])]
def absent (x : Execution) : Lean.Json :=
  let y := advance absentSupply x false FullInterface.replicaLeft 1
  Lean.Json.arr #[data y,Lean.toJson (bits.map fun a => (rawRows absentSupply y a).length)]
def missingProgram : Execution := {TemporalTransport.sourceAtCopy with resident :=
  {TemporalTransport.sourceAtCopy.resident with installed:=none}}
def missingAccount : Execution := {TemporalTransport.sourceAtCopy with accounts :=
  {TemporalTransport.sourceAtCopy.accounts with allocation:=put TemporalTransport.sourceAtCopy.accounts.allocation 0 none}}
def depleted : Execution := {TemporalTransport.sourceAtCopy with accounts := debit TemporalTransport.sourceAtCopy.accounts 0}
def missingResident : Raw := ⟨Credit.creditedBothWorld,0⟩
def wrongOwner : Raw := ⟨{sourceRaw.world with carriers:=putOwner sourceRaw.world.carriers 0 (some {TemporalTransport.sourceAtCopy.resident with owner:=1})},0⟩
def value (p t : Bool) : State → State → Rat := if t then Objecthood.two p else Objecthood.perturbed p
def vector (v : State → Rat) : Lean.Json := Lean.toJson (states.map fun s => rat (v s))
def matrix (m : State → State → Rat) : Lean.Json := Lean.toJson (states.map fun s => states.map fun t => rat (m s t))
def squaredValue (p t : Bool) : State → State → Rat := if t then Objecthood.four p else Objecthood.two p
def defect (p t : Bool) : Rat := (states.map fun s =>
  ((states.map fun k => Objecthood.absRat (squaredValue p t s k-value p t s k)).sum)/2).foldl max 0
namespace Legacy
open CSTTT.TargetTheory.GenericHandoff.NativeComposition
  CSTTT.TargetTheory.GenericHandoff.NativeComposition.CoupledNativeKernelPrototype
  CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOriginalInterfacePrototype
def oldClasses := kernelStates.map (CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOriginalInterfacePrototype.classes (input false))
def mass : Rat := ((CSTTT.TargetTheory.GenericHandoff.TemporalFactorRules.actualRows (factorSchema false)
  (input false).temporal (context (embed (false,false)) 0 0 ([],[]) true) false).map Prod.snd).sum
end Legacy
def conditionalControls : List (Option Lean.Json) := [
  (JointClaims.conditionedJoint [] [JointClaims.correlatedObservation false]).map rat,
  do let l ← JointClaims.conditionedBranch false [] [(JointClaims.correlatedObservation false).1]
     let r ← JointClaims.conditionedBranch true [] [(JointClaims.correlatedObservation false).2]
     pure (rat (l*r))]
def snapshot : Lean.Json := Lean.Json.arr #[
  Lean.toJson (endpoints.map endpoint),Lean.toJson (endpoints.map absent),
  Lean.toJson (endpoints.map fun x => data (ClockClosure.secondReturn x)),
  Lean.toJson ([missingProgram,missingAccount,depleted].map fun x => Lean.Json.arr #[data x,
    Lean.toJson (bits.map fun a => (rawRows renewable x a).length)]),
  Lean.toJson ([missingResident,wrongOwner].map fun p => (execution p).map data),
  Lean.Json.arr #[Lean.toJson (bits.flatMap fun p => bits.map fun t => matrix (value p t)),
    Lean.toJson (bits.map fun p => vector (Objecthood.stationary p)),
    Lean.toJson (bits.map fun p => rat (CSTTT.TargetTheory.GenericHandoff.FixedPointVerifier.mass Objecthood.core (Objecthood.stationary p))),
    Lean.toJson (bits.map fun p => rat (Objecthood.stationaryTV p)),
    Lean.toJson (bits.flatMap fun p => bits.map fun t => rat (defect p t)),
    Lean.toJson (bits.map fun p => vector (Objecthood.phaseLaw p))],
  Lean.Json.arr #[Lean.toJson ((Credit.bridgeCredit Credit.scheduledCycleWorld 1).map label),
    Lean.toJson ((Credit.localCredit Credit.scheduledCycleWorld 1).map label),
    Lean.toJson ((Credit.localCredit Credit.flatCycleWorld 0).map label),
    Lean.toJson ((Credit.localCredit Credit.mixedCycleWorld 1).map label),Lean.toJson Legacy.oldClasses,
    rat Legacy.mass,Lean.toJson conditionalControls,
    Lean.toJson [rat (Binding.emittedLaw (normalizedRows renewable) (fun y => Binding.joint y.resident.current)
      TemporalTransport.sourceAtCopy [] []),rat (WeightedFuture.law (normalizedRows renewable)
      (fun y => FullInterface.observe (frame y)) TemporalTransport.sourceAtCopy [] [])]]]
#eval snapshot.compress
"""


def evaluate():
    folder = ROOT / "lean/.validate-logs"
    folder.mkdir(exist_ok=True)
    probe = folder / "G27PackageTranscriptionProbe.lean"
    probe.write_text(PROBE)
    run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean",
                         capture_output=True, text=True)
    (folder / "G27-package-transcription-probe.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise RuntimeError("Lean transcription failed; see G27-package-transcription-probe.log")

    def decode(value):
        if isinstance(value, str):
            return value if value in {"self", "other", "neutral", "rejected"} else F(value)
        if isinstance(value, list):
            return [decode(v) for v in value]
        return value
    return decode(json.loads(json.loads(run.stdout.strip())))


def main():
    actual, expected = evaluate(), reference()
    assert actual == expected, "G27 shared raw execution/receipt/operator/control drift"
    print("G27 transcription passed: 3 actual endpoints, 27 native successors, 4 C1 closure cases,")
    print("3 stored-charge stops, 3 logged return traces, 5 missing-input/address controls; old negatives retained.")


if __name__ == "__main__":
    main()
