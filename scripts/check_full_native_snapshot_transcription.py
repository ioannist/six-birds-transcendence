#!/usr/bin/env python3
"""Check every copied physical bit/program and actual simultaneous sibling row."""
from __future__ import annotations
from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def references():
    frozen = json.loads((ROOT / "audit/proposed_models/G17-full-native-package.model.json").read_text())
    states = list(product((False, True), repeat=5))
    matrix = frozen["primitive_dynamics"]["inside_maintenance_weights"]

    def row(s, action, flat=False):
        out, u, v, replica, phase = s
        if action:
            return [(tuple((True, u, v, replica, not phase)), 16)]
        weights = [2] * 4 if out or flat else matrix[2 * int(u) + int(v)]
        return [((False, x, y, r, not phase), weights[k])
                for k, (x, y) in enumerate(product((False, True), repeat=2)) for r in (False, True)]

    copied = []
    for flat in (False, True):
        for state in states:
            table = [[[list(s), n] for s, n in row(start, action, flat)]
                     for start in states for action in (False, True)]
            lenses = [1 + 2 * (2 * int(s[1]) + int(s[2])) + int(s[4]) if s[0] else 0
                      for s in states]
            copied.append([list(state), 1, 1, [list(state)], [0], False, table, lenses])
    root = (False, False, False, False, True)
    joint = []
    for a, b in product((False, True), repeat=2):
        joint.append([[list(s), list(t), n * m, True, True, 1, 1, 1, 2, 1, 1,
                       True, False, True, 1, True, 0]
                      for s, n in row(root, a) for t, m in row(root, b)])
    return copied, joint


def evaluate():
    folder = ROOT / "lean/.validate-logs"
    probe = folder / "G20SnapshotTranscriptionProbe.lean"
    probe.write_text("""import CSTTT.FullNative.SnapshotExecution
open CSTTT.FullNative CSTTT.FullNative.AccountExecution
open CSTTT.FullNative.PhysicalExecution CSTTT.FullNative.SnapshotExecution
def encode (s : State) : List Bool := [s.outside,s.u,s.v,s.replica,s.phase]
def sourceAt (flat : Bool) (s : State) : World :=
  let before : State := ⟨false,s.u,s.v,s.replica,!s.phase⟩
  let d := if flat then flatten model else model
  let p : Local := ⟨0,0,some d,before,[],([],[]),0⟩
  let n := if s.outside then 16 else if flat then 2 else weight before s.u s.v
  let x := advance renewable ⟨canonical,p⟩ s.outside s n
  {initialWorld with accounts := x.accounts,carriers := putOwner initialWorld.carriers 0 (some x.resident)}
def copyCase (flat : Bool) (s : State) : Lean.Json :=
  match writeSnapshot (sourceAt flat s) 1 with
  | none => Lean.Json.null
  | some w => match activate w 1 with
    | none => Lean.Json.null
    | some v => match v.carriers 1 with
      | none => Lean.Json.null
      | some p => match p.installed with
        | none => Lean.Json.null
        | some d => Lean.Json.arr #[Lean.toJson (encode p.current),Lean.toJson p.owner.val,
            Lean.toJson p.token.val,Lean.toJson (p.rootedRoute.1.map encode),
            Lean.toJson p.rootedRoute.2,Lean.toJson (v.slots 1).isSome,
            Lean.toJson (states.flatMap fun start => bits.map fun a =>
              (d.rows start a).map fun e => (encode e.1,e.2)),Lean.toJson (states.map d.publicLens)]
def jointCase (e : World × Nat) : Lean.Json :=
  let w := e.1
  match w.carriers 1,w.carriers 2 with
  | some p,some q => match p.receipts.head?,q.receipts.head? with
    | some r,some t => Lean.Json.arr #[Lean.toJson (encode p.current),Lean.toJson (encode q.current),
        Lean.toJson e.2,Lean.toJson (w.accounts.charge 1),Lean.toJson (w.accounts.charge 2),
        Lean.toJson (w.accounts.portCursor 1),Lean.toJson (w.accounts.portCursor 2),
        Lean.toJson r.serial,Lean.toJson t.serial,Lean.toJson p.receipts.length,Lean.toJson q.receipts.length,
        Lean.toJson (w.carriers 0).isNone,Lean.toJson w.bridge.isSome,Lean.toJson (w.accounts.charge 0),
        Lean.toJson (w.accounts.portCursor 0),Lean.toJson (w.accounts.charge 3),Lean.toJson (w.accounts.portCursor 3)]
    | _,_ => Lean.Json.null
  | _,_ => Lean.Json.null
def snapshot : Lean.Json := Lean.toJson
  (bits.flatMap (fun flat => states.map (copyCase flat)),
   bits.flatMap (fun a => bits.map fun b => (jointRows renewable autonomousSiblings a b).map jointCase))
#eval snapshot.compress
""")
    result = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean",
                            capture_output=True, text=True, check=True)
    (folder / "G20SnapshotTranscriptionProbe.log").write_text(result.stdout + result.stderr)
    values = json.loads(json.loads(result.stdout.strip()))
    return values[0], values[1]


def compare(actual, reference):
    if actual != reference:
        raise AssertionError("snapshot consumer or simultaneous sibling readouts differ from frozen recipe")


def main():
    actual, reference = evaluate(), references()
    compare(actual, reference)
    print("PASS snapshot transcription: all32 physical inputs, canonical+flatten programs; all4096 copied action rows")
    print("PASS joint transcription: 4 action pairs, 81 actual jointly funded outcomes after withdrawal")
    for label, mutation in [
        ("phase copy", lambda x: x[0][0][0].__setitem__(4, True)),
        ("program copy", lambda x: x[0][0][6][0][0].__setitem__(1, 2)),
        ("public lens copy", lambda x: x[0][0][7].__setitem__(0, 1)),
        ("token alias", lambda x: x[1][0][0].__setitem__(6, 0)),
        ("source reactivation", lambda x: x[1][0][0].__setitem__(11, False)),
    ]:
        broken = deepcopy(reference)
        mutation(broken)
        try:
            compare(actual, broken)
        except AssertionError:
            print("CAUGHT planted " + label + " drift")
        else:
            raise AssertionError("missed planted " + label + " drift")


if __name__ == "__main__":
    main()
