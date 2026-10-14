#!/usr/bin/env python3
"""Independently reconstruct emitted laws and actual historical split readouts."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as F
from itertools import product
from functools import lru_cache
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def references():
    frozen = json.loads((ROOT / "audit/proposed_models/G17-full-native-package.model.json").read_text())
    states = list(product((False, True), repeat=5))
    matrix = frozen["primitive_dynamics"]["inside_maintenance_weights"]
    cases = [(w, o) for n in range(3) for w in product((False, True), repeat=n)
             for o in product(range(4), repeat=n)]

    def rows(s, a, flat):
        out, u, v, replica, phase = s
        if a:
            return [((True, u, v, replica, not phase), 16)]
        weights = [2]*4 if flat or out else matrix[2*int(u)+int(v)]
        return [((False, x, y, r, not phase), weights[k])
                for k, (x, y) in enumerate(product((False, True), repeat=2))
                for r in (False, True)]

    def observe(s, channel):
        if s[0]:
            return 0
        return int(s[1]) if channel == 0 else int(s[2]) if channel == 1 else 2*int(s[1])+int(s[2])

    @lru_cache(None)
    def law(s, flat, channel, word, output):
        if not word:
            return F(1 if not output else 0)
        if not output:
            return F(0)
        return sum((F(n, 16)*law(t, flat, channel, word[1:], output[1:])
                    for t, n in rows(s, word[0], flat) if observe(t, channel)==output[0]), F(0))

    physical = [[[[law(s, flat, channel, w, o) for w, o in cases]
                   for channel in range(3)] for s in states] for flat in (False, True)]
    actual = []
    contexts = []
    for owner in range(3):
        for right in (False, True):
            s = (False, False, right, False, owner==0)
            actual.append([[ [law(s, flat, channel, w, o) for w, o in cases]
                            for channel in range(3)] for flat in (False, True)])
            contexts.append([list(s), 2*int(right)+int(s[4]), [0,16,16], 1,1,
                             [] if owner==0 else [[False,False,False,False,True]],
                             [] if owner==0 else [0], True,owner,owner,1])
    return physical, actual, contexts


def evaluate():
    folder = ROOT / "lean/.validate-logs"
    probe = folder / "G22BindingTranscriptionProbe.lean"
    probe.write_text("""import CSTTT.FullNative.HistoryFactor
open CSTTT.FullNative CSTTT.FullNative.Binding
open CSTTT.FullNative.PhysicalExecution CSTTT.FullNative.SnapshotExecution
open CSTTT.FullNative.AccountExecution
def rat (x : Rat) : Lean.Json := Lean.toJson (toString x)
def encode (s : State) : List Bool := [s.outside,s.u,s.v,s.replica,s.phase]
def lawCases : List (List Bool × List Nat) :=
  [([],[])] ++ (bits.flatMap fun a => (List.range 4).map fun o => ([a],[o])) ++
  (bits.flatMap fun a => bits.flatMap fun b => (List.range 4).flatMap fun o =>
    (List.range 4).map fun p => ([a,b],[o,p]))
def channel (c : Nat) : State → Nat := if c=0 then branch false else if c=1 then branch true else joint
def physicalCase (flat : Bool) (s : State) : Lean.Json := Lean.toJson
  ((List.range 3).map fun c => lawCases.map fun z =>
    rat (emittedLaw (rationalRows (if flat then flatten model else model)) (channel c) s z.1 z.2))
def actualInputs : List Execution :=
  [splitExecution source false,splitExecution source true,
   splitExecution ⟨autonomousSiblings.accounts,activatedLocal 1⟩ false,
   splitExecution ⟨autonomousSiblings.accounts,activatedLocal 1⟩ true,
   splitExecution ⟨autonomousSiblings.accounts,activatedLocal 2⟩ false,
   splitExecution ⟨autonomousSiblings.accounts,activatedLocal 2⟩ true]
def actualCase (x : Execution) : Lean.Json := Lean.toJson
  (bits.map fun flat => (List.range 3).map fun c => lawCases.map fun z =>
    let y := if flat then {x with resident := {x.resident with installed := some (flatten model)}} else x
    rat (emittedLaw (normalizedRows renewable) (fun y => channel c y.resident.current) y z.1 z.2))
def contextCase (x : Execution) : Lean.Json :=
  let c := (frame x).context
  Lean.Json.arr #[Lean.toJson (encode x.resident.current),Lean.toJson (FullInterface.code (frame x)).1,
    Lean.toJson [ (actualCurrent x).1,(actualCurrent x).2.1,(actualCurrent x).2.2 ],
    Lean.toJson c.order,Lean.toJson c.localRecords,Lean.toJson (c.rootedRoute.1.map encode),
    Lean.toJson c.rootedRoute.2,Lean.toJson c.charge,Lean.toJson c.owner.val,
    Lean.toJson x.resident.token.val,Lean.toJson (x.accounts.portCursor x.resident.token)]
def snapshot : Lean.Json := Lean.Json.arr #[
  Lean.toJson (bits.map fun flat => states.map (physicalCase flat)),
  Lean.toJson (actualInputs.map actualCase),Lean.toJson (actualInputs.map contextCase)]
#eval snapshot.compress
""")
    run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean",
                         capture_output=True, text=True, check=True)
    (folder / "G22BindingTranscriptionProbe.log").write_text(run.stdout+run.stderr)
    value = json.loads(json.loads(run.stdout.strip()))

    def decode(x):
        if isinstance(x, str):
            return F(x)
        if isinstance(x, list):
            return [decode(y) for y in x]
        return x
    return decode(value)


def main():
    expected = list(references())
    actual = evaluate()
    assert actual == expected, "actual native/flattened law or historical context drift"
    print("PASS: all 32 native/flattened states, three emitted channels, every action/output word of lengths 0-2")
    print("PASS: six actually supported source/target split executions, installed flattening control, complete rooted contexts")
    mutations = []
    # Unregistered initial-register observations destroy branchwise equivalence.
    wrong = deepcopy(expected)
    wrong[0][0][0][0][0] = F(0)
    mutations.append(("prepend initial observation", wrong))
    wrong = deepcopy(expected)
    wrong[0][1][0][2] = deepcopy(expected[0][0][0][2])
    mutations.append(("retain native correlations after flattening", wrong))
    wrong = deepcopy(expected)
    wrong[2][2][8] = 0
    mutations.append(("inherit source hardware owner", wrong))
    wrong = deepcopy(expected)
    wrong[2][4][6] = []
    mutations.append(("discard consumed snapshot receipt", wrong))
    for label, wrong in mutations:
        assert actual != wrong, f"failed planted drift control: {label}"
        print(f"PASS: caught planted drift: {label}")


if __name__ == "__main__":
    main()
