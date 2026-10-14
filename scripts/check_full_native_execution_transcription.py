#!/usr/bin/env python3
"""Independent full-native account, receipt and enabled-edge transcription."""
from __future__ import annotations

from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]


def expected():
    frozen = json.loads((ROOT / "audit/proposed_models/G17-full-native-package.model.json").read_text())
    matrix = frozen["primitive_dynamics"]["inside_maintenance_weights"]
    contexts = []
    # Installed/missing program, owned/wrong/absent allocation, charge and packet.
    for installed, allocation, charge, packet in product((False, True), range(3), (False, True), (False, True)):
        outputs = []
        for s in product((False, True), repeat=5):
            for action in (False, True):
                out, u, v, replica, phase = s
                edges = []
                if installed and allocation == 0 and charge:
                    if action:
                        raw = [((True, u, v, replica, not phase), 16)]
                    else:
                        weights = [2] * 4 if out else matrix[2 * int(u) + int(v)]
                        raw = [((False, x, y, r, not phase), weights[k])
                               for k, (x, y) in enumerate(product((False, True), repeat=2))
                               for r in (False, True)]
                    for target, weight in raw:
                        # owner1/token1, initial cursor7, receipt ID 4*7+1;
                        # previous receipt count zero, clock base5, unchanged route.
                        edges.append([list(target), weight, packet, 8, 1, 6, 1, 1,
                                      29, list(s), list(target), action, weight, packet,
                                      True, 0, True, 0, True, 0, 1,
                                      [list(s)], [19]])
                outputs.append(edges)
        contexts.append(outputs)
    return contexts


def evaluated():
    folder = ROOT / "lean/.validate-logs"
    probe = folder / "G19ExecutionTranscriptionProbe.lean"
    probe.write_text("""import CSTTT.FullNative.PhysicalExecution
open CSTTT.FullNative CSTTT.FullNative.AccountExecution CSTTT.FullNative.PhysicalExecution
def encodeState (s : State) : List Bool := [s.outside,s.u,s.v,s.replica,s.phase]
def actorCode : Actor → Nat | .localGenerator o => o.val | .bridge => 3
def mkExecution (installed : Bool) (allocation : Nat) (charge : Bool) (s : State) : Execution :=
  ⟨⟨(fun t => if t=1 then (if allocation=0 then some (.localGenerator 1)
         else if allocation=1 then some .bridge else none) else canonical.allocation t),
     (fun t => if t=1 then charge else true),(fun t => if t=1 then 7 else 0)⟩,
   ⟨1,1,(if installed then some model else none),s,[],([s],[19]),5⟩⟩
def edgeJson (e : Execution × Nat) : Lean.Json :=
  let x := e.1
  match x.resident.receipts.head? with
  | none => Lean.Json.null
  | some r => Lean.Json.arr #[Lean.toJson (encodeState x.resident.current),Lean.toJson e.2,
      Lean.toJson (x.accounts.charge 1),Lean.toJson (x.accounts.portCursor 1),
      Lean.toJson x.resident.receipts.length,Lean.toJson (frame x).context.order,
      Lean.toJson x.resident.owner.val,Lean.toJson x.resident.token.val,
      Lean.toJson r.serial,Lean.toJson (encodeState r.before),Lean.toJson (encodeState r.after),
      Lean.toJson r.action,Lean.toJson r.weight,Lean.toJson r.energy.isSome,
      Lean.toJson (x.accounts.charge 0),Lean.toJson (x.accounts.portCursor 0),
      Lean.toJson (x.accounts.charge 2),Lean.toJson (x.accounts.portCursor 2),
      Lean.toJson (x.accounts.charge 3),Lean.toJson (x.accounts.portCursor 3),
      Lean.toJson (actorCode r.issuer),Lean.toJson (x.resident.rootedRoute.1.map encodeState),
      Lean.toJson x.resident.rootedRoute.2]
def snapshot : Lean.Json := Lean.toJson (bits.flatMap fun installed =>
  [0,1,2].flatMap fun allocation => bits.flatMap fun charge => bits.map fun packet =>
    states.flatMap fun s => bits.map fun action =>
      (rawRows (if packet then renewable else absentSupply)
        (mkExecution installed allocation charge s) action).map edgeJson)
#eval snapshot.compress
""")
    run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean",
                         capture_output=True, text=True, check=True)
    (folder / "G19ExecutionTranscriptionProbe.log").write_text(run.stdout + run.stderr)
    return json.loads(json.loads(run.stdout.strip()))


def compare(actual, reference):
    if actual != reference:
        raise AssertionError("physical execution differs from frozen account/edge/receipt recipe")


def main():
    actual, reference = evaluated(), expected()
    compare(actual, reference)
    count = sum(len(edges) for context in reference for edges in context)
    print(f"PASS execution transcription: 24 account/input contexts, 1536 action rows, {count} enabled edges")
    # Alter operative readouts, without touching installed tools or tracked sources.
    for label, index, replacement in [("recharge", 2, False), ("port consumption", 3, 7),
                                      ("receipt source", 9, [True] * 5)]:
        changed = deepcopy(reference)
        witness = next(edges for context in changed for edges in context if edges and edges[0][2])
        witness[0][index] = replacement
        try:
            compare(actual, changed)
        except AssertionError:
            print("CAUGHT planted " + label + " drift")
        else:
            raise AssertionError("missed planted " + label + " drift")


if __name__ == "__main__":
    main()
