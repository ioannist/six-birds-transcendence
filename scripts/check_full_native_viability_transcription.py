#!/usr/bin/env python3
"""Reconstruct the full charge factor and actual native C8 readouts independently.

Finite transcription supplements the universal Lean history proofs; it does not
enumerate arbitrary predicates or pretend to establish history greatestness.
"""
from __future__ import annotations

from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
STATES = list(product((False, True), repeat=5))
FACTOR = [(s, c) for s in STATES for c in (False, True)]


def references():
    frozen = json.loads((ROOT / "audit/proposed_models/G17-full-native-package.model.json").read_text())
    matrix = frozen["primitive_dynamics"]["inside_maintenance_weights"]

    def rows(s, action):
        out, u, v, replica, phase = s
        if action:
            return [((True, u, v, replica, not phase), 16)]
        weights = [2] * 4 if out else matrix[2 * int(u) + int(v)]
        return [((False, x, y, r, not phase), weights[k])
                for k, (x, y) in enumerate(product((False, True), repeat=2))
                for r in (False, True)]

    def funded(q, renew, action):
        return [(t, renew, n) for t, n in rows(q[0], action)] if q[1] else []

    def candidates(q):
        s, c = q
        return [True, not s[0] and c, False, c, not s[4], q == FACTOR[1]]

    def predecessor(q, renew, index):
        return not q[0][0] and any(
            bool(rs := funded(q, renew, a)) and all(candidates((t, c))[index] for t, c, _ in rs)
            for a in (False, True))

    def encode_row(s, renew, action, t, n, owner=0, cursor=0, records=0):
        # Complete new receipt, retained history counters and actual own account.
        return [list(t), renew, n, owner, owner, cursor + 1, records + 1, records + 1,
                [owner, owner, 4 * cursor + owner, list(s), list(t), action, n, renew], True, True]

    cases = []
    for s, c in FACTOR:
        for renew in (False, True):
            actual_rows = [[encode_row(s, renew, a, t, n) for t, n in rows(s, a)] if c else []
                           for a in (False, True)]
            factor_rows = [[[list(t), charge, n] for t, charge, n in funded((s, c), renew, a)]
                           for a in (False, True)]
            pres = [predecessor((s, c), renew, k) for k in range(6)]
            cases.append([list(s), c, renew, actual_rows, factor_rows, pres, pres])

    root = [False] * 5
    anchors = []
    for owner, records, cursor, roots, serials in [(0, 0, 0, [], []),
                                                (1, 6, 6, [root], [20]),
                                                (2, 6, 6, [root], [20])]:
        metadata = [root, True, owner, owner, records, records, roots, serials, cursor, True, True]
        successors = [[encode_row(root, renew, a, t, n, owner, cursor, records)
                       for t, n in rows(tuple(root), a)]
                      for renew in (False, True) for a in (False, True)]
        anchors.append([metadata, True, successors])

    # Missing program/allocation, mismatched actor, depleted charge; all supplies
    # and all six retained-set candidates. No missing-input defaults are used.
    gates = [[False] * 12 for _ in range(4)]
    iterations = []
    for renew in (False, True):
        current = set(FACTOR)
        chain = []
        for _ in range(4):
            chain.append([q in current for q in FACTOR])
            current = {q for q in FACTOR if not q[0][0] and any(
                bool(rs := funded(q, renew, a)) and all((t, c) in current for t, c, _ in rs)
                for a in (False, True))}
        iterations.append(chain)
    return [cases, anchors, gates, iterations, [64, 16]]


PROBE = r"""import CSTTT.FullNative.ViabilityFactor
open CSTTT.FullNative CSTTT.FullNative.Viability
open CSTTT.FullNative.AccountExecution CSTTT.FullNative.PhysicalExecution
def encode (s : State) : List Bool := [s.outside,s.u,s.v,s.replica,s.phase]
def receipt (r : Receipt) : Lean.Json := Lean.Json.arr #[
  Lean.toJson (match r.issuer with | .localGenerator o => o.val | .bridge => 3),
  Lean.toJson r.token.val,Lean.toJson r.serial,Lean.toJson (encode r.before),
  Lean.toJson (encode r.after),Lean.toJson r.action,Lean.toJson r.weight,Lean.toJson r.energy.isSome]
def actualRow (e : Execution × Nat) : Lean.Json :=
  let x := e.1
  Lean.Json.arr #[Lean.toJson (encode x.resident.current),Lean.toJson (quote x).2,Lean.toJson e.2,
    Lean.toJson x.resident.owner.val,Lean.toJson x.resident.token.val,
    Lean.toJson (x.accounts.portCursor x.resident.token),Lean.toJson (frame x).context.order,
    Lean.toJson (frame x).context.localRecords,Lean.toJson (x.resident.receipts.head?.map receipt),
    Lean.toJson x.resident.installed.isSome,
    Lean.toJson (decide (x.accounts.allocation x.resident.token=some (.localGenerator x.resident.owner)))]
def candidates : List (VState → Bool) := [fun _ => true,core,fun _ => false,Prod.snd,
  fun q => !q.1.phase,fun q => decide (q=(FullInterface.rootState,true))]
def factorRow (e : VState × Nat) : Lean.Json :=
  Lean.Json.arr #[Lean.toJson (encode e.1.1),Lean.toJson e.1.2,Lean.toJson e.2]
def caseData (q : VState) (renew : Bool) : Lean.Json := Lean.Json.arr #[
  Lean.toJson (encode q.1),Lean.toJson q.2,Lean.toJson renew,
  Lean.toJson (bits.map fun a => (rawRows (environment renew) (initialFor q) a).map actualRow),
  Lean.toJson (bits.map fun a => (fundedRows renew q a).map factorRow),
  Lean.toJson (candidates.map fun V => pre renew V q),
  Lean.toJson (candidates.map fun V => actualPre renew V (initialFor q))]
def anchor (x : Execution) : Lean.Json := Lean.Json.arr #[
  Lean.Json.arr #[Lean.toJson (encode x.resident.current),Lean.toJson (quote x).2,
    Lean.toJson x.resident.owner.val,Lean.toJson x.resident.token.val,
    Lean.toJson (frame x).context.order,Lean.toJson (frame x).context.localRecords,
    Lean.toJson (x.resident.rootedRoute.1.map encode),Lean.toJson x.resident.rootedRoute.2,
    Lean.toJson (x.accounts.portCursor x.resident.token),Lean.toJson x.resident.installed.isSome,
    Lean.toJson (decide (x.accounts.allocation x.resident.token=some (.localGenerator x.resident.owner)))],
  Lean.toJson (core (quote x)),Lean.toJson (bits.flatMap fun renew => bits.map fun a =>
    (rawRows (environment renew) x a).map actualRow)]
def missingProgram : Execution := {source with resident := {source.resident with installed := none}}
def missingAccount : Execution := {source with accounts := {source.accounts with
  allocation := put source.accounts.allocation source.resident.token none}}
def wrongActor : Execution := {source with accounts := {source.accounts with
  allocation := put source.accounts.allocation source.resident.token (some .bridge)}}
def depleted : Execution := {source with accounts := debit source.accounts source.resident.token}
def rounds (renew : Bool) : Nat → VState → Bool
  | 0 => fun _ => true
  | n+1 => pre renew (rounds renew n)
def snapshot : Lean.Json := Lean.Json.arr #[
  Lean.toJson (carrier.flatMap fun q => bits.map fun renew => caseData q renew),
  Lean.toJson [anchor source,anchor (firstTargetHistory true).1,anchor (secondTargetHistory true).1],
  Lean.toJson ([missingProgram,missingAccount,wrongActor,depleted].map fun x =>
    bits.flatMap fun renew => candidates.map fun V => actualPre renew V x),
  Lean.toJson (bits.map fun renew => (List.range 4).map fun n => carrier.map (rounds renew n)),
  Lean.toJson [carrier.length,(carrier.filter core).length]]
#eval snapshot.compress
"""


def evaluate():
    folder = ROOT / "lean/.validate-logs"
    folder.mkdir(exist_ok=True)
    probe = folder / "G24ViabilityTranscriptionProbe.lean"
    probe.write_text(PROBE)
    run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean",
                         capture_output=True, text=True)
    (folder / "G24-viability-transcription-probe.log").write_text(run.stdout + run.stderr)
    if run.returncode:
        raise RuntimeError("Lean transcription failed; see G24-viability-transcription-probe.log")
    return json.loads(json.loads(run.stdout.strip()))


def main():
    expected = references()
    actual = evaluate()
    assert actual == expected, "actual charge-factor/native predecessor/account/receipt drift"
    assert [sum(level) for level in actual[3][0]] == [64, 16, 0, 0]
    assert [sum(level) for level in actual[3][1]] == [64, 16, 16, 16]
    print("PASS: all 64 physical/charge states, both supplies/actions; 256 rows and 576 complete successors")
    print("PASS: six retained sets, exact finite/actual predecessor, 64->16->16 and 64->16->0 pruning")
    print("PASS: actual source/credited targets, new receipts/cursors, four actual rejection controls")
    mutations = []
    wrong = deepcopy(expected); wrong[0][2][3] = [[], []]
    mutations.append(("absence erases first stored-charge step", wrong))
    wrong = deepcopy(expected); wrong[0][2][3][0][0][1] = True
    mutations.append(("absent supply renews charge", wrong))
    wrong = deepcopy(expected); wrong[2][0][0] = True
    mutations.append(("missing program admits predecessor", wrong))
    wrong = deepcopy(expected); wrong[1][1][0][7] = [0]
    mutations.append(("target root receipt20 replaced by default", wrong))
    wrong = deepcopy(expected); wrong[0][3][3][0][0][0][4] = False
    mutations.append(("phase erased from successor", wrong))
    for label, wrong in mutations:
        assert actual != wrong, f"failed planted drift: {label}"
        print(f"PASS: caught planted drift: {label}")


if __name__ == "__main__":
    main()
