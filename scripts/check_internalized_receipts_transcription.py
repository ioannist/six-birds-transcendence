#!/usr/bin/env python3
"""Independent exact transcription of the frozen reversible nine-state control."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as F
from itertools import product
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
STATES = list(product(range(3), repeat=2))


def kernel(p, phase, x, y):
    pair = (1, 2) if phase == 1 else (0, 1)
    if x not in pair:
        return F(x == y)
    return 1-p if x == y else p if y in pair else F(0)


def part(p, channel, s, t):
    return (kernel(p, s[1], s[0], t[0])/2 if s[1] == t[1] else F(0)) if channel == 0 else (
        F(1, 6) if s[0] == t[0] else F(0))


def receipt(owner, channel, before, after, w, cursors, renew):
    token = owner if channel == 0 else 3
    return [owner if channel == 0 else 3, token, 4*cursors[channel]+token,
            channel, list(before), list(after), w, renew]


def references():
    # Bias values and phase-kernel recipes are frozen G15a inputs, not fitted
    # to the readouts. The Lean native parameter is derived from the old P.
    frozen = json.loads((ROOT / "audit/proposed_models/G15a/native-generator-credit-primitives-predictions.json").read_text())
    assert "P05 bias2/3" in " ".join(frozen["predictions"])
    matrices = []; cases = []; histories = []; protocols = []
    cycle = [(0, (1, 0)), (1, (1, 2)), (0, (0, 2)), (1, (0, 0))]
    holonomy = [(0, (1, 0)), (1, (1, 1)), (0, (2, 1)), (1, (2, 0))]
    for p in (F(2, 3), F(3, 8)):
        matrices.append([[part(p, 0, s, t), part(p, 1, s, t),
                          part(p, 0, s, t)+part(p, 1, s, t)] for s in STATES for t in STATES])
        for owner in range(3):
            for s in STATES:
                for content_charge, clock_charge in product((False, True), repeat=2):
                    for renew in (False, True):
                        rs = []
                        for channel in range(2):
                            if not (content_charge, clock_charge)[channel]:
                                continue
                            for t in STATES:
                                w = part(p, channel, s, t)
                                if w <= 0:
                                    continue
                                charges = [content_charge, clock_charge]; charges[channel] = renew
                                cursors = [0, 0]; cursors[channel] = 1
                                rs.append([list(t), w, charges, cursors,
                                           receipt(owner, channel, s, t, w, [0, 0], renew)])
                        cases.append(rs)
            for plan in (cycle, holonomy):
                s = (0, 0); cursors = [0, 0]; receipts = []; weight = F(1)
                for channel, t in plan:
                    w = part(p, channel, s, t); assert w > 0
                    receipts.insert(0, receipt(owner, channel, s, t, w, cursors, True))
                    cursors[channel] += 1; weight *= w; s = t
                histories.append([list(s), cursors, [True, True], receipts, True, weight,
                                  F(0), F(0), weight])
            # Full matrices for both return-to-a protocols, not just a single
            # favorable endpoint. Rows are selected without renormalization.
            ab = []; ba = []
            for x in range(3):
                for y in range(3):
                    ab.append(sum(kernel(p, 0, x, m)*kernel(p, 1, m, y) for m in range(3))/144)
                    ba.append(sum(kernel(p, 1, x, m)*kernel(p, 0, m, y) for m in range(3))/144)
            protocols.append([ab, ba])
    controls = [0, 3, 2, 3, 0, False, False]
    return [matrices, cases, histories, protocols, controls]


PROBE = r"""import CSTTT.FullNative.InternalizedCredit
open CSTTT.FullNative.Internalized CSTTT.FullNative.AccountExecution
open CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeGeneratorCreditPrototype
def tri : Tri → Nat | .a => 0 | .b => 1 | .c => 2
def state (s : CSTTT.FullNative.Internalized.State) : List Nat := [tri s.1,tri s.2]
def rat (w : Rat) : Lean.Json := Lean.toJson (toString w)
def actor : Actor → Nat | .localGenerator o => o.val | .bridge => 3
def channel : Channel → Nat | .content => 0 | .clock => 1
def encodeReceipt (r : Receipt) : Lean.Json := Lean.Json.arr #[
  Lean.toJson (actor r.issuer),Lean.toJson r.token.val,Lean.toJson r.serial,
  Lean.toJson (channel r.channel),Lean.toJson (state r.before),Lean.toJson (state r.after),
  rat r.weight,Lean.toJson r.energy.isSome]
def cursors (x : Execution) : List Nat := [x.accounts.portCursor x.token,x.accounts.portCursor 3]
def charges (x : Execution) : List Bool := [x.accounts.charge x.token,x.accounts.charge 3]
def row (e : Execution × Rat) : Lean.Json := Lean.Json.arr #[Lean.toJson (state e.1.current),rat e.2,
  Lean.toJson (charges e.1),Lean.toJson (cursors e.1),Lean.toJson (e.1.receipts.head?.map encodeReceipt)]
def config (f : Flavor) (o : Owner) (s : CSTTT.FullNative.Internalized.State) (c k : Bool) : Execution :=
  let x := root f o
  {x with current := s,accounts := {x.accounts with charge := put (put x.accounts.charge x.token c) 3 k}}
def history (f : Flavor) (x : Execution) : Lean.Json := Lean.Json.arr #[
  Lean.toJson (state x.current),Lean.toJson (cursors x),Lean.toJson (charges x),
  Lean.toJson (x.receipts.map encodeReceipt),Lean.toJson (receiptAudit f x),
  rat (receiptProduct Receipt.weight x.receipts),
  rat (edgeProduct (contentChannel (parameter f)) (edges x.receipts)),
  rat (edgeProduct clockChannel (edges x.receipts)),
  rat (edgeProduct (liftP (parameter f)) (reversedEdges (edges x.receipts)))]
def flavors : List Flavor := [.source,.native]
def owners : List Owner := [0,1,2]
def matrix (f : Flavor) : List Lean.Json := liftStates.flatMap fun s => liftStates.map fun t =>
  Lean.Json.arr #[rat (part f .content s t),rat (part f .clock s t),rat (liftP (parameter f) s t)]
def protocolData (f : Flavor) (o : Owner) : Lean.Json := Lean.Json.arr #[
  Lean.toJson (triStates.flatMap fun s => triStates.map fun t =>
    rat (protocolMass renewable {root f o with current := (s,.a)} protocolAB (t,.a))),
  Lean.toJson (triStates.flatMap fun s => triStates.map fun t =>
    rat (protocolMass renewable {root f o with current := (s,.a)} protocolBA (t,.a)))]
def absentFirst : Execution := advance absentSupply (root .source 0) .content (.b,.a) (1/3)
def absentBoth : Execution := advance absentSupply absentFirst .clock (.b,.b) (1/6)
def noProgram : Execution := {root .source 0 with installed := none}
def noContent : Execution := {root .source 0 with accounts :=
  {canonical with allocation := put canonical.allocation 0 none}}
def noClock : Execution := {root .source 0 with accounts :=
  {canonical with allocation := put canonical.allocation 3 none}}
def snapshot : Lean.Json := Lean.Json.arr #[
  Lean.toJson (flavors.map matrix),
  Lean.toJson (flavors.flatMap fun f => owners.flatMap fun o => liftStates.flatMap fun s =>
    [false,true].flatMap fun c => [false,true].flatMap fun k => [false,true].map fun renew =>
      (rawRows (if renew then renewable else absentSupply) (config f o s c k)).map row),
  Lean.toJson (flavors.flatMap fun f => owners.flatMap fun o =>
    [history f (cycleEnd f o),history f (holonomyEnd f o)]),
  Lean.toJson (flavors.flatMap fun f => owners.map fun o => protocolData f o),
  Lean.Json.arr #[Lean.toJson (rawRows renewable noProgram).length,Lean.toJson (rawRows renewable noContent).length,
    Lean.toJson (rawRows renewable noClock).length,Lean.toJson (rawRows absentSupply absentFirst).length,
    Lean.toJson (rawRows absentSupply absentBoth).length,Lean.toJson (receiptAudit .source
      {cycleEnd .source 0 with receipts := []}),Lean.toJson (receiptAudit .source
      {cycleEnd .source 0 with receipts := (cycleEnd .source 0).receipts.map fun r => {r with issuer := .localGenerator 0}})]]
#eval snapshot.compress
"""


def evaluate():
    folder = ROOT / "lean/.validate-logs"; folder.mkdir(exist_ok=True)
    probe = folder / "G25InternalizedTranscriptionProbe.lean"; probe.write_text(PROBE)
    run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean", capture_output=True, text=True)
    (folder / "G25-internalized-transcription-probe.log").write_text(run.stdout+run.stderr)
    if run.returncode:
        raise RuntimeError("Lean probe failed: see G25-internalized-transcription-probe.log")
    def decode(x):
        if isinstance(x, str): return F(x)
        if isinstance(x, list): return [decode(y) for y in x]
        return x
    return decode(json.loads(json.loads(run.stdout.strip())))


def main():
    expected = references(); actual = evaluate()
    assert actual == expected, "nine-state matrix/account/receipt/protocol drift"
    assert len(actual[1]) == 432 and sum(map(len, actual[1])) == 1008
    print("PASS: both frozen 9x9 matrices, 432 account/supply rows and 1008 complete generated successors")
    print("PASS: all three owners, 12 supported cycle/protocol histories, all 48 complete receipts and exact products")
    print("PASS: complete actual AB/BA protocol matrices; absent, missing-program/account and forged-issuer controls")
    mutations = []
    wrong = deepcopy(expected); wrong[2][0][3][0][0] = 0
    mutations.append(("clock issuer relabelled local", wrong))
    wrong = deepcopy(expected); wrong[2][0][4] = False
    mutations.append(("valid mixed channel provenance rejected as G23 mixed issuer", wrong))
    wrong = deepcopy(expected); wrong[3][0][0][2] = F(0)
    mutations.append(("holonomy erased", wrong))
    wrong = deepcopy(expected); wrong[4][3] = 0
    mutations.append(("absence disables both channels after only one debit", wrong))
    wrong = deepcopy(expected); wrong[0][1][0][0] = F(2, 3)
    mutations.append(("native bias replaced by source bias", wrong))
    for label, wrong in mutations:
        assert actual != wrong, f"failed planted drift: {label}"
        print(f"PASS: caught planted drift: {label}")


if __name__ == "__main__":
    main()
