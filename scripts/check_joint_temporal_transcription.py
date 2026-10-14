#!/usr/bin/env python3
"""Independent exact G26 anchor, world-row, full-future and conditioning check."""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
BITS = (False, True)
ROOT_STATE = (False,)*5


def references():
    frozen = json.loads((ROOT / "audit/proposed_models/G17-full-native-package.model.json").read_text())
    matrix = frozen["primitive_dynamics"]["inside_maintenance_weights"]

    def rows(s, a):
        out, u, v, replica, phase = s
        if a: return [((True, u, v, replica, not phase), 16)]
        weights = [2]*4 if out else matrix[2*int(u)+int(v)]
        return [((False, x, y, r, not phase), weights[k])
                for k, (x, y) in enumerate(product(BITS, repeat=2)) for r in BITS]

    def observation(s, owner, count, serials=(20,), root_states=(ROOT_STATE,), offset=6):
        code = 8*int(s[0])+4*int(s[1])+2*int(s[2])+int(s[4])
        return [code, offset+count, int(s[4]), offset+count, offset+count,
                [list(t) for t in root_states], list(serials), True, owner]

    @lru_cache(None)
    def branch(s, owner, count, word, trace):
        ob = freeze(observation(s, owner, count))
        if not word: return F(trace == (ob,))
        if not trace or trace[0] != ob: return F(0)
        return sum((F(n, 16)*branch(t, owner, count+1, word[1:], trace[1:]) for t, n in rows(s, word[0])), F(0))

    @lru_cache(None)
    def joint(s, t, count, word, trace):
        ob = (freeze(observation(s, 1, count)), freeze(observation(t, 2, count)))
        if not word: return F(trace == (ob,))
        if not trace or trace[0] != ob: return F(0)
        return sum((F(n*m, 256)*joint(l, r, count+1, word[1:], trace[1:])
                    for l, n in rows(s, word[0][0]) for r, m in rows(t, word[0][1])), F(0))

    source = observation(ROOT_STATE, 0, 6, (), (), 0)
    anchors = [[6, 6, 20, list(ROOT_STATE)], source,
               [observation(ROOT_STATE, o, 0, offset=0) for o in (1, 2)],
               [observation(ROOT_STATE, o, 0) for o in (1, 2)], 20, [0, 0], [[6, 6], [6, 6]]]
    actual_rows = []; futures = []
    words = [()] + list(product(list(product(BITS, repeat=2)), repeat=1)) + list(
        product(list(product(BITS, repeat=2)), repeat=2))
    for initial in (0, 6):
        for a, b in product(BITS, repeat=2):
            rs = []
            for s, n in rows(ROOT_STATE, a):
                for t, m in rows(ROOT_STATE, b):
                    heads = [[o, o, 4*initial+o, list(ROOT_STATE), list(state), action, weight, True]
                             for o, state, action, weight in [(1, s, a, n), (2, t, b, m)]]
                    rs.append([list(s), list(t), F(n*m, 256), observation(s, 1, initial+1),
                               observation(t, 2, initial+1), heads, [initial+1, initial+1],
                               [True, True], [6, 0], True, True, True])
            actual_rows.append(rs)
        for word in words:
            for variant in BITS:
                s = t = ROOT_STATE
                trace = [(freeze(observation(s, 1, initial)), freeze(observation(t, 2, initial)))]
                for k, (a, b) in enumerate(word):
                    s = rows(s, True)[0][0] if a else (False, False, variant, False, not s[4])
                    t = rows(t, True)[0][0] if b else (False, False, variant, False, not t[4])
                    trace.append((freeze(observation(s, 1, initial+k+1)), freeze(observation(t, 2, initial+k+1))))
                trace = tuple(trace)
                left = branch(ROOT_STATE, 1, initial, tuple(a for a, _ in word), tuple(x for x, _ in trace))
                right = branch(ROOT_STATE, 2, initial, tuple(b for _, b in word), tuple(y for _, y in trace))
                mass = joint(ROOT_STATE, ROOT_STATE, initial, tuple(word), trace)
                assert mass == left*right
                futures.append([mass, left, right])
    controls = [[F(1, 256), F(9, 256)], F(5, 128), F(1, 10), F(1, 10), F(1, 10), F(1, 100), 0, True]
    return [anchors, actual_rows, futures, controls]


def freeze(x):
    return tuple(freeze(y) for y in x) if isinstance(x, (list, tuple)) else x


PROBE = r"""import CSTTT.FullNative.JointClaims
open CSTTT.FullNative CSTTT.FullNative.AccountExecution CSTTT.FullNative.PhysicalExecution
open CSTTT.FullNative.SnapshotExecution CSTTT.FullNative.TemporalTransport
open CSTTT.FullNative.JointFuture CSTTT.FullNative.JointClaims
def encode (s : State) : List Bool := [s.outside,s.u,s.v,s.replica,s.phase]
def rat (v : Rat) : Lean.Json := Lean.toJson (toString v)
def ob (v : Observation) : Lean.Json := Lean.Json.arr #[
  Lean.toJson (match v.predictive with | .inl p => some p.1 | .inr _ => none),Lean.toJson v.order,
  Lean.toJson v.tickPhase,Lean.toJson v.progress,Lean.toJson v.record,
  Lean.toJson (v.residue.1.map encode),Lean.toJson v.residue.2,Lean.toJson v.maintenance,Lean.toJson v.owner.val]
-- Proven definitional readout acceleration, not an observer restriction.
def fast (r : FullInterface.Run) : Observation :=
  let c := shiftContext anchor r.context
  ⟨.inl (classFormula r.current,[]),c.order,bit r.current.phase,c.order,c.localRecords,c.rootedRoute,c.charge,c.owner⟩
theorem fast_exact (r : FullInterface.Run) : fast r=FullInterface.observe (shiftRun anchor r) := by
  simp [fast,FullInterface.observe,shiftRun,first_profile_equation]
def fastWorld (w : World) := (worldRuns w).map fun rs => (fast rs.1,fast rs.2)
theorem fast_world_exact (w : World) : fastWorld w=worldObservation anchor w := by
  simp only [fastWorld,worldObservation,fast_exact]
  rfl
def fastJoint (w : World) (word : List (Bool × Bool)) (trace : List (Observation × Observation)) :=
  WeightedFuture.law normalizedJointRows fastWorld w word (trace.map some)
theorem fast_joint_exact (w : World) (word : List (Bool × Bool)) (trace : List (Observation × Observation)) :
    fastJoint w word trace=jointLaw anchor w word trace := by
  unfold fastJoint jointLaw
  congr 1
  funext w
  exact fast_world_exact w
def head (r : Receipt) : Lean.Json := Lean.Json.arr #[
  Lean.toJson (match r.issuer with | .localGenerator o => o.val | .bridge => 3),Lean.toJson r.token.val,
  Lean.toJson r.serial,Lean.toJson (encode r.before),Lean.toJson (encode r.after),Lean.toJson r.action,
  Lean.toJson r.weight,Lean.toJson r.energy.isSome]
def rowData (e : World × Rat) : Lean.Json := match e.1.carriers 1,e.1.carriers 2 with
  | some p,some q => Lean.Json.arr #[Lean.toJson (encode p.current),Lean.toJson (encode q.current),rat e.2,
    ob (fast (frame ⟨e.1.accounts,p⟩)),ob (fast (frame ⟨e.1.accounts,q⟩)),
    Lean.toJson [p.receipts.head?.map head,q.receipts.head?.map head],
    Lean.toJson [e.1.accounts.portCursor 1,e.1.accounts.portCursor 2],
    Lean.toJson [e.1.accounts.charge 1,e.1.accounts.charge 2],
    Lean.toJson [e.1.accounts.portCursor 0,e.1.accounts.portCursor 3],
    Lean.toJson (e.1.carriers 0).isNone,Lean.toJson e.1.bridge.isNone,
    Lean.toJson ([0,1,2].all fun o => (e.1.slots o).isNone)]
  | _,_ => Lean.Json.null
def actions : List (Bool × Bool) := [(false,false),(false,true),(true,false),(true,true)]
def words : List (List (Bool × Bool)) := [[]]++actions.map (fun a => [a])++
  actions.flatMap fun a => actions.map fun b => [a,b]
def next (s : State) (a variant : Bool) : State :=
  if a then ⟨true,s.u,s.v,s.replica,!s.phase⟩ else ⟨false,false,variant,false,!s.phase⟩
def plannedTrace (rs : FullInterface.Run × FullInterface.Run) : List (Bool × Bool) → Bool → List (Observation × Observation)
  | [],_ => [(fast rs.1,fast rs.2)]
  | a::rest,v => (fast rs.1,fast rs.2)::plannedTrace
    (FullInterface.advance rs.1 (next rs.1.current a.1 v),FullInterface.advance rs.2 (next rs.2.current a.2 v)) rest v
def futureData (w : World) : List Lean.Json := match w.carriers 1,w.carriers 2 with
  | some p,some q => words.flatMap fun word => bits.map fun v =>
    let rs := (frame ⟨w.accounts,p⟩,frame ⟨w.accounts,q⟩)
    let trace := plannedTrace rs word v
    Lean.Json.arr #[rat (fastJoint w word trace),
      rat (WeightedFuture.law (normalizedRows renewable) (fun x => fast (frame x)) ⟨w.accounts,p⟩
        (word.map Prod.fst) (trace.map Prod.fst)),
      rat (WeightedFuture.law (normalizedRows renewable) (fun x => fast (frame x)) ⟨w.accounts,q⟩
        (word.map Prod.snd) (trace.map Prod.snd))]
  | _,_ => []
def anchorData : Lean.Json := Lean.Json.arr #[
  Lean.Json.arr #[Lean.toJson anchor.order,Lean.toJson anchor.records,Lean.toJson anchor.receipt,Lean.toJson (encode anchor.state)],
  ob (FullInterface.observe (frame sourceAtCopy)),
  Lean.toJson (bits.map fun r => ob (FullInterface.observe (frame (targetAtCopy r)))),
  Lean.toJson (bits.map fun r => ob (fast (frame (targetAtCopy r)))),
  Lean.toJson (sourceAtCopy.resident.receipts.head?.map Receipt.serial),
  Lean.toJson (bits.map fun r => (targetAtCopy r).resident.receipts.length),
  Lean.toJson (bits.map fun r => retainedEpoch (frame (targetAtCopy r)).context)]
def snapshot : Lean.Json := Lean.Json.arr #[anchorData,
  Lean.toJson ([Credit.creditedTransferWorld,Credit.creditedBothWorld].flatMap fun w =>
    actions.map fun a => (normalizedJointRows w a).map rowData),
  Lean.toJson ([Credit.creditedTransferWorld,Credit.creditedBothWorld].flatMap futureData),
  Lean.Json.arr #[Lean.toJson (eventRows.map fun e => rat e.2),rat eventMass,
    Lean.toJson ((conditionedJoint [] [correlatedObservation false]).map rat),
    Lean.toJson ((conditionedBranch false [] [(correlatedObservation false).1]).map rat),
    Lean.toJson ((conditionedBranch true [] [(correlatedObservation false).2]).map rat),rat ((1/10:Rat)*(1/10)),
    Lean.toJson (normalizedJointRows {Credit.creditedBothWorld with carriers := putOwner Credit.creditedBothWorld.carriers 2 none}
      (false,false)).length,
    Lean.toJson (worldRuns {Credit.creditedBothWorld with carriers := putOwner Credit.creditedBothWorld.carriers 2 none}).isNone]]
#eval snapshot.compress
"""


def evaluate():
    folder = ROOT / "lean/.validate-logs"; folder.mkdir(exist_ok=True)
    probe = folder / "G26JointTranscriptionProbe.lean"; probe.write_text(PROBE)
    run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean", capture_output=True, text=True)
    (folder / "G26-joint-transcription-probe.log").write_text(run.stdout+run.stderr)
    if run.returncode: raise RuntimeError("Lean probe failed: see G26-joint-transcription-probe.log")
    def decode(x):
        if isinstance(x, str): return F(x)
        if isinstance(x, list): return [decode(y) for y in x]
        return x
    return decode(json.loads(json.loads(run.stdout.strip())))


def main():
    expected = references(); actual = evaluate()
    assert actual == expected, "anchor/temporal/joint-world/full-future/conditioning drift"
    assert len(actual[1]) == 8 and sum(map(len, actual[1])) == 162 and len(actual[2]) == 84
    print("PASS: consumed receipt20 and source6/local0 anchor; exact retained owner/root and context transport")
    print("PASS: 8 actual joint rows, all 162 complete successor/receipt/account/readout records; normalization256")
    print("PASS: 84 actual initial-inclusive full-future queries (paired words through length2), both branch laws")
    print("PASS: actual conditioned weights1,9; joint1/10 vs marginal product1/100; missing-branch None/empty")
    changes = []
    wrong = deepcopy(expected); wrong[0][0][0] = 0; changes.append(("elapsed source order erased", wrong))
    wrong = deepcopy(expected); wrong[0][2][0][4] = 6; changes.append(("target local record supplied as inherited6", wrong))
    wrong = deepcopy(expected); wrong[1][0][0][2] *= 16; changes.append(("joint denominator16 instead of256", wrong))
    wrong = deepcopy(expected); wrong[0][3][0][8] = 0; changes.append(("target ownership collapsed to source", wrong))
    wrong = deepcopy(expected); wrong[3][2] = F(1, 100); changes.append(("conditioned marginals falsely multiplied", wrong))
    for label, wrong in changes:
        assert actual != wrong, f"failed planted drift: {label}"
        print(f"PASS: caught planted drift: {label}")


if __name__ == "__main__": main()
