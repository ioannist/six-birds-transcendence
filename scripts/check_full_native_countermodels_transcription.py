#!/usr/bin/env python3
"""G28 actual TTN readouts and old/upgraded cyclic interface comparison.

Finite transcription checks concrete readouts, not the universal Lean gluing or
all-word theorems. Reuse the independently reconstructed G27 execution ledger.
"""
from __future__ import annotations
from copy import deepcopy
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
import json
from pathlib import Path
import subprocess
from check_full_native_package_transcription import PROBE as G27_PROBE, reference as package_reference

ROOT = Path(__file__).resolve().parents[1]
BITS = (False, True)
STATES = list(product(BITS, repeat=5))


def reference():
    packet = package_reference()
    before = packet[0][1][0]
    after = packet[0][1][1][0][0][0]
    source = packet[0][0][0]
    flat = deepcopy(source)
    flat[12] = "neutral"
    for r in flat[11]: r[6] = 2
    flat[15] = [F(1, 8) if not s[0] and s[4] else F(0) for s in STATES]
    frozen = json.loads((ROOT / "audit/proposed_models/G17-full-native-package.model.json").read_text())
    weights = frozen["primitive_dynamics"]["inside_maintenance_weights"]

    def rows(s, a, null):
        out, u, v, replica, phase = s
        if a: return [((True, u, v, replica, not phase), 16)]
        ws = [2]*4 if null or out else weights[2*int(u)+int(v)]
        return [((False, x, y, r, not phase), ws[k])
                for k, (x, y) in enumerate(product(BITS, repeat=2)) for r in BITS]

    @lru_cache(None)
    def emitted(s, null, channel, word, trace):
        if not word: return F(not trace)
        if not trace: return F(0)
        def observe(t):
            if t[0]: return 0
            return int(t[1]) if channel == 0 else int(t[2]) if channel == 1 else 2*int(t[1])+int(t[2])
        return sum((F(n,16)*emitted(t,null,channel,word[1:],trace[1:])
                    for t,n in rows(s,word[0],null) if observe(t)==trace[0]),F(0))

    queries = []
    for n in range(3):
        for word in product(BITS, repeat=n):
            for channel in range(3):
                for trace in product(range(2 if channel<2 else 4), repeat=n):
                    a=emitted(tuple(source[0]),False,channel,word,trace)
                    b=emitted(tuple(flat[0]),True,channel,word,trace)
                    if channel<2: assert a==b
                    queries.append([list(word),channel,list(trace),a,b])
    codes = [[0,6,6,[],[],0] if c!=5 else [0,6,6,[list(source[0])],[20],1] for c in range(8)]
    edges = [[c,d] for c in range(8) for d in range(8) if (c+1)%8==d or (d+1)%8==c]
    return [[before,after],flat,queries,[edges,[[0,16,16]]*8,codes,
            [codes[c]==codes[d] for c,d in edges],1,[0,0]],
            [F(1,8),F(1,4),source[12],flat[12],1,0,[1,0]]]


PROBE = G27_PROBE.split("def endpoints")[0].replace(
    "import CSTTT.FullNative.OriginalPackage", "import CSTTT.FullNative.PackageCycle") + r"""
def words : Nat → List (List Bool)
  | 0 => [[]]
  | n+1 => bits.flatMap fun a => (words n).map (a::·)
def outputs (base : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n+1 => (List.range base).flatMap fun a => (outputs base n).map (a::·)
def observed (channel : Nat) (x : Execution) : Nat :=
  if channel=2 then Binding.joint x.resident.current else Binding.branch (channel=1) x.resident.current
def queries : List Lean.Json := (List.range 3).flatMap fun n => (words n).flatMap fun word =>
  (List.range 3).flatMap fun channel => (outputs (if channel=2 then 4 else 2) n).map fun trace =>
  Lean.Json.arr #[Lean.toJson word,Lean.toJson channel,Lean.toJson trace,
    rat (Binding.emittedLaw (normalizedRows renewable) (observed channel)
      RecombinationBoundary.canonicalExecution word trace),
    rat (Binding.emittedLaw (normalizedRows renewable) (observed channel)
      RecombinationBoundary.flatExecution word trace)]
def clauses : List Clause := [.c1,.c2,.c3,.c4,.c5,.c6,.c7,.c8]
def code (c : Clause) : Option Lean.Json := (PackageCycle.fullCode (PackageCycle.mixed c)).map fun q =>
  Lean.Json.arr #[Lean.toJson q.1,Lean.toJson q.2.order,Lean.toJson q.2.localRecords,
    Lean.toJson (q.2.rootedRoute.1.map encode),Lean.toJson q.2.rootedRoute.2,Lean.toJson q.2.owner.val]
def edgePairs : List (Clause × Clause) := clauses.flatMap fun c => clauses.filterMap fun d =>
  if PackageCycle.adjacent c d then some (c,d) else none
def snapshot : Lean.Json := Lean.Json.arr #[
  Lean.toJson [data PublicShadow.beforeExecution,data PublicShadow.afterExecution],
  data RecombinationBoundary.flatExecution,Lean.toJson queries,
  Lean.Json.arr #[Lean.toJson (edgePairs.map fun p => [clauses.idxOf p.1,clauses.idxOf p.2]),
    Lean.toJson (clauses.map fun c => (PublicShadow.shadow (PackageCycle.mixed c)).map fun t => [t.1,t.2.1,t.2.2]),
    Lean.toJson (clauses.map code),Lean.toJson (edgePairs.map fun p => decide
      (PackageCycle.fullCode (PackageCycle.mixed p.1)=PackageCycle.fullCode (PackageCycle.mixed p.2))),
    Lean.toJson PackageCycle.oldC6Position,Lean.toJson ([sourceRaw,targetRaw false].map fun p =>
      PackageCycle.installedPublic p FullInterface.rootState)],
  Lean.Json.arr #[rat (RecombinationBoundary.jointLaw RecombinationBoundary.canonicalExecution [false] [0]),
    rat (RecombinationBoundary.jointLaw RecombinationBoundary.flatExecution [false] [0]),
    Lean.toJson (label (credit RecombinationBoundary.canonicalExecution)),
    Lean.toJson (label (credit RecombinationBoundary.flatExecution)),
    rat (WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (frame x))
      TemporalTransport.sourceAtCopy [] [FullInterface.observe (frame TemporalTransport.sourceAtCopy)]),
    rat (WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (frame x))
      (targetExecution false) [] [FullInterface.observe (frame TemporalTransport.sourceAtCopy)]),
    Lean.toJson [rat (Binding.emittedLaw (normalizedRows renewable) (fun x => publicLens x.resident.current)
      PublicShadow.beforeExecution [true] [2]),rat (Binding.emittedLaw (normalizedRows renewable)
      (fun x => publicLens x.resident.current) PublicShadow.afterExecution [true] [2])]]]
#eval snapshot.compress
"""


def evaluate():
    folder = ROOT / "lean/.validate-logs"
    probe = folder / "G28CountermodelsTranscriptionProbe.lean"
    probe.write_text(PROBE)
    run = subprocess.run(["lake","env","lean",str(probe)],cwd=ROOT/"lean",capture_output=True,text=True)
    (folder/"G28-countermodels-transcription-probe.log").write_text(run.stdout+run.stderr)
    if run.returncode: raise RuntimeError("Lean transcription failed; see G28-countermodels-transcription-probe.log")
    def decode(v):
        if isinstance(v,str): return v if v in {"self","other","neutral","rejected"} else F(v)
        if isinstance(v,list): return [decode(x) for x in v]
        return v
    return decode(json.loads(json.loads(run.stdout.strip())))


def main():
    actual,expected=evaluate(),reference()
    assert actual==expected,"G28 actual package/receipt/law/cyclic-readout drift"
    print(f"G28 transcription passed: target checkpoint/prefix, registered flat control, {len(actual[2])} ordered law queries,")
    print("16 original cycle edges; CURRENT aliases but 2 full-decoder boundaries fail; C6 positions 1 versus 0.")


if __name__ == "__main__": main()
