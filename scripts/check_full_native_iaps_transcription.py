#!/usr/bin/env python3
"""G29 shared provenance and actual package-autonomy obstruction readouts.

Reconstruct the frozen G27 ledger independently, compare all nine immediate
outcomes of each target and all 81 first paired outcomes. These finite checks
supplement the universal Lean path and controlled-invariant negatives.
"""
from __future__ import annotations
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
from check_full_native_package_transcription import PROBE as G27_PROBE, reference as package_reference

ROOT = Path(__file__).resolve().parents[1]


def reference():
    entries = package_reference()[0]
    source, left, right = [entry[0] for entry in entries]
    receipt = source[11][0]
    event = 3 + 4*receipt[2] + receipt[1]
    edges = []
    for target in (left, right):
        assert target[5] == [receipt[4]] and target[6] == [receipt[2]]
        assert receipt[0] == source[1] and receipt[1] == source[2]
        assert source[9][receipt[1]] == receipt[0] and receipt[4] == source[0]
        edges += [[source[1], event], [event, target[1]]]
    successors = []
    for entry in entries[1:]:
        branch = []
        for rows in entry[1]:
            action = []
            for data, weight in rows:
                closed = bool(data[11]) and data[11][0][4] == data[11][-1][3]
                assert not closed and data[12] == 'rejected'
                assert data[0][4] and data[4] == 7 and data[7][data[2]] == 7
                action.append([data, weight, closed])
            branch.append(action)
        successors.append(branch)

    def cell(data):
        return [data[0], data[1], data[2], data[4], data[5], data[6]]

    joint = []
    for a in range(2):
        for b in range(2):
            paired = []
            for p, n in entries[1][1][a]:
                for q, m in entries[2][1][b]:
                    cursors = list(left[7])
                    cursors[1], cursors[2] = p[7][1], q[7][2]
                    shape = [[None, cell(p), cell(q)], cursors, left[8], left[9], False, [False]*3]
                    paired.append([shape, n*m])
            assert sum(n for _, n in paired) == 256
            joint.append(paired)
    return [[source, left, right], edges, successors, joint, [False, True, True], [], []]


PROBE = G27_PROBE.split('def endpoints')[0].replace(
    'import CSTTT.FullNative.OriginalPackage', 'import CSTTT.FullNative.IAPSAdjudication') + r"""
def owners : List Owner := [0,1,2]
def tokens : List Token := [0,1,2,3]
def cell (p : Local) : Lean.Json := Lean.Json.arr #[Lean.toJson (encode p.current),
  Lean.toJson p.owner.val,Lean.toJson p.token.val,Lean.toJson p.receipts.length,
  Lean.toJson (p.rootedRoute.1.map encode),Lean.toJson p.rootedRoute.2]
def shape (w : World) : Lean.Json := Lean.Json.arr #[
  Lean.toJson (owners.map fun o => (w.carriers o).map cell),
  Lean.toJson (tokens.map w.accounts.portCursor),Lean.toJson (tokens.map w.accounts.charge),
  Lean.toJson (tokens.map fun t => (w.accounts.allocation t).map issuer),
  Lean.toJson w.bridge.isSome,Lean.toJson (owners.map fun o => (w.slots o).isSome)]
def nextRows (right : Bool) : Lean.Json := Lean.toJson (bits.map fun a =>
  Lean.toJson ((rawRows renewable (targetExecution right) a).map fun e =>
    Lean.Json.arr #[data e.1,Lean.toJson e.2,Lean.toJson (Credit.closedReceipts e.1.resident.receipts)]))
def pairedRows : Lean.Json := Lean.toJson (bits.flatMap fun a => bits.map fun b =>
  Lean.toJson ((jointRows renewable (targetRaw false).world a b).map fun e =>
    Lean.Json.arr #[shape e.1,Lean.toJson e.2]))
def snapshot : Lean.Json := Lean.Json.arr #[
  Lean.toJson [data TemporalTransport.sourceAtCopy,data (targetExecution false),data (targetExecution true)],
  Lean.toJson SharedAttribution.edges,Lean.toJson (bits.map nextRows),pairedRows,
  Lean.toJson (owners.map fun o => ((targetRaw false).world.carriers o).isSome),
  Lean.toJson (SharedAttribution.retainedEdges ⟨(targetRaw false).world,0⟩ (targetRaw false)),
  Lean.toJson (SharedAttribution.retainedEdges sourceRaw ⟨(targetRaw false).world,0⟩)]
#eval snapshot.compress
"""


def evaluate():
    folder = ROOT / 'lean/.validate-logs'
    probe = folder / 'G29IAPSTranscriptionProbe.lean'
    probe.write_text(PROBE)
    run = subprocess.run(['lake', 'env', 'lean', str(probe)], cwd=ROOT/'lean', capture_output=True, text=True)
    (folder/'G29-iaps-transcription-probe.log').write_text(run.stdout+run.stderr)
    if run.returncode:
        raise RuntimeError('Lean transcription failed; see G29-iaps-transcription-probe.log')
    def decode(value):
        if isinstance(value, str):
            return value if value in {'self','other','neutral','rejected'} else F(value)
        if isinstance(value, list):
            return [decode(x) for x in value]
        return value
    return decode(json.loads(json.loads(run.stdout.strip())))


def main():
    actual, expected = evaluate(), reference()
    assert actual == expected, 'G29 shared ancestry/native package/fusion readout drift'
    print('G29 transcription passed: 3 endpoints, 4 decoded edges, 18 rejected successors,')
    print('81 paired outcomes; withdrawn source remains absent, both parents retain distinct ownership; missing edges reject.')


if __name__ == '__main__':
    main()
