#!/usr/bin/env python3
"""Exact FULL-NATIVE-01 raw-row and computed-profile transcription.

The second step uses classFormula, whose equality to the actual computed first
profile is kernel-proved in PhysicalProfile; this avoids exponential re-evaluation.
This verifies values, not prose. It evaluates Lean and independently constructs
all raw rows from the frozen matrix and explicit primitive recipe. Future-law
theorems, physical account simulation and original-package assembly are separate.
"""
from __future__ import annotations

from copy import deepcopy
from itertools import product
import json
from pathlib import Path
import subprocess

ROOT = Path(__file__).resolve().parents[1]
MODEL = ROOT / "audit/proposed_models/G17-full-native-package.model.json"


def python_snapshot(data):
    states = list(product((False, True), repeat=5))
    kernels = [tuple(k) for k in data["primitive_dynamics"]["kernel_order"]]
    matrix = data["primitive_dynamics"]["inside_maintenance_weights"]
    if kernels != list(product((False, True), repeat=2)):
        raise AssertionError("frozen kernel order drift")
    if data["primitive_carrier"]["normalization"] != 16:
        raise AssertionError("frozen normalization drift")

    def lens(s):
        out, u, v, _, phase = s
        return 1 + 2 * (2 * int(u) + int(v)) + int(phase) if out else 0

    def row(s, action):
        out, u, v, replica, phase = s
        if action:
            return [[list((True, u, v, replica, not phase)), 16]]
        weights = [2] * 4 if out else matrix[kernels.index((u, v))]
        return [[list((False, x, y, r, not phase)), weights[k]]
                for k, (x, y) in enumerate(kernels) for r in (False, True)]

    rows = [[row(s, a) for a in (False, True)] for s in states]
    seed = [lens(s) for s in states]

    def refine(classes):
        signatures = []
        for i, _ in enumerate(states):
            signatures.append((classes[i], tuple(
                tuple(sum(w for target, w in action_row
                          if classes[states.index(tuple(target))] == b)
                      for b in range(32)) for action_row in rows[i])))
        ordered = list(dict.fromkeys(signatures))
        return [ordered.index(sig) for sig in signatures]

    first = refine(seed)
    second = refine(first)
    return [list(s) for s in states], rows, seed, first, second


def lean_snapshot():
    folder = ROOT / "lean/.validate-logs"
    probe = folder / "G18TranscriptionProbe.lean"
    probe.write_text("""import CSTTT.FullNative.PhysicalProfile
open CSTTT.FullNative
open CSTTT.TargetTheory.GenericHandoff
def encode (s : State) : List Bool := [s.outside,s.u,s.v,s.replica,s.phase]
def snapshot : Lean.Json := Lean.toJson
  (states.map encode,
   states.map (fun s => bits.map (fun a => (rows s a).map (fun e => (encode e.1,e.2)))),
   states.map publicLens, states.map (classes model),
   states.map (ProfileRules.step (profile model) classFormula))
#eval snapshot.compress
""")
    completed = subprocess.run(["lake", "env", "lean", str(probe)],
                               cwd=ROOT / "lean", check=True,
                               capture_output=True, text=True)
    (folder / "G18TranscriptionProbe.log").write_text(completed.stdout + completed.stderr)
    raw = json.loads(json.loads(completed.stdout.strip()))
    # Lean serializes nested products as nested two-element JSON arrays.
    return raw[0], raw[1][0], raw[1][1][0], raw[1][1][1][0], raw[1][1][1][1]


def compare(got, data):
    if tuple(got) != python_snapshot(data):
        raise AssertionError("Lean values differ from frozen raw recipe or independently computed refinement")


def main():
    data = json.loads(MODEL.read_text())
    got = lean_snapshot()
    compare(got, data)
    print("PASS full native transcription: 32 states, 64 raw rows, public seed, first and second refinement")
    for label, mutate in [
        ("maintenance weight", lambda d: d["primitive_dynamics"]["inside_maintenance_weights"][0].__setitem__(0, 2)),
        ("normalization", lambda d: d["primitive_carrier"].__setitem__("normalization", 8)),
        ("kernel enumeration", lambda d: d["primitive_dynamics"]["kernel_order"].reverse()),
    ]:
        broken = deepcopy(data)
        mutate(broken)
        try:
            compare(got, broken)
        except AssertionError:
            print("CAUGHT planted " + label + " drift")
        else:
            raise AssertionError("missed planted " + label + " drift")
    print("Coverage: physical rows/refinement only; all-word laws and account/history lifts are Lean obligations.")


if __name__ == "__main__":
    main()
