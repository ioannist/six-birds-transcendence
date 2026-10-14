#!/usr/bin/env python3
"""Full32-state C1 audit; export uses kernel-proved matrix acceleration formulas."""
from copy import deepcopy
from fractions import Fraction as F
import json
from pathlib import Path
import subprocess
from check_full_native_transcription import python_snapshot

ROOT = Path(__file__).resolve().parents[1]


def multiply(a, b):
    return [[sum((a[i][k] * b[k][j] for k in range(32)), F(0))
             for j in range(32)] for i in range(32)]


def expected():
    data = json.loads((ROOT / "audit/proposed_models/G17-full-native-package.model.json").read_text())
    states, rows, _, classes, _ = python_snapshot(data)
    groups = [[i for i, c in enumerate(classes) if c == k] for k in dict.fromkeys(classes)]
    prototypes = [states[g[0]] for g in groups]
    P = [[sum((F(n, 16) for target, n in rows[i][0] if target == t), F(0))
          for t in states] for i in range(32)]
    C = [[F(classes[i] == k) for k in range(16)] for i in range(32)]
    U = [[F(1, len(g)) if i in g else F(0) for i in range(32)] for g in groups]
    CU = [[F(1, sum(c == classes[i] for c in classes)) if classes[i] == classes[j] else F(0)
           for j in range(32)] for i in range(32)]
    closure, squares, stationary, retention, tv, defects = [], [], [], [], [], []
    for e in (F(0), F(1, 16)):
        A = [[(1 - e) * p + e / 32 for p in row] for row in P]
        A2 = multiply(A, A)
        E1, E2 = multiply(A, CU), multiply(A2, CU)
        for E in (E1, E2):
            E_square = multiply(E, E)
            closure.append(E)
            squares.append(E_square)
            defects.append(max(sum(abs(q - p) for p, q in zip(row, second)) / 2
                               for row, second in zip(E, E_square)))
        # Solve the actual normalized stationary linear system independently.
        system = [[A[j][i] - F(i == j) for j in range(32)] + [F(0)] for i in range(32)]
        system[0] = [F(1)] * 33
        for i in range(32):
            pivot = next(j for j in range(i, 32) if system[j][i])
            system[i], system[pivot] = system[pivot], system[i]
            divisor = system[i][i]
            system[i] = [x / divisor for x in system[i]]
            for j in range(32):
                if j != i:
                    multiplier = system[j][i]
                    system[j] = [x - multiplier * y for x, y in zip(system[j], system[i])]
        pi = [row[-1] for row in system]
        assert sum(pi) == 1 and all(p >= 0 for p in pi)
        assert [sum(pi[i] * A[i][j] for i in range(32)) for j in range(32)] == pi
        stationary.append(pi)
        retention.append(sum(pi[i] for i, s in enumerate(states) if not s[0]))
        tv.append(sum(abs(p - (F(0) if s[0] else F(1, 16))) for s, p in zip(states, pi)) / 2)
    phase = [[2 * stationary[0][i] if s[4] == tick else F(0)
              for i, s in enumerate(states)] for tick in (False, True)]
    assert phase[0] != phase[1] and all(sum(p) == 1 for p in phase)
    for p in phase:
        assert [sum(p[i] * closure[1][i][j] for i in range(32)) for j in range(32)] == p
    return [prototypes, classes, C, U, P, CU, closure, squares, stationary, retention, tv, defects, phase]


def evaluated():
    folder = ROOT / "lean/.validate-logs"
    probe = folder / "G21ObjecthoodTranscriptionProbe.lean"
    probe.write_text("""import CSTTT.FullNative.ObjecthoodDefect
open CSTTT.FullNative CSTTT.FullNative.Objecthood
def encode (s : State) : List Bool := [s.outside,s.u,s.v,s.replica,s.phase]
def rat (x : Rat) : Lean.Json := Lean.toJson (toString x)
def vector (x : State → Rat) : Lean.Json := Lean.toJson (states.map fun s => rat (x s))
def matrix (P : State → State → Rat) : Lean.Json := Lean.toJson (states.map fun s => states.map fun t => rat (P s t))
def value (p t : Bool) := if t then two p else perturbed p
def squaredValue (p t : Bool) := if t then four p else two p
def optimizedDefect (p t : Bool) : Rat :=
  (states.map fun s => ((states.map fun k => absRat (squaredValue p t s k-value p t s k)).sum)/2).foldl max 0
def snapshot : Lean.Json := Lean.Json.arr #[
  Lean.toJson ((states.filter fun s => !s.replica).map encode),
  Lean.toJson (states.map classFormula),
  Lean.toJson (states.map fun s => (List.range 16).map fun k => rat (if classFormula s=k then 1 else 0)),
  Lean.toJson ((List.range 16).map fun k => states.map fun s => rat (if classFormula s=k then 1/2 else 0)),
  matrix P,
  matrix (fun s t => if eraseReplica s=eraseReplica t then 1/2 else 0),
  Lean.toJson (bits.flatMap fun p => bits.map fun t => matrix (value p t)),
  Lean.toJson (bits.flatMap fun p => bits.map fun t => matrix (squaredValue p t)),
  Lean.toJson (bits.map fun p => vector (stationary p)),
  Lean.toJson (bits.map fun p => rat ((core.map (stationary p)).sum)),
  Lean.toJson (bits.map fun p => rat (stationaryTV p)),
  Lean.toJson (bits.flatMap fun p => bits.map fun t => rat (optimizedDefect p t)),
  Lean.toJson (bits.map fun p => vector (phaseLaw p))]
#eval snapshot.compress
""")
    run = subprocess.run(["lake", "env", "lean", str(probe)], cwd=ROOT / "lean",
                         check=True, capture_output=True, text=True)
    (folder / "G21ObjecthoodTranscriptionProbe.log").write_text(run.stdout + run.stderr)
    values = json.loads(json.loads(run.stdout.strip()))
    def decode(value):
        if isinstance(value, str):
            return F(value)
        if isinstance(value, list):
            return [decode(x) for x in value]
        return value
    return decode(values)


def main():
    actual, reference = evaluated(), expected()
    assert actual == reference, "physical C1 derived matrices/readouts differ from independent raw reconstruction"
    print("PASS full32 C1: derived prototypes/classes/C/U/CU, all4 closure and squared matrices, stationary laws, retention/TV/defects, phase counterexample")
    for label, mutation in [("clock phase", lambda x: x[6][0][0].__setitem__(0, F(1))),
                            ("perturb-before-power", lambda x: x[6][3][0].__setitem__(0, F(1))),
                            ("stationary mass", lambda x: x[8][1].__setitem__(0, F(0)))]:
        broken = deepcopy(reference)
        mutation(broken)
        assert actual != broken, "missed planted " + label + " drift"
        print("CAUGHT planted " + label + " drift")


if __name__ == "__main__":
    main()
