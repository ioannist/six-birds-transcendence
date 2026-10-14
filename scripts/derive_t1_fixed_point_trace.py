#!/usr/bin/env python3
"""Check the G6d-2a trace against a declared, deterministic algebraic rule.

Read T1Audit's kernel-computed E2eps via a temporary Lean probe. Normalize row
0, process columns in published order, choose the first nonzero pivot, scale
it to one, and eliminate each other row in order. Exact Fraction arithmetic;
no repository writes and no proposed-model evaluation.
"""
from __future__ import annotations

import ast
from fractions import Fraction
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def derive() -> list[str]:
    probe = """import CSTTT.Objecthood.T1Audit
open CSTTT.Objecthood.T1Audit
#eval E2eps.den
#eval (List.finRange 10).map fun i => (List.finRange 10).map fun j => E2eps.num i j
"""
    with tempfile.TemporaryDirectory(prefix="g6d2-t1-", dir="/tmp") as tmp:
        path = Path(tmp) / "probe.lean"
        path.write_text(probe)
        lines = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
            text=True, capture_output=True, check=True,
        ).stdout.splitlines()
    denominator = int(lines[0])
    rows = ast.literal_eval(" ".join(lines[1:]))
    if len(rows) != 10 or any(len(row) != 10 for row in rows):
        raise ValueError("T1 carrier shape differs from the published ten-state order")
    E = [[Fraction(n, denominator) for n in row] for row in rows]
    matrix = [[Fraction(1) if i == 0 else E[j][i] - int(i == j)
               for j in range(10)] for i in range(10)]
    operations: list[str] = []

    def rat(q: Fraction) -> str:
        return f"({q.numerator} / {q.denominator} : Rat)"

    for column in range(10):
        pivot = next(i for i in range(column, 10) if matrix[i][column])
        if pivot != column:
            matrix[column], matrix[pivot] = matrix[pivot], matrix[column]
            operations.append(f".swap {column} {pivot}")
        q = 1 / matrix[column][column]
        if q != 1:
            matrix[column] = [q * v for v in matrix[column]]
            operations.append(f".scale {column} {rat(q)}")
        for i in range(10):
            if i != column and matrix[i][column]:
                q = -matrix[i][column]
                matrix[i] = [v + q * w for v, w in zip(matrix[i], matrix[column])]
                operations.append(f".add {i} {column} {rat(q)}")
    return operations


def main() -> None:
    source = (ROOT / "lean/CSTTT/Targets/GenericHandoff/FixedPointT1.lean").read_text()
    block = source.split("def operations :", 1)[1].split("set_option", 1)[0]
    actual = re.findall(r"\.(?:swap \d+ \d+|scale \d+ \(-?\d+ / \d+ : Rat\)|"
                        r"add \d+ \d+ \(-?\d+ / \d+ : Rat\))", block)
    expected = derive()
    if actual != expected:
        raise SystemExit("FAIL: Lean trace differs from deterministic T1 reduction rule")
    print(f"PASS: {len(expected)} exact row operations match T1-derived rule")


if __name__ == "__main__":
    main()
