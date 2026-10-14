#!/usr/bin/env python3
"""Read-only, exact row check of CSTTT's T1 tables against sibling T1-L1.

Source: ../six-birds-consciousness/lab/sixbirds_consciousness/labs/
        t1_l1_self_wheel.py, especially lines 23-69, 85-178, 604-695,
        and 828-1013. No POS-04 model is read or evaluated.
"""

from __future__ import annotations

import ast
from fractions import Fraction
from pathlib import Path
import re
import subprocess
import sys
import tempfile


ROOT = Path(__file__).resolve().parents[1]
LEAN = ROOT / "lean/CSTTT/Objecthood/T1Audit.lean"
SIBLING = ROOT.parent / "six-birds-consciousness"


def lean_list(source: str, name: str) -> str:
    match = re.search(rf"\bdef {re.escape(name)}\b[^\n]*:=", source)
    if not match:
        raise ValueError(f"missing Lean table {name}")
    start = source.find("[", match.end())
    if start < 0:
        raise ValueError(f"missing list body for {name}")
    depth = 0
    for pos in range(start, len(source)):
        if source[pos] == "[":
            depth += 1
        elif source[pos] == "]":
            depth -= 1
            if depth == 0:
                return source[start : pos + 1]
    raise ValueError(f"unclosed list body for {name}")


def check_equal(name: str, actual: object, expected: object) -> None:
    if actual != expected:
        raise AssertionError(f"{name}: Lean {actual!r} != sibling {expected!r}")


def evaluated_matrices() -> dict[str, tuple[int, list[list[int]]]]:
    """Read the actual Lean definitions, including their computed entries."""
    probe = ["import CSTTT.Objecthood.T1Audit", "open CSTTT.Objecthood.T1Audit"]
    for name in ("P", "Peps", "CU"):
        probe.append(
            f'#eval ("{name}", {name}.den, '
            '(List.range 10).map (fun i => (List.range 10).map '
            f'(fun j => {name}.num (Fin.ofNat 10 i) (Fin.ofNat 10 j))))'
        )
    with tempfile.TemporaryDirectory(prefix="t1-transcription-") as scratch:
        path = Path(scratch) / "probe.lean"
        path.write_text("\n".join(probe) + "\n")
        result = subprocess.run(
            ["lake", "env", "lean", str(path)], cwd=ROOT / "lean",
            text=True, capture_output=True, check=True,
        )
    markers = list(re.finditer(r'^\("(?:P|Peps|CU)",', result.stdout, re.M))
    if len(markers) != 3:
        raise AssertionError(f"expected three tagged Lean matrix outputs: {result.stdout}")
    matrices: dict[str, tuple[int, list[list[int]]]] = {}
    for index, marker in enumerate(markers):
        end = markers[index + 1].start() if index + 1 < len(markers) else len(result.stdout)
        name, denominator, rows = ast.literal_eval(result.stdout[marker.start():end].strip())
        if name in matrices or denominator <= 0 or len(rows) != 10 or any(len(row) != 10 for row in rows):
            raise AssertionError(f"malformed Lean matrix {name}")
        matrices[name] = denominator, rows
    check_equal("Lean matrix names", set(matrices), {"P", "Peps", "CU"})
    return matrices


def main() -> None:
    source = LEAN.read_text()
    matrices = evaluated_matrices()
    sys.dont_write_bytecode = True
    sys.path.insert(0, str(SIBLING / "lab"))
    from sixbirds_consciousness.labs import t1_l1_self_wheel as t1

    kernel = tuple(s for s in t1.STATES if s in t1.EXPECTED_DEADLINE_KERNEL)
    labels = [s.label() for s in kernel]
    check_equal("kernel order", re.findall(r"\.p\dw\d", lean_list(source, "kernel")),
                ["." + x for x in labels])
    check_equal("CORE", re.findall(r"\.p\dw\d", lean_list(source, "core")),
                ["." + s.label() for s in t1.CORE])

    policy = t1.canonical_closed_loop_policy()
    source_actions = [policy[t1.canonical_predictive_class(s)] for s in kernel]
    check_equal("canonical policy",
                [x.removeprefix(".") for x in re.findall(r"\.(?:stay|cw|ccw)",
                                                       lean_list(source, "canonicalPolicy"))],
                source_actions)

    p_rows = ast.literal_eval(lean_list(source, "pRows"))
    check_equal("P shape", [len(row) for row in p_rows], [10] * 10)
    p_den, lean_p = matrices["P"]
    source_p = t1.canonical_closed_loop_matrix(kernel, policy)
    for i in range(10):
        for j in range(10):
            check_equal(f"P raw[{labels[i]},{labels[j]}]", p_rows[i][j], lean_p[i][j])
            check_equal(f"P[{labels[i]},{labels[j]}]", Fraction(lean_p[i][j], p_den),
                        source_p[i][j])

    classes = [t1.canonical_predictive_class(s) for s in kernel]
    seen: dict[object, int] = {}
    source_class_ids = [seen.setdefault(cls, len(seen)) for cls in classes]
    check_equal("canonical M classes", ast.literal_eval(lean_list(source, "mClasses")),
                source_class_ids)
    indicator, class_order = t1.canonical_class_indicator_matrix(kernel)
    prototype = t1.uniform_self_prototype_matrix(kernel, class_order)
    source_cu = t1._matrix_multiply(indicator, prototype)
    cu_den, lean_cu = matrices["CU"]
    for i in range(10):
        for j in range(10):
            check_equal(f"CU[{labels[i]},{labels[j]}]",
                        Fraction(lean_cu[i][j], cu_den), source_cu[i][j])

    check_equal("tau", t1.C1_STAGING_TAU, 2)
    check_equal("epsilon", t1.C1_PERTURBATION_EPSILON, Fraction(1, 16))
    check_equal("retention threshold", t1.C1_RETENTION_THRESHOLD, Fraction(3, 4))
    pe_match = re.search(
        r"def Peps : ScaledMatrix := ⟨(\d+), fun i j => (\d+) \* pNum i j \+ (\d+)⟩",
        source,
    )
    if not pe_match:
        raise AssertionError("Peps scaled mixture formula changed or is missing")
    pe_den, pe_mul, pe_add = map(int, pe_match.groups())
    lean_pe_den, lean_pe = matrices["Peps"]
    check_equal("Peps denominator", lean_pe_den, pe_den)
    source_pe = t1.perturb_closed_loop(source_p, kernel, t1.C1_PERTURBATION_EPSILON)
    for i in range(10):
        for j in range(10):
            check_equal(f"Peps formula[{labels[i]},{labels[j]}]",
                        lean_pe[i][j], pe_mul * p_rows[i][j] + pe_add)
            check_equal(f"Peps[{labels[i]},{labels[j]}]",
                        Fraction(lean_pe[i][j], lean_pe_den), source_pe[i][j])

    audit = t1.compute_closure_objecthood_audit()
    if not audit.passed:
        raise AssertionError("sibling published T1 C1 audit no longer passes")
    fixed = dict(audit.perturbation.unique_fixed_point or ())
    weights = ast.literal_eval(lean_list(source, "piWeights"))
    check_equal("pi shape", len(weights), 10)
    for i, state in enumerate(kernel):
        check_equal(f"pi[{labels[i]}]", Fraction(weights[i], 4960), fixed[state])
    check_equal("published CORE mass", audit.perturbation.core_mass, Fraction(77, 80))
    check_equal("published TV", audit.perturbation.total_variation_from_core_uniform,
                Fraction(3, 80))
    check_equal("published defect", audit.perturbation.idempotence_defect,
                Fraction(78795, 524288))
    print("T1 transcription PASS: 10 kernel states, 4 CORE states, 10 policies, "
          "100 P entries, 100 CU entries, 100 Peps entries, and 10 fixed masses")


if __name__ == "__main__":
    main()
