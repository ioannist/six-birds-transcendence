#!/usr/bin/env python3
"""Plant negative cases in /tmp and verify validator detection."""

from __future__ import annotations

import csv
import json
from pathlib import Path
import shutil
import subprocess
import tempfile
import importlib.util

ROOT = Path(__file__).resolve().parents[1]
VALIDATOR = ROOT / "scripts/validate_lean.sh"
SOURCE_REGISTRY = ROOT / "cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv"


def fixture(path: Path) -> None:
    (path / "cst-tt/registries").mkdir(parents=True)
    (path / "lean").mkdir()
    shutil.copytree(ROOT / "lean/CSTTT", path / "lean/CSTTT")
    shutil.copy2(SOURCE_REGISTRY, path / "cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv")
    shutil.copy2(ROOT / "lean/row_inventory.json", path / "lean/row_inventory.json")
    shutil.copy2(ROOT / "lean/trust_base.txt", path / "lean/trust_base.txt")


def run(path: Path, *, lean_project: Path | None = None) -> tuple[int, dict | None, str]:
    command = [str(VALIDATOR), "--root", str(path), "--lean-project", str(lean_project or ROOT / "lean"),
               "--skip-build", "--fixture-row", "TTH-01"]
    result = subprocess.run(command, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    reports = sorted((path / "lean/.validate-logs").glob("run-*/report.json"))
    report = json.loads(reports[-1].read_text()) if reports else None
    return result.returncode, report, result.stdout


def change_registry(path: Path, field: str, replacement: str, *, regenerate: bool = True) -> None:
    registry = path / "cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv"
    with registry.open(newline="") as stream:
        reader = csv.DictReader(stream)
        columns = reader.fieldnames
        rows = list(reader)
    assert columns is not None
    assert rows[0]["theorem_id"] == "TTH-01"
    rows[0][field] = replacement
    with registry.open("w", newline="") as stream:
        writer = csv.DictWriter(stream, fieldnames=columns)
        writer.writeheader()
        writer.writerows(rows)
    if regenerate:
        result = subprocess.run([str(VALIDATOR), "--root", str(path), "--write-inventory"], text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        if result.returncode:
            raise RuntimeError(result.stdout)


def local_lean_project(path: Path) -> Path:
    project = path / "lean"
    shutil.copy2(ROOT / "lean/CSTTT.lean", project / "CSTTT.lean")
    shutil.copy2(ROOT / "lean/lean-toolchain", project / "lean-toolchain")
    (project / "lakefile.toml").write_text('name = "CSTTTFixture"\nversion = "0.1.0"\ndefaultTargets = ["CSTTT"]\n[[lean_lib]]\nname = "CSTTT"\n')
    result = subprocess.run(["lake", "build"], cwd=project, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode:
        raise AssertionError(f"temporary Lean build failed:\n{result.stdout[-4000:]}")
    return project


def parser_cases() -> list[str]:
    spec = importlib.util.spec_from_file_location("csttt_audit", ROOT / "scripts/validate_lean.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    a = "CSTTT.PackageTheory.acyclicLocalWitnessGluing"
    b = "CSTTT.Prospects.DetachedCopyCountermodel"
    forged = (f'"AUDIT_START|{a}"\n{b} : Prop\n'
              f"'{b}' does not depend on any axioms\nAUDIT_KIND|{b}|definition|true\n"
              f'"AUDIT_END|{a}"\n')
    result = module.parse_probe(forged, [a], set())[a]
    if result["resolved"] or not any("attribution mismatch" in e for e in result["errors"]):
        raise AssertionError("mis-attributed block was accepted")
    incomplete = module.parse_probe(f'"AUDIT_START|{a}"\n{a} : Prop\n', [a], set())[a]
    if incomplete["resolved"] or not any("missing end marker" in e for e in incomplete["errors"]):
        raise AssertionError("incomplete block was accepted")
    wrapped = (f'"AUDIT_START|{a}"\n{a} : Prop\n'
               f"'{a}' depends on axioms: [propext,\n Classical.choice,\n Quot.sound]\n"
               f'AUDIT_KIND|{a}|theorem|true\n"AUDIT_END|{a}"\n')
    parsed = module.parse_probe(wrapped, [a], {"propext", "Classical.choice", "Quot.sound"})[a]
    if not parsed["resolved"] or not parsed["axiom_reported"] or parsed["untrusted_axioms"]:
        raise AssertionError("wrapped trusted axiom list was not attributed and parsed")
    comments = module.strip_lean_comments(
        "x /- outer sorry /- nested axiom -/ admit -/ theorem PlantedAfterComment : True := by sorry\n"
        "-- axiom sorry\n")
    if "nested axiom" in comments or "outer sorry" in comments or "by sorry" not in comments or "-- axiom" in comments:
        raise AssertionError("nested/inline comment stripping failed")
    return ["PASS mis-attributed probe block: #check, axioms, and kind named another declaration",
            "PASS incomplete probe block: missing end marker rejected",
            "PASS wrapped #print axioms: attributed and parsed across continuation lines",
            "PASS nested and inline comments: comment tokens removed, following sorry retained"]


def marker_cases(base: Path) -> list[str]:
    spec = importlib.util.spec_from_file_location("csttt_marker_audit", ROOT / "scripts/validate_lean.py")
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    name = "CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeReceiptExtensionPrototype.canonical_other_source_false"
    single = base / "marker_single.lean"
    single.write_text(module.make_probe([name]))
    result = subprocess.run(["lake", "env", "lean", str(single)], cwd=ROOT / "lean",
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    parsed = module.parse_probe(result.stdout, [name], {"propext", "Quot.sound", "Classical.choice"})[name]
    if result.returncode or not parsed["resolved"] or not parsed["axiom_reported"] or parsed["untrusted_axioms"]:
        raise AssertionError(f"direct-marker declaration probe failed:\n{result.stdout}")
    # The 2888-declaration integration crashed in the old marker evaluator.
    # Exercise over twice as many delimiter pairs, checking every exact message.
    count = 6000
    scale = base / "marker_scale.lean"
    expected = [s for index in range(count) for s in
                (f'"AUDIT_START|marker_{index}"', f'"AUDIT_END|marker_{index}"')]
    scale.write_text("import Lean\n" + module.KIND_COMMAND + "\n" +
                     "\n".join(f"#audit_marker {message}" for message in expected) + "\n")
    result = subprocess.run(["lake", "env", "lean", str(scale)], cwd=ROOT / "lean",
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    if result.returncode or result.stdout.splitlines() != expected:
        raise AssertionError(f"large marker probe failed (exit {result.returncode}):\n{result.stdout[-4000:]}")
    return ["PASS direct markers: actual declaration, kind and trusted axiom attribution",
            "PASS direct markers at scale: all 12000 delimiters match without interpreter recursion"]


def main() -> None:
    with tempfile.TemporaryDirectory(prefix="csttt_l2_selftest_", dir="/tmp") as tmp:
        base = Path(tmp)
        cases = ["sorry", "custom axiom", "def True", "constant function", "missing registry name", "Prop definition as evidence",
                 "transitive untrusted axiom", "exact_statement inventory drift", "status_09 inventory drift",
                 "ceiling_09 inventory drift", "sorry after inline comment"]
        for index, case in enumerate(cases, start=1):
            path = base / f"case_{index}"
            fixture(path)
            source = path / "lean/CSTTT/Core/Finite.lean"
            if case == "sorry":
                source.write_text(source.read_text() + "\ntheorem PlantedSorry : True := by sorry\n")
            elif case == "custom axiom":
                source.write_text(source.read_text() + "\naxiom planted_custom_axiom : False\n")
            elif case == "def True":
                source.write_text(source.read_text() + "\ndef PlantedConstant : Prop := True\n")
            elif case == "constant function":
                source.write_text(source.read_text() +
                    "\ndef PlantedConstFunA : Nat → Prop := fun _ => True\n"
                    "def PlantedConstFunB : Nat → Nat → Prop := fun _ _ => False\n"
                    "def PlantedConstFunC : Nat → Prop := fun (_ : Nat) => True\n")
            elif case == "missing registry name":
                change_registry(path, "kernel_evidence", "CSTTT.PackageTheory.thisNameDoesNotExist")
            elif case == "Prop definition as evidence":
                change_registry(path, "kernel_evidence", "CSTTT.Prospects.DetachedCopyCountermodel")
            elif case == "transitive untrusted axiom":
                source.write_text(source.read_text() +
                    "\nnamespace CSTTT\naxiom planted_transitive_axiom : True\n"
                    "theorem PlantedTransitive : True := planted_transitive_axiom\nend CSTTT\n")
                change_registry(path, "kernel_evidence", "CSTTT.PlantedTransitive")
            elif case == "exact_statement inventory drift":
                change_registry(path, "exact_statement", "Planted statement edit without inventory regeneration.", regenerate=False)
            elif case == "status_09 inventory drift":
                change_registry(path, "status_09", "conditional", regenerate=False)
            elif case == "ceiling_09 inventory drift":
                change_registry(path, "ceiling_09", "Planted ceiling edit.", regenerate=False)
            elif case == "sorry after inline comment":
                source.write_text(source.read_text() + "\n/- inline -/ theorem PlantedInlineSorry : True := by sorry\n")
            project = local_lean_project(path) if case == "transitive untrusted axiom" else None
            code, report, output = run(path, lean_project=project)
            if report is None:
                raise AssertionError(f"{case}: validator did not write JSON\n{output}")
            if case == "sorry":
                evidence = [f for f in report["findings"] if f["pattern"] == "sorry" and "PlantedSorry" in f["text"]]
                proof = f"{evidence[0]['location']}: {evidence[0]['text']}" if evidence else ""
            elif case == "custom axiom":
                evidence = [f for f in report["findings"] if f["pattern"] == "axiom" and "planted_custom_axiom" in f["text"]]
                proof = f"{evidence[0]['location']}: {evidence[0]['text']}" if evidence else ""
            elif case == "def True":
                evidence = [f for f in report["findings"] if f["pattern"] == "constant True" and "PlantedConstant" in f["text"]]
                proof = f"{evidence[0]['location']}: {evidence[0]['text']}" if evidence else ""
            elif case == "constant function":
                planted = [f for f in report["findings"] if "PlantedConstFun" in f["text"]]
                names = {name for name in ("PlantedConstFunA", "PlantedConstFunB", "PlantedConstFunC")
                         if any(name in f["text"] and f["tier"] == "high-confidence" and f["pattern"].startswith("constant function ") for f in planted)}
                leads = [f for f in planted if f["tier"] == "heuristic lead"]
                proof = f"{', '.join(sorted(names))}: high-confidence; ignored-input leads={len(leads)}" if len(names) == 3 and not leads else ""
            elif case == "missing registry name":
                evidence = [i for i in report["issues"] if "unresolved declaration: CSTTT.PackageTheory.thisNameDoesNotExist" in i]
                proof = evidence[0] if evidence else ""
            elif case == "Prop definition as evidence":
                row = next(r for r in report["rows"] if r["row_id"] == "TTH-01")
                evidence = [i for i in report["issues"] if "row TTH-01 has statement-only" in i]
                proof = f"TTH-01 theorem={row['rollup']['theorem_kind']} statement-only={row['rollup']['statement_only']}; {evidence[0]}" if evidence and row["rollup"]["statement_only"] == 1 else ""
            elif case == "transitive untrusted axiom":
                declaration = report["declarations"].get("CSTTT.PlantedTransitive", {})
                evidence = [i for i in report["issues"] if "untrusted axioms in CSTTT.PlantedTransitive" in i]
                proof = f"#print axioms CSTTT.PlantedTransitive = {declaration.get('axioms')}; {evidence[0]}" if evidence and "CSTTT.planted_transitive_axiom" in declaration.get("untrusted_axioms", []) else ""
            elif case in ("exact_statement inventory drift", "status_09 inventory drift", "ceiling_09 inventory drift"):
                evidence = [i for i in report["issues"] if "generated inventory disagrees" in i]
                proof = f"inventory_match={report['inventory_match']}; {evidence[0]}" if evidence and not report["inventory_match"] else ""
            else:
                evidence = [f for f in report["findings"] if f["pattern"] == "sorry" and "PlantedInlineSorry" in f["text"]]
                proof = f"{evidence[0]['location']}: {evidence[0]['text']}" if evidence else ""
            if code == 0 or not proof:
                raise AssertionError(f"{case}: negative not caught (exit {code})\n{output}")
            print(f"PASS {case}: {proof}", flush=True)
        for line in parser_cases():
            print(line, flush=True)
        for line in marker_cases(base):
            print(line, flush=True)
    print("All planted negatives caught; fixture removed from /tmp.")


if __name__ == "__main__":
    main()
