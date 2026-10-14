#!/usr/bin/env python3
"""CSV-derived, per-declaration Lean audit. Run via scripts/validate_lean.sh."""

from __future__ import annotations

import argparse
import csv
from datetime import datetime, timezone
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
REQUIRED_COLUMNS = {"theorem_id", "final_status", "formal_declarations", "claim_ceiling",
                    "exact_statement", "cst_tt_08_status", "l3_verdict", "kernel_evidence",
                    "status_09", "ceiling_09", "delta_rationale"}
DECL_RE = re.compile(r"^CSTTT(?:\.[A-Za-z_][A-Za-z_0-9']*)+$")
PLACEHOLDER_RE = re.compile(r"\b(sorry|admit|native_decide|implemented_by|opaque|axiom)\b")
DIRECT_CONSTANT_RE = re.compile(
    r"^\s*(?:def|abbrev)\s+([A-Za-z_][\w']*)\b.*:=\s*(True|False)\b"
)
CONSTANT_FUNCTION_RE = re.compile(
    r"\bfun\s+(?:(?:_|\([^)]*\))\s*)+=>\s*(True|False)\b"
)
IGNORED_ARGUMENT_RE = re.compile(r"\bfun\s+_\s*=>|\(_\s*:\s*[^)]+\)")
DECL_LINE_RE = re.compile(r"^\s*(?:def|abbrev)\s+([A-Za-z_][\w']*)\b")
AXIOMS_RE = re.compile(r"depends on axioms:\s*\[([^]]*)\]")
KIND_RE = re.compile(r"AUDIT_KIND\|([^|]+)\|([^|]+)\|(true|false)")
MARKER_RE = re.compile(r'^"AUDIT_(START|END)\|([^"\s]+)"$')
CHECK_RE = re.compile(r"^(CSTTT(?:\.[A-Za-z_][A-Za-z_0-9']*)+)(?=\s|:|$)")
AXIOM_LINE_RE = re.compile(r"^'([^']+)' (does not depend on any axioms|depends on axioms:.*)$")
THEOREM_TRUE_RE = re.compile(r"^\s*(?:theorem|lemma)\s+[A-Za-z_][\w']*\b[^\n]*:\s*True\b")

KIND_COMMAND = r'''
open Lean Elab Command Meta
-- Audit delimiters are syntax messages, not executable evidence. Emitting
-- them directly avoids thousands of generated #eval interpreter closures.
elab "#audit_marker " marker:str : command => do
  logInfo m!"\"{marker.getString}\""
elab "#audit_kind " ident:ident : command => do
  let env ← getEnv
  let name := ident.getId
  match env.find? name with
  | none => logInfo m!"AUDIT_KIND|{name}|missing|false"
  | some info =>
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .axiomInfo _ => "axiom"
      | .opaqueInfo _ => "opaque"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient"
    let propSort ← liftTermElabM do
      forallTelescopeReducing info.type fun _ body => do
        let body ← whnf body
        pure (body == mkSort Level.zero)
    logInfo m!"AUDIT_KIND|{name}|{kind}|{propSort}"
'''


def read_rows(csv_path: Path) -> list[dict]:
    with csv_path.open(newline="", encoding="utf-8") as stream:
        reader = csv.DictReader(stream)
        if not reader.fieldnames or not REQUIRED_COLUMNS <= set(reader.fieldnames):
            raise ValueError(f"registry missing columns: {sorted(REQUIRED_COLUMNS)}")
        rows = []
        seen_ids = set()
        for line, source in enumerate(reader, start=2):
            row_id = source["theorem_id"].strip()
            names = [name.strip() for name in source["kernel_evidence"].split(";")]
            if not row_id or row_id in seen_ids or not names or any(not DECL_RE.fullmatch(n) for n in names):
                raise ValueError(f"invalid or duplicate row/declaration at {csv_path}:{line}")
            if len(names) != len(set(names)):
                raise ValueError(f"duplicate declaration at {csv_path}:{line}")
            seen_ids.add(row_id)
            rows.append({"row_id": row_id, "status": source["status_09"].strip(),
                "exact_statement": source["exact_statement"], "claim_ceiling": source["ceiling_09"],
                "cst_tt_08_status": source["cst_tt_08_status"],
                "l3_verdict": source["l3_verdict"], "delta_rationale": source["delta_rationale"],
                "declarations": names})
    if len(rows) != 39:
        raise ValueError(f"expected 39 registry rows, found {len(rows)}")
    return rows


def inventory_for(rows: list[dict]) -> dict:
    return {"schema": "csttt-row-inventory-v3", "rows": rows}


def write_json(path: Path, value: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")


def strip_lean_comments(source: str) -> str:
    """Erase line and nested block comments, preserving offsets and newlines."""
    out = list(source)
    depth = 0
    line_comment = False
    in_string = False
    escaped = False
    i = 0
    while i < len(source):
        pair = source[i:i + 2]
        char = source[i]
        if line_comment:
            if char == "\n":
                line_comment = False
            else:
                out[i] = " "
        elif depth:
            if pair == "/-":
                depth += 1
                out[i:i + 2] = "  "
                i += 2
                continue
            if pair == "-/":
                depth -= 1
                out[i:i + 2] = "  "
                i += 2
                continue
            if char != "\n":
                out[i] = " "
        elif in_string:
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                in_string = False
        elif pair == "--":
            line_comment = True
            out[i:i + 2] = "  "
            i += 2
            continue
        elif pair == "/-":
            depth = 1
            out[i:i + 2] = "  "
            i += 2
            continue
        elif char == '"':
            in_string = True
        i += 1
    return "".join(out)


def scan_sources(root: Path) -> list[dict]:
    findings = []
    source_dir = root / "lean/CSTTT"
    if not source_dir.is_dir():
        raise ValueError(f"missing source directory: {source_dir}")
    for path in sorted(source_dir.rglob("*.lean")):
        original_lines = path.read_text(encoding="utf-8").splitlines()
        lines = strip_lean_comments("\n".join(original_lines)).splitlines()
        relative = path.relative_to(root).as_posix()
        for number, line in enumerate(lines, start=1):
            location = f"{relative}:{number}"
            original = original_lines[number - 1].strip()
            for match in PLACEHOLDER_RE.finditer(line):
                findings.append({"category": "placeholder", "tier": "gating", "pattern": match.group(1), "location": location, "text": original})
            direct = DIRECT_CONSTANT_RE.search(line)
            if direct:
                findings.append({"category": "vacuity", "tier": "high-confidence", "pattern": f"constant {direct.group(2)}", "location": location, "text": original})
            if THEOREM_TRUE_RE.search(line):
                findings.append({"category": "vacuity", "tier": "high-confidence", "pattern": "theorem True", "location": location, "text": original})
            declaration = DECL_LINE_RE.search(line)
            if declaration:
                preview = line
                if ":=" in line and not line.split(":=", 1)[1].strip() and number < len(lines):
                    preview += "\n" + lines[number]
                    if lines[number].rstrip().endswith("=>") and number + 1 < len(lines):
                        preview += "\n" + lines[number + 1]
                constant_function = CONSTANT_FUNCTION_RE.search(preview)
                if constant_function:
                    findings.append({"category": "vacuity", "tier": "high-confidence", "pattern": f"constant function {constant_function.group(1)}", "location": location, "text": original})
                elif not direct and IGNORED_ARGUMENT_RE.search(preview):
                    findings.append({"category": "vacuity", "tier": "heuristic lead", "pattern": "ignored input", "location": location, "text": original})
    return findings


def make_probe(names: list[str]) -> str:
    lines = ["import Lean", "import CSTTT", KIND_COMMAND]
    for name in names:
        lines.extend((
            f'#audit_marker "AUDIT_START|{name}"',
            f"#check {name}",
            f"#print axioms {name}",
            f"#audit_kind {name}",
            f'#audit_marker "AUDIT_END|{name}"',
        ))
    return "\n".join(lines) + "\n"


def axiom_messages(block: list[str]) -> list[tuple[str, str]]:
    """Collect Lean's possibly wrapped #print axioms message per declaration."""
    messages = []
    index = 0
    while index < len(block):
        match = AXIOM_LINE_RE.match(block[index])
        if match:
            name, body = match.groups()
            if body.startswith("depends on axioms:") and "]" not in body:
                while index + 1 < len(block):
                    following = block[index + 1].strip()
                    if not following or AXIOM_LINE_RE.match(following) or KIND_RE.fullmatch(following):
                        break
                    index += 1
                    body += " " + following
                    if "]" in following:
                        break
            messages.append((name, body))
        index += 1
    return messages


def parse_probe(output: str, names: list[str], trusted: set[str]) -> dict[str, dict]:
    blocks: dict[str, list[str]] = {}
    block_errors: dict[str, list[str]] = {name: [] for name in names}
    complete = set()
    current = None
    for line in output.splitlines():
        marker = MARKER_RE.fullmatch(line.strip())
        if marker and marker.group(1) == "START":
            name = marker.group(2)
            if current is not None:
                block_errors.setdefault(current, []).append(f"start for {name} before end for {current}")
            if name in blocks:
                block_errors.setdefault(name, []).append("duplicate start marker")
            blocks[name] = []
            current = name
        elif marker and marker.group(1) == "END":
            name = marker.group(2)
            if current != name:
                block_errors.setdefault(name, []).append(f"end marker for {name} without matching start")
                if current is not None:
                    block_errors.setdefault(current, []).append(f"end marker names {name}, expected {current}")
            else:
                complete.add(name)
            current = None
        elif current is not None:
            blocks[current].append(line)
    if current is not None:
        block_errors.setdefault(current, []).append("missing end marker")
    results = {}
    for name in names:
        block = blocks.get(name, [])
        errors = list(block_errors.get(name, [])) + [line for line in block if "error:" in line]
        if name not in blocks:
            errors.append("missing start marker")
        if name not in complete:
            errors.append("incomplete probe block")
        checks = [match.group(1) for line in block if (match := CHECK_RE.match(line))]
        axiom_lines = axiom_messages(block)
        kinds = [match for line in block if (match := KIND_RE.fullmatch(line))]
        for label, messages in (("#check", checks),
                                ("#print axioms", [m[0] for m in axiom_lines]),
                                ("kind", [m.group(1) for m in kinds])):
            if messages != [name]:
                errors.append(f"{label} attribution mismatch: expected [{name}], got {messages}")
        kind_match = kinds[0] if len(kinds) == 1 and kinds[0].group(1) == name else None
        kind = kind_match.group(2) if kind_match else "unknown"
        prop_sort = kind_match.group(3) == "true" if kind_match else False
        axiom_line = axiom_lines[0][1] if len(axiom_lines) == 1 and axiom_lines[0][0] == name else ""
        axiom_match = AXIOMS_RE.search(axiom_line)
        no_axioms = axiom_line == "does not depend on any axioms"
        axioms = sorted(set(a.strip() for a in axiom_match.group(1).split(",") if a.strip())) if axiom_match else []
        axiom_reported = bool(axiom_match or no_axioms)
        results[name] = {
            "resolved": not errors and kind not in ("unknown", "missing"),
            "kind": kind,
            "statement_only": kind == "definition" and prop_sort,
            "axioms": axioms,
            "axiom_reported": axiom_reported,
            "untrusted_axioms": sorted(set(axioms) - trusted),
            "errors": errors,
        }
    return results


def render(report: dict) -> str:
    out = ["ROW      STATUS                       THM  STMT  OTHER  PROBE  AXIOMS", "-" * 73]
    for row in report["rows"]:
        counts = row["rollup"]
        out.append(f"{row['row_id']:<8} {row['status']:<28} {counts['theorem_kind']:>3}  {counts['statement_only']:>4}  {counts['other_definitions']:>5}  {row['probe_status']:<5}  {row['axiom_status']}")
    totals = report["totals"]
    out.append("-" * 73)
    out.append(f"TOTALS   {totals['rows']} rows; {totals['declarations']} row declarations; {totals['theorem_kind']} theorem-kind; {totals['statement_only']} statement-only; {totals['other_definitions']} other definitions")
    out.append(f"BUILD    {report['build']['status']}")
    out.append(f"AXIOMS   trusted={','.join(report['trust_base'])}; untrusted={','.join(report['untrusted_axioms']) or 'none'}")
    out.append(f"INVENTORY {'MATCH' if report['inventory_match'] else 'MISMATCH'}")
    scan = report["scan_summary"]
    out.append(f"SCANS    heuristic source scan: placeholders={scan['placeholders']} (gating), high-confidence vacuity={scan['high_confidence']} (gating), ignored-input leads={scan['heuristic_leads']} (reported only)")
    for finding in report["findings"]:
        out.append(f"  {finding['tier']} {finding['category']} {finding['pattern']} {finding['location']}: {finding['text']}")
    for issue in report["issues"]:
        out.append(f"ISSUE    {issue}")
    out.append(f"OVERALL  {report['overall']}")
    return "\n".join(out) + "\n"


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--root", type=Path, default=ROOT, help="repository root (fixtures only)")
    parser.add_argument("--lean-project", type=Path, help="alternate compiled Lean project (fixtures only)")
    parser.add_argument("--skip-build", action="store_true", help="fixture probe mode; never reports full validation")
    parser.add_argument("--fixture-row", help="probe one row in skip-build fixture mode")
    parser.add_argument("--write-inventory", action="store_true", help="regenerate lean/row_inventory.json from the CSV")
    args = parser.parse_args()
    if args.fixture_row and not args.skip_build:
        parser.error("--fixture-row requires --skip-build")
    root = args.root.resolve()
    project = (args.lean_project or root / "lean").resolve()
    registry = root / "cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv"
    inventory_path = root / "lean/row_inventory.json"
    trust_path = root / "lean/trust_base.txt"
    try:
        rows = read_rows(registry)
        expected = inventory_for(rows)
        if args.write_inventory:
            write_json(inventory_path, expected)
            print(f"Wrote {inventory_path}: {len(rows)} rows, {sum(len(r['declarations']) for r in rows)} declaration entries")
            return 0
        actual = json.loads(inventory_path.read_text(encoding="utf-8"))
        inventory_match = actual == expected
        trusted = {line.strip() for line in trust_path.read_text(encoding="utf-8").splitlines() if line.strip() and not line.lstrip().startswith("#")}
        required_trust = {"propext", "Quot.sound", "Classical.choice"}
        if trusted != required_trust:
            raise ValueError(f"trust base must be exactly {sorted(required_trust)}; found {sorted(trusted)}")
        findings = scan_sources(root)
    except (OSError, ValueError, json.JSONDecodeError) as exc:
        print(f"AUDIT ERROR: {exc}", file=sys.stderr)
        return 2

    log_root = root / "lean/.validate-logs"
    run_dir = log_root / datetime.now(timezone.utc).strftime("run-%Y%m%dT%H%M%S-%fZ")
    run_dir.mkdir(parents=True, exist_ok=False)
    audited_rows = [row for row in rows if row["row_id"] == args.fixture_row] if args.fixture_row else rows
    if not audited_rows:
        print(f"AUDIT ERROR: unknown fixture row {args.fixture_row}", file=sys.stderr)
        return 2
    names = list(dict.fromkeys(name for row in audited_rows for name in row["declarations"]))
    (run_dir / "probe.lean").write_text(make_probe(names), encoding="utf-8")
    build = {"status": "skipped (fixture mode)", "exit_code": None}
    if not args.skip_build:
        result = subprocess.run(["lake", "build"], cwd=project, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        (run_dir / "build.log").write_text(result.stdout, encoding="utf-8")
        build = {"status": "pass" if result.returncode == 0 else "fail", "exit_code": result.returncode}
    # Large declaration inventories also execute the kind-inspection elaborator.
    # Give this subprocess a 64 MiB worker stack; proof/trust options are unchanged.
    probe = subprocess.run(["lake", "env", "lean", "-s", "65536", str(run_dir / "probe.lean")], cwd=project, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (run_dir / "probe.log").write_text(probe.stdout, encoding="utf-8")
    declarations = parse_probe(probe.stdout, names, trusted)
    issues = []
    if not inventory_match:
        issues.append("generated inventory disagrees with CST-TT-09_THEOREM_STATUS.csv")
    if build["status"] == "fail":
        issues.append("lake build failed")
    if probe.returncode != 0:
        issues.append("Lean declaration probe failed")
    for name, item in declarations.items():
        for error in item["errors"]:
            issues.append(f"probe {name}: {error}")
        if not item["resolved"]:
            issues.append(f"unresolved declaration: {name}")
        if not item["axiom_reported"]:
            issues.append(f"missing #print axioms output: {name}")
        if item["untrusted_axioms"]:
            issues.append(f"untrusted axioms in {name}: {', '.join(item['untrusted_axioms'])}")
        if item["kind"] in ("axiom", "opaque"):
            issues.append(f"non-evidence declaration kind in {name}: {item['kind']}")
    row_reports = []
    for row in audited_rows:
        items = [declarations[n] for n in row["declarations"]]
        rollup = {
            "theorem_kind": sum(x["kind"] == "theorem" for x in items),
            "statement_only": sum(x["statement_only"] for x in items),
            "other_definitions": sum(x["kind"] == "definition" and not x["statement_only"] for x in items),
        }
        row_reports.append({**row, "rollup": rollup,
            "probe_status": "PASS" if all(x["resolved"] for x in items) else "FAIL",
            "axiom_status": "PASS" if all(x["axiom_reported"] and not x["untrusted_axioms"] for x in items) else "FAIL"})
        if row["status"] in ("conditional", "proved", "checked finite countermodel") and not rollup["theorem_kind"] and not rollup["other_definitions"]:
            issues.append(f"row {row['row_id']} has statement-only definitions but no theorem-kind or constructive definition evidence")
    totals = {"rows": len(audited_rows), "declarations": sum(len(r["declarations"]) for r in audited_rows),
        "unique_declarations": len(names),
        **{key: sum(r["rollup"][key] for r in row_reports) for key in ("theorem_kind", "statement_only", "other_definitions")}}
    untrusted = sorted({a for item in declarations.values() for a in item["untrusted_axioms"]})
    scan_summary = {"placeholders": sum(f["category"] == "placeholder" for f in findings),
        "high_confidence": sum(f["tier"] == "high-confidence" for f in findings),
        "heuristic_leads": sum(f["tier"] == "heuristic lead" for f in findings)}
    overall = "fail" if issues or scan_summary["placeholders"] or scan_summary["high_confidence"] or args.skip_build else "pass"
    report = {"schema": "csttt-lean-audit-v1", "mode": "fixture" if args.skip_build else "full",
        "registry": str(registry), "inventory": str(inventory_path), "inventory_match": inventory_match,
        "trust_base": sorted(trusted), "build": build, "probe_exit_code": probe.returncode,
        "rows": row_reports, "declarations": declarations, "totals": totals, "scan_summary": scan_summary,
        "untrusted_axioms": untrusted, "findings": findings, "issues": issues, "overall": overall}
    write_json(run_dir / "report.json", report)
    human = render(report)
    (run_dir / "report.txt").write_text(human, encoding="utf-8")
    print(human, end="")
    print(f"JSON: {run_dir / 'report.json'}")
    print(f"TEXT: {run_dir / 'report.txt'}")
    return 0 if overall == "pass" else 1


if __name__ == "__main__":
    raise SystemExit(main())
