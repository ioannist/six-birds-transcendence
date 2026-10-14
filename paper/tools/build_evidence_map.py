#!/usr/bin/env python3
"""Generate W3 evidence metadata (Python stdlib only; no result interpretation).

--check regenerates every output in memory, including fresh Lean probes. Dates
are explicit snapshot metadata (--as-of, default W3 date 2026-10-13); release
W19 must generate and check with a new --as-of date and refresh the inputs.
Abbreviations are never expanded into declarations. Artifact links are taken
from registry references or audit notes tied to exact declarations/manifests.
"""
from __future__ import annotations

import argparse
import csv
from datetime import date
import io
import json
from pathlib import Path
import re
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[2]
OUTPUT = ROOT / 'paper/prewriting'
FQN = re.compile(r'CSTTT(?:\.[A-Za-z_][A-Za-z_0-9\']*)+')
ROW = re.compile(r'\b(?:TTH|TTN|TTD|TTF|TTS)-\d{2}\b')
DECL_COLUMNS = ['claim_id', 'source_rows', 'headline_declarations', 'lean_modules',
                'declaration_axioms', 'in_inventory', 'inventory_declaration_count', 'model_files',
                'transcription_scripts', 'not_mechanized']
MATRIX_COLUMNS = ['row_id', 'status_09', 'ceiling_09', 'inventory_declaration_count',
                  'ledger_claim_ids', 'model_files', 'transcription_scripts']
LOOKUP_COMMAND = r'''
open Lean Elab Command
syntax "#evidence_lookup " ident : command
elab_rules : command
  | `(#evidence_lookup $id:ident) => do
    let n := id.getId
    let env ← getEnv
    match env.find? n with
    | none => logInfo m!"W3_DECL|{n}|UNRESOLVED"
    | some _ =>
      match env.getModuleIdxFor? n with
      | none => throwError "No defining module for {n}"
      | some idx => logInfo m!"W3_DECL|{n}|{env.header.moduleNames[idx.toNat]!}"
'''


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline='', encoding='utf-8') as stream:
        return list(csv.DictReader(stream))


def csv_text(columns: list[str], rows: list[dict]) -> str:
    stream = io.StringIO(newline='')
    writer = csv.DictWriter(stream, fieldnames=columns, lineterminator='\n')
    writer.writeheader()
    writer.writerows(rows)
    return stream.getvalue()


def source_ids(claim: dict, registry: dict) -> list[str]:
    return sorted(set(ROW.findall(claim['source_rows'])) & registry.keys())


def headline_metadata(claim: dict) -> list[tuple[str, bool]]:
    parts = [p.strip() for p in claim['evidence'].split(';') if p.strip()]
    return [(p.removesuffix(' [supplemental]').strip().strip('`'),
             p.endswith(' [supplemental]')) for p in parts]


def headlines(claim: dict) -> list[str]:
    return [name for name, _ in headline_metadata(claim)]


def lean_code(text: str) -> str:
    """Remove nested Lean block comments and line comments before scanning imports."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1; i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1; i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' '); i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        else:
            out.append(text[i]); i += 1
    if depth:
        raise ValueError('Unclosed Lean comment')
    return ''.join(out)


def check_import_closure() -> dict:
    """Scan ALL CSTTT modules, including modules outside the root import closure."""
    paths = [ROOT / 'lean/CSTTT.lean', *sorted((ROOT / 'lean/CSTTT').rglob('*.lean'))]
    internal, external = set(), set()
    for path in paths:
        code = lean_code(path.read_text())
        for line in code.splitlines():
            match = re.match(r'^\s*(?:public\s+)?import\s+(.+)$', line)
            if not match:
                continue
            for name in match[1].split():
                if name == 'CSTTT' or name.startswith('CSTTT.'):
                    target = ROOT / 'lean' / (name.replace('.', '/') + '.lean')
                    if not target.is_file():
                        raise ValueError(f'Missing internal import: {name}')
                    internal.add(name)
                elif name.split('.')[0] in {'Init', 'Lean', 'Std'}:
                    external.add(name.split('.')[0])
                else:
                    raise ValueError(f'Unexpected CSTTT external import: {path}: {name}')
    hidden = [str(p.relative_to(ROOT)) for p in
              (ROOT / 'lean/vendor').rglob('*.lean')
              if re.search(r'\baxiom\s+hiddenness_pending\b', lean_code(p.read_text()))]
    if not hidden:
        raise ValueError('Vendored hiddenness_pending axiom not found')
    return {'modules_scanned': len(paths), 'external_roots': sorted(external),
            'hiddenness_sources': sorted(hidden)}


def run_probe(path: Path, log: Path) -> str:
    run = subprocess.run(['lake', 'env', 'lean', str(path)], cwd=ROOT / 'lean',
                         capture_output=True, text=True)
    output = run.stdout + run.stderr
    log.write_text(output)
    if run.returncode:
        raise RuntimeError(f'Lean probe failed; see {log.relative_to(ROOT)}')
    return output


def probe_names(names: list[str]) -> tuple[dict[str, str], dict, set[str]]:
    # Reuse the campaign's attributed axiom/kind parser, not its full gates.
    sys.path.insert(0, str(ROOT / 'scripts'))
    from validate_lean import make_probe, parse_probe
    logs = ROOT / 'lean/.validate-logs'
    logs.mkdir(exist_ok=True)
    lookup = logs / 'W3-resolution-probe.lean'
    lookup.write_text('import Lean\nimport CSTTT\n' + LOOKUP_COMMAND + '\n' +
                      '\n'.join('#evidence_lookup ' + name for name in names) + '\n')
    output = run_probe(lookup, logs / 'W3-resolution-probe.log')
    modules = {}
    for line in output.splitlines():
        if line.startswith('W3_DECL|'):
            _, name, module = line.split('|')
            if name in modules:
                raise ValueError(f'Duplicate lookup: {name}')
            modules[name] = module
    if set(modules) != set(names):
        raise ValueError('Incomplete declaration lookup')
    resolved = [name for name in names if modules[name] != 'UNRESOLVED']
    trusted = {line.strip() for line in (ROOT / 'lean/trust_base.txt').read_text().splitlines()
               if line.strip() and not line.lstrip().startswith('#')}
    probe = logs / 'W3-axiom-probe.lean'
    probe.write_text(make_probe(resolved))
    results = parse_probe(run_probe(probe, logs / 'W3-axiom-probe.log'), resolved, trusted)
    for name, result in results.items():
        if not result['resolved'] or not result['axiom_reported'] or result['errors']:
            raise ValueError(f'Incomplete axiom result: {name}')
    return modules, results, trusted


def existing_reference(value: str) -> Path | None:
    value = re.sub(r':\d+(?:-\d+)?$', '', value)
    for prefix in [ROOT, ROOT / 'cst-tt']:
        candidate = prefix / value
        if candidate.is_file() and candidate.is_relative_to(ROOT):
            return candidate
    return None


def model_spec(path: Path) -> bool:
    # Certificates are evidence artifacts, not automatically model specs.
    return (path.parent == ROOT / 'audit/proposed_models' and path.suffix == '.json'
            or path.suffix == '.md' and ('model_spec' in path.name or 'preregistration' in path.name))


class ArtifactIndex:
    """Conservative, explicit documentary association; absent links stay blank."""
    def __init__(self):
        self.docs = {p: p.read_text() for p in sorted((ROOT / 'audit').glob('*.md'))}
        self.artifacts = sorted([*(ROOT / 'audit/proposed_models').glob('*.json'),
                                 *(ROOT / 'audit').glob('*model_spec*.md'),
                                 *(ROOT / 'audit').glob('*preregistration*.md'),
                                 *(ROOT / 'scripts').glob('check_*.py')])
        self.by_declaration: dict[str, set[Path]] = {}
        self.by_module: dict[str, set[Path]] = {}
        modules = sorted((ROOT / 'lean/CSTTT').rglob('*.lean'))
        basename_counts = {}
        for module in modules:
            basename_counts[module.name] = basename_counts.get(module.name, 0) + 1
        module_labels = {str(p.relative_to(ROOT)): str(p.relative_to(ROOT)) for p in modules}
        module_labels.update({str(p.relative_to(ROOT / 'lean')): str(p.relative_to(ROOT)) for p in modules})
        module_labels.update({p.name: str(p.relative_to(ROOT)) for p in modules if basename_counts[p.name] == 1})
        module_refs = re.compile(r'(?<![\w./-])((?:lean/)?CSTTT/[\w/-]+\.lean|[\w-]+\.lean)(?![\w./-])')
        for path, text in self.docs.items():
            for label in set(module_refs.findall(text)):
                if label in module_labels:
                    self.by_module.setdefault(module_labels[label], set()).add(path)
        for path, text in self.docs.items():
            for name in set(FQN.findall(text)):
                self.by_declaration.setdefault(name, set()).add(path)
        for manifest in sorted((ROOT / 'audit').glob('*declarations.json')):
            data = json.loads(manifest.read_text())
            doc = manifest.with_name(manifest.name.replace('_declarations.json', '.md'))
            if doc not in self.docs:
                continue
            for declaration in data.get('declarations', []):
                if isinstance(declaration, dict) and declaration.get('name'):
                    self.by_declaration.setdefault(declaration['name'], set()).add(doc)

    def links(self, text: str) -> set[Path]:
        # Exact existing paths/basenames only, including Markdown links.
        found = set()
        for path in self.artifacts:
            for label in [str(path.relative_to(ROOT)), path.name]:
                if re.search(r'(?<![\w./-])' + re.escape(label) + r'(?![\w./-])', text):
                    found.add(path)
                    break
        # Audit text can explicitly identify a frozen preregistration by packet,
        # e.g. "G30 freeze". Follow only unique preregistration documents.
        for packet in set(re.findall(r'\b(G\d+[a-z]?)\b(?=[^\n]{0,80}\b(?:freeze|preregistration)\b)', text)):
            matches = [p for p in self.docs if re.match(re.escape(packet) + r'[_-]', p.name)
                       and 'preregistration' in p.name]
            if len(matches) == 1:
                found.add(matches[0])
        return found

    def collect(self, registry_rows: list[dict], declarations: list[str],
                modules: list[str] | None = None) -> tuple[str, str]:
        docs = set()
        for module in modules or []:
            docs.update(self.by_module.get(module, set()))
        found = set()
        for row in registry_rows:
            for ref in row['evidence_refs'].split(';'):
                path = existing_reference(ref.strip())
                if path is not None:
                    if model_spec(path):
                        found.add(path)
                    if path in self.docs:
                        docs.add(path)
            found.update(self.links(row['delta_rationale']))
        for name in declarations:
            docs.update(self.by_declaration.get(name, set()))
        # Follow only linked model/preregistration documents, never all mentions
        # of a row ID (which can also appear in future-work/failure notes).
        visited = set()
        pending = docs | {p for p in found if p in self.docs}
        while pending:
            path = min(pending)
            pending.remove(path)
            if path in visited:
                continue
            visited.add(path)
            linked = self.links(self.docs[path])
            found.update(linked)
            pending.update(p for p in linked if p in self.docs and p not in visited)
        models = sorted(str(p.relative_to(ROOT)) for p in found if model_spec(p))
        scripts = sorted(str(p.relative_to(ROOT)) for p in found
                         if p.parent == ROOT / 'scripts' and p.name.startswith('check_'))
        return ';'.join(models), ';'.join(scripts)


def snapshot_date(explicit: str | None) -> str:
    # A stable metadata parameter, never inferred from the generated outputs.
    value = explicit if explicit is not None else '2026-10-13'
    date.fromisoformat(value)
    return value


def generate(as_of: str) -> tuple[dict[str, str], dict]:
    registry_rows = read_csv(ROOT / 'cst-tt/registries/CST-TT-09_THEOREM_STATUS.csv')
    registry = {r['theorem_id']: r for r in registry_rows}
    inventory = json.loads((ROOT / 'lean/row_inventory.json').read_text())
    indexed = {r['row_id']: r for r in inventory['rows']}
    if (len(registry_rows) != 39 or len(inventory['rows']) != 39
            or len(registry) != 39 or set(registry) != set(indexed)):
        raise ValueError('Registry/inventory row mismatch')
    for rid, row in registry.items():
        inv = indexed[rid]
        if (inv['status'] != row['status_09'] or inv['claim_ceiling'] != row['ceiling_09']
                or inv['declarations'] != [n.strip() for n in row['kernel_evidence'].split(';')]):
            raise ValueError(f'Registry/inventory drift: {rid}')
    ledger = read_csv(ROOT / 'paper/prewriting/claim_ledger.csv')
    if len({r['claim_id'] for r in ledger}) != len(ledger):
        raise ValueError('Duplicate ledger claim IDs')
    claims = [r for r in ledger if 'CSTTT.' in r['evidence']]
    all_names = sorted({n for r in claims for n in headlines(r)})
    lookup, axioms, trusted = probe_names([n for n in all_names if FQN.fullmatch(n)])
    unresolved = sorted(n for n in all_names if n not in axioms)
    module_paths = {}
    for name in axioms:
        path = ROOT / 'lean' / (lookup[name].replace('.', '/') + '.lean')
        if not path.is_file():
            raise ValueError(f'Defining source module unavailable: {name}: {lookup[name]}')
        module_paths[name] = str(path.relative_to(ROOT))
    closure = check_import_closure()
    inventory_names = {n for r in indexed.values() for n in r['declarations']}
    authored_rows = read_csv(ROOT / 'paper/prewriting/not_mechanized.csv')
    authored = {r['claim_id']: r['not_mechanized'] for r in authored_rows}
    if len(authored) != len(authored_rows) or set(authored) - {r['claim_id'] for r in ledger}:
        raise ValueError('Duplicate or unknown not_mechanized claim IDs')
    for claim in claims:
        for name, supplemental in headline_metadata(claim):
            if name in axioms and (name in inventory_names) == supplemental:
                raise ValueError(f'Inventory/supplemental mismatch: {name}')
    index = ArtifactIndex()
    declaration_rows = []
    for claim in claims:
        ids = source_ids(claim, registry)
        names = headlines(claim)
        resolved = [n for n in names if n in axioms]
        models, scripts = index.collect([registry[rid] for rid in ids], resolved, [module_paths[n] for n in resolved])
        declaration_rows.append({
            'claim_id': claim['claim_id'], 'source_rows': claim['source_rows'],
            'headline_declarations': ';'.join(n if n in axioms else 'UNRESOLVED:' + n for n in names),
            'lean_modules': ';'.join(sorted({module_paths[n] for n in resolved})),
            'declaration_axioms': json.dumps({n: axioms[n]['axioms'] for n in resolved}, sort_keys=True, separators=(',', ':')),
            'inventory_declaration_count': sum(len(indexed[rid]['declarations']) for rid in ids),
            'model_files': models, 'transcription_scripts': scripts,
            'in_inventory': ';'.join('yes' if n in inventory_names else 'no' for n in names),
            'not_mechanized': authored.get(claim['claim_id'], ''),
        })
    matrix = []
    for row in registry_rows:
        rid = row['theorem_id']
        models, scripts = index.collect([row], indexed[rid]['declarations'],
                                        [module_paths[n] for n in indexed[rid]['declarations'] if n in module_paths])
        matrix.append({'row_id': rid, 'status_09': row['status_09'], 'ceiling_09': row['ceiling_09'],
                       'inventory_declaration_count': len(indexed[rid]['declarations']),
                       'ledger_claim_ids': ';'.join(r['claim_id'] for r in ledger if rid in source_ids(r, registry)),
                       'model_files': models, 'transcription_scripts': scripts})
    used = sorted({tuple(r['axioms']) for r in axioms.values()})
    untrusted = sorted({a for r in axioms.values() for a in r['untrusted_axioms']})
    toolchain = (ROOT / 'lean/lean-toolchain').read_text().strip()
    if toolchain != 'leanprover/lean4:v4.28.0':
        raise ValueError(f'Unexpected toolchain: {toolchain}')
    vendor = sorted(str(p.relative_to(ROOT)) for p in (ROOT / 'lean/vendor/foundations').iterdir() if p.is_dir())
    total = sum(len(r['declarations']) for r in indexed.values())
    unique = len({n for r in indexed.values() for n in r['declarations']})
    note = f'''# Lean evidence traceability

<!-- evidence-map-date: {as_of} -->
Snapshot date: **{as_of}**. Generated by `paper/tools/build_evidence_map.py`.
Counts are refreshed at release (W19), with an explicit `--as-of YYYY-MM-DD`.

- Toolchain: `{toolchain}` (Lean 4.28.0). CSTTT uses Lean core, no Mathlib.
- Permitted trust base, read from `lean/trust_base.txt`: `{', '.join(sorted(trusted))}`.
- Vendored source roots: {', '.join('`' + p + '`' for p in vendor)}.
- Registry/inventory: **39 rows**, **{total:,} declaration entries**, **{unique:,} unique inventory names**.
- Ledger: **{len(ledger)} claims**, **{len(claims)} with CSTTT headline evidence**.
- Headline names: **{len(axioms)} resolved**, **{len(unresolved)} unresolved** (unique literal names).
- Observed headline axiom sets: `{json.dumps(used)}`. Untrusted axioms: `{json.dumps(untrusted)}`.

`evidence_matrix.csv` maps every registry row to its exact `status_09`, verbatim
`ceiling_09`, inventory declaration count and ledger claim IDs.
`lean_declaration_map.csv` records each Lean-bearing claim's literal headline
names, defining source modules and per-declaration axiom sets. Source-row counts
sum their inventory entries; unique-name counts are reported separately.
Abbreviations and missing names are explicitly UNRESOLVED; they are not expanded
by namespace inference. The ` [supplemental]` suffix is ledger metadata, removed
before lookup. `in_inventory` contains `yes`/`no` flags in headline order,
separated by semicolons for claims with multiple declarations. Supplemental
names must be outside the inventory; all other names must be in it.
`not_mechanized` is merged verbatim by claim ID from Claude's authored
`paper/prewriting/not_mechanized.csv`; absent authored rows yield empty cells.

The generator's `check_import_closure()` scans all **{closure['modules_scanned']}
CSTTT source modules**, removes nested/block and line comments, resolves all
internal imports and rejects external roots other than `Init`, `Lean`, `Std`.
CSTTT imports only `Init`, `Lean` and `Std` outside its own modules, including
implicit Lean core imports. The vendored Six Birds tree contains the non-standard
axiom `hiddenness_pending` in `{closure['hiddenness_sources'][0]}`, but is not
imported by any CSTTT module, so no CSTTT declaration depends on it. The same
check also verifies the actual vendored axiom declaration exists.

A fresh `lake env lean` lookup through `import CSTTT` obtains defining modules;
a second fresh probe runs `#check` and `#print axioms` for each resolved headline.
The probes are `lean/.validate-logs/W3-resolution-probe.lean` and
`lean/.validate-logs/W3-axiom-probe.lean`; axiom output is saved to
`lean/.validate-logs/W3-axiom-probe.log`. Existing compiled modules are used;
this generator does not rebuild Lean. It reuses the attributed probe/parser from
`scripts/validate_lean.py`. The campaign-wide `scripts/validate_lean.sh` checks
all registry evidence, declaration kinds, axioms, source scans and inventory.
That full gate is not rerun by this generator.

Model/spec and transcription paths are included only when explicitly linked by
registry references or audit documentation associated with exact declarations
or declaration manifests, or cited defining source files; unique documented
frozen-preregistration packet links
are followed. Paths are existing repository files. Blank cells mean no such
association was determined, not that no model or check exists. Certificates are
not automatically classified as model specifications. These links record
artifacts, not a coverage or statement-fidelity judgment.

The snapshot date is an explicit parameter (`--as-of`, default W3 date
2026-10-13), never inferred from generated outputs. At W19, generation and
checking use the same new explicit date.
`--check` regenerates outputs in memory with fresh probes and compares bytes;
it reports drift and never overwrites the three outputs. Any unresolved headline
name makes generation and `--check` fail, even if output bytes match.
'''
    summary = {'mapped_claims': len(claims), 'resolved_names': len(axioms), 'unresolved_names': unresolved,
               'axiom_sets': used, 'untrusted_axioms': untrusted}
    return {'lean_declaration_map.csv': csv_text(DECL_COLUMNS, declaration_rows),
            'evidence_matrix.csv': csv_text(MATRIX_COLUMNS, matrix), 'lean_traceability.md': note}, summary


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check', action='store_true')
    parser.add_argument('--as-of', help='ISO snapshot date; refresh explicitly at W19')
    args = parser.parse_args()
    try:
        outputs, summary = generate(snapshot_date(args.as_of))
    except (ValueError, RuntimeError) as exc:
        print(str(exc), file=sys.stderr)
        return 1
    if summary.get('unresolved_names'):
        print('Unresolved headline names: ' + '; '.join(summary['unresolved_names']), file=sys.stderr)
        return 1
    drift = [name for name, content in outputs.items()
             if not (OUTPUT / name).exists() or (OUTPUT / name).read_bytes() != content.encode()]
    if args.check:
        if drift:
            print('Evidence-map drift: ' + ', '.join(drift), file=sys.stderr)
            return 1
    else:
        for name, content in outputs.items():
            (OUTPUT / name).write_text(content)
    print(json.dumps(summary, sort_keys=True))
    return 1 if summary['untrusted_axioms'] else 0


if __name__ == '__main__':
    raise SystemExit(main())
