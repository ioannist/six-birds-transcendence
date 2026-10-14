#!/usr/bin/env python3
"""Validate the CST-EXP-01 corpus-mining and canonical-asset phase.

The validator checks source accounting, statement provenance, card coverage,
fixed-support visibility, version/exclusion handling, asset-to-statement links,
map typing, gap records, consciousness-repository inventory, and the strict
nonselection boundary. It does not validate the scientific truth of the papers.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import os
import re
import subprocess
import sys
import zipfile
from collections import Counter, defaultdict
from dataclasses import dataclass, asdict
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import unquote


@dataclass
class Result:
    name: str
    passed: bool
    evidence: str


class Validator:
    def __init__(self, root: Path):
        self.root = root.resolve()
        self.results: list[Result] = []

    def add(self, name: str, condition: bool, evidence: object) -> None:
        if isinstance(evidence, (dict, list, tuple, set)):
            text = json.dumps(evidence, ensure_ascii=False, sort_keys=True, default=str)
        else:
            text = str(evidence)
        self.results.append(Result(name, bool(condition), text.replace("\n", " ")))

    def require_file(self, rel: str) -> Path:
        return self.root / rel

    def csv_rows(self, rel: str) -> list[dict[str, str]]:
        with self.require_file(rel).open(newline="", encoding="utf-8") as fh:
            return list(csv.DictReader(fh))

    def json_data(self, rel: str):
        return json.loads(self.require_file(rel).read_text(encoding="utf-8"))

    @staticmethod
    def sha(path: Path) -> str:
        h = hashlib.sha256()
        with path.open("rb") as fh:
            for chunk in iter(lambda: fh.read(1024 * 1024), b""):
                h.update(chunk)
        return h.hexdigest()

    def run(self) -> None:
        r = self.root

        # 1. Core artifact presence and parseability.
        required = [
            "README.md", "STATE.md", "STATUS.md", "CHANGELOG.md",
            "changelog/CST-EXP-01.md",
            "corpus/README.md",
            "corpus/paper_cards/INDEX.md", "corpus/paper_cards/INDEX.csv",
            "corpus/clause_cards/INDEX.md", "corpus/theorem_cards/INDEX.md",
            "corpus/asset_atlas/ASSET_ATLAS.md",
            "corpus/asset_atlas/ASSET_PROVENANCE.md",
            "corpus/asset_atlas/COMPOSITION_NOTES.md",
            "corpus/asset_atlas/STATEMENT_SELECTION_METHOD.md",
            "corpus/asset_atlas/PAPER_COVERAGE_AUDIT.md",
            "corpus/asset_atlas/EXIT_GATE_AUDIT.md",
            "corpus/asset_atlas/dependency_graph.dot",
            "corpus/asset_atlas/dependency_graph.mmd",
            "corpus/asset_atlas/dependency_graph.svg",
            "corpus/asset_atlas/dependency_graph.png",
            "corpus/machine_index/all_statement_index.csv",
            "corpus/machine_index/paper_inventory.csv",
            "corpus/consciousness_repo/consciousness_repo_inventory.csv",
            "corpus/consciousness_repo/formal_inventory.csv",
            "corpus/consciousness_repo/test_inventory.csv",
            "corpus/consciousness_repo/VERIFICATION.md",
            "ledgers/statement_provenance.csv",
            "ledgers/support_and_carrier_assumptions.csv",
            "ledgers/asset_provenance.csv",
            "ledgers/map_type_ledger.csv",
            "ledgers/lexical_dependency_index.csv",
            "ledgers/source_label_index.csv",
            "ledgers/paper_coverage_audit.csv",
            "ledgers/gap_to_asset_matrix.csv",
            "ledgers/version_and_exclusion_log.md",
            "ledgers/corpus_duplicate_map.csv",
            "ledgers/dependency_read_wave_log.csv",
            "ledgers/DECISION_LOG.md", "ledgers/decision_log.csv",
            "ledgers/UNRESOLVED_QUESTIONS.md", "ledgers/REJECTED_DEFAULTS.md",
            "scripts/extract_corpus.py", "scripts/build_exp01_assets.py",
            "scripts/enrich_exp01_assets.py", "scripts/rebuild_exp01.sh",
            "scripts/validate_exp01.py",
            "inputs/source_archives/six_birds_papers_tex.zip",
            "inputs/source_archives/six-birds-consciousness_v41.zip",
            "inputs/normative/PAPER_TRIAGE.md",
            "inputs/normative/PREPARATORY_EXPLORATION_PLAN.md",
            "manifests/CST-EXP-01_COMPLETION_REPORT.md",
            "manifests/CST-EXP-00_VALIDATION_REPORT.md",
            "manifests/PHASE_SUMMARY.json",
            "manifests/MANIFEST.json",
            "manifests/RESTORE_AND_VERIFY.md",
        ]
        missing = [x for x in required if not (r / x).is_file()]
        self.add("Required phase artifacts exist", not missing, {"required": len(required), "missing": missing})
        empty = [x for x in required if (r / x).is_file() and (r / x).stat().st_size == 0]
        self.add("Required phase artifacts are nonempty", not empty, {"empty": empty})

        csv_files = [
            "corpus/paper_cards/INDEX.csv", "corpus/machine_index/all_statement_index.csv",
            "corpus/machine_index/paper_inventory.csv",
            "corpus/consciousness_repo/consciousness_repo_inventory.csv",
            "corpus/consciousness_repo/formal_inventory.csv",
            "corpus/consciousness_repo/test_inventory.csv",
            "ledgers/statement_provenance.csv", "ledgers/support_and_carrier_assumptions.csv",
            "ledgers/asset_provenance.csv", "ledgers/map_type_ledger.csv",
            "ledgers/lexical_dependency_index.csv", "ledgers/source_label_index.csv",
            "ledgers/paper_coverage_audit.csv", "ledgers/gap_to_asset_matrix.csv",
            "ledgers/corpus_duplicate_map.csv", "ledgers/dependency_read_wave_log.csv",
            "corpus/asset_atlas/dependency_graph_nodes.csv",
            "corpus/asset_atlas/dependency_graph_edges.csv", "ledgers/decision_log.csv",
        ]
        parse_errors: list[str] = []
        for rel in csv_files:
            try:
                rows = self.csv_rows(rel)
                if not rows:
                    parse_errors.append(f"{rel}: no rows")
            except Exception as exc:  # pragma: no cover - diagnostic path
                parse_errors.append(f"{rel}: {exc}")
        self.add("All phase CSV ledgers parse and contain data", not parse_errors, parse_errors or f"{len(csv_files)} CSV files")

        json_errors: list[str] = []
        for rel in ["manifests/PHASE_SUMMARY.json", "manifests/MANIFEST.json"]:
            try:
                self.json_data(rel)
            except Exception as exc:
                json_errors.append(f"{rel}: {exc}")
        self.add("Phase JSON metadata parses", not json_errors, json_errors or "2 JSON files")

        # 2. Source archives and corpus accounting.
        papers_zip = r / "inputs/source_archives/six_birds_papers_tex.zip"
        consciousness_zip = r / "inputs/source_archives/six-birds-consciousness_v41.zip"
        zip_errors: list[str] = []
        zip_members: dict[str, bytes] = {}
        for path in [papers_zip, consciousness_zip]:
            try:
                with zipfile.ZipFile(path) as zf:
                    bad = zf.testzip()
                    if bad:
                        zip_errors.append(f"{path.name}: corrupt member {bad}")
                    if path == papers_zip:
                        for info in zf.infolist():
                            if not info.is_dir() and info.filename.endswith(".tex") and "/" not in info.filename:
                                zip_members[info.filename] = zf.read(info)
            except Exception as exc:
                zip_errors.append(f"{path.name}: {exc}")
        self.add("Both embedded source archives pass ZIP integrity", not zip_errors, zip_errors or "ZIP CRC checks pass")
        self.add("Paper archive contains exactly 60 top-level TeX manuscripts", len(zip_members) == 60, len(zip_members))

        pin_rows: dict[str, str] = {}
        pin_path = r / "manifests/SOURCE_SHA256SUMS"
        if pin_path.exists():
            for line in pin_path.read_text(encoding="utf-8").splitlines():
                m = re.match(r"^([0-9a-f]{64})\s+\*?(.+)$", line.strip())
                if m:
                    pin_rows[m.group(2)] = m.group(1)
        pin_bad = []
        for rel, expected in pin_rows.items():
            p = r / rel
            if not p.exists() or self.sha(p) != expected:
                pin_bad.append(rel)
        self.add("Normative inputs and source archives match pinned hashes", bool(pin_rows) and not pin_bad, {"pinned": len(pin_rows), "bad": pin_bad})

        paper_inv = self.csv_rows("corpus/machine_index/paper_inventory.csv")
        machine = self.csv_rows("corpus/machine_index/all_statement_index.csv")
        self.add("Paper inventory contains P01 through P60 exactly once", len(paper_inv) == 60 and {x["paper_id"] for x in paper_inv} == {f"P{i:02d}" for i in range(1, 61)}, len(paper_inv))
        original_count = sum(int(x["statement_count"]) for x in paper_inv)
        p46_count = int(next(x for x in paper_inv if x["paper_id"] == "P46")["statement_count"])
        self.add("Original theorem-like environment census is 1,363", original_count == 1363, original_count)
        self.add("P46 contributes four quarantined environments to the original census", p46_count == 4, p46_count)
        self.add("Non-quarantined machine statement bank contains 1,359 rows", len(machine) == 1359, len(machine))
        machine_ids = [x["statement_id"] for x in machine]
        self.add("Machine statement IDs are unique", len(machine_ids) == len(set(machine_ids)), {"rows": len(machine_ids), "unique": len(set(machine_ids))})
        self.add("P46 is absent from the machine statement bank", not any(x["paper_id"] == "P46" for x in machine), Counter(x["paper_id"] for x in machine).get("P46", 0))
        counts = Counter(x["paper_id"] for x in machine)
        self.add("P42/P60 statement counts retain version delta", counts["P42"] == 173 and counts["P60"] == 157, {"P42": counts["P42"], "P60": counts["P60"]})

        # Verify inventory SHA/size/line metadata against the retained source archive.
        inv_bad: list[str] = []
        for row in paper_inv:
            name = row["filename"]
            data = zip_members.get(name)
            if data is None:
                inv_bad.append(f"{row['paper_id']}: missing {name}")
                continue
            actual_sha = hashlib.sha256(data).hexdigest()
            actual_lines = data.decode("utf-8", errors="replace").count("\n") + 1
            if actual_sha != row["sha256"] or len(data) != int(row["bytes"]) or actual_lines != int(row["lines"]):
                inv_bad.append(row["paper_id"])
        self.add("Paper inventory hashes, bytes, and line counts match source archive", not inv_bad, inv_bad or "60/60")

        # 3. Paper cards and coverage.
        card_paths = sorted((r / "corpus/paper_cards").glob("P[0-9][0-9].md"))
        self.add("Exactly 60 paper cards exist", len(card_paths) == 60, len(card_paths))
        card_ids = {p.stem for p in card_paths}
        self.add("Paper-card IDs are exactly P01 through P60", card_ids == {f"P{i:02d}" for i in range(1, 61)}, sorted(card_ids ^ {f"P{i:02d}" for i in range(1, 61)}))
        card_required = ["## Source identity", "## Evidence and scope", "## Transfer-relevant primitives and definitions", "## Explicit boundary / what it cannot establish", "## Distinct-carrier generalization required", "## Phase disposition"]
        card_bad: list[str] = []
        for p in card_paths:
            text = p.read_text(encoding="utf-8")
            if p.stem == "P46":
                continue
            missing_heads = [h for h in card_required if h not in text]
            if missing_heads or "SHA-256" not in text or "Fixed-support" not in text:
                card_bad.append(f"{p.stem}:{','.join(missing_heads)}")
        self.add("Every non-quarantined paper card contains provenance, extraction, support, boundary, generalization, and disposition sections", not card_bad, card_bad or "59/59")
        p46_text = (r / "corpus/paper_cards/P46.md").read_text(encoding="utf-8")
        p46_safe = all(x in p46_text.lower() for x in ["quarantine", "metadata", "no substantive"]) and "## Transfer-relevant extraction" not in p46_text
        self.add("P46 card is fail-closed metadata/exclusion only", p46_safe, p46_text[:300])
        contamination = [p.name for p in card_paths if "Existing gaps and what would be required next" in p.read_text(encoding="utf-8")]
        self.add("No paper card absorbs report-level triage text", not contamination, contamination)

        coverage = self.csv_rows("ledgers/paper_coverage_audit.csv")
        self.add("Paper coverage audit has 60 unique rows", len(coverage) == 60 and len({x["paper_id"] for x in coverage}) == 60, len(coverage))
        self.add("Every coverage row resolves to an existing paper card", all((r / x["card_path"]).is_file() for x in coverage), [x["paper_id"] for x in coverage if not (r / x["card_path"]).is_file()])

        # 4. Curated statement provenance and exact source spans.
        prov = self.csv_rows("ledgers/statement_provenance.csv")
        self.add("Curated statement/provenance ledger has 378 rows", len(prov) == 378, len(prov))
        prov_ids = [x["statement_id"] for x in prov]
        self.add("Curated statement IDs are unique", len(prov_ids) == len(set(prov_ids)), {"rows": len(prov_ids), "unique": len(set(prov_ids))})
        curated_counts = Counter(x["paper_id"] for x in prov)
        self.add("Every one of 60 papers has an explicit curated disposition", set(curated_counts) == {f"P{i:02d}" for i in range(1, 61)} and all(curated_counts[f"P{i:02d}"] >= 1 for i in range(1, 61)), dict(sorted(curated_counts.items())))
        self.add("P46 has exactly one exclusion record and no content record", curated_counts["P46"] == 1 and next(x for x in prov if x["paper_id"] == "P46")["selection_status"] == "excluded", curated_counts["P46"])

        machine_set = set(machine_ids)
        bad_refs: list[str] = []
        bad_spans: list[str] = []
        essential_fields = ["paper_id", "canonical_title", "source_file", "source_sha256", "source_lines", "statement_kind", "compact_statement", "claim_lanes", "fixed_support", "carrier_scope", "selection_status", "version_status", "nonclaim_or_limit"]
        missing_fields: list[str] = []
        manual_count = 0
        for row in prov:
            sid = row["statement_id"]
            if row["paper_id"] == "P46":
                continue
            if sid in machine_set:
                pass
            elif re.fullmatch(r"P\d{2}-M\d{3}", sid):
                manual_count += 1
            else:
                bad_refs.append(sid)
            absent = [f for f in essential_fields if not row.get(f, "").strip()]
            if absent:
                missing_fields.append(f"{sid}:{','.join(absent)}")
            data = zip_members.get(row["source_file"])
            if data is None or hashlib.sha256(data).hexdigest() != row["source_sha256"]:
                bad_spans.append(f"{sid}:source/hash")
                continue
            m = re.fullmatch(r"(\d+)-(\d+)", row["source_lines"])
            if not m:
                bad_spans.append(f"{sid}:span={row['source_lines']}")
                continue
            a, b = map(int, m.groups())
            nlines = data.decode("utf-8", errors="replace").count("\n") + 1
            if not (1 <= a <= b <= nlines):
                bad_spans.append(f"{sid}:{a}-{b}/{nlines}")
        self.add("Every curated formal record resolves to machine bank and every manual record has a declared manual ID", not bad_refs and manual_count == 55, {"bad": bad_refs, "manual_passages": manual_count})
        self.add("Every non-quarantined curated record has a valid source hash and line span", not bad_spans, bad_spans[:20] or f"{len(prov)-1}/{len(prov)-1}")
        self.add("Curated provenance has all fail-closed scope and nonclaim fields populated", not missing_fields, missing_fields[:20] or f"{len(prov)-1} records")
        lane_bad = [x["statement_id"] for x in prov if x["paper_id"] != "P46" and any(t not in {"S-T", "S-R", "S-L", "A", "R", "O", "M"} for t in x["claim_lanes"].split(";") if t)]
        self.add("All curated claim lanes use the canonical seven-lane vocabulary", not lane_bad, lane_bad)

        # Machine source span check.
        machine_span_bad: list[str] = []
        for row in machine:
            data = zip_members.get(row["filename"])
            if data is None:
                machine_span_bad.append(f"{row['statement_id']}:file")
                continue
            nlines = data.decode("utf-8", errors="replace").count("\n") + 1
            a, b = int(row["line_start"]), int(row["line_end"])
            if not (1 <= a <= b <= nlines):
                machine_span_bad.append(f"{row['statement_id']}:{a}-{b}/{nlines}")
        self.add("All 1,359 machine-index statement spans resolve inside source files", not machine_span_bad, machine_span_bad[:20] or "1359/1359")

        # 5. Fixed-support and version handling.
        support = self.csv_rows("ledgers/support_and_carrier_assumptions.csv")
        paper_support = [x for x in support if x["asset_id"] == "paper-level"]
        self.add("Support/carrier ledger includes one paper-level row for every manuscript", len(paper_support) == 60 and {x["paper_id"] for x in paper_support} == {f"P{i:02d}" for i in range(1, 61)}, len(paper_support))
        support_fields = ["support_scope", "fixed_support_flag", "carrier_relation", "retyping_needed", "identity_status", "autonomy_status"]
        support_bad = [x["paper_id"] for x in paper_support if any(not x[f].strip() for f in support_fields)]
        self.add("Every paper-level support record exposes support, carrier, retyping, identity, and autonomy limits", not support_bad, support_bad)
        fixed_ids = {x["paper_id"] for x in paper_support if x["fixed_support_flag"] == "yes"}
        expected_fixed = {"P03", "P08", "P09", "P14", "P16", "P18", "P23", "P24", "P39"}
        self.add("Nine fixed-support imports are explicitly flagged", fixed_ids == expected_fixed, {"actual": sorted(fixed_ids), "expected": sorted(expected_fixed)})

        version_text = (r / "ledgers/version_and_exclusion_log.md").read_text(encoding="utf-8")
        self.add("P42 is frozen as normative newer SAU revision and P60 has zero independent weight", all(s in version_text for s in ["P42 (normative newer revision)", "P60 (older revision)", "zero independent weight", "16 labels appear only in P42"]), "version log")
        p42_status = {x["version_status"] for x in prov if x["paper_id"] == "P42"}
        p60_status = {x["version_status"] for x in prov if x["paper_id"] == "P60"}
        self.add("Curated provenance preserves P42/P60 evidential status", p42_status == {"normative-newer-revision"} and p60_status == {"superseded-older-revision-no-independent-weight"}, {"P42": sorted(p42_status), "P60": sorted(p60_status)})
        dup = self.csv_rows("ledgers/corpus_duplicate_map.csv")
        self.add("All 18 embedded paper duplicates are recorded and not double-counted", len(dup) == 18 and all(x["byte_identical"] == "True" and "not-double-counted" in x["handling"] for x in dup), len(dup))

        # 6. Clause and theorem-family cards.
        clause_cards = sorted((r / "corpus/clause_cards").glob("C[1-8].md"))
        self.add("C1–C8 have exactly eight separate clause cards", len(clause_cards) == 8 and {p.stem for p in clause_cards} == {f"C{i}" for i in range(1, 9)}, [p.stem for p in clause_cards])
        clause_bad = []
        for p in clause_cards:
            text = p.read_text(encoding="utf-8")
            if not all(x in text for x in ["## Primitive and type", "## Landed component evidence", "## What must survive a carrier change", "## Open gap", "## Nonclaim"]):
                clause_bad.append(p.stem)
            if "component evidence" not in text.lower() or "integrated" not in text.lower():
                clause_bad.append(p.stem + ":boundary")
        self.add("Every clause card separates design contract, component evidence, transfer use, and integrated-instance boundary", not clause_bad, clause_bad)

        theorem_cards = sorted(p for p in (r / "corpus/theorem_cards").glob("*.md") if p.name != "INDEX.md")
        self.add("Theorem-family bank contains 25 source-scoped cards", len(theorem_cards) == 25, len(theorem_cards))
        theorem_names = {p.stem for p in theorem_cards}
        core_theorems = {"T14", "T15", "T17", "P14-PT", "P30-F19", "P50-CF", "P06-AOR"}
        self.add("Core lineage, combination, realization, transport, persistence, confluence, and completion cards exist", core_theorems <= theorem_names, sorted(core_theorems - theorem_names))
        t14 = (r / "corpus/theorem_cards/T14.md").read_text(encoding="utf-8").lower()
        t15 = (r / "corpus/theorem_cards/T15.md").read_text(encoding="utf-8").lower()
        t17 = (r / "corpus/theorem_cards/T17.md").read_text(encoding="utf-8").lower()
        self.add("T14 card exposes fission, fusion, empty target, and fixed-route/cross-carrier limits", all(x in t14 for x in ["fission", "fusion", "empty", "cross-carrier"]), "T14 boundary vocabulary")
        self.add("T15 card is a joint-carrier combination gate, not a lineage theorem", all(x in t15 for x in ["joint", "combination", "not", "lineage"]), "T15 boundary vocabulary")
        self.add("T17 card records absent A2 invariance theorem, certificate-soundness purchase, and absent integrated target", all(x in t17 for x in ["a2", "invariance", "certificate soundness", "integrated"]), "T17 boundary vocabulary")

        # 7. Assets, maps, dependencies, graph, and gaps.
        assets = self.csv_rows("ledgers/asset_provenance.csv")
        asset_ids = sorted({x["asset_id"] for x in assets})
        self.add("Canonical asset provenance has 196 exact links across 26 asset families", len(assets) == 196 and len(asset_ids) == 26, {"links": len(assets), "families": len(asset_ids)})
        prov_set = set(prov_ids)
        asset_bad = [f"{x['asset_id']}:{x['statement_id']}" for x in assets if x["statement_id"] not in prov_set]
        self.add("Every asset link resolves to a curated provenance record", not asset_bad, asset_bad[:20])
        per_asset = Counter(x["asset_id"] for x in assets)
        self.add("Every canonical asset family has at least one exact source link", set(per_asset) == set(asset_ids) and min(per_asset.values()) >= 1, dict(per_asset))
        atlas_text = (r / "corpus/asset_atlas/ASSET_ATLAS.md").read_text(encoding="utf-8")
        missing_asset_text = [a for a in asset_ids if a not in atlas_text]
        self.add("Asset atlas names all 26 canonical asset IDs", not missing_asset_text, missing_asset_text)
        fail_closed = all(x in atlas_text for x in ["Fail-closed import rule", "genuinely new", "fixed-support flag"])
        self.add("Asset reuse is frozen fail-closed to exact provenance or a genuinely new primitive", fail_closed, "atlas import rule")

        maps = self.csv_rows("ledgers/map_type_ledger.csv")
        self.add("Typed map ledger contains 106 positive or explicit-negative records", len(maps) == 106, len(maps))
        map_bad = [x["map_id"] for x in maps if any(not x[f].strip() for f in ["paper_id", "object_or_map", "type_signature", "source_type", "target_type", "imported_status", "cross_carrier_caution", "fixed_support_flag", "version_status"])]
        self.add("Every map record declares source type, target type, import status, and cross-carrier caution", not map_bad, map_bad)
        self.add("Typed map ledger covers all 60 papers, including explicit-negative records", {x["paper_id"] for x in maps} == {f"P{i:02d}" for i in range(1, 61)}, sorted({f"P{i:02d}" for i in range(1, 61)} - {x["paper_id"] for x in maps}))
        self.add("P46 is absent from substantive typed maps", all(x["paper_id"] != "P46" or x["imported_status"] == "quarantined-no-import" for x in maps), [x for x in maps if x["paper_id"] == "P46"])

        deps = self.csv_rows("ledgers/lexical_dependency_index.csv")
        self.add("Lexical dependency ledger covers all and only 1,359 non-quarantined statements", len(deps) == 1359 and {x["statement_id"] for x in deps} == machine_set, {"rows": len(deps), "ids": len({x['statement_id'] for x in deps})})
        dep_bad = []
        for row in deps:
            for sid in [x for x in row["resolved_statement_ids"].split(";") if x]:
                if sid not in machine_set:
                    dep_bad.append(f"{row['statement_id']}->{sid}")
        self.add("Every resolved explicit statement dependency points to a live machine-index statement", not dep_bad, dep_bad[:20])
        self.add("P46 is absent from lexical dependency and source-label ledgers", not any(x["paper_id"] == "P46" for x in deps) and not any(x["paper_id"] == "P46" for x in self.csv_rows("ledgers/source_label_index.csv")), "quarantine exclusion")
        labels = self.csv_rows("ledgers/source_label_index.csv")
        self.add("Source-label index contains 3,658 exact label locations", len(labels) == 3658, len(labels))

        nodes = self.csv_rows("corpus/asset_atlas/dependency_graph_nodes.csv")
        edges = self.csv_rows("corpus/asset_atlas/dependency_graph_edges.csv")
        node_ids = {x["node_id"] for x in nodes}
        graph_required_labels = {"Predictive quotient M", "Holonomy / route residue", "Relation-valued persistence", "Full C1–C8 package", "A2 Substrate Indifference", "Cross-carrier invariance H-XCI", "Recognition bridge", "Post-handoff autonomy"}
        self.add("Dependency graph contains all required structural, obstruction, assumption, and missing-theorem nodes", graph_required_labels <= {x["label"] for x in nodes}, sorted(graph_required_labels - {x["label"] for x in nodes}))
        self.add("Every graph edge resolves to live nodes", all(x["source"] in node_ids and x["target"] in node_ids for x in edges), [x for x in edges if x["source"] not in node_ids or x["target"] not in node_ids])
        edge_tuples = {(x["source"], x["target"], x["relation"]) for x in edges}
        neg_expected = {("N31", "N32", "no-ordering-theorem"), ("N37", "N38", "does-not-prove"), ("N12", "N36", "does-not-imply"), ("N31", "N36", "does-not-imply-unconditionally")}
        self.add("Dependency graph encodes the four critical negative/nonimplication edges", neg_expected <= edge_tuples, sorted(neg_expected - edge_tuples))
        self.add("Rendered graph artifacts are nontrivial", (r / "corpus/asset_atlas/dependency_graph.svg").stat().st_size > 1000 and (r / "corpus/asset_atlas/dependency_graph.png").stat().st_size > 1000, {"svg": (r / "corpus/asset_atlas/dependency_graph.svg").stat().st_size, "png": (r / "corpus/asset_atlas/dependency_graph.png").stat().st_size})

        gaps = self.csv_rows("ledgers/gap_to_asset_matrix.csv")
        gap_ids = {x["gap_id"] for x in gaps}
        self.add("Gap-to-asset matrix contains 14 unique gaps", len(gaps) == 14 and len(gap_ids) == 14, len(gaps))
        self.add("Required G01–G08 gaps are all present", {f"G{i:02d}" for i in range(1, 9)} <= gap_ids, sorted({f"G{i:02d}" for i in range(1, 9)} - gap_ids))
        gap_bad = [x["gap_id"] for x in gaps if any(not x[f].strip() for f in ["gap", "partial_assets", "missing_assumptions_or_data", "new_result_needed", "gap_type", "falsifier_or_kill_test", "status"])]
        self.add("Every gap states partial assets, missing purchase, needed result type, and kill test", not gap_bad, gap_bad)

        # 8. Consciousness repository inventory and honest verification status.
        c_inv = self.csv_rows("corpus/consciousness_repo/consciousness_repo_inventory.csv")
        f_inv = self.csv_rows("corpus/consciousness_repo/formal_inventory.csv")
        t_inv = self.csv_rows("corpus/consciousness_repo/test_inventory.csv")
        self.add("Consciousness repository inventory contains 350 non-directory files", len(c_inv) == 350, len(c_inv))
        self.add("Formal/formal-metadata inventory contains 92 files", len(f_inv) == 92, len(f_inv))
        self.add("Python test inventory contains 21 modules", len(t_inv) == 21, len(t_inv))
        required_test_paths = {"lab/tests/test_t14_lineage.py", "lab/tests/test_t15_combination_gate.py", "lab/tests/test_t17_certification_protocol.py", "lab/tests/test_scaffold.py"}
        self.add("T14/T15/T17 and scaffold executable surfaces are inventoried", required_test_paths <= {x["path"] for x in t_inv}, sorted(required_test_paths - {x["path"] for x in t_inv}))
        verify = (r / "corpus/consciousness_repo/VERIFICATION.md").read_text(encoding="utf-8")
        self.add("Selected consciousness checks honestly report 45 passing tests", "45 passed" in verify and "validate_package.py` | **PASS**" in verify, "selected verification")
        self.add("Incomplete full-suite, snapshot, and Lean checks are explicitly not reported as passes", all(x in verify for x in ["Timed out after 300 s", "Timed out after 180 s", "Lean build", "**Not a pass.**"]), "incomplete checks retained")
        self.add("Verification report preserves the no-integrated-instance/no-A2/no-lineage boundary", all(x in verify for x in ["integrated full C1–C8 instance", "A2 carrier-invariance theorem", "cross-carrier lineage theorem", "personal-identity conclusion"]), "scope boundary")

        # 9. Decision persistence, phase state, and strict nonselection boundary.
        decisions = self.csv_rows("ledgers/decision_log.csv")
        d_ids = {x["id"] for x in decisions}
        self.add("Decision ledger retains all 18 CST-EXP-00 rulings and 12 CST-EXP-01 rulings", {f"D00-{i:03d}" for i in range(1, 19)} <= d_ids and {f"D01-{i:03d}" for i in range(1, 13)} <= d_ids, {"rows": len(decisions), "missing_D01": sorted({f'D01-{i:03d}' for i in range(1,13)} - d_ids)})
        human_decisions = (r / "ledgers/DECISION_LOG.md").read_text(encoding="utf-8")
        self.add("Human decision log mirrors every machine decision ID", all(x in human_decisions for x in d_ids), {"machine_ids": len(d_ids)})
        state_text = "\n".join((r / f).read_text(encoding="utf-8") for f in ["README.md", "STATE.md", "STATUS.md"])
        self.add("Repository state declares CST-EXP-01 complete and CST-EXP-02 next", "CST-EXP-01" in state_text and "CST-EXP-02" in state_text and "Current completed phase:** `CST-EXP-01`" in state_text, "state headers")
        self.add("Repository state explicitly says no target, theorem target, or toy program was selected", all(x in state_text.lower() for x in ["no transported object", "no preferred bridge", "no theorem target", "no toy program"]), "nonselection state")
        phase_summary = self.json_data("manifests/PHASE_SUMMARY.json")
        expected_counts = {"papers": 60, "machine_statements": 1359, "curated_provenance_records": 378, "manual_source_passages": 55, "clause_cards": 8, "theorem_family_cards": 25, "asset_families": 26, "asset_provenance_links": 196, "typed_map_records": 106, "lexical_dependency_rows": 1359, "source_labels": 3658, "gap_rows": 14, "consciousness_repo_files": 350, "embedded_duplicate_papers": 18}
        live_counts = phase_summary.get("counts", {})
        self.add("Phase summary matches all major live CST-EXP-01 counts", all(live_counts.get(k) == v for k, v in expected_counts.items()), {k: live_counts.get(k) for k in expected_counts})
        self.add("Phase summary records complete/pass/frozen with no target or implementation", phase_summary.get("phase") == "CST-EXP-01" and phase_summary.get("status") == "complete" and phase_summary.get("exit_gate") == "pass" and phase_summary.get("target_selected") is False and phase_summary.get("theorem_or_program_implemented") is False and phase_summary.get("repository_state") == "frozen", phase_summary)

        late_files: list[str] = []
        for d in ["candidates", "scenarios", "synthesis", "challenges", "feasibility"]:
            for p in (r / d).rglob("*"):
                if p.is_file() and p.name != ".gitkeep":
                    late_files.append(str(p.relative_to(r)))
        self.add("Later exploration/implementation directories remain unexecuted", not late_files, late_files)
        comp = (r / "corpus/asset_atlas/COMPOSITION_NOTES.md").read_text(encoding="utf-8").lower()
        self.add("Composition notes are explicitly unranked and do not freeze a target", all(x in comp for x in ["unranked", "selected candidate", "no target"]), "composition boundary")
        exit_audit = (r / "corpus/asset_atlas/EXIT_GATE_AUDIT.md").read_text(encoding="utf-8")
        self.add("All six CST-EXP-01 exit gates are recorded PASS", exit_audit.count("**PASS.**") == 6, exit_audit.count("**PASS.**"))

        # 10. Repository hygiene, scripts, links, and manifests.
        py_compile_bad = []
        for rel in ["scripts/extract_corpus.py", "scripts/build_exp01_assets.py", "scripts/enrich_exp01_assets.py", "scripts/validate_exp01.py"]:
            proc = subprocess.run([sys.executable, "-m", "py_compile", str(r / rel)], capture_output=True, text=True)
            if proc.returncode:
                py_compile_bad.append(f"{rel}:{proc.stderr.strip()}")
        self.add("All CST-EXP-01 Python scripts compile", not py_compile_bad, py_compile_bad or "4/4")
        shell_proc = subprocess.run(["bash", "-n", str(r / "scripts/rebuild_exp01.sh")], capture_output=True, text=True)
        self.add("Portable rebuild shell script passes syntax check", shell_proc.returncode == 0, shell_proc.stderr.strip() or "bash -n")

        broken_links: list[str] = []
        md_re = re.compile(r"(?<!!)\[[^\]]*\]\(([^)]+)\)")
        for p in r.rglob("*.md"):
            if ".git" in p.parts:
                continue
            text = p.read_text(encoding="utf-8")
            for raw in md_re.findall(text):
                dest = unquote(raw.strip().split()[0].strip("<>"))
                if not dest or dest.startswith(("http://", "https://", "mailto:", "#", "sandbox:")):
                    continue
                if not any(ch in dest for ch in ("/", ".", "#", ":")):
                    continue
                dest = dest.split("#", 1)[0]
                if not dest:
                    continue
                target = (p.parent / dest).resolve()
                try:
                    target.relative_to(r)
                except ValueError:
                    broken_links.append(f"{p.relative_to(r)}->{dest}:outside")
                    continue
                if not target.exists():
                    broken_links.append(f"{p.relative_to(r)}->{dest}")
        self.add("All local Markdown links resolve", not broken_links, broken_links[:40])

        text_errors: list[str] = []
        symlinks: list[str] = []
        empty_files: list[str] = []
        for p in r.rglob("*"):
            rel = p.relative_to(r)
            if ".git" in rel.parts:
                continue
            if p.is_symlink():
                symlinks.append(str(rel))
            elif p.is_file():
                if p.stat().st_size == 0 and p.name != ".gitkeep":
                    empty_files.append(str(rel))
                if p.suffix.lower() in {".md", ".csv", ".json", ".yml", ".yaml", ".py", ".sh", ".txt", ".dot", ".mmd", ".toml"}:
                    try:
                        p.read_text(encoding="utf-8")
                    except Exception as exc:
                        text_errors.append(f"{rel}:{exc}")
        self.add("Repository contains no symlinks", not symlinks, symlinks)
        self.add("All repository text artifacts are UTF-8 readable", not text_errors, text_errors)
        self.add("No unintended empty files remain", not empty_files, empty_files)

        # Manifest check is intentionally before the newly written current validation reports.
        manifest = self.json_data("manifests/MANIFEST.json")
        entries = manifest.get("files", [])
        manifest_bad = []
        for entry in entries:
            p = r / entry["path"]
            if not p.is_file() or p.stat().st_size != entry["size_bytes"] or self.sha(p) != entry["sha256"]:
                manifest_bad.append(entry["path"])
        self.add("Content manifest entries match live files", bool(entries) and not manifest_bad, {"entries": len(entries), "bad": manifest_bad[:20]})

    def write(self, report: Path, json_path: Path) -> int:
        passed = sum(x.passed for x in self.results)
        total = len(self.results)
        status = "PASS" if passed == total else "FAIL"
        now = datetime.now(timezone.utc).isoformat()
        lines = [
            "# CST-EXP-01 Validation Report", "",
            f"**Generated:** {now}  ",
            f"**Result:** **{status}**  ",
            f"**Checks passed:** **{passed}/{total}**  ",
            "**Scope:** source accounting, complete paper coverage, statement and asset provenance, fixed-support and version discipline, consciousness-repository inventory, phase exit gates, and absence of target implementation. This is not proof of consciousness transfer, personal identity, or A2.", "",
            "## Executed checks", "",
            "| # | Check | Result | Evidence |", "|---:|---|---:|---|",
        ]
        for i, x in enumerate(self.results, 1):
            evidence = x.evidence.replace("|", "\\|")
            if len(evidence) > 800:
                evidence = evidence[:797] + "…"
            lines.append(f"| {i} | {x.name} | {'PASS' if x.passed else 'FAIL'} | {evidence} |")
        lines += ["", "## Exit-gate ruling", ""]
        if status == "PASS":
            lines.append("**PASS.** CST-EXP-01 provides a complete, source-traceable, support-audited corpus bank and canonical asset atlas while leaving target selection, theorem conjecture, toy-program design, empirical recognition, and ontological interpretation open for later phases.")
        else:
            failed = [x.name for x in self.results if not x.passed]
            lines.append("**FAIL.** The phase must not be frozen until these checks are repaired: " + "; ".join(failed) + ".")
        report.parent.mkdir(parents=True, exist_ok=True)
        report.write_text("\n".join(lines) + "\n", encoding="utf-8")
        payload = {
            "project": "CST-EXP", "phase": "CST-EXP-01", "generated_at_utc": now,
            "status": status.lower(), "checks_passed": passed, "checks_total": total,
            "results": [asdict(x) for x in self.results],
        }
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(json.dumps({"status": status, "passed": passed, "total": total, "report": str(report)}, indent=2))
        return 0 if status == "PASS" else 1


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo", type=Path, required=True)
    ap.add_argument("--report", type=Path)
    ap.add_argument("--json", dest="json_path", type=Path)
    args = ap.parse_args()
    root = args.repo.resolve()
    report = args.report or root / "manifests/VALIDATION_REPORT.md"
    json_path = args.json_path or root / "manifests/VALIDATION_RESULTS.json"
    v = Validator(root)
    v.run()
    return v.write(report, json_path)


if __name__ == "__main__":
    raise SystemExit(main())
