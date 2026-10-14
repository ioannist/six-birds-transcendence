#!/usr/bin/env python3
"""Validate CST-EXP-02: scenario atlas and neutral transfer semantics.

This validator establishes completeness, provenance discipline, and neutrality of
35 scenario records (20 governing-plan cases plus 15 supplemental controls). It
does not decide consciousness transfer, personal identity, survival, or A2.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import sys
import zipfile
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from datetime import datetime, timezone
from pathlib import Path
from urllib.parse import unquote


@dataclass
class Result:
    name: str
    passed: bool
    evidence: str


class Validator:
    def __init__(self, root: Path, *, skip_manifest: bool = False):
        self.root = root.resolve()
        self.skip_manifest = skip_manifest
        self.results: list[Result] = []

    def add(self, name: str, ok: bool, evidence: object) -> None:
        if isinstance(evidence, (dict, list, tuple, set, Counter)):
            text = json.dumps(evidence, ensure_ascii=False, sort_keys=True, default=str)
        else:
            text = str(evidence)
        self.results.append(Result(name, bool(ok), text.replace("\n", " ")))

    def csv_rows(self, rel: str) -> list[dict[str, str]]:
        with (self.root / rel).open(newline="", encoding="utf-8") as fh:
            return list(csv.DictReader(fh))

    def json_data(self, rel: str):
        return json.loads((self.root / rel).read_text(encoding="utf-8"))

    @staticmethod
    def sha(path: Path) -> str:
        h = hashlib.sha256()
        with path.open("rb") as fh:
            for chunk in iter(lambda: fh.read(1024 * 1024), b""):
                h.update(chunk)
        return h.hexdigest()

    @staticmethod
    def split_ids(value: str) -> list[str]:
        return [x.strip() for x in value.split(";") if x.strip()]

    def run(self) -> None:
        r = self.root
        all_ids = {f"S{i:02d}" for i in range(1, 36)}
        canonical_ids = {f"S{i:02d}" for i in range(1, 21)}
        supplemental_ids = all_ids - canonical_ids
        discriminator_ids = {f"D{i:02d}" for i in range(1, 11)}
        canonical_lanes = {"S-T", "S-R", "S-L", "A", "R", "O", "M"}

        # 1. Required artifacts and parseability.
        required = [
            "README.md", "STATE.md", "STATUS.md", "CHANGELOG.md",
            "changelog/CST-EXP-02.md",
            "scenarios/NEUTRAL_TRANSFER_SCHEMA.md",
            "scenarios/PROTOCOL_AXIS_DICTIONARY.md",
            "scenarios/PROTOCOL_AXIS_REGISTRY.csv",
            "scenarios/PROTOCOL_AXIS_MATRIX.csv",
            "scenarios/OUTCOME_TAXONOMY.md",
            "scenarios/OUTCOME_LABEL_REGISTRY.csv",
            "scenarios/CANONICAL_BATTERY.md",
            "scenarios/SCENARIO_REGISTRY.json",
            "scenarios/EXIT_GATE_AUDIT.md",
            "scenarios/cards/INDEX.md",
            "ledgers/scenario_discriminator_matrix.csv",
            "ledgers/scenario_question_crosswalk.csv",
            "ledgers/scenario_asset_crosswalk.csv",
            "ledgers/scenario_verdict_template.csv",
            "templates/SCENARIO_VERDICT_RECORD.yml",
            "scripts/build_exp02_assets.py",
            "scripts/exp02_supplemental.py",
            "scripts/validate_exp02.py",
            "scripts/finalize_exp02_manifest.py",
            "scripts/rebuild_exp02.sh",
            "manifests/EXP02_ASSET_SUMMARY.json",
            "manifests/PHASE_SUMMARY.json",
            "manifests/CST-EXP-02_COMPLETION_REPORT.md",
            "manifests/RESTORE_AND_VERIFY.md",
            "manifests/REBUILD_VERIFICATION.md",
            "manifests/REBUILD_VERIFICATION.json",
            "inputs/normative/PREPARATORY_EXPLORATION_PLAN.md",
        ] + [f"scenarios/cards/S{i:02d}.md" for i in range(1, 36)]
        missing = [x for x in required if not (r / x).is_file()]
        self.add("All required CST-EXP-02 artifacts exist", not missing,
                 {"required": len(required), "missing": missing})
        empty = [x for x in required if (r / x).is_file() and (r / x).stat().st_size == 0]
        self.add("Required CST-EXP-02 artifacts are nonempty", not empty, empty)

        csv_files = [
            "scenarios/PROTOCOL_AXIS_REGISTRY.csv", "scenarios/PROTOCOL_AXIS_MATRIX.csv",
            "scenarios/OUTCOME_LABEL_REGISTRY.csv", "ledgers/scenario_discriminator_matrix.csv",
            "ledgers/scenario_question_crosswalk.csv", "ledgers/scenario_asset_crosswalk.csv",
            "ledgers/scenario_verdict_template.csv", "ledgers/decision_log.csv",
            "ledgers/asset_provenance.csv", "ledgers/statement_provenance.csv",
            "ledgers/support_and_carrier_assumptions.csv",
        ]
        csv_errors: list[str] = []
        for rel in csv_files:
            try:
                rows = self.csv_rows(rel)
                if not rows:
                    csv_errors.append(f"{rel}: no data rows")
            except Exception as exc:
                csv_errors.append(f"{rel}: {exc}")
        self.add("All phase and inherited corpus CSVs parse", not csv_errors,
                 csv_errors or f"{len(csv_files)} CSV files")

        json_errors: list[str] = []
        for rel in ["scenarios/SCENARIO_REGISTRY.json", "manifests/EXP02_ASSET_SUMMARY.json", "manifests/PHASE_SUMMARY.json", "manifests/REBUILD_VERIFICATION.json"]:
            try:
                self.json_data(rel)
            except Exception as exc:
                json_errors.append(f"{rel}: {exc}")
        self.add("Scenario registry and phase metadata JSON parse", not json_errors,
                 json_errors or "4 JSON files")

        # 2. EXP-01 corpus continuity and source controls.
        papers_zip = r / "inputs/source_archives/six_birds_papers_tex.zip"
        consciousness_zip = r / "inputs/source_archives/six-birds-consciousness_v41.zip"
        zip_errors: list[str] = []
        paper_members: list[str] = []
        for path in [papers_zip, consciousness_zip]:
            try:
                with zipfile.ZipFile(path) as zf:
                    bad = zf.testzip()
                    if bad:
                        zip_errors.append(f"{path.name}: corrupt member {bad}")
                    if path == papers_zip:
                        paper_members = [m.filename for m in zf.infolist()
                                         if not m.is_dir() and m.filename.endswith(".tex") and "/" not in m.filename]
            except Exception as exc:
                zip_errors.append(f"{path.name}: {exc}")
        self.add("Embedded source archives retain ZIP integrity", not zip_errors,
                 zip_errors or "both CRC checks pass")
        self.add("Paper archive still contains 60 top-level TeX manuscripts", len(paper_members) == 60, len(paper_members))

        pin_rows: dict[str, str] = {}
        pin_path = r / "manifests/SOURCE_SHA256SUMS"
        if pin_path.is_file():
            for line in pin_path.read_text(encoding="utf-8").splitlines():
                m = re.match(r"^([0-9a-f]{64})\s+\*?(.+)$", line.strip())
                if m:
                    pin_rows[m.group(2)] = m.group(1)
        pin_bad = []
        for rel, expected in pin_rows.items():
            p = r / rel
            if not p.is_file() or self.sha(p) != expected:
                pin_bad.append(rel)
        self.add("Normative inputs and source archives retain pinned hashes", bool(pin_rows) and not pin_bad,
                 {"pinned": len(pin_rows), "bad": pin_bad})

        paper_inv = self.csv_rows("corpus/machine_index/paper_inventory.csv")
        machine = self.csv_rows("corpus/machine_index/all_statement_index.csv")
        prov = self.csv_rows("ledgers/statement_provenance.csv")
        assets = self.csv_rows("ledgers/asset_provenance.csv")
        maps = self.csv_rows("ledgers/map_type_ledger.csv")
        lexical = self.csv_rows("ledgers/lexical_dependency_index.csv")
        source_labels = self.csv_rows("ledgers/source_label_index.csv")
        gaps = self.csv_rows("ledgers/gap_to_asset_matrix.csv")
        duplicates = self.csv_rows("ledgers/corpus_duplicate_map.csv")
        self.add("Frozen paper inventory remains P01–P60", len(paper_inv) == 60 and {x["paper_id"] for x in paper_inv} == {f"P{i:02d}" for i in range(1, 61)}, len(paper_inv))
        self.add("Machine and curated statement banks retain 1,359 and 378 rows", len(machine) == 1359 and len(prov) == 378, {"machine": len(machine), "curated": len(prov)})
        self.add("Canonical asset bank retains 26 families and 196 links", len({x["asset_id"] for x in assets}) == 26 and len(assets) == 196, {"families": len({x['asset_id'] for x in assets}), "links": len(assets)})
        self.add("Typed-map, dependency, source-label, and gap counts remain frozen", len(maps) == 106 and len(lexical) == 1359 and len(source_labels) == 3658 and len(gaps) == 14, {"maps": len(maps), "lexical": len(lexical), "labels": len(source_labels), "gaps": len(gaps)})
        self.add("All 18 embedded duplicate manuscripts remain mapped", len(duplicates) == 18, len(duplicates))
        self.add("P46 remains quarantined from substantive statement imports", not any(x["paper_id"] == "P46" for x in machine) and sum(1 for x in prov if x["paper_id"] == "P46") == 1 and next(x for x in prov if x["paper_id"] == "P46")["selection_status"] == "excluded", "machine=0; curated exclusion=1")
        version_log = (r / "ledgers/version_and_exclusion_log.md").read_text(encoding="utf-8").lower()
        self.add("P42 remains normative and P60 has zero independent evidential weight", all(x in version_log for x in ["p42", "p60", "normative", "zero independent"]), "version log")

        # 3. Registry and protocol-axis matrix.
        registry = self.json_data("scenarios/SCENARIO_REGISTRY.json")
        scenarios = registry.get("scenarios", [])
        axes = registry.get("axes", {})
        discriminators = registry.get("discriminators", [])
        self.add("Registry declares neutral CST-EXP-02 semantics", registry.get("phase") == "CST-EXP-02" and "Operational edges are not lineage edges" in registry.get("neutrality_rule", ""), registry.get("neutrality_rule", ""))
        expected_axes = {"carrier_relation", "change_mode", "source_fate", "target_timing", "branching", "bridge_dependence", "fidelity", "reversibility", "route_multiplicity", "granularity"}
        self.add("Registry contains exactly the ten governing protocol axes", len(axes) == 10 and set(axes) == expected_axes, sorted(set(axes) ^ expected_axes))
        axis_values = {a: set(spec.get("values", {})) for a, spec in axes.items()}
        self.add("Ten axes expose the complete 44-value vocabulary", sum(len(v) for v in axis_values.values()) == 44, {a: len(v) for a, v in axis_values.items()})
        axis_registry = self.csv_rows("scenarios/PROTOCOL_AXIS_REGISTRY.csv")
        self.add("Axis registry has one unique row per declared value", len(axis_registry) == 44 and {(x["axis"], x["value"]) for x in axis_registry} == {(a, v) for a, vals in axis_values.items() for v in vals}, len(axis_registry))
        self.add("Every axis value has a neutral meaning, question, and blocked inference", all(all(x[k].strip() for k in ["neutral_meaning", "axis_question", "blocked_inference"]) for x in axis_registry), "44/44")

        scenario_map = {x.get("id"): x for x in scenarios}
        self.add("Registry contains exactly S01–S35", len(scenarios) == 35 and set(scenario_map) == all_ids, {"rows": len(scenarios), "ids": sorted(scenario_map)})
        self.add("S01–S20 are the governing-plan cases and S21–S35 are supplemental", all(int(scenario_map[s]["number"]) <= 20 for s in canonical_ids) and all(int(scenario_map[s]["number"]) > 20 for s in supplemental_ids), {"canonical": len(canonical_ids), "supplemental": len(supplemental_ids)})
        matrix = self.csv_rows("scenarios/PROTOCOL_AXIS_MATRIX.csv")
        matrix_map = {x["scenario_id"]: x for x in matrix}
        self.add("Protocol-axis matrix contains exactly S01–S35", len(matrix) == 35 and set(matrix_map) == all_ids, {"rows": len(matrix), "ids": sorted(matrix_map)})

        bad_axis_uses: list[str] = []
        uncovered = {(a, v) for a, vals in axis_values.items() for v in vals}
        for sid, row in matrix_map.items():
            for axis in expected_axes:
                value = row.get(axis, "")
                if value not in axis_values[axis]:
                    bad_axis_uses.append(f"{sid}:{axis}={value}")
                uncovered.discard((axis, value))
        self.add("Every matrix axis cell uses a declared value", not bad_axis_uses, bad_axis_uses)
        self.add("All 44 axis values are represented in the 35-case battery", not uncovered, sorted(uncovered))

        mismatches: list[str] = []
        for sid in all_ids:
            reg, row = scenario_map[sid], matrix_map[sid]
            if reg.get("title") != row.get("title"):
                mismatches.append(f"{sid}:title")
            for axis in expected_axes:
                if reg.get(axis) != row.get(axis):
                    mismatches.append(f"{sid}:{axis}")
        self.add("JSON registry and CSV matrix agree on IDs, titles, and ten axes", not mismatches, mismatches)
        detail_fields = ["cross_carrier_status", "handoff_shape", "branch_graph", "clock_relation", "causal_structure", "fidelity_scope", "autonomy_intervention", "instrument_constraints", "primary_discriminators", "card_path"]
        self.add("Every scenario supplies operational detail beyond axis labels", all(all(matrix_map[s].get(k, "").strip() for k in detail_fields) for s in all_ids), "35/35")
        self.add("All matrix card paths resolve", all((r / matrix_map[s]["card_path"]).is_file() for s in all_ids), [s for s in sorted(all_ids) if not (r / matrix_map[s]["card_path"]).is_file()])

        # 4. Governing-plan case fidelity and deliberate controls.
        profiles = {
            "S01": {"change_mode": "gradual_replacement", "carrier_relation": "partially_overlapping_support"},
            "S02": {"change_mode": "destructive_scan", "source_fate": "erased_before_activation"},
            "S03": {"change_mode": "nondestructive_copy", "source_fate": "persists"},
            "S04": {"change_mode": "nondestructive_copy", "source_fate": "erased_after_activation"},
            "S05": {"branching": "one_to_many", "source_fate": "erased_before_activation"},
            "S06": {"target_timing": "temporal_gap", "change_mode": "checkpoint_restart"},
            "S07": {"target_timing": "continuous_overlap", "source_fate": "remains_coupled"},
            "S08": {"change_mode": "distributed_extension", "bridge_dependence": "permanent"},
            "S09": {"branching": "one_to_many", "fidelity": "exact"},
            "S10": {"branching": "many_to_one", "granularity": "event_package"},
            "S11": {"fidelity": "lossy", "granularity": "predictive_state"},
            "S12": {"fidelity": "lossy", "granularity": "predictive_state"},
            "S13": {"bridge_dependence": "externally_decoded", "source_fate": "remains_coupled"},
            "S14": {"route_multiplicity": "holonomy_bearing_routes", "granularity": "predictive_state"},
            "S15": {"granularity": "event_package", "branching": "many_to_many"},
            "S16": {"fidelity": "residual_bounded", "granularity": "package_state"},
            "S17": {"fidelity": "error_corrected", "change_mode": "checkpoint_restart"},
            "S18": {"reversibility": "reversible", "granularity": "package_state"},
            "S19": {"target_timing": "time_rescaled_activation", "granularity": "predictive_state"},
            "S20": {"carrier_relation": "same_support_reencoding", "cross_carrier_status": "same_carrier_negative_control"},
        }
        profile_bad = [f"{sid}:{k}" for sid, expect in profiles.items() for k, v in expect.items() if matrix_map[sid].get(k) != v]
        self.add("All twenty governing-plan cases retain their defining protocol profiles", not profile_bad, profile_bad)
        canonical_prompts = [scenario_map[s].get("canonical_prompt", "").strip() for s in sorted(canonical_ids)]
        self.add("Every governing-plan case retains explicit canonical prompt wording", all(canonical_prompts) and len(set(canonical_prompts)) == 20, canonical_prompts)
        self.add("S11 stipulates public/report perfection with predictive mismatch", "public" in matrix_map["S11"]["fidelity_scope"].lower() and "predictive" in matrix_map["S11"]["fidelity_scope"].lower() and "nonexact" in matrix_map["S11"]["fidelity_scope"].lower(), matrix_map["S11"]["fidelity_scope"])
        self.add("S12 stipulates predictive matching with binding/action-credit mismatch", "predictive" in matrix_map["S12"]["fidelity_scope"].lower() and ("binding" in matrix_map["S12"]["fidelity_scope"].lower() or "action-credit" in matrix_map["S12"]["fidelity_scope"].lower()), matrix_map["S12"]["fidelity_scope"])
        self.add("S13 isolates continuing external decoder/source dependence", matrix_map["S13"]["bridge_dependence"] == "externally_decoded" and matrix_map["S13"]["source_fate"] == "remains_coupled", matrix_map["S13"]["autonomy_intervention"])
        self.add("S14 is a holonomy control rather than the exact round-trip case", matrix_map["S14"]["route_multiplicity"] == "holonomy_bearing_routes" and matrix_map["S14"]["reversibility"] != "reversible", {k: matrix_map["S14"][k] for k in ["route_multiplicity", "reversibility", "fidelity_scope"]})
        self.add("S15 isolates local matching with failed global gluing", "local" in matrix_map["S15"]["fidelity_scope"].lower() and "global" in matrix_map["S15"]["fidelity_scope"].lower(), matrix_map["S15"]["fidelity_scope"])
        self.add("S16 and S17 separate bounded defect from endogenous repair", matrix_map["S16"]["fidelity"] == "residual_bounded" and matrix_map["S17"]["fidelity"] == "error_corrected" and "repair" in matrix_map["S17"]["autonomy_intervention"].lower(), {"S16": matrix_map["S16"]["fidelity"], "S17": matrix_map["S17"]["fidelity"]})
        self.add("S18 is an exact reversible round-trip contrast to S14", matrix_map["S18"]["reversibility"] == "reversible" and matrix_map["S18"]["route_multiplicity"] != "holonomy_bearing_routes", {k: matrix_map["S18"][k] for k in ["reversibility", "route_multiplicity", "fidelity_scope"]})
        self.add("S19 uses an explicit non-unit clock relation", matrix_map["S19"]["target_timing"] == "time_rescaled_activation" and any(t in matrix_map["S19"]["clock_relation"].lower() for t in ["non-unit", "rescal", "rho", "ρ"]), matrix_map["S19"]["clock_relation"])
        self.add("S20 is a same-carrier false-positive control", matrix_map["S20"]["carrier_relation"] == "same_support_reencoding" and matrix_map["S20"]["cross_carrier_status"] == "same_carrier_negative_control", {k: matrix_map["S20"][k] for k in ["carrier_relation", "cross_carrier_status"]})

        supplemental_titles = {scenario_map[s]["title"] for s in supplemental_ids}
        required_supplemental_concepts = ["checkpoint", "concurrent source updates", "many-source fusion", "many-to-many", "error-corrected", "independently built", "persistent shared core", "delayed target collapse", "external scheduler", "certificate-only", "locally admissible edges", "approximately reversible", "dormant backup", "degrades the source", "critical pair"]
        supp_blob = " ".join(t.lower() for t in supplemental_titles)
        self.add("Fifteen supplemental controls cover the declared failure-mode extensions", all(x in supp_blob for x in required_supplemental_concepts), [x for x in required_supplemental_concepts if x not in supp_blob])
        self.add("Supplemental controls remain operational cases rather than candidate verdicts", all(scenario_map[s].get("blocked_inferences") and scenario_map[s].get("stress_questions") for s in supplemental_ids), "15/15")

        # 5. Neutral source-target semantics.
        schema = (r / "scenarios/NEUTRAL_TRANSFER_SCHEMA.md").read_text(encoding="utf-8")
        schema_l = schema.lower()
        schema_topics = ["operational episode graph", "lineage graph", "scenario facts versus criterion outputs", "local clocks", "withdrawal", "handoff", "branching and merging", "fidelity and granularity", "typed candidate verdict record", "nonclaims"]
        self.add("Neutral schema covers all required semantic topics", all(x in schema_l for x in schema_topics), [x for x in schema_topics if x not in schema_l])
        self.add("G_op is explicitly prior to and distinct from candidate G_kappa", all(x in schema for x in ["`G_op`", "`G_κ`", "built before any candidate criterion", "There is no requirement that `G_κ` reproduce `G_op`"]), "graph separation")
        self.add("Source and target are protocol roles, not a presupposed identity relation", "roles in a protocol" in schema and "not a pre-existing identity relation" in schema, "role typing")
        self.add("Handoff records protocol responsibility rather than subject movement", "Handoff is therefore a protocol interval/event" in schema and "same subject move" in schema, "handoff neutrality")
        self.add("Time uses local clocks and an optional relation rather than canonical now", "optional relation `Θ`" in schema and "not an assumed canonical synchronized `now`" in schema, "clock neutrality")
        self.add("Autonomy uses a declared withdrawal intervention signature", "J = (removed resources, retained environment, disturbance class, horizon/closure condition)" in schema, "withdrawal signature")
        self.add("Fidelity is paired with comparison granularity", "(quality class, comparison granularity)" in schema, "fidelity pair")
        self.add("Verdicts separate S-T, S-R, S-L, A, and R", all(x in schema for x in ["v_ST", "v_SR", "v_SL", "v_A", "v_R"]), "five lane slots")
        self.add("Schema explicitly makes no consciousness, identity, survival, uploading, or A2 conclusion", all(x in schema_l for x in ["does not define consciousness", "personal identity", "substrate indifference"]), "nonclaims")

        # 6. Scenario cards and battery coverage.
        card_paths = sorted((r / "scenarios/cards").glob("S[0-9][0-9].md"))
        self.add("Exactly 35 scenario cards exist", len(card_paths) == 35 and {p.stem for p in card_paths} == all_ids, [p.name for p in card_paths])
        card_heads = [
            "## 1. Discriminating purpose", "## 2. Stipulated scenario facts",
            "## 3. Neutral frame instantiation", "## 4. Protocol-axis profile",
            "## 5. Controlled variants", "## 6. Discriminator audit",
            "## 7. Scenario-specific stress questions", "## 8. Required candidate response",
            "## 9. Corpus assets that sharpen the case", "## 10. Blocked inferences",
            "## 11. Nonclaims",
        ]
        card_bad: list[str] = []
        unfilled_bad: list[str] = []
        disc_card_bad: list[str] = []
        facts_loaded: list[str] = []
        for p in card_paths:
            text = p.read_text(encoding="utf-8")
            missing_heads = [h for h in card_heads if h not in text]
            if missing_heads:
                card_bad.append(f"{p.stem}:{','.join(missing_heads)}")
            if "deliberately unfilled" not in text.lower() or not all(f"one `{lane}` outcome label" in text for lane in ["S-T", "S-R", "S-L", "A", "R"]):
                unfilled_bad.append(p.stem)
            if not all(f"`D{i:02d}`" in text for i in range(1, 11)):
                disc_card_bad.append(p.stem)
            facts_section = text.lower().split("## 2. stipulated scenario facts", 1)[-1].split("## 3.", 1)[0]
            if any(term in facts_section for term in ["same person", "the subject survives", "the subject dies", "is conscious"]):
                facts_loaded.append(p.stem)
        self.add("Every card contains the complete neutral card schema", not card_bad, card_bad)
        self.add("Every card leaves five candidate outcome lanes deliberately unfilled", not unfilled_bad, unfilled_bad)
        self.add("Every card applies all ten discriminators", not disc_card_bad, disc_card_bad)
        self.add("Stipulated facts do not prefill identity or consciousness verdicts", not facts_loaded, facts_loaded)
        operational_lineage_bad = []
        for p in card_paths:
            t = p.read_text(encoding="utf-8").lower()
            frame = t.split("## 3. neutral frame instantiation", 1)[-1].split("## 4.", 1)[0]
            if "supplies no lineage edge" not in frame and "no lineage edge" not in frame:
                operational_lineage_bad.append(p.stem)
        self.add("Every card states that its operational graph supplies no lineage edge", not operational_lineage_bad, operational_lineage_bad)

        battery = (r / "scenarios/CANONICAL_BATTERY.md").read_text(encoding="utf-8")
        battery_l = battery.lower()
        self.add("Battery declares 20 governing cases plus 15 supplemental controls", "20 governing-plan scenarios + 15 supplemental stress controls (35 total)" in battery, "battery size line")
        self.add("Battery index contains every S01–S35 card link", all(f"cards/{s}.md" in battery for s in all_ids), [s for s in sorted(all_ids) if f"cards/{s}.md" not in battery])
        required_plan_concepts = [
            "gradual component-by-component", "destructive scan", "nondestructive exact copy",
            "source deletion later", "two simultaneous exact targets", "temporal gap",
            "long-lived source-target overlap", "distributed extension", "independent divergence",
            "later fusion", "public-perfect", "different binding or action-credit", "external decoder",
            "restoring current observables but changing predictive state", "without a global package",
            "viability boundary", "endogenous repair", "reversible round trip", "rescaled clock",
            "representation or gauge change",
        ]
        self.add("Battery explicitly names all twenty governing-plan thought experiments", all(x in battery_l for x in required_plan_concepts), [x for x in required_plan_concepts if x not in battery_l])
        self.add("Battery states that no scenario defines transfer for the others", "no scenario defines transfer for the others" in battery_l, "anti-paradigm rule")
        self.add("Battery keeps target, lineage, autonomy, and ontology as candidate outputs", all(x in battery_l for x in ["remain candidate outputs", "whether a target package exists", "whether operational edges become lineage edges", "every ontological or personal-identity interpretation"]), "facts/outputs boundary")

        # 7. Outcome taxonomy.
        outcome_rows = self.csv_rows("scenarios/OUTCOME_LABEL_REGISTRY.csv")
        outcome_ids = {x["outcome_id"] for x in outcome_rows}
        self.add("Outcome registry contains 27 unique labels", len(outcome_rows) == 27 and len(outcome_ids) == 27, {"rows": len(outcome_rows), "unique": len(outcome_ids)})
        lane_counts = Counter(x["claim_lane"] for x in outcome_rows)
        self.add("Outcome labels cover exactly S-T, S-R, S-L, A, and R", set(lane_counts) == {"S-T", "S-R", "S-L", "A", "R"}, lane_counts)
        self.add("Every label has a neutral meaning and blocked inference", all(all(x[k].strip() for k in ["label", "neutral_meaning", "blocked_inference"]) for x in outcome_rows), "27/27")
        taxonomy = (r / "scenarios/OUTCOME_TAXONOMY.md").read_text(encoding="utf-8")
        taxonomy_l = taxonomy.lower()
        required_outcomes = [
            "no valid target package", "target package exists but no declared lineage relation reaches it",
            "structural successor", "one-to-one lineage continuation", "branch-valued continuation",
            "fusion-valued continuation", "public duplicate with hidden mismatch",
            "package-equivalent duplicate with unresolved token identity", "bridge-dependent shadow",
            "autonomous target realization", "indeterminate under the declared instruments",
            "empty target after viability failure",
        ]
        self.add("Taxonomy maps all twelve governing-plan outcome concepts", all(x in taxonomy_l for x in required_outcomes), [x for x in required_outcomes if x not in taxonomy_l])
        forbidden_label_terms = ["same_person", "survives", "dies", "death", "conscious", "soul", "true_identity"]
        label_bad = [x["outcome_id"] for x in outcome_rows if any(t in x["label"].lower() for t in forbidden_label_terms)]
        self.add("Canonical outcome labels avoid metaphysically loaded terms", not label_bad, label_bad)
        self.add("Taxonomy is explicitly candidate-output vocabulary with no preclassified scenario", "candidate-output vocabulary" in taxonomy_l and "no scenario is preclassified" in taxonomy_l, "taxonomy status")
        self.add("Underdetermination requires a typed basis", all(x in taxonomy_l for x in ["criterion_underspecified", "scenario_underspecified", "symmetry_nonselection", "route_dependence", "instrument_nonidentifiability", "assumption_dependence", "out_of_scope"]), "seven bases")
        self.add("No outcome label licenses an O claim", "no label in this taxonomy licenses an `o` claim" in taxonomy_l, "ontology boundary")

        # 8. Discriminator, question, and asset crosswalks.
        disc_def = {x.get("id"): x for x in discriminators}
        self.add("Registry contains the ten required discriminators D01–D10", len(discriminators) == 10 and set(disc_def) == discriminator_ids, sorted(disc_def))
        disc_blob = " ".join((x.get("label", "") + " " + x.get("question", "")).lower() for x in discriminators)
        disc_concepts = ["predictive", "admissible continuation", "temporal overlap", "recombination", "viability", "action-credit", "holonomy", "autonomous closure", "defect", "branching"]
        self.add("Discriminators cover all ten governing-plan distinctions", all(x in disc_blob for x in disc_concepts), [x for x in disc_concepts if x not in disc_blob])
        disc_rows = self.csv_rows("ledgers/scenario_discriminator_matrix.csv")
        pairs = {(x["scenario_id"], x["discriminator_id"]) for x in disc_rows}
        self.add("Discriminator matrix is the complete 35×10 Cartesian product", len(disc_rows) == 350 and pairs == {(s, d) for s in all_ids for d in discriminator_ids}, {"rows": len(disc_rows), "pairs": len(pairs)})
        self.add("Every discriminator row permits answer, explicit underdetermination, or scoped nonapplicability", all(all(term in x["required_response"] for term in ["answer", "underdetermined", "not_applicable"]) for x in disc_rows), "350/350")
        valid_relevance = {"primary", "secondary", "mandatory"}
        self.add("Discriminator relevance uses a controlled vocabulary", all(x["relevance"] in valid_relevance for x in disc_rows), Counter(x["relevance"] for x in disc_rows))
        primaries = defaultdict(set)
        for x in disc_rows:
            if x["relevance"] in {"primary", "mandatory"}:
                primaries[x["scenario_id"]].add(x["discriminator_id"])
        self.add("Every scenario has at least four primary/mandatory discriminators", all(len(primaries[s]) >= 4 for s in all_ids), {s: len(primaries[s]) for s in sorted(all_ids)})
        self.add("Autonomy and continuation-cardinality probes are primary/mandatory in every scenario", all({"D08", "D10"} <= primaries[s] for s in all_ids), {s: sorted({"D08", "D10"} - primaries[s]) for s in sorted(all_ids) if not {"D08", "D10"} <= primaries[s]})
        self.add("All discriminator claim lanes use the canonical vocabulary", all(set(self.split_ids(x["claim_lanes"])) <= canonical_lanes for x in disc_rows), "350/350")

        qtext = (r / "ledgers/exploration_question_bank.yml").read_text(encoding="utf-8")
        qids = set(re.findall(r"^\s*(?:-\s*)?id:\s*(Q-[A-Z]+-\d+)\s*$", qtext, flags=re.MULTILINE))
        qrows = self.csv_rows("ledgers/scenario_question_crosswalk.csv")
        qpairs = [(x["scenario_id"], x["question_id"]) for x in qrows]
        self.add("Scenario-question crosswalk has 1,278 unique valid rows", len(qrows) == 1278 and len(set(qpairs)) == 1278 and all(x["scenario_id"] in all_ids and x["question_id"] in qids for x in qrows), {"rows": len(qrows), "unique": len(set(qpairs)), "bank_ids": len(qids)})
        core_ids = {f"Q-CORE-{i:03d}" for i in range(1, 13)}
        by_q = defaultdict(set)
        for x in qrows:
            by_q[x["scenario_id"]].add(x["question_id"])
        self.add("Every scenario is linked to all twelve governing core questions", all(core_ids <= by_q[s] for s in all_ids), {s: sorted(core_ids - by_q[s]) for s in sorted(all_ids) if not core_ids <= by_q[s]})
        self.add("Every scenario has at least ten tailored questions beyond the core", all(len(by_q[s] - core_ids) >= 10 for s in all_ids), {s: len(by_q[s] - core_ids) for s in sorted(all_ids)})

        asset_ids = {x["asset_id"] for x in assets}
        arows = self.csv_rows("ledgers/scenario_asset_crosswalk.csv")
        apairs = [(x["scenario_id"], x["asset_id"]) for x in arows]
        self.add("Scenario-asset crosswalk has 164 unique valid rows", len(arows) == 164 and len(set(apairs)) == 164 and all(x["scenario_id"] in all_ids and x["asset_id"] in asset_ids for x in arows), {"rows": len(arows), "unique": len(set(apairs))})
        self.add("Every scenario imports at least three corpus asset families", all(sum(1 for x in arows if x["scenario_id"] == s) >= 3 for s in all_ids), {s: sum(1 for x in arows if x["scenario_id"] == s) for s in sorted(all_ids)})
        self.add("Every scenario asset import preserves fixed-support scope and imports no verdict", all(all(t in x["import_rule"] for t in ["fixed-support", "nonclaim", "no scenario verdict imported"]) for x in arows), "164/164")
        disc_bad_refs: list[str] = []
        for x in disc_rows:
            if not set(self.split_ids(x["asset_ids"])) <= asset_ids:
                disc_bad_refs.append(f"{x['scenario_id']}:{x['discriminator_id']}:asset")
            if not set(self.split_ids(x["question_bank_ids"])) <= qids:
                disc_bad_refs.append(f"{x['scenario_id']}:{x['discriminator_id']}:question")
        self.add("All discriminator asset and question references resolve", not disc_bad_refs, disc_bad_refs)

        # 9. Candidate verdict contract and exit gate.
        verdict_rows = self.csv_rows("ledgers/scenario_verdict_template.csv")
        self.add("Verdict template contains one row for every S01–S35 case", len(verdict_rows) == 35 and {x["scenario_id"] for x in verdict_rows} == all_ids, len(verdict_rows))
        outcome_fields = ["st_outcome_id", "sr_outcome_id", "sl_outcome_id", "autonomy_outcome_id", "recognition_outcome_id"]
        self.add("All 175 candidate output cells remain UNFILLED", all(x[f] == "UNFILLED" for x in verdict_rows for f in outcome_fields), sum(1 for x in verdict_rows for f in outcome_fields if x[f] == "UNFILLED"))
        required_verdict_fields = ["underdetermination_basis", "criterion_sensitive_scenario_fields", "assumptions_spent", "route_sensitivity", "approximation_scope", "evidence_or_argument", "blocked_inferences", "nonclaims"]
        self.add("Verdict rows require assumptions, route/approximation scope, evidence, blocks, nonclaims, and underdetermination basis", all(k in verdict_rows[0] for k in required_verdict_fields), required_verdict_fields)
        verdict_yaml = (r / "templates/SCENARIO_VERDICT_RECORD.yml").read_text(encoding="utf-8")
        self.add("YAML contract requires S01–S35 and all five typed outcome fields", all(x in verdict_yaml for x in ["S01..S35", "st_outcome_id", "sr_outcome_id", "sl_outcome_id", "autonomy_outcome_id", "recognition_outcome_id", "underdetermination_basis"]), "YAML contract")
        exit_audit = (r / "scenarios/EXIT_GATE_AUDIT.md").read_text(encoding="utf-8")
        self.add("Scenario exit audit records all required outputs as PASS", exit_audit.count("| PASS |") >= 8 and "PASS subject to validator" in exit_audit, {"pass_rows": exit_audit.count('| PASS |')})
        self.add("Exit gate requires typed verdict or explicit underdetermination for every battery case", "typed verdict" in exit_audit.lower() and "underdetermined" in exit_audit.lower() and "35" in exit_audit, "exit contract")
        self.add("Exit gate forbids any single scenario from defining transfer", "No scenario has been allowed to define the meaning of transfer" in exit_audit or "No single scenario" in exit_audit, "anti-paradigm rule")

        # 10. Governance, phase state, and nonselection.
        decisions = self.csv_rows("ledgers/decision_log.csv")
        d_ids = {x["id"] for x in decisions}
        expected_d02 = {f"D02-{i:03d}" for i in range(1, 15)}
        self.add("Decision ledger retains 18 D00, 12 D01, and 14 D02 rulings", len(decisions) == 44 and {f"D00-{i:03d}" for i in range(1, 19)} <= d_ids and {f"D01-{i:03d}" for i in range(1, 13)} <= d_ids and expected_d02 <= d_ids, {"rows": len(decisions), "missing_D02": sorted(expected_d02 - d_ids)})
        human_decisions = (r / "ledgers/DECISION_LOG.md").read_text(encoding="utf-8")
        self.add("Human decision log mirrors every machine decision ID", all(x in human_decisions for x in d_ids), len(d_ids))
        rejected = (r / "ledgers/REJECTED_DEFAULTS.md").read_text(encoding="utf-8")
        unresolved = (r / "ledgers/UNRESOLVED_QUESTIONS.md").read_text(encoding="utf-8")
        self.add("Eighteen rejected defaults RD02-001–RD02-018 are recorded", all(f"RD02-{i:03d}" in rejected for i in range(1, 19)), "18/18")
        self.add("Sixteen phase-specific unresolved questions 45–60 remain open", all(re.search(rf"^\s*{i}\.\s", unresolved, flags=re.MULTILINE) for i in range(45, 61)), "16/16")

        state_text = "\n".join((r / x).read_text(encoding="utf-8") for x in ["README.md", "STATE.md", "STATUS.md", "CHANGELOG.md", "changelog/CST-EXP-02.md"])
        state_l = state_text.lower()
        self.add("Repository state declares CST-EXP-02 complete and CST-EXP-03 next", "Current completed phase:** `CST-EXP-02`" in state_text and "CST-EXP-03" in state_text and "**Exit gate:** PASS" in state_text, "state headers")
        nonselection_alternatives = {
            "transported object": ["no transported object"],
            "bridge": ["no preferred bridge", "no transported object or bridge type selected"],
            "lineage": ["no lineage criterion", "no continuation or personal-identity criterion"],
            "theorem": ["no theorem target", "no theorem conjecture selected", "no theorem conjecture freeze"],
            "toy": ["no toy program"],
            "verdict": ["no scenario verdict"],
        }
        missing_nonselection = [name for name, phrases in nonselection_alternatives.items() if not any(p in state_l for p in phrases)]
        self.add("Repository state preserves every phase nonselection boundary", not missing_nonselection, missing_nonselection)

        expected_counts = {
            "battery_scenarios": 35, "governing_plan_scenarios": 20,
            "supplemental_stress_controls": 15, "protocol_axes": 10,
            "axis_values": 44, "outcome_labels": 27, "discriminators": 10,
            "scenario_discriminator_rows": 350,
            "scenario_question_crosswalk_rows": 1278,
            "scenario_asset_crosswalk_rows": 164,
            "scenario_cards": 35, "unfilled_verdict_rows": 35,
        }
        asset_summary = self.json_data("manifests/EXP02_ASSET_SUMMARY.json")
        self.add("Generated EXP-02 summary matches every live phase count", all(asset_summary.get("counts", {}).get(k) == v for k, v in expected_counts.items()), asset_summary.get("counts", {}))
        self.add("Generated summary records no target, verdict, theorem, or program selection", asset_summary.get("target_selected") is False and asset_summary.get("scenario_verdicts_selected") is False and asset_summary.get("theorem_or_program_implemented") is False, "all false")
        phase_summary = self.json_data("manifests/PHASE_SUMMARY.json")
        self.add("Frozen phase summary records complete/pass/frozen CST-EXP-02 with CST-EXP-03 next", phase_summary.get("phase") == "CST-EXP-02" and phase_summary.get("status") == "complete" and phase_summary.get("exit_gate") == "pass" and phase_summary.get("repository_state") == "frozen" and phase_summary.get("next_phase") == "CST-EXP-03", {k: phase_summary.get(k) for k in ["phase", "status", "exit_gate", "repository_state", "next_phase"]})
        self.add("Frozen phase summary matches all live scenario counts", all(phase_summary.get("counts", {}).get(k) == v for k, v in expected_counts.items()), phase_summary.get("counts", {}))
        self.add("Frozen phase summary records no scientific target or implementation", phase_summary.get("target_selected") is False and phase_summary.get("scenario_verdicts_selected") is False and phase_summary.get("scientific_conclusion_selected") is False and phase_summary.get("theorem_or_program_implemented") is False, "all false")

        rebuild_verification = self.json_data("manifests/REBUILD_VERIFICATION.json")
        self.add("Portable rebuild reproduced all 55 deterministic phase-02 surfaces byte-for-byte", rebuild_verification.get("result") == "pass" and rebuild_verification.get("compared_files") == 55 and bool(re.fullmatch(r"[0-9a-f]{64}", rebuild_verification.get("hash_map_sha256", ""))), rebuild_verification)
        rv = rebuild_verification.get("rebuild_validator", {})
        self.add("Portable rebuilt repository passed the full validator", rv.get("status") == "pass" and rv.get("checks_passed") == 113 and rv.get("checks_total") == 113, rv)

        leakage: list[str] = []
        for d in ["candidates", "challenges", "feasibility", "synthesis"]:
            for p in (r / d).rglob("*"):
                if p.is_file() and p.name != ".gitkeep":
                    leakage.append(str(p.relative_to(r)))
        self.add("Later candidate, challenge, feasibility, and synthesis phases remain unexecuted", not leakage, leakage)

        # 11. Scripts, links, encoding, caches, and manifest.
        py_files = [
            "scripts/extract_corpus.py", "scripts/build_exp01_assets.py",
            "scripts/enrich_exp01_assets.py", "scripts/validate_exp01.py",
            "scripts/build_exp02_assets.py", "scripts/exp02_supplemental.py",
            "scripts/finalize_exp02_manifest.py", "scripts/validate_exp02.py",
        ]
        compile_bad: list[str] = []
        for rel in py_files:
            try:
                source = (r / rel).read_text(encoding="utf-8")
                compile(source, rel, "exec")
            except Exception as exc:
                compile_bad.append(f"{rel}:{exc}")
        self.add("All retained CST-EXP Python sources compile without emitting cache files", not compile_bad, compile_bad or f"{len(py_files)}/{len(py_files)}")
        shell_bad: list[str] = []
        for rel in ["scripts/rebuild_exp01.sh", "scripts/rebuild_exp02.sh"]:
            proc = subprocess.run(["bash", "-n", str(r / rel)], capture_output=True, text=True)
            if proc.returncode:
                shell_bad.append(f"{rel}:{proc.stderr.strip()}")
        self.add("EXP-01 and EXP-02 rebuild scripts pass shell syntax", not shell_bad, shell_bad or "2/2")

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
                if "," in dest or not any(ch in dest for ch in ("/", ".", "#", ":")):
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
        self.add("All local Markdown file links resolve", not broken_links, broken_links[:50])

        text_errors: list[str] = []
        symlinks: list[str] = []
        empty_files: list[str] = []
        cache_files: list[str] = []
        proof_or_toy_files: list[str] = []
        text_suffixes = {".md", ".csv", ".json", ".yml", ".yaml", ".py", ".sh", ".txt", ".dot", ".mmd", ".toml"}
        for p in r.rglob("*"):
            rel = p.relative_to(r)
            if ".git" in rel.parts:
                continue
            if p.is_symlink():
                symlinks.append(str(rel))
            elif p.is_file():
                if "__pycache__" in rel.parts or p.suffix == ".pyc":
                    cache_files.append(str(rel))
                if p.suffix.lower() in {".lean", ".olean", ".ipynb"}:
                    proof_or_toy_files.append(str(rel))
                if p.stat().st_size == 0 and p.name != ".gitkeep":
                    empty_files.append(str(rel))
                if p.suffix.lower() in text_suffixes:
                    try:
                        p.read_text(encoding="utf-8")
                    except Exception as exc:
                        text_errors.append(f"{rel}:{exc}")
        self.add("Repository contains no symlinks", not symlinks, symlinks)
        self.add("All text artifacts are UTF-8 readable", not text_errors, text_errors)
        self.add("No unintended empty files remain", not empty_files, empty_files)
        self.add("No generated Python cache files remain", not cache_files, cache_files)
        self.add("No Lean proof, compiled proof, notebook, or toy-program artifact was introduced", not proof_or_toy_files, proof_or_toy_files)

        if not self.skip_manifest:
            manifest_path = r / "manifests/MANIFEST.json"
            checksum_path = r / "manifests/SHA256SUMS"
            manifest_ok = manifest_path.is_file() and checksum_path.is_file()
            manifest_bad: list[str] = []
            checksum_bad: list[str] = []
            entries: list[dict] = []
            if manifest_ok:
                try:
                    manifest = json.loads(manifest_path.read_text(encoding="utf-8"))
                    entries = manifest.get("files", [])
                    for entry in entries:
                        p = r / entry["path"]
                        if not p.is_file() or p.stat().st_size != int(entry["size_bytes"]) or self.sha(p) != entry["sha256"]:
                            manifest_bad.append(entry["path"])
                    parsed: dict[str, str] = {}
                    for line in checksum_path.read_text(encoding="utf-8").splitlines():
                        m = re.match(r"^([0-9a-f]{64})\s+\*?(.+)$", line)
                        if m:
                            parsed[m.group(2)] = m.group(1)
                    expected = {x["path"]: x["sha256"] for x in entries}
                    if parsed != expected:
                        checksum_bad = sorted(set(parsed) ^ set(expected))
                        checksum_bad += [p for p in set(parsed) & set(expected) if parsed[p] != expected[p]]
                except Exception as exc:
                    manifest_bad.append(str(exc))
            self.add("Content manifest and SHA256SUMS match every frozen file", manifest_ok and bool(entries) and not manifest_bad and not checksum_bad, {"entries": len(entries), "manifest_bad": manifest_bad[:20], "checksum_bad": checksum_bad[:20]})

    def write(self, report: Path, json_path: Path) -> int:
        passed = sum(x.passed for x in self.results)
        total = len(self.results)
        status = "PASS" if passed == total else "FAIL"
        now = datetime.now(timezone.utc).isoformat()
        lines = [
            "# CST-EXP-02 Validation Report", "",
            f"**Generated:** {now}",
            f"**Result:** **{status}**",
            f"**Checks passed:** **{passed}/{total}**",
            "**Scope:** completeness and coherence of the neutral source–target schema, 20 governing-plan scenarios, 15 supplemental controls, ten-axis matrix, lane-typed outcome vocabulary, discriminator/question/asset crosswalks, inherited corpus controls, and strict nonselection boundary. This is not evidence that consciousness transfers or that personal identity is preserved.", "",
            "## Executed checks", "",
            "| # | Check | Result | Evidence |", "|---:|---|---:|---|",
        ]
        for i, item in enumerate(self.results, 1):
            evidence = item.evidence.replace("|", "\\|")
            if len(evidence) > 900:
                evidence = evidence[:897] + "…"
            lines.append(f"| {i} | {item.name} | {'PASS' if item.passed else 'FAIL'} | {evidence} |")
        lines += ["", "## Exit-gate ruling", ""]
        if status == "PASS":
            lines.append("**PASS.** CST-EXP-02 supplies a neutral, carrier-typed protocol language and a complete 35-case stress battery. Every later candidate must return separately typed transport, target-realization, lineage, autonomy, and recognition outputs—or explicit underdetermination/nonapplicability—without any scenario, operational edge, or source-fate fact predefining continuation.")
        else:
            failed = [x.name for x in self.results if not x.passed]
            lines.append("**FAIL.** The phase must not be frozen until these checks are repaired: " + "; ".join(failed) + ".")
        report.parent.mkdir(parents=True, exist_ok=True)
        report.write_text("\n".join(lines) + "\n", encoding="utf-8")
        payload = {
            "project": "CST-EXP", "phase": "CST-EXP-02", "generated_at_utc": now,
            "status": status.lower(), "checks_passed": passed, "checks_total": total,
            "manifest_check_skipped": self.skip_manifest,
            "results": [asdict(x) for x in self.results],
        }
        json_path.parent.mkdir(parents=True, exist_ok=True)
        json_path.write_text(json.dumps(payload, indent=2, ensure_ascii=False) + "\n", encoding="utf-8")
        print(json.dumps({"status": status, "passed": passed, "total": total, "report": str(report), "skip_manifest": self.skip_manifest}, indent=2))
        return 0 if status == "PASS" else 1


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", type=Path, required=True)
    parser.add_argument("--report", type=Path)
    parser.add_argument("--json", dest="json_path", type=Path)
    parser.add_argument("--skip-manifest", action="store_true")
    args = parser.parse_args()
    root = args.repo.resolve()
    report = args.report or root / "manifests/VALIDATION_REPORT.md"
    json_path = args.json_path or root / "manifests/VALIDATION_RESULTS.json"
    validator = Validator(root, skip_manifest=args.skip_manifest)
    validator.run()
    return validator.write(report, json_path)


if __name__ == "__main__":
    raise SystemExit(main())
