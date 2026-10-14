#!/usr/bin/env python3
"""Validate CST-EXP-03 candidate generation and cross-carrier bridge design.

The validator checks completeness, typing, provenance, scenario coverage,
anti-conflation discipline, and nonselection. It does not establish any
candidate theorem, consciousness claim, survival claim, or personal identity.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from dataclasses import asdict, dataclass
from pathlib import Path
from urllib.parse import unquote

import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent))
import exp03_data as D  # noqa: E402


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
        if isinstance(evidence, Counter):
            evidence = {str(k): v for k, v in evidence.items()}
        if isinstance(evidence, set):
            evidence = sorted(evidence, key=str)
        if isinstance(evidence, (dict, list, tuple)):
            text = json.dumps(evidence, ensure_ascii=False, sort_keys=True, default=str)
        else:
            text = str(evidence)
        self.results.append(Result(name, bool(ok), text.replace("\n", " ")))

    def rows(self, rel: str) -> list[dict[str, str]]:
        with (self.root / rel).open(newline="", encoding="utf-8") as fh:
            return list(csv.DictReader(fh))

    def json(self, rel: str):
        return json.loads((self.root / rel).read_text(encoding="utf-8"))

    @staticmethod
    def split_ids(value: str) -> list[str]:
        return [x.strip() for x in str(value).split(";") if x.strip()]

    @staticmethod
    def sha(path: Path) -> str:
        h = hashlib.sha256()
        with path.open("rb") as fh:
            for chunk in iter(lambda: fh.read(1024 * 1024), b""):
                h.update(chunk)
        return h.hexdigest()

    def run(self) -> None:
        r = self.root
        candidate_ids = {f"TS-{i:02d}" for i in range(1, 11)}
        scenario_ids = {f"S{i:02d}" for i in range(1, 36)}
        object_ids = {f"TO-{i:02d}" for i in range(1, 16)}
        invariant_ids = {f"IV-{i:02d}" for i in range(1, 13)}
        bridge_ids = {f"BR-{i:02d}" for i in range(1, 13)}
        lane_fields = {
            "st_outcome_id": "S-T",
            "sr_outcome_id": "S-R",
            "sl_outcome_id": "S-L",
            "autonomy_outcome_id": "A",
            "recognition_outcome_id": "R",
        }

        # 1. Required artifacts and parseability.
        required = [
            "README.md", "STATE.md", "STATUS.md", "CHANGELOG.md",
            "changelog/CST-EXP-03.md",
            "candidates/TRANSPORTED_OBJECT_ATLAS.md",
            "candidates/INVARIANT_ATLAS.md",
            "candidates/BRIDGE_DESIGN_SPACE.md",
            "candidates/CANDIDATE_REGISTRY.json",
            "candidates/CANDIDATE_COMPARISON_GUIDE.md",
            "candidates/EXIT_GATE_AUDIT.md",
            "candidates/transported_object_registry.csv",
            "candidates/invariant_registry.csv",
            "candidates/bridge_registry.csv",
            "candidates/brainstorms/INDEX.md",
            "candidates/brainstorms/BRAINSTORM_FREEZE.sha256",
            "candidates/target_schemas/INDEX.md",
            "candidates/candidate_design_space.dot",
            "candidates/candidate_design_space.svg",
            "candidates/candidate_design_space.png",
            "ledgers/candidate_feature_matrix.csv",
            "ledgers/new_primitive_register.csv",
            "ledgers/candidate_scenario_verdicts.csv",
            "ledgers/candidate_question_responses.csv",
            "ledgers/candidate_anti_conflation_audit.csv",
            "ledgers/candidate_asset_crosswalk.csv",
            "ledgers/candidate_assumption_matrix.csv",
            "ledgers/candidate_discriminator_crosswalk.csv",
            "ledgers/candidate_divergence_matrix.csv",
            "synthesis/CST-EXP-03_CANDIDATE_GENERATION_SYNTHESIS.md",
            "scripts/build_exp03_assets.py",
            "scripts/exp03_data.py",
            "scripts/validate_exp03.py",
            "scripts/finalize_exp03_manifest.py",
            "scripts/rebuild_exp03.sh", "scripts/verify_exp03_rebuild.py",
            "manifests/EXP03_ASSET_SUMMARY.json",
            "inputs/normative/PREPARATORY_EXPLORATION_PLAN.md",
        ] + [f"candidates/brainstorms/{x['file']}" for x in D.BRAINSTORMS] + [f"candidates/target_schemas/{cid}.md" for cid in sorted(candidate_ids)]
        if not self.skip_manifest:
            required += [
                "manifests/PHASE_SUMMARY.json", "manifests/MANIFEST.json",
                "manifests/SHA256SUMS", "manifests/REPO_TREE.txt",
                "manifests/CST-EXP-03_COMPLETION_REPORT.md",
                "manifests/RESTORE_AND_VERIFY.md",
                "manifests/REBUILD_VERIFICATION.md",
                "manifests/REBUILD_VERIFICATION.json",
            ]
        missing = [x for x in required if not (r / x).is_file()]
        self.add("All required CST-EXP-03 artifacts exist", not missing, {"required": len(required), "missing": missing})
        empty = [x for x in required if (r / x).is_file() and (r / x).stat().st_size == 0]
        self.add("Required CST-EXP-03 artifacts are nonempty", not empty, empty or len(required))

        csv_files = [
            "candidates/transported_object_registry.csv", "candidates/invariant_registry.csv",
            "candidates/bridge_registry.csv", "ledgers/candidate_feature_matrix.csv",
            "ledgers/new_primitive_register.csv", "ledgers/candidate_scenario_verdicts.csv",
            "ledgers/candidate_question_responses.csv", "ledgers/candidate_anti_conflation_audit.csv",
            "ledgers/candidate_asset_crosswalk.csv", "ledgers/candidate_assumption_matrix.csv",
            "ledgers/candidate_discriminator_crosswalk.csv", "ledgers/candidate_divergence_matrix.csv",
            "ledgers/decision_log.csv", "ledgers/assumption_register.csv",
            "ledgers/asset_provenance.csv", "scenarios/OUTCOME_LABEL_REGISTRY.csv",
        ]
        csv_errors: list[str] = []
        for rel in csv_files:
            try:
                rows = self.rows(rel)
                if not rows:
                    csv_errors.append(f"{rel}: no data rows")
            except Exception as exc:
                csv_errors.append(f"{rel}: {exc}")
        self.add("All phase and inherited CSV ledgers parse", not csv_errors, csv_errors or len(csv_files))

        json_files = ["candidates/CANDIDATE_REGISTRY.json", "scenarios/SCENARIO_REGISTRY.json", "manifests/EXP03_ASSET_SUMMARY.json"]
        if not self.skip_manifest:
            json_files += ["manifests/PHASE_SUMMARY.json", "manifests/MANIFEST.json", "manifests/REBUILD_VERIFICATION.json"]
        json_errors: list[str] = []
        for rel in json_files:
            try:
                self.json(rel)
            except Exception as exc:
                json_errors.append(f"{rel}: {exc}")
        self.add("Phase registries and metadata JSON parse", not json_errors, json_errors or len(json_files))

        yaml_errors: list[str] = []
        for rel in ["ledgers/exploration_question_bank.yml", "ledgers/assumption_register.yml", "ledgers/claim_tag_registry.yml"]:
            try:
                yaml.safe_load((r / rel).read_text(encoding="utf-8"))
            except Exception as exc:
                yaml_errors.append(f"{rel}: {exc}")
        self.add("Inherited YAML governance files parse", not yaml_errors, yaml_errors or 3)

        # 2. Inherited corpus and phase controls.
        exp02_result = self.json("manifests/CST-EXP-02_VALIDATION_RESULTS.json")
        self.add("Retained CST-EXP-02 validation record is a pass", exp02_result.get("status") == "pass", exp02_result.get("status"))
        paper_inv = self.rows("corpus/machine_index/paper_inventory.csv")
        machine = self.rows("corpus/machine_index/all_statement_index.csv")
        prov = self.rows("ledgers/statement_provenance.csv")
        assets = self.rows("ledgers/asset_provenance.csv")
        maps = self.rows("ledgers/map_type_ledger.csv")
        lexical = self.rows("ledgers/lexical_dependency_index.csv")
        labels = self.rows("ledgers/source_label_index.csv")
        gaps = self.rows("ledgers/gap_to_asset_matrix.csv")
        duplicates = self.rows("ledgers/corpus_duplicate_map.csv")
        self.add("Frozen paper inventory remains P01–P60", len(paper_inv) == 60 and {x["paper_id"] for x in paper_inv} == {f"P{i:02d}" for i in range(1,61)}, len(paper_inv))
        self.add("Machine and curated statement banks retain 1,359 and 378 rows", len(machine) == 1359 and len(prov) == 378, {"machine":len(machine),"curated":len(prov)})
        self.add("Canonical asset bank retains 26 families and 196 links", len({x["asset_id"] for x in assets}) == 26 and len(assets) == 196, {"families":len({x['asset_id'] for x in assets}),"links":len(assets)})
        self.add("Typed maps, lexical dependencies, source labels, and gaps remain frozen", (len(maps),len(lexical),len(labels),len(gaps)) == (106,1359,3658,14), {"maps":len(maps),"lexical":len(lexical),"labels":len(labels),"gaps":len(gaps)})
        self.add("All 18 embedded duplicate manuscripts remain mapped", len(duplicates) == 18, len(duplicates))
        self.add("P46 remains substantively quarantined", not any(x["paper_id"] == "P46" for x in machine) and sum(1 for x in prov if x["paper_id"] == "P46") == 1 and next(x for x in prov if x["paper_id"] == "P46")["selection_status"] == "excluded", "machine=0; curated exclusion=1")
        version_log = (r / "ledgers/version_and_exclusion_log.md").read_text(encoding="utf-8").lower()
        self.add("P42 remains normative and P60 has zero independent evidential weight", all(x in version_log for x in ["p42","p60","normative","zero independent"]), "version log")
        source_pins: dict[str,str] = {}
        for line in (r / "manifests/SOURCE_SHA256SUMS").read_text(encoding="utf-8").splitlines():
            m = re.match(r"^([0-9a-f]{64})\s+\*?(.+)$", line.strip())
            if m:
                source_pins[m.group(2)] = m.group(1)
        pin_bad = [rel for rel,h in source_pins.items() if not (r/rel).is_file() or self.sha(r/rel) != h]
        self.add("Normative/source files retain pinned hashes", bool(source_pins) and not pin_bad, {"pinned":len(source_pins),"bad":pin_bad})

        # 3. Transported-object atlas.
        objects = self.rows("candidates/transported_object_registry.csv")
        self.add("Transported-object registry has 15 unique entries", len(objects) == 15 and {x["id"] for x in objects} == object_ids, len(objects))
        self.add("Every transported object has a typed skeleton", all(x["type_skeleton"].strip() for x in objects), [x["id"] for x in objects if not x["type_skeleton"].strip()])
        self.add("Every transported object records dependence/status profile", all(x["status_profile"].strip() for x in objects), [x["id"] for x in objects if not x["status_profile"].strip()])
        self.add("Every transported object records promise and failure surface", all(x["promise"].strip() and x["failure_surface"].strip() for x in objects), [x["id"] for x in objects if not x["promise"].strip() or not x["failure_surface"].strip()])
        self.add("Every transported object records cross-carrier debt", all("need" in x["cross_carrier_debt"].lower() for x in objects), [x["id"] for x in objects if "need" not in x["cross_carrier_debt"].lower()])
        object_blob = " ".join((x["name"]+" "+x["kind"]).lower() for x in objects)
        mandatory_object_terms = ["c1–c8", "predictive quotient", "predictive transition", "continuation algebra", "closure", "viability", "self-coordinate", "temporal", "recombination", "action-credit", "quality-space", "event package", "relation among", "error-corrected", "minimal"]
        self.add("Object atlas covers every governing-plan object family", all(t in object_blob for t in mandatory_object_terms), [t for t in mandatory_object_terms if t not in object_blob])
        valid_asset_ids = {x["asset_id"] for x in assets}
        bad_object_assets = sorted({aid for x in objects for aid in self.split_ids(x["assets"]) if aid not in valid_asset_ids})
        self.add("Transported-object asset references resolve", not bad_object_assets, bad_object_assets or "all resolve")
        used_objects = {oid for c in D.CANDIDATES for oid in self.split_ids(c["object_ids"])}
        self.add("Every non-atlas-only object is used by a candidate", all(x["id"] in used_objects or "atlas-only" in x["candidate_use"] for x in objects), [x["id"] for x in objects if x["id"] not in used_objects and "atlas-only" not in x["candidate_use"]])

        # 4. Invariant atlas.
        invariants = self.rows("candidates/invariant_registry.csv")
        self.add("Invariant registry has 12 unique entries", len(invariants) == 12 and {x["id"] for x in invariants} == invariant_ids, len(invariants))
        audit_fields = ["necessity","sufficiency","composition","route","copy","approx","observability","hidden"]
        for field in audit_fields:
            self.add(f"Every invariant audits {field}", all(x[field].strip() for x in invariants), [x["id"] for x in invariants if not x[field].strip()])
        invariant_blob = " ".join((x["name"]+" "+x["signature"]).lower() for x in invariants)
        mandatory_inv_terms = ["quotient", "bisimulation", "continuation", "closure", "recombination", "viability", "holonomy", "c-package", "gauge", "residual", "ancestry"]
        self.add("Invariant atlas covers every governing-plan family", all(t in invariant_blob for t in mandatory_inv_terms), [t for t in mandatory_inv_terms if t not in invariant_blob])
        used_invariants = {iid for c in D.CANDIDATES for iid in self.split_ids(c["invariant_ids"])}
        self.add("Every registered invariant is used by at least one candidate", used_invariants == invariant_ids, sorted(invariant_ids-used_invariants))

        # 5. Bridge design space.
        bridges = self.rows("candidates/bridge_registry.csv")
        self.add("Bridge registry has 12 unique entries", len(bridges) == 12 and {x["id"] for x in bridges} == bridge_ids, len(bridges))
        for field in ["signature","best_for","composition","admissibility","risk"]:
            self.add(f"Every bridge records {field}", all(x[field].strip() for x in bridges), [x["id"] for x in bridges if not x[field].strip()])
        bridge_blob = " ".join((x["name"]+" "+x["signature"]).lower() for x in bridges)
        bridge_terms = ["state map", "history relation", "simulation", "bisimulation", "span", "cospan", "moving", "functor", "recover", "staged", "residual", "branch"]
        self.add("Bridge atlas covers all twelve required morphologies", all(t in bridge_blob for t in bridge_terms), [t for t in bridge_terms if t not in bridge_blob])
        used_bridges = {bid for c in D.CANDIDATES for bid in self.split_ids(c["bridge_ids"])}
        self.add("Every registered bridge is represented in candidate use or atlas-only analysis", all(x["id"] in used_bridges or "atlas" in x["candidates"].lower() for x in bridges), [x["id"] for x in bridges if x["id"] not in used_bridges and "atlas" not in x["candidates"].lower()])

        # 6. Independent brainstorming freeze.
        memo_paths = [r / "candidates/brainstorms" / x["file"] for x in D.BRAINSTORMS]
        self.add("Seven distinct brainstorming memos exist", len(memo_paths) == 7 and all(p.is_file() for p in memo_paths), [str(p) for p in memo_paths if not p.is_file()])
        self.add("Brainstorm lenses are unique", len({x["lens"] for x in D.BRAINSTORMS}) == 7, [x["lens"] for x in D.BRAINSTORMS])
        memo_ts = [p.name for p in memo_paths if re.search(r"\bTS-\d\d\b", p.read_text(encoding="utf-8"))]
        self.add("Frozen memo bytes contain no candidate IDs", not memo_ts, memo_ts or "none")
        freeze_rows = {}
        for line in (r / "candidates/brainstorms/BRAINSTORM_FREEZE.sha256").read_text(encoding="utf-8").splitlines():
            m = re.match(r"^([0-9a-f]{64})\s+(.+)$", line.strip())
            if m:
                freeze_rows[m.group(2)] = m.group(1)
        bad_freeze = [p.name for p in memo_paths if freeze_rows.get(p.name) != self.sha(p)]
        self.add("All seven brainstorming memo hashes match the freeze", len(freeze_rows) == 7 and not bad_freeze, {"rows":len(freeze_rows),"bad":bad_freeze})
        for x,p in zip(D.BRAINSTORMS,memo_paths):
            text = p.read_text(encoding="utf-8").lower()
            self.add(f"{p.name} contains starting point, ideas, tension, and boundary", all(k in text for k in ["starting point","ideas generated","internal tension","phase boundary"]), [k for k in ["starting point","ideas generated","internal tension","phase boundary"] if k not in text])
        bindex = (r / "candidates/brainstorms/INDEX.md").read_text(encoding="utf-8")
        self.add("Brainstorm index labels candidate mapping as post-freeze", "post-freeze candidate translations" in bindex, "index wording")

        # 7. Candidate registry, cards, and typing.
        registry = self.json("candidates/CANDIDATE_REGISTRY.json")
        candidates = registry["candidates"]
        by_cid = {x["id"]: x for x in candidates}
        self.add("Candidate registry has exactly TS-01–TS-10", len(candidates) == 10 and set(by_cid) == candidate_ids, {"count":len(candidates),"ids":sorted(by_cid)})
        self.add("Candidate registry counts match design data", registry.get("counts") == {"candidates":10,"transported_objects":15,"invariants":12,"bridges":12,"brainstorms":7}, registry.get("counts"))
        self.add("Candidate titles and slugs are unique", len({x["title"] for x in candidates}) == 10 and len({x["slug"] for x in candidates}) == 10, "10 unique titles/slugs")
        self.add("Primary lanes span S-T, S-R, S-L, and A", {x["primary_lane"] for x in candidates} == {"S-T","S-R","S-L","A"}, sorted({x["primary_lane"] for x in candidates}))
        required_candidate_fields = [
            "one_sentence","source_type","target_type","common_type","bridge_signature","bridge_kind","bridge_data","admissibility",
            "exact_invariants","approximate_version","route_policy","composition_rule","copy_rule","fission_rule","fusion_rule","deletion_rule",
            "target_scope","removal","autonomy_horizon","recognition","assumptions","assets","new_terms","theorem_shapes","no_go_shapes","toys",
            "positive_control","negative_control","adversarial","falsifier","nearest_alternative","minimal_model","kill_criteria","nonclaims","ontological_boundary",
        ]
        for field in required_candidate_fields:
            self.add(f"Every candidate populates {field}", all(str(x.get(field,"" )).strip() for x in candidates), [x["id"] for x in candidates if not str(x.get(field,"" )).strip()])
        for cid,c in sorted(by_cid.items()):
            self.add(f"{cid} uses separately typed source and target symbols", "X_S" in c["source_type"] and "X_T" in c["target_type"], {"source":c["source_type"],"target":c["target_type"]})
            self.add(f"{cid} has a nonempty common comparison type", bool(c["common_type"].strip()), c["common_type"])
            self.add(f"{cid} object references resolve", set(self.split_ids(c["object_ids"])) <= object_ids, self.split_ids(c["object_ids"]))
            self.add(f"{cid} invariant references resolve", set(self.split_ids(c["invariant_ids"])) <= invariant_ids, self.split_ids(c["invariant_ids"]))
            self.add(f"{cid} bridge references resolve", set(self.split_ids(c["bridge_ids"])) <= bridge_ids, self.split_ids(c["bridge_ids"]))
            self.add(f"{cid} asset references resolve", set(self.split_ids(c["assets"])) <= valid_asset_ids, sorted(set(self.split_ids(c["assets"]))-valid_asset_ids))
            card = (r / f"candidates/target_schemas/{cid}.md").read_text(encoding="utf-8")
            card_sections = ["One-sentence idea","Formal objects and types","Exact and approximate versions","Lane-separated contract","Route, composition, branching, and deletion","Assumption ladder","Controls and possible later theorem forms","Falsification and kill criteria","Explicit nonclaims"]
            self.add(f"{cid} card contains all required sections", all(s in card for s in card_sections), [s for s in card_sections if s not in card])
            self.add(f"{cid} card explicitly remains unranked and unselected", "unranked" in card.lower() and "not selected" in card.lower(), "card status")
            self.add(f"{cid} card explicitly withholds consciousness and personal-identity conclusions", "consciousness" in card.lower() and "personal identity" in card.lower() and "nonclaims" in card.lower(), "explicit nonclaim section")
        features = self.rows("ledgers/candidate_feature_matrix.csv")
        self.add("Feature matrix has one row per candidate", len(features) == 10 and {x["candidate_id"] for x in features} == candidate_ids, len(features))
        self.add("All candidates are marked distinct-carrier typed", all(x["distinct_carrier_typed"] == "yes" for x in features), [x["candidate_id"] for x in features if x["distinct_carrier_typed"] != "yes"])
        self.add("Ranking is withheld uniformly until CST-EXP-06", all(x["ranking"] == "withheld_until_CST-EXP-06" for x in features), Counter(x["ranking"] for x in features))
        self.add("Every candidate names a valid nearest alternative", all(x["nearest_alternative"] in candidate_ids-{x["candidate_id"]} for x in features), [(x["candidate_id"],x["nearest_alternative"]) for x in features if x["nearest_alternative"] not in candidate_ids-{x["candidate_id"]}])
        self.add("Every candidate has at least one distinguishing scenario", all(set(self.split_ids(x["distinguishing_scenarios"])) <= scenario_ids and self.split_ids(x["distinguishing_scenarios"]) for x in features), [(x["candidate_id"],x["distinguishing_scenarios"]) for x in features])

        # 8. Scenario verdict coverage and pairwise divergence.
        scenario_registry = self.json("scenarios/SCENARIO_REGISTRY.json")
        self.add("Inherited scenario registry still has 35 scenarios", len(scenario_registry["scenarios"]) == 35 and {x["id"] for x in scenario_registry["scenarios"]} == scenario_ids, len(scenario_registry["scenarios"]))
        outcomes = {x["outcome_id"]:x for x in self.rows("scenarios/OUTCOME_LABEL_REGISTRY.csv")}
        verdicts = self.rows("ledgers/candidate_scenario_verdicts.csv")
        self.add("Scenario ledger has 350 candidate–scenario rows", len(verdicts) == 350, len(verdicts))
        pair_keys = [(x["candidate_id"],x["scenario_id"]) for x in verdicts]
        self.add("Scenario ledger has every candidate × scenario pair exactly once", len(set(pair_keys)) == 350 and set(pair_keys) == set(itertools.product(candidate_ids,scenario_ids)), {"unique":len(set(pair_keys))})
        for cid in sorted(candidate_ids):
            cr = [x for x in verdicts if x["candidate_id"] == cid]
            self.add(f"{cid} covers all 35 scenarios", len(cr) == 35 and {x["scenario_id"] for x in cr} == scenario_ids, len(cr))
        bad_outcomes: list[str] = []
        lane_mismatches: list[str] = []
        for row in verdicts:
            for field,lane in lane_fields.items():
                oid = row[field]
                if oid not in outcomes:
                    bad_outcomes.append(f"{row['candidate_id']}/{row['scenario_id']}/{field}:{oid}")
                elif outcomes[oid]["claim_lane"] != lane:
                    lane_mismatches.append(f"{row['candidate_id']}/{row['scenario_id']}/{field}:{oid}->{outcomes[oid]['claim_lane']}")
        self.add("All 1,750 outcome cells reference registered labels", not bad_outcomes, bad_outcomes[:20] or 1750)
        self.add("All outcome labels are used only in their typed lane", not lane_mismatches, lane_mismatches[:20] or 1750)
        self.add("Every scenario verdict records basis, assumptions, evidence, blocked inference, and nonclaim", all(all(x[f].strip() for f in ["criterion_sensitive_scenario_fields","assumptions_spent","evidence_or_argument","blocked_inferences","nonclaims","status"]) for x in verdicts), [(x["candidate_id"],x["scenario_id"]) for x in verdicts if not all(x[f].strip() for f in ["criterion_sensitive_scenario_fields","assumptions_spent","evidence_or_argument","blocked_inferences","nonclaims","status"])][:20])
        self.add("All scenario rows are explicitly exploratory and unranked", all(x["status"] == "exploratory_expected_not_ranked" for x in verdicts), Counter(x["status"] for x in verdicts))
        self.add("Same-carrier control S20 is nonapplicable in S-T for every candidate", all(x["st_outcome_id"] == D.ST_NA for x in verdicts if x["scenario_id"] == "S20"), [(x["candidate_id"],x["st_outcome_id"]) for x in verdicts if x["scenario_id"] == "S20"])
        self.add("S20 also keeps target, lineage, and autonomy nonapplicable", all((x["sr_outcome_id"],x["sl_outcome_id"],x["autonomy_outcome_id"]) == (D.SR_NA,D.SL_NA,D.A_NT) for x in verdicts if x["scenario_id"] == "S20"), [(x["candidate_id"],x["sr_outcome_id"],x["sl_outcome_id"],x["autonomy_outcome_id"]) for x in verdicts if x["scenario_id"] == "S20"])
        self.add("Symmetric exact duplication S05 never yields one-to-one continuation", all(x["sl_outcome_id"] != D.SL_ONE for x in verdicts if x["scenario_id"] == "S05"), [(x["candidate_id"],x["sl_outcome_id"]) for x in verdicts if x["scenario_id"] == "S05"])
        self.add("Independent twin S26 never receives source-derived lineage", all(x["sl_outcome_id"] == D.SL_NO for x in verdicts if x["scenario_id"] == "S26"), [(x["candidate_id"],x["sl_outcome_id"]) for x in verdicts if x["scenario_id"] == "S26"])
        self.add("External-decoder case S13 never passes target autonomy", all(x["autonomy_outcome_id"] == D.A_SHADOW for x in verdicts if x["scenario_id"] == "S13"), [(x["candidate_id"],x["autonomy_outcome_id"]) for x in verdicts if x["scenario_id"] == "S13"])
        self.add("Certificate-only counterfeit S30 never receives target-package success", all(x["sr_outcome_id"] not in {D.SR_YES} for x in verdicts if x["scenario_id"] == "S30"), [(x["candidate_id"],x["sr_outcome_id"]) for x in verdicts if x["scenario_id"] == "S30"])

        by_sig = {(x["candidate_id"],x["scenario_id"]): tuple(x[f] for f in lane_fields) for x in verdicts}
        computed: dict[tuple[str,str],tuple[int,int,set[str]]] = {}
        for a,b in itertools.combinations(sorted(candidate_ids),2):
            cells=0; scenes=set()
            for sid in sorted(scenario_ids):
                av=by_sig[a,sid]; bv=by_sig[b,sid]
                n=sum(x!=y for x,y in zip(av,bv))
                cells += n
                if n: scenes.add(sid)
            computed[(a,b)] = (cells,len(scenes),scenes)
        self.add("Every candidate pair differs on at least one scenario/lane", all(v[0] > 0 for v in computed.values()), {f"{a}/{b}":v[0] for (a,b),v in computed.items() if v[0] == 0})
        div = self.rows("ledgers/candidate_divergence_matrix.csv")
        self.add("Pairwise divergence ledger has all 45 unordered pairs", len(div) == 45 and {(x["candidate_a"],x["candidate_b"]) for x in div} == set(computed), len(div))
        div_bad=[]
        for x in div:
            key=(x["candidate_a"],x["candidate_b"]); calc=computed.get(key)
            if not calc or int(x["differing_lane_cells"]) != calc[0] or int(x["differing_scenario_count"]) != calc[1] or set(self.split_ids(x["differing_scenarios"])) != calc[2]:
                div_bad.append(key)
        self.add("Divergence ledger agrees with recomputed signatures", not div_bad, div_bad or "45 pairs")
        hashes = [x["scenario_lane_signature_sha256"] for x in features]
        self.add("All candidate scenario signature hashes are unique", len(hashes) == len(set(hashes)) == 10, hashes)

        # 9. Mandatory question bank and guards.
        questions = yaml.safe_load((r / "ledgers/exploration_question_bank.yml").read_text(encoding="utf-8"))["questions"]
        question_ids = {x["id"] for x in questions}
        self.add("Frozen exploration question bank has 100 unique questions", len(questions) == 100 and len(question_ids) == 100, len(questions))
        qrows = self.rows("ledgers/candidate_question_responses.csv")
        self.add("Candidate question ledger has 1,000 rows", len(qrows) == 1000, len(qrows))
        qkeys={(x["candidate_id"],x["question_id"]) for x in qrows}
        self.add("Every candidate answers every mandatory question exactly once", len(qkeys) == 1000 and qkeys == set(itertools.product(candidate_ids,question_ids)), len(qkeys))
        self.add("All question responses are substantive and marked answered", all(x["status"] == "answered" and len(x["response"].strip()) >= 30 for x in qrows), [(x["candidate_id"],x["question_id"],len(x["response"].strip())) for x in qrows if x["status"] != "answered" or len(x["response"].strip()) < 30][:20])
        self.add("Every question response records claim tags, assumptions, provenance status, and nonclaims", all(all(x[f].strip() for f in ["claim_tags","assumptions","source_or_new_status","nonclaims"]) for x in qrows), [(x["candidate_id"],x["question_id"]) for x in qrows if not all(x[f].strip() for f in ["claim_tags","assumptions","source_or_new_status","nonclaims"])][:20])
        guards = self.rows("ledgers/anti_conflation_checklist.csv")
        guard_ids={x["guard_id"] for x in guards}
        self.add("Frozen anti-conflation checklist has 60 active unique guards", len(guards) == 60 and len(guard_ids) == 60 and all(x["status"] == "active" for x in guards), {"rows":len(guards),"active":sum(x['status']=='active' for x in guards)})
        grows=self.rows("ledgers/candidate_anti_conflation_audit.csv")
        self.add("Candidate guard audit has 600 rows", len(grows) == 600, len(grows))
        gkeys={(x["candidate_id"],x["guard_id"]) for x in grows}
        self.add("Every candidate audits every guard exactly once", len(gkeys) == 600 and gkeys == set(itertools.product(candidate_ids,guard_ids)), len(gkeys))
        self.add("All guard audits pass without blank evidence/boundary", all(x["status"] == "passed" and x["audit_response"].strip() and x["evidence_paths"].strip() and x["unresolved_boundary"].strip() for x in grows), [(x["candidate_id"],x["guard_id"],x["status"]) for x in grows if x["status"] != "passed" or not x["audit_response"].strip() or not x["evidence_paths"].strip() or not x["unresolved_boundary"].strip()][:20])

        # 10. Assumption, asset, primitive, and discriminator pricing.
        assumptions = self.rows("ledgers/assumption_register.csv")
        assumption_ids={x["assumption_id"] for x in assumptions}
        self.add("Inherited assumption register retains 20 assumptions", len(assumptions) == 20 and len(assumption_ids) == 20, len(assumptions))
        am=self.rows("ledgers/candidate_assumption_matrix.csv")
        self.add("Assumption matrix has 200 rows", len(am) == 200, len(am))
        self.add("Every candidate prices every assumption", {(x["candidate_id"],x["assumption_id"]) for x in am} == set(itertools.product(candidate_ids,assumption_ids)), len(am))
        ont_ids={"A1","A2-P","H-CERT-SOUND","H-IDENTITY-O"}
        ont_bad=[(x["candidate_id"],x["assumption_id"],x["status"]) for x in am if x["assumption_id"] in ont_ids and x["status"] not in {"not_used","explicitly_not_spent_structurally","optional_later_interpretation_only","optional_semantic_boundary"}]
        self.add("A1, A2-P, certificate soundness, and identity interpretation are not spent structurally", not ont_bad, ont_bad or "all separated")
        crosswalk=self.rows("ledgers/candidate_asset_crosswalk.csv")
        self.add("Candidate asset crosswalk has 69 resolving links", len(crosswalk) == 69 and all(x["candidate_id"] in candidate_ids and x["asset_id"] in valid_asset_ids for x in crosswalk), {"rows":len(crosswalk),"bad":[(x['candidate_id'],x['asset_id']) for x in crosswalk if x['candidate_id'] not in candidate_ids or x['asset_id'] not in valid_asset_ids]})
        self.add("Every asset import records heterogeneous retyping debt and independence boundary", all(x["heterogeneous_retyping_obligation"].strip() and x["independence_boundary"].strip() for x in crosswalk), [(x["candidate_id"],x["asset_id"]) for x in crosswalk if not x["heterogeneous_retyping_obligation"].strip() or not x["independence_boundary"].strip()])
        primitives=self.rows("ledgers/new_primitive_register.csv")
        self.add("New-primitive register contains 60 unique candidate-scoped primitives", len(primitives) == 60 and len({x["primitive_id"] for x in primitives}) == 60 and Counter(x["candidate_id"] for x in primitives) == Counter({cid:6 for cid in candidate_ids}), {"rows":len(primitives),"per_candidate":Counter(x['candidate_id'] for x in primitives)})
        self.add("All new primitives are explicitly exploratory and heterogeneously new/retyped", all(x["source_or_new_status"] == "genuinely_new_or_heterogeneous_retyping" and x["definition_status"] == "exploratory_not_formalized" for x in primitives), Counter((x["source_or_new_status"],x["definition_status"]) for x in primitives))
        circular_terms=["identity", "survival", "consciousness", "transfer success", "transcendence"]
        self.add("Every new primitive carries the non-circularity audit", all(all(t in x["circularity_audit"].lower() for t in circular_terms) for x in primitives), [x["primitive_id"] for x in primitives if not all(t in x["circularity_audit"].lower() for t in circular_terms)])
        self.add("Every new primitive records fixed-support debt, discriminators, and nonclaims", all(x["fixed_support_debt"].strip() and x["scenario_discriminators"].strip() and x["nonclaims"].strip() for x in primitives), [x["primitive_id"] for x in primitives if not x["fixed_support_debt"].strip() or not x["scenario_discriminators"].strip() or not x["nonclaims"].strip()])
        dcross=self.rows("ledgers/candidate_discriminator_crosswalk.csv")
        discriminator_ids={f"D{i:02d}" for i in range(1,11)}
        self.add("Discriminator crosswalk has 100 rows", len(dcross) == 100, len(dcross))
        self.add("Every candidate addresses all ten discriminators", {(x["candidate_id"],x["discriminator_id"]) for x in dcross} == set(itertools.product(candidate_ids,discriminator_ids)), len(dcross))
        self.add("Every discriminator response has at least one nontrivial scenario", all(self.split_ids(x["nontrivial_scenario_ids"]) for x in dcross), [(x["candidate_id"],x["discriminator_id"]) for x in dcross if not self.split_ids(x["nontrivial_scenario_ids"])])

        # 11. Governance, phase boundary, and repository hygiene.
        decisions=self.rows("ledgers/decision_log.csv")
        d03=[x for x in decisions if x["id"].startswith("D03-")]
        self.add("Decision ledger contains exactly 16 active CST-EXP-03 rulings", len(d03) == 16 and all(x["status"] == "active" for x in d03), len(d03))
        rejected=(r / "ledgers/REJECTED_DEFAULTS.md").read_text(encoding="utf-8")
        self.add("Rejected-default ledger contains all 15 phase-03 entries", all(x[0] in rejected for x in D.PHASE_REJECTED_DEFAULTS), [x[0] for x in D.PHASE_REJECTED_DEFAULTS if x[0] not in rejected])
        unresolved=(r / "ledgers/UNRESOLVED_QUESTIONS.md").read_text(encoding="utf-8")
        self.add("Unresolved-question ledger contains all 18 phase-03 questions", all(q in unresolved for q in D.PHASE_UNRESOLVED), [q for q in D.PHASE_UNRESOLVED if q not in unresolved])
        summary=self.json("manifests/EXP03_ASSET_SUMMARY.json")
        expected_counts={
            "candidate_schemas":10,"transported_objects":15,"invariants":12,"bridge_morphologies":12,"independent_brainstorms":7,
            "candidate_scenario_rows":350,"typed_scenario_lane_cells":1750,"candidate_question_rows":1000,"candidate_guard_rows":600,
            "new_primitives":60,"candidate_assumption_rows":200,"candidate_asset_links":69,"candidate_discriminator_rows":100,
            "pairwise_divergence_rows":45,"candidate_cards":10,"phase_03_decisions":16,"phase_03_rejected_defaults":15,"phase_03_unresolved_questions":18,
        }
        self.add("EXP03 asset summary reports exact generated counts", summary.get("counts") == expected_counts, summary.get("counts"))
        self.add("EXP03 asset summary records nonselection and no implementation", summary.get("target_selected") is False and summary.get("ranking_performed") is False and summary.get("theorem_or_program_implemented") is False, summary)
        status_blob="\n".join((r/x).read_text(encoding="utf-8") for x in ["README.md","STATE.md","STATUS.md","changelog/CST-EXP-03.md","synthesis/CST-EXP-03_CANDIDATE_GENERATION_SYNTHESIS.md"]).lower()
        self.add("Repository status identifies CST-EXP-03 complete and CST-EXP-04 next", "cst-exp-03" in status_blob and "cst-exp-04" in status_blob, "status documents")
        self.add("Status documents explicitly deny ranking, target selection, theorem proof, and ontology", all(t in status_blob for t in ["no candidate ranking","no theorem","consciousness","personal-identity","no candidate selected"]), [t for t in ["no candidate ranking","no theorem","consciousness","personal-identity","no candidate selected"] if t not in status_blob])
        future_files=[]
        for dirname in ["challenges","feasibility"]:
            d=r/dirname
            if d.exists():
                future_files += [str(p.relative_to(r)) for p in d.rglob("*") if p.is_file() and p.name != ".gitkeep"]
        self.add("CST-EXP-04/05 work directories remain unpopulated", not future_files, future_files or "empty")
        phase_impl=[str(p.relative_to(r)) for p in (r/"candidates").rglob("*") if p.is_file() and p.suffix.lower() in {".lean",".ipynb",".py",".cpp",".rs",".jl"}]
        self.add("Candidate assets contain no theorem or toy implementation source", not phase_impl, phase_impl or "none")
        pycache=[str(p.relative_to(r)) for p in r.rglob("__pycache__") if ".git" not in p.parts]
        pyc=[str(p.relative_to(r)) for p in r.rglob("*.pyc") if ".git" not in p.parts]
        self.add("Repository contains no Python cache artifacts", not pycache and not pyc, {"dirs":pycache,"pyc":pyc})
        symlinks=[str(p.relative_to(r)) for p in r.rglob("*") if p.is_symlink() and ".git" not in p.parts]
        self.add("Repository contains no symlinks", not symlinks, symlinks or "none")
        utf_bad=[]
        for p in r.rglob("*"):
            if not p.is_file() or ".git" in p.parts or p.suffix.lower() in {".zip",".png",".pdf"}:
                continue
            try: p.read_text(encoding="utf-8")
            except Exception as exc: utf_bad.append(f"{p.relative_to(r)}:{exc}")
        self.add("All nonbinary repository files decode as UTF-8", not utf_bad, utf_bad[:20] or "all")

        # Markdown relative-link check for current-phase surfaces.
        md_files=[r/"README.md",r/"STATUS.md",r/"STATE.md"] + list((r/"candidates").rglob("*.md")) + [r/"synthesis/CST-EXP-03_CANDIDATE_GENERATION_SYNTHESIS.md"]
        broken=[]
        pat=re.compile(r"(?<!!)\[[^\]]*\]\(([^)]+)\)")
        for p in md_files:
            if not p.is_file(): continue
            for raw in pat.findall(p.read_text(encoding="utf-8")):
                target=raw.strip().split()[0].strip("<>")
                if not target or target.startswith(("#","http://","https://","mailto:")):
                    continue
                target=unquote(target.split("#",1)[0])
                if not (p.parent/target).resolve().exists():
                    broken.append(f"{p.relative_to(r)} -> {raw}")
        self.add("Current-phase Markdown relative links resolve", not broken, broken[:30] or len(md_files))

        # 12. Manifest/hash integrity when frozen.
        if not self.skip_manifest:
            phase_summary=self.json("manifests/PHASE_SUMMARY.json")
            self.add("Frozen phase summary marks CST-EXP-03 complete", phase_summary.get("phase") == D.PHASE and phase_summary.get("status") == "complete" and phase_summary.get("exit_gate") == "pass", {k:phase_summary.get(k) for k in ["phase","status","exit_gate"]})
            self.add("Frozen phase summary preserves nonselection flags", phase_summary.get("target_selected") is False and phase_summary.get("ranking_performed") is False and phase_summary.get("theorem_or_program_implemented") is False, "all false")
            manifest=self.json("manifests/MANIFEST.json")
            entries=manifest.get("files",[])
            bad=[]
            for e in entries:
                p=r/e["path"]
                if not p.is_file() or p.stat().st_size != e["bytes"] or self.sha(p) != e["sha256"]:
                    bad.append(e["path"])
            self.add("Manifest file entries resolve with exact size and SHA-256", bool(entries) and not bad, {"entries":len(entries),"bad":bad[:20]})
            sum_rows={}
            for line in (r/"manifests/SHA256SUMS").read_text(encoding="utf-8").splitlines():
                m=re.match(r"^([0-9a-f]{64})\s+\*?(.+)$",line.strip())
                if m: sum_rows[m.group(2)] = m.group(1)
            sum_bad=[rel for rel,h in sum_rows.items() if not (r/rel).is_file() or self.sha(r/rel) != h]
            self.add("SHA256SUMS verifies all listed content surfaces", bool(sum_rows) and not sum_bad, {"rows":len(sum_rows),"bad":sum_bad[:20]})
            completion=(r/"manifests/CST-EXP-03_COMPLETION_REPORT.md").read_text(encoding="utf-8").lower()
            self.add("Completion report states exit pass and exploration-only boundary", "exit gate passes" in completion and "no candidate" in completion and "no theorem" in completion, "completion report")
            rebuild=self.json("manifests/REBUILD_VERIFICATION.json")
            self.add("Portable rebuild record is a pass", rebuild.get("status") == "pass", rebuild)

    def write_reports(self) -> int:
        passed=sum(x.passed for x in self.results)
        failed=len(self.results)-passed
        status="pass" if failed == 0 else "fail"
        report=[
            "# CST-EXP-03 Validation Report", "",
            f"**Status:** {status.upper()}  ",
            f"**Checks passed:** {passed}/{len(self.results)}  ",
            "**Scope:** candidate-generation completeness, cross-carrier typing, provenance, scenario coverage, anti-conflation discipline, nonselection, and repository integrity. This is not a proof of any candidate criterion or ontological claim.", "",
            "| # | Check | Result | Evidence |", "|---:|---|---|---|",
        ]
        for i,x in enumerate(self.results,1):
            ev=x.evidence.replace("|","\\|")
            if len(ev)>420: ev=ev[:419]+"…"
            report.append(f"| {i} | {x.name} | {'PASS' if x.passed else 'FAIL'} | {ev} |")
        if failed:
            report += ["", "## Failed checks", ""] + [f"- **{x.name}:** {x.evidence}" for x in self.results if not x.passed]
        out={"project":"CST-EXP","phase":D.PHASE,"status":status,"checks_total":len(self.results),"checks_passed":passed,"checks_failed":failed,"results":[asdict(x) for x in self.results]}
        (self.root/"manifests/VALIDATION_REPORT.md").write_text("\n".join(report)+"\n",encoding="utf-8")
        (self.root/"manifests/VALIDATION_RESULTS.json").write_text(json.dumps(out,indent=2,ensure_ascii=False)+"\n",encoding="utf-8")
        print(f"CST-EXP-03 validation: {passed}/{len(self.results)} checks passed ({status.upper()})")
        if failed:
            for x in self.results:
                if not x.passed: print(f"FAIL: {x.name}: {x.evidence}")
        return 0 if failed == 0 else 1


def main() -> None:
    ap=argparse.ArgumentParser()
    ap.add_argument("--repo",default=".")
    ap.add_argument("--skip-manifest",action="store_true")
    args=ap.parse_args()
    v=Validator(Path(args.repo),skip_manifest=args.skip_manifest)
    v.run()
    raise SystemExit(v.write_reports())


if __name__ == "__main__":
    main()
