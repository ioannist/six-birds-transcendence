#!/usr/bin/env python3
"""Validate CST-EXP-05 theorem/toy reconnaissance assets."""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import sys
from collections import Counter
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import exp05_data as D  # noqa: E402


class Validator:
    def __init__(self, root: Path, skip_manifest: bool = False, write: bool = True):
        self.root = root.resolve()
        self.skip_manifest = skip_manifest
        self.write = write
        self.results: list[dict[str, Any]] = []

    def add(self, name: str, ok: bool, detail: Any = "") -> None:
        self.results.append({"name": name, "ok": bool(ok), "detail": detail})

    def text(self, rel: str) -> str:
        return (self.root / rel).read_text(encoding="utf-8")

    def rows(self, rel: str) -> list[dict[str, str]]:
        with (self.root / rel).open(newline="", encoding="utf-8") as fh:
            return list(csv.DictReader(fh))

    def j(self, rel: str) -> Any:
        return json.loads(self.text(rel))

    @staticmethod
    def sha(path: Path) -> str:
        h = hashlib.sha256()
        with path.open("rb") as fh:
            for chunk in iter(lambda: fh.read(1024 * 1024), b""):
                h.update(chunk)
        return h.hexdigest()

    @staticmethod
    def split_ids(s: str) -> list[str]:
        return [x.strip() for x in str(s).split(";") if x.strip()]

    def run(self) -> bool:
        r = self.root
        # 1. Base repository and inherited freeze.
        self.add("Repository has Git metadata", (r / ".git").is_dir(), ".git")
        self.add("Frozen CST-EXP-04 manifest exists", (r / "manifests/CST-EXP-04_MANIFEST.json").is_file(), "prior manifest")
        prior = self.j("manifests/CST-EXP-04_MANIFEST.json")
        self.add("Prior manifest is labeled CST-EXP-04", prior.get("phase") == "CST-EXP-04", prior.get("phase"))
        mutable = {
            "README.md", "STATE.md", "STATUS.md", "CHANGELOG.md",
            "ledgers/DECISION_LOG.md", "ledgers/REJECTED_DEFAULTS.md", "ledgers/UNRESOLVED_QUESTIONS.md", "ledgers/decision_log.csv",
            "manifests/MANIFEST.json", "manifests/SHA256SUMS", "manifests/REPO_TREE.txt", "manifests/VALIDATION_REPORT.md",
            "manifests/VALIDATION_RESULTS.json", "manifests/PHASE_SUMMARY.json", "manifests/RESTORE_AND_VERIFY.md",
            "manifests/CST-EXP-04_COMPLETION_REPORT.md",
        }
        frozen_bad = []
        frozen_checked = 0
        for e in prior.get("files", []):
            rel = e["path"]
            if rel in mutable or rel.startswith("scripts/") or rel.startswith("manifests/"):
                continue
            p = r / rel
            frozen_checked += 1
            if not p.is_file() or p.stat().st_size != e["bytes"] or self.sha(p) != e["sha256"]:
                frozen_bad.append(rel)
        self.add("Inherited CST-EXP-04 scientific surfaces remain byte-frozen", not frozen_bad and frozen_checked >= 350, {"checked": frozen_checked, "bad": frozen_bad[:20]})

        # ID banks.
        family_rows = self.rows("ledgers/family_feasibility_registry.csv")
        model_rows = self.rows("ledgers/model_registry.csv")
        discr = self.rows("ledgers/model_candidate_discrimination.csv")
        program_rows = self.rows("ledgers/toy_program_registry.csv")
        theorem_rows = self.rows("ledgers/theorem_dependency_and_risk.csv")
        surfaces = self.rows("ledgers/formalization_surface.csv")
        ladders = self.rows("ledgers/family_assumption_ladder.csv")
        bundles = self.rows("ledgers/landing_bundle_registry.csv")
        crosswalk = self.rows("ledgers/model_theorem_program_crosswalk.csv")
        ng_map = self.rows("ledgers/no_go_refinement_map.csv")
        family_ids = {x["family_id"] for x in family_rows}
        model_ids = {x["id"] for x in model_rows}
        program_ids = {x["id"] for x in program_rows}
        theorem_ids = {x["id"] for x in theorem_rows}
        asset_ids = {x["asset_id"] for x in self.rows("ledgers/asset_provenance.csv")}
        assumption_ids = {x["assumption_id"] for x in self.rows("ledgers/assumption_register.csv")}
        prior_ng_ids = {x["id"] for x in self.rows("ledgers/no_go_register.csv")}

        # 2. Family feasibility.
        self.add("Exactly three survivor-family feasibility records", len(family_rows) == 3, len(family_rows))
        self.add("Family IDs are SF-01..SF-03", family_ids == {"SF-01", "SF-02", "SF-03"}, sorted(family_ids))
        self.add("All family exit gates are reconnaissance-admissible", all(x["exit_gate"].startswith("reconnaissance_admissible_") for x in family_rows), [x["exit_gate"] for x in family_rows])
        self.add("All family records remain unranked", all(x["unranked"] == "true" for x in family_rows), "all three")
        for f in family_rows:
            self.add(f"{f['family_id']} has positive models", bool(self.split_ids(f["positive_models"])), f["positive_models"])
            self.add(f"{f['family_id']} has negative models", bool(self.split_ids(f["negative_models"])), f["negative_models"])
            self.add(f"{f['family_id']} positive models resolve", set(self.split_ids(f["positive_models"])) <= model_ids, f["positive_models"])
            self.add(f"{f['family_id']} negative models resolve", set(self.split_ids(f["negative_models"])) <= model_ids, f["negative_models"])
            self.add(f"{f['family_id']} constructive theorem IDs resolve", set(self.split_ids(f["constructive_theorems"])) <= theorem_ids, f["constructive_theorems"])
            self.add(f"{f['family_id']} companion no-go IDs resolve", set(self.split_ids(f["companion_no_go"])) <= theorem_ids, f["companion_no_go"])
            self.add(f"{f['family_id']} toy program IDs resolve", set(self.split_ids(f["toy_programs"])) <= program_ids, f["toy_programs"])
            self.add(f"{f['family_id']} has an elementary path and kill condition", bool(f["elementary_path"] and f["kill_condition"]), "present")
            self.add(f"{f['family_id']} has an ontological nonclaim", any(k in f["nonclaim"].lower() for k in ["consciousness", "identity", "survival"]), f["nonclaim"])

        # 3. Model suite.
        self.add("Exactly ten finite model records", len(model_rows) == 10, len(model_rows))
        self.add("Model IDs are MF-01..MF-10", model_ids == {f"MF-{i:02d}" for i in range(1, 11)}, sorted(model_ids))
        self.add("Every governing-plan model slot is unique", len({x["plan_slot"] for x in model_rows}) == 10, [x["plan_slot"] for x in model_rows])
        required_model_fields = ["purpose", "carriers", "states", "inputs", "transition", "interfaces", "bridge", "positive_witness", "negative_control", "expected_witnesses", "controls", "separates", "minimality", "formalization", "kill_condition", "nonclaim"]
        for m in model_rows:
            mid = m["id"]
            self.add(f"{mid} has every required model field", all(m.get(k, "").strip() for k in required_model_fields), [k for k in required_model_fields if not m.get(k, "").strip()])
            self.add(f"{mid} is exact finite and not implemented", m["exact_finite"] == "true" and m["implementation_status"] == "specified_not_implemented", {"finite": m["exact_finite"], "status": m["implementation_status"]})
            self.add(f"{mid} theorem references resolve", set(self.split_ids(m["theorem_ids"])) <= theorem_ids, m["theorem_ids"])
            self.add(f"{mid} program references resolve", set(self.split_ids(m["program_ids"])) <= program_ids, m["program_ids"])
            p = r / f"feasibility/model_cards/{mid}.md"
            self.add(f"{mid} card exists", p.is_file(), str(p.relative_to(r)))
            if p.is_file():
                t = p.read_text(encoding="utf-8").lower()
                heads = ["## exact finite signature", "## positive witness", "## exact negative or counterfeit control", "## kill condition", "## explicit nonclaim"]
                self.add(f"{mid} card has mandatory sections", all(h in t for h in heads), [h for h in heads if h not in t])
                self.add(f"{mid} card marks no implementation", "not implemented" in t, "boundary")
        self.add("Model suite index covers all ten IDs", all(mid in self.text("feasibility/MODEL_SUITE.md") for mid in model_ids), "all IDs")

        # 4. Model-family discrimination.
        expected_pairs = {(m, f) for m in model_ids for f in family_ids}
        actual_pairs = {(x["model_id"], x["family_id"]) for x in discr}
        self.add("Model-family discrimination has 30 records", len(discr) == 30, len(discr))
        self.add("Model-family discrimination covers full 10×3 key set", actual_pairs == expected_pairs, {"missing": sorted(expected_pairs - actual_pairs), "extra": sorted(actual_pairs - expected_pairs)})
        self.add("All discrimination records are exact and nonranking", all(x["exact_finite"] == "true" and x["not_a_ranking"] == "true" for x in discr), "all rows")
        self.add("Every family has at least one positive and one negative exit-gate model", all(any(x["family_id"] == f and x["positive_exit_gate_witness"] == "true" for x in discr) and any(x["family_id"] == f and x["negative_exit_gate_control"] == "true" for x in discr) for f in family_ids), "all families")
        self.add("All discrimination theorem/program IDs resolve", all(set(self.split_ids(x["theorem_ids"])) <= theorem_ids and set(self.split_ids(x["program_ids"])) <= program_ids for x in discr), "all rows")

        # 5. Theorem prospectus.
        self.add("Exactly twenty-four theorem prospectuses", len(theorem_rows) == 24, len(theorem_rows))
        self.add("Theorem IDs are TH-01..TH-24", theorem_ids == {f"TH-{i:02d}" for i in range(1, 25)}, sorted(theorem_ids))
        kinds = Counter(x["kind"].split("_", 1)[0] for x in theorem_rows)
        constructive_count = sum(x["kind"].startswith("constructive") for x in theorem_rows)
        no_go_count = len(theorem_rows) - constructive_count
        self.add("Theorem bank has 12 constructive/boundary prospects", constructive_count == 12, constructive_count)
        self.add("Theorem bank has 12 no-go/underdetermination prospects", no_go_count == 12, no_go_count)
        required_thm_fields = ["setup", "conjecture", "proof_spine", "finite_cases", "interactions", "objects", "lean_core", "python_role", "tractability", "quotient_risk", "category_need", "circularity_risk", "external_dependency", "falsifier", "nonclaim"]
        for trow in theorem_rows:
            tid = trow["id"]
            self.add(f"{tid} has every six-part/risk field", all(trow.get(k, "").strip() for k in required_thm_fields), [k for k in required_thm_fields if not trow.get(k, "").strip()])
            self.add(f"{tid} remains conjecture-grade and unranked", trow["status"] == "conjecture_grade_not_proved" and trow["not_a_ranking"] == "true", {"status": trow["status"], "rank": trow["not_a_ranking"]})
            self.add(f"{tid} family references resolve", set(self.split_ids(trow["families"])) <= family_ids, trow["families"])
            self.add(f"{tid} model references resolve", set(self.split_ids(trow["models"])) <= model_ids, trow["models"])
            self.add(f"{tid} program references resolve", set(self.split_ids(trow["programs"])) <= program_ids, trow["programs"])
            self.add(f"{tid} asset references resolve", set(self.split_ids(trow["source_assets"])) <= asset_ids, trow["source_assets"])
            self.add(f"{tid} assumptions resolve", set(self.split_ids(trow["assumptions"])) <= assumption_ids, trow["assumptions"])
            self.add(f"{tid} prior no-go references resolve", set(self.split_ids(trow["refines_no_go"])) <= prior_ng_ids, trow["refines_no_go"])
            p = r / f"feasibility/theorem_prospectus/{tid}.md"
            self.add(f"{tid} card exists", p.is_file(), str(p.relative_to(r)))
            if p.is_file():
                txt = p.read_text(encoding="utf-8").lower()
                heads = ["## 1. setup", "## 2. conjecture", "## 3. proof spine", "## 4. exact finite cases", "## 5. interactions", "## 6. formalization reconnaissance", "## 7. explicit nonclaim"]
                self.add(f"{tid} card has all theorem sections", all(h in txt for h in heads), [h for h in heads if h not in txt])
                self.add(f"{tid} card explicitly denies proof status", "not proved" in txt, "status")
        self.add("Theorem index covers all 24 IDs", all(tid in self.text("feasibility/theorem_prospectus/INDEX.md") for tid in theorem_ids), "all IDs")

        # 6. Toy program contracts.
        self.add("Exactly ten toy-program contracts", len(program_rows) == 10, len(program_rows))
        self.add("Program IDs are TP-01..TP-10", program_ids == {f"TP-{i:02d}" for i in range(1, 11)}, sorted(program_ids))
        required_prog_fields = ["purpose", "input_types", "outputs", "witness_format", "controls", "complexity", "falsifies", "models", "theorems", "lean_role", "python_role", "nonclaim"]
        for pgr in program_rows:
            pid = pgr["id"]
            self.add(f"{pid} has every contract field", all(pgr.get(k, "").strip() for k in required_prog_fields), [k for k in required_prog_fields if not pgr.get(k, "").strip()])
            self.add(f"{pid} is contract-only", pgr["implementation_status"] == "contract_only_no_code", pgr["implementation_status"])
            self.add(f"{pid} model references resolve", set(self.split_ids(pgr["models"])) <= model_ids, pgr["models"])
            self.add(f"{pid} theorem references resolve", set(self.split_ids(pgr["theorems"])) <= theorem_ids, pgr["theorems"])
            p = r / f"feasibility/toy_program_prospectus/{pid}.md"
            self.add(f"{pid} card exists", p.is_file(), str(p.relative_to(r)))
            if p.is_file():
                txt = p.read_text(encoding="utf-8").lower()
                heads = ["## input types", "## exact outputs", "## witness and certificate format", "## expected complexity", "## lean/python division", "## explicit nonclaim"]
                self.add(f"{pid} card has all contract sections", all(h in txt for h in heads), [h for h in heads if h not in txt])
                self.add(f"{pid} card states no code", "no code written" in txt or "no code" in txt, "boundary")
        self.add("Program index covers all ten IDs", all(pid in self.text("feasibility/toy_program_prospectus/INDEX.md") for pid in program_ids), "all IDs")

        # 7. Formalization surfaces.
        self.add("Exactly 96 formalization surfaces", len(surfaces) == 96, len(surfaces))
        expected_surface = {(tid, kind) for tid in theorem_ids for kind in ["definition", "statement", "proof_spine", "finite_witness"]}
        actual_surface = {(x["theorem_id"], x["surface_kind"]) for x in surfaces}
        self.add("Formalization surface covers 24×4 exact key set", actual_surface == expected_surface, {"missing": sorted(expected_surface - actual_surface)[:10], "extra": sorted(actual_surface - expected_surface)[:10]})
        self.add("Every formal surface is planned only", all(x["implementation_status"] == "planned_only" for x in surfaces), "all rows")
        self.add("Every formal surface has an acceptance test", all(x["acceptance_test"].strip() for x in surfaces), "all rows")
        self.add("Every formal surface resolves theorem IDs", all(x["theorem_id"] in theorem_ids for x in surfaces), "all rows")

        # 8. Assumption ladders.
        self.add("Exactly 24 family-assumption ladder rows", len(ladders) == 24, len(ladders))
        self.add("Every family has rungs 1 through 8", all({int(x["rung"]) for x in ladders if x["family_id"] == fid} == set(range(1, 9)) for fid in family_ids), "all families")
        self.add("All ladder assumption IDs resolve", all(set(self.split_ids(x["assumption_ids"])) <= assumption_ids for x in ladders), "all rows")
        self.add("Ladder contains A1, A2-P, recognition, and identity boundaries", all(any(a in self.split_ids(x["assumption_ids"]) for x in ladders) for a in ["A1", "A2-P", "H-RECOG", "H-IDENTITY-O"]), "all protected assumptions")
        ladder_doc = self.text("feasibility/ASSUMPTION_LADDER.md").lower()
        self.add("Assumption ladder denies higher-rung structural rescue", "cannot rescue" in ladder_doc or "cannot repair" in ladder_doc, "boundary")
        self.add("Assumption ladder treats A2-P as not a bridge theorem", "a2-p does not prove bridge existence" in ladder_doc or "a2-p does not create predictive transport" in ladder_doc, "A2 boundary")

        # 9. Landing bundles.
        bundle_ids = {x["id"] for x in bundles}
        self.add("Exactly four landing bundles", len(bundles) == 4, len(bundles))
        self.add("Landing bundle IDs are LB-01, LB-02, LB-03, LB-NG", bundle_ids == {"LB-01", "LB-02", "LB-03", "LB-NG"}, sorted(bundle_ids))
        self.add("All landing bundles remain unranked", all(x["unranked"] == "true" for x in bundles), "all rows")
        self.add("Exactly one common no-go bundle", sum(x["family"] == "COMMON" for x in bundles) == 1, [x["id"] for x in bundles if x["family"] == "COMMON"])
        for b in bundles:
            self.add(f"{b['id']} theorem IDs resolve", set(self.split_ids(b["positive_core"] + ";" + b["negative_core"])) <= theorem_ids, b["positive_core"] + ";" + b["negative_core"])
            self.add(f"{b['id']} model IDs resolve", set(self.split_ids(b["models"])) <= model_ids, b["models"])
            self.add(f"{b['id']} program IDs resolve", set(self.split_ids(b["programs"])) <= program_ids, b["programs"])
            self.add(f"{b['id']} has risk and kill condition", bool(b["risk"] and b["kill"]), "present")
        bundles_doc = self.text("feasibility/LANDING_BUNDLES.md").lower()
        self.add("Landing-bundle document explicitly denies target selection", "not a primary/fallback target choice" in bundles_doc and "remain unranked" in bundles_doc, "boundary")

        # 10. Crosswalks/refinements.
        self.add("Model-theorem-program crosswalk has at least 100 rows", len(crosswalk) >= 100, len(crosswalk))
        self.add("All model-theorem-program crosswalk IDs resolve", all(x["model_id"] in model_ids and x["theorem_id"] in theorem_ids and x["program_id"] in program_ids for x in crosswalk), "all rows")
        self.add("No-go refinement map has at least 20 rows", len(ng_map) >= 20, len(ng_map))
        self.add("All no-go refinement references resolve", all(x["theorem_id"] in theorem_ids and x["prior_no_go_id"] in prior_ng_ids for x in ng_map), "all rows")
        self.add("Every no-go refinement remains unproved", all(x["status"] == "not_proved" for x in ng_map), "all rows")

        # 11. Core documents and scientific boundaries.
        required_docs = [
            "feasibility/README.md", "feasibility/FINITE_CORE_SEMANTICS.md", "feasibility/MODEL_SUITE.md",
            "feasibility/FORMALIZATION_TRACTABILITY.md", "feasibility/ASSUMPTION_LADDER.md",
            "feasibility/LANDING_BUNDLES.md", "feasibility/EXIT_GATE_AUDIT.md", "feasibility/RECONNAISSANCE_SYNTHESIS.md",
        ]
        for rel in required_docs:
            self.add(f"Required document exists: {rel}", (r / rel).is_file(), rel)
        finite = self.text("feasibility/FINITE_CORE_SEMANTICS.md").lower()
        for phrase in ["distinctcarrier", "no operational bridge edge is a lineage edge", "withdraw", "exact rational vector", "does not by itself support ontology"]:
            self.add(f"Finite semantics contains boundary: {phrase}", phrase in finite, phrase)
        tract = self.text("feasibility/FORMALIZATION_TRACTABILITY.md").lower()
        for phrase in ["category-theoretic language", "canonical finite partitions", "python", "lean", "definition-smuggling audit"]:
            self.add(f"Tractability document contains: {phrase}", phrase in tract, phrase)
        synth = self.text("feasibility/RECONNAISSANCE_SYNTHESIS.md").lower()
        for phrase in ["no credible first theorem", "three unranked constructive bundles", "shared no-go kernel", "no code was written", "a2-p is not a bridge theorem", "pass"]:
            self.add(f"Synthesis contains: {phrase}", phrase in synth, phrase)
        exit_doc = self.text("feasibility/EXIT_GATE_AUDIT.md").lower()
        for fid in family_ids:
            self.add(f"Exit-gate audit names {fid}", fid.lower() in exit_doc, fid)
        self.add("Exit gate explicitly keeps families unranked", "no family is selected, merged, or ranked" in exit_doc, "boundary")

        # 12. Governance and root state.
        dlog = self.rows("ledgers/decision_log.csv")
        self.add("Decision log contains exactly eight active D05 rulings", sum(x["id"].startswith("D05-") and x["status"] == "active" for x in dlog) == 8, [x["id"] for x in dlog if x["id"].startswith("D05-")])
        self.add("Rejected-defaults log contains twelve RD05 entries", len(re.findall(r"\| RD05-\d+", self.text("ledgers/REJECTED_DEFAULTS.md"))) == 12, "12")
        self.add("Unresolved-question log contains CST-EXP-05 section", "Feasibility questions added after CST-EXP-05" in self.text("ledgers/UNRESOLVED_QUESTIONS.md"), "section")
        state = self.text("STATE.md")
        status = self.text("STATUS.md")
        self.add("STATE advances to CST-EXP-05-v1 and names CST-EXP-06", "CST-EXP-05-v1" in state and "CST-EXP-06" in state, "state")
        self.add("STATUS records no implementation authorization", "Implementation authorization:** none" in status, "status")
        self.add("README marks CST-EXP-05 complete", "**Current completed phase:** `CST-EXP-05`" in self.text("README.md"), "README")

        # 13. No implementation/overclaim and links.
        new_impl = []
        for p in (r / "feasibility").rglob("*"):
            if p.is_file() and p.suffix in {".py", ".lean", ".ipynb", ".exe", ".so"}:
                new_impl.append(str(p.relative_to(r)))
        self.add("Feasibility bank contains no proof or program implementation", not new_impl, new_impl or "none")
        prohibited = []
        core_paths = list((r / "feasibility").rglob("*.md")) + [r / "STATE.md", r / "STATUS.md"]
        patterns = [
            r"we proved consciousness", r"consciousness moved", r"the same subject moved", r"personal identity is established",
            r"a2(?:-p)? is proved", r"numerical identity is proved", r"this theorem is proved(?! not)",
        ]
        for p in core_paths:
            txt = p.read_text(encoding="utf-8").lower()
            for pat in patterns:
                if re.search(pat, txt):
                    prohibited.append((str(p.relative_to(r)), pat))
        self.add("New phase surfaces contain no prohibited ontological/proof overclaim", not prohibited, prohibited or "none")
        broken = []
        link_re = re.compile(r"\[[^\]]+\]\(([^)]+)\)")
        for p in (r / "feasibility").rglob("*.md"):
            for target in link_re.findall(p.read_text(encoding="utf-8")):
                if target.startswith(("http://", "https://", "#", "mailto:")):
                    continue
                target = target.split("#", 1)[0]
                if target and not (p.parent / target).resolve().exists():
                    broken.append(f"{p.relative_to(r)} -> {target}")
        self.add("All local Markdown links in feasibility bank resolve", not broken, broken[:20] or "all resolve")
        self.add("Landing architecture DOT and SVG exist", (r / "feasibility/landing_architecture.dot").is_file() and (r / "feasibility/landing_architecture.svg").is_file(), "diagram")

        # 14. Summary.
        summ = self.j("manifests/EXP05_ASSET_SUMMARY.json")
        expected = {
            "survivor_families": 3, "finite_model_families": 10, "model_family_discrimination_records": 30,
            "theorem_prospectuses": 24, "constructive_or_boundary_prospects": 12,
            "no_go_or_underdetermination_prospects": 12, "toy_program_contracts": 10,
            "formalization_surfaces": 96, "family_assumption_ladder_records": 24, "landing_bundles": 4,
            "model_theorem_program_crosswalk_rows": len(crosswalk), "no_go_refinement_rows": len(ng_map),
        }
        self.add("EXP05 summary is labeled CST-EXP-05", summ.get("phase") == "CST-EXP-05", summ.get("phase"))
        for k, v in expected.items():
            self.add(f"EXP05 summary count matches {k}", summ["counts"].get(k) == v, summ["counts"].get(k))
        self.add("EXP05 summary boundary denies proof/code/selection/ontology", all(x in summ["boundary"].lower() for x in ["no theorem", "no toy program", "no final target", "consciousness", "a2"]), summ["boundary"])

        # 15. Manifest and checksums.
        if not self.skip_manifest:
            man = self.j("manifests/MANIFEST.json")
            self.add("Manifest is labeled CST-EXP-05", man.get("phase") == "CST-EXP-05", man.get("phase"))
            entries = {x["path"]: x for x in man.get("files", [])}
            bad = []
            for rel, e in entries.items():
                p = r / rel
                if not p.is_file() or p.stat().st_size != e["bytes"] or self.sha(p) != e["sha256"]:
                    bad.append(rel)
            self.add("Every manifest file exists with matching size and SHA-256", not bad, {"entries": len(entries), "bad": bad[:20]})
            excluded = set(man.get("excluded", []))
            required_excluded = {"manifests/MANIFEST.json", "manifests/SHA256SUMS", "manifests/REPO_TREE.txt", "manifests/VALIDATION_REPORT.md", "manifests/VALIDATION_RESULTS.json"}
            self.add("Dynamic validation/manifest surfaces are excluded", required_excluded <= excluded, sorted(excluded))
            sums = {}
            for line in self.text("manifests/SHA256SUMS").splitlines():
                m = re.match(r"^([0-9a-f]{64})\s+\*?(.+)$", line.strip())
                if m:
                    sums[m.group(2)] = m.group(1)
            sum_bad = [rel for rel, h in sums.items() if not (r / rel).is_file() or self.sha(r / rel) != h]
            self.add("SHA256SUMS verifies all listed files", not sum_bad, {"rows": len(sums), "bad": sum_bad[:20]})

        ok = all(x["ok"] for x in self.results)
        if self.write:
            self.write_report(ok)
        return ok

    def write_report(self, ok: bool) -> None:
        passed = sum(x["ok"] for x in self.results)
        total = len(self.results)
        lines = [
            "# CST-EXP-05 Validation Report", "",
            f"**Result:** {'PASS' if ok else 'FAIL'} — {passed}/{total} checks passed", "",
            "| # | Check | Result | Detail |", "|---:|---|---|---|",
        ]
        for i, x in enumerate(self.results, 1):
            detail = json.dumps(x["detail"], ensure_ascii=False, sort_keys=True) if not isinstance(x["detail"], str) else x["detail"]
            detail = detail.replace("|", "\\|").replace("\n", " ")
            lines.append(f"| {i} | {x['name'].replace('|', '\\|')} | {'PASS' if x['ok'] else 'FAIL'} | {detail} |")
        (self.root / "manifests/VALIDATION_REPORT.md").write_text("\n".join(lines) + "\n", encoding="utf-8")
        payload = {"phase": D.PHASE, "date": D.DATE, "passed": passed, "total": total, "result": "PASS" if ok else "FAIL", "checks": self.results}
        (self.root / "manifests/VALIDATION_RESULTS.json").write_text(json.dumps(payload, indent=2, ensure_ascii=False, sort_keys=True) + "\n", encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--skip-manifest", action="store_true")
    ap.add_argument("--no-write", action="store_true")
    args = ap.parse_args()
    v = Validator(args.root, skip_manifest=args.skip_manifest, write=not args.no_write)
    ok = v.run()
    passed = sum(x["ok"] for x in v.results)
    print(f"{'PASS' if ok else 'FAIL'} {passed}/{len(v.results)}")
    if not ok:
        for x in v.results:
            if not x["ok"]:
                print("FAIL:", x["name"], "::", x["detail"])
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
