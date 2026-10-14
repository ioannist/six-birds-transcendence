#!/usr/bin/env python3
"""Validate the CST-EXP-06 synthesis and target-freeze repository.

This validator checks the frozen decision surfaces, their provenance and internal
consistency, preservation of inherited CST-EXP-05 scientific assets, the absence
of theorem/toy implementation, and (after finalization) the static manifest and
portable-rebuild record.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import re
import subprocess
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

sys.path.insert(0, str(Path(__file__).resolve().parent))
import exp06_data as D  # noqa: E402


class Validator:
    def __init__(self, root: Path, *, skip_manifest: bool = False, write: bool = True):
        self.root = root.resolve()
        self.skip_manifest = skip_manifest
        self.write_outputs = write
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
            for block in iter(lambda: fh.read(1024 * 1024), b""):
                h.update(block)
        return h.hexdigest()

    @staticmethod
    def split_ids(value: str) -> list[str]:
        return [x.strip() for x in re.split(r"[;,×]", str(value)) if x.strip()]

    def git_output(self, *args: str) -> tuple[int, str, str]:
        p = subprocess.run(
            ["git", "-C", str(self.root), *args], capture_output=True, text=True
        )
        return p.returncode, p.stdout.strip(), p.stderr.strip()

    def run(self) -> bool:
        r = self.root

        # ------------------------------------------------------------------
        # 1. Repository continuity and inherited freeze.
        # ------------------------------------------------------------------
        self.add("Repository has Git metadata", (r / ".git").is_dir(), ".git")
        pin_path = r / "manifests/CST-EXP-05_MANIFEST.json"
        self.add("Frozen CST-EXP-05 manifest pin exists", pin_path.is_file(), "manifests/CST-EXP-05_MANIFEST.json")
        prior = self.j("manifests/CST-EXP-05_MANIFEST.json") if pin_path.is_file() else {}
        self.add("Prior manifest is labeled CST-EXP-05", prior.get("phase") == "CST-EXP-05", prior.get("phase"))
        self.add("Prior manifest has a substantial file bank", prior.get("file_count", 0) >= 450, prior.get("file_count"))

        mutable = {
            "README.md", "STATE.md", "STATUS.md", "CHANGELOG.md",
            "ledgers/DECISION_LOG.md", "ledgers/REJECTED_DEFAULTS.md",
            "ledgers/UNRESOLVED_QUESTIONS.md", "ledgers/decision_log.csv",
        }
        frozen_bad: list[str] = []
        frozen_checked = 0
        for entry in prior.get("files", []):
            rel = entry["path"]
            if rel in mutable or rel.startswith("scripts/") or rel.startswith("manifests/"):
                continue
            p = r / rel
            frozen_checked += 1
            if (
                not p.is_file()
                or p.stat().st_size != entry["bytes"]
                or self.sha(p) != entry["sha256"]
            ):
                frozen_bad.append(rel)
        self.add(
            "Inherited CST-EXP-05 scientific surfaces remain byte-frozen",
            not frozen_bad and frozen_checked >= 400,
            {"checked": frozen_checked, "bad": frozen_bad[:20]},
        )

        # Scope of phase modifications, where the base tag is available.
        rc, _, _ = self.git_output("rev-parse", "--verify", "CST-EXP-05-v1^{commit}")
        if rc == 0:
            _, changed, _ = self.git_output("diff", "--name-only", "CST-EXP-05-v1")
            _, untracked, _ = self.git_output("ls-files", "--others", "--exclude-standard")
            touched = {x for x in (changed + "\n" + untracked).splitlines() if x}
            allowed_exact = mutable | {
                "changelog/CST-EXP-06.md",
                "manifests/CST-EXP-05_MANIFEST.json",
                "manifests/EXP06_ASSET_SUMMARY.json",
                "manifests/MANIFEST.json",
                "manifests/PHASE_SUMMARY.json",
                "manifests/REBUILD_VERIFICATION.json",
                "manifests/REBUILD_VERIFICATION.md",
                "manifests/REPO_TREE.txt",
                "manifests/RESTORE_AND_VERIFY.md",
                "manifests/SHA256SUMS",
                "manifests/VALIDATION_REPORT.md",
                "manifests/VALIDATION_RESULTS.json",
                "manifests/CST-EXP-06_COMPLETION_REPORT.md",
                "manifests/CST-EXP-06_PREVALIDATION_REPORT.md",
                "manifests/CST-EXP-06_PREVALIDATION_RESULTS.json",
            }
            bad_scope = sorted(
                x for x in touched
                if x not in allowed_exact
                and not x.startswith("synthesis/")
                and x not in {
                    "scripts/exp06_data.py", "scripts/build_exp06_assets.py",
                    "scripts/validate_exp06.py", "scripts/rebuild_exp06.sh",
                    "scripts/verify_exp06_rebuild.py", "scripts/finalize_exp06_manifest.py",
                }
            )
            self.add("Phase modifications stay inside the declared CST-EXP-06 scope", not bad_scope, bad_scope)
            lean_changes = sorted(x for x in touched if x.endswith(".lean"))
            self.add("No Lean implementation was added or modified", not lean_changes, lean_changes)
        else:
            self.add("Portable copy uses manifest freeze when base Git tag is absent", True, "CST-EXP-05-v1 unavailable")
            self.add("No untracked Lean implementation exists", not list(r.rglob("*.lean.tmp")), "no temporary Lean outputs")

        # ------------------------------------------------------------------
        # 2. Required governing-plan outputs.
        # ------------------------------------------------------------------
        required = [
            "synthesis/FINALIST_COMPARISON.md",
            "synthesis/TARGET_SELECTION_SCORECARD.csv",
            "synthesis/PRIMARY_TARGET_SPECIFICATION.md",
            "synthesis/FALLBACK_TARGET_SPECIFICATION.md",
            "synthesis/COPY_VS_CONTINUATION_AUDIT.md",
            "synthesis/EXPLORATION_DOSSIER.md",
            "synthesis/LATER_LANDING_HANDOFF.md",
            "synthesis/TARGET_REGISTRY.json",
            "synthesis/TARGET_SCENARIO_VERDICTS.csv",
            "synthesis/FROZEN_THEOREM_FAMILY.csv",
            "synthesis/FROZEN_WITNESS_SUITE.csv",
            "synthesis/frozen_target_architecture.svg",
            "changelog/CST-EXP-06.md",
            "manifests/EXP06_ASSET_SUMMARY.json",
        ]
        for rel in required:
            p = r / rel
            self.add(f"Required phase output exists: {rel}", p.is_file() and p.stat().st_size > 20, p.stat().st_size if p.is_file() else "missing")

        plan = self.text("inputs/normative/PREPARATORY_EXPLORATION_PLAN.md")
        self.add("Normative plan contains CST-EXP-06 phase", "# Phase CST-EXP-06" in plan, "plan phase")
        for rel in required[:7]:
            self.add(f"Normative plan names required output {rel}", f"`{rel}`" in plan, rel)

        # ------------------------------------------------------------------
        # 3. Frozen target registry.
        # ------------------------------------------------------------------
        reg = self.j("synthesis/TARGET_REGISTRY.json")
        self.add("Target registry phase is CST-EXP-06", reg.get("phase") == D.PHASE, reg.get("phase"))
        self.add("Target registry generated date is frozen", reg.get("generated_date") == D.DATE, reg.get("generated_date"))
        self.add("Primary target ID is FT-01", reg.get("primary", {}).get("id") == D.PRIMARY_ID, reg.get("primary", {}).get("id"))
        self.add("Primary target code is FIACH", reg.get("primary", {}).get("code") == "FIACH", reg.get("primary", {}).get("code"))
        self.add("Fallback target ID is FT-02", reg.get("fallback", {}).get("id") == D.FALLBACK_ID, reg.get("fallback", {}).get("id"))
        self.add("Fallback target code is IAPS", reg.get("fallback", {}).get("code") == "IAPS", reg.get("fallback", {}).get("code"))
        self.add("Mandatory companion is FT-NG", reg.get("mandatory_companion", {}).get("id") == D.TERMINAL_ID, reg.get("mandatory_companion", {}).get("id"))
        for key in ("primary", "fallback"):
            obj = reg[key]
            self.add(f"{key} separately declares S-R, S-L, and A", obj.get("claim_lanes") == ["S-R", "S-L", "A"], obj.get("claim_lanes"))
            self.add(f"{key} has exactly two source survivor families", len(obj.get("source_families", [])) == 2, obj.get("source_families"))
            self.add(f"{key} has a nonempty mandatory component bank", len(obj.get("mandatory_components", [])) >= 7, obj.get("mandatory_components"))
            nonclaim = obj.get("core_nonclaim", "").lower()
            self.add(f"{key} registry states an ontological nonclaim", any(x in nonclaim for x in ("conscious", "identity", "survival")), nonclaim)
        self.add("Primary uses SF-01 plus SF-02", reg["primary"]["source_families"] == ["SF-01", "SF-02"], reg["primary"]["source_families"])
        self.add("Fallback uses SF-01 plus SF-03", reg["fallback"]["source_families"] == ["SF-01", "SF-03"], reg["fallback"]["source_families"])

        # ------------------------------------------------------------------
        # 4. Hard gates and weighted scorecard.
        # ------------------------------------------------------------------
        score = self.rows("synthesis/TARGET_SELECTION_SCORECARD.csv")
        finalist_by_id = {x["id"]: x for x in D.FINALISTS}
        finalist_ids = set(finalist_by_id)
        hard_ids = {x[0] for x in D.HARD_GATES}
        soft_by_id = {x[0]: x for x in D.SOFT_CRITERIA}
        self.add("Scorecard has 161 rows (7 × (10 hard + 12 soft + 1 summary))", len(score) == 161, len(score))
        self.add("Scorecard covers exactly seven finalist architectures", {x["candidate_id"] for x in score} == finalist_ids, sorted({x["candidate_id"] for x in score}))
        self.add("All scorecard candidate/criterion keys are unique", len(score) == len({(x["candidate_id"], x["record_type"], x["criterion_id"]) for x in score}), "unique")
        for cid, f in finalist_by_id.items():
            rows = [x for x in score if x["candidate_id"] == cid]
            hard = [x for x in rows if x["record_type"] == "hard_gate"]
            soft = [x for x in rows if x["record_type"] == "soft_criterion"]
            summary = [x for x in rows if x["record_type"] == "summary"]
            self.add(f"{cid} has ten hard-gate rows", len(hard) == 10 and {x["criterion_id"] for x in hard} == hard_ids, len(hard))
            self.add(f"{cid} hard-gate results match frozen data", all(x["gate_result"] == f["hard"][x["criterion_id"]] for x in hard), {x["criterion_id"]: x["gate_result"] for x in hard})
            self.add(f"{cid} has twelve soft rows", len(soft) == 12 and {x["criterion_id"] for x in soft} == set(soft_by_id), len(soft))
            weights = sum(int(x["weight"]) for x in soft)
            self.add(f"{cid} soft weights total 100", weights == 100, weights)
            range_ok = all(0 <= float(x["score_0_to_5"]) <= 5 for x in soft)
            self.add(f"{cid} soft scores stay within 0–5", range_ok, [x["score_0_to_5"] for x in soft])
            soft_key_ok = all(
                abs(float(x["score_0_to_5"]) - f["scores"][soft_by_id[x["criterion_id"]][1]]) < 1e-9
                for x in soft
            )
            self.add(f"{cid} soft scores match frozen decision data", soft_key_ok, "all 12")
            calc = round(sum(int(x["weight"]) * float(x["score_0_to_5"]) / 5 for x in soft), 1)
            points_ok = all(abs(float(x["weighted_points"]) - int(x["weight"]) * float(x["score_0_to_5"]) / 5) < 0.011 for x in soft)
            self.add(f"{cid} per-row weighted points recompute", points_ok, calc)
            self.add(f"{cid} has one summary row", len(summary) == 1, len(summary))
            if summary:
                s = summary[0]
                self.add(f"{cid} summary total recomputes", abs(float(s["weighted_points"]) - calc) < 0.011, {"file": s["weighted_points"], "calc": calc})
                expected_gate = "pass" if all(v == "pass" for v in f["hard"].values()) else "fail"
                self.add(f"{cid} summary gate is correct", s["gate_result"] == expected_gate, s["gate_result"])
                self.add(f"{cid} selection status matches registry data", s["selection_status"] == f["selection_status"], s["selection_status"])
                self.add(f"{cid} scorecard warns totals are not evidence", "not evidence" in s["rationale"].lower(), s["rationale"])
        summaries = {x["candidate_id"]: x for x in score if x["record_type"] == "summary"}
        self.add("Only FT-01 is marked primary", [k for k, v in summaries.items() if v["selection_status"] == "PRIMARY_FROZEN"] == ["FT-01"], "FT-01")
        self.add("Only FT-02 is marked fallback", [k for k, v in summaries.items() if v["selection_status"] == "FALLBACK_FROZEN"] == ["FT-02"], "FT-02")
        self.add("FT-01 and FT-02 pass every hard gate", all(summaries[x]["gate_result"] == "pass" for x in ("FT-01", "FT-02")), "both")
        self.add("Standalone families fail only project-completeness HG-10", all(finalist_by_id[x]["hard"]["HG-10"] == "fail" and all(finalist_by_id[x]["hard"][f"HG-{i:02d}"] == "pass" for i in range(1, 10)) for x in ("F-01", "F-02", "F-03")), "F-01..F-03")
        self.add("No-go kernel is retained despite failing positive-target HG-10", finalist_by_id["FT-NG"]["selection_status"].startswith("MANDATORY_COMPANION"), finalist_by_id["FT-NG"]["selection_status"])

        # ------------------------------------------------------------------
        # 5. Finalist comparison completeness.
        # ------------------------------------------------------------------
        comparison = self.text("synthesis/FINALIST_COMPARISON.md")
        self.add("Finalist comparison explicitly distinguishes comparison from ranking", "Compare rather than" in plan and "not evidence" in comparison.lower(), "rule")
        for f in D.FINALISTS:
            cid = f["id"]
            self.add(f"Finalist comparison contains profile {cid}", f"### {cid} —" in comparison, cid)
            for key, label in [
                ("strongest_case", "strongest case"),
                ("strongest_counterexample", "strongest counterexample"),
                ("unique_insight", "unique insight"),
                ("outperforming_scenario", "scenario advantage"),
                ("assumptions", "assumptions"),
                ("burden", "burden"),
                ("abandon", "abandonment trigger"),
            ]:
                snippet = f[key]
                self.add(f"{cid} comparison records {label}", snippet in comparison, snippet[:80])
        self.add("Comparison explains FIACH selection independently of decimal score", "choice is made by their substantive interpretation of copying" in comparison, "copy discriminator")
        self.add("Comparison explains IAPS fallback role", "source-derived destructive reconstruction" in comparison and "FT-02" in comparison, "fallback")
        self.add("Comparison defers dual-lineage unification", "FT-03" in comparison and "deferred" in comparison.lower(), "FT-03")
        self.add("Comparison makes no-go kernel mandatory", "no-go kernel is mandatory" in comparison.lower(), "FT-NG")

        # ------------------------------------------------------------------
        # 6. Primary and fallback target specifications.
        # ------------------------------------------------------------------
        primary = self.text("synthesis/PRIMARY_TARGET_SPECIFICATION.md")
        fallback = self.text("synthesis/FALLBACK_TARGET_SPECIFICATION.md")
        primary_heads = [
            "## 1. Motivation", "## 2. Typed finite data", "## 3. Independently defined predicates",
            "## 4. Frozen relation", "## 5. Core theorem family", "## 6. Exact finite witness suite",
            "## 7. Toy-program contracts", "## 8. Lean kernel targets", "## 9. Corpus dependency map",
            "## 10. Assumptions and claim tiers", "## 11. Copy and fission policy",
            "## 12. Kill and downgrade criteria", "## 13. Excluded claims",
        ]
        for h in primary_heads:
            self.add(f"Primary specification contains {h}", h in primary, h)
        fallback_heads = [
            "## 1. Motivation", "## 2. Typed finite data", "## 3. Frozen relation",
            "## 4. Core theorem family", "## 5. Exact finite witness suite",
            "## 6. Toy-program contracts", "## 7. Lean kernel targets",
            "## 8. Assumptions and claim tiers", "## 9. Copy, fission, fusion, and gap policy",
            "## 10. Kill and downgrade criteria", "## 11. Explicit nonclaims",
        ]
        for h in fallback_heads:
            self.add(f"Fallback specification contains {h}", h in fallback, h)
        for token in ["CarrierId", "DistinctCarrier(S,T)", "Stage := Fin", "LocalWitness", "LiveCorridor", "Autonomous", "FIACH_e(s,t)"]:
            self.add(f"Primary specification types {token}", token in primary, token)
        for token in ["Seed", "Gamma", "leastFixedPoint", "Anc", "IAPS_e(s,t)", "no-ex-nihilo"]:
            self.add(f"Fallback specification types {token}", token in fallback, token)
        self.add("Primary relation is explicitly relation-valued rather than identity", "binary relation, not a function and not an identity predicate" in primary, "relation boundary")
        self.add("Primary detached-copy boundary is explicit", "detached exact copy" in primary.lower() and "does not satisfy" in primary.lower(), "copy separation")
        self.add("Primary autonomy uses declared withdrawal", "withdrawal removes the source" in primary.lower(), "withdrawal")
        self.add("Primary requires target ownership", "owned by the target" in primary.lower() or "target-owned" in primary.lower(), "ownership")
        self.add("Fallback excludes independent twins through no-ex-nihilo reachability", "independent twin" in fallback.lower() and "no-ex-nihilo" in fallback.lower(), "twin exclusion")
        self.add("Fallback permits destructive structural successorship conditionally", "destructive reconstruction" in fallback.lower() and "structural successor" in fallback.lower(), "destructive fallback")
        self.add("Fallback does not claim unique identity", "does not select a unique" in fallback.lower() or "no unique" in fallback.lower(), "uniqueness boundary")
        for doc_name, doc in (("primary", primary), ("fallback", fallback)):
            lower = doc.lower()
            self.add(f"{doc_name} states no consciousness proof", ("does not establish" in lower or "no result" in lower) and "conscious" in lower, "nonclaim")
            self.add(f"{doc_name} states no numerical-identity proof", ("numerical identity" in lower or "numerical-identity" in lower or "same person" in lower), "nonclaim")
            self.add(f"{doc_name} keeps A2 outside", "a2" in lower, "assumption boundary")
            self.add(f"{doc_name} contains kill criteria", "kill and downgrade criteria" in lower and ("abandon" in lower or "downgrade" in lower), "falsifier")

        # ------------------------------------------------------------------
        # 7. Frozen theorem and witness banks.
        # ------------------------------------------------------------------
        theorem = self.rows("synthesis/FROZEN_THEOREM_FAMILY.csv")
        expected_theorem_ids = {x[0] for x in D.PRIMARY_THEOREMS + D.FALLBACK_THEOREMS}
        self.add("Frozen theorem family has twenty entries", len(theorem) == 20, len(theorem))
        self.add("Frozen theorem IDs are complete and unique", {x["theorem_id"] for x in theorem} == expected_theorem_ids and len(theorem) == len({x["theorem_id"] for x in theorem}), sorted({x["theorem_id"] for x in theorem}))
        self.add("Primary theorem bank has twelve entries", sum(x["target_id"] == "FT-01" for x in theorem) == 12, Counter(x["target_id"] for x in theorem))
        self.add("Fallback theorem bank has eight entries", sum(x["target_id"] == "FT-02" for x in theorem) == 8, Counter(x["target_id"] for x in theorem))
        self.add("All theorem entries remain conjecture-grade and unproved", all(x["status"] == "conjecture_grade_not_proved" for x in theorem), Counter(x["status"] for x in theorem))
        self.add("Theorem bank contains constructive and no-go/boundary results", any(x["kind"].startswith("constructive") for x in theorem) and any("no_go" in x["kind"] for x in theorem), Counter(x["kind"] for x in theorem))
        prior_theorem_ids = {x["id"] for x in self.rows("ledgers/theorem_dependency_and_risk.csv")}
        for row in theorem:
            self.add(f"{row['theorem_id']} has a nonempty exact conjecture shape", len(row["frozen_conjecture_shape"].strip()) >= 40, row["title"])
            sources = [x for x in re.findall(r"TH-\d+", row["source_prospectus"])]
            self.add(f"{row['theorem_id']} source prospectus references resolve", all(x in prior_theorem_ids for x in sources), sources)

        witnesses = self.rows("synthesis/FROZEN_WITNESS_SUITE.csv")
        expected_witness_ids = {x[0] for x in D.WITNESSES}
        self.add("Frozen witness suite has twelve entries", len(witnesses) == 12, len(witnesses))
        self.add("Frozen witness IDs are complete and unique", {x["witness_id"] for x in witnesses} == expected_witness_ids and len(witnesses) == len({x["witness_id"] for x in witnesses}), sorted({x["witness_id"] for x in witnesses}))
        self.add("All witness entries remain specified, not implemented", all(x["status"] == "specified_not_implemented" for x in witnesses), Counter(x["status"] for x in witnesses))
        self.add("Primary suite includes a positive and multiple controls", any(x["target_scope"] == "primary" and x["role"] == "positive" for x in witnesses) and sum(x["target_scope"] == "primary" and x["role"] != "positive" for x in witnesses) >= 5, Counter((x["target_scope"], x["role"]) for x in witnesses))
        self.add("Fallback suite includes a positive and independent-twin control", any(x["witness_id"] == "FW-01" and x["role"] == "positive" for x in witnesses) and any(x["witness_id"] == "FW-02" and x["role"] == "negative" for x in witnesses), "FW-01/FW-02")
        model_ids = {x["id"] for x in self.rows("ledgers/model_registry.csv")}
        for row in witnesses:
            refs = re.findall(r"MF-\d+", row["source_models"])
            self.add(f"{row['witness_id']} source model references resolve", bool(refs) and all(x in model_ids for x in refs), refs)
            self.add(f"{row['witness_id']} states an exact purpose", len(row["exact_purpose"].strip()) >= 35, row["title"])

        # ------------------------------------------------------------------
        # 8. Scenario-verdict ledger and typed outcomes.
        # ------------------------------------------------------------------
        scenario_reg = self.j("scenarios/SCENARIO_REGISTRY.json")
        scenario_ids = {x["id"] for x in scenario_reg["scenarios"]}
        scenario_titles = {x["id"]: x["title"] for x in scenario_reg["scenarios"]}
        outcomes = self.rows("scenarios/OUTCOME_LABEL_REGISTRY.csv")
        outcome_map = {x["outcome_id"]: x for x in outcomes}
        sv = self.rows("synthesis/TARGET_SCENARIO_VERDICTS.csv")
        self.add("Target-scenario ledger has seventy rows", len(sv) == 70, len(sv))
        self.add("Scenario registry supplies thirty-five canonical scenarios", len(scenario_ids) == 35, len(scenario_ids))
        self.add("Each frozen target covers all thirty-five scenarios", all({x["scenario_id"] for x in sv if x["target_id"] == tid} == scenario_ids for tid in ("FT-01", "FT-02")), Counter(x["target_id"] for x in sv))
        self.add("Target-scenario keys are unique", len(sv) == len({(x["target_id"], x["scenario_id"]) for x in sv}), "unique")
        lane_columns = [
            ("st_outcome_id", "st_label", "S-T"),
            ("sr_outcome_id", "sr_label", "S-R"),
            ("sl_outcome_id", "sl_label", "S-L"),
            ("autonomy_outcome_id", "autonomy_label", "A"),
            ("recognition_outcome_id", "recognition_label", "R"),
        ]
        for row in sv:
            key = f"{row['target_id']}/{row['scenario_id']}"
            self.add(f"{key} scenario title resolves", row["scenario_title"] == scenario_titles.get(row["scenario_id"]), row["scenario_title"])
            for id_col, label_col, lane in lane_columns:
                oid = row[id_col]
                meta = outcome_map.get(oid)
                self.add(f"{key} {lane} outcome ID resolves", meta is not None, oid)
                if meta:
                    self.add(f"{key} {lane} lane and label match registry", meta["claim_lane"] == lane and meta["label"] == row[label_col], {"id": oid, "label": row[label_col]})
            self.add(f"{key} remains an expected nonempirical verdict", row["status"] == "frozen_expected_verdict_not_empirical_result", row["status"])
            self.add(f"{key} records a lineage basis", row["lineage_basis"] in {"live-corridor lineage", "least operational predictive ancestry"}, row["lineage_basis"])
            self.add(f"{key} records a derivation basis", "S-R/A inherited" in row["derivation_basis"], row["derivation_basis"])
        counts = Counter((x["target_id"], x["joint_status"]) for x in sv)
        expected_counts = {
            ("FT-01", "joint_target_underdetermined_pending_candidate_specific_witnesses"): 10,
            ("FT-01", "joint_target_fails_on_declared_facts"): 24,
            ("FT-01", "not_applicable_same_carrier"): 1,
            ("FT-02", "joint_target_underdetermined_pending_candidate_specific_witnesses"): 24,
            ("FT-02", "joint_target_fails_on_declared_facts"): 9,
            ("FT-02", "joint_target_satisfied_at_declared_scope"): 1,
            ("FT-02", "not_applicable_same_carrier"): 1,
        }
        self.add("Joint-status counts match frozen criterion-relative ledger", all(counts[k] == v for k, v in expected_counts.items()) and sum(counts.values()) == 70, dict(counts))
        by_key = {(x["target_id"], x["scenario_id"]): x for x in sv}
        self.add("FIACH rejects instantaneous destructive reconstruction lineage", by_key[("FT-01", "S02")]["sl_label"] == "no_declared_lineage_reaches_target", by_key[("FT-01", "S02")]["sl_label"])
        self.add("IAPS permits conditional destructive structural successorship", by_key[("FT-02", "S02")]["sl_label"] == "structural_successor", by_key[("FT-02", "S02")]["sl_label"])
        self.add("IAPS treats simultaneous exact targets branch-valuedly", by_key[("FT-02", "S05")]["sl_label"] == "branch_valued_continuation", by_key[("FT-02", "S05")]["sl_label"])
        self.add("Both targets fail external-decoder autonomy", all(by_key[(t, "S13")]["autonomy_label"] == "bridge_dependent_shadow" for t in ("FT-01", "FT-02")), "S13")
        self.add("Both targets fail delayed post-withdrawal collapse", all(by_key[(t, "S28")]["autonomy_label"] == "autonomy_failure_after_withdrawal" for t in ("FT-01", "FT-02")), "S28")
        self.add("Same-carrier representation control is not misclassified as cross-carrier", all(by_key[(t, "S20")]["joint_status"] == "not_applicable_same_carrier" for t in ("FT-01", "FT-02")), "S20")

        # ------------------------------------------------------------------
        # 9. Copy audit and implementation handoff.
        # ------------------------------------------------------------------
        audit = self.text("synthesis/COPY_VS_CONTINUATION_AUDIT.md")
        audit_prompts = [
            ("exact duplication", "What differs between the primary and exact duplication?"),
            ("symmetric fission", "relation-valued under symmetric fission"),
            ("uniqueness", "Is any uniqueness claim structural or purchased?"),
            ("destructive transfer", "Can destructive transfer satisfy the criterion?"),
            ("gradual replacement", "Does gradual replacement receive its verdict for substantive reasons?"),
            ("autonomy", "Is post-handoff autonomy demonstrated or assumed?"),
            ("claim ceiling", "What does the result concern?"),
        ]
        for label, phrase in audit_prompts:
            self.add(f"Copy audit answers {label}", phrase.lower() in audit.lower(), phrase)
        self.add("Copy audit states an interior operational discriminator", "interior operational witness" in audit and "counterfactually nonredundant" in audit, "corridor")
        self.add("Copy audit refuses uniqueness under exact symmetry", "invariant unique selection impossible" in audit and "no uniqueness claim is frozen" in audit.lower(), "symmetry")
        self.add("Copy audit distinguishes FIACH and IAPS on destructive reconstruction", "FIACH" in audit and "IAPS" in audit and "structural successorship" in audit, "primary/fallback split")
        self.add("Copy audit states autonomy is demonstrated only relative to model data", "demonstrated relative to declared model data" in audit, "autonomy boundary")
        self.add("Copy audit limits result to structural precursor", "structural precursor" in audit and "do not establish phenomenal consciousness" in audit, "claim ceiling")

        handoff = self.text("synthesis/LATER_LANDING_HANDOFF.md")
        for heading in [
            "## 1. Authorized target order", "## 2. Theorem statements to attempt",
            "## 3. Toy programs to build", "## 4. Proof/program order",
            "## 5. Controls required before any positive claim", "## 6. Switch conditions",
            "## 7. Completion conditions for the later project",
        ]:
            self.add(f"Later handoff contains {heading}", heading in handoff, heading)
        self.add("Later handoff starts with no-go/control work before combined positive claim", "No-go and definition unit tests first" in handoff or "countermodels" in handoff.lower(), "order")
        self.add("Later handoff defines primary-to-fallback switch conditions", "Switch from FIACH to IAPS" in handoff or "fallback" in handoff.lower(), "switch")
        self.add("Later handoff explicitly requires no full Six Birds simulation", "No full Six Birds simulation" in handoff, "scope")
        self.add("Later handoff preserves Python-generator/Lean-checker trust split", "Lean" in handoff and "certificate" in handoff.lower(), "trust split")

        # ------------------------------------------------------------------
        # 10. Dossier exit gate, provenance, assumptions, and ledgers.
        # ------------------------------------------------------------------
        dossier = self.text("synthesis/EXPLORATION_DOSSIER.md")
        for phase in range(7):
            self.add(f"Dossier recounts CST-EXP-{phase:02d}", f"CST-EXP-{phase:02d}" in dossier, f"phase {phase}")
        for concept in ["what exact theorem-and-toy target", "counterexample", "assumption", "falsifier", "would not answer"]:
            self.add(f"Dossier supports exit-gate concept: {concept}", concept.lower() in dossier.lower(), concept)
        corpus_assets = {x["asset_id"] for x in self.rows("ledgers/asset_provenance.csv")}
        for aid in ["A-CT-01", "A-PQ-01", "A-PQ-02", "A-PR-01", "A-EX-01", "A-EV-01", "A-LG-01", "A-AG-01", "A-VI-01", "A-TM-01", "A-CF-01", "A-HO-01", "A-RE-01", "A-OP-01", "A-QEC-01", "A-FS-01", "A-NO-01"]:
            self.add(f"Frozen target corpus dependency {aid} resolves", aid in corpus_assets and (aid in dossier + primary + fallback or (aid == "A-PQ-02" and "A-PQ-01/A-PQ-02" in dossier)), aid)
        assumptions = {x["assumption_id"] for x in self.rows("ledgers/assumption_register.csv")}
        for aid in ["D-CARRIER", "H-DISTINCT", "H-BRIDGE-ADM", "H-XCI", "H-SOURCE-FULL", "H-PRESERVE-O", "H-GLOBAL-GLUE", "H-LINEAGE", "H-AUTONOMY", "H-CERT-SOUND", "H-RECOG", "A1", "A2-P", "H-IDENTITY-O"]:
            self.add(f"Frozen target assumption {aid} resolves", aid in assumptions, aid)
        self.add("Dossier keeps certificate soundness and recognition outside structural theorem", "Certificate soundness" in dossier and "recognition" in dossier.lower(), "assumption ladder")
        self.add("Dossier keeps A1/A2-P outside structural theorem", "A1" in dossier and "A2-P" in dossier and "remain outside" in dossier, "ontology boundary")

        decisions = self.rows("ledgers/decision_log.csv")
        d06 = [x for x in decisions if x.get("id", x.get("decision_id", "")).startswith("D06-")]
        self.add("Decision ledger contains ten active CST-EXP-06 decisions", len(d06) == 10 and all(x["status"] == "active" for x in d06), len(d06))
        self.add("Decision IDs are D06-001..D06-010", {x.get("id", x.get("decision_id", "")) for x in d06} == {f"D06-{i:03d}" for i in range(1, 11)}, sorted(x.get("id", x.get("decision_id", "")) for x in d06))
        decision_md = self.text("ledgers/DECISION_LOG.md")
        for did, *_ in D.DECISIONS:
            self.add(f"Markdown decision ledger contains {did}", did in decision_md, did)
        rejected_md = self.text("ledgers/REJECTED_DEFAULTS.md")
        for rid, default, reason in D.REJECTED_DEFAULTS:
            self.add(f"Rejected-default ledger contains {rid}", rid in rejected_md and default in rejected_md and reason in rejected_md, rid)
        unresolved = self.text("ledgers/UNRESOLVED_QUESTIONS.md")
        for number, question in D.OPEN_QUESTIONS:
            self.add(f"Unresolved-question ledger contains implementation question {number}", f"{number}. {question}" in unresolved, number)

        # ------------------------------------------------------------------
        # 11. Explicit nonimplementation and claim-ceiling audit.
        # ------------------------------------------------------------------
        new_code = [
            p for p in r.rglob("*") if p.is_file()
            and ".git" not in p.parts and "__pycache__" not in p.parts
            and p.suffix in {".lean", ".cpp", ".rs", ".go", ".jl"}
            and str(p.relative_to(r)).startswith(("synthesis/", "feasibility/toys/", "formalization/exp06/"))
        ]
        self.add("No theorem or toy implementation file was introduced", not new_code, [str(x.relative_to(r)) for x in new_code])
        admin_python = {
            "scripts/exp06_data.py", "scripts/build_exp06_assets.py", "scripts/validate_exp06.py",
            "scripts/verify_exp06_rebuild.py", "scripts/finalize_exp06_manifest.py",
        }
        phase_python = [str(p.relative_to(r)) for p in r.rglob("*.py") if "exp06" in p.name]
        self.add("Phase Python files are administrative build/validation only", set(phase_python) <= admin_python, sorted(phase_python))
        boundary_docs = [primary, fallback, audit, dossier, handoff, comparison]
        boundary_blob = "\n".join(boundary_docs).lower()
        boundary_checks = [
            ("consciousness nonclaim", "conscious" in boundary_blob and ("does not establish" in boundary_blob or "would not answer" in boundary_blob)),
            ("numerical identity nonclaim", "numerical identity" in boundary_blob or "numerical-identity" in boundary_blob),
            ("A2 boundary", "a2" in boundary_blob),
            ("proof nonimplementation", "not proved" in boundary_blob or "no theorem is proved" in boundary_blob or "no theorem has been proved" in boundary_blob or "prospects, not proofs" in boundary_blob),
            ("toy nonimplementation", "not implemented" in boundary_blob or "no toy program is implemented" in boundary_blob or "no toy program has been written" in boundary_blob),
        ]
        for label, present in boundary_checks:
            self.add(f"Final synthesis preserves boundary: {label}", present, label)
        self.add("Root STATE advances to CST-EXP-06-v1", "CST-EXP-06-v1" in self.text("STATE.md"), "state")
        self.add("Root README names FIACH primary and IAPS fallback", "FIACH" in self.text("README.md") and "IAPS" in self.text("README.md"), "root readme")
        self.add("Root STATUS marks implementation as none", "Implementation inside this phase:** none" in self.text("STATUS.md"), "status")
        self.add("Root CHANGELOG records CST-EXP-06", "## CST-EXP-06" in self.text("CHANGELOG.md"), "changelog")

        # ------------------------------------------------------------------
        # 12. Manifest, rebuild, and final freeze checks.
        # ------------------------------------------------------------------
        if not self.skip_manifest:
            manifest_path = r / "manifests/MANIFEST.json"
            self.add("Final manifest exists", manifest_path.is_file(), "manifests/MANIFEST.json")
            manifest = self.j("manifests/MANIFEST.json") if manifest_path.is_file() else {}
            self.add("Final manifest is labeled CST-EXP-06", manifest.get("phase") == D.PHASE, manifest.get("phase"))
            manifest_bad: list[str] = []
            for entry in manifest.get("files", []):
                p = r / entry["path"]
                if not p.is_file() or p.stat().st_size != entry["bytes"] or self.sha(p) != entry["sha256"]:
                    manifest_bad.append(entry["path"])
            self.add("Every final manifest entry verifies", not manifest_bad and len(manifest.get("files", [])) >= 500, {"checked": len(manifest.get("files", [])), "bad": manifest_bad[:20]})
            self.add("Manifest file_count equals entry count", manifest.get("file_count") == len(manifest.get("files", [])), manifest.get("file_count"))

            sums_path = r / "manifests/SHA256SUMS"
            self.add("SHA256SUMS exists", sums_path.is_file(), "manifests/SHA256SUMS")
            sums_bad: list[str] = []
            sums_count = 0
            if sums_path.is_file():
                for line in sums_path.read_text(encoding="utf-8").splitlines():
                    if not line.strip():
                        continue
                    sums_count += 1
                    expected, rel = line.split("  ", 1)
                    p = r / rel
                    if not p.is_file() or self.sha(p) != expected:
                        sums_bad.append(rel)
            self.add("Every static SHA256SUMS entry verifies", not sums_bad and sums_count >= 500, {"checked": sums_count, "bad": sums_bad[:20]})

            phase_summary = self.j("manifests/PHASE_SUMMARY.json")
            self.add("Phase summary is CST-EXP-06-v1", phase_summary.get("phase") == D.PHASE and phase_summary.get("state_version") == D.STATE_VERSION, {"phase": phase_summary.get("phase"), "state": phase_summary.get("state_version")})
            self.add("Phase summary freezes FIACH and IAPS", phase_summary.get("primary_target", {}).get("id") == "FT-01" and phase_summary.get("fallback_target", {}).get("id") == "FT-02", {"primary": phase_summary.get("primary_target"), "fallback": phase_summary.get("fallback_target")})
            rebuild = self.j("manifests/REBUILD_VERIFICATION.json")
            self.add("Portable rebuild verification passes", rebuild.get("status") == "pass", rebuild.get("status"))
            self.add("Portable rebuild compares a substantial phase surface bank", rebuild.get("surfaces_compared", 0) >= 25 and not rebuild.get("missing") and not rebuild.get("different"), {"count": rebuild.get("surfaces_compared"), "missing": rebuild.get("missing"), "different": rebuild.get("different")})
            self.add("Completion report exists and passes exit gate", "**Exit gate:** PASS" in self.text("manifests/CST-EXP-06_COMPLETION_REPORT.md"), "completion")
            self.add("Restore instructions name CST-EXP-06 tag", "CST-EXP-06-v1" in self.text("manifests/RESTORE_AND_VERIFY.md"), "restore")

        ok = all(x["ok"] for x in self.results)
        if self.write_outputs:
            self.write(ok)
        return ok

    @staticmethod
    def json_safe(value: Any) -> Any:
        if isinstance(value, dict):
            return {str(k): Validator.json_safe(v) for k, v in value.items()}
        if isinstance(value, (list, tuple, set)):
            return [Validator.json_safe(v) for v in value]
        if isinstance(value, Path):
            return str(value)
        return value

    def write(self, ok: bool) -> None:
        out_json = self.root / "manifests/VALIDATION_RESULTS.json"
        out_md = self.root / "manifests/VALIDATION_REPORT.md"
        safe_results = self.json_safe(self.results)
        payload = {
            "schema_version": "1.0",
            "project": "CST-EXP",
            "phase": D.PHASE,
            "status": "pass" if ok else "fail",
            "checks": len(self.results),
            "passed": sum(x["ok"] for x in self.results),
            "failed": sum(not x["ok"] for x in self.results),
            "results": safe_results,
        }
        out_json.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
        lines = [
            "# CST-EXP-06 Validation Report",
            "",
            f"**Result:** {'PASS' if ok else 'FAIL'} — {payload['passed']}/{payload['checks']} checks passed.",
            "",
            "| # | Check | Result | Detail |",
            "|---:|---|---|---|",
        ]
        for i, row in enumerate(safe_results, 1):
            detail = json.dumps(row["detail"], ensure_ascii=False, sort_keys=True) if not isinstance(row["detail"], str) else row["detail"]
            detail = detail.replace("|", "\\|").replace("\n", " ")
            lines.append(f"| {i} | {row['name']} | {'PASS' if row['ok'] else 'FAIL'} | {detail} |")
        out_md.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    ap.add_argument("--skip-manifest", action="store_true")
    ap.add_argument("--no-write", action="store_true")
    args = ap.parse_args()
    v = Validator(args.root, skip_manifest=args.skip_manifest, write=not args.no_write)
    ok = v.run()
    passed = sum(x["ok"] for x in v.results)
    print(("PASS" if ok else "FAIL"), f"{passed}/{len(v.results)}")
    if not ok:
        for row in v.results:
            if not row["ok"]:
                print("FAIL:", row["name"], "::", row["detail"])
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
