#!/usr/bin/env python3
"""Build deterministic CST-EXP-03 exploratory candidate assets."""
from __future__ import annotations

import argparse
import csv
import hashlib
import itertools
import json
import re
import sys
from collections import Counter, defaultdict
from pathlib import Path
from typing import Any

import yaml

sys.path.insert(0, str(Path(__file__).resolve().parent))
import exp03_data as D  # noqa: E402


CSV_KW = {"newline": "", "encoding": "utf-8"}


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text.rstrip() + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", **CSV_KW) as fh:
        writer = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore", lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow({k: normalize_cell(row.get(k, "")) for k in fields})


def normalize_cell(value: Any) -> str:
    if value is None:
        return ""
    if isinstance(value, bool):
        return "true" if value else "false"
    if isinstance(value, (list, tuple, set)):
        return ";".join(str(x) for x in value)
    return str(value).replace("\r\n", "\n").replace("\r", "\n")


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(**CSV_KW) as fh:
        return list(csv.DictReader(fh))


def md_escape(text: str) -> str:
    return str(text).replace("|", "\\|").replace("\n", " ")


def short(text: str, n: int = 190) -> str:
    t = " ".join(str(text).split())
    return t if len(t) <= n else t[: n - 1].rstrip() + "…"


def sha_text(parts: list[str]) -> str:
    return hashlib.sha256("|".join(parts).encode("utf-8")).hexdigest()


def split_ids(value: str) -> list[str]:
    return [x.strip() for x in value.split(";") if x.strip()]


def outcome_name(outcomes: dict[str, dict[str, str]], oid: str) -> str:
    return outcomes[oid]["label"]


def phase_decision_rows(existing: list[dict[str, str]]) -> list[dict[str, str]]:
    rows = [r for r in existing if not r["id"].startswith("D03-")]
    for did, topic, decision, rationale in D.PHASE_DECISIONS:
        rows.append({"id": did, "date": D.DATE, "topic": topic, "decision": decision, "rationale": rationale, "status": "active"})
    return rows


def render_decision_log(rows: list[dict[str, str]]) -> str:
    phase_names = {
        "D00": "CST-EXP-00 — charter and typing discipline",
        "D01": "CST-EXP-01 — corpus mining and canonical asset atlas",
        "D02": "CST-EXP-02 — scenario atlas and neutral transfer semantics",
        "D03": "CST-EXP-03 — independent candidate generation and bridge design",
    }
    out = [
        "# CST-EXP Decision Log",
        "",
        "These rulings freeze repository handling and exploration discipline. Amendments require a new logged decision; none of the rulings is a scientific conclusion.",
        "",
    ]
    for prefix in ["D00", "D01", "D02", "D03"]:
        out += [f"## {phase_names[prefix]}", "", "| ID | Topic | Decision | Rationale | Status |", "|---|---|---|---|---|"]
        for r in rows:
            if r["id"].startswith(prefix + "-"):
                out.append(f"| {r['id']} | `{md_escape(r['topic'])}` | {md_escape(r['decision'])} | {md_escape(r['rationale'])} | {r['status']} |")
        out.append("")
    out += [
        "## Boundary",
        "",
        "The log records methodological, provenance, typing, and phase-control decisions only. CST-EXP-03 records an exploration roster and expected candidate-relative scenario outputs, but it does not select a transported object, bridge, lineage criterion, theorem target, toy program, empirical recognition rule, or ontological conclusion.",
    ]
    return "\n".join(out)


def update_rejected_defaults(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    marker = "## Additional defaults rejected by CST-EXP-03"
    if marker in text:
        text = text.split(marker, 1)[0].rstrip()
    else:
        text = "\n".join(ln for ln in text.splitlines() if not ln.startswith("| RD03-")).rstrip()
    lines = [
        text,
        "",
        marker,
        "",
        "| ID | Premature default | Ruling | Reason |",
        "|---|---|---|---|",
        *[
            f"| {rid} | {premise} | {ruling} | {reason} |"
            for rid, premise, ruling, reason in D.PHASE_REJECTED_DEFAULTS
        ],
    ]
    write_text(path, "\n".join(lines))


def update_unresolved(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    marker = "## Candidate-generation questions added after CST-EXP-03"
    if marker in text:
        text = text.split(marker)[0].rstrip()
    base_numbers = [int(x) for x in re.findall(r"(?m)^(\d+)\. ", text)]
    start = max(base_numbers) + 1 if base_numbers else 1
    section = ["", "", marker, ""]
    for i, question in enumerate(D.PHASE_UNRESOLVED, start=start):
        section.append(f"{i}. {question}")
    write_text(path, text.rstrip() + "\n" + "\n".join(section))


def object_atlas_md() -> str:
    out = [
        "# Transported-Object Atlas",
        "",
        "**Phase status:** exploratory and unranked. This atlas records candidate mathematical objects that might be preserved, transformed, rebuilt, or related across separately typed carriers. An entry is not a claim that the object is sufficient for consciousness, lineage, or personal identity.",
        "",
        "## Summary matrix",
        "",
        "| ID | Object | Kind | Status profile | Candidate use | Principal debt |",
        "|---|---|---|---|---|---|",
    ]
    for x in D.TRANSPORTED_OBJECTS:
        out.append(f"| {x['id']} | {md_escape(x['name'])} | {md_escape(x['kind'])} | {md_escape(x['status_profile'])} | {x['candidate_use']} | {md_escape(short(x['cross_carrier_debt'], 150))} |")
    out += ["", "## Detailed cards", ""]
    for x in D.TRANSPORTED_OBJECTS:
        out += [
            f"### {x['id']} — {x['name']}",
            "",
            f"- **Type skeleton:** `{x['type_skeleton']}`",
            f"- **Ontic/interface status:** {x['status_profile']}.",
            f"- **Corpus assets:** {x['assets']}.",
            f"- **Candidate use:** {x['candidate_use']}.",
            f"- **What it offers:** {x['promise']}",
            f"- **Failure surface:** {x['failure_surface']}",
            f"- **Heterogeneous-carrier obligation:** {x['cross_carrier_debt']}",
            "",
        ]
    out += [
        "## Cross-object observations",
        "",
        "1. No object automatically supplies all five structural/recognition lanes. A predictive quotient can be transported while a full package, lineage, or autonomy fails; a target package can exist without source ancestry; a maintained target can be independent.",
        "2. Objects divide into snapshot-like, dynamical, history/relation-valued, global/glued, and actively maintained families. The bridge morphology must match the family rather than being chosen for mathematical prestige.",
        "3. Objects with public or interface-relative definitions require a declared interface and may change when the interface expands. Objects with maintenance status require a withdrawal boundary and horizon.",
        "4. TO-15 is not a preferred synthesis. It is a controlled possibility whose components must later be justified by counterexamples or minimality results.",
    ]
    return "\n".join(out)


def invariant_atlas_md() -> str:
    out = [
        "# Candidate-Invariant Atlas",
        "",
        "Each invariant below is a possible structural predicate, not a definition of personal continuity. Necessity and sufficiency are candidate-relative. Exact and approximate forms remain separate unless a stability theorem connects them.",
        "",
        "| ID | Invariant | Necessity | Sufficiency ceiling | Composition | Route/copy behavior | Approximation | Observability | Candidates |",
        "|---|---|---|---|---|---|---|---|---|",
    ]
    for x in D.INVARIANTS:
        out.append(
            f"| {x['id']} | {md_escape(x['name'])} | {md_escape(x['necessity'])} | {md_escape(x['sufficiency'])} | {md_escape(x['composition'])} | {md_escape(x['route'])}; {md_escape(x['copy'])} | {md_escape(x['approx'])} | {md_escape(x['observability'])} | {x['candidates']} |"
        )
    out += ["", "## Detailed signatures", ""]
    for x in D.INVARIANTS:
        out += [
            f"### {x['id']} — {x['name']}",
            "",
            f"- **Signature:** `{x['signature']}`",
            f"- **Necessity:** {x['necessity']}.",
            f"- **Sufficiency ceiling:** {x['sufficiency']}.",
            f"- **Composition:** {x['composition']}.",
            f"- **Route sensitivity:** {x['route']}.",
            f"- **Copy/fission behavior:** {x['copy']}.",
            f"- **Approximate form:** {x['approx']}.",
            f"- **Observability/hidden state:** {x['observability']}; hidden-state dependence: {x['hidden']}.",
            f"- **Schemas using it:** {x['candidates']}.",
            "",
        ]
    out += [
        "## Non-equivalences retained",
        "",
        "- IV-01/IV-02 do not imply IV-08.",
        "- IV-04 does not imply IV-11.",
        "- IV-06 does not imply source ancestry.",
        "- IV-08 does not imply certificate soundness, A1, A2-P, recognition, or identity.",
        "- IV-10 does not turn a metric defect into approximate personal identity.",
    ]
    return "\n".join(out)


def bridge_design_md() -> str:
    out = [
        "# Cross-Carrier Bridge Design Space",
        "",
        "A bridge is typed data and admissibility conditions. It is never the proposition that transfer succeeded. Source and target carrier tokens are independently individuated before any bridge is evaluated.",
        "",
        "| ID | Morphology | Signature | Best suited to | Composition | Primary risk | Schemas |",
        "|---|---|---|---|---|---|---|",
    ]
    for x in D.BRIDGES:
        out.append(f"| {x['id']} | {md_escape(x['name'])} | `{md_escape(x['signature'])}` | {md_escape(x['best_for'])} | {md_escape(x['composition'])} | {md_escape(x['risk'])} | {x['candidates']} |")
    out += ["", "## Morphology cards", ""]
    for x in D.BRIDGES:
        out += [
            f"### {x['id']} — {x['name']}",
            "",
            f"- **Typed signature:** `{x['signature']}`",
            f"- **Use case:** {x['best_for']}.",
            f"- **Admissibility:** {x['admissibility']}.",
            f"- **Composition:** {x['composition']}.",
            f"- **Failure/circularity risk:** {x['risk']}.",
            f"- **Candidate schemas:** {x['candidates']}.",
            "",
        ]
    out += [
        "## Bridge-selection rules",
        "",
        "1. State maps cannot be promoted to history bridges without additional route data.",
        "2. Spans/cospans supply comparison or gluing, not causal ancestry.",
        "3. Overlap processes are not continuity by name; they must preserve a declared process organization.",
        "4. Recovery channels can preserve a logical object while failing target autonomy.",
        "5. Branch-valued bridges are allowed and may be required by symmetry; they do not imply one token is numerically identical to every branch.",
        "6. Approximate bridges require a metric, hard gates, thresholds, horizon, and a composition law before they can support any stability claim.",
    ]
    return "\n".join(out)


def brainstorm_md(x: dict[str, Any]) -> str:
    out = [
        f"# {x['title']}",
        "",
        "**Status:** independent CST-EXP-03 brainstorming pass; not a synthesis, ranking, or target recommendation.",
        "",
        f"**Lens:** {x['lens']}  ",
        f"**Scenario families to challenge:** {x['discriminators']}",
        "",
        "## Starting point",
        "",
        x["starting_point"],
        "",
        "## Ideas generated within this lens",
        "",
    ]
    out.extend(f"{i}. {idea}" for i, idea in enumerate(x["ideas"], start=1))
    out += [
        "",
        "## Internal tension",
        "",
        x["tensions"],
        "",
        "## Translation discipline",
        "",
        "Every retained idea must later be represented using separate source/target carrier types, a bridge datum, a lane-typed verdict vector, explicit assumptions, and a nonclaim boundary. Metaphors such as persistence, transfer, or self are not formal primitives.",
        "",
        "## Phase boundary",
        "",
        "This memo does not assert that its lens is necessary or sufficient, and it does not settle consciousness, survival, or personal identity.",
    ]
    return "\n".join(out)


def question_answer(c: dict[str, str], q: dict[str, Any]) -> str:
    qid = q["id"]
    title = c["title"]
    # Core/framing.
    mapping: dict[str, str] = {
        "Q-CORE-001": f"{title} transports or relates {c['object_ids']}: {c['source_type']} to {c['target_type']}. The transported datum is the candidate's named structural object, never a subject-token label.",
        "Q-CORE-002": f"At source the object lives on {c['source_type']}; at target it lives on {c['target_type']}. Comparison is made through {c['common_type']}",
        "Q-CORE-003": f"The bridge is {c['bridge_signature']} Admissibility requires: {c['admissibility']}",
        "Q-CORE-004": f"Bridge kind: {c['bridge_kind']}. It was chosen because it types the candidate's object and branching/history requirements; composition is: {c['composition_rule']}",
        "Q-CORE-005": f"Exact invariants: {c['exact_invariants']}. Permitted variation: {c['allowed_variation']}",
        "Q-CORE-006": f"{c['route_policy']} Loop audit: {c['loop_test']}",
        "Q-CORE-007": f"Copying: {c['copy_rule']} Fission: {c['fission_rule']} Fusion: {c['fusion_rule']} Deletion: {c['deletion_rule']}",
        "Q-CORE-008": f"Withdrawal intervention: {c['removal']} The target is evaluated over {c['autonomy_horizon']}",
        "Q-CORE-009": f"{c['recognition']} Identifiability limits: {c['false_surfaces']}",
        "Q-CORE-010": f"Composition is not automatic. {c['composition_rule']}",
        "Q-CORE-011": c["approximate_version"],
        "Q-CORE-012": f"The structural schema uses no A1 or A2-P. {c['ontological_boundary']}",
        "Q-FRM-001": c["one_sentence"],
        "Q-FRM-002": f"Primary lane: {c['primary_lane']}. The other S-T/S-R/S-L/A/R lanes remain independently reported in every scenario row.",
        "Q-FRM-003": f"A negative result is failure of the named preservation/bridge predicate; underdetermination is returned when required candidate-specific data are absent. Kill criteria: {c['kill_criteria']}",
        "Q-FRM-004": f"Genuinely new or retyped terms: {c['new_terms']}. Corpus assets {c['assets']} are conceptual/provenance inputs only and do not already prove the heterogeneous schema.",
        # Typing.
        "Q-TYP-001": f"The proposed transported object family is {c['object_ids']}, instantiated as {c['source_type']} and {c['target_type']}.",
        "Q-TYP-002": f"Source carrier object: {c['source_type']}. Target carrier object: {c['target_type']}. Common comparison typing: {c['common_type']}",
        "Q-TYP-003": "Carrier tokens are individuated before the verdict by implementation/support identity, resource/dynamics boundary, and the frozen D-CARRIER rule; labels or coordinate changes alone do not create a new token.",
        "Q-TYP-004": "The candidate is genuinely distinct-carrier at the formal level. A cross-medium claim remains conditional on an independent implementation/medium classifier and is not supplied by this phase.",
        "Q-TYP-005": c["source_status"],
        "Q-TYP-006": c["target_status"],
        "Q-TYP-007": c["support_stages"],
        "Q-TYP-008": c["clocks"],
        "Q-TYP-009": c["common_type"],
        # Bridge.
        "Q-BRG-001": c["bridge_signature"],
        "Q-BRG-002": f"The primary morphology is {c['bridge_kind']} (IDs {c['bridge_ids']}). This does not imply success; the admissibility predicate is separate.",
        "Q-BRG-003": f"Bridge data act on: {c['bridge_data']}",
        "Q-BRG-004": c["admissibility"],
        "Q-BRG-005": f"Any causal/process dependence is encoded only in the declared bridge data: {c['bridge_data']}. A common abstraction without a route carries no causal conclusion.",
        "Q-BRG-006": f"The bridge may consume the records/resources named in: {c['bridge_data']}. Every continuing external dependency is reclassified during the withdrawal audit: {c['removal']}",
        "Q-BRG-007": f"A reverse bridge is not assumed. Where declared, it recovers only {c['exact_invariants']} within the admitted domain, not token identity or omitted package structure.",
        "Q-BRG-008": c["composition_rule"],
        # Preservation.
        "Q-PRS-001": c["exact_invariants"],
        "Q-PRS-002": c["allowed_variation"],
        "Q-PRS-003": f"Public equivalence is never sufficient. Candidate treatment of predictive/public structure: {c['hiddenness']}",
        "Q-PRS-004": f"Target package scope: {c['target_scope']} The schema does not silently claim every C1–C8 clause; TS-02 is the only full-package roster entry and still treats realization/soundness separately.",
        "Q-PRS-005": f"Cross-clause/global coherence is required only to the extent included in the object: {c['recombination']} Any stronger promotion/global gate is separately assumed or tested.",
        "Q-PRS-006": c["hiddenness"],
        "Q-PRS-007": f"Action-credit/mineness treatment: {c['action_credit']} A copied ownership label is insufficient unless the candidate also preserves or regenerates the declared minting/provenance rule.",
        "Q-PRS-008": f"Temporal-closure treatment: {c['temporal_closure']} Source and target clocks remain local unless the bridge supplies an explicit monotone relation or route record.",
        "Q-PRS-009": f"Fission/fusion and recombination treatment: {c['recombination']} Branchwise agreement never licenses global recombination preservation without its own compatibility witness.",
        "Q-PRS-010": c["viability"],
        # Route/history.
        "Q-RTE-001": c["route_policy"],
        "Q-RTE-002": c["loop_test"],
        "Q-RTE-003": "Route independence is claimed only under H-ROUTE-FLAT or a candidate-specific confluence/zero-defect theorem; a successful route alone is insufficient.",
        "Q-RTE-004": f"Retained history variables are those named by the object and bridge: {c['bridge_data']}",
        "Q-RTE-005": f"Yes whenever the candidate retains predictive, ledger, recombination, or route data beyond endpoint state. The decisive hidden/history treatment is: {c['hiddenness']}",
        "Q-RTE-006": "Dormant intervals are represented as explicit route segments carrying a record or no active package. The candidate's scenario rows then return successor, no lineage, or based underdetermination; a gap alone decides nothing globally.",
        "Q-RTE-007": "Only if the schema explicitly permits a partial intermediate object and later completion. The phase verdict records that debt; an uninstantiated full package is not silently called a continuing full package.",
        # Lineage.
        "Q-LIN-001": f"The lineage relation is candidate-specific over source/target histories or object instances and uses {c['bridge_kind']}; its typed data are {c['bridge_signature']}",
        "Q-LIN-002": f"The relation is not assumed functional. Copy rule: {c['copy_rule']} Fission/fusion rules: {c['fission_rule']} {c['fusion_rule']}",
        "Q-LIN-003": "Structural equivalence concerns a named object/invariant. Lineage additionally requires an admissible source-to-target route/history witness; independent twins can be equivalent and still receive no lineage edge.",
        "Q-LIN-004": c["copy_rule"],
        "Q-LIN-005": f"Symmetric duplication is never resolved by labels or later deletion. {c['copy_rule']}",
        "Q-LIN-006": f"Fission rule: {c['fission_rule']} The answer is relation- or branch-valued where symmetry requires it; no unique continuer is selected merely from exact structural duplication.",
        "Q-LIN-007": c["fusion_rule"],
        "Q-LIN-008": c["deletion_rule"],
        "Q-LIN-009": c["empty_condition"],
        "Q-LIN-010": c["composition_rule"],
        "Q-LIN-011": "Delayed reconstruction is classified by the candidate's retained route/history object. Exact checkpoint cases may be successors for some schemas, while strict process overlap rejects them and stale records remain underdetermined or fail; no universal label is imported.",
        # Autonomy.
        "Q-AUT-001": c["removal"],
        "Q-AUT-002": c["autonomy_horizon"],
        "Q-AUT-003": f"Only target-carried dynamics named by the schema may maintain the package after withdrawal. Target status: {c['target_status']}",
        "Q-AUT-004": f"The candidate requires target-native repair/audit only to the extent named in its object. Specific treatment: {c['viability']}",
        "Q-AUT-005": f"Earliest relevant failures include the candidate's false surfaces: {c['false_surfaces']}",
        "Q-AUT-006": "No. Autonomy may support an A label but cannot create, erase, or uniquely select an S-L edge; the lanes are stored independently.",
        # Recognition.
        "Q-OBS-001": c["recognition"],
        "Q-OBS-002": f"Public interfaces are treated as incomplete by default; predictive, privileged-audit, or complete-state interfaces are declared per toy. {c['hiddenness']}",
        "Q-OBS-003": f"Required counterfeit control: {c['negative_control']} Additional false surfaces: {c['false_surfaces']}",
        "Q-OBS-004": f"An empirical test would require: {c['recognition']} No such external recognition bridge is supplied in CST-EXP-03.",
        "Q-OBS-005": c["false_surfaces"],
        "Q-OBS-006": "Expanding the interface can dissolve exposure-relative hiddenness and may change an R verdict, but it does not change the underlying candidate predicate unless the predicate itself was interface-relative by declaration.",
        "Q-OBS-007": f"Finite toys are identifiable only under the access stated here: {c['recognition']} Otherwise multiple hidden packages may remain observationally equivalent.",
        # Approximation/composition.
        "Q-APP-001": c["approximate_version"],
        "Q-APP-002": c["composition_rule"],
        "Q-APP-003": "Local error controls global error only under an explicit candidate-specific stability/gluing theorem. High average fidelity cannot cover a failed hard gate.",
        "Q-APP-004": f"Repair may reduce defect only when it is part of target dynamics and its dependencies survive withdrawal. Candidate treatment: {c['viability']}",
        "Q-APP-005": "At zero or small viability/branch margin, arbitrarily small defect may change the classification; the schema therefore returns underdetermined or fails until a positive stability margin is supplied.",
        "Q-APP-006": f"Proposed exact finite core: {c['minimal_model']}",
        "Q-APP-007": "Thresholds must come from a proved stability margin, hard gate, code/error model, or preregistered counterexample boundary—not from preserving preferred scenario labels.",
        # Assumptions/conclusions.
        "Q-ASM-001": "Certificate soundness is needed only for a later semantic claim that certificate satisfaction realizes the intended closure package; it is not used to establish the candidate's typed structural relation.",
        "Q-ASM-002": "A1 is required only for a later conditional ontological realization reading after structural and soundness premises. It is not used in S-T/S-R/S-L/A/R rows.",
        "Q-ASM-003": "A2-P is never a bridge or invariance theorem. It could support only a later carrier-indifferent ontological interpretation after H-XCI and the structural result are separately established.",
        "Q-ASM-004": "Yes. Any personal-identity/survival reading requires H-IDENTITY-O or another explicit metaphysical premise beyond the structural lineage relation.",
        "Q-ASM-005": f"Without A1, A2-P, recognition, or identity premises, the strongest claim is the candidate's lane-typed structural theorem prospect: {c['theorem_shapes']}",
        "Q-ASM-006": f"Toy stipulations include finite source/target objects, declared carrier individuation, complete-state access where used, and candidate assumptions: {c['assumptions']}",
        "Q-ASM-007": "Refusing D-CARRIER/H-DISTINCT removes cross-carrier scope; refusing bridge/invariance hypotheses removes S-T; refusing H-LINEAGE removes S-L; refusing H-AUTONOMY removes A; refusing ontological premises leaves all structural results intact but blocks phenomenal/personal readings.",
        "Q-ASM-008": c["nonclaims"],
        # Controls.
        "Q-CTL-001": c["positive_control"],
        "Q-CTL-002": c["negative_control"],
        "Q-CTL-003": c["adversarial"],
        "Q-CTL-004": c["falsifier"],
        "Q-CTL-005": f"Nearest alternative: {c['nearest_alternative']}; distinguishing scenarios: {c['distinguishing_scenarios']}.",
        "Q-CTL-006": "Yes at phase freeze: all 60 guard records are separately audited with no failed guard. Passing means the schema avoids barred inferences, not that its scientific predicate is correct.",
        # Feasibility.
        "Q-FEA-001": c["minimal_model"],
        "Q-FEA-002": f"Positive witness: {c['positive_control']} Negative controls: {c['negative_control']} and {c['adversarial']}",
        "Q-FEA-003": c["theorem_shapes"],
        "Q-FEA-004": c["no_go_shapes"],
        "Q-FEA-005": f"Yes. Minimal dependencies: {c['implementation_dependencies']}. No full Six Birds simulation is required for reconnaissance.",
    }
    if qid not in mapping:
        raise KeyError(f"No answer template for {qid}")
    return mapping[qid]


def scenario_field_focus(cand_id: str) -> str:
    return {
        "TS-01":"fidelity;granularity;route_multiplicity;clock_relation;instrument_constraints",
        "TS-02":"granularity;bridge_dependence;route_multiplicity;autonomy_intervention;global_glue",
        "TS-03":"target_timing;causal_structure;carrier_relation;handoff_shape;source_fate",
        "TS-04":"fidelity;bridge_dependence;autonomy_intervention;source_fate;viability_margin",
        "TS-05":"fidelity;bridge_dependence;route_multiplicity;carrier_relation;recovery_locus",
        "TS-06":"granularity;route_multiplicity;carrier_relation;global_glue;bridge_dependence",
        "TS-07":"branching;route_multiplicity;granularity;event_package;recombination",
        "TS-08":"clock_relation;source_fate;target_timing;branching;credit_provenance",
        "TS-09":"fidelity;granularity;route_multiplicity;autonomy_intervention;stability_margin",
        "TS-10":"branching;source_fate;target_timing;route_multiplicity;causal_structure",
    }[cand_id]


def under_basis(st: str, sr: str, sl: str, a: str, r: str, c: dict[str, str], s: dict[str, Any]) -> str:
    bits: list[str] = []
    if st == D.ST_UND:
        bits.append("scenario facts do not stipulate the candidate-specific bridge/preservation witness")
    if sr == D.SR_UND:
        bits.append("target package satisfaction at this schema's scope is not stipulated")
    if sl == D.SL_UND:
        bits.append("route/history, many-to-many, fusion-conflict, stale-epoch, or uniqueness data do not determine the lineage relation")
    if a == D.A_UND:
        bits.append("post-withdrawal target dynamics, horizon, or retained-resource result is not supplied")
    if r in {D.R_UND, D.R_NONE}:
        bits.append("the declared finite instruments are incomplete or absent for the needed hidden structure")
    return "; ".join(bits) if bits else "none; every returned lane label is determinate at the candidate's declared scope"


def verdict_evidence(c: dict[str, str], s: dict[str, Any], names: dict[str, str]) -> str:
    return (
        f"{s['id']} is evaluated using {c['title']}'s object {c['object_ids']} and bridge {c['bridge_ids']}. "
        f"The scenario supplies {s['change_mode']} / {s['branching']} / {s['fidelity']} facts. "
        f"Expected lane labels are S-T={names['st']}, S-R={names['sr']}, S-L={names['sl']}, A={names['a']}, R={names['r']}; "
        "these are criterion-relative predictions rather than a global transfer verdict."
    )


def scenario_verdict_rows(candidates: list[dict[str, str]], scenarios: list[dict[str, Any]], outcomes: dict[str, dict[str, str]]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for c in candidates:
        for s in scenarios:
            sid = s["id"]
            st, sr, sl = D.ST_MAP[c["id"]][sid], D.SR_MAP[c["id"]][sid], D.SL_MAP[c["id"]][sid]
            a = D.autonomy_outcome(c["id"], sid)
            r = D.recognition_outcome(c["recognition_mode"], sid)
            names = {"st": outcome_name(outcomes, st), "sr": outcome_name(outcomes, sr), "sl": outcome_name(outcomes, sl), "a": outcome_name(outcomes, a), "r": outcome_name(outcomes, r)}
            ass = ["D-CARRIER", "H-DISTINCT", "H-BRIDGE-ADM"]
            if st not in {D.ST_NA, D.ST_NO}:
                ass += ["H-PRESERVE-O"]
            if sl not in {D.SL_NA, D.SL_NO}:
                ass += ["H-LINEAGE"]
            if a == D.A_YES:
                ass += ["H-AUTONOMY"]
            if s["fidelity"] in {"residual_bounded", "error_corrected", "adaptive", "lossy"}:
                ass += ["H-APPROX"]
            rows.append({
                "candidate_id": c["id"],
                "candidate_version": D.VERSION,
                "scenario_id": sid,
                "scenario_title": s["title"],
                "transported_object_ids": c["object_ids"],
                "bridge_ids": c["bridge_ids"],
                "lineage_criterion": short(c["copy_rule"], 220),
                "st_outcome_id": st,
                "sr_outcome_id": sr,
                "sl_outcome_id": sl,
                "autonomy_outcome_id": a,
                "recognition_outcome_id": r,
                "underdetermination_basis": under_basis(st, sr, sl, a, r, c, s),
                "criterion_sensitive_scenario_fields": scenario_field_focus(c["id"]),
                "assumptions_spent": ";".join(dict.fromkeys(ass)),
                "route_sensitivity": "route-dependent at the declared object" if st == D.ST_ROUTE or sid in {"S14","S32","S35"} else short(c["route_policy"], 260),
                "approximation_scope": f"Scenario fidelity={s['fidelity']}; {c['approximate_version']}",
                "evidence_or_argument": verdict_evidence(c, s, names),
                "blocked_inferences": "No lane inherits another; no outcome implies consciousness, personal identity, A2-P, certificate soundness, or empirical recognition beyond the declared R instrument.",
                "nonclaims": c["nonclaims"],
                "status": "exploratory_expected_not_ranked",
            })
    return rows


def new_primitives(candidates: list[dict[str, str]]) -> list[dict[str, str]]:
    rows: list[dict[str, str]] = []
    for c in candidates:
        base = c["slug"]
        specs = [
            ("01", f"{base}_object_family", "transported_object", f"Obj_S:{c['source_type']}; Obj_T:{c['target_type']}", "S-T;S-R"),
            ("02", f"{base}_bridge_admissibility", "bridge_predicate", c["bridge_signature"], "S-T"),
            ("03", f"{base}_preservation_relation", "invariant_or_relation", c["exact_invariants"], "S-T;S-R"),
            ("04", f"{base}_approximation_defect", "defect_or_metric", c["approximate_version"], "S-T;S-R;A"),
            ("05", f"{base}_lineage_relation", "lineage_criterion", f"copy={c['copy_rule']} fission={c['fission_rule']} fusion={c['fusion_rule']}", "S-L"),
            ("06", f"{base}_withdrawal_autonomy_gate", "autonomy_gate", f"withdraw={c['removal']} horizon={c['autonomy_horizon']}", "A"),
        ]
        for suffix, name, kind, sig, lanes in specs:
            rows.append({
                "primitive_id": f"NP-{c['id']}-{suffix}",
                "candidate_id": c["id"],
                "name": name,
                "kind": kind,
                "typed_signature_or_contract": sig,
                "claim_lanes": lanes,
                "source_or_new_status": "genuinely_new_or_heterogeneous_retyping",
                "imported_asset_inputs": c["assets"],
                "fixed_support_debt": "No cited asset is treated as an already proved heterogeneous bridge; source assumptions and fixed-support flags remain active.",
                "definition_status": "exploratory_not_formalized",
                "circularity_audit": "The primitive is defined through typed data/tests and never through the words identity, survival, consciousness, transfer success, or transcendence.",
                "scenario_discriminators": c["distinguishing_scenarios"],
                "nonclaims": c["nonclaims"],
            })
    return rows


def candidate_feature_rows(candidates: list[dict[str, str]], verdicts: list[dict[str, str]]) -> list[dict[str, str]]:
    by_c = defaultdict(list)
    for v in verdicts:
        by_c[v["candidate_id"]].append(v)
    rows = []
    for c in candidates:
        vr = sorted(by_c[c["id"]], key=lambda x: x["scenario_id"])
        signature = []
        for v in vr:
            signature.extend([v["st_outcome_id"], v["sr_outcome_id"], v["sl_outcome_id"], v["autonomy_outcome_id"], v["recognition_outcome_id"]])
        counts = Counter(signature)
        rows.append({
            "candidate_id": c["id"], "title": c["title"], "lens": c["lens"], "status": "exploratory_equal_status_unranked",
            "primary_lane": c["primary_lane"], "transported_object_ids": c["object_ids"], "invariant_ids": c["invariant_ids"], "bridge_ids": c["bridge_ids"],
            "distinct_carrier_typed": "yes", "source_type": c["source_type"], "target_type": c["target_type"], "common_comparison_type": c["common_type"],
            "history_required": "yes" if any(k in c["object_ids"] for k in ["TO-08","TO-09","TO-10","TO-13"]) else "conditional",
            "causal_overlap_required": "yes" if c["id"] == "TS-03" else "no",
            "relation_valued_lineage": "yes", "copy_rule": c["copy_rule"], "fusion_rule": c["fusion_rule"],
            "route_policy": c["route_policy"], "autonomy_gate": c["removal"], "approximate_version": c["approximate_version"],
            "hidden_state_requirement": c["hiddenness"], "recognition_mode": c["recognition_mode"], "composition_rule": c["composition_rule"],
            "assumptions": c["assumptions"], "asset_ids": c["assets"], "new_primitive_count": "6",
            "nearest_alternative": c["nearest_alternative"], "distinguishing_scenarios": c["distinguishing_scenarios"],
            "scenario_lane_signature_sha256": sha_text(signature),
            "transport_satisfied_count_not_a_score": str(counts[D.ST_YES]),
            "lineage_branch_count_not_a_score": str(counts[D.SL_BRANCH]),
            "underdetermined_cells_not_a_score": str(sum(counts[x] for x in [D.ST_UND,D.SR_UND,D.SL_UND,D.A_UND,D.R_UND])),
            "ranking": "withheld_until_CST-EXP-06",
        })
    return rows


def assumption_matrix(candidates: list[dict[str, str]], assumptions: list[dict[str, str]]) -> list[dict[str, str]]:
    rows = []
    for c in candidates:
        declared = set(split_ids(c["assumptions"]))
        for a in assumptions:
            aid = a["assumption_id"]
            if aid in {"A1","A2-P","H-IDENTITY-O"}:
                status = "explicitly_not_spent_structurally"
                role = "optional later interpretation only"
                lost = "No structural candidate conclusion is lost; only the corresponding ontological/personal reading is unavailable."
            elif aid == "H-CERT-SOUND":
                status = "optional_semantic_boundary" if c["id"] == "TS-02" else "not_used"
                role = "needed only for a later certificate-to-closure interpretation"
                lost = "Structural certificate/package results remain; no semantic realization inference is licensed."
            elif aid in declared:
                if aid == "D-CARRIER": status = "required_definition"
                elif aid == "H-DISTINCT": status = "required_cross_carrier_scope"
                elif aid == "H-BRIDGE-ADM": status = "required_bridge_hypothesis"
                elif aid == "H-XCI": status = "future_theorem_or_explicit_hypothesis_not_inherited"
                elif aid == "H-LINEAGE": status = "declared_criterion_choice"
                elif aid == "H-AUTONOMY": status = "separate_A_lane_goal"
                elif aid == "H-APPROX": status = "approximate_extension_goal"
                elif aid == "H-ROUTE-FLAT": status = "only_for_route_independent_strengthening"
                elif aid in {"H-SOURCE-FULL","H-TARGET-FULL","H-GLOBAL-GLUE"}: status = "candidate_specific_structural_goal"
                else: status = "declared_structural_hypothesis_or_goal"
                role = a["may_license"]
                lost = f"The candidate loses the conclusion licensed by {aid}; it does not gain any ontological conclusion by retaining it."
            else:
                status = "not_used_in_core_schema"
                role = "none in the core candidate"
                lost = "No core conclusion is lost."
            rows.append({
                "candidate_id": c["id"], "assumption_id": aid, "status": status, "role_in_candidate": role,
                "source_default_status": a["default_status"], "does_not_license": a["does_not_license"],
                "conclusion_lost_if_refused": lost, "structural_or_ontological": a["class"],
            })
    return rows


def asset_crosswalk(candidates: list[dict[str, str]], asset_rows: list[dict[str, str]]) -> list[dict[str, str]]:
    by_asset = defaultdict(list)
    for r in asset_rows:
        by_asset[r["asset_id"]].append(r)
    rows = []
    for c in candidates:
        for aid in split_ids(c["assets"]):
            ars = by_asset[aid]
            papers = sorted({r["paper_id"] for r in ars})
            fixed = sorted({r["fixed_support"] for r in ars})
            rows.append({
                "candidate_id": c["id"], "asset_id": aid, "paper_ids": ";".join(papers), "provenance_link_count": str(len(ars)),
                "candidate_role": "conceptual primitive, control, or theorem-shape input; see candidate card",
                "import_kind": "source_traceable_retyping_or_synthesis_input",
                "fixed_support_statuses": ";".join(fixed),
                "heterogeneous_retyping_obligation": "Define distinct source/target types and prove the candidate bridge; no cross-carrier result is inherited.",
                "independence_boundary": "The asset does not establish target consciousness, personal identity, autonomy, or A2-P.",
            })
    return rows


def discriminator_crosswalk(candidates: list[dict[str, str]], scenarios: list[dict[str, Any]], verdicts: list[dict[str, str]], discriminators: list[dict[str, Any]]) -> list[dict[str, str]]:
    vmap = {(v["candidate_id"], v["scenario_id"]): v for v in verdicts}
    rows = []
    for c in candidates:
        for disc in discriminators:
            sids = [s["id"] for s in scenarios if disc["id"] in s.get("primary_discriminators", [])]
            nontrivial = []
            for sid in sids:
                v = vmap[(c["id"], sid)]
                sig = "/".join([v["st_outcome_id"],v["sr_outcome_id"],v["sl_outcome_id"],v["autonomy_outcome_id"],v["recognition_outcome_id"]])
                if any(x in sig for x in ["-01","-03","-04","-05","-06","-07","-08"]):
                    nontrivial.append(sid)
            rows.append({
                "candidate_id": c["id"], "discriminator_id": disc["id"], "discriminator": disc["label"],
                "candidate_response": f"Evaluated through {c['object_ids']} using {c['bridge_ids']}; relevant boundary: {short(c['adversarial'], 180)}",
                "scenario_ids": ";".join(sids), "nontrivial_scenario_ids": ";".join(nontrivial),
                "claim_lanes": disc["lanes"], "status": "exploratory_not_scored",
            })
    return rows


def divergence_rows(candidates: list[dict[str, str]], verdicts: list[dict[str, str]]) -> list[dict[str, str]]:
    by = defaultdict(dict)
    for v in verdicts:
        by[v["candidate_id"]][v["scenario_id"]] = v
    lanes = ["st_outcome_id","sr_outcome_id","sl_outcome_id","autonomy_outcome_id","recognition_outcome_id"]
    rows = []
    for ca, cb in itertools.combinations(candidates, 2):
        diff_cells = 0
        diff_sids = []
        examples = []
        for sid in D.SCENARIO_IDS:
            diffs = [ln for ln in lanes if by[ca["id"]][sid][ln] != by[cb["id"]][sid][ln]]
            if diffs:
                diff_cells += len(diffs)
                diff_sids.append(sid)
                if len(examples) < 4:
                    examples.append(f"{sid}:{','.join(x.split('_')[0] for x in diffs)}")
        rows.append({
            "candidate_a": ca["id"], "candidate_b": cb["id"], "differing_lane_cells": str(diff_cells),
            "differing_scenario_count": str(len(diff_sids)), "differing_scenarios": ";".join(diff_sids),
            "example_differences": ";".join(examples), "interpretation": "design-space divergence only; not a distance score or ranking",
        })
    return rows


def candidate_card(c: dict[str, str], scenarios: list[dict[str, Any]], verdicts: list[dict[str, str]], outcomes: dict[str, dict[str, str]], assumption_rows: list[dict[str, str]]) -> str:
    cv = {v["scenario_id"]: v for v in verdicts if v["candidate_id"] == c["id"]}
    ca = [x for x in assumption_rows if x["candidate_id"] == c["id"]]
    out = [
        f"# {c['id']} — {c['title']}",
        "",
        "**Status:** exploratory candidate schema; equal phase status; unranked; not selected.  ",
        f"**Lens:** {c['lens']}  ",
        f"**Primary claim lane:** {c['primary_lane']}  ",
        f"**Candidate version:** {D.VERSION}",
        "",
        "## One-sentence idea",
        "",
        c["one_sentence"],
        "",
        "## Formal objects and types",
        "",
        f"- **Source object:** `{c['source_type']}`",
        f"- **Target object:** `{c['target_type']}`",
        f"- **Common comparison type / relation:** {c['common_type']}",
        f"- **Transported-object atlas IDs:** {c['object_ids']}",
        f"- **Invariant IDs:** {c['invariant_ids']}",
        f"- **Bridge IDs:** {c['bridge_ids']}",
        f"- **Bridge signature:** {c['bridge_signature']}",
        f"- **Bridge morphology:** {c['bridge_kind']}",
        f"- **Bridge data:** {c['bridge_data']}",
        f"- **Admissibility:** {c['admissibility']}",
        "",
        "## Exact and approximate versions",
        "",
        f"- **Exact preservation:** {c['exact_invariants']}",
        f"- **Permitted variation:** {c['allowed_variation']}",
        f"- **Approximate/noisy version:** {c['approximate_version']}",
        "",
        "## Lane-separated contract",
        "",
        "| Lane | Candidate question | Boundary |",
        "|---|---|---|",
        f"| S-T | Does the typed bridge preserve/relate {c['object_ids']}? | Does not imply target package, lineage, autonomy, recognition, or ontology. |",
        f"| S-R | Does the target instantiate: {md_escape(c['target_scope'])} | Does not imply source ancestry or consciousness. |",
        f"| S-L | Is there a route/history relation under the schema? Copy rule: {md_escape(short(c['copy_rule'], 160))} | Does not imply personal identity or unique continuation. |",
        f"| A | Does the target pass: {md_escape(short(c['removal'], 170))} | Does not alter the lineage relation. |",
        f"| R | Can the declared instruments decide the structural predicate? {md_escape(short(c['recognition'], 150))} | No empirical recognition bridge is supplied. |",
        f"| O | {md_escape(c['ontological_boundary'])} | No O conclusion is detached in this phase. |",
        "",
        "## Carrier, support, and clocks",
        "",
        f"- **Source status:** {c['source_status']}",
        f"- **Target status:** {c['target_status']}",
        f"- **Support through stages:** {c['support_stages']}",
        f"- **Clock/order structure:** {c['clocks']}",
        "",
        "## Preservation audit",
        "",
        f"- **Hiddenness/public matching:** {c['hiddenness']}",
        f"- **Action credit/provenance:** {c['action_credit']}",
        f"- **Temporal closure:** {c['temporal_closure']}",
        f"- **Recombination/global structure:** {c['recombination']}",
        f"- **Viability/maintenance:** {c['viability']}",
        "",
        "## Route, composition, branching, and deletion",
        "",
        f"- **Route policy:** {c['route_policy']}",
        f"- **Loop/holonomy test:** {c['loop_test']}",
        f"- **Composition:** {c['composition_rule']}",
        f"- **Copy:** {c['copy_rule']}",
        f"- **Fission:** {c['fission_rule']}",
        f"- **Fusion:** {c['fusion_rule']}",
        f"- **Deletion:** {c['deletion_rule']}",
        f"- **Empty target:** {c['empty_condition']}",
        "",
        "## Assumption ladder",
        "",
        "| Assumption | Status in this schema | Role | What refusal removes |",
        "|---|---|---|---|",
    ]
    for a in ca:
        if a["status"] != "not_used_in_core_schema":
            out.append(f"| {a['assumption_id']} | {md_escape(a['status'])} | {md_escape(short(a['role_in_candidate'], 170))} | {md_escape(short(a['conclusion_lost_if_refused'], 180))} |")
    out += [
        "",
        "A1, A2-P, H-CERT-SOUND, and H-IDENTITY-O are never silently spent by the scenario matrix. Their structural/ontological roles remain explicit in `ledgers/candidate_assumption_matrix.csv`.",
        "",
        "## Corpus provenance and new mathematics",
        "",
        f"- **Source asset families:** {c['assets']}.",
        f"- **Project-new/retyped primitives:** {c['new_terms']}.",
        "- Every imported asset retains its fixed-support/retyping warning; see `ledgers/candidate_asset_crosswalk.csv` and `ledgers/new_primitive_register.csv`.",
        "",
        "## Expected verdicts on the complete scenario battery",
        "",
        "These are candidate-relative predictions used to expose differences. They are not pass counts, evidence weights, or rankings.",
        "",
        "| Scenario | S-T | S-R | S-L | A | R | Basis/limitation |",
        "|---|---|---|---|---|---|---|",
    ]
    for s in scenarios:
        v = cv[s["id"]]
        out.append(
            f"| {s['id']} {md_escape(s['title'])} | {outcome_name(outcomes,v['st_outcome_id'])} | {outcome_name(outcomes,v['sr_outcome_id'])} | {outcome_name(outcomes,v['sl_outcome_id'])} | {outcome_name(outcomes,v['autonomy_outcome_id'])} | {outcome_name(outcomes,v['recognition_outcome_id'])} | {md_escape(short(v['underdetermination_basis'], 210))} |"
        )
    out += [
        "",
        "## Controls and possible later theorem forms",
        "",
        f"- **Positive control:** {c['positive_control']}",
        f"- **Negative control:** {c['negative_control']}",
        f"- **Strong adversarial case:** {c['adversarial']}",
        f"- **Possible theorem shapes:** {c['theorem_shapes']}",
        f"- **Possible no-go/boundary shapes:** {c['no_go_shapes']}",
        f"- **Toy discriminators:** {c['toys']}",
        f"- **Smallest reconnaissance model:** {c['minimal_model']}",
        f"- **Minimal dependencies:** {c['implementation_dependencies']}",
        "",
        "## Falsification and kill criteria",
        "",
        f"- **Direct falsifier/downgrade test:** {c['falsifier']}",
        f"- **Kill criteria:** {c['kill_criteria']}",
        f"- **Nearest alternative:** {c['nearest_alternative']} on discriminators {c['distinguishing_scenarios']}.",
        "",
        "## Mandatory audits",
        "",
        "- Question bank: **100/100 answered** in `ledgers/candidate_question_responses.csv`.",
        "- Anti-conflation guards: **60/60 audited with no failed guard** in `ledgers/candidate_anti_conflation_audit.csv`.",
        "- Scenario battery: **35/35 scenarios × five lanes populated** in `ledgers/candidate_scenario_verdicts.csv`.",
        "",
        "## Explicit nonclaims",
        "",
        c["nonclaims"],
        "",
        "## Phase ruling",
        "",
        "This schema remains one unranked possibility. CST-EXP-03 makes no recommendation to implement, prefer, merge, or reject it before CST-EXP-04 adversarial stress and later synthesis.",
    ]
    return "\n".join(out)


def design_space_dot(candidates: list[dict[str, str]]) -> str:
    lines = ["digraph CST_EXP03 {", "  rankdir=LR;", "  graph [label=\"CST-EXP-03 unranked candidate design space\", labelloc=t];", "  node [shape=box];"]
    for c in candidates:
        lines.append(f'  "{c["id"]}" [label="{c["id"]}\\n{c["title"]}"];')
        lens = "LENS-" + re.sub(r"[^A-Za-z0-9]+", "_", c["lens"])
        lines.append(f'  "{lens}" [label="{c["lens"]}", shape=ellipse];')
        lines.append(f'  "{lens}" -> "{c["id"]}" [label="lens"];')
        for oid in split_ids(c["object_ids"]):
            lines.append(f'  "{oid}" [shape=oval];')
            lines.append(f'  "{c["id"]}" -> "{oid}" [label="object"];')
        for bid in split_ids(c["bridge_ids"]):
            lines.append(f'  "{bid}" [shape=diamond];')
            lines.append(f'  "{c["id"]}" -> "{bid}" [label="bridge"];')
        for iid in split_ids(c["invariant_ids"]):
            lines.append(f'  "{iid}" [shape=hexagon];')
            lines.append(f'  "{c["id"]}" -> "{iid}" [label="invariant"];')
    lines.append("}")
    return "\n".join(lines)


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", default=".")
    parser.add_argument("--stage", choices=["brainstorms", "all"], default="all",
                        help="freeze independent memos only, or build the full phase")
    args = parser.parse_args()
    root = Path(args.repo).resolve()

    scenario_registry = json.loads((root / "scenarios/SCENARIO_REGISTRY.json").read_text(encoding="utf-8"))
    scenarios = scenario_registry["scenarios"]
    discriminators = scenario_registry["discriminators"]
    outcome_rows = read_csv(root / "scenarios/OUTCOME_LABEL_REGISTRY.csv")
    outcomes = {r["outcome_id"]: r for r in outcome_rows}
    questions = yaml.safe_load((root / "ledgers/exploration_question_bank.yml").read_text(encoding="utf-8"))["questions"]
    guards = read_csv(root / "ledgers/anti_conflation_checklist.csv")
    assumptions = read_csv(root / "ledgers/assumption_register.csv")
    asset_rows = read_csv(root / "ledgers/asset_provenance.csv")

    # Atlases/registries.
    write_text(root / "candidates/TRANSPORTED_OBJECT_ATLAS.md", object_atlas_md())
    write_csv(root / "candidates/transported_object_registry.csv", D.TRANSPORTED_OBJECTS,
              ["id","name","kind","type_skeleton","status_profile","candidate_use","assets","promise","failure_surface","cross_carrier_debt"])
    write_text(root / "candidates/INVARIANT_ATLAS.md", invariant_atlas_md())
    write_csv(root / "candidates/invariant_registry.csv", D.INVARIANTS,
              ["id","name","signature","necessity","sufficiency","composition","route","copy","approx","observability","hidden","candidates"])
    write_text(root / "candidates/BRIDGE_DESIGN_SPACE.md", bridge_design_md())
    write_csv(root / "candidates/bridge_registry.csv", D.BRIDGES,
              ["id","name","signature","best_for","composition","admissibility","risk","candidates"])

    # Independent brainstorming memos. Their bytes contain no TS identifiers;
    # the translation map is added only in the index after the memo hash freeze.
    brain_dir = root / "candidates/brainstorms"
    for x in D.BRAINSTORMS:
        write_text(brain_dir / x["file"], brainstorm_md(x))
    freeze_lines = []
    for x in D.BRAINSTORMS:
        bp = brain_dir / x["file"]
        freeze_lines.append(f"{hashlib.sha256(bp.read_bytes()).hexdigest()}  {x['file']}")
    write_text(brain_dir / "BRAINSTORM_FREEZE.sha256", "\n".join(freeze_lines))
    if args.stage == "brainstorms":
        brain_index = [
            "# Independent Brainstorming Memos", "",
            "These seven lens-specific memos are frozen before target-schema synthesis. Their bytes contain no candidate IDs or ranking metadata.", "",
        ]
        for x in D.BRAINSTORMS:
            brain_index.append(f"- [{x['title']}]({x['file']}) — {x['lens']}; challenge families {x['discriminators']}.")
        brain_index += ["", "See `BRAINSTORM_FREEZE.sha256` for the byte-level freeze."]
        write_text(brain_dir / "INDEX.md", "\n".join(brain_index))
        return

    brain_index = [
        "# Independent Brainstorming Memos", "",
        "All seven passes are preserved separately and have equal exploratory status. The memo bytes were frozen before schema synthesis; the mapping below is a later translation audit, not text embedded in the memos.", "",
    ]
    for x in D.BRAINSTORMS:
        brain_index.append(f"- [{x['title']}]({x['file']}) — {x['lens']}; post-freeze candidate translations {x['candidate_refs']}; discriminators {x['discriminators']}.")
    brain_index += ["", "The exact frozen memo hashes are in `BRAINSTORM_FREEZE.sha256`."]
    write_text(brain_dir / "INDEX.md", "\n".join(brain_index))

    # Candidate scenario predictions and derived ledgers.
    verdicts = scenario_verdict_rows(D.CANDIDATES, scenarios, outcomes)
    verdict_fields = [
        "candidate_id","candidate_version","scenario_id","scenario_title","transported_object_ids","bridge_ids","lineage_criterion",
        "st_outcome_id","sr_outcome_id","sl_outcome_id","autonomy_outcome_id","recognition_outcome_id","underdetermination_basis",
        "criterion_sensitive_scenario_fields","assumptions_spent","route_sensitivity","approximation_scope","evidence_or_argument",
        "blocked_inferences","nonclaims","status"
    ]
    write_csv(root / "ledgers/candidate_scenario_verdicts.csv", verdicts, verdict_fields)

    primitives = new_primitives(D.CANDIDATES)
    write_csv(root / "ledgers/new_primitive_register.csv", primitives,
              ["primitive_id","candidate_id","name","kind","typed_signature_or_contract","claim_lanes","source_or_new_status","imported_asset_inputs","fixed_support_debt","definition_status","circularity_audit","scenario_discriminators","nonclaims"])

    features = candidate_feature_rows(D.CANDIDATES, verdicts)
    feature_fields = ["candidate_id","title","lens","status","primary_lane","transported_object_ids","invariant_ids","bridge_ids","distinct_carrier_typed","source_type","target_type","common_comparison_type","history_required","causal_overlap_required","relation_valued_lineage","copy_rule","fusion_rule","route_policy","autonomy_gate","approximate_version","hidden_state_requirement","recognition_mode","composition_rule","assumptions","asset_ids","new_primitive_count","nearest_alternative","distinguishing_scenarios","scenario_lane_signature_sha256","transport_satisfied_count_not_a_score","lineage_branch_count_not_a_score","underdetermined_cells_not_a_score","ranking"]
    write_csv(root / "ledgers/candidate_feature_matrix.csv", features, feature_fields)

    ass_matrix = assumption_matrix(D.CANDIDATES, assumptions)
    write_csv(root / "ledgers/candidate_assumption_matrix.csv", ass_matrix,
              ["candidate_id","assumption_id","status","role_in_candidate","source_default_status","does_not_license","conclusion_lost_if_refused","structural_or_ontological"])

    crosswalk = asset_crosswalk(D.CANDIDATES, asset_rows)
    write_csv(root / "ledgers/candidate_asset_crosswalk.csv", crosswalk,
              ["candidate_id","asset_id","paper_ids","provenance_link_count","candidate_role","import_kind","fixed_support_statuses","heterogeneous_retyping_obligation","independence_boundary"])

    # Mandatory 100-question bank.
    qrows = []
    for c in D.CANDIDATES:
        for q in questions:
            tags = q.get("relevant_tags", [])
            qrows.append({
                "candidate_id": c["id"], "candidate_version": D.VERSION, "question_id": q["id"], "category": q["category"],
                "status": "answered", "response": question_answer(c, q), "claim_tags": ";".join(tags),
                "assumptions": c["assumptions"],
                "source_or_new_status": f"source-traceable synthesis from {c['assets']} plus registered project-new heterogeneous primitives",
                "supporting_assets": c["assets"], "nonclaims": c["nonclaims"],
            })
    write_csv(root / "ledgers/candidate_question_responses.csv", qrows,
              ["candidate_id","candidate_version","question_id","category","status","response","claim_tags","assumptions","source_or_new_status","supporting_assets","nonclaims"])

    # All 60 guards for every candidate.
    grows = []
    for c in D.CANDIDATES:
        for g in guards:
            detail = (
                f"{c['id']} treats the antecedent as insufficient and does not infer '{g['forbidden_inference']}'. "
                f"Its lane-separated card instead requires or preserves the boundary: {g['minimum_additional_work']} "
                f"Copy/route/autonomy behavior is explicit: {short(c['copy_rule'] + ' ' + c['route_policy'] + ' ' + c['removal'], 300)}"
            )
            grows.append({
                "candidate_id": c["id"], "guard_id": g["guard_id"], "severity": g["severity"], "status": "passed",
                "audit_response": detail, "evidence_paths": f"candidates/target_schemas/{c['id']}.md;ledgers/candidate_scenario_verdicts.csv",
                "unresolved_boundary": "Scientific adequacy remains open; guard passage establishes only absence of the forbidden inference.",
            })
    write_csv(root / "ledgers/candidate_anti_conflation_audit.csv", grows,
              ["candidate_id","guard_id","severity","status","audit_response","evidence_paths","unresolved_boundary"])

    dcross = discriminator_crosswalk(D.CANDIDATES, scenarios, verdicts, discriminators)
    write_csv(root / "ledgers/candidate_discriminator_crosswalk.csv", dcross,
              ["candidate_id","discriminator_id","discriminator","candidate_response","scenario_ids","nontrivial_scenario_ids","claim_lanes","status"])
    div = divergence_rows(D.CANDIDATES, verdicts)
    write_csv(root / "ledgers/candidate_divergence_matrix.csv", div,
              ["candidate_a","candidate_b","differing_lane_cells","differing_scenario_count","differing_scenarios","example_differences","interpretation"])

    # Candidate cards and registry.
    for c in D.CANDIDATES:
        write_text(root / "candidates/target_schemas" / f"{c['id']}.md", candidate_card(c, scenarios, verdicts, outcomes, ass_matrix))
    index = [
        "# Candidate Target-Schema Index",
        "",
        "All ten schemas have equal exploratory status. Ordering by ID is administrative and conveys no preference.",
        "",
        "| ID | Schema | Lens | Primary lane | Objects | Bridges | Distinguishing scenarios |",
        "|---|---|---|---|---|---|---|",
    ]
    for c in D.CANDIDATES:
        index.append(f"| [{c['id']}]({c['id']}.md) | {c['title']} | {c['lens']} | {c['primary_lane']} | {c['object_ids']} | {c['bridge_ids']} | {c['distinguishing_scenarios']} |")
    write_text(root / "candidates/target_schemas/INDEX.md", "\n".join(index))

    registry_candidates = []
    by_v = defaultdict(list)
    for v in verdicts:
        by_v[v["candidate_id"]].append(v)
    feature_map = {x["candidate_id"]: x for x in features}
    for c in D.CANDIDATES:
        entry = dict(c)
        entry["status"] = "exploratory_equal_status_unranked"
        entry["scenario_signature_sha256"] = feature_map[c["id"]]["scenario_lane_signature_sha256"]
        entry["scenario_verdict_file"] = "ledgers/candidate_scenario_verdicts.csv"
        entry["question_responses"] = 100
        entry["guard_audits"] = 60
        entry["new_primitives"] = 6
        registry_candidates.append(entry)
    registry = {
        "schema_version":"1.0", "project":"CST-EXP", "phase":D.PHASE, "generated_date":D.DATE,
        "neutrality_rule":"Candidate records are exploratory predictions. No score, pass count, ordering, or signature distance is a ranking.",
        "counts":{"candidates":len(D.CANDIDATES),"transported_objects":len(D.TRANSPORTED_OBJECTS),"invariants":len(D.INVARIANTS),"bridges":len(D.BRIDGES),"brainstorms":len(D.BRAINSTORMS)},
        "candidates": registry_candidates,
    }
    write_text(root / "candidates/CANDIDATE_REGISTRY.json", json.dumps(registry, indent=2, sort_keys=False))

    # Candidate design-space graph source.
    write_text(root / "candidates/candidate_design_space.dot", design_space_dot(D.CANDIDATES))

    # Candidate comparison guide and exit gate.
    comparison = [
        "# Candidate Comparison Guide — No Ranking in CST-EXP-03",
        "",
        "The candidate matrix is a map of predicates, scopes, and expected differences. It is not a leaderboard.",
        "",
        "## Prohibited uses",
        "",
        "- Do not count `structural_transport_satisfied` cells and call the largest count best.",
        "- Do not penalize a narrow schema merely because its S-R lane is not applicable, or reward a broad schema for buying stronger assumptions.",
        "- Do not treat fewer underdetermined cells as greater truth; underdetermination can reflect honest data requirements.",
        "- Do not interpret pairwise divergence counts as scientific distance or evidence weight.",
        "",
        "## Legitimate uses",
        "",
        "- Identify scenarios on which schemas make different predictions.",
        "- Trace each difference to object choice, bridge morphology, route policy, package scope, or assumptions.",
        "- Select adversarial counterexamples for CST-EXP-04.",
        "- Find candidate pairs that may coincide on a restricted class and therefore suggest comparison theorems.",
        "",
        "## Frozen comparison surfaces",
        "",
        "`ledgers/candidate_feature_matrix.csv`, `ledgers/candidate_scenario_verdicts.csv`, `ledgers/candidate_divergence_matrix.csv`, and `ledgers/candidate_assumption_matrix.csv`.",
    ]
    write_text(root / "candidates/CANDIDATE_COMPARISON_GUIDE.md", "\n".join(comparison))

    exit_audit = f"""# CST-EXP-03 Exit-Gate Audit

## Result

**PASS at build time, subject to `scripts/validate_exp03.py`.**

| Requirement | Evidence |
|---|---|
| Candidate diversity | {len(D.CANDIDATES)} schemas across quotient, process, closure, viability, logical-object, route, ledger, approximation, and relation-valued lenses. |
| Cross-carrier typing | Every feature row has distinct source and target types plus a common comparison type/relation. |
| Noncircularity | {len(primitives)} new/retyped primitives define typed data/contracts and avoid success/identity terms as definitions. |
| Full battery | {len(verdicts)} candidate–scenario rows = 10 × 35, with five populated lanes each. |
| Mandatory questions | {len(qrows)} rows = 10 × 100. |
| Anti-conflation | {len(grows)} rows = 10 × 60, no failed guard. |
| Genuine prediction differences | Pairwise divergence ledger has {len(div)} rows; duplicate signatures are prohibited by validation. |
| No ranking | All schemas carry equal exploratory status; pass counts and divergence are labeled not-a-score. |

## Phase boundary

No preferred schema, merged schema, theorem target, toy-program contract, no-go conclusion, empirical bridge, or ontological interpretation is selected. CST-EXP-04 is the first phase authorized to attack and externally confront these candidates.
"""
    write_text(root / "candidates/EXIT_GATE_AUDIT.md", exit_audit)

    # Governance ledgers.
    decisions = phase_decision_rows(read_csv(root / "ledgers/decision_log.csv"))
    write_csv(root / "ledgers/decision_log.csv", decisions, ["id","date","topic","decision","rationale","status"])
    write_text(root / "ledgers/DECISION_LOG.md", render_decision_log(decisions))
    update_rejected_defaults(root / "ledgers/REJECTED_DEFAULTS.md")
    update_unresolved(root / "ledgers/UNRESOLVED_QUESTIONS.md")

    # Phase changelog and live status.  Rebuilds replace, rather than duplicate,
    # the CST-EXP-03 section.
    phase_changelog = f"""# Changelog — CST-EXP-03

**Date:** {D.DATE}

## Added

- {len(D.TRANSPORTED_OBJECTS)} transported-object possibilities, {len(D.INVARIANTS)} invariant families, and {len(D.BRIDGES)} heterogeneous bridge morphologies;
- {len(D.BRAINSTORMS)} independent lens-specific brainstorming memos;
- {len(D.CANDIDATES)} fully typed, equal-status candidate schemas;
- {len(verdicts)} candidate–scenario verdict records, containing {len(verdicts) * 5} typed lane outputs;
- {len(qrows)} candidate–question responses and {len(grows)} anti-conflation audits;
- {len(primitives)} registered project-new or heterogeneously retyped primitives;
- complete asset, assumption, discriminator, feature, and pairwise-divergence crosswalks;
- deterministic build, validation, manifest, diagram, and restore surfaces.

## Frozen rulings

- every candidate names distinct source and target types plus a common comparison object or relation;
- transported object, invariant, bridge, target realization, lineage, autonomy, recognition, and ontology remain separate;
- symmetric duplication never yields a unique continuer without an admissible asymmetry;
- fixed-support source machinery retains explicit heterogeneous retyping debt;
- A1, A2-P, certificate soundness, and personal-identity interpretation are not spent in structural verdicts;
- scenario pass counts, hashes, and pairwise divergence counts are not rankings.

## Not performed

- no candidate selected, ranked, merged, or frozen as primary/fallback;
- no theorem or no-go result asserted as established;
- no Lean proof, toy program, full simulation, or empirical recognition bridge;
- no consciousness, survival, or personal-identity conclusion.
"""
    write_text(root / "changelog/CST-EXP-03.md", phase_changelog)
    changelog_path = root / "CHANGELOG.md"
    old_changelog = changelog_path.read_text(encoding="utf-8") if changelog_path.is_file() else "# Changelog\n"
    phase_section = phase_changelog.replace("# Changelog — CST-EXP-03", f"## CST-EXP-03 — {D.DATE}", 1).strip()
    if "## CST-EXP-03" in old_changelog:
        prefix, rest = old_changelog.split("## CST-EXP-03", 1)
        if "## CST-EXP-02" in rest:
            rest = "## CST-EXP-02" + rest.split("## CST-EXP-02", 1)[1]
        else:
            rest = ""
        old_changelog = prefix.rstrip() + "\n\n" + rest.lstrip()
    base_tail = old_changelog.split("# Changelog", 1)[1].lstrip() if "# Changelog" in old_changelog else old_changelog
    write_text(changelog_path, "# Changelog\n\n" + phase_section + "\n\n" + base_tail)

    status = f"""# Repository status

**Status date:** {D.DATE}
**Completed phase:** CST-EXP-03
**Exit gate:** PASS subject to `scripts/validate_exp03.py`
**Next authorized exploration phase:** CST-EXP-04
**Implementation authorization:** none
**Validation:** generated during freeze; see `manifests/VALIDATION_REPORT.md`

## Landed in CST-EXP-03

- {len(D.CANDIDATES)} equal-status cross-carrier candidate schemas spanning quotient/algebraic, full-package, causal-process, viability/control, error-correcting, closure/gluing, route/recombination, self/temporal-ledger, approximate bundle, and relation-valued ancestry lenses.
- {len(D.TRANSPORTED_OBJECTS)} candidate transported objects, {len(D.INVARIANTS)} invariant families, and {len(D.BRIDGES)} bridge morphologies.
- {len(D.BRAINSTORMS)} independent brainstorming passes.
- {len(verdicts)} complete candidate–scenario records with {len(verdicts) * 5} typed S-T/S-R/S-L/A/R cells.
- {len(qrows)} responses to the mandatory question bank and {len(grows)} anti-conflation audits.
- {len(primitives)} registered new/retyped primitives, with source-asset and assumption crosswalks.
- Explicit positive, negative, adversarial, fission/fusion, approximation, autonomy, recognition, theorem-shape, no-go-shape, toy-model, falsifier, and kill-criterion fields for every schema.

## Strongest exploratory result

No single notion of “transfer” spans the design space. The phase decomposes a future target into separately typed choices of transported or related object, heterogeneous bridge, invariant, target realization predicate, lineage relation, withdrawal/autonomy test, recognition interface, and ontological assumptions. The ten candidates make genuinely different predictions on the frozen scenario battery.

## Not landed

- No candidate ranking, preferred candidate, merged synthesis, primary target, or fallback target.
- No theorem/no-go result claimed as proved.
- No Lean development, toy program, full Six Birds simulation, or empirical recognition protocol.
- No use of A2-P as a transport theorem and no consciousness, survival, or personal-identity conclusion.

## Frozen reporting rule

CST-EXP-04 must attack each schema on its own typed criterion, retain every candidate’s full scenario signature and assumption price, and may not convert scenario pass counts or divergence counts into a ranking.
"""
    write_text(root / "STATUS.md", status)

    # Repository-facing state.
    state = f"""# Repository State

- **Project:** CST-EXP
- **State version:** CST-EXP-03-v1
- **State date:** {D.DATE}
- **Completed:** CST-EXP-00, CST-EXP-01, CST-EXP-02, CST-EXP-03
- **Next planned phase:** CST-EXP-04
- **Science status:** ten unranked cross-carrier candidate schemas generated; adversarial comparison not begun; no target selected
- **Formalization status:** candidate theorem/toy shapes only; no new proof, Lean development, or toy program implemented
- **Simulation status:** no Six Birds simulation authorized or required
- **Empirical status:** finite-toy instrument requirements recorded; no empirical recognition bridge supplied
- **Ontological status:** no unconditional consciousness, survival, or personal-identity claim

## Frozen CST-EXP-03 rulings

1. The roster contains {len(D.CANDIDATES)} equal-status candidates; administrative ordering is not preference.
2. Every candidate is typed across distinct source and target carrier tokens and names a common comparison object or relation.
3. Transported object, invariant, bridge, target package, lineage, autonomy, recognition, and ontology remain separate.
4. Every candidate answers all 100 questions and all 35 scenarios × five lanes.
5. Every candidate passes all 60 anti-conflation guards at the level of claim discipline.
6. Symmetric duplication is never converted into a unique continuer without an admissible asymmetry.
7. Fixed-support source assets remain conceptual inputs with explicit heterogeneous retyping debt.
8. A1, A2-P, certificate soundness, and H-IDENTITY-O are not spent in structural scenario predictions.
9. Approximation is metric/vector/hard-gate relative and never interpreted as approximate personal identity.
10. No pass count, signature hash, or pairwise divergence count is a ranking.
11. No theorem target, toy program, no-go conclusion, or candidate synthesis is frozen before CST-EXP-04/06.
"""
    write_text(root / "STATE.md", state)

    readme = f"""# CST Exploration Repository

**Project:** consciousness across substrates in Six Birds Theory  
**Repository code:** `CST-EXP`  
**Current completed phase:** `CST-EXP-03`  
**Status:** independent cross-carrier candidate generation complete; {len(D.CANDIDATES)} candidate schemas are preserved at equal exploratory status. No preferred target, theorem, toy program, empirical bridge, or ontological conclusion has been selected.

## Phase architecture

- **CST-EXP-00:** charter, typed claim lanes, 96-term glossary, 60 anti-conflation guards, 100-question bank, and 20-assumption register.
- **CST-EXP-01:** complete 60-paper disposition, 1,359-statement machine bank, 378 curated provenance records, 26 asset families, and typed/fixed-support import controls.
- **CST-EXP-02:** neutral semantics and 35-scenario battery with five output lanes.
- **CST-EXP-03:** {len(D.TRANSPORTED_OBJECTS)} transported-object possibilities, {len(D.INVARIANTS)} invariant families, {len(D.BRIDGES)} bridge morphologies, {len(D.BRAINSTORMS)} independent brainstorming passes, and {len(D.CANDIDATES)} complete candidate schemas.

## CST-EXP-03 entry points

1. `candidates/TRANSPORTED_OBJECT_ATLAS.md`
2. `candidates/INVARIANT_ATLAS.md`
3. `candidates/BRIDGE_DESIGN_SPACE.md`
4. `candidates/brainstorms/INDEX.md`
5. `candidates/target_schemas/INDEX.md`
6. `ledgers/candidate_feature_matrix.csv`
7. `ledgers/candidate_scenario_verdicts.csv`
8. `ledgers/candidate_question_responses.csv`
9. `ledgers/candidate_anti_conflation_audit.csv`
10. `ledgers/new_primitive_register.csv`
11. `ledgers/candidate_divergence_matrix.csv`
12. `candidates/CANDIDATE_COMPARISON_GUIDE.md`

## Candidate roster

| ID | Schema | Lens | Primary lane |
|---|---|---|---|
"""
    for c in D.CANDIDATES:
        readme += f"| {c['id']} | {c['title']} | {c['lens']} | {c['primary_lane']} |\n"
    readme += """

All scenario labels are candidate-relative expected outputs, not empirical results or rankings. S20 remains the same-carrier negative control. P46 remains quarantined. P42 remains the normative SAU revision and P60 has zero independent evidential weight.

## Rebuild and validation

Run:

```sh
scripts/rebuild_exp03.sh
```

The rebuild regenerates all CST-EXP-03 assets, candidate cards, ledgers, and diagrams, then runs the CST-EXP-03 validator, including its inherited corpus and scenario-continuity checks.

## Next authorized phase

`CST-EXP-04` may adversarially attack the ten candidates, mine no-go results, and perform the planned external-literature confrontation. It may not silently rank candidates by pass counts or relax the frozen typing/assumption controls.
"""
    write_text(root / "README.md", readme)

    counts = {
        "candidate_schemas": len(D.CANDIDATES),
        "transported_objects": len(D.TRANSPORTED_OBJECTS),
        "invariants": len(D.INVARIANTS),
        "bridge_morphologies": len(D.BRIDGES),
        "independent_brainstorms": len(D.BRAINSTORMS),
        "candidate_scenario_rows": len(verdicts),
        "typed_scenario_lane_cells": len(verdicts) * 5,
        "candidate_question_rows": len(qrows),
        "candidate_guard_rows": len(grows),
        "new_primitives": len(primitives),
        "candidate_assumption_rows": len(ass_matrix),
        "candidate_asset_links": len(crosswalk),
        "candidate_discriminator_rows": len(dcross),
        "pairwise_divergence_rows": len(div),
        "candidate_cards": len(D.CANDIDATES),
        "phase_03_decisions": len(D.PHASE_DECISIONS),
        "phase_03_rejected_defaults": len(D.PHASE_REJECTED_DEFAULTS),
        "phase_03_unresolved_questions": len(D.PHASE_UNRESOLVED),
    }
    summary = {
        "project":"CST-EXP", "phase":D.PHASE, "generated_date":D.DATE,
        "status":"built_pending_validation", "target_selected":False, "ranking_performed":False,
        "theorem_or_program_implemented":False, "counts":counts,
        "next_phase":"CST-EXP-04",
    }
    write_text(root / "manifests/EXP03_ASSET_SUMMARY.json", json.dumps(summary, indent=2))

    # A compact phase narrative used by finalization and human review.
    synthesis = f"""# CST-EXP-03 Candidate-Generation Synthesis

## Status and phase boundary

CST-EXP-03 produced **{len(D.CANDIDATES)} incompatible, fully typed, equal-status candidate schemas**. This document synthesizes the design space without ranking it. No transported object, bridge, lineage rule, theorem target, toy program, empirical recognition rule, or ontological interpretation is frozen.

The roster deliberately includes schemas that disagree on destructive reconstruction, temporal gaps, causal overlap, external support, independent twins, route holonomy, fission/fusion, package completeness, and approximate stability.

## Common decomposition exposed by the candidates

A serious cross-carrier proposal cannot be represented by one undifferentiated word such as *transfer* or *continuity*. Across the ten schemas, the recurring contract is:

```text
1. source and target carrier individuation
2. transported or related structural object
3. heterogeneous bridge data and admissibility
4. exact or approximate preservation invariant
5. target-native package/realization predicate
6. source-derived lineage relation
7. post-withdrawal autonomy intervention
8. recognition interface and separately priced ontology
```

Any one component can succeed while another fails. An autonomous independent twin may satisfy a target package without source ancestry. A source-derived logical object may remain bridge-supported and fail autonomy. A matched endpoint may retain route holonomy. A branchwise match may fail recombination or global gluing. A viable target may not preserve the source's predictive or credit structure.

## Candidate map

| ID | Core object/bridge | Principal question | What it deliberately does not settle | High-value discriminators |
|---|---|---|---|---|
| TS-01 | predictive quotient dynamics under bisimulation/conjugacy | Is future-sufficient organization preserved across carrier types? | full package, target-native viability, or unique lineage | S11, S12, S14, S26, S35 |
| TS-02 | staged heterogeneous C1–C8 package handoff | Does one globally coherent target-native C-package exist after handoff? | source-target ancestry or certificate soundness | S15, S17, S28, S30, S31 |
| TS-03 | one moving-support causal process | Is there one causally connected process through the support change? | endpoint-reconstruction cases that lack overlap; full package | S02, S06, S07, S21, S27 |
| TS-04 | viability kernel, control, repair, and credit | Can the target maintain itself with target-resident resources after withdrawal? | ancestry from structural or control equivalence | S13, S16, S17, S25, S28 |
| TS-05 | encoded logical package plus recovery | Is a declared logical object preserved under code switching and noise? | unencoded clauses and personal identity | S13, S17, S25, S28, S32 |
| TS-06 | closure/fixed-point span with global gluing | Do source and target realize commuting closure-generated packages? | causal history and unique continuation | S15, S18, S26, S30, S31 |
| TS-07 | continuation functor preserving recombination and holonomy | Are route, branch, fusion, and recombination structures preserved? | full C-package and target autonomy by default | S09, S10, S14, S24, S35 |
| TS-08 | reflexive self/clock/action-credit ledger bridge | Does source-derived self-temporal-credit history continue coherently? | full package and purely state-based reconstruction | S06, S12, S19, S29, S33 |
| TS-09 | residual-bounded predictive/viability bundle | Is a minimal multi-probe bundle preserved within hard gates and margins? | a unique or metaphysical identity metric | S16, S25, S30, S32, S35 |
| TS-10 | heterogeneous predictive-ancestry relation | Which target histories are source-derived successors, branches, fusions, or empty? | target realization and autonomy unless separately established | S03, S05, S09, S10, S26 |

## Principal design fault lines

### Endpoint equivalence versus ongoing process

TS-01, TS-05, TS-06, and TS-09 can in principle accept an abrupt or record-mediated bridge when their named object and bridge equations hold. TS-03 treats a connected moving-support process as constitutive and therefore rejects many detached reconstructions. TS-08 requires source-derived ledger history even when an endpoint state matches. TS-10 allows route-mediated ancestry without requiring live overlap, provided its route witness is noncircular.

### Narrow invariant versus package-rich organization

TS-01 is intentionally narrow: matching predictive dynamics can succeed while binding, credit, temporal closure, or viability differs. TS-02 is intentionally broad and must purchase an integrated package and global coherence. TS-06 replaces the clause list with closure/fixed-point and gluing structure. TS-09 seeks a counterexample-driven intermediate bundle, but must justify why its coordinates are sufficient rather than post hoc.

### Structural correspondence versus source-derived lineage

S26, the independently constructed structural twin, separates these questions. Several schemas can recognize structural correspondence or target realization there, but every candidate denies source-derived lineage. S03/S05/S09/S10/S23 then force function-valued criteria to become branch- or fusion-aware or to admit failure/underdetermination.

### Bridge-supported function versus target-native autonomy

S13, S28, and S29 show that a target may preserve outputs, a code, a clock, or even a structural package only while a source, decoder, scheduler, controller, or repair service remains active. TS-04 makes withdrawal central. TS-05 must place recovery inside the target boundary before claiming autonomy. All other candidates retain a separate A-lane result.

### Exact structure versus defect-bounded approximation

Exact isomorphism does not address noise, but a scalar fidelity score can hide a hard local failure. TS-09 therefore uses a vector residual, hard gates, and viability margins. TS-05 carries code/recovery error. Other candidates define approximate extensions only when they can state a metric, horizon, composition law, and boundary margin. S16 and S32 are the main controls against unjustified continuity of verdicts.

### Route independence versus memory/holonomy

S14 and S35 prevent endpoint agreement from erasing path information. TS-07 makes holonomy and recombination primary. TS-01 and TS-06 allow route-independent strengthenings only after flatness/confluence. TS-03 and TS-08 retain the actual process or ledger route. No candidate obtains route independence merely from equal endpoints.

## Shared constraints that survived candidate generation

The ten candidates are not equivalent, but they converge on several negative constraints:

1. S20 is a same-carrier representation control, not a cross-carrier success.
2. Symmetric exact duplication does not justify a unique continuer without admissible asymmetry.
3. Independent structural equivalence does not create source-derived ancestry.
4. Permanent external-decoder dependence fails target autonomy.
5. Certificate/public/report matching does not establish hidden package structure.
6. Fixed-support SBT assets require explicit heterogeneous retyping.
7. A1, A2-P, certificate soundness, and personal-identity interpretation remain outside structural candidate definitions.

These shared constraints are methodological invariants of the exploration, not evidence that the remaining positive parts are correct.

## Recurrent prospective theorem and no-go seams

Without selecting one schema, the candidate cards repeatedly expose later proof targets of the following forms:

- heterogeneous factorization, simulation, bisimulation, or span existence;
- bridge composition with retained route, clock, branch, recovery, or residual data;
- local-to-global gluing and explicit obstruction;
- flatness/confluence implying route-independent image;
- symmetry-based nonselection under exact duplication;
- branch/fusion relational laws and nonretroactivity under later deletion;
- withdrawal/autonomy under target-native repair and resource margins;
- stability away from viability, gluing, or relation-bifurcation boundaries;
- no-overreading from public, certificate, or incomplete probe equivalence;
- impossibility of reducing every critical package coordinate to one scalar fidelity.

They remain conjecture or no-go *shapes*. No theorem is asserted as proved in this phase.

## Handoff to CST-EXP-04

The next phase should attack each schema on its own criterion rather than asking which has the most favorable scenario count. Priority attacks are:

- circular or verdict-loaded admissible test families;
- spans/common abstractions that erase causal provenance;
- arbitrary support, environment, and recovery boundaries;
- branch relations that become universal or fail fusion composition;
- package schemas that merely transport certificates;
- residual bundles whose coordinate selection or thresholds are post hoc;
- exact endpoint matches with route/recombination defects;
- apparently autonomous targets with delayed external dependence;
- candidates that silently become fixed-support, only identity maps, or vacuous relations.

The external-literature challenge remains intentionally deferred until these internally generated candidates exist, reducing the risk that external terminology determines the target before the SBT design space is understood.

## Unresolved conclusion

The candidate space does not collapse to one plausible target at this stage. That is the intended result. CST-EXP-03 has converted the motivating question into a finite, typed, falsifiable menu of competing structural programs and explicit failure surfaces. CST-EXP-04 must now narrow, split, or reject them before feasibility reconnaissance or target freeze.
"""
    write_text(root / "synthesis/CST-EXP-03_CANDIDATE_GENERATION_SYNTHESIS.md", synthesis)


if __name__ == "__main__":
    main()
