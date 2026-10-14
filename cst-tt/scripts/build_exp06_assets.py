#!/usr/bin/env python3
"""Build CST-EXP-06 synthesis and target-freeze assets.

This phase selects conjecture-grade targets and implementation boundaries only.
It does not prove theorems or implement toy programs.
"""
from __future__ import annotations

import argparse
import csv
import json
import math
import shutil
import subprocess
import sys
from collections import defaultdict
from pathlib import Path
from textwrap import dedent

SCRIPT_DIR = Path(__file__).resolve().parent
if str(SCRIPT_DIR) not in sys.path:
    sys.path.insert(0, str(SCRIPT_DIR))

from exp06_data import (  # noqa: E402
    DATE,
    DECISIONS,
    FALLBACK_ID,
    FALLBACK_THEOREMS,
    FINALISTS,
    HARD_GATES,
    OPEN_QUESTIONS,
    PHASE,
    PRIMARY_ID,
    PRIMARY_THEOREMS,
    REJECTED_DEFAULTS,
    SOFT_CRITERIA,
    STATE_VERSION,
    TARGET_REGISTRY,
    TERMINAL_ID,
    WITNESSES,
)


def write(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    clean = "\n".join(line.rstrip() for line in dedent(text).splitlines())
    path.write_text(clean.rstrip() + "\n", encoding="utf-8")


def csv_write(path: Path, fieldnames: list[str], rows: list[dict[str, object]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as fh:
        w = csv.DictWriter(fh, fieldnames=fieldnames)
        w.writeheader()
        for row in rows:
            w.writerow(row)


def soft_total(finalist: dict) -> float:
    weights = {key: weight for _, key, _, weight in SOFT_CRITERIA}
    return round(sum(weights[k] * finalist["scores"][k] / 5.0 for k in weights), 2)


def selection_scorecard(root: Path) -> tuple[list[dict[str, object]], dict[str, float]]:
    rows: list[dict[str, object]] = []
    totals: dict[str, float] = {}
    for f in FINALISTS:
        all_hard = True
        for gate_id, gate_name in HARD_GATES:
            result = f["hard"][gate_id]
            all_hard &= result == "pass"
            rows.append({
                "candidate_id": f["id"],
                "candidate_title": f["title"],
                "candidate_class": f["class"],
                "selection_status": f["selection_status"],
                "record_type": "hard_gate",
                "criterion_id": gate_id,
                "criterion": gate_name,
                "weight": 0,
                "score_0_to_5": "",
                "weighted_points": "",
                "gate_result": result,
                "rationale": f.get("hard_notes", {}).get(gate_id, "Satisfied by the frozen typed architecture and its explicit controls."),
            })
        total = soft_total(f)
        totals[f["id"]] = total
        for cid, key, name, weight in SOFT_CRITERIA:
            score = f["scores"][key]
            points = round(weight * score / 5.0, 2)
            rows.append({
                "candidate_id": f["id"],
                "candidate_title": f["title"],
                "candidate_class": f["class"],
                "selection_status": f["selection_status"],
                "record_type": "soft_criterion",
                "criterion_id": cid,
                "criterion": name,
                "weight": weight,
                "score_0_to_5": score,
                "weighted_points": points,
                "gate_result": "",
                "rationale": "Comparative decision aid only; see FINALIST_COMPARISON.md for the qualitative basis and counterexample audit.",
            })
        rows.append({
            "candidate_id": f["id"],
            "candidate_title": f["title"],
            "candidate_class": f["class"],
            "selection_status": f["selection_status"],
            "record_type": "summary",
            "criterion_id": "TOTAL",
            "criterion": "Weighted soft-criteria total after hard-gate audit",
            "weight": 100,
            "score_0_to_5": "",
            "weighted_points": total,
            "gate_result": "pass" if all_hard else "fail",
            "rationale": "The total is not evidence and does not automatically determine selection. FT-01 is selected for narrowness, substantive copy discrimination, and joint S-R/S-L/A coverage.",
        })
    csv_write(
        root / "synthesis/TARGET_SELECTION_SCORECARD.csv",
        ["candidate_id", "candidate_title", "candidate_class", "selection_status", "record_type", "criterion_id", "criterion", "weight", "score_0_to_5", "weighted_points", "gate_result", "rationale"],
        rows,
    )
    return rows, totals


def outcome_maps(root: Path) -> tuple[dict[str, dict], dict[str, dict], dict[str, str]]:
    candidate_rows: dict[str, dict] = {}
    with (root / "ledgers/candidate_scenario_verdicts.csv").open(encoding="utf-8") as fh:
        for r in csv.DictReader(fh):
            candidate_rows[(r["candidate_id"], r["scenario_id"])] = r
    scenarios: dict[str, dict] = {}
    with (root / "scenarios/SCENARIO_REGISTRY.json").open(encoding="utf-8") as fh:
        data = json.load(fh)
    seq = data.get("scenarios", data if isinstance(data, list) else [])
    for r in seq:
        scenarios[r["scenario_id"] if "scenario_id" in r else r["id"]] = r
    labels: dict[str, str] = {}
    with (root / "scenarios/OUTCOME_LABEL_REGISTRY.csv").open(encoding="utf-8") as fh:
        for r in csv.DictReader(fh):
            labels[r["outcome_id"]] = r["label"]
    return candidate_rows, scenarios, labels


def combine_st(a: str, b: str) -> str:
    if a == "OT-ST-05" and b == "OT-ST-05":
        return "OT-ST-05"
    if "OT-ST-01" in {a, b}:
        return "OT-ST-01"
    if "OT-ST-03" in {a, b}:
        return "OT-ST-03"
    if a == "OT-ST-02" and b == "OT-ST-02":
        return "OT-ST-02"
    return "OT-ST-04"


def combine_recognition(a: str, b: str) -> str:
    if "OT-R-03" in {a, b}:
        return "OT-R-03"
    if "OT-R-02" in {a, b}:
        return "OT-R-02"
    return "OT-R-01"


def joint_status(st: str, sr: str, sl: str, au: str) -> str:
    if st == "OT-ST-05":
        return "not_applicable_same_carrier"
    if st == "OT-ST-01" or sr in {"OT-SR-01", "OT-SR-04"} or sl == "OT-SL-01" or au in {"OT-A-01", "OT-A-03"}:
        return "joint_target_fails_on_declared_facts"
    if sr == "OT-SR-02" and sl in {"OT-SL-02", "OT-SL-03", "OT-SL-04", "OT-SL-05"} and au == "OT-A-02" and st in {"OT-ST-02", "OT-ST-03"}:
        return "joint_target_satisfied_at_declared_scope"
    return "joint_target_underdetermined_pending_candidate_specific_witnesses"


def target_scenario_rows(root: Path) -> list[dict[str, object]]:
    candidate, scenarios, labels = outcome_maps(root)
    targets = [
        (PRIMARY_ID, "FIACH", "TS-02", "TS-03", "live-corridor lineage"),
        (FALLBACK_ID, "IAPS", "TS-02", "TS-10", "least operational predictive ancestry"),
    ]
    rows: list[dict[str, object]] = []
    for target_id, code, package_cid, lineage_cid, lineage_name in targets:
        for i in range(1, 36):
            sid = f"S{i:02d}"
            p = candidate[(package_cid, sid)]
            l = candidate[(lineage_cid, sid)]
            st = combine_st(p["st_outcome_id"], l["st_outcome_id"])
            sr = p["sr_outcome_id"]
            sl = l["sl_outcome_id"]
            au = p["autonomy_outcome_id"]
            rec = combine_recognition(p["recognition_outcome_id"], l["recognition_outcome_id"])
            status = joint_status(st, sr, sl, au)
            rows.append({
                "target_id": target_id,
                "target_code": code,
                "scenario_id": sid,
                "scenario_title": p["scenario_title"],
                "st_outcome_id": st,
                "st_label": labels[st],
                "sr_outcome_id": sr,
                "sr_label": labels[sr],
                "sl_outcome_id": sl,
                "sl_label": labels[sl],
                "autonomy_outcome_id": au,
                "autonomy_label": labels[au],
                "recognition_outcome_id": rec,
                "recognition_label": labels[rec],
                "joint_status": status,
                "lineage_basis": lineage_name,
                "derivation_basis": f"S-R/A inherited from {package_cid}; S-L inherited from {lineage_cid}; S-T is conservative conjunction; R is the weaker supplied instrument status.",
                "status": "frozen_expected_verdict_not_empirical_result",
            })
    csv_write(
        root / "synthesis/TARGET_SCENARIO_VERDICTS.csv",
        ["target_id", "target_code", "scenario_id", "scenario_title", "st_outcome_id", "st_label", "sr_outcome_id", "sr_label", "sl_outcome_id", "sl_label", "autonomy_outcome_id", "autonomy_label", "recognition_outcome_id", "recognition_label", "joint_status", "lineage_basis", "derivation_basis", "status"],
        rows,
    )
    return rows


def theorem_and_witness_ledgers(root: Path) -> None:
    theorem_rows: list[dict[str, object]] = []
    for target_id, items in [(PRIMARY_ID, PRIMARY_THEOREMS), (FALLBACK_ID, FALLBACK_THEOREMS)]:
        for order, (tid, title, kind, provenance, statement) in enumerate(items, 1):
            theorem_rows.append({
                "target_id": target_id,
                "order": order,
                "theorem_id": tid,
                "title": title,
                "kind": kind,
                "source_prospectus": provenance,
                "frozen_conjecture_shape": statement,
                "status": "conjecture_grade_not_proved",
            })
    csv_write(root / "synthesis/FROZEN_THEOREM_FAMILY.csv", list(theorem_rows[0]), theorem_rows)
    witness_rows = [
        {"witness_id": wid, "target_scope": scope, "role": role, "title": title, "source_models": models, "exact_purpose": purpose, "status": "specified_not_implemented"}
        for wid, scope, role, title, models, purpose in WITNESSES
    ]
    csv_write(root / "synthesis/FROZEN_WITNESS_SUITE.csv", list(witness_rows[0]), witness_rows)


def finalist_comparison_md(totals: dict[str, float]) -> str:
    summary_rows = []
    for f in FINALISTS:
        gate = "PASS" if all(v == "pass" for v in f["hard"].values()) else "FAIL"
        summary_rows.append(f"| {f['id']} | {f['title']} | {gate} | {totals[f['id']]:.2f} | {f['selection_status']} |")
    profiles = []
    for f in FINALISTS:
        profiles.append(f"""
### {f['id']} — {f['title']}

- **Architecture:** {f['architecture']}
- **Status:** `{f['selection_status']}`
- **Strongest case:** {f['strongest_case']}
- **Strongest counterexample:** {f['strongest_counterexample']}
- **Unique insight:** {f['unique_insight']}
- **Scenario where it outperforms alternatives:** {f['outperforming_scenario']}
- **Assumptions spent:** {f['assumptions']}
- **Theorem/toy burden:** {f['burden']}
- **Implementation abandonment trigger:** {f['abandon']}
""")
    return f"""
# CST-EXP-06 Finalist Comparison and Target Selection

**Status:** final exploration comparison; target freeze complete.  
**Date:** {DATE}  
**Primary:** `{PRIMARY_ID}` — Finite Integrated Autonomous Causal Handoff.  
**Fallback:** `{FALLBACK_ID}` — Integrated Autonomous Predictive Successorship.  
**Mandatory companion / terminal fallback:** `{TERMINAL_ID}` — shared finite no-go kernel.

## 1. Comparison rule

The three CST-EXP-05 survivor families answer different lanes. A complete constructive target for this project must keep those lanes separate while jointly representing:

1. **S-R:** an integrated target-native package rather than a public shadow;
2. **S-L:** an explicitly declared source-target structural relation;
3. **A:** post-withdrawal target autonomy.

Consequently, the standalone landing bundles remain indispensable modules but are not by themselves final constructive targets. The paired architectures are the true finalists. The no-go kernel is evaluated as a mandatory companion and terminal fallback, not as a positive transfer theory.

The scorecard uses the governing-plan hard gates plus one explicit project-completeness gate, `HG-10`. Soft scores are transparent decision aids on a 0–5 scale with weights totaling 100. They are not evidence, and a small numerical difference is not a scientific result.

## 2. Hard-gate and weighted summary

| ID | Architecture | Hard gates | Weighted soft total / 100 | Frozen status |
|---|---|---:|---:|---|
{chr(10).join(summary_rows)}

`FT-NG` scores well because small no-go theorems are clean and finishable, but it fails the constructive joint-target gate. `FT-03` has the broadest reach but is not the narrowest first landing. `FT-01` and `FT-02` are close; the choice is made by their substantive interpretation of copying, not by a decimal margin.

## 3. Why FT-01 is primary

`FT-01` is the narrowest architecture that jointly addresses target realization, lineage, and autonomy while making **interior process history** do real mathematical work. It distinguishes a live staged handoff from an exact detached copy even when the copy has the same endpoint state, the same finite package certificate, and target autonomy. The distinguishing condition is not intuition or substrate labels: it is a separately audited no-gap mixed-support corridor containing at least one causally nonredundant source-target update, followed by target takeover and successful withdrawal.

This is the best first meaning of *move* available in the explored formal space. It is conservative: destructive reconstruction does not satisfy the primary lineage relation. That exclusion is a criterion boundary, not a theorem that consciousness cannot survive destructive uploading.

## 4. Why FT-02 is the fallback

`FT-02` addresses the strongest exact case excluded by the primary. It permits a source-derived destructive reconstruction to be a relation-valued structural successor when a finite operational provenance seed, predictive bridge, no-ex-nihilo closure, target package, and autonomy are all established. It excludes independently constructed twins and refuses unique identity under symmetric duplication.

The fallback is activated only if the live-corridor criterion is shown to be circular, noncompositional, or too restrictive for the intended scientific target. It is not an automatic broadening after a failed proof.

## 5. Why the dual-lineage architecture is deferred

`FT-03` would retain both `LiveHandoff` and `PredictiveAncestry`, ideally proving an inclusion such as `LiveHandoff ⊆ PredictiveAncestry` and an exact destructive-reconstruction separation. That is scientifically attractive but too broad for the first theorem-and-toy project. It requires both lineage engines and a nonarbitrary theorem connecting them. It becomes a later unification target after one engine has landed.

## 6. Why the no-go kernel is mandatory

Every constructive attempt must ship with exact boundaries:

- public/report equality does not identify hidden package or process structure;
- symmetric targets admit no invariant unique selector;
- branch marginals need not preserve recombination;
- a permanently external decoder does not establish target autonomy;
- endpoint equality does not establish live-process lineage;
- local certificates need not glue globally;
- path-equivalent public endpoints may retain route holonomy;
- a small scalar residual can hide a local hard-gate failure.

If both constructive targets fail their circularity or nonvacuity gates, these results become the terminal landing rather than discarded preparatory work.

## 7. Full finalist profiles

{''.join(profiles)}

## 8. Freeze decision

The exploration freezes:

- **Primary:** `FT-01 / FIACH`, a relation-valued finite integrated autonomous causal handoff.
- **Fallback:** `FT-02 / IAPS`, a relation-valued integrated autonomous predictive successor.
- **Companion:** `FT-NG`, the exact finite insufficiency and underdetermination suite.

No theorem has been proved and no toy program has been written. The selection specifies what the later project should attempt, what controls it must pass, and what conclusions remain excluded.
"""


def primary_spec_md() -> str:
    theorem_table = "\n".join(f"| {tid} | {title} | {kind} | {src} | {stmt} |" for tid, title, kind, src, stmt in PRIMARY_THEOREMS)
    witness_table = "\n".join(f"| {wid} | {role} | {title} | {models} | {purpose} |" for wid, scope, role, title, models, purpose in WITNESSES if scope in {"primary", "common"})
    return f"""
# Primary Target Specification — FIACH

**Target ID:** `{PRIMARY_ID}`  
**Name:** **Finite Integrated Autonomous Causal Handoff**  
**Status:** frozen conjecture-grade target for a later theorem-and-toy project  
**Claim lanes:** `S-R`, `S-L`, and `A`, returned as separate fields  
**Result ceiling:** structural precursor only

## 1. Motivation

The explored corpus does not justify treating endpoint equality, behavioral copying, target package realization, source ancestry, or target autonomy as interchangeable. The primary target therefore asks for the strongest small finite result that still resembles a system *moving* rather than merely being reconstructed: a heterogeneous episode must build one coherent target-native package, maintain one live causally connected process through a support transition, and leave a target that continues after the source and migration support are withdrawn.

## 2. Typed finite data

All sets below are finite and all carrier tokens are individuated before the verdict.

```text
CarrierId                         finite type
S T : CarrierId                  source and target, with DistinctCarrier(S,T)
Stage := Fin (n+1)               finite ordered handoff stages
State(c)                         carrier-local state type
Event                            finite event type
owner : Event -> CarrierId
stage : Event -> Stage
parents : Event -> Finset Event  acyclic operational dependency graph
Support : Stage -> Finset CarrierId

ClauseId                         finite clause index; first toy uses eight C-shaped proxies
Coord                            finite package-coordinate type
Scope : ClauseId -> Finset Coord
LocalWitness(c,i)                independently defined local witness relation
restrict(i,j)                    overlap restriction maps
JoinTree                         running-intersection witness for the clause cover
HardGate                         independently declared package gate
Ownership                        dependency/resource ownership graph

ProcessSig                       finite process-signature type fixed before evaluation
sig : Event -> ProcessSig
counterfactualInfluence          finite intervention-based nonredundancy predicate
ClockRel                         explicit local-clock/order compatibility

withdraw : Episode -> TargetSystem
Disturbance                      declared finite disturbance alphabet/class
PackageValid : TargetState -> Prop
K : Finset TargetState           proposed target-owned controlled invariant region
```

The first theorem layer may be parametric over `ClauseId` and `LocalWitness`. The first concrete toy must instantiate eight independently falsifiable proxies corresponding to objecthood, strict promotion, reflexive self-coordinate, interface-relative nonexposure, action credit, target-local temporal organization, joint binding/recombination, and viability/repair. This is a finite structural surrogate, not an empirical consciousness certificate.

## 3. Independently defined predicates

### 3.1 Integrated target package

`IntegratedPkg(T,e)` holds only when:

1. every target-local clause relation has a witness;
2. witnesses agree under all declared overlap restrictions;
3. a running-intersection join tree or another proved gluing condition supplies one global witness;
4. every hard gate passes;
5. every final witness and essential dependency is owned by the target boundary after takeover.

No clause may mention `FIACH`, successful transfer, consciousness, sameness of subject, or the final verdict.

### 3.2 Live causal-overlap corridor

`LiveCorridor(S,T,e)` holds only when:

1. `Support(0)` is source-only and the final support is target-only;
2. every process stage is nonempty—there is no undeclared gap or dormant token;
3. at least one stage is genuinely mixed;
4. at least one mixed update has independently checkable nonredundant source and target contributions to a later declared process signature;
5. the admitted process signature and local clock/order relation are preserved according to predeclared rules;
6. a takeover frontier exists after which source-owned process contributions are absent;
7. route memory is retained unless a flatness/confluence theorem proves it irrelevant.

A mere source-to-record-to-target data edge is not a live corridor. A detached exact copy therefore does not satisfy this predicate.

### 3.3 Post-withdrawal autonomy

`Autonomous(T,e,D,K)` holds only when:

1. withdrawal removes the source, migration bridge/controller, external decoder, scheduler, and repair resources not declared inside the target boundary;
2. `K` contains the handoff endpoint and every state in `K` satisfies the target package predicate;
3. for every allowed disturbance from a state in `K`, a target-owned response keeps all successors in `K`;
4. the target boundary and disturbance class were fixed before evaluating the candidate.

The exact theorem should prove controlled invariance for every finite horizon. It does not claim indefinite physical persistence outside the model.

## 4. Frozen relation

For source history node `s`, target history node `t`, and episode `e`:

```text
FIACH_e(s,t) : Prop :=
  DistinctCarrier(S,T)
  ∧ SourcePkg(S,s)                  -- explicit toy stipulation or independent premise
  ∧ StagedClausePreservation(e,s,t)
  ∧ IntegratedPkg(T,t,e)
  ∧ LiveCorridor(S,T,e,s,t)
  ∧ Autonomous(T,e,D,K)
```

`FIACH` is a binary relation, not a function and not an identity predicate. If a common live prefix branches into two separately valid target corridors, both source-target pairs may belong to the relation.

The relation returns a record with separately checkable fields:

```text
{{ package_realized : S-R,
   live_lineage     : S-L,
   autonomous       : A,
   route_status     : flat | route-indexed | unresolved,
   recognition      : R-status }}
```

No field inherits another.

## 5. Core theorem family

| ID | Frozen theorem/no-go target | Kind | Reconnaissance source | Exact intended content |
|---|---|---|---|---|
{theorem_table}

The central theorem is `PTH-05`, but it is intentionally decomposed. The proof is scientifically useful only if `PTH-01` through `PTH-04` are stated independently and the certificate checker does not define success by reusing `FIACH`.

## 6. Exact finite witness suite

| ID | Role | Witness/control | Source model(s) | Required exact discrimination |
|---|---|---|---|---|
{witness_table}

### Primary positive witness shape

The first positive model should combine the finite skeletons without simulating the full Six Birds system:

```text
stage 0: active support {{S0,S1}}
stage 1: active support {{S1,T0}}; both contributions counterfactually nonredundant
stage 2: active support {{T0,T1}}; target takeover
stage 3: source/bridge withdrawn; target remains in package-valid invariant K
```

The target state carries exact finite coordinates `(q,h,a,k,z,v,self=T)` and eight clause records. The clause cover must have an explicit join tree. The negative shadow produces the same finite public trace before withdrawal but obtains hidden update, clock, or repair from removed external tokens and then reaches a sink.

## 7. Toy-program contracts

The later project should build only the following exact tools for the primary:

1. **TP-10 bounded witness/counterexample enumerator** — establish minimal examples and prevent definitions from being rescued after counterexamples appear.
2. **TP-07 package/gluing auditor** — emit per-clause, overlap, join-tree, ownership, and global-witness certificates.
3. **TP-03 continuation/branch classifier** — compute `LiveCorridor` separately from any ancestry relation and return branch-valued results.
4. **TP-08 withdrawal/autonomy checker** — remove named dependencies and compute controlled-invariant sets or shortest collapse traces.
5. **TP-04 bridge-composition checker** — test frontier compatibility, direct-versus-factored agreement, and replacement-order critical pairs.
6. **TP-05/TP-06/TP-09 controls as needed** — holonomy, recombination, and vector hard-gate audits.

Python may search and emit explicit certificates. Lean must define the semantics and check the certificates; enumeration is not a proof oracle.

## 8. Lean kernel targets

A small first kernel can be organized as:

```text
CST/Finite/Carrier.lean
CST/Package/Scope.lean
CST/Package/JoinTree.lean
CST/Package/Gluing.lean
CST/Process/EventGraph.lean
CST/Process/Corridor.lean
CST/Process/CorridorComposition.lean
CST/Autonomy/Ownership.lean
CST/Autonomy/Withdrawal.lean
CST/Autonomy/ControlledInvariant.lean
CST/Handoff/FIACH.lean
CST/Handoff/Fission.lean
CST/Countermodels/{{Copy,Decoder,Gluing,Symmetry,Holonomy}}.lean
```

The first kernel need not import category theory, quotient types, continuous dynamics, neuroscience, or a full Six Birds simulator.

## 9. Corpus dependency map

- `A-CT-01 / P05` supplies the C-package target and the explicit warning that no integrated instance or A2 transport theorem currently exists.
- `A-PR-01` and `A-EX-01` supply promotion/exactification motifs but retain fixed-support retyping debt.
- `A-EV-01` and `A-LG-01` motivate typed event records and the local/global gluing gate.
- `A-AG-01` and `A-VI-01` supply agency, viability, maintenance, and withdrawal-sensitive autonomy machinery.
- `A-TM-01`, `A-CF-01`, `A-RT-01`, and `A-HO-01` motivate local clocks, route memory, critical-pair/confluence, and holonomy controls.
- `A-RE-01` motivates branch/recombination distinctions.
- `A-FS-01` supplies finite semantics and no-smuggling discipline.

Every cross-carrier use is new or heterogeneously retyped; no fixed-support theorem is silently relabeled.

## 10. Assumptions and claim tiers

### Structural theorem premises

`D-CARRIER`, `H-DISTINCT`, `H-BRIDGE-ADM`, a stipulated/checkable finite `H-SOURCE-FULL` surrogate, object-specific `H-PRESERVE-O`, `H-GLOBAL-GLUE`, the criterion choice `H-LINEAGE`, and `H-AUTONOMY`. `H-ROUTE-FLAT` is required only for route-independent strengthenings; otherwise results remain route-indexed.

### Not used by the structural theorem

`H-CERT-SOUND`, `H-RECOG`, `A1`, `A2-P`, and `H-IDENTITY-O` are not proof premises. They cannot repair a failed corridor, gluing, ownership, or autonomy antecedent.

### Claim ceiling

A proved FIACH theorem would establish only:

- one finite target package surrogate exists;
- one declared live structural lineage relation connects source and target histories;
- the target is autonomous under the declared withdrawal and disturbance model.

It would not establish that either system is conscious, that consciousness literally moved, that the source survived, that the source and target are numerically identical, or that substrate indifference is true.

## 11. Copy and fission policy

- **Independent twin:** may satisfy target package and autonomy; fails FIACH lineage.
- **Nondestructive detached exact copy:** fails FIACH unless created along a valid live corridor; source persistence does not change that.
- **Later deletion of source:** does not retroactively create a corridor or unique selection.
- **Symmetric live fission:** both valid branches are related; no unique identity claim.
- **Fusion:** requires actual coupled process merger plus package/recombination gluing; endpoint state fusion is insufficient.
- **Destructive reconstruction/gap:** fails the primary corridor predicate and is routed to the fallback audit.

## 12. Kill and downgrade criteria

Switch away from the primary if any of the following occurs:

1. every viable process signature or nonredundancy predicate mentions the desired continuation verdict;
2. two individually valid corridors fail composition despite all stated frontier conditions;
3. a detached reconstruction satisfies every declared corridor condition;
4. no nontrivial finite integrated target package survives an independent clause/gluing/ownership audit;
5. target autonomy requires an undeclared or post hoc enlarged boundary;
6. route-memory omissions make direct and factored results noncongruent and cannot be repaired without making the target unwieldy.

Items 1–3 trigger the FT-02 fallback. Items 4–5 also threaten FT-02 and may force the terminal no-go landing. Approximation is deferred rather than used to rescue a failed exact target.

## 13. Excluded claims

No result in this target is a theorem about empirical human uploading, biological necessity, phenomenal continuity, moral status, legal identity, numerical identity, A1, A2-P, or certificate soundness. “Causal handoff” is the name of a finite structural relation, not a synonym for personal survival.
"""


def fallback_spec_md() -> str:
    theorem_table = "\n".join(f"| {tid} | {title} | {kind} | {src} | {stmt} |" for tid, title, kind, src, stmt in FALLBACK_THEOREMS)
    witness_table = "\n".join(f"| {wid} | {role} | {title} | {models} | {purpose} |" for wid, scope, role, title, models, purpose in WITNESSES if scope in {"fallback", "common"})
    return f"""
# Fallback Target Specification — IAPS

**Target ID:** `{FALLBACK_ID}`  
**Name:** **Integrated Autonomous Predictive Successorship**  
**Status:** frozen fallback for a later theorem-and-toy project  
**Activation condition:** the primary live-corridor relation is circular, noncompositional, or scientifically too restrictive, while a noncircular operational ancestry relation remains viable

## 1. Motivation

The primary deliberately excludes detached destructive reconstruction. The fallback asks what can still be said when the source is scanned, recorded, erased, and reconstructed on a distinct target carrier. It does not call such a target the uniquely identical continuer. Instead it seeks a finite, source-derived, relation-valued **successorship** result joined to the same independent target-package and autonomy gates used by the primary.

## 2. Typed finite data

The target package, gluing, ownership, withdrawal, disturbance, and invariant-region types are inherited from FIACH. The lineage engine is replaced by:

```text
HistNode                         finite history/event node type
H : FiniteOperationalGraph
srcNodes tgtNodes : Finset HistNode
reachable_H : HistNode -> HistNode -> Prop

Probe                           declared finite predictive probe family
PredSig(node)                   canonical bounded predictive signature
PredCompat : HistNode -> HistNode -> Prop

Seed : HistNode -> HistNode -> Prop
Gamma : Relation HistNode -> Relation HistNode
Anc := leastFixedPoint(Gamma, Seed)
```

`Seed(s,t)` may hold only when a predeclared operational provenance path connects `s` to `t`, the typed record/bridge is admissible, and the selected predictive/transition obligations hold. It may not mention ancestry, continuation, same subject, survival, or the final IAPS verdict.

`Gamma` must be monotone and may add only declared transition-matched descendants and guarded fission/fusion consequences. Every nonseed rule requires an already related predecessor; no target pair is created ex nihilo.

## 3. Frozen relation

```text
IAPS_e(s,t) : Prop :=
  DistinctCarrier(S,T)
  ∧ SourcePkg(S,s)
  ∧ Anc_e(s,t)
  ∧ IntegratedPkg(T,t,e)
  ∧ Autonomous(T,e,D,K)
```

`IAPS` is relation-valued. A source-derived destructive reconstruction can satisfy it. An independently constructed but structurally identical twin with no source-reachable operational path cannot. Symmetric copies may both be successors.

The result remains a conjunction of separate lanes; ancestry does not prove package realization and package realization does not prove ancestry.

## 4. Core theorem family

| ID | Frozen theorem/no-go target | Kind | Reconnaissance source | Exact intended content |
|---|---|---|---|---|
{theorem_table}

The fallback's central scientific burden is not fixed-point existence; that part is elementary. The burden is specifying `Seed` and `Gamma` operationally enough to exclude independent twins and stale/adversarial records without encoding the desired conclusion.

## 5. Exact finite witness suite

| ID | Role | Witness/control | Source model(s) | Required exact discrimination |
|---|---|---|---|---|
{witness_table}

### Destructive reconstruction positive shape

```text
source active q
  --snapshot--> record r with typed provenance and predictive certificate
  --erase-->    no active source token
  --activate--> target q := decode(r)
  --withdraw--> target package remains autonomous
```

The gap is represented explicitly. The ancestry result comes from the declared source-record-target operational path and closure rules, not from endpoint equality. A twin initialized to the same `q` without a source-reachable path is excluded.

## 6. Toy-program contracts

1. **TP-01 predictive quotient calculator** — compute finite predictive signatures and bridge saturation.
2. **TP-03 continuation/branch classifier** — compute `Anc`, derivation ranks, fission/fusion shapes, and the disagreement with `LiveCorridor`.
3. **TP-07 package/gluing auditor** — establish the target package independently of ancestry.
4. **TP-08 withdrawal/autonomy checker** — establish target-native maintenance independently of ancestry.
5. **TP-06 recombination tester** — block fusion claims that preserve branch marginals but lose joint provenance or credit.
6. **TP-10 bounded enumerator** — search for universalization, independent-twin entry, or smaller countermodels.

## 7. Lean kernel targets

```text
CST/Predictive/Signature.lean
CST/Predictive/Partition.lean
CST/Predictive/Bridge.lean
CST/Ancestry/OperationalGraph.lean
CST/Ancestry/Seed.lean
CST/Ancestry/Closure.lean
CST/Ancestry/Leastness.lean
CST/Ancestry/FissionFusion.lean
CST/Ancestry/TwinExclusion.lean
CST/Successor/IAPS.lean
CST/Countermodels/{{Symmetry,Gap,PackageInsufficiency}}.lean
```

The package/gluing/autonomy modules are shared with the primary.

## 8. Assumptions and claim tiers

Structural premises include `D-CARRIER`, `H-DISTINCT`, `H-BRIDGE-ADM`, a finite source package premise, object-specific `H-PRESERVE-O`, `H-GLOBAL-GLUE`, the operational `Seed`, monotone no-ex-nihilo `Gamma`, criterion choice `H-LINEAGE`, and `H-AUTONOMY`.

`A2-P` does not create a provenance path or predictive bridge. `A1`, certificate soundness, recognition, and personal-identity interpretation remain outside the theorem.

## 9. Copy, fission, fusion, and gap policy

- **Source-derived destructive reconstruction:** may be an IAPS successor when its seed and all target gates pass.
- **Independent exact twin:** excluded under no-ex-nihilo reachability.
- **Nondestructive exact copies:** each qualifying source-derived target may enter the relation; no exclusive selector.
- **Later deletion:** does not retroactively select one branch.
- **Fission:** one-to-many relation.
- **Fusion:** many-to-one relation only under declared predecessor and conflict/gluing rules; ancestry may hold while package realization fails.
- **Undeclared temporal gap/dormancy semantics:** underdetermined rather than automatically accepted or rejected.

## 10. Kill and downgrade criteria

Abandon or downgrade IAPS if:

1. `Seed` contains continuation-equivalent vocabulary or every data edge qualifies;
2. the least relation includes a disconnected independent twin;
3. repeated fission/fusion makes the relation universal;
4. stale or adversarial records cannot be distinguished without post hoc conditions;
5. predictive ancestry is used to infer package realization rather than paired with an independent audit;
6. no finite source-derived destructive positive survives all target package/autonomy gates.

If these occur, the terminal target is the common no-go suite: symmetry, public-shadow, temporal-gap underdetermination, predictive-package insufficiency, and independent-twin nonidentifiability under restricted interfaces.

## 11. Explicit nonclaims

IAPS does not establish that destructive uploading preserves consciousness, that every source-derived copy is the same person, that operational ancestry is metaphysically sufficient, or that a relation-valued successor has any particular moral/legal status. It is a finite structural successorship theorem target only.
"""


def copy_audit_md() -> str:
    return f"""
# Final Copy-versus-Continuation Audit

**Primary:** `{PRIMARY_ID}` / FIACH  
**Fallback:** `{FALLBACK_ID}` / IAPS  
**Audit status:** PASS for target freeze; no theorem-level conclusion is claimed.

## 1. Formal comparison table

| Episode type | Target package may exist? | Target autonomy may hold? | Source provenance? | Live mixed corridor? | FIACH S-L | IAPS S-L | Unique identity? |
|---|---:|---:|---:|---:|---|---|---|
| Independently constructed structural twin | yes | yes | no | no | no | no | not supplied |
| Detached nondestructive exact copy | yes | yes | usually yes | no | no | branch-valued if Seed/Γ pass | not supplied |
| Copy followed by later source deletion | yes | yes | yes | no | no; deletion is nonretroactive | unchanged relation-valued result | not supplied |
| Two exact symmetric targets | yes | separately testable | symmetric | no or symmetric corridors | both if both have valid live corridors; otherwise neither | both if both satisfy ancestry | invariant unique selection impossible |
| Destructive source-record-target reconstruction | yes | yes | yes | no | no | structural successor if Seed/Γ pass | not supplied |
| Gradual component replacement | separately audited | must pass withdrawal | yes | yes when mixed/nonredundant/no-gap conditions hold | qualifying live relation | normally also ancestral if a later inclusion theorem is proved | not supplied |
| Decoder-supported shadow | apparent/conditional | no after withdrawal | may exist | may exist | joint FIACH fails A | joint IAPS fails A | not supplied |

## 2. What differs between the primary and exact duplication?

The difference is not endpoint state, behavior, public report, certificate text, or target autonomy. FIACH requires an **interior operational witness**:

```text
source-only support
→ at least one mixed support stage
→ a counterfactually nonredundant source-and-target update
→ no undeclared empty process interval
→ target takeover
→ withdrawal with target-owned persistence
```

An exact detached copy can match every endpoint field and still lack this corridor. This gives the primary a substantive copy/continuation discriminator without claiming the discriminator is metaphysically necessary for consciousness.

## 3. Is the criterion relation-valued under symmetric fission?

Yes. Both targets are included when both satisfy the selected relation and all target gates. Neither target labels, later divergence, nor later deletion can choose one arm. `PTH-07/FTH-07` requires an automorphism argument showing that an invariant selector cannot choose a singleton from an exact two-target orbit.

## 4. Is any uniqueness claim structural or purchased?

No uniqueness claim is frozen. A one-target output can occur in a particular finite episode because only one target satisfies the relation, but the theorem does not assert global uniqueness or numerical identity. A future unique-successor theorem would require an independently stated asymmetry and would spend `H-LINEAGE-UNIQUE`; that assumption is not part of either target.

## 5. Can destructive transfer satisfy the criterion?

- **FIACH:** no, when “destructive transfer” means the source process terminates before the target process becomes active and no declared dormancy/process token bridges the gap. This is a definition-level boundary of the live-corridor relation.
- **IAPS:** yes conditionally, when there is an operational source-record-target path, a saturated predictive/transition bridge, a no-ex-nihilo ancestry closure, an integrated target package, and post-withdrawal autonomy.

The fallback verdict is **structural successorship**, not unique continuation or personal identity.

## 6. Does gradual replacement receive its verdict for substantive reasons?

Yes. Merely ordering replacements slowly is insufficient. The positive witness must show:

1. distinct source and target support tokens;
2. nonempty process support at every stage;
3. a genuinely mixed stage;
4. an intervention-based certificate that both source and target contributions matter to the next declared process signature;
5. package preservation/gluing at the target;
6. target takeover and source/bridge removal;
7. a target-owned invariant region after withdrawal.

If any item fails, graduality alone does not pass FIACH.

## 7. Is post-handoff autonomy demonstrated or assumed?

In the later finite theorem it is **demonstrated relative to declared model data** by controlled-invariance or exhaustive finite-horizon reachability. The target boundary, removed resources, disturbance class, and package-valid set are theorem inputs. The empirical claim that a real target has those transition/resource facts would still require a recognition bridge; that is not supplied here.

## 8. What does the result concern?

The frozen targets concern only a structural precursor:

- FIACH: integrated target realization + live structural lineage + finite-model autonomy;
- IAPS: integrated target realization + operational predictive successorship + finite-model autonomy.

They do not establish phenomenal consciousness, personal survival, numerical identity, or substrate indifference. Those conclusions require additional premises that remain separately priced and contested.

## 9. Additional edge cases

### Later source deletion

Deletion does not alter the relation already determined at the split. It cannot turn two symmetric copies into one unique continuer.

### Fusion

A target may have several structural predecessors only when all declared predecessor paths and a conflict/recombination guard pass. Ancestry can hold while the integrated target package fails because exclusive action-credit or joint-binding histories do not glue.

### Temporal gaps

FIACH rejects undeclared gaps. IAPS decides only when a dormancy/provenance rule is explicit; otherwise it returns typed underdetermination.

### Route holonomy

Equal endpoints do not imply route-independent handoff. Results remain route-indexed unless retained route-memory actions are proved flat/confluent.

### Approximate copying

No approximate verdict is frozen from a scalar similarity score. A later extension must use exact rational coordinate defects, hard gates, margins, and a composition theorem.

## 10. Audit verdict

The primary is not “copying under another name”: it adds a live mixed-process condition that exact detached copying can fail while endpoint, package, and autonomy facts remain fixed. The fallback openly studies source-derived copying as relation-valued successorship and refuses to relabel it numerical identity. This explicit split is the central reason the final target freeze is defensible.
"""


def dossier_md(totals: dict[str, float], scenario_rows: list[dict[str, object]]) -> str:
    primary_counts = defaultdict(int)
    fallback_counts = defaultdict(int)
    for r in scenario_rows:
        (primary_counts if r["target_id"] == PRIMARY_ID else fallback_counts)[r["joint_status"]] += 1
    return f"""
# CST-EXP Exploration Dossier

**Project:** consciousness across substrates in Six Birds Theory  
**Completed preparatory phases:** CST-EXP-00 through CST-EXP-06  
**Frozen primary target:** `{PRIMARY_ID}` / FIACH  
**Frozen fallback target:** `{FALLBACK_ID}` / IAPS  
**Mandatory companion:** `{TERMINAL_ID}` / finite no-go kernel  
**Boundary:** this dossier selects later theorem and toy targets; it does not answer whether consciousness actually survives a substrate change.

## Executive synthesis

The most defensible first project is not a theorem saying “consciousness transfers.” It is a finite structural theorem family about a **target-native integrated package**, a **source-target lineage relation**, and **post-withdrawal autonomy**, with those three results returned separately.

The primary relation, FIACH, uses a live no-gap mixed-support process corridor. It treats gradual/live handoff as a structural continuation relation and rejects detached exact reconstruction even when endpoint package and autonomy match. The fallback, IAPS, uses a least operational predictive ancestry relation. It can classify a source-derived destructive reconstruction as an autonomous structural successor, excludes independent twins, and is explicitly relation-valued under copying and fission.

Both targets stop before consciousness, personal identity, or survival. The common no-go suite proves the insufficiency of public matching, symmetry-breaking by labels/deletion, branch marginals, permanent decoder support, endpoint equality, local certificates, route endpoints, and scalar fidelity.

## 1. How the target was reached

### CST-EXP-00 — type discipline

The project separated structural transport (`S-T`), target structural realization (`S-R`), lineage (`S-L`), autonomy (`A`), recognition (`R`), ontology (`O`), and methodological claims (`M`). A1, A2-P, certificate soundness, recognition, and personal identity were registered as separate assumptions rather than hidden implications.

### CST-EXP-01 — complete corpus extraction

All sixty manuscript files received explicit dispositions. The corpus supplied:

- the C1–C8 target contract and T14 predictive-lineage machinery;
- current/predictive separation and hiddenness controls;
- fixed-support promotion, exactification, event-package, recombination, and route machinery;
- local/global obstruction, temporal closure, viability, agency, and object-persistence laws;
- a QEC logical-object engineering analogue.

It did **not** supply one heterogeneous theorem jointly establishing integrated target realization, source lineage, and autonomy. The consciousness manuscript explicitly leaves A2 without a carrier-transport theorem and does not exhibit one integrated full C-package instance with certificate soundness.

### CST-EXP-02 — neutral scenario semantics

Thirty-five scenarios were typed across ten protocol axes. Operational copying, overlap, record provenance, deletion, recovery, or causal edges were kept separate from lineage. Every candidate was required to return independent S-T/S-R/S-L/A/R results.

### CST-EXP-03 — plural candidate generation

Ten candidate schemas were generated from quotient, process, closure, viability, error-correcting, route/recombination, temporal-credit, approximation, and ancestry perspectives. The design space repeatedly factored into carrier individuation, transported/related object, bridge, invariant, target realization, lineage, autonomy, recognition, and ontology.

### CST-EXP-04 — adversarial narrowing

Public shadows, exact duplication, route holonomy, local/global obstruction, recombination, decoder dependence, temporal gaps, viability boundaries, bridge composition, and independent twins were used to attack every candidate. Three families survived:

- SF-01 integrated autonomous target realization;
- SF-02 causal-overlap process lineage;
- SF-03 relation-valued predictive ancestry.

### CST-EXP-05 — theorem/toy reconnaissance

Ten exact finite model families, twenty-four theorem/no-go prospectuses, and ten toy-program contracts showed that all three families were landable in elementary finite mathematics. The key risk was circular definitions, not model size.

### CST-EXP-06 — target freeze

Standalone families were retained as modules, but the final constructive target had to jointly represent S-R, S-L, and A. The paired finalists were compared under hard gates and weighted soft criteria. Their totals were:

- FIACH `{totals[PRIMARY_ID]:.2f}/100`;
- IAPS `{totals[FALLBACK_ID]:.2f}/100`;
- dual-lineage unification `{totals['FT-03']:.2f}/100`;
- no-go kernel `{totals[TERMINAL_ID]:.2f}/100`, disqualified as a positive target.

FIACH was selected because it is the narrowest nontrivial joint target and gives “move” a process-sensitive finite meaning. IAPS was frozen because it handles the exact destructive-copy cases FIACH intentionally excludes.

## 2. Frozen primary in one statement

For distinct finite carriers `S` and `T`, an episode establishes `FIACH(S,T)` when independently checked clause witnesses glue into one target-owned integrated package, a no-gap mixed-support causal corridor connects source and target histories with at least one nonredundant joint update, and the target package remains inside a target-owned controlled invariant region after source/bridge withdrawal.

The relation is branch-valued under valid fission and makes no numerical-identity claim.

## 3. Frozen fallback in one statement

For distinct finite carriers `S` and `T`, an episode establishes `IAPS(S,T)` when a least no-ex-nihilo relation generated from operational provenance and predictive compatibility relates the source to the target, independently checked clause witnesses glue into one target-owned integrated package, and that package remains autonomous after withdrawal.

A destructive reconstruction may pass; an independent twin does not; exact copies may all be successors.

## 4. Scenario-battery status

The final expected-verdict ledger contains seventy rows: thirty-five scenarios for each target. It preserves typed underdetermination rather than inventing missing package or autonomy witnesses.

- FIACH joint statuses: `{dict(primary_counts)}`.
- IAPS joint statuses: `{dict(fallback_counts)}`.

These are criterion-relative expected outputs derived from the frozen TS-02 package/autonomy lane and TS-03 or TS-10 lineage lane. They are not empirical findings. The most important exact disagreement is destructive reconstruction: FIACH has no live lineage edge; IAPS may have a source-derived successor edge.

## 5. Core theorem landing

The primary later project should attempt:

1. acyclic local-witness gluing;
2. staged target-package assembly with ownership;
3. live-corridor composition;
4. post-withdrawal controlled invariance;
5. soundness of the combined FIACH certificate;
6. FIACH composition across matched intermediate frontiers;
7. branch-valued fission and symmetry nonselection;
8. detached-copy, decoder-shadow, local/global, route, and public-shadow countermodels.

If the corridor engine fails its noncircularity or composition gate, the fallback project should attempt predictive quotient descent, least operational ancestry, independent-twin exclusion, fission/fusion, and the integrated IAPS target theorem.

## 6. Exact finite toys

No full Six Birds simulation is required. The minimal witness suite combines:

- a four-stage mixed-support corridor;
- a finite eight-clause package surrogate with explicit overlap/gluing records;
- a target-owned viability/repair invariant region;
- a destructive source-record-target graph and disconnected twin;
- a symmetric two-target fork;
- an XOR recombination obstruction;
- a route square with holonomy;
- a decoder-supported shadow;
- a vector-residual hard-gate counterfeit.

The tools should emit explicit JSON/CSV certificates that Lean can check.

## 7. Corpus grounding

| Asset | Source line(s) | Role in the frozen target | Retained warning |
|---|---|---|---|
| `A-CT-01` | P05 consciousness architecture | finite C-shaped target contract and claim separation | no integrated full instance, soundness theorem, or A2 transport theorem |
| `A-PQ-01/A-PQ-02` | P05, P12, P13, P14, P30 | predictive signatures, future sufficiency, fallback bridge | predictive equivalence does not imply the full package |
| `A-PR-01/A-EX-01` | P03, P08, P16, P23 | promotion/exactification motifs for target clause transport | strongest results are fixed-support and need heterogeneous retyping |
| `A-EV-01/A-LG-01` | P09, P17, P30, P39 | typed event records and local/global gluing | local/pairwise acceptance does not yield a global package |
| `A-AG-01/A-VI-01` | P05, P22, P32, P57 | target ownership, viability, maintenance, withdrawal autonomy | autonomy is intervention- and boundary-relative |
| `A-TM-01/A-CF-01/A-HO-01` | P05, P14, P30, P35, P50, P53 | clocks, route memory, critical pairs, confluence | endpoint equality does not erase route history |
| `A-RE-01/A-OP-01` | P05, P18, P24, P30 | fission, fusion, recombination, relation-valued persistence | branchwise equality and identity are distinct |
| `A-QEC-01` | P07 | engineering pattern for logical object + recovery + audit | analogy only; no conscious or personal persistence result |
| `A-FS-01/A-NO-01` | P30, P33, P52 | finite semantics and no-smuggling discipline | packaging/report descent is not identity or consciousness |

## 8. Assumption ladder

### Unconditional finite mathematics

Finite graphs, relations, partitions, join trees, controlled invariant sets, automorphisms, and explicit countermodels require no A1, A2-P, recognition, or personal-identity premise.

### Structural target premises

Carrier distinctness, admissible bridge data, a stipulated/checkable source package surrogate, clause preservation, global gluing, a declared lineage criterion, target boundary, withdrawal operation, and disturbance class.

### Interpretation premises not spent

Certificate soundness, empirical recognition, A1, A2-P, and H-IDENTITY-O remain outside the theorem. No higher rung can rescue a failed finite structural antecedent.

## 9. Falsifiers and switch rules

The primary is abandoned or downgraded if its corridor definition is verdict-loaded, detached reconstruction passes it, valid corridors fail composition, no noncircular integrated package witness exists, or autonomy depends on post hoc boundary enlargement.

The fallback is abandoned or downgraded if its seed is an ancestry oracle, independent twins enter, fission/fusion universalizes the relation, or predictive ancestry is used as a substitute for package realization.

If both fail, the project lands the finite no-go kernel and states precisely which information classes and criterion families are insufficient.

## 10. What the exploration now recommends

Attempt **FIACH first**, with no-go microtheorems and exact countermodels built before the combined positive theorem. Keep the target relation branch-valued and route-indexed unless stronger theorems justify uniqueness or flatness. Reuse the package/autonomy layer in **IAPS** only if the live-corridor lineage engine fails for a registered scientific reason. Do not run a full Six Birds simulation before these finite definitions and countermodels have survived formalization.

## 11. What remains unanswered

Even a complete later proof would not answer whether actual consciousness is present in the source or target, whether phenomenal experience survives, whether the target is the same person, whether A2 is true, or how real instruments recognize the structural predicates. The preparatory program has answered the narrower question it was designed to answer: **what exact theorem-and-toy target is worth attempting next, which counterexamples and countermodels it must survive, and what must it not claim?**
"""


def handoff_md() -> str:
    return f"""
# Later Theorem-and-Toy Landing Handoff

**This document defines the next project's boundary. It is not a detailed implementation plan.**

## 1. Authorized target order

1. Attempt `{PRIMARY_ID}` / FIACH.
2. Carry `{TERMINAL_ID}` no-go controls from the first commit; do not postpone them until after a positive result.
3. Switch to `{FALLBACK_ID}` / IAPS only when a primary kill criterion is documented.
4. Defer the dual-lineage unification theorem until one lineage engine has landed.

No full Six Birds simulation is needed or authorized for the first landing.

## 2. Theorem statements to attempt

### Required primary core

- `PTH-01` acyclic local-witness gluing.
- `PTH-03` live-corridor composition.
- `PTH-04` post-withdrawal controlled invariance.
- `PTH-05` FIACH certificate soundness with S-R/S-L/A as separate fields.
- `PTH-07` relation-valued fission and symmetry nonselection.
- At least three exact companion boundaries: detached-copy separation, decoder-support autonomy failure, and local/global obstruction.

### Primary strengthening after the core

- `PTH-06` composition of two full autonomous handoffs.
- route-memory/confluence strengthening;
- exact vector-defect extension only after the exact theorem is stable.

### Fallback core after a registered switch

- finite predictive bridge descent;
- least operational ancestry and leastness;
- independent-twin exclusion;
- integrated IAPS target theorem;
- fission/fusion and symmetry boundaries.

## 3. Toy programs to build

The minimum suite is:

```text
package_gluing_auditor
corridor_and_branch_checker
withdrawal_autonomy_checker
bridge_composition_checker
bounded_counterexample_enumerator
```

The fallback additionally needs:

```text
predictive_partition_calculator
ancestry_closure_and_derivation_checker
recombination_conflict_tester
```

Every program must export canonical finite structures and certificates. The trusted Lean proof layer checks those certificates; Python generation is not a proof oracle.

## 4. Proof/program order

1. Formalize tiny negative witnesses first: symmetry, detached endpoints, decoder collapse, and cyclic gluing obstruction.
2. Freeze independent package, corridor, boundary, and autonomy definitions before searching for a positive example.
3. Build the finite checkers and reproduce all registered positive/negative witnesses.
4. Prove the generic gluing, corridor-composition, and controlled-invariance lemmas.
5. Prove the combined certificate theorem only after one-obligation-removed counterexamples are stable.
6. Attempt full handoff composition and approximate extensions last.

This ordering is a circularity control: counterexamples and definitions exist before the main positive theorem is optimized.

## 5. Controls required before any positive claim

- public-perfect hidden mismatch;
- endpoint-identical detached reconstruction;
- independent package-equivalent twin;
- exact symmetric fork;
- external decoder/scheduler/repair shadow;
- local certificates with no global witness;
- branchwise equality with recombination failure;
- route holonomy/direct-versus-factored mismatch;
- scalar residual passing despite a hard local failure;
- same-carrier representation change as a negative cross-carrier control.

## 6. Switch conditions

Switch from FIACH to IAPS when a documented result shows that:

- no noncircular mixed-process/nonredundancy definition survives bounded counterexample search; or
- the live corridor is not closed under composition under any scientifically acceptable frontier rule; or
- destructive source-derived reconstruction must remain within scope and cannot be represented honestly by FIACH.

Do **not** switch merely because an FIACH proof is difficult.

Switch from IAPS to the no-go-only landing when:

- operational seeds encode successorhood;
- independent twins or arbitrary record paths enter the relation;
- repeated closure universalizes ancestry;
- target package/autonomy remains unavailable independently.

## 7. Completion conditions for the later project

A successful landing contains:

- exact definitions with no verdict-loaded fields;
- at least one finite positive witness and all required counterfeits;
- machine-checkable proofs or explicit checked countermodels;
- reproducible certificate-producing toys;
- an assumption/claim-tier statement;
- explicit copy/fission/fusion/gap/route verdicts;
- a final statement of what consciousness and identity claims do not follow.

The later project may stop at the no-go suite if the constructive targets fail honestly. That is a valid scientific outcome.
"""


def update_ledgers(root: Path) -> None:
    # CSV decision log
    p = root / "ledgers/decision_log.csv"
    with p.open(encoding="utf-8") as fh:
        existing = list(csv.DictReader(fh))
        fields = list(existing[0])
    id_field = "decision_id" if "decision_id" in fields else "id"
    existing = [r for r in existing if not r[id_field].startswith("D06-")]
    for did, topic, decision, rationale in DECISIONS:
        existing.append({
            id_field: did, "date": DATE, "topic": topic, "decision": decision,
            "rationale": rationale, "status": "active",
        })
    csv_write(p, fields, existing)

    # Markdown decision log: preserve earlier sections, replace phase-06 tail.
    p = root / "ledgers/DECISION_LOG.md"
    txt = p.read_text(encoding="utf-8")
    marker = "\n## CST-EXP-06 — synthesis and target freeze\n"
    txt = txt.split(marker)[0].rstrip()
    rows = "\n".join(f"| {did} | `{topic}` | {decision} | {rationale} | active |" for did, topic, decision, rationale in DECISIONS)
    txt += marker + "\n| ID | Topic | Decision | Rationale | Status |\n|---|---|---|---|---|\n" + rows
    txt += "\n\n## Final exploration boundary\n\nCST-EXP-06 freezes conjecture-grade primary and fallback targets and authorizes only a later finite theorem-and-toy project. No theorem, program, simulation, empirical bridge, consciousness result, survival result, numerical-identity result, or A2 carrier-invariance result is contained in this repository state.\n"
    write(p, txt)

    # Rejected defaults markdown.
    p = root / "ledgers/REJECTED_DEFAULTS.md"
    txt = p.read_text(encoding="utf-8")
    marker = "\n## Additional defaults rejected by CST-EXP-06\n"
    txt = txt.split(marker)[0].rstrip()
    rows = "\n".join(f"| {rid} | {default} | Rejected as a default. | {reason} |" for rid, default, reason in REJECTED_DEFAULTS)
    txt += marker + "\n| ID | Premature default | Ruling | Reason |\n|---|---|---|---|\n" + rows + "\n"
    write(p, txt)

    # Unresolved questions markdown.
    p = root / "ledgers/UNRESOLVED_QUESTIONS.md"
    txt = p.read_text(encoding="utf-8")
    marker = "\n## Implementation questions retained after CST-EXP-06\n"
    txt = txt.split(marker)[0].rstrip()
    txt += marker + "\n\nThese questions no longer block target selection; they are falsification and formalization questions for the later landing.\n\n"
    txt += "\n".join(f"{n}. {q}" for n, q in OPEN_QUESTIONS) + "\n"
    write(p, txt)


def update_root_docs(root: Path, totals: dict[str, float], scenario_rows: list[dict[str, object]]) -> None:
    write(root / "README.md", f"""
# CST Exploration Repository

**Project:** consciousness across substrates in Six Birds Theory  
**Repository code:** `CST-EXP`  
**Current completed phase:** `CST-EXP-06`  
**Status:** preparatory exploration complete; primary and fallback theorem/toy targets frozen. No theorem or program is implemented.

## Frozen target

- **Primary — `{PRIMARY_ID}` / FIACH:** Finite Integrated Autonomous Causal Handoff. It joins an independently audited target package, a live no-gap mixed-support process lineage relation, and post-withdrawal target autonomy.
- **Fallback — `{FALLBACK_ID}` / IAPS:** Integrated Autonomous Predictive Successorship. It joins a least operational predictive-ancestry relation to the same target package and autonomy gates, permitting source-derived destructive reconstruction without asserting unique identity.
- **Mandatory companion — `{TERMINAL_ID}`:** finite no-go/underdetermination kernel.

## Start here

1. `synthesis/EXPLORATION_DOSSIER.md`
2. `synthesis/PRIMARY_TARGET_SPECIFICATION.md`
3. `synthesis/FALLBACK_TARGET_SPECIFICATION.md`
4. `synthesis/COPY_VS_CONTINUATION_AUDIT.md`
5. `synthesis/FINALIST_COMPARISON.md`
6. `synthesis/LATER_LANDING_HANDOFF.md`
7. `synthesis/TARGET_SELECTION_SCORECARD.csv`
8. `synthesis/TARGET_SCENARIO_VERDICTS.csv`

## Phase record

- CST-EXP-00: charter and typing discipline.
- CST-EXP-01: complete sixty-paper extraction and asset atlas.
- CST-EXP-02: neutral semantics and thirty-five-scenario battery.
- CST-EXP-03: ten complete candidate schemas.
- CST-EXP-04: adversarial stress, no-go mining, and three survivor families.
- CST-EXP-05: exact finite theorem/toy reconnaissance.
- CST-EXP-06: finalist comparison, copy audit, primary/fallback freeze, and later landing brief.

## Boundary

FIACH and IAPS are structural precursor targets. Neither is a theorem of consciousness transfer, personal survival, numerical identity, certificate soundness, A1, or A2-P. Recognition remains separately assumed. A full Six Birds simulation is not required for the next project.

## Rebuild and validation

```bash
scripts/rebuild_exp06.sh
python scripts/validate_exp06.py
python scripts/verify_exp06_rebuild.py
sha256sum -c manifests/SHA256SUMS
```
""")
    write(root / "STATE.md", f"""
# Repository State

- **Project:** CST-EXP
- **State version:** {STATE_VERSION}
- **State date:** {DATE}
- **Completed:** CST-EXP-00 through CST-EXP-06
- **Preparatory program:** complete
- **Primary target:** {PRIMARY_ID} / FIACH
- **Fallback target:** {FALLBACK_ID} / IAPS
- **Companion/terminal fallback:** {TERMINAL_ID}
- **Science status:** conjecture-grade target specifications and exact witness contracts; no theorem proved
- **Formalization status:** later Lean kernel surfaces frozen; no Lean code written
- **Toy-program status:** later program contracts frozen; no toy implemented
- **Simulation status:** no full Six Birds simulation required or authorized for the first landing
- **Empirical status:** recognition remains separately assumed
- **Ontological status:** no consciousness, survival, numerical-identity, certificate-soundness, A1, or A2-P conclusion

## Final rulings

1. A final constructive target must jointly but separately represent S-R, S-L, and A.
2. FIACH is primary because it gives live movement a process-sensitive finite criterion and rejects detached exact copying.
3. IAPS is fallback because it handles source-derived destructive reconstruction relation-valuedly.
4. Symmetric fission never yields an invariant unique continuer without an additional asymmetry.
5. The no-go kernel is mandatory under either target.
6. Exact finite results precede approximation.
7. Python may generate certificates; Lean or another trusted kernel must check them.
8. The repository ends exploration and hands off to a separate theorem-and-toy implementation project.
""")
    write(root / "STATUS.md", f"""
# Repository Status

**Status date:** {DATE}  
**Completed phase:** CST-EXP-06  
**Exit gate:** target freeze complete; validation performed by `scripts/validate_exp06.py`  
**Next authorized work:** separate finite theorem-and-toy landing project  
**Implementation inside this phase:** none

## Landed

- auditable hard-gate and weighted finalist comparison;
- primary FIACH target specification;
- fallback IAPS target specification;
- final copy-versus-continuation audit;
- self-contained exploration dossier;
- later theorem/toy landing handoff;
- frozen theorem-family and witness-suite ledgers;
- seventy target-scenario expected-verdict records;
- explicit primary/fallback/terminal switch rules.

## Not landed

No theorem/no-go proof, Lean development, Python toy, full simulation, empirical recognition protocol, consciousness result, survival result, numerical-identity result, or formal A2 carrier-invariance theorem.
""")

    new_change = f"""
## CST-EXP-06 — {DATE}

- Compared standalone and paired finalist architectures under ten hard gates and twelve weighted soft criteria.
- Froze `{PRIMARY_ID}` FIACH as the primary target and `{FALLBACK_ID}` IAPS as the fallback.
- Retained `{TERMINAL_ID}` as mandatory companion and terminal fallback.
- Added exact theorem-family, witness-suite, scenario-verdict, copy-audit, and later-handoff assets.
- Closed the preparatory exploration without proving a theorem or implementing a toy.
"""
    p = root / "CHANGELOG.md"
    txt = p.read_text(encoding="utf-8")
    marker = f"\n## CST-EXP-06 — {DATE}\n"
    txt = txt.split(marker)[0].rstrip() + "\n" + new_change
    write(p, txt)
    write(root / "changelog/CST-EXP-06.md", f"""
# CST-EXP-06 Change Record

**Date:** {DATE}

## Added

- final target-selection scorecard and qualitative comparison;
- FIACH primary specification and IAPS fallback specification;
- copy-versus-continuation audit;
- self-contained exploration dossier and later landing handoff;
- frozen theorem and witness registries;
- complete primary/fallback expected verdicts over all thirty-five scenarios;
- deterministic build, validation, rebuild, manifest, and restore surfaces.

## Frozen rulings

- FIACH is the narrowest first target jointly covering target realization, live structural lineage, and autonomy.
- IAPS is the explicit destructive-reconstruction fallback and remains relation-valued.
- exact symmetric duplication supplies no unique selector;
- no-go controls accompany every positive theorem;
- structural results do not imply consciousness or identity.

## Not performed

No proof, Lean code, toy implementation, full simulation, empirical bridge, or ontological conclusion.
""")


def diagrams(root: Path) -> None:
    dot = r'''
digraph CST_EXP_06 {
  rankdir=LR;
  graph [fontname="Helvetica", bgcolor="white", pad="0.2", nodesep="0.45", ranksep="0.7"];
  node [shape=box, style="rounded", fontname="Helvetica", fontsize=11, margin="0.12"];
  edge [fontname="Helvetica", fontsize=9];

  pkg [label="Target package\nlocal clauses + gluing + ownership"];
  live [label="FIACH lineage\nlive mixed-support corridor"];
  anc [label="IAPS lineage\nleast operational ancestry"];
  aut [label="Autonomy\nwithdrawal + controlled invariant K"];
  primary [label="PRIMARY FT-01 / FIACH\nS-R + live S-L + A", penwidth=2];
  fallback [label="FALLBACK FT-02 / IAPS\nS-R + ancestry S-L + A", penwidth=2];
  nogo [label="MANDATORY FT-NG\nsymmetry · shadow · decoder · gluing\nroute · recombination · residual"];
  excluded [label="Excluded interpretations\nconsciousness · survival · numerical identity\ncertificate soundness · A1 · A2-P", shape=note];

  pkg -> primary;
  live -> primary;
  aut -> primary;
  pkg -> fallback;
  anc -> fallback;
  aut -> fallback;
  primary -> fallback [label="switch only under\nregistered kill criteria", style=dashed];
  nogo -> primary [label="required controls", style=dotted];
  nogo -> fallback [label="required controls", style=dotted];
  primary -> excluded [label="does not imply", style=dashed];
  fallback -> excluded [label="does not imply", style=dashed];
}
'''
    write(root / "synthesis/frozen_target_architecture.dot", dot)
    dot_bin = shutil.which("dot")
    if dot_bin:
        subprocess.run([dot_bin, "-Tsvg", str(root / "synthesis/frozen_target_architecture.dot"), "-o", str(root / "synthesis/frozen_target_architecture.svg")], check=True)
        subprocess.run([dot_bin, "-Tpng", str(root / "synthesis/frozen_target_architecture.dot"), "-o", str(root / "synthesis/frozen_target_architecture.png")], check=True)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = ap.parse_args()
    root = args.root.resolve()

    _, totals = selection_scorecard(root)
    scenario_rows = target_scenario_rows(root)
    theorem_and_witness_ledgers(root)

    write(root / "synthesis/FINALIST_COMPARISON.md", finalist_comparison_md(totals))
    write(root / "synthesis/PRIMARY_TARGET_SPECIFICATION.md", primary_spec_md())
    write(root / "synthesis/FALLBACK_TARGET_SPECIFICATION.md", fallback_spec_md())
    write(root / "synthesis/COPY_VS_CONTINUATION_AUDIT.md", copy_audit_md())
    write(root / "synthesis/EXPLORATION_DOSSIER.md", dossier_md(totals, scenario_rows))
    write(root / "synthesis/LATER_LANDING_HANDOFF.md", handoff_md())
    write(root / "synthesis/TARGET_REGISTRY.json", json.dumps(TARGET_REGISTRY, indent=2, sort_keys=True))
    write(root / "synthesis/README.md", """
# CST-EXP-06 Synthesis Assets

Read `EXPLORATION_DOSSIER.md` first. The primary and fallback target specifications, scorecard, scenario verdicts, copy audit, theorem family, witness suite, and later handoff are frozen exploration outputs. They are not proofs or implementations.
""")

    update_ledgers(root)
    update_root_docs(root, totals, scenario_rows)
    diagrams(root)

    summary = {
        "schema_version": "1.0",
        "project": "CST-EXP",
        "phase": PHASE,
        "state_version": STATE_VERSION,
        "generated_date": DATE,
        "primary_target": PRIMARY_ID,
        "fallback_target": FALLBACK_ID,
        "terminal_fallback": TERMINAL_ID,
        "counts": {
            "finalist_architectures": len(FINALISTS),
            "hard_gates": len(HARD_GATES),
            "soft_criteria": len(SOFT_CRITERIA),
            "scorecard_records": len(FINALISTS) * (len(HARD_GATES) + len(SOFT_CRITERIA) + 1),
            "target_scenario_records": len(scenario_rows),
            "primary_theorem_targets": len(PRIMARY_THEOREMS),
            "fallback_theorem_targets": len(FALLBACK_THEOREMS),
            "frozen_witnesses_controls": len(WITNESSES),
            "phase_decisions": len(DECISIONS),
            "phase_rejected_defaults": len(REJECTED_DEFAULTS),
            "retained_implementation_questions": len(OPEN_QUESTIONS),
        },
        "soft_totals": totals,
        "boundary": "No theorem or no-go is proved; no Lean or toy implementation is present; no empirical, consciousness, survival, numerical-identity, certificate-soundness, A1, or A2-P conclusion is made.",
    }
    write(root / "manifests/EXP06_ASSET_SUMMARY.json", json.dumps(summary, indent=2, sort_keys=True))
    print(f"Built CST-EXP-06 assets: {len(scenario_rows)} target-scenario rows; primary={PRIMARY_ID}; fallback={FALLBACK_ID}")


if __name__ == "__main__":
    main()
