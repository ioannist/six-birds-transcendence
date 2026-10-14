#!/usr/bin/env python3
"""Build deterministic CST-EXP-05 theorem/toy reconnaissance assets."""
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
import exp05_data as D  # noqa: E402

CSV_KW = {"newline": "", "encoding": "utf-8"}


def norm(v: Any) -> str:
    if v is None:
        return ""
    if isinstance(v, bool):
        return "true" if v else "false"
    if isinstance(v, (list, tuple, set)):
        return ";".join(str(x) for x in v)
    return str(v).replace("\r\n", "\n").replace("\r", "\n")


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    clean = "\n".join(line.rstrip() for line in text.splitlines())
    path.write_text(clean.rstrip() + "\n", encoding="utf-8")


def write_csv(path: Path, rows: list[dict[str, Any]], fields: list[str]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", **CSV_KW) as fh:
        w = csv.DictWriter(fh, fieldnames=fields, extrasaction="ignore", lineterminator="\n")
        w.writeheader()
        for row in rows:
            w.writerow({k: norm(row.get(k, "")) for k in fields})


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(**CSV_KW) as fh:
        return list(csv.DictReader(fh))


def split_ids(s: str) -> list[str]:
    return [x.strip() for x in str(s).split(";") if x.strip()]


def md(s: Any) -> str:
    return str(s).replace("|", "\\|").replace("\n", " ")


def parse_roles(s: str) -> dict[str, str]:
    out: dict[str, str] = {}
    for piece in split_ids(s):
        if "=" in piece:
            k, v = piece.split("=", 1)
            out[k.strip()] = v.strip()
    return out


def sha_text(s: str) -> str:
    return hashlib.sha256(s.encode("utf-8")).hexdigest()


def render_model_card(m: dict[str, str]) -> str:
    return f"""# {m['id']} — {m['title']}

**Status:** exact finite reconnaissance model; specified but not implemented.  
**Governing-plan slot:** {m['plan_slot']}  
**Phase:** CST-EXP-05

## Purpose

{m['purpose']}

## Exact finite signature

- **Carriers:** {m['carriers']}
- **States:** {m['states']}
- **Inputs/interventions:** {m['inputs']}
- **Transition law:** {m['transition']}
- **Interfaces/probes:** {m['interfaces']}
- **Bridge/episode data:** {m['bridge']}

## Positive witness

{m['positive_witness']}

## Exact negative or counterfeit control

{m['negative_control']}

## Required witness package

{m['expected_witnesses']}

## Controls

{m['controls']}

## Discrimination role

- **What it separates:** {m['separates']}
- **Family roles:** {m['family_roles']}
- **Theorem prospectuses:** {m['theorem_ids']}
- **Toy-program contracts:** {m['program_ids']}

## Minimality rationale

{m['minimality']}

## Formalization path

{m['formalization']}

## Kill condition

{m['kill_condition']}

## Explicit nonclaim

{m['nonclaim']}
"""


def render_program_card(p: dict[str, str]) -> str:
    return f"""# {p['id']} — {p['title']}

**Status:** later toy-program contract; no code written in CST-EXP-05.  
**Phase:** CST-EXP-05

## Purpose

{p['purpose']}

## Input types

{p['input_types']}

## Exact outputs

{p['outputs']}

## Witness and certificate format

{p['witness_format']}

## Positive and negative controls

{p['controls']}

## Expected complexity

{p['complexity']}

## Candidate/theorem falsification role

{p['falsifies']}

- **Models:** {p['models']}
- **Theorem prospectuses:** {p['theorems']}

## Lean/Python division

- **Lean kernel:** {p['lean_role']}
- **Python reconnaissance/implementation:** {p['python_role']}

## Explicit nonclaim

{p['nonclaim']}
"""


def render_theorem_card(t: dict[str, str]) -> str:
    return f"""# {t['id']} — {t['title']}

**Status:** conjecture-grade theorem prospectus; not proved.  
**Kind:** {t['kind']}  
**Families:** {t['families']}  
**Phase:** CST-EXP-05

## 1. Setup

{t['setup']}

## 2. Conjecture / candidate statement

{t['conjecture']}

## 3. Proof spine

{t['proof_spine']}

## 4. Exact finite cases

{t['finite_cases']}

## 5. Interactions

{t['interactions']}

- **Models:** {t['models']}
- **Toy programs:** {t['programs']}
- **Corpus assets:** {t['source_assets']}
- **Refines prior no-go prospect(s):** {t['refines_no_go'] or 'none'}
- **Structural assumptions:** {t['assumptions']}

## 6. Formalization reconnaissance

- **Required objects:** {t['objects']}
- **Lean core:** {t['lean_core']}
- **Python role:** {t['python_role']}
- **Tractability:** {t['tractability']}
- **Quotient/setoid risk:** {t['quotient_risk']}
- **Category-theoretic necessity:** {t['category_need']}
- **Circularity risk:** {t['circularity_risk']}
- **Unformalized external dependency:** {t['external_dependency']}

## Falsifier or downgrade condition

{t['falsifier']}

## 7. Explicit nonclaim

{t['nonclaim']}
"""


def finite_core_semantics() -> str:
    return r"""# CST-EXP-05 Finite Core Semantics

**Status:** common exact vocabulary for theorem and toy reconnaissance; not an implementation and not a final target.

## 1. Carrier systems

A finite carrier system is a tuple

```text
Sys(X) = (X, U, δ, E, L, own)
```

where `X` is a finite state type tied to one declared carrier token, `U` is a finite input/intervention type, `δ ⊆ X × U × X` is a total deterministic function or finite relation as declared, `E` is the retained environment/resource record, `L` is a family of public or audit lenses, and `own` labels dependencies by their support owner. Source and target state types remain distinct even when they are isomorphic.

`DistinctCarrier(X_S,X_T)` is fixed before any bridge verdict. A mere relabeling or gauge change on one token is not a cross-carrier episode.

## 2. Histories, current shadows, and predictive quotients

A history is a finite path in `δ`. For a finite probe family `Π` and horizon `H`, two states are predictively equivalent when every admitted probe produces the same exact trace for every admitted input word of length at most `H`. Current equivalence may use only the present lens. The finite quotient is represented initially by canonical partition blocks rather than dependent quotient types.

## 3. Package records

A finite package record is

```text
CPkg(X) = (W1,...,W8, scopes, restrictions, hard, ownership, K)
```

where each `Wi` is an independently stated finite witness relation for one C-clause surrogate, `scopes` and `restrictions` define the overlap/gluing problem, `hard` is a set of non-negotiable gates, `ownership` records every support dependency, and `K` is the package-valid/viable region. `CPkg` contains no field named consciousness, survival, same subject, successful transfer, or transcendence.

The MF-07 proxy package keeps these obligations independently falsifiable: closed object dynamics; strict/nonpublic predictive structure; target self-coordinate; interface-relative nonexposure; endogenous action credit; target-minted temporal order; joint binding; and target-owned viability/repair.

## 4. Bridges and routes

A typed bridge edge from `X_i` to `X_j` contains explicit state/history relations, input and clock maps, clause transformations, provenance edges, resource dependencies, and residuals. A route is a finite path of bridge edges. Composition is relational/function composition only when the codomain contract of one edge matches the domain contract of the next.

No operational bridge edge is a lineage edge by default. Route independence is a separate statement; nontrivial holonomy is retained rather than erased.

## 5. Two independent lineage constructions

### 5.1 Causal-overlap corridor

An overlap corridor is a finite time-indexed support sequence with no empty process state, at least one mixed source-target update in which both sides are nonredundant, a declared process signature preserved at each step, and a target takeover boundary. Its derived relation is conservative and rejects a detached destructive copy lacking the mixed/no-gap structure.

### 5.2 Predictive ancestry

Predictive ancestry is the least fixed point of a monotone operator on source-target history pairs. The operator begins from operationally defined provenance seeds and closes under declared transition, fission, fusion, and route rules. The no-ex-nihilo condition forbids a rule from introducing a target pair without a seed or an already related predecessor.

These two relations are intentionally different. Neither is called numerical identity.

## 6. Withdrawal and autonomy

`withdraw_B` removes the source, bridge translator, decoder, migration controller, external scheduler, external repair service, and any other dependency named by the episode, except resources explicitly inside the predeclared target boundary. The post-withdrawal target system is evaluated over a declared disturbance class and horizon or invariant region.

Autonomy is a property of this transformed target system. Supported behavior before withdrawal is not autonomy.

## 7. Exact approximation layer

Approximation uses an exact rational vector

```text
d(B) = (d_pred, d_bind, d_time, d_credit, d_glue, d_via, ...)
```

with coordinate semantics, local margins, hard gates, and a proved composition/drift rule. A scalar summary may be reported but cannot override a failed coordinate or gate.

## 8. Claim lanes and ceiling

The finite semantics can support structural transport (`S-T`), target package realization (`S-R`), structural lineage (`S-L`), autonomy (`A`), and finite instrument claims (`R`) as separately typed results. It does not by itself support ontology (`O`). Certificate soundness, empirical recognition, A1, A2-P, and personal-identity interpretation remain additional premises.
"""


def render_model_index() -> str:
    rows = ["# Exact Finite Model Suite", "", "All ten models are specified, not implemented. Counts and apparent simplicity are not candidate rankings.", "", "| ID | Model | Plan slot | Families separated |", "|---|---|---|---|"]
    for m in D.MODELS:
        rows.append(f"| [{m['id']}](model_cards/{m['id']}.md) | {md(m['title'])} | {md(m['plan_slot'])} | {md(m['separates'])} |")
    return "\n".join(rows)


def render_program_index() -> str:
    rows = ["# Toy-Program Prospectus Index", "", "No program is implemented in CST-EXP-05. Each entry is a typed later-build contract.", "", "| ID | Contract | Models | Theorems |", "|---|---|---|---|"]
    for p in D.PROGRAMS:
        rows.append(f"| [{p['id']}]({p['id']}.md) | {md(p['title'])} | {md(p['models'])} | {md(p['theorems'])} |")
    return "\n".join(rows)


def render_theorem_index() -> str:
    rows = ["# Theorem Prospectus Index", "", "Every item is conjecture-grade or an exact no-go prospect. None is represented as proved.", "", "| ID | Prospect | Kind | Families | Tractability |", "|---|---|---|---|---|"]
    for t in D.THEOREMS:
        rows.append(f"| [{t['id']}]({t['id']}.md) | {md(t['title'])} | {md(t['kind'])} | {md(t['families'])} | {md(t['tractability'])} |")
    return "\n".join(rows)


def render_assumption_ladder() -> str:
    lines = [
        "# CST-EXP-05 Assumption Ladder",
        "",
        "The ladder prevents structural mathematics, target realization, lineage, autonomy, recognition, ontology, and personal identity from doing one another's work. Refusing a higher rung never invalidates a lower structural theorem; it removes only the interpretation licensed by that rung.",
        "",
    ]
    ftitle = {f["family_id"]: f["title"] for f in D.FAMILY_FEASIBILITY}
    for fid, entries in D.ASSUMPTION_LADDERS.items():
        lines += [f"## {fid} — {ftitle[fid]}", "", "| Rung | Question | Exact role | Assumption IDs |", "|---:|---|---|---|"]
        for n, title, text, aids in entries:
            lines.append(f"| {n} | {md(title)} | {md(text)} | `{md(aids)}` |")
        lines += ["", "**Claim ceiling:** " + next(f["nonclaim"] for f in D.FAMILY_FEASIBILITY if f["family_id"] == fid), ""]
    lines += [
        "## Shared no-go kernel",
        "",
        "The finite symmetry, public-shadow, parity, decoder-dependence, holonomy, scalar-residual, and local/global counterexamples do not require A1, A2-P, certificate soundness, empirical recognition, or H-IDENTITY-O. Those assumptions cannot rescue a failed antecedent or erase a finite countermodel.",
    ]
    return "\n".join(lines)


def render_tractability() -> str:
    bands = Counter(t["tractability"] for t in D.THEOREMS)
    lines = [
        "# CST-EXP-05 Formalization Tractability",
        "",
        "## Overall judgment",
        "",
        "All first-landing prospects admit elementary finite formulations. Category-theoretic language can organize later abstractions, but no theorem in the first landing requires it. Quotient complexity can be controlled by canonical finite partitions and relations before introducing quotient types or setoids. Exact rationals suffice for the approximation layer.",
        "",
        "The correct proof/program split is certificate-producing Python plus certificate-checking Lean: Python may enumerate partitions, paths, joins, invariant sets, or countermodels, while Lean proves the definitions, generic finite lemmas, and each exported witness. An enumerator is never trusted as an oracle.",
        "",
        "## Tractability bands",
        "",
    ]
    for k, v in sorted(bands.items()):
        lines.append(f"- `{k}`: {v} theorem prospectuses.")
    lines += [
        "",
        "## Definition-smuggling audit",
        "",
        "1. `DistinctCarrier` must be fixed before success is evaluated.",
        "2. `CPkg` may contain independent clause witnesses and coherence data, never a field equivalent to successful transfer or consciousness.",
        "3. The overlap corridor may use finite support/causal/nonredundancy facts, never the phrase same continuing process as a premise.",
        "4. Predictive-ancestry seeds must be operational provenance facts; the closure operator may not contain an ancestry oracle.",
        "5. Autonomy is tested after withdrawal; pre-withdrawal behavior is not an autonomy antecedent.",
        "6. Approximation metrics, margins, and hard gates must be declared before candidate comparison.",
        "",
        "## Prospect-by-prospect surface",
        "",
        "| ID | Kind | Tractability | Quotient risk | Category need | Circularity risk |",
        "|---|---|---|---|---|---|",
    ]
    for t in D.THEOREMS:
        lines.append(f"| [{t['id']}](theorem_prospectus/{t['id']}.md) | {md(t['kind'])} | {md(t['tractability'])} | {md(t['quotient_risk'])} | {md(t['category_need'])} | {md(t['circularity_risk'])} |")
    lines += [
        "",
        "## Lean/Python division by family",
        "",
        "- **SF-01:** Lean should carry finite clause records, acyclic gluing, ownership, and invariant-set theorems. Python should solve the finite witness/gluing CSPs and enumerate one-obligation-removed counterfeits.",
        "- **SF-02:** Lean should carry the overlap-corridor relation, composition, and branch laws. Python should find corridors and exhibit endpoint-equal interior-graph countermodels.",
        "- **SF-03:** Lean should carry finite monotone closure, leastness, and no-ex-nihilo exclusion. Python should compute predictive partitions, relation derivations, and fission/fusion examples.",
        "- **Common no-gos:** Prefer tiny explicit Lean examples; Python is useful only to search for minimal witnesses or verify no smaller model exists within declared bounds.",
    ]
    return "\n".join(lines)


def render_landing_bundles() -> str:
    lines = [
        "# Unranked Landing Bundles",
        "",
        "These bundles are reconnaissance products, not a primary/fallback target choice. `LB-01`, `LB-02`, and `LB-03` remain unranked. `LB-NG` is a companion boundary kernel rather than a transfer candidate.",
        "",
    ]
    for b in D.LANDING_BUNDLES:
        lines += [
            f"## {b['id']} — {b['title']}",
            "",
            f"- **Family:** {b['family']}",
            f"- **Constructive core:** {b['positive_core'] or 'none'}",
            f"- **Negative/boundary core:** {b['negative_core']}",
            f"- **Models:** {b['models']}",
            f"- **Toy contracts:** {b['programs']}",
            f"- **Lean kernel:** {b['lean_kernel']}",
            f"- **Python support:** {b['python_support']}",
            f"- **Landing shape:** {b['landing_shape']}",
            f"- **Principal risk:** {b['risk']}",
            f"- **Kill condition:** {b['kill']}",
            "",
        ]
    return "\n".join(lines)


def render_exit_gate() -> str:
    lines = [
        "# CST-EXP-05 Exit-Gate Audit",
        "",
        "## Gate",
        "",
        "A finalist must have an exact finite positive witness, an exact negative/counterfeit control, a precise conjecture-grade theorem statement, an elementary formalization path, and an explicit empirical/ontological nonclaim.",
        "",
        "| Family | Gate status | Positive witness | Negative control | Theorem core | Formal path |",
        "|---|---|---|---|---|---|",
    ]
    for f in D.FAMILY_FEASIBILITY:
        lines.append(f"| {f['family_id']} {md(f['title'])} | `{md(f['exit_gate'])}` | {md(f['positive_models'])} | {md(f['negative_models'])} | {md(f['constructive_theorems'])} | {md(f['elementary_path'])} |")
    lines += [
        "",
        "## Judgment",
        "",
        "All three survivor families are **reconnaissance-admissible**, but in different, noncomparable senses:",
        "",
        "- SF-01 has a decomposable exact package/autonomy path and the highest risk of definitional circularity or vacuity.",
        "- SF-02 has a conservative exact process-lineage path whose value depends on a defensible noncircular mixed-process predicate.",
        "- SF-03 has an exact finite least-relation path whose decisive burden is excluding independently constructed twins without turning the seed relation into an ancestry oracle.",
        "",
        "No family is selected, merged, or ranked. The fact that a theorem is shorter or a program is easier does not make its philosophical criterion correct. CST-EXP-06 must compare claim value, assumptions, and failure boundaries before freezing a target.",
        "",
        "## Boundary",
        "",
        "The gate concerns landability of structural mathematics and toy contracts only. It does not establish certificate soundness, empirical recognition, A1, A2-P, consciousness, survival, or numerical identity.",
    ]
    return "\n".join(lines)


def render_synthesis() -> str:
    return """# CST-EXP-05 — Theorem and Toy-Program Reconnaissance Synthesis

## Executive result

The survivor space is landable only after factorization. There is no credible first theorem that directly asserts migration of consciousness from carrier S to carrier T. The exact finite work divides into three unranked constructive bundles and a shared negative kernel:

1. **Integrated target package plus withdrawal autonomy (SF-01):** establish a target-local package from independently checked clause, gluing, ownership, hard-gate, and invariant-set obligations. This bundle deliberately says nothing about source lineage.
2. **Causal-overlap process lineage (SF-02):** define a conservative finite corridor relation from support, causal, nonredundancy, no-gap, and takeover data; prove composition and relation-valued fission; reject detached reconstruction under that criterion.
3. **Relation-valued predictive ancestry (SF-03):** compute a least finite ancestry relation from operational provenance and monotone closure; represent destructive reconstruction, fission, fusion, empty targets, and independent-twin exclusion without unique identity.
4. **Shared no-go kernel:** public shadows, symmetric duplication, branch marginals, external decoder support, endpoint equality, route holonomy, scalar residuals, and local certificates each fail to settle a stronger claim.

## Exact model reconnaissance

Ten finite model families now cover every governing-plan slot. They are deliberately small: Boolean product automata, four-stage support corridors, a source-record-target gap, a two-target automorphism, a three-bit hidden counterfeit, XOR recombination, a six-coordinate package with ownership and withdrawal, a square route graph, exact rational residual vectors, and a three-state viability system.

Each family has both a positive witness and a negative/counterfeit control. The model suite is not evidence that the full Six Birds consciousness architecture has been realized; it is a discrimination and theorem-design surface.

## Theorem reconnaissance

Twenty-four conjecture-grade theorem prospectuses are frozen:

- twelve constructive or constructive-boundary families;
- twelve no-go or underdetermination families;
- exact setup, statement, proof spine, finite cases, interactions, assumptions, formalization risks, falsifiers, and nonclaims for every item.

The most elementary common results are the symmetry selector impossibility, XOR recombination counterexample, decoder-withdrawal counterexample, nontrivial-loop route no-go, scalar/local-defect separation, and cyclic local/global inconsistency. The more scientifically central but riskier results are integrated package preservation, overlap-corridor composition, and the no-ex-nihilo predictive-ancestry fixed point.

This distinction is a tractability description, not a ranking of candidate families.

## Toy-program reconnaissance

Ten later program contracts cover quotient calculation, bisimulation, lineage/branch classification, composition/confluence, holonomy, recombination, package/gluing audit, withdrawal/autonomy, residuals/blind spots, and finite counterexample enumeration. Every contract declares exact inputs and outputs, witness format, controls, complexity, a falsification role, and a Lean/Python division.

No code was written. The preferred eventual architecture is untrusted enumeration plus checked certificates: Python searches and exports; Lean checks definitions, generic lemmas, and explicit witnesses.

## Formalization judgment

Elementary finite mathematics suffices for every first landing. Category theory is explanatory rather than necessary. Quotient/setoid debt is avoidable initially through canonical partition blocks. Exact rationals avoid floating-point ambiguity. The principal danger is not mathematical size but circular definitions:

- a package predicate that already says the handoff succeeded;
- a process invariant that already means same continuing process;
- an ancestry seed that already means successor;
- a target boundary or metric chosen after seeing the desired verdict.

The formalization surface explicitly audits these hazards.

## Assumption judgment

Structural mathematics, target realization, lineage, autonomy, recognition, certificate soundness, A1, A2-P, and personal identity form an eight-rung ladder. No higher rung is needed to prove the finite structural/no-go statements, and no higher rung can repair a failed structural antecedent.

A2-P is not a bridge theorem. Where cross-carrier preservation is needed, the narrow replacement is object- and bridge-specific `H-XCI`, which must itself be proved or stated as a structural hypothesis.

## Exit-gate judgment

PASS. All three survivor families admit the required exact positive witness, exact negative control, precise conjecture-grade theorem bundle, elementary formalization path, falsifiers, and nonclaims. They remain unranked and no final target is frozen. CST-EXP-06 must choose the narrowest defensible primary target and fallback only after comparing these bundles and running the final copy-versus-continuation audit.
"""


def render_readme() -> str:
    return """# CST-EXP-05 Feasibility Bank

This directory contains theorem and toy-program reconnaissance only.

- `FINITE_CORE_SEMANTICS.md` fixes the exact finite grammar.
- `MODEL_SUITE.md` and `model_cards/` specify ten finite discriminator families.
- `theorem_prospectus/` contains twenty-four conjecture/no-go cards; none is proved.
- `toy_program_prospectus/` contains ten later-build contracts; no code is implemented.
- `FORMALIZATION_TRACTABILITY.md` records the Lean/Python split and circularity risks.
- `ASSUMPTION_LADDER.md` prices structural, recognition, and ontological premises separately.
- `LANDING_BUNDLES.md` packages the three unranked constructive paths and common no-go kernel.
- `EXIT_GATE_AUDIT.md` records phase admission without selecting a final target.
- `RECONNAISSANCE_SYNTHESIS.md` is the phase synthesis.

This bank does not establish consciousness, personal survival, numerical identity, or a carrier-invariance theorem.
"""


def build_ledgers(root: Path) -> dict[str, list[dict[str, str]]]:
    family_map = {f["family_id"]: f for f in D.FAMILY_FEASIBILITY}
    model_rows = []
    discrimination = []
    crosswalk = []
    for m in D.MODELS:
        model_rows.append({**m, "exact_finite": "true", "implementation_status": "specified_not_implemented", "phase": D.PHASE})
        roles = parse_roles(m["family_roles"])
        for fid, f in family_map.items():
            pos = m["id"] in split_ids(f["positive_models"])
            neg = m["id"] in split_ids(f["negative_models"])
            discrimination.append({
                "model_id": m["id"], "model_title": m["title"], "family_id": fid, "family_title": f["title"],
                "role": roles.get(fid, "not_primary_but_available_control"),
                "positive_exit_gate_witness": pos, "negative_exit_gate_control": neg,
                "positive_witness": m["positive_witness"], "negative_control": m["negative_control"],
                "separating_question": m["purpose"], "theorem_ids": m["theorem_ids"], "program_ids": m["program_ids"],
                "exact_finite": True, "not_a_ranking": True, "phase": D.PHASE,
            })
        for tid in split_ids(m["theorem_ids"]):
            for pid in split_ids(m["program_ids"]):
                crosswalk.append({"model_id": m["id"], "theorem_id": tid, "program_id": pid, "relation": "model_witness_or_control_for_theorem_checked_by_program", "phase": D.PHASE})

    program_rows = [{**p, "implementation_status": "contract_only_no_code", "phase": D.PHASE} for p in D.PROGRAMS]
    theorem_rows = [{**t, "status": "conjecture_grade_not_proved", "phase": D.PHASE, "not_a_ranking": "true"} for t in D.THEOREMS]

    surfaces = []
    for t in D.THEOREMS:
        base = {
            "theorem_id": t["id"], "theorem_title": t["title"], "families": t["families"],
            "tractability": t["tractability"], "quotient_risk": t["quotient_risk"], "category_need": t["category_need"],
            "circularity_risk": t["circularity_risk"], "phase": D.PHASE, "implementation_status": "planned_only",
        }
        surfaces.extend([
            {**base, "surface_id": f"FS-{t['id']}-DEF", "surface_kind": "definition", "object_or_statement": t["objects"], "lean_role": "Define the finite objects and decidability/typing conditions.", "python_role": "Serialize canonical finite instances.", "acceptance_test": "Definitions contain no consciousness, survival, same-subject, or successful-transfer oracle."},
            {**base, "surface_id": f"FS-{t['id']}-STM", "surface_kind": "statement", "object_or_statement": t["conjecture"], "lean_role": t["lean_core"], "python_role": "No proof authority; may emit checked antecedent data.", "acceptance_test": "The theorem statement is well typed, finite, and marked conjecture-grade until proved."},
            {**base, "surface_id": f"FS-{t['id']}-PRF", "surface_kind": "proof_spine", "object_or_statement": t["proof_spine"], "lean_role": "Formal proof or explicit countermodel in the kernel.", "python_role": t["python_role"], "acceptance_test": "Every imported lemma and structural assumption is named; no empirical or ontological premise appears in the proof path."},
            {**base, "surface_id": f"FS-{t['id']}-WIT", "surface_kind": "finite_witness", "object_or_statement": t["finite_cases"], "lean_role": "Check exported witness tables or construct the example directly.", "python_role": "Enumerate or minimize finite witnesses using " + t["programs"], "acceptance_test": "At least one positive or negative exact finite case resolves and has a reproducible certificate."},
        ])

    ladder_rows = []
    for fid, entries in D.ASSUMPTION_LADDERS.items():
        for n, title, text, aids in entries:
            ladder_rows.append({"family_id": fid, "rung": n, "rung_title": title, "role": text, "assumption_ids": aids, "phase": D.PHASE})

    feasibility_rows = [{**f, "unranked": "true", "phase": D.PHASE} for f in D.FAMILY_FEASIBILITY]
    bundle_rows = [{**b, "unranked": "true", "phase": D.PHASE} for b in D.LANDING_BUNDLES]
    ng_map = []
    for t in D.THEOREMS:
        for ng in split_ids(t["refines_no_go"]):
            ng_map.append({"theorem_id": t["id"], "theorem_title": t["title"], "prior_no_go_id": ng, "refinement_role": "exact finite theorem prospectus or boundary refinement", "status": "not_proved", "phase": D.PHASE})
    return {
        "models": model_rows,
        "discrimination": discrimination,
        "programs": program_rows,
        "theorems": theorem_rows,
        "surfaces": surfaces,
        "ladders": ladder_rows,
        "feasibility": feasibility_rows,
        "bundles": bundle_rows,
        "crosswalk": crosswalk,
        "ng_map": ng_map,
    }


def render_diagram(root: Path) -> None:
    lines = [
        "digraph CST_EXP_05 {",
        "  rankdir=LR;",
        "  graph [label=\"CST-EXP-05 unranked landing architecture\", labelloc=t];",
        "  node [shape=box];",
    ]
    for f in D.FAMILY_FEASIBILITY:
        lines.append(f'  "{f["family_id"]}" [shape=oval,label="{f["family_id"]}\\n{f["title"]}"];')
    for b in D.LANDING_BUNDLES:
        lines.append(f'  "{b["id"]}" [shape=diamond,label="{b["id"]}\\n{b["title"]}"];')
        if b["family"] != "COMMON":
            lines.append(f'  "{b["family"]}" -> "{b["id"]}" [label="reconnaissance bundle"];')
    for m in D.MODELS:
        lines.append(f'  "{m["id"]}" [label="{m["id"]}\\n{m["title"]}"];')
    for b in D.LANDING_BUNDLES:
        for mid in split_ids(b["models"]):
            lines.append(f'  "{mid}" -> "{b["id"]}" [style=dashed,label="witness/control"];')
    lines.append('  "LB-NG" -> "LB-01" [style=dotted,label="companion boundaries"];')
    lines.append('  "LB-NG" -> "LB-02" [style=dotted,label="companion boundaries"];')
    lines.append('  "LB-NG" -> "LB-03" [style=dotted,label="companion boundaries"];')
    lines.append("}")
    dot = root / "feasibility/landing_architecture.dot"
    write_text(dot, "\n".join(lines))
    for fmt in ["svg", "png"]:
        try:
            subprocess.run(["dot", f"-T{fmt}", str(dot), "-o", str(root / f"feasibility/landing_architecture.{fmt}")], check=True, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
        except Exception:
            pass


def update_decisions(root: Path) -> None:
    csv_path = root / "ledgers/decision_log.csv"
    rows = read_csv(csv_path)
    rows = [r for r in rows if not r["id"].startswith("D05-")]
    additions = [
        ("D05-001", D.DATE, "finite_first_landing", "Require elementary exact finite semantics for every finalist before any abstract generalization.", "The phase must distinguish landability from attractive philosophical vocabulary.", "active"),
        ("D05-002", D.DATE, "three_unranked_bundles", "Preserve SF-01, SF-02, and SF-03 as unranked landing bundles throughout CST-EXP-05.", "Tractability and theorem length do not determine which criterion is scientifically preferable.", "active"),
        ("D05-003", D.DATE, "common_no_go_kernel", "Treat the shared no-go results as companion boundary mathematics, not as a fourth transfer candidate.", "They constrain every constructive family without answering target realization or lineage themselves.", "active"),
        ("D05-004", D.DATE, "certificate_producing_tools", "Specify Python tools as witness generators and Lean as the proof/certificate checker.", "Enumeration must not become an untrusted proof oracle.", "active"),
        ("D05-005", D.DATE, "category_optional", "Do not require category-theoretic or quotient-type machinery for the first landing when finite relations and canonical partitions suffice.", "Elementary formulations reduce formalization debt and expose hidden assumptions.", "active"),
        ("D05-006", D.DATE, "definition_smuggling_audit", "Reject package, process, ancestry, boundary, or metric definitions that encode the desired verdict.", "The principal risk is circularity rather than model size.", "active"),
        ("D05-007", D.DATE, "vector_hard_gate_approximation", "Use exact rational vectors, local margins, and hard gates for approximate claims; scalar summaries are nonauthoritative.", "A small average can hide a decisive local failure.", "active"),
        ("D05-008", D.DATE, "phase_nonimplementation", "Write theorem and toy contracts only; implement no proof, Lean development, Python toy, or Six Birds simulation.", "CST-EXP-05 is feasibility reconnaissance and target selection remains CST-EXP-06 work.", "active"),
    ]
    fields = list(rows[0].keys())
    for a in additions:
        rows.append(dict(zip(fields, a)))
    write_csv(csv_path, rows, fields)

    md_path = root / "ledgers/DECISION_LOG.md"
    text = md_path.read_text(encoding="utf-8")
    marker = "## CST-EXP-05 — theorem and toy-program reconnaissance"
    if marker in text:
        text = text.split(marker, 1)[0]
    text = text.rstrip()
    sec = ["", "", marker, "", "| ID | Topic | Decision | Rationale | Status |", "|---|---|---|---|---|"]
    for a in additions:
        sec.append(f"| {a[0]} | `{a[2]}` | {md(a[3])} | {md(a[4])} | {a[5]} |")
    write_text(md_path, text + "\n".join(sec))


def update_rejections(root: Path) -> None:
    p = root / "ledgers/REJECTED_DEFAULTS.md"
    text = p.read_text(encoding="utf-8")
    marker = "## CST-EXP-05 rejected defaults"
    if marker in text:
        text = text.split(marker, 1)[0]
    text = text.rstrip()
    rows = [
        ("RD05-01", "The easiest theorem is the preferred target", "Rejected: tractability is reported but not used as a scientific ranking."),
        ("RD05-02", "One predicate can combine realization, lineage, autonomy, and identity", "Rejected: each lane retains separate definitions, theorems, and assumptions."),
        ("RD05-03", "A full package theorem may define the package as successful handoff", "Rejected as circular; clause, gluing, ownership, and hard-gate obligations must be independently stated."),
        ("RD05-04", "A causal data edge is enough for overlap lineage", "Rejected: SF-02 requires a nonredundant mixed-support corridor and no-gap process record."),
        ("RD05-05", "An ancestry seed may simply mark the true successor", "Rejected as an ancestry oracle; seeds must be operational provenance facts."),
        ("RD05-06", "A scalar similarity score is adequate for approximate transfer", "Rejected: vector defects, local margins, and hard gates are mandatory."),
        ("RD05-07", "Endpoint equality makes bridge composition automatic", "Rejected by route-memory and holonomy controls."),
        ("RD05-08", "Local clause certificates automatically form a global target", "Rejected: gluing is a separate theorem obligation."),
        ("RD05-09", "Supported target behavior is enough for autonomy", "Rejected: the withdrawal transform and target-owned invariant region are mandatory."),
        ("RD05-10", "Python enumeration can count as a proof", "Rejected: exported finite witnesses require independent kernel checking."),
        ("RD05-11", "A2-P may be used to bypass H-XCI", "Rejected: A2-P supplies no bridge existence or preservation theorem."),
        ("RD05-12", "CST-EXP-05 may select a primary target", "Rejected: final comparative freeze belongs to CST-EXP-06."),
    ]
    sec = ["", "", marker, "", "| ID | Default | Ruling |", "|---|---|---|"]
    for rid, default, ruling in rows:
        sec.append(f"| {rid} | {md(default)} | {md(ruling)} |")
    write_text(p, text + "\n".join(sec))


def update_unresolved(root: Path) -> None:
    p = root / "ledgers/UNRESOLVED_QUESTIONS.md"
    text = p.read_text(encoding="utf-8")
    marker = "## Feasibility questions added after CST-EXP-05"
    if marker in text:
        text = text.split(marker, 1)[0]
    text = text.rstrip()
    qs = [
        "Which SF-01 clause surrogate is the narrowest faithful first target without pretending to instantiate the full empirical C1–C8 package?",
        "Can the MF-07 ownership/gluing package be reduced further while keeping every clause independently falsifiable?",
        "What nonredundancy notion for SF-02 best resists both endpoint collapse and biological-material stipulation?",
        "Should SF-02 corridor composition require a shared active frontier or only exact boundary-state/clock compatibility?",
        "Which operational provenance edges are admissible SF-03 seeds, and how should stale or adversarial records be treated?",
        "Can SF-03 fusion closure remain nonuniversal under repeated fission-fusion cycles?",
        "Which common no-go should accompany the primary target as the strongest boundary result rather than merely the easiest proof?",
        "Should CST-EXP-06 freeze a target-realization theorem plus a separate lineage theorem, or one deliberately partial theorem with the other lane left open?",
        "What target boundary rule prevents post hoc enlargement while still allowing genuinely distributed substrates?",
        "Which exact rational metric and margins are intrinsic enough for an approximate theorem rather than a model-specific convention?",
        "Can any source C-package premise be weakened from H-SOURCE-FULL to a finite clause subset without losing the project's central insight?",
        "What is the cleanest copy-versus-continuation audit for a combined SF-01+SF-02 or SF-01+SF-03 target?",
    ]
    sec = ["", "", marker, ""] + [f"{89+i}. {q}" for i, q in enumerate(qs)]
    write_text(p, text + "\n".join(sec))


def update_root_surfaces(root: Path) -> None:
    write_text(root / "STATE.md", f"""# Repository State

- **Project:** CST-EXP
- **State version:** CST-EXP-05-v1
- **State date:** {D.DATE}
- **Completed:** CST-EXP-00 through CST-EXP-05
- **Next planned phase:** CST-EXP-06
- **Science status:** three unranked structural landing bundles plus a common finite no-go kernel; no final target selected
- **Formalization status:** 24 conjecture/no-go prospectuses and 96 planned formal surfaces; none proved or implemented
- **Toy-program status:** 10 exact contracts; no program written
- **Model status:** 10 exact finite families with positive and negative controls; specified only
- **Simulation status:** no Six Birds simulation authorized or required
- **Empirical status:** recognition remains separately assumed; no empirical bridge supplied
- **Ontological status:** no unconditional consciousness, survival, numerical-identity, or A2 carrier-invariance claim

## Frozen CST-EXP-05 rulings

1. SF-01, SF-02, and SF-03 are all reconnaissance-admissible and remain unranked.
2. The first landing can use elementary finite types, relations, graphs, partitions, hypergraphs, invariant sets, and exact rationals.
3. Category theory is optional explanatory language, not a first-landing dependency.
4. Python may generate witnesses; Lean or another trusted proof layer must check exported certificates.
5. Package, process, ancestry, boundary, and metric definitions are rejected if they encode the desired verdict.
6. Approximation uses typed vector defects and hard gates.
7. The shared no-go kernel is a companion result bank, not a fourth transfer theory.
8. Target selection, primary/fallback freeze, and the final copy-versus-continuation audit remain CST-EXP-06 work.
""")
    write_text(root / "STATUS.md", f"""# Repository Status

**Status date:** {D.DATE}  
**Completed phase:** CST-EXP-05  
**Exit gate:** pending/finalized by `scripts/validate_exp05.py`  
**Next authorized phase:** CST-EXP-06 — synthesis, target freeze, and landing brief  
**Implementation authorization:** none

## Landed

- 10 exact finite model cards covering every governing-plan model slot.
- 30 model × survivor-family discrimination records.
- 24 conjecture/no-go theorem prospectuses in six-part form.
- 10 typed later toy-program contracts.
- 96 planned formalization surfaces with Lean/Python split and circularity audits.
- 24 family-assumption ladder records.
- 3 unranked constructive landing bundles plus 1 shared no-go kernel.
- Formalization tractability, finite core semantics, synthesis, and exit-gate audits.

## Not landed

No final target, primary/fallback freeze, theorem proof, no-go proof, Lean code, Python toy, full simulation, empirical recognition protocol, consciousness result, survival result, or personal-identity verdict.
""")

    readme = root / "README.md"
    text = readme.read_text(encoding="utf-8")
    # Correct stale header without rewriting historical phase sections.
    text = re.sub(r"\*\*Current completed phase:\*\* `CST-EXP-\d+`", "**Current completed phase:** `CST-EXP-05`", text)
    text = re.sub(r"\*\*Status:\*\*.*", "**Status:** theorem/toy reconnaissance complete; three unranked finite landing bundles and a shared no-go kernel are specified. No target, proof, program, empirical bridge, or ontological conclusion has been selected.", text, count=1)
    marker = "## CST-EXP-05 feasibility layer"
    if marker in text:
        text = text.split(marker, 1)[0].rstrip()
    sec = f"""

{marker}

CST-EXP-05 specifies 10 exact finite model families, 24 conjecture/no-go theorem prospectuses, 10 later toy-program contracts, 96 formalization surfaces, and an eight-rung assumption ladder. The phase preserves three unranked landing bundles:

- `LB-01` — integrated target package plus withdrawal autonomy;
- `LB-02` — finite causal-overlap process lineage;
- `LB-03` — least relation-valued predictive ancestry.

`LB-NG` is a shared finite no-go kernel, not a fourth transfer candidate. See `feasibility/RECONNAISSANCE_SYNTHESIS.md` and `feasibility/EXIT_GATE_AUDIT.md`.
"""
    write_text(readme, text.rstrip() + sec)

    changelog = root / "CHANGELOG.md"
    text = changelog.read_text(encoding="utf-8")
    marker = "## CST-EXP-05"
    if marker in text:
        text = text.split(marker, 1)[0].rstrip()
    sec = f"""

{marker} — {D.DATE}

- Added 10 exact finite model specifications with positive witnesses and counterfeit controls.
- Added 24 conjecture/no-go theorem prospectuses and 10 later toy-program contracts.
- Added 96 planned formalization surfaces and a certificate-producing Python / certificate-checking Lean split.
- Added the finite core semantics, formalization tractability audit, eight-rung family assumption ladders, and exit-gate audit.
- Preserved SF-01, SF-02, and SF-03 as unranked landing bundles and isolated a shared no-go kernel.
- Did not select a target, prove a theorem, write code, or make an empirical or ontological claim.
"""
    write_text(changelog, text.rstrip() + sec)

    write_text(root / "changelog/CST-EXP-05.md", f"""# CST-EXP-05 Change Record

**Date:** {D.DATE}

The phase added exact finite theorem/toy reconnaissance while preserving the CST-EXP-04 survivor architecture. It specified ten model families, twenty-four conjecture/no-go prospectuses, ten program contracts, ninety-six formal surfaces, assumption ladders, and four unranked landing bundles including the common no-go kernel.

No proof, code, simulation, empirical bridge, final target, or ontological conclusion was added.
""")


def build(root: Path) -> None:
    root = root.resolve()
    # Directories and cards.
    write_text(root / "feasibility/README.md", render_readme())
    write_text(root / "feasibility/FINITE_CORE_SEMANTICS.md", finite_core_semantics())
    write_text(root / "feasibility/MODEL_SUITE.md", render_model_index())
    write_text(root / "feasibility/toy_program_prospectus/INDEX.md", render_program_index())
    write_text(root / "feasibility/theorem_prospectus/INDEX.md", render_theorem_index())
    write_text(root / "feasibility/ASSUMPTION_LADDER.md", render_assumption_ladder())
    write_text(root / "feasibility/FORMALIZATION_TRACTABILITY.md", render_tractability())
    write_text(root / "feasibility/LANDING_BUNDLES.md", render_landing_bundles())
    write_text(root / "feasibility/EXIT_GATE_AUDIT.md", render_exit_gate())
    write_text(root / "feasibility/RECONNAISSANCE_SYNTHESIS.md", render_synthesis())
    for m in D.MODELS:
        write_text(root / f"feasibility/model_cards/{m['id']}.md", render_model_card(m))
    for p in D.PROGRAMS:
        write_text(root / f"feasibility/toy_program_prospectus/{p['id']}.md", render_program_card(p))
    for t in D.THEOREMS:
        write_text(root / f"feasibility/theorem_prospectus/{t['id']}.md", render_theorem_card(t))

    led = build_ledgers(root)
    write_csv(root / "ledgers/model_registry.csv", led["models"], list(led["models"][0].keys()))
    write_csv(root / "ledgers/model_candidate_discrimination.csv", led["discrimination"], list(led["discrimination"][0].keys()))
    write_csv(root / "ledgers/toy_program_registry.csv", led["programs"], list(led["programs"][0].keys()))
    write_csv(root / "ledgers/theorem_dependency_and_risk.csv", led["theorems"], list(led["theorems"][0].keys()))
    write_csv(root / "ledgers/formalization_surface.csv", led["surfaces"], list(led["surfaces"][0].keys()))
    write_csv(root / "ledgers/family_assumption_ladder.csv", led["ladders"], list(led["ladders"][0].keys()))
    write_csv(root / "ledgers/family_feasibility_registry.csv", led["feasibility"], list(led["feasibility"][0].keys()))
    write_csv(root / "ledgers/landing_bundle_registry.csv", led["bundles"], list(led["bundles"][0].keys()))
    write_csv(root / "ledgers/model_theorem_program_crosswalk.csv", led["crosswalk"], list(led["crosswalk"][0].keys()))
    write_csv(root / "ledgers/no_go_refinement_map.csv", led["ng_map"], list(led["ng_map"][0].keys()))

    summary = {
        "schema_version": "1.0", "project": "CST-EXP", "phase": D.PHASE, "generated_date": D.DATE,
        "counts": {
            "survivor_families": len(D.FAMILY_FEASIBILITY), "finite_model_families": len(D.MODELS),
            "model_family_discrimination_records": len(led["discrimination"]), "theorem_prospectuses": len(D.THEOREMS),
            "constructive_or_boundary_prospects": sum(t["kind"].startswith("constructive") for t in D.THEOREMS),
            "no_go_or_underdetermination_prospects": sum(not t["kind"].startswith("constructive") for t in D.THEOREMS),
            "toy_program_contracts": len(D.PROGRAMS), "formalization_surfaces": len(led["surfaces"]),
            "family_assumption_ladder_records": len(led["ladders"]), "landing_bundles": len(D.LANDING_BUNDLES),
            "model_theorem_program_crosswalk_rows": len(led["crosswalk"]), "no_go_refinement_rows": len(led["ng_map"]),
        },
        "family_exit_gates": [{"id": f["family_id"], "status": f["exit_gate"], "unranked": True} for f in D.FAMILY_FEASIBILITY],
        "boundary": "No theorem or no-go is proved; no toy program is implemented; no final target is selected; no consciousness, survival, numerical-identity, empirical-recognition, or A2 carrier-invariance conclusion is made.",
    }
    write_text(root / "manifests/EXP05_ASSET_SUMMARY.json", json.dumps(summary, indent=2, sort_keys=True))

    render_diagram(root)
    update_decisions(root)
    update_rejections(root)
    update_unresolved(root)
    update_root_surfaces(root)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", type=Path, default=Path(__file__).resolve().parents[1])
    args = ap.parse_args()
    build(args.root)
    print("CST-EXP-05 assets built")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
