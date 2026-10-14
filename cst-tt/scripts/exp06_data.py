#!/usr/bin/env python3
"""Structured CST-EXP-06 target-selection data.

This module contains decision data only.  It does not prove any theorem or
implement any toy model.
"""
from __future__ import annotations

DATE = "2026-08-10"
PHASE = "CST-EXP-06"
STATE_VERSION = "CST-EXP-06-v1"

SOFT_CRITERIA = [
    ("SC-01", "explanatory_reach", "Explanatory reach across the scenario atlas", 12),
    ("SC-02", "theorem_novelty", "Theorem novelty", 7),
    ("SC-03", "mathematical_cleanliness", "Mathematical cleanliness", 10),
    ("SC-04", "compositionality", "Compositionality", 8),
    ("SC-05", "route_treatment", "Treatment of route dependence", 7),
    ("SC-06", "approximation_robustness", "Robustness to approximation", 5),
    ("SC-07", "c_package_fidelity", "Faithfulness to the consciousness C-package", 12),
    ("SC-08", "primitive_economy", "Economy of new primitives", 8),
    ("SC-09", "formal_compatibility", "Compatibility with finite Lean/toy assets", 8),
    ("SC-10", "boundary_clarity", "Clarity of the structural/ontological boundary", 8),
    ("SC-11", "literature_fit", "Relation to the confronted external literature", 5),
    ("SC-12", "finishability", "Likelihood of a clean small theorem-and-toy landing", 10),
]
assert sum(x[3] for x in SOFT_CRITERIA) == 100

HARD_GATES = [
    ("HG-01", "genuinely cross-carrier typed statement"),
    ("HG-02", "not reducible to public or behavioral matching"),
    ("HG-03", "explicit verdict on duplication and fission"),
    ("HG-04", "target-autonomy condition or explicit scoped exclusion"),
    ("HG-05", "no hidden use of A2-P or the desired identity conclusion"),
    ("HG-06", "source-traceable SBT machinery"),
    ("HG-07", "exact finite semantics"),
    ("HG-08", "positive and negative controls"),
    ("HG-09", "clear nonclaims and falsifiers"),
    ("HG-10", "jointly addresses S-R, S-L, and A for a final constructive target"),
]

FINALISTS = [
    {
        "id": "F-01",
        "title": "Integrated target package plus withdrawal autonomy",
        "architecture": "LB-01 / SF-01",
        "class": "standalone_component",
        "selection_status": "not_selected_component_only",
        "hard": {**{f"HG-{i:02d}": "pass" for i in range(1, 10)}, "HG-10": "fail"},
        "hard_notes": {"HG-10": "Supplies S-R and A but deliberately supplies no source-target lineage."},
        "scores": {
            "explanatory_reach": 3.0, "theorem_novelty": 4.5, "mathematical_cleanliness": 4.0,
            "compositionality": 4.0, "route_treatment": 3.5, "approximation_robustness": 3.5,
            "c_package_fidelity": 5.0, "primitive_economy": 4.0, "formal_compatibility": 4.0,
            "boundary_clarity": 5.0, "literature_fit": 4.0, "finishability": 4.0,
        },
        "strongest_case": "It is the only standalone family that directly audits an integrated target-native package and withdrawal autonomy.",
        "strongest_counterexample": "An autonomous package-equivalent independent twin passes S-R and A while lacking source lineage.",
        "unique_insight": "Target realization and target-native maintenance are independent of ancestry.",
        "outperforming_scenario": "S13/S28 external-decoder and delayed-collapse cases.",
        "assumptions": "H-SOURCE-FULL; H-PRESERVE-O; H-GLOBAL-GLUE; H-TARGET-FULL; H-AUTONOMY",
        "burden": "TH-04; TH-05; TH-06 plus package/gluing/autonomy toys.",
        "abandon": "No noncircular finite package witness or no target-owned post-withdrawal invariant region.",
    },
    {
        "id": "F-02",
        "title": "Finite causal-overlap process lineage",
        "architecture": "LB-02 / SF-02",
        "class": "standalone_component",
        "selection_status": "not_selected_component_only",
        "hard": {**{f"HG-{i:02d}": "pass" for i in range(1, 10)}, "HG-10": "fail"},
        "hard_notes": {"HG-10": "Supplies S-L and an autonomy gate but does not establish the target C-package."},
        "scores": {
            "explanatory_reach": 3.5, "theorem_novelty": 4.5, "mathematical_cleanliness": 4.0,
            "compositionality": 4.5, "route_treatment": 4.0, "approximation_robustness": 3.0,
            "c_package_fidelity": 2.5, "primitive_economy": 4.5, "formal_compatibility": 4.5,
            "boundary_clarity": 5.0, "literature_fit": 4.0, "finishability": 4.5,
        },
        "strongest_case": "It gives the cleanest process-sensitive reason to distinguish gradual handoff from detached copying.",
        "strongest_counterexample": "A source-derived destructive reconstruction may preserve every declared endpoint structure while failing the live-overlap criterion.",
        "unique_insight": "A continuing causal process is route/history data, not an endpoint property.",
        "outperforming_scenario": "S01/S07 gradual or prolonged overlap versus S02/S06 detached reconstruction/gap.",
        "assumptions": "H-LINEAGE; H-BRIDGE-ADM; H-XCI for the selected process signature; H-AUTONOMY if paired with takeover.",
        "burden": "TH-07; TH-08; TH-22 and an event-graph corridor checker.",
        "abandon": "Every nonredundancy/process definition is verdict-loaded, or valid corridors do not compose.",
    },
    {
        "id": "F-03",
        "title": "Least relation-valued predictive ancestry",
        "architecture": "LB-03 / SF-03",
        "class": "standalone_component",
        "selection_status": "not_selected_component_only",
        "hard": {**{f"HG-{i:02d}": "pass" for i in range(1, 10)}, "HG-10": "fail"},
        "hard_notes": {"HG-10": "Supplies S-L but does not establish target package realization or autonomy."},
        "scores": {
            "explanatory_reach": 4.5, "theorem_novelty": 4.5, "mathematical_cleanliness": 3.5,
            "compositionality": 4.0, "route_treatment": 4.0, "approximation_robustness": 4.0,
            "c_package_fidelity": 2.5, "primitive_economy": 3.5, "formal_compatibility": 4.0,
            "boundary_clarity": 5.0, "literature_fit": 4.5, "finishability": 4.0,
        },
        "strongest_case": "It handles destructive reconstruction, fission, fusion, empty targets, and independent twins without arbitrary uniqueness.",
        "strongest_counterexample": "A permissive provenance seed can act as an ancestry oracle and make the least closure formally correct but scientifically empty.",
        "unique_insight": "Cross-carrier succession may be a least relation rather than a function or equivalence relation.",
        "outperforming_scenario": "S02/S03/S05/S09/S10 destructive reconstruction, copying, fission, and fusion.",
        "assumptions": "Operational Seed; monotone Γ; no-ex-nihilo; H-LINEAGE; object-specific H-XCI.",
        "burden": "TH-01; TH-09; TH-10; TH-11 plus quotient and closure tools.",
        "abandon": "No operational seed excludes independent twins without already encoding successorhood.",
    },
    {
        "id": "FT-01",
        "title": "Finite Integrated Autonomous Causal Handoff (FIACH)",
        "architecture": "SF-01 + SF-02; mandatory route/recombination/approximation controls",
        "class": "paired_constructive",
        "selection_status": "PRIMARY_FROZEN",
        "hard": {f"HG-{i:02d}": "pass" for i in range(1, 11)},
        "hard_notes": {},
        "scores": {
            "explanatory_reach": 4.0, "theorem_novelty": 4.5, "mathematical_cleanliness": 4.0,
            "compositionality": 4.5, "route_treatment": 4.0, "approximation_robustness": 3.0,
            "c_package_fidelity": 5.0, "primitive_economy": 4.0, "formal_compatibility": 4.0,
            "boundary_clarity": 5.0, "literature_fit": 4.0, "finishability": 4.0,
        },
        "strongest_case": "It is the narrowest target that jointly establishes target package, source-derived live process lineage, and target autonomy while rejecting detached exact copies for a substantive interior-history reason.",
        "strongest_counterexample": "A destructive source-record-target reconstruction can be exact, autonomous, and source-derived yet fails the required live mixed-support corridor.",
        "unique_insight": "A defensible structural precursor to 'moving' requires a target-native package plus a continuing process and a successful withdrawal, not endpoint equality.",
        "outperforming_scenario": "Gradual replacement and live migration with a mixed nonredundant stage, contrasted with detached copying and decoder shadows.",
        "assumptions": "D-CARRIER; H-DISTINCT; H-BRIDGE-ADM; H-SOURCE-FULL (toy stipulation); H-PRESERVE-O; H-GLOBAL-GLUE; H-LINEAGE; H-AUTONOMY; route conditions when claimed.",
        "burden": "TH-04/05/06/07/08 plus combined certificate and composition lemmas; TP-03/04/07/08/10.",
        "abandon": "Corridor circularity, noncomposition, absence of a nontrivial integrated target witness, or inability to internalize all essential support before withdrawal.",
    },
    {
        "id": "FT-02",
        "title": "Integrated Autonomous Predictive Successorship (IAPS)",
        "architecture": "SF-01 + SF-03; mandatory twin/symmetry/route controls",
        "class": "paired_constructive",
        "selection_status": "FALLBACK_FROZEN",
        "hard": {f"HG-{i:02d}": "pass" for i in range(1, 11)},
        "hard_notes": {},
        "scores": {
            "explanatory_reach": 4.5, "theorem_novelty": 4.5, "mathematical_cleanliness": 3.5,
            "compositionality": 4.0, "route_treatment": 4.0, "approximation_robustness": 4.0,
            "c_package_fidelity": 5.0, "primitive_economy": 3.5, "formal_compatibility": 4.0,
            "boundary_clarity": 5.0, "literature_fit": 4.5, "finishability": 3.5,
        },
        "strongest_case": "It retains target realization and autonomy while allowing source-derived destructive reconstruction and relation-valued branching.",
        "strongest_counterexample": "Operational provenance may be too cheap: a record path can exist without carrying the organization that should ground succession.",
        "unique_insight": "The strongest defensible result for copying may be autonomous source-derived successorship, not unique continuation.",
        "outperforming_scenario": "Destructive reconstruction, delayed activation with declared dormancy/provenance, fission, and fusion.",
        "assumptions": "All SF-01 structural assumptions plus operational Seed, monotone Γ, no-ex-nihilo, predictive bridge admissibility, and H-LINEAGE.",
        "burden": "TH-01/04/05/06/09/10/11 plus integrated successor theorem; TP-01/03/06/07/08/10.",
        "abandon": "The ancestry seed is circular/universal, independent twins enter, or target package/autonomy cannot be independently established.",
    },
    {
        "id": "FT-03",
        "title": "Layered dual-lineage autonomous handoff",
        "architecture": "SF-01 + SF-02 + SF-03 with Live ⊆ Anc as an additional theorem target",
        "class": "paired_constructive_extended",
        "selection_status": "DEFERRED_UNIFICATION",
        "hard": {f"HG-{i:02d}": "pass" for i in range(1, 11)},
        "hard_notes": {},
        "scores": {
            "explanatory_reach": 5.0, "theorem_novelty": 5.0, "mathematical_cleanliness": 3.0,
            "compositionality": 4.0, "route_treatment": 4.5, "approximation_robustness": 4.0,
            "c_package_fidelity": 5.0, "primitive_economy": 2.5, "formal_compatibility": 3.0,
            "boundary_clarity": 5.0, "literature_fit": 5.0, "finishability": 2.5,
        },
        "strongest_case": "It represents the live-handoff and destructive-reconstruction notions simultaneously and could prove their exact inclusion/separation.",
        "strongest_counterexample": "Two independently contestable lineage criteria plus the full package may make the first project broad enough that no decisive theorem lands cleanly.",
        "unique_insight": "There may be a hierarchy of structural continuation grades rather than one binary predicate.",
        "outperforming_scenario": "The complete scenario atlas, especially the live/destructive split.",
        "assumptions": "Union of FT-01 and FT-02 plus a theorem connecting overlap corridors to ancestry seeds.",
        "burden": "Almost the whole constructive reconnaissance bank and both lineage engines.",
        "abandon": "The unification theorem depends on arbitrary seed choices or prevents a bounded first landing.",
    },
    {
        "id": "FT-NG",
        "title": "Shared finite no-go and underdetermination kernel",
        "architecture": "LB-NG",
        "class": "negative_kernel",
        "selection_status": "MANDATORY_COMPANION_TERMINAL_FALLBACK",
        "hard": {**{f"HG-{i:02d}": "pass" for i in range(1, 10)}, "HG-10": "fail"},
        "hard_notes": {"HG-10": "A no-go suite deliberately does not supply a positive joint target."},
        "scores": {
            "explanatory_reach": 4.0, "theorem_novelty": 4.0, "mathematical_cleanliness": 5.0,
            "compositionality": 3.0, "route_treatment": 4.0, "approximation_robustness": 4.0,
            "c_package_fidelity": 3.0, "primitive_economy": 5.0, "formal_compatibility": 5.0,
            "boundary_clarity": 5.0, "literature_fit": 4.0, "finishability": 5.0,
        },
        "strongest_case": "Its symmetry, public-shadow, gluing, recombination, decoder, endpoint, route, and residual countermodels remain useful under every constructive choice.",
        "strongest_counterexample": "Each no-go can become trivial if its information boundary or criterion class is drawn too narrowly.",
        "unique_insight": "Many attractive transfer tests are provably insufficient even when no positive criterion is yet accepted.",
        "outperforming_scenario": "Symmetric duplication, public-perfect counterfeits, decoder dependence, local/global obstruction, and route holonomy.",
        "assumptions": "Finite typed structures and explicitly restricted observation/criterion classes only.",
        "burden": "TH-13/14/16/17/18/19/20/22/23 and tiny finite witnesses.",
        "abandon": "The statement omits its information boundary or is defeated by an obvious complete-interface exception.",
    },
]

PRIMARY_ID = "FT-01"
FALLBACK_ID = "FT-02"
TERMINAL_ID = "FT-NG"

DECISIONS = [
    ("D06-001", "selection_unit", "Select among joint target architectures rather than treating SF-01, SF-02, or SF-03 alone as a complete answer.", "The project requires target realization, lineage, and autonomy to remain separate but jointly represented in the final constructive target."),
    ("D06-002", "primary_target", "Freeze FT-01 Finite Integrated Autonomous Causal Handoff as the primary later landing.", "It is the narrowest nontrivial architecture that jointly covers S-R, S-L, and A and distinguishes live handoff from detached exact copying by interior causal structure."),
    ("D06-003", "fallback_target", "Freeze FT-02 Integrated Autonomous Predictive Successorship as the fallback.", "It preserves package and autonomy while handling destructive source-derived reconstruction relation-valuedly if the live-overlap criterion is too restrictive or cannot be made noncircular."),
    ("D06-004", "mandatory_no_go_kernel", "Require the shared finite no-go kernel alongside either constructive target.", "Positive results must be fenced by exact symmetry, public-shadow, recombination, decoder, gluing, endpoint, route, and residual countermodels."),
    ("D06-005", "relation_valued_fission", "Both primary and fallback lineage outputs are relations, not partial identity functions.", "Exact symmetric fission yields multiple qualifying structural successors and supplies no invariant unique selector."),
    ("D06-006", "destructive_transfer_scope", "The primary rejects detached destructive reconstruction as live causal handoff; the fallback may classify it as source-derived successorship under an operational seed.", "This preserves the substantive disagreement instead of deciding it by terminology."),
    ("D06-007", "claim_ceiling", "Freeze only a structural precursor target: target package surrogate, structural lineage/successorship, and finite-model autonomy.", "Certificate soundness, empirical recognition, A1, A2-P, consciousness, personal survival, and numerical identity remain outside the theorem statements."),
    ("D06-008", "approximation_order", "Land exact finite theorems first; approximate extensions require vector defects, local hard gates, margins, and composition laws.", "Approximation should not blur the criterion before its exact positive and negative cases are understood."),
    ("D06-009", "implementation_boundary", "Authorize a later theorem-and-toy project but no full Six Birds simulation.", "The selected targets have elementary finite proof and program surfaces; a full simulation would add cost without resolving the first mathematical questions."),
    ("D06-010", "switch_rule", "Switch from FT-01 to FT-02 only under registered kill criteria, and switch to FT-NG if both constructive lineage definitions remain circular or vacuous.", "Fallbacks are scientific downgrades with explicit reasons, not post hoc rescue labels."),
]

REJECTED_DEFAULTS = [
    ("RD06-001", "The highest numerical score automatically wins.", "Scores are auditable decision aids; FT-01 is selected for narrowness and copy discrimination, not a sub-point numerical margin."),
    ("RD06-002", "A target package plus autonomy already means the source subject moved.", "An autonomous independent twin is a counterexample; a separate lineage relation is mandatory."),
    ("RD06-003", "Any causal data edge is enough for live-process lineage.", "FT-01 requires a no-gap mixed-support corridor and an independently checkable nonredundant update, not mere record provenance."),
    ("RD06-004", "The primary proves destructive uploading impossible.", "It only states that detached reconstruction does not satisfy the selected live-handoff relation; FT-02 studies a different structural successorship relation."),
    ("RD06-005", "Source deletion after copying makes one copy the unique continuer.", "Later deletion does not break an exact symmetry present at the split."),
    ("RD06-006", "A passed finite C-package surrogate proves consciousness.", "The finite package is a structural audit object; certificate soundness, recognition, A1, and ontology remain separate."),
    ("RD06-007", "A source-derived record path is automatically enough for fallback ancestry.", "The seed must also satisfy declared predictive/transition and no-ex-nihilo rules and remains independently contestable."),
    ("RD06-008", "A full C1-C8 empirical realization must be built before any theorem is useful.", "The first theorem may be parametric over independently declared finite clause predicates and demonstrated on an eight-clause surrogate, with the empirical bridge explicitly absent."),
    ("RD06-009", "The dual-lineage architecture should be implemented first because it has the greatest reach.", "It is deferred because its added breadth reduces cleanliness and finishability; it becomes a later unification theorem after one lineage engine lands."),
    ("RD06-010", "Failure of both constructive targets would make the project empty.", "The mandatory no-go kernel remains a substantive landing that isolates what copying, public matching, local certificates, and supported behavior cannot establish."),
]

OPEN_QUESTIONS = [
    (101, "What is the smallest process signature whose preservation is strong enough for FT-01 but does not encode the continuation verdict?"),
    (102, "What finite counterfactual/nonredundancy definition composes under corridor concatenation?"),
    (103, "Can the eight-clause MF-07 surrogate be reduced without losing independent falsifiability or global-gluing content?"),
    (104, "What exact frontier-matching condition is necessary and sufficient for composition of two autonomous handoffs?"),
    (105, "Which route-memory coordinates must be retained so that direct and factored FT-01 handoffs form a congruence?"),
    (106, "Which operational provenance edges are admissible FT-02 seeds, especially for stale, lossy, adversarial, or many-copy records?"),
    (107, "Can LiveHandoff imply PredictiveAncestry under a seed extraction theorem without making the ancestry seed circular?"),
    (108, "What target-boundary declaration rule permits distributed substrates while blocking post hoc boundary enlargement?"),
    (109, "Which exact no-go theorem should be proved first to constrain implementation most efficiently?"),
    (110, "What minimal exact rational defect vector and hard gates support a later approximate extension of the landed exact theorem?"),
]

PRIMARY_THEOREMS = [
    ("PTH-01", "Acyclic local-witness gluing", "constructive", "TH-04", "Prove a global target package witness from independently satisfiable local clause relations on a running-intersection cover."),
    ("PTH-02", "Staged heterogeneous package preservation", "constructive", "TH-05", "Assemble target-local clause witnesses, hard gates, and ownership into the declared finite integrated package."),
    ("PTH-03", "Live corridor composition", "constructive", "TH-07", "Prove composition/transitivity of no-gap mixed-support corridors under exact frontier, clock, and signature compatibility."),
    ("PTH-04", "Post-withdrawal controlled invariance", "constructive_boundary", "TH-06", "Prove target package persistence over all finite horizons inside a target-owned controlled invariant region."),
    ("PTH-05", "FIACH certificate soundness", "constructive", "new_synthesis_of_TH-04_05_06_07", "A checked certificate entails S-R target package, S-L live structural lineage, and A autonomy as separate fields of one handoff record."),
    ("PTH-06", "FIACH composition", "constructive", "new_synthesis", "Composable FIACH episodes yield a FIACH relation from the first source to the final target, subject to route-memory and ownership-interface compatibility."),
    ("PTH-07", "Relation-valued fission", "constructive_boundary", "TH-08;TH-14", "A symmetric valid fork relates the source to both targets and cannot be invariantly reduced to one target."),
    ("PTH-08", "Detached-copy separation", "no_go_boundary", "TH-22", "Endpoint-isomorphic package-bearing autonomous reconstruction need not satisfy live-corridor lineage."),
    ("PTH-09", "External-support autonomy failure", "no_go", "TH-17", "A decoder/scheduler/repair-dependent target fails the declared withdrawal autonomy predicate."),
    ("PTH-10", "Local/global package obstruction", "no_go", "TH-20;TH-16", "Local or branchwise certificates need not form one globally coherent package or preserve recombination."),
    ("PTH-11", "Route-memory composition boundary", "no_go_boundary", "TH-23", "Endpoint/public bridge equivalence is not a congruence when retained route memory differs."),
    ("PTH-12", "Public-shadow insufficiency", "no_go", "TH-13", "Public/report-perfect matching cannot decide hidden package or process predicates on a model class containing shadow-colliding alternatives."),
]

FALLBACK_THEOREMS = [
    ("FTH-01", "Predictive quotient and bridge descent", "constructive", "TH-01", "Define finite predictive partitions and a representative-independent cross-carrier bridge."),
    ("FTH-02", "Least operational ancestry relation", "constructive", "TH-09", "Prove finite monotone closure stabilizes at a unique least relation."),
    ("FTH-03", "Independent-twin exclusion", "constructive_boundary", "TH-11", "A disconnected structural twin cannot enter the least relation under no-ex-nihilo rules."),
    ("FTH-04", "Fission, fusion, and empty targets", "constructive_boundary", "TH-10;TH-14;TH-16", "Derive relation-valued branch/fusion forms and retain a conflict/gluing guard."),
    ("FTH-05", "IAPS integrated target theorem", "constructive", "TH-04;TH-05;TH-06;TH-09", "An ancestral target with a glued target package and post-withdrawal invariant region is an integrated autonomous structural successor."),
    ("FTH-06", "Destructive-reconstruction/twin separation", "constructive_boundary", "TH-11;TH-21", "A source-record-target path may qualify while an identical independent twin does not; without seed/dormancy semantics the gap case remains underdetermined."),
    ("FTH-07", "No unique identity from ancestry", "no_go_boundary", "TH-14", "Relation membership under exact symmetry supplies no invariant unique successor or numerical-identity conclusion."),
    ("FTH-08", "Predictive ancestry is package-insufficient", "no_go", "TH-15", "Predictive equivalence/ancestry alone does not establish the independent C-package obligations."),
]

WITNESSES = [
    ("PW-01", "primary", "positive", "Live integrated handoff", "MF-02 × MF-07 × MF-10", "Four-stage source/mixed/target support sequence; eight finite package proxies; target-owned invariant region after withdrawal."),
    ("PW-02", "primary", "negative", "Detached exact copy", "MF-03 with MF-07 target", "Same endpoint package and autonomy but no mixed/no-gap corridor; S-L fails under FT-01."),
    ("PW-03", "primary", "negative", "Decoder shadow", "MF-07 shadow", "Supported public/package fields match before withdrawal; target collapses after decoder/scheduler/repair removal."),
    ("PW-04", "primary", "negative", "Local-global obstruction", "MF-06/MF-07", "Every local clause check passes while parity/gluing prevents one global package."),
    ("PW-05", "primary", "branch", "Symmetric live fission", "MF-04 with duplicated valid corridor suffix", "Both branches satisfy corridor/package/autonomy; target-swap symmetry blocks unique selection."),
    ("PW-06", "primary", "route", "Replacement-order holonomy", "MF-08", "Two locally valid routes agree publicly but differ on retained route memory; composition needs flatness/confluence."),
    ("FW-01", "fallback", "positive", "Source-derived destructive successor", "MF-03 + MF-07 target", "Operational source-record-target path, predictive bridge, target package, and autonomy; no live overlap required."),
    ("FW-02", "fallback", "negative", "Independent structural twin", "MF-03 twin/MF-05", "Isomorphic target with no source-reachable provenance path is excluded by no-ex-nihilo ancestry."),
    ("FW-03", "fallback", "branch", "Symmetric duplication", "MF-04", "Both source-derived copies enter Anc; no invariant singleton selector."),
    ("FW-04", "fallback", "fusion", "Fusion with recombination conflict", "MF-06", "Many-to-one ancestry may exist while integrated target package fails the conflict/gluing guard."),
    ("CW-01", "common", "negative", "Public-shadow collision", "MF-01/MF-05", "Same public/report input, different hidden predictive/package fact."),
    ("CW-02", "common", "negative", "Scalar residual false positive", "MF-09", "Small aggregate score hides a viability hard-gate failure."),
]

TARGET_REGISTRY = {
    "schema_version": "1.0",
    "project": "CST-EXP",
    "phase": PHASE,
    "generated_date": DATE,
    "primary": {
        "id": PRIMARY_ID,
        "code": "FIACH",
        "title": "Finite Integrated Autonomous Causal Handoff",
        "claim_lanes": ["S-R", "S-L", "A"],
        "status": "frozen_for_later_implementation",
        "source_families": ["SF-01", "SF-02"],
        "mandatory_components": ["TS-02", "TS-03", "TS-04", "TS-06", "TS-07", "TS-08", "TS-09"],
        "core_nonclaim": "No consciousness, personal survival, numerical identity, empirical recognition, certificate soundness, A1, or A2-P conclusion follows.",
    },
    "fallback": {
        "id": FALLBACK_ID,
        "code": "IAPS",
        "title": "Integrated Autonomous Predictive Successorship",
        "claim_lanes": ["S-R", "S-L", "A"],
        "status": "frozen_fallback",
        "source_families": ["SF-01", "SF-03"],
        "mandatory_components": ["TS-01", "TS-02", "TS-04", "TS-06", "TS-07", "TS-09", "TS-10"],
        "core_nonclaim": "Structural successorship is relation-valued and is not numerical identity or proof of conscious survival.",
    },
    "mandatory_companion": {
        "id": TERMINAL_ID,
        "title": "Shared finite no-go and underdetermination kernel",
        "status": "mandatory_companion_and_terminal_fallback",
    },
}
