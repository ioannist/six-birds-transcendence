#!/usr/bin/env python3
"""Build CST-EXP-02 scenario-atlas assets deterministically.

This script creates only preparatory bookkeeping artifacts. It does not select a
transported object, bridge semantics, lineage criterion, scenario verdict,
theorem target, or toy program.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
from collections import Counter, OrderedDict
from pathlib import Path
from textwrap import dedent
from typing import Any, Iterable

from exp02_supplemental import SUPPLEMENTAL_SCENARIOS

PHASE = "CST-EXP-02"
DATE = "2026-08-09"


def write_text(path: Path, text: str) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    clean = "\n".join(line.rstrip() for line in text.splitlines()).rstrip() + "\n"
    path.write_text(clean, encoding="utf-8")


def write_csv(path: Path, fieldnames: list[str], rows: Iterable[dict[str, Any]]) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", newline="", encoding="utf-8") as fh:
        writer = csv.DictWriter(fh, fieldnames=fieldnames, extrasaction="ignore", lineterminator="\n")
        writer.writeheader()
        for row in rows:
            writer.writerow({k: row.get(k, "") for k in fieldnames})


def compact_list(items: Iterable[str]) -> str:
    return ";".join(items)


AXES: "OrderedDict[str, dict[str, Any]]" = OrderedDict([
    ("carrier_relation", {
        "question": "How are source and target supports related at the protocol level?",
        "values": OrderedDict([
            ("same_support_reencoding", "One support is retained while representation, coordinates, or packaging changes."),
            ("partially_overlapping_support", "Source-side and target-side supports are separately typed but share components or jointly contribute during some interval."),
            ("disjoint_support", "Source-side and target-side supports have no shared support component at the declared comparison level."),
        ]),
        "blocked": "Carrier relation does not determine transport, lineage, realization, or ontology.",
    }),
    ("change_mode", {
        "question": "What operational mechanism changes source-side support into target-side support?",
        "values": OrderedDict([
            ("gradual_replacement", "Support responsibility changes in multiple ordered stages."),
            ("abrupt_translation", "A single or effectively unresolved stage maps a declared source record/package into target form."),
            ("checkpoint_restart", "A retained record is used to activate a target after pause, shutdown, or absence."),
            ("live_migration", "An active package is maintained while responsibility moves between concurrently operating supports."),
            ("destructive_scan", "Source support/package is disabled or made unavailable as part of acquisition/reconstruction."),
            ("nondestructive_copy", "A target is constructed while the source remains available for at least one stage."),
            ("distributed_extension", "A package is extended across multiple supports without requiring a unique transfer instant."),
        ]),
        "blocked": "Mode names describe engineering order, not continuity verdicts.",
    }),
    ("source_fate", {
        "question": "What happens operationally to source-side package support?",
        "values": OrderedDict([
            ("persists", "Source support remains active and available after target activation."),
            ("degrades", "Source contribution is progressively reduced or loses declared capability."),
            ("paused", "Source dynamics are intentionally suspended while a recoverable record/support remains."),
            ("erased_before_activation", "Source package/support is made unavailable before target activation."),
            ("erased_after_activation", "Source package/support remains for a period after target activation and is then made unavailable."),
            ("remains_coupled", "Source remains an active causal/resource component of the operating source-target assembly."),
        ]),
        "blocked": "Source destruction, persistence, or coupling does not by itself decide lineage.",
    }),
    ("target_timing", {
        "question": "How is target activation temporally related to source activity?",
        "values": OrderedDict([
            ("continuous_overlap", "Source and target have an interval of concurrent operation or contribution."),
            ("delayed_activation", "Target activates after acquisition/construction, without a stipulated extended dormant gap."),
            ("temporal_gap", "No active package is stipulated for a nonzero interval between source cessation/pause and target activation."),
            ("time_rescaled_activation", "Target operation is related by an explicit non-unit clock map or time reparameterization."),
        ]),
        "blocked": "Temporal continuity or discontinuity does not define lineage by itself.",
    }),
    ("branching", {
        "question": "What is the cardinality/topology of operational package episodes?",
        "values": OrderedDict([
            ("one_to_one", "One designated source episode is connected operationally to one designated target episode."),
            ("one_to_many", "One source episode produces or feeds multiple target/live continuation episodes."),
            ("many_to_one", "Multiple source/branch episodes contribute to one target episode."),
            ("many_to_many", "The protocol contains multiple source-side and target-side episodes or distributed pieces."),
        ]),
        "blocked": "Operational branching is not a lineage graph until a criterion supplies lineage edges.",
    }),
    ("bridge_dependence", {
        "question": "What continuing bridge or protocol support is built into the scenario?",
        "values": OrderedDict([
            ("permanent", "The source-target coupling/bridge remains part of the declared operating assembly."),
            ("temporary", "The protocol schedules the bridge to end, but target autonomy is not stipulated."),
            ("removable", "The setup exposes a well-defined withdrawal intervention; survival after withdrawal is left open."),
            ("externally_decoded", "The claimed target-facing structure/readout requires a continuing external decoder or source process."),
        ]),
        "blocked": "A removable bridge is not thereby safely removable; a permanent bridge is not thereby illegitimate.",
    }),
    ("fidelity", {
        "question": "What kind of agreement is stipulated at the scenario's declared transfer granularity?",
        "values": OrderedDict([
            ("exact", "Zero declared defect at the named granularity only."),
            ("lossy", "Some declared source information/structure is omitted or changed."),
            ("error_corrected", "A recovery/repair mechanism is part of the stipulated target construction."),
            ("residual_bounded", "A named nonzero defect is bounded, with threshold significance left open."),
            ("adaptive", "Agreement is maintained or approached through ongoing adjustment rather than one fixed copy map."),
        ]),
        "blocked": "Exactness at one granularity does not imply exactness of the full package or lineage.",
    }),
    ("reversibility", {
        "question": "Does the protocol expose an inverse at the declared granularity?",
        "values": OrderedDict([
            ("reversible", "A declared inverse route recovers the named object exactly within its admissible domain."),
            ("approximately_reversible", "A reverse route recovers the named object only up to a declared residual/equivalence."),
            ("irreversible", "No admissible inverse is stipulated for the named object."),
        ]),
        "blocked": "Protocol reversibility does not entail token identity or zero route holonomy for unmeasured structures.",
    }),
    ("route_multiplicity", {
        "question": "How many admissible routes connect the declared operational endpoints?",
        "values": OrderedDict([
            ("unique_route", "Only one route is admitted at the scenario's declared resolution."),
            ("multiple_equivalent_routes", "Several routes are stipulated to agree under a named endpoint comparison, with stronger equivalence left open."),
            ("holonomy_bearing_routes", "Closed or alternative routes can restore selected endpoint observables while changing another declared structure."),
        ]),
        "blocked": "One successful route does not establish route independence; endpoint agreement does not erase route history.",
    }),
    ("granularity", {
        "question": "At what level is the scenario's stipulated fidelity/comparison made?",
        "values": OrderedDict([
            ("microstate", "Carrier-level state/configuration information."),
            ("predictive_state", "Future-sufficient classes, transition structure, or continuation-relevant state."),
            ("package_state", "A multi-clause package record or maintained package-level structure."),
            ("event_package", "Globally packaged event/role/time/identity structure rather than pairwise local records."),
            ("certificate_only", "Only a declared certificate, report, or externally decoded signature is matched."),
        ]),
        "blocked": "Agreement at a coarser granularity cannot be promoted to a finer one without a theorem.",
    }),
])

DISCRIMINATORS = [
    {
        "id": "D01", "name": "predictive_fiber_continuity", "label": "Continuity of predictive fibers",
        "question": "Does the candidate relate source and target future-sufficient classes, rather than only current/public states?",
        "assets": ["A-PQ-01", "A-PQ-02", "A-RT-01"],
        "questions": ["Q-PRS-003", "Q-RTE-004", "Q-RTE-005", "Q-OBS-007"],
        "lanes": "S-T;S-L;R",
    },
    {
        "id": "D02", "name": "admissible_continuation_structure", "label": "Preservation of admissible continuation structure",
        "question": "Does the bridge preserve, simulate, or rebuild the admissible continuation law on histories/processes?",
        "assets": ["A-PQ-02", "A-RT-01", "A-CF-01"],
        "questions": ["Q-BRG-003", "Q-PRS-001", "Q-LIN-001", "Q-LIN-010"],
        "lanes": "S-T;S-L",
    },
    {
        "id": "D03", "name": "temporal_overlap_and_causal_coupling", "label": "Temporal overlap and causal coupling",
        "question": "Which causal/process dependence and clock relation connects source, bridge stages, and target?",
        "assets": ["A-TM-01", "A-PT-01", "A-EV-01"],
        "questions": ["Q-BRG-005", "Q-TYP-008", "Q-RTE-006", "Q-LIN-008"],
        "lanes": "S-T;S-L;A",
    },
    {
        "id": "D04", "name": "recombination_content", "label": "Survival of recombination content",
        "question": "Are joint/branchwise facts preserved or reconstructed, and can locally matching pieces glue globally?",
        "assets": ["A-RE-01", "A-OP-01", "A-LG-01"],
        "questions": ["Q-PRS-009", "Q-LIN-006", "Q-LIN-007", "Q-PRS-005"],
        "lanes": "S-R;S-L",
    },
    {
        "id": "D05", "name": "ledger_and_viability_continuity", "label": "Ledger and viability continuity",
        "question": "Do viability, resource, repair, and maintenance ledgers remain valid through and after handoff?",
        "assets": ["A-VI-01", "A-CU-01", "A-AG-01"],
        "questions": ["Q-PRS-010", "Q-AUT-002", "Q-AUT-003", "Q-APP-005"],
        "lanes": "S-R;A",
    },
    {
        "id": "D06", "name": "action_credit_history", "label": "Source-target action-credit history",
        "question": "How are provenance, action-credit, and source/target responsibility allocated across stages?",
        "assets": ["A-CT-01", "A-OP-01", "A-EV-01"],
        "questions": ["Q-PRS-007", "Q-LIN-003", "Q-BRG-005", "Q-TYP-007"],
        "lanes": "S-R;S-L;A",
    },
    {
        "id": "D07", "name": "route_holonomy", "label": "Route holonomy",
        "question": "Can alternative routes or closed loops change predictive, temporal, memory, or lineage data despite endpoint agreement?",
        "assets": ["A-HO-01", "A-CF-01", "A-TM-01"],
        "questions": ["Q-RTE-001", "Q-RTE-002", "Q-RTE-003", "Q-BRG-008"],
        "lanes": "S-T;S-L",
    },
    {
        "id": "D08", "name": "autonomous_closure_after_withdrawal", "label": "Autonomous closure after bridge removal",
        "question": "What remains when source, bridge, decoder, or staging support is removed, and what target-native dynamics maintain it?",
        "assets": ["A-AG-01", "A-VI-01", "A-PT-01", "A-QEC-01"],
        "questions": ["Q-CORE-008", "Q-AUT-001", "Q-AUT-003", "Q-AUT-004", "Q-AUT-005"],
        "lanes": "A;S-R",
    },
    {
        "id": "D09", "name": "exact_vs_approximate_defect", "label": "Exact versus approximate defect",
        "question": "Which defect is zero/bounded, how does it compose, and can small local defects trigger package or viability discontinuities?",
        "assets": ["A-AR-01", "A-CD-01", "A-QEC-01", "A-VI-01"],
        "questions": ["Q-CORE-011", "Q-APP-001", "Q-APP-002", "Q-APP-003", "Q-APP-004", "Q-APP-005", "Q-APP-007"],
        "lanes": "S-T;S-R;A",
    },
    {
        "id": "D10", "name": "lineage_cardinality_and_uniqueness", "label": "Uniqueness or branching of continuation",
        "question": "Does the criterion return zero, one, many, or fused successors, and what breaks symmetry or yields underdetermination?",
        "assets": ["A-OP-01", "A-PQ-01", "A-RE-01"],
        "questions": ["Q-CORE-007", "Q-LIN-002", "Q-LIN-004", "Q-LIN-005", "Q-LIN-006", "Q-LIN-007", "Q-LIN-008", "Q-LIN-009"],
        "lanes": "S-L",
    },
]

OUTCOME_LABELS = [
    # Transport lane
    ("OT-ST-01", "S-T", "no_transport", "The candidate's named transport predicate fails on the scenario.", "Does not imply no target package or no lineage under another criterion."),
    ("OT-ST-02", "S-T", "structural_transport_satisfied", "The named object/invariant satisfies the candidate's typed transport predicate.", "Does not imply target realization, lineage, autonomy, recognition, or ontology."),
    ("OT-ST-03", "S-T", "route_dependent_transport", "Transport verdict or transported structure differs across admissible routes.", "Does not say which route is normatively correct."),
    ("OT-ST-04", "S-T", "transport_underdetermined", "The candidate/instruments do not determine whether the transport predicate holds.", "Must state whether the source is criterion ambiguity, missing data, or scenario underspecification."),
    ("OT-ST-05", "S-T", "not_applicable_same_carrier", "The scenario fails the candidate's distinct-carrier applicability condition.", "Does not deny same-support invariance or usefulness as a control."),
    # Target realization lane
    ("OT-SR-01", "S-R", "no_valid_target_package", "No target episode satisfies the declared target package/gate predicate.", "Does not by itself settle lineage of records or partial structures."),
    ("OT-SR-02", "S-R", "target_package_exists", "At least one target episode satisfies the declared target package/gate predicate.", "Does not imply source-target lineage or autonomy."),
    ("OT-SR-03", "S-R", "public_duplicate_with_hidden_mismatch", "Target matches the declared public/report interface while failing a named hidden, predictive, coherence, or package condition.", "Public mismatch is not required; the hidden mismatch must be named."),
    ("OT-SR-04", "S-R", "empty_target_after_viability_failure", "The target package relation returns empty because a declared viability/maintenance condition fails.", "This is structural extinction under a criterion, not an ontological death claim."),
    ("OT-SR-05", "S-R", "target_package_underdetermined", "Available scenario data do not determine target package satisfaction.", "Must distinguish unavailable evidence from an undefined target predicate."),
    ("OT-SR-06", "S-R", "target_package_not_applicable", "The scenario/candidate has no separately designated target-package question at the declared scope.", "Permitted only with an explicit boundary, such as a same-carrier representation control or genuinely joint distributed object."),
    # Lineage lane
    ("OT-SL-01", "S-L", "no_declared_lineage_reaches_target", "A target package may exist, but the chosen lineage relation has no source-to-target edge.", "Does not imply target nonrealization or metaphysical nonidentity."),
    ("OT-SL-02", "S-L", "structural_successor", "The target is related forward to the source by the declared structural criterion, without a uniqueness/exclusivity claim.", "Does not imply one-to-one continuation or personal identity."),
    ("OT-SL-03", "S-L", "one_to_one_lineage_continuation", "Exactly one target successor is selected within the declared candidate domain and route scope.", "Cardinality one does not license personal identity or global uniqueness outside scope."),
    ("OT-SL-04", "S-L", "branch_valued_continuation", "One source has multiple lineage successors under the declared criterion.", "Does not assert one token is literally numerically identical to all branches."),
    ("OT-SL-05", "S-L", "fusion_valued_continuation", "One target has multiple lineage predecessors under the declared criterion.", "Does not imply identity with every predecessor or preservation of conflicting histories."),
    ("OT-SL-06", "S-L", "package_equivalent_duplicate_with_unresolved_token_identity", "Target tokens are package-equivalent under the declared structure while token/personal identity remains unresolved.", "This is an explicit boundary label, not a hidden assertion that copies are new or same persons."),
    ("OT-SL-07", "S-L", "lineage_underdetermined", "The criterion or available facts do not select a lineage classification.", "Must identify symmetry, missing history, route dependence, or another specific source."),
    ("OT-SL-08", "S-L", "lineage_not_applicable", "The candidate does not define lineage for this scenario class.", "Permitted only with an explicit scope limitation, not silent omission."),
    # Autonomy lane
    ("OT-A-01", "A", "bridge_dependent_shadow", "Named target package behavior fails or is undefined when continuing source/bridge/decoder support is withdrawn.", "Does not entail that the coupled distributed assembly lacks a package."),
    ("OT-A-02", "A", "autonomous_target_realization", "A target package exists and remains maintained under the declared withdrawal intervention, environment, disturbance class, and horizon.", "Does not imply lineage or consciousness."),
    ("OT-A-03", "A", "autonomy_failure_after_withdrawal", "A target package exists before withdrawal but fails the declared maintenance condition afterward.", "Does not determine whether a shorter horizon would pass."),
    ("OT-A-04", "A", "autonomy_underdetermined", "The setup or candidate does not determine post-withdrawal maintenance.", "Must state missing intervention, horizon, dynamics, or observability."),
    ("OT-A-05", "A", "autonomy_not_tested", "No autonomy intervention is applicable or supplied for the claim being evaluated.", "Cannot be paraphrased as autonomous."),
    # Recognition/instrument lane
    ("OT-R-01", "R", "determinate_under_declared_instruments", "The declared instruments suffice to decide the candidate's structural verdict within stated error bounds.", "Does not make the structural predicate true by observation alone."),
    ("OT-R-02", "R", "indeterminate_under_declared_instruments", "Distinct structural/lineage possibilities remain observationally equivalent under the declared instruments.", "Does not imply metaphysical indeterminacy."),
    ("OT-R-03", "R", "instrument_not_supplied", "The candidate has not supplied a recognition/measurement bridge for this scenario.", "Structural analysis may still be possible in a toy with complete-state access."),
]

SCENARIOS: list[dict[str, Any]] = [
    {
        "id": "S01", "number": 1, "title": "Gradual component-by-component replacement",
        "canonical_prompt": "Gradual neuron-by-neuron or component-by-component replacement.",
        "purpose": "Isolate staged responsibility transfer, overlap, order effects, and the difference between local replacement success and a globally maintained package.",
        "facts": [
            "Source-side components are retired in a declared sequence while target-side components assume corresponding operational roles.",
            "At least one interval contains contributions from both separately typed supports.",
            "Each local replacement is stipulated to meet a declared local interface test; full-package preservation is not stipulated.",
            "The source contribution decreases over stages, and a final source-withdrawal intervention is available.",
        ],
        "episode_graph": "E_S^0 -> E_mix^1 -> ... -> E_mix^n -> E_T^n",
        "carrier_relation": "partially_overlapping_support", "change_mode": "gradual_replacement", "source_fate": "degrades",
        "target_timing": "continuous_overlap", "branching": "one_to_one", "bridge_dependence": "temporary",
        "fidelity": "adaptive", "reversibility": "approximately_reversible", "route_multiplicity": "multiple_equivalent_routes", "granularity": "package_state",
        "secondary_modes": "live_migration", "cross_carrier_status": "genuine_cross_carrier_candidate", "handoff_shape": "extended_interval",
        "branch_graph": "operational 1->1 with mixed-support intermediate episodes", "clock_relation": "shared route order; local clocks need not be identical",
        "causal_structure": "continuous coupled process with moving support responsibility",
        "fidelity_scope": "local role/interface tests plus an adaptive package-level trajectory; hidden/predictive equivalence remains open",
        "autonomy_intervention": "remove every remaining source-side contribution and transfer controller after the final scheduled stage",
        "instrument_constraints": "local tests may be public or privileged; global hidden/predictive state need not be observable",
        "variants": ["different replacement orders", "brief versus long overlap per component", "exact local tests versus residual-bounded local tests"],
        "primary_discriminators": ["D02", "D03", "D06", "D07", "D08", "D10"],
        "stress_questions": [
            "Do all admissible replacement orders yield equivalent target package data?",
            "Can every local handoff pass while no global package exists at an intermediate stage?",
            "Which source-specific history is carried by mixed-support episodes rather than reconstructed at the end?",
            "Does final source withdrawal expose protocol dependence that was hidden during overlap?",
        ],
        "blocked_inferences": ["Graduality is not continuity by definition.", "Overlap is not token identity.", "Local test success is not global package preservation.", "A smooth public trajectory is not predictive-fiber continuity."],
        "asset_focus": ["A-TM-01", "A-CF-01", "A-LG-01", "A-AG-01", "A-RT-01"],
        "question_focus": ["Q-TYP-007", "Q-BRG-005", "Q-RTE-003", "Q-RTE-007", "Q-AUT-001", "Q-LIN-010"],
    },
    {
        "id": "S02", "number": 2, "title": "Instantaneous destructive scan and reconstruction",
        "canonical_prompt": "Instantaneous destructive scan and reconstruction.",
        "purpose": "Separate exact record reconstruction from causal overlap, source persistence, and any assumed lineage effect of destruction.",
        "facts": [
            "A source record is acquired at one declared resolution and the source package/support is made unavailable before target activation.",
            "A disjoint target is constructed from the retained record in one unresolved translation stage.",
            "The target is stipulated exact at the declared microstate record, but continuation laws and full-package gates are candidate questions.",
            "No source-target operating overlap is stipulated.",
        ],
        "episode_graph": "E_S --scan/erase--> R --reconstruct--> E_T",
        "carrier_relation": "disjoint_support", "change_mode": "destructive_scan", "source_fate": "erased_before_activation",
        "target_timing": "delayed_activation", "branching": "one_to_one", "bridge_dependence": "temporary",
        "fidelity": "exact", "reversibility": "irreversible", "route_multiplicity": "unique_route", "granularity": "microstate",
        "secondary_modes": "abrupt_translation", "cross_carrier_status": "genuine_cross_carrier_candidate", "handoff_shape": "sharp_record_mediated",
        "branch_graph": "operational 1->record->1", "clock_relation": "source endpoint precedes target start; no shared now required",
        "causal_structure": "record-mediated source-to-target dependence without live overlap",
        "fidelity_scope": "exact retained scan record only; no automatic predictive, package, or lineage exactness",
        "autonomy_intervention": "remove the scan record, reconstruction machinery, and source-side resources after activation",
        "instrument_constraints": "complete scan-record access is stipulated; hidden dynamics not encoded in the record remain open",
        "variants": ["record includes transition law versus state only", "zero versus small construction delay", "source erased during versus immediately after scan"],
        "primary_discriminators": ["D01", "D02", "D03", "D08", "D09", "D10"],
        "stress_questions": [
            "Does exact microstate reconstruction induce a well-defined history/continuation bridge?",
            "Which conclusion changes solely because the source is erased before activation?",
            "Can a candidate distinguish reconstruction from continuation without smuggling token identity into the record?",
            "What target-native maintenance remains after reconstruction equipment is removed?",
        ],
        "blocked_inferences": ["Source destruction is not proof of target lineage.", "Microstate equality under a record map is not cross-typed token equality.", "A record is not a dormant subject by definition.", "No overlap is not discontinuity under every criterion."],
        "asset_focus": ["A-PQ-01", "A-PQ-02", "A-OP-01", "A-FS-01", "A-AG-01"],
        "question_focus": ["Q-BRG-003", "Q-RTE-006", "Q-LIN-008", "Q-LIN-011", "Q-AUT-001", "Q-ASM-004"],
    },
    {
        "id": "S03", "number": 3, "title": "Nondestructive exact copy while source continues",
        "canonical_prompt": "Nondestructive exact copy while the source continues.",
        "purpose": "Expose the difference between exact structural duplication, source persistence, branch cardinality, and unique-continuation claims.",
        "facts": [
            "One disjoint target is activated while the source remains active.",
            "Source and target are stipulated exact at the declared package-state comparison at the split instant.",
            "After activation, source and target receive independently selectable continuations.",
            "The copying bridge can be removed without changing the fact that both live episodes exist; post-removal maintenance remains to be tested.",
        ],
        "episode_graph": "E_S^0 -> {E_S^+, E_T^+}",
        "carrier_relation": "disjoint_support", "change_mode": "nondestructive_copy", "source_fate": "persists",
        "target_timing": "continuous_overlap", "branching": "one_to_many", "bridge_dependence": "removable",
        "fidelity": "exact", "reversibility": "irreversible", "route_multiplicity": "unique_route", "granularity": "package_state",
        "secondary_modes": "", "cross_carrier_status": "genuine_cross_carrier_candidate", "handoff_shape": "copy_split_no_exclusive_handoff",
        "branch_graph": "one pre-copy episode to two simultaneously live episodes", "clock_relation": "split event plus independent post-split local times",
        "causal_structure": "common causal ancestry followed by independent dynamics",
        "fidelity_scope": "exact package-state relation at split; future equivalence after divergent inputs is not stipulated",
        "autonomy_intervention": "remove copy machinery and any shared synchronization channel while keeping ordinary environments",
        "instrument_constraints": "exact package access at split is stipulated; future hidden state may diverge under different continuations",
        "variants": ["identical versus different post-split environments", "source/target labels swapped", "copy bridge removed immediately versus later"],
        "primary_discriminators": ["D01", "D03", "D06", "D08", "D10"],
        "stress_questions": [
            "Can a criterion select one unique successor without an asymmetric fact?",
            "Does source persistence alter lineage or only reveal branching that was already implicit?",
            "Are both post-split episodes successors, or is lineage undefined/underdetermined?",
            "What structures remain exact after independently controlled futures?",
        ],
        "blocked_inferences": ["Exact duplication is not unique continuation.", "A duplicate is not nonreal by definition.", "Source persistence is not proof that only the source continues.", "Common ancestry is not token identity."],
        "asset_focus": ["A-OP-01", "A-PQ-01", "A-RE-01", "A-AG-01"],
        "question_focus": ["Q-LIN-004", "Q-LIN-005", "Q-LIN-002", "Q-PRS-009", "Q-AUT-006", "Q-ASM-004"],
    },
    {
        "id": "S04", "number": 4, "title": "Copy first, source deletion later",
        "canonical_prompt": "Copy first, source deletion later.",
        "purpose": "Test whether lineage classifications illegitimately change retroactively when a source is deleted after a period of coactivation.",
        "facts": [
            "A target is created while the source continues, and both operate for a declared overlap interval.",
            "The target is exact at the declared package-state comparison at activation.",
            "The source is erased only after source and target have accumulated distinguishable post-copy histories.",
            "The target remains available for a withdrawal/autonomy test after deletion.",
        ],
        "episode_graph": "E_S^0 -> {E_S^1, E_T^1}; E_S^1 -> erased; E_T^1 -> E_T^2",
        "carrier_relation": "disjoint_support", "change_mode": "nondestructive_copy", "source_fate": "erased_after_activation",
        "target_timing": "continuous_overlap", "branching": "one_to_many", "bridge_dependence": "temporary",
        "fidelity": "exact", "reversibility": "irreversible", "route_multiplicity": "unique_route", "granularity": "package_state",
        "secondary_modes": "post_copy_deletion", "cross_carrier_status": "genuine_cross_carrier_candidate", "handoff_shape": "delayed_exclusive_handoff",
        "branch_graph": "one-to-many split followed by removal of the source-side branch", "clock_relation": "shared split marker; independent histories before deletion",
        "causal_structure": "copy ancestry, independent coactivity, then exogenous source removal",
        "fidelity_scope": "exact at copy instant only; histories differ before source deletion",
        "autonomy_intervention": "source deletion is one intervention; separately remove any remaining copy/synchronization apparatus",
        "instrument_constraints": "both branch histories are available in the thought experiment",
        "variants": ["immediate versus long-delayed source deletion", "deletion chosen by source versus external operator", "source branch damaged versus clean at deletion"],
        "primary_discriminators": ["D03", "D06", "D08", "D10"],
        "stress_questions": [
            "Can deletion at time t change the lineage relation assigned at the earlier split?",
            "Does the target acquire uniqueness only because a competing branch is removed?",
            "Which branch-specific histories matter after deletion?",
            "Is source deletion part of handoff, autonomy testing, lineage evidence, or all three separately?",
        ],
        "blocked_inferences": ["Later deletion does not retroactively erase a prior branch.", "Being the sole survivor is not unique lineage by definition.", "Source erasure is not an ontological transfer event.", "Target availability is not target autonomy."],
        "asset_focus": ["A-OP-01", "A-TM-01", "A-RE-01", "A-AG-01"],
        "question_focus": ["Q-LIN-008", "Q-LIN-004", "Q-RTE-004", "Q-AUT-001", "Q-AUT-006"],
    },
    {
        "id": "S05", "number": 5, "title": "Two simultaneous exact targets",
        "canonical_prompt": "Two simultaneous exact targets.",
        "purpose": "Create a maximally symmetric duplication case that tests unique-lineage rules and hidden tie-breakers.",
        "facts": [
            "Two disjoint target carriers are activated simultaneously from the same source-side record/process.",
            "The two targets are stipulated isomorphic and exact at the declared package-state comparison at activation.",
            "No target-distinguishing causal, temporal, spatial-priority, naming, or quality fact is admitted at the split.",
            "The source is erased before joint activation to prevent source persistence from being the sole asymmetry.",
        ],
        "episode_graph": "E_S -> erase; R -> {E_T1, E_T2} (symmetric)",
        "carrier_relation": "disjoint_support", "change_mode": "destructive_scan", "source_fate": "erased_before_activation",
        "target_timing": "delayed_activation", "branching": "one_to_many", "bridge_dependence": "removable",
        "fidelity": "exact", "reversibility": "irreversible", "route_multiplicity": "multiple_equivalent_routes", "granularity": "package_state",
        "secondary_modes": "symmetric_multi_target_reconstruction", "cross_carrier_status": "genuine_cross_carrier_candidate", "handoff_shape": "symmetric_branch_activation",
        "branch_graph": "one source record to two symmetry-related targets", "clock_relation": "joint activation under a symmetry-preserving clock relation",
        "causal_structure": "equal common ancestry with no admitted asymmetry between target legs",
        "fidelity_scope": "exact package-state match on both legs at activation",
        "autonomy_intervention": "remove common reconstruction/synchronization support from both targets symmetrically",
        "instrument_constraints": "complete declared structural access; target labels are treated as gauge-like names for symmetry testing",
        "variants": ["targets later diverge", "one target later fails", "a tiny asymmetry is introduced only after activation"],
        "primary_discriminators": ["D01", "D06", "D08", "D10"],
        "stress_questions": [
            "What non-arbitrary fact could select exactly one target?",
            "Does the candidate return two successors, no unique successor, or token-level underdetermination?",
            "Would relabeling T1 and T2 change the verdict?",
            "Can later divergence or failure determine an earlier lineage fact without retroactivity?",
        ],
        "blocked_inferences": ["Numerical multiplicity is not nonrealization.", "Symmetry cannot be broken by names alone.", "Source deletion does not select one target.", "Exact package equivalence does not resolve token identity."],
        "asset_focus": ["A-OP-01", "A-PQ-01", "A-RE-01"],
        "question_focus": ["Q-LIN-005", "Q-LIN-002", "Q-CTL-003", "Q-ASM-004", "Q-TYP-003"],
    },
    {
        "id": "S06", "number": 6, "title": "Target activation after a temporal gap",
        "canonical_prompt": "Target activation after a temporal gap.",
        "purpose": "Separate a dormant record/restart protocol from uninterrupted activity and force explicit temporal-lineage semantics.",
        "facts": [
            "The source is paused or made unavailable after producing a retained checkpoint record.",
            "A nonzero interval contains no stipulated active full package on source or target.",
            "A disjoint target is later activated exactly from the checkpoint at the declared predictive-state granularity.",
            "The record persists through the gap; whether anything else persists is not stipulated.",
        ],
        "episode_graph": "E_S -> checkpoint R -> [gap: no active package stipulated] -> E_T",
        "carrier_relation": "disjoint_support", "change_mode": "checkpoint_restart", "source_fate": "paused",
        "target_timing": "temporal_gap", "branching": "one_to_one", "bridge_dependence": "removable",
        "fidelity": "exact", "reversibility": "approximately_reversible", "route_multiplicity": "unique_route", "granularity": "predictive_state",
        "secondary_modes": "delayed_reconstruction", "cross_carrier_status": "genuine_cross_carrier_candidate", "handoff_shape": "record_mediated_with_dormant_interval",
        "branch_graph": "one active episode, one inert record interval, one target episode", "clock_relation": "partial order with a gap; no canonical phase alignment unless supplied",
        "causal_structure": "record-mediated dependence across an inactive interval",
        "fidelity_scope": "exact predictive checkpoint as defined by the scenario; temporal closure and full package are open",
        "autonomy_intervention": "remove checkpoint store and restart controller after target activation",
        "instrument_constraints": "checkpoint contents are available; no observation during the inactive gap can certify an active package",
        "variants": ["short versus arbitrarily long gap", "source can versus cannot be resumed", "checkpoint stores state only versus transition/ledger history"],
        "primary_discriminators": ["D01", "D02", "D03", "D05", "D08", "D10"],
        "stress_questions": [
            "What object, if any, carries lineage through an interval with no active package?",
            "Is the checkpoint a bridge record, a package component, or only a reconstruction resource?",
            "Does gap duration matter if the structural record is unchanged?",
            "Can temporal closure be re-established without being preserved continuously?",
        ],
        "blocked_inferences": ["A stored record is not an active package by definition.", "Temporal gap is not extinction under every lineage criterion.", "Exact restart is not uninterrupted causal activity.", "Dormancy and reconstruction require separate classification."],
        "asset_focus": ["A-TM-01", "A-PQ-02", "A-OP-01", "A-VI-01"],
        "question_focus": ["Q-RTE-006", "Q-LIN-011", "Q-LIN-009", "Q-PRS-008", "Q-TYP-008"],
    },
    {
        "id": "S07", "number": 7, "title": "Long-lived source-target overlap",
        "canonical_prompt": "Transfer through a long-lived source-target overlap.",
        "purpose": "Test process-level handoff, moving responsibility, source-target coupling, and whether overlap hides dependence rather than establishing autonomy.",
        "facts": [
            "Separately typed source and target supports operate jointly for a long interval.",
            "Package functions are reassigned gradually, but both sides remain causally coupled through most of the route.",
            "A target-dominant episode is reached before source-side support is finally removed.",
            "The protocol adaptively corrects discrepancies during overlap.",
        ],
        "episode_graph": "E_S -> E_joint^1 -> ... -> E_joint^m(target-dominant) -> E_T?",
        "carrier_relation": "partially_overlapping_support", "change_mode": "live_migration", "source_fate": "remains_coupled",
        "target_timing": "continuous_overlap", "branching": "one_to_one", "bridge_dependence": "temporary",
        "fidelity": "adaptive", "reversibility": "approximately_reversible", "route_multiplicity": "multiple_equivalent_routes", "granularity": "package_state",
        "secondary_modes": "gradual_replacement", "cross_carrier_status": "genuine_cross_carrier_candidate", "handoff_shape": "long_overlap_then_withdrawal",
        "branch_graph": "one coupled operational trajectory with changing contribution weights", "clock_relation": "coupled clocks during overlap; independent target clock after withdrawal",
        "causal_structure": "continuous bidirectional or feedback coupling during overlap",
        "fidelity_scope": "adaptive package-level agreement under coupled operation",
        "autonomy_intervention": "remove all source-target coupling channels and source-side repair/control after target-dominant operation stabilizes",
        "instrument_constraints": "joint operation can mask which side generates the observed package behavior",
        "variants": ["unidirectional versus bidirectional coupling", "fast versus slow handoff", "withdrawal before versus after target repair internalization"],
        "primary_discriminators": ["D02", "D03", "D05", "D06", "D08"],
        "stress_questions": [
            "Which package predicates are genuinely target-native before withdrawal?",
            "Can contribution weights define handoff without defining identity?",
            "Does long overlap provide evidence unavailable in an abrupt protocol, or merely more opportunity for external correction?",
            "What fails first when coupling is removed?",
        ],
        "blocked_inferences": ["Long overlap is not autonomy.", "Continuous coupling is not one carrier unless explicitly retyped.", "Target dominance is not exclusive realization.", "Adaptive correction can be externally supplied."],
        "asset_focus": ["A-AG-01", "A-PT-01", "A-TM-01", "A-CU-01", "A-EV-01"],
        "question_focus": ["Q-BRG-006", "Q-TYP-007", "Q-AUT-001", "Q-AUT-004", "Q-BRG-005"],
    },
    {
        "id": "S08", "number": 8, "title": "Distributed extension with no sharp handoff",
        "canonical_prompt": "Distributed extension in which no sharp handoff exists.",
        "purpose": "Challenge source-target narratives that require an exclusive transfer instant when a package remains jointly distributed.",
        "facts": [
            "A source package is extended onto additional target-side support while source-side support remains a permanent active component.",
            "No stage is designated as the unique handoff or as a target-only episode.",
            "The declared package is jointly organized across supports and may fail if either side is removed.",
            "Operational responsibility changes, but the joint boundary remains the candidate package boundary.",
        ],
        "episode_graph": "E_S -> E_joint -> E_joint' -> ... (no target-only node stipulated)",
        "carrier_relation": "partially_overlapping_support", "change_mode": "distributed_extension", "source_fate": "remains_coupled",
        "target_timing": "continuous_overlap", "branching": "many_to_many", "bridge_dependence": "permanent",
        "fidelity": "adaptive", "reversibility": "approximately_reversible", "route_multiplicity": "multiple_equivalent_routes", "granularity": "package_state",
        "secondary_modes": "live_migration", "cross_carrier_status": "boundary_cross_carrier_distributed", "handoff_shape": "no_sharp_handoff",
        "branch_graph": "one joint distributed package assembled from multiple support episodes", "clock_relation": "partially synchronized distributed clocks",
        "causal_structure": "permanent joint causal organization",
        "fidelity_scope": "joint package behavior; no target-only package is stipulated",
        "autonomy_intervention": "remove one support partition at a time and test whether the remaining assembly still satisfies the declared package",
        "instrument_constraints": "observations of the joint assembly may not localize package predicates to either support",
        "variants": ["redundant versus nonredundant distribution", "source contribution tends to zero without reaching zero", "joint package with modular versus inseparable clauses"],
        "primary_discriminators": ["D03", "D04", "D05", "D06", "D08", "D10"],
        "stress_questions": [
            "Must a candidate force this case into source and target tokens, or may the joint package be the only valid object?",
            "Is lineage applicable when no target-only episode exists?",
            "Does permanent bridge dependence indicate failure, or simply define the distributed package boundary?",
            "How are C-clause carriers typed when different clauses live on different supports?",
        ],
        "blocked_inferences": ["No sharp handoff does not imply no structural change.", "Permanent coupling is not automatically counterfeit.", "Distributed realization does not specify one or many subjects.", "A joint carrier cannot be assumed without declaring its support and interfaces."],
        "asset_focus": ["A-CT-01", "A-LG-01", "A-EV-01", "A-AG-01", "A-TM-01"],
        "question_focus": ["Q-TYP-007", "Q-LIN-008", "Q-AUT-001", "Q-PRS-005", "Q-BRG-002"],
    },
    {
        "id": "S09", "number": 9, "title": "Fission followed by independent divergence",
        "canonical_prompt": "Fission followed by independent divergence.",
        "purpose": "Force relation-valued or branch-sensitive lineage semantics and expose the loss of a single future after a common split.",
        "facts": [
            "One source episode produces two target episodes exact at the declared package state at the split.",
            "The source-side episode is then removed, and the two targets receive different admissible continuations.",
            "Branch histories diverge in predictive state, action-credit ledger, and possibly viability outcomes.",
            "No later fusion is stipulated.",
        ],
        "episode_graph": "E_S -> {E_T1^0, E_T2^0} -> {E_T1^1, E_T2^1} (divergent)",
        "carrier_relation": "disjoint_support", "change_mode": "nondestructive_copy", "source_fate": "erased_after_activation",
        "target_timing": "continuous_overlap", "branching": "one_to_many", "bridge_dependence": "temporary",
        "fidelity": "exact", "reversibility": "irreversible", "route_multiplicity": "unique_route", "granularity": "package_state",
        "secondary_modes": "fission", "cross_carrier_status": "genuine_cross_carrier_candidate", "handoff_shape": "branching_handoff",
        "branch_graph": "1->2 with independent post-split histories", "clock_relation": "common split coordinate followed by independent clocks",
        "causal_structure": "shared prehistory, equal split ancestry, then causally separate branches",
        "fidelity_scope": "exact at branch point; divergence is stipulated afterward",
        "autonomy_intervention": "remove common bridge and source resources, then test branches independently",
        "instrument_constraints": "both branch histories and target package records are available",
        "variants": ["symmetric versus asymmetric post-split environments", "one branch later fails viability", "branches retain versus erase common-prehistory markers"],
        "primary_discriminators": ["D01", "D04", "D05", "D06", "D10"],
        "stress_questions": [
            "Can one source have two legitimate successors without violating the candidate's ontology-free structural rules?",
            "Which common-prehistory facts remain well-defined after divergent futures?",
            "Does branch failure affect the status of the other branch?",
            "Can action-credit be duplicated, divided, or only related by ancestry?",
        ],
        "blocked_inferences": ["Fission does not force a function-valued lineage.", "Divergence does not retroactively remove common ancestry.", "One branch's failure does not select the other as uniquely original.", "Shared prehistory is not shared token identity."],
        "asset_focus": ["A-OP-01", "A-RE-01", "A-PQ-01", "A-CU-01"],
        "question_focus": ["Q-LIN-006", "Q-PRS-009", "Q-PRS-007", "Q-LIN-002", "Q-LIN-009"],
    },
    {
        "id": "S10", "number": 10, "title": "Fission followed by later fusion",
        "canonical_prompt": "Fission followed by later fusion.",
        "purpose": "Probe whether branch histories and recombination content can be coherently merged, lost, or retained in a many-to-one target.",
        "facts": [
            "One source fissions into two exact-at-split branches that later acquire nonidentical histories.",
            "A fusion bridge combines both branch records/processes into one target episode.",
            "The target may match selected branchwise summaries while joint/recombination facts remain a separate question.",
            "The two branch episodes are retired after fusion.",
        ],
        "episode_graph": "E_S -> {E_B1, E_B2} -> E_F",
        "carrier_relation": "disjoint_support", "change_mode": "abrupt_translation", "source_fate": "erased_after_activation",
        "target_timing": "continuous_overlap", "branching": "many_to_one", "bridge_dependence": "temporary",
        "fidelity": "adaptive", "reversibility": "irreversible", "route_multiplicity": "holonomy_bearing_routes", "granularity": "event_package",
        "secondary_modes": "fission;fusion;recombination", "cross_carrier_status": "genuine_cross_carrier_candidate", "handoff_shape": "branch_then_fusion",
        "branch_graph": "1->2->1 with route-sensitive branch histories", "clock_relation": "branch-local clocks require a fusion synchronization/ordering rule",
        "causal_structure": "two causally independent branch histories jointly feed one fusion process",
        "fidelity_scope": "adaptive event/package synthesis from two nonidentical branch histories",
        "autonomy_intervention": "retire both branch sources and fusion controller, then test the fused target",
        "instrument_constraints": "branchwise summaries may be observable while cross-branch recombination content may require privileged audit",
        "variants": ["compatible versus conflicting action-credit ledgers", "fusion order B1-then-B2 versus B2-then-B1", "lossless versus lossy branch-history merge"],
        "primary_discriminators": ["D02", "D04", "D05", "D06", "D07", "D10"],
        "stress_questions": [
            "What source-specific facts can the fused target inherit when branch histories conflict?",
            "Does fusion order create holonomy or different target package states?",
            "Can pairwise branch-to-target matches exist without one globally coherent fusion package?",
            "Does the lineage relation allow multiple predecessors without asserting token identity with all of them?",
        ],
        "blocked_inferences": ["Fusion is not identity with every source branch.", "Matching branchwise summaries is not preservation of recombination content.", "A single final target does not make the route one-to-one.", "Conflict resolution is a substantive rule, not a bookkeeping detail."],
        "asset_focus": ["A-RE-01", "A-OP-01", "A-LG-01", "A-HO-01", "A-CF-01"],
        "question_focus": ["Q-LIN-007", "Q-PRS-009", "Q-RTE-002", "Q-PRS-007", "Q-PRS-005"],
    },
    {
        "id": "S11", "number": 11, "title": "Public-perfect copy with predictive mismatch",
        "canonical_prompt": "Public/report-perfect copy with predictive mismatch.",
        "purpose": "Serve as a counterfeit control demonstrating that current/report equivalence can leave future-sufficient structure different.",
        "facts": [
            "A disjoint target matches every declared current public/report observable of the source over the stipulated test set.",
            "A privileged continuation test reveals different predictive classes or transition responses.",
            "The source remains active so both systems can be probed under matched and divergent continuations.",
            "The mismatch is a scenario input fact, not an outcome label or ontological judgment.",
        ],
        "episode_graph": "E_S -> {E_S^+, E_T^+}; public(E_S^+)=public(E_T^+), predictive(E_S^+)!=predictive(E_T^+)",
        "carrier_relation": "disjoint_support", "change_mode": "nondestructive_copy", "source_fate": "persists",
        "target_timing": "continuous_overlap", "branching": "one_to_many", "bridge_dependence": "removable",
        "fidelity": "lossy", "reversibility": "irreversible", "route_multiplicity": "unique_route", "granularity": "predictive_state",
        "secondary_modes": "counterfeit_public_matching", "cross_carrier_status": "genuine_cross_carrier_negative_control", "handoff_shape": "copy_without_predictive_transport",
        "branch_graph": "source plus one public-matching target", "clock_relation": "matched public test times plus privileged continuation probes",
        "causal_structure": "copy process followed by independent counterfactual probing",
        "fidelity_scope": "exact public/report equivalence; explicitly nonexact predictive state",
        "autonomy_intervention": "remove source and bridge, then test whether target's own predictive dynamics produce the declared package",
        "instrument_constraints": "public instruments cannot detect the stipulated mismatch; privileged predictive probes can",
        "variants": ["mismatch visible only after long horizon", "mismatch under rare intervention", "expanded public interface that does or does not dissolve hiddenness"],
        "primary_discriminators": ["D01", "D02", "D08", "D09", "D10"],
        "stress_questions": [
            "Which candidate criteria incorrectly collapse public and predictive equivalence?",
            "Can a recognition protocol detect the mismatch without complete-state access?",
            "Does predictive mismatch defeat target package status, transport only, lineage only, or different lanes under different candidates?",
            "How does interface expansion change the classification?",
        ],
        "blocked_inferences": ["Public perfection is not predictive equivalence.", "A hidden mismatch does not by itself decide all C-clauses.", "Counterfeit is a named structural control, not a claim of phenomenal absence.", "Behavioral indistinguishability under one test set is not global identity."],
        "asset_focus": ["A-PQ-01", "A-HID-01", "A-NO-01", "A-EX-01", "A-CD-01"],
        "question_focus": ["Q-PRS-003", "Q-OBS-003", "Q-OBS-006", "Q-OBS-007", "Q-RTE-005"],
    },
    {
        "id": "S12", "number": 12, "title": "Predictive match with different binding or action-credit structure",
        "canonical_prompt": "Predictive match with different binding or action-credit structure.",
        "purpose": "Prevent predictive equivalence from being silently upgraded to full package equivalence or preserved mineness/provenance.",
        "facts": [
            "A disjoint target matches the source's declared predictive quotient and transition responses.",
            "Privileged audit shows a different binding relation, action-credit ledger, or source-provenance structure.",
            "The source remains active during comparison.",
            "The mismatch concerns a named package clause or cross-clause relation, not an untyped essence.",
        ],
        "episode_graph": "E_S -> {E_S^+, E_T^+}; predictive-match; binding/credit-mismatch",
        "carrier_relation": "disjoint_support", "change_mode": "abrupt_translation", "source_fate": "persists",
        "target_timing": "continuous_overlap", "branching": "one_to_many", "bridge_dependence": "removable",
        "fidelity": "lossy", "reversibility": "irreversible", "route_multiplicity": "unique_route", "granularity": "predictive_state",
        "secondary_modes": "nondestructive_copy", "cross_carrier_status": "genuine_cross_carrier_negative_control", "handoff_shape": "predictive_match_with_package_mismatch",
        "branch_graph": "source plus one predictive-matching target", "clock_relation": "matched continuation indexing; ledger histories separately indexed",
        "causal_structure": "copy/translation preserves declared predictive law but changes internal package organization",
        "fidelity_scope": "exact predictive dynamics; explicitly nonexact binding or action-credit structure",
        "autonomy_intervention": "remove source/bridge and test whether target maintains its own (possibly different) package organization",
        "instrument_constraints": "predictive interface alone cannot detect the stipulated binding/credit mismatch",
        "variants": ["binding differs but credit matches", "credit differs but binding matches", "current and predictive interfaces both match while cross-clause glue fails"],
        "primary_discriminators": ["D01", "D04", "D06", "D08", "D10"],
        "stress_questions": [
            "Is predictive equivalence necessary, sufficient, or neither for the candidate's transported object?",
            "Which package clauses must be preserved versus rebuilt?",
            "Can a lineage criterion ignore provenance/action-credit without becoming insensitive to source history?",
            "Does target-native autonomy compensate for a source-relative package mismatch?",
        ],
        "blocked_inferences": ["Predictive equivalence is not full C-package equivalence.", "Matching futures does not preserve action-credit by definition.", "Different binding is not necessarily no target package; it may be a different package.", "Target autonomy does not repair lineage automatically."],
        "asset_focus": ["A-PQ-01", "A-CT-01", "A-OP-01", "A-EV-01", "A-LG-01"],
        "question_focus": ["Q-PRS-004", "Q-PRS-005", "Q-PRS-007", "Q-LIN-003", "Q-ASM-005"],
    },
    {
        "id": "S13", "number": 13, "title": "Target maintained only by an external decoder or source process",
        "canonical_prompt": "Target maintained only by an external decoder or source process.",
        "purpose": "Distinguish target-native realization and autonomy from an externally generated readout or continuously reconstructed shadow.",
        "facts": [
            "A disjoint target-facing interface produces the declared public/certificate outputs only while a continuing source process or external decoder runs.",
            "Removing that decoder/source process causes the target-facing package predicate to fail or become undefined by construction.",
            "The target carrier alone need not contain the predictive, repair, or audit structure used to generate the outputs.",
            "The coupled assembly may still be a legitimate distributed object under a separately declared boundary.",
        ],
        "episode_graph": "E_S + decoder D -> interface episode E_T^shadow; remove(D or E_S) -> no stipulated target package",
        "carrier_relation": "disjoint_support", "change_mode": "distributed_extension", "source_fate": "remains_coupled",
        "target_timing": "continuous_overlap", "branching": "one_to_one", "bridge_dependence": "externally_decoded",
        "fidelity": "lossy", "reversibility": "reversible", "route_multiplicity": "unique_route", "granularity": "certificate_only",
        "secondary_modes": "external_readout", "cross_carrier_status": "genuine_cross_carrier_autonomy_control", "handoff_shape": "no_completed_handoff",
        "branch_graph": "one source-driven output episode labeled target-facing", "clock_relation": "decoder schedule mediates timing",
        "causal_structure": "continuing source/decoder causally generates target outputs",
        "fidelity_scope": "certificate/public output fidelity only; target-native structure explicitly left absent or unspecified",
        "autonomy_intervention": "remove source process and decoder separately, then jointly; retain ordinary target environment",
        "instrument_constraints": "public observation of the target-facing interface may not reveal where the determining state lives",
        "variants": ["decoder stateless versus stateful", "decoder later internalized into target", "source removed while decoder retains a finite model versus live source dependence"],
        "primary_discriminators": ["D02", "D03", "D05", "D06", "D08"],
        "stress_questions": [
            "Is the relevant package instantiated on the target, on the source-decoder-target assembly, or nowhere under the candidate?",
            "Which withdrawal distinguishes readout from target-native maintenance?",
            "Can decoder internalization convert a shadow into an autonomous target without deciding lineage?",
            "Does the candidate's bridge definition explicitly expose all ongoing dependencies?",
        ],
        "blocked_inferences": ["Correct output is not target-native realization.", "Bridge dependence is not phenomenal nonrealization by definition.", "A coupled assembly may require a different carrier boundary.", "Removing a decoder tests autonomy, not source-target lineage."],
        "asset_focus": ["A-EX-01", "A-AG-01", "A-PT-01", "A-QEC-01", "A-NO-01"],
        "question_focus": ["Q-BRG-006", "Q-AUT-001", "Q-AUT-003", "Q-AUT-004", "Q-OBS-003"],
    },
    {
        "id": "S14", "number": 14, "title": "Closed route restoring current observables but changing predictive state",
        "canonical_prompt": "Route loop that restores every current observable while changing predictive state.",
        "purpose": "Expose route holonomy and block endpoint-current equality from erasing memory or continuation-relevant route effects.",
        "facts": [
            "A route leaves a source carrier, passes through a disjoint target/intermediate carrier, and returns to the source-side carrier type.",
            "Every declared current/public observable at the endpoint equals its initial value.",
            "A privileged continuation test shows a changed predictive class, memory residue, or route-sensitive package coordinate.",
            "The loop action is a stipulated scenario fact; its significance for transport or lineage is candidate-dependent.",
        ],
        "episode_graph": "E_S^0 -> E_T -> E_S^1; public(E_S^1)=public(E_S^0), predictive(E_S^1)!=predictive(E_S^0)",
        "carrier_relation": "disjoint_support", "change_mode": "live_migration", "source_fate": "paused",
        "target_timing": "delayed_activation", "branching": "one_to_one", "bridge_dependence": "temporary",
        "fidelity": "lossy", "reversibility": "approximately_reversible", "route_multiplicity": "holonomy_bearing_routes", "granularity": "predictive_state",
        "secondary_modes": "round_trip", "cross_carrier_status": "genuine_cross_carrier_route_control", "handoff_shape": "out_and_back_loop",
        "branch_graph": "one operational route with common start/end carrier type", "clock_relation": "closed route with possible phase/memory offset",
        "causal_structure": "sequential cross-carrier route returning to an endpoint-current-equivalent state",
        "fidelity_scope": "exact current observables at loop closure; explicitly nonexact predictive state",
        "autonomy_intervention": "remove intermediate bridge after return and test persistence of the route-induced residue",
        "instrument_constraints": "current public instruments are blind to the stipulated holonomy; predictive probes reveal it",
        "variants": ["different loop orders", "residue erased by repair versus persistent", "same predictive class but changed action-credit ledger"],
        "primary_discriminators": ["D01", "D02", "D03", "D07", "D09"],
        "stress_questions": [
            "What equivalence relation, if any, makes the round trip an identity bridge?",
            "Can route-sensitive memory coexist with a useful route-independent transport theorem on a coarser object?",
            "Does a nonzero loop residue affect lineage, only transported state, or neither under a candidate?",
            "Which critical-pair or flatness condition would exclude this scenario?",
        ],
        "blocked_inferences": ["Restored current observables are not full restoration.", "Approximate inverse is not route independence.", "Holonomy is not automatically failure; it must be interpreted relative to the object.", "A loop endpoint on the same carrier is not token identity by notation alone."],
        "asset_focus": ["A-HO-01", "A-CF-01", "A-PQ-01", "A-TM-01"],
        "question_focus": ["Q-RTE-001", "Q-RTE-002", "Q-RTE-003", "Q-RTE-005", "Q-BRG-007"],
    },
    {
        "id": "S15", "number": 15, "title": "Local pairwise matches without a global package",
        "canonical_prompt": "Local pairwise matches that fail to glue into one global identity package.",
        "purpose": "Test local-to-global obstruction: accepted pairwise bridge records need not form one coherent target event/package object.",
        "facts": [
            "Multiple source-side clauses/events are paired with multiple target-side clauses/events by locally accepted records.",
            "Every pairwise test passes at its declared local scope.",
            "The overlaps/cycle constraints are stipulated inconsistent, so no one global event/package satisfies all local records simultaneously.",
            "The scenario does not stipulate whether a weaker partial target package exists.",
        ],
        "episode_graph": "{local E_Si -> E_Tj records}; all local gates pass; global glue obstruction != 0",
        "carrier_relation": "partially_overlapping_support", "change_mode": "distributed_extension", "source_fate": "remains_coupled",
        "target_timing": "continuous_overlap", "branching": "many_to_many", "bridge_dependence": "temporary",
        "fidelity": "lossy", "reversibility": "irreversible", "route_multiplicity": "multiple_equivalent_routes", "granularity": "event_package",
        "secondary_modes": "local_bridge_assembly", "cross_carrier_status": "genuine_cross_carrier_global_glue_control", "handoff_shape": "multiple_local_handoffs_no_global_completion",
        "branch_graph": "many local source-target episode pairs with no global node", "clock_relation": "locally compatible timestamps with globally inconsistent cycle/order data",
        "causal_structure": "pairwise causal records without one coherent global causal package",
        "fidelity_scope": "exact local records; globally inconsistent package",
        "autonomy_intervention": "remove source/local coordinators and test whether any target-native global package remains",
        "instrument_constraints": "local audits pass; only a global consistency audit reveals the obstruction",
        "variants": ["time-cycle obstruction", "role/identity conflict", "binding/recombination conflict", "one additional global witness repairs the cover"],
        "primary_discriminators": ["D02", "D03", "D04", "D06", "D07", "D08"],
        "stress_questions": [
            "What gluing condition turns accepted local bridge records into one target event package?",
            "Can a candidate return partial target realization without pretending global coherence?",
            "Does the obstruction live in transport, target package, lineage, or several separately typed lanes?",
            "Can a route completion repair the obstruction without changing local records?",
        ],
        "blocked_inferences": ["Pairwise acceptance is not global package existence.", "A common label is not a glued identity object.", "Local time compatibility is not a global clock.", "A global failure does not erase valid local structures."],
        "asset_focus": ["A-LG-01", "A-EV-01", "A-CF-01", "A-RE-01", "A-AOR-01"],
        "question_focus": ["Q-PRS-005", "Q-BRG-008", "Q-RTE-003", "Q-TYP-009", "Q-AUT-001"],
    },
    {
        "id": "S16", "number": 16, "title": "Residual-bounded transfer near a viability boundary",
        "canonical_prompt": "Transfer near a viability boundary.",
        "purpose": "Test whether small structural defects can cause discontinuous maintenance failure near a threshold and whether scalar fidelity conceals dangerous directions.",
        "facts": [
            "A disjoint target is constructed with a declared nonzero residual bound relative to a source package.",
            "The source package lies near a declared viability/maintenance boundary.",
            "Admissible perturbations within the same residual budget can place the target on either side of that boundary.",
            "No stability theorem is stipulated.",
        ],
        "episode_graph": "E_S --bridge with defect <= epsilon--> E_T near boundary d(K)=delta",
        "carrier_relation": "disjoint_support", "change_mode": "abrupt_translation", "source_fate": "degrades",
        "target_timing": "delayed_activation", "branching": "one_to_one", "bridge_dependence": "temporary",
        "fidelity": "residual_bounded", "reversibility": "approximately_reversible", "route_multiplicity": "unique_route", "granularity": "package_state",
        "secondary_modes": "approximate_transfer", "cross_carrier_status": "genuine_cross_carrier_stability_control", "handoff_shape": "approximate_sharp_handoff",
        "branch_graph": "one source to one target with a defect set of possible endpoints", "clock_relation": "ordered activation; horizon required for maintenance",
        "causal_structure": "approximate bridge followed by target dynamics near a bifurcation/viability threshold",
        "fidelity_scope": "bounded package residual with direction-dependent viability consequences",
        "autonomy_intervention": "withdraw bridge and apply the declared disturbance class over the maintenance horizon",
        "instrument_constraints": "a small global residual score may not identify the component that crosses the viability boundary",
        "variants": ["different residual norms", "same epsilon with different error directions", "positive versus zero viability margin", "finite versus invariant-horizon autonomy"],
        "primary_discriminators": ["D02", "D05", "D08", "D09", "D10"],
        "stress_questions": [
            "Which metric controls the viability-relevant package directions?",
            "Can lineage classification be stable under perturbations away from but not near the boundary?",
            "What defect-composition law applies across multiple substrate changes?",
            "Does a small score hide a local catastrophic mismatch?",
        ],
        "blocked_inferences": ["Small residual is not harmlessness.", "Approximate preservation is not exact lineage.", "A scalar fidelity score may hide threshold-crossing components.", "Source viability margin does not automatically transport."],
        "asset_focus": ["A-AR-01", "A-CD-01", "A-VI-01", "A-QEC-01"],
        "question_focus": ["Q-APP-001", "Q-APP-003", "Q-APP-005", "Q-APP-007", "Q-AUT-002"],
    },
    {
        "id": "S17", "number": 17, "title": "Lossy transfer followed by endogenous repair",
        "canonical_prompt": "Lossy transfer followed by endogenous repair.",
        "purpose": "Separate preservation through the bridge from target-native recovery after a defect and ask what lineage does across a repair interval.",
        "facts": [
            "A disjoint target activates from a lossy record/bridge outside at least one desired package condition.",
            "A target-internal recovery process subsequently returns the target to the declared package/viability region.",
            "The source and transfer bridge are removed before or at the start of recovery.",
            "Recovery uses retained target resources and dynamics rather than continuing source reconstruction.",
        ],
        "episode_graph": "E_S -> E_T^defective --target-native repair--> E_T^recovered",
        "carrier_relation": "disjoint_support", "change_mode": "checkpoint_restart", "source_fate": "erased_before_activation",
        "target_timing": "delayed_activation", "branching": "one_to_one", "bridge_dependence": "removable",
        "fidelity": "error_corrected", "reversibility": "approximately_reversible", "route_multiplicity": "unique_route", "granularity": "package_state",
        "secondary_modes": "lossy_translation;endogenous_repair", "cross_carrier_status": "genuine_cross_carrier_repair_case", "handoff_shape": "defective_activation_then_recovery",
        "branch_graph": "one source to defective target to recovered target episode", "clock_relation": "repair interval explicitly represented in target local time",
        "causal_structure": "source-derived initialization followed by target-native recovery dynamics",
        "fidelity_scope": "lossy at activation; package/viability restored under a declared recovery map",
        "autonomy_intervention": "remove source, bridge, and external repair controller before recovery; retain target's encoded repair machinery and ordinary environment",
        "instrument_constraints": "the defective intermediate and recovery trajectory are auditable",
        "variants": ["repair before versus after full package failure", "unique versus multiple repaired attractors", "repair preserves versus rewrites action-credit/history"],
        "primary_discriminators": ["D02", "D04", "D05", "D06", "D08", "D09", "D10"],
        "stress_questions": [
            "Is lineage preserved through a period in which the target package predicate fails?",
            "Which structures are repaired versus newly instantiated?",
            "Does target-native recovery establish autonomy without establishing source-target continuity?",
            "Can repair reduce structural defect while altering route memory or action-credit?",
        ],
        "blocked_inferences": ["Repair is not proof that nothing was lost.", "Recovered package satisfaction is not bridge preservation.", "Endogenous repair supports autonomy but not lineage by default.", "A defective intermediate may matter even if the endpoint is exact."],
        "asset_focus": ["A-QEC-01", "A-VI-01", "A-AG-01", "A-AR-01", "A-OP-01"],
        "question_focus": ["Q-APP-004", "Q-AUT-004", "Q-RTE-007", "Q-LIN-011", "Q-PRS-007"],
    },
    {
        "id": "S18", "number": 18, "title": "Exact reversible round trip across carriers",
        "canonical_prompt": "Reversible round trip across substrates.",
        "purpose": "Provide a strong structural positive control for inverse bridges while keeping reversibility separate from lineage and ontology.",
        "facts": [
            "A source package is transported to a disjoint target and later returned through a declared inverse route.",
            "The round trip restores every named package-state structure exactly within the admitted domain.",
            "The source carrier is paused rather than destroyed while the target operates.",
            "No nontrivial holonomy is stipulated for the named structure, but unmeasured structures remain outside scope.",
        ],
        "episode_graph": "E_S^0 --B--> E_T --B^{-1}--> E_S^1 with named-structure equality",
        "carrier_relation": "disjoint_support", "change_mode": "live_migration", "source_fate": "paused",
        "target_timing": "delayed_activation", "branching": "one_to_one", "bridge_dependence": "removable",
        "fidelity": "exact", "reversibility": "reversible", "route_multiplicity": "multiple_equivalent_routes", "granularity": "package_state",
        "secondary_modes": "round_trip", "cross_carrier_status": "genuine_cross_carrier_positive_control", "handoff_shape": "out_and_back_with_declared_inverse",
        "branch_graph": "one operational route and one declared inverse", "clock_relation": "explicit time/phase translation with exact inverse on named structure",
        "causal_structure": "causal migration to target, target operation, causal return",
        "fidelity_scope": "exact preservation of a declared package-state family under B and B^{-1}",
        "autonomy_intervention": "while target is active, remove the source-side execution and bridge after handoff; later re-enable only the declared reverse bridge for return",
        "instrument_constraints": "complete access to the named transported structure is stipulated; ontology is not an instrument output",
        "variants": ["different exact routes with same endpoint", "long versus short target residence", "extra unmeasured memory coordinate to test scope honesty"],
        "primary_discriminators": ["D02", "D03", "D07", "D08", "D09", "D10"],
        "stress_questions": [
            "Does exact round-trip recovery imply forward target autonomy, or can the bridge carry the structure continuously?",
            "What is the maximal named object for which the inverse law holds?",
            "Can a lineage criterion remain route-sensitive even when structural transport is flat?",
            "Which claim lanes receive a positive control and which remain open?",
        ],
        "blocked_inferences": ["Reversibility is not token identity.", "A structural positive control is not an ontological demonstration.", "Exactness is scoped to named structures.", "An inverse route does not prove target-native maintenance."],
        "asset_focus": ["A-RT-01", "A-CF-01", "A-HO-01", "A-QEC-01", "A-AG-01"],
        "question_focus": ["Q-BRG-007", "Q-BRG-008", "Q-RTE-003", "Q-AUT-001", "Q-ASM-005"],
    },
    {
        "id": "S19", "number": 19, "title": "Target with a radically rescaled clock",
        "canonical_prompt": "Target running at a radically rescaled clock rate.",
        "purpose": "Force explicit clock translation and test whether continuity relies on a hidden canonical synchronized now.",
        "facts": [
            "A disjoint target implements the declared predictive/package dynamics under a non-unit, possibly nonlinear time reparameterization.",
            "Source and target local clocks cannot be identified pointwise without a supplied clock relation.",
            "The source is retired after target activation.",
            "Order of admissible events may be preserved even when durations and phases differ radically.",
        ],
        "episode_graph": "E_S(t_S) --B, theta--> E_T(t_T), with t_T=theta(t_S) or a partial-order relation",
        "carrier_relation": "disjoint_support", "change_mode": "live_migration", "source_fate": "erased_after_activation",
        "target_timing": "time_rescaled_activation", "branching": "one_to_one", "bridge_dependence": "temporary",
        "fidelity": "adaptive", "reversibility": "approximately_reversible", "route_multiplicity": "unique_route", "granularity": "predictive_state",
        "secondary_modes": "temporal_reparameterization", "cross_carrier_status": "genuine_cross_carrier_temporal_case", "handoff_shape": "clock_translated_handoff",
        "branch_graph": "one source episode to one target episode under clock translation", "clock_relation": "explicit non-unit map or order-preserving relation; no canonical simultaneity",
        "causal_structure": "causal transport with mismatched local rates and possible phase reset",
        "fidelity_scope": "predictive dynamics up to declared time reparameterization; temporal closure must be re-audited",
        "autonomy_intervention": "remove synchronization/clock-translation service and test target-local temporal closure",
        "instrument_constraints": "cross-carrier observations require a clock-comparison protocol that may itself introduce artifacts",
        "variants": ["constant speedup", "nonlinear but monotone reparameterization", "pauses/bursts preserving order", "clock map with holonomy around a round trip"],
        "primary_discriminators": ["D01", "D02", "D03", "D07", "D08", "D09"],
        "stress_questions": [
            "Which temporal structures require duration preservation versus only order/conjugacy?",
            "Does removal of an external synchronizer break target temporal closure?",
            "Can predictive equivalence be defined modulo time reparameterization without erasing causally relevant delays?",
            "How are handoff and autonomy horizons translated between clocks?",
        ],
        "blocked_inferences": ["Different clock rate is not different lineage by definition.", "Equal event order is not equal temporal closure.", "A synchronization protocol is not a canonical now.", "Time rescaling exactness is scoped to a declared conjugacy."],
        "asset_focus": ["A-TM-01", "A-RT-01", "A-HO-01", "A-PT-01"],
        "question_focus": ["Q-TYP-008", "Q-PRS-008", "Q-RTE-003", "Q-AUT-002", "Q-BRG-005"],
    },
    {
        "id": "S20", "number": 20, "title": "Pure representation or gauge change on one carrier",
        "canonical_prompt": "A pure representation/gauge change that should not count as movement to a new carrier.",
        "purpose": "Provide the carrier-distinctness negative control and detect criteria that manufacture migration by relabeling one fixed support.",
        "facts": [
            "One support, dynamics, resource law, and implementation map are retained.",
            "Only coordinates, labels, gauge, serialization, or presentation change through an exactly invertible translation.",
            "No separately typed target implementation or support is introduced.",
            "Every named package structure is preserved under the representation isomorphism.",
        ],
        "episode_graph": "E_S --representation isomorphism--> E_S' (same carrier token/support)",
        "carrier_relation": "same_support_reencoding", "change_mode": "abrupt_translation", "source_fate": "persists",
        "target_timing": "continuous_overlap", "branching": "one_to_one", "bridge_dependence": "removable",
        "fidelity": "exact", "reversibility": "reversible", "route_multiplicity": "multiple_equivalent_routes", "granularity": "microstate",
        "secondary_modes": "gauge_change", "cross_carrier_status": "same_carrier_negative_control", "handoff_shape": "no_carrier_handoff",
        "branch_graph": "one carrier episode in two representations", "clock_relation": "identical operational clock modulo notation",
        "causal_structure": "same physical/formal process viewed through an invertible representation change",
        "fidelity_scope": "exact representation isomorphism on all named structures",
        "autonomy_intervention": "not a source-target autonomy test; removing the translator tests interface availability only",
        "instrument_constraints": "all differences are stipulated representational; any criterion detecting a new carrier must identify an additional nonrepresentational fact",
        "variants": ["state renaming", "gauge transformation", "lossless serialization change", "same hardware with different software display format"],
        "primary_discriminators": ["D02", "D03", "D07", "D09", "D10"],
        "stress_questions": [
            "Does the candidate pass the carrier-distinctness audit before applying a cross-carrier verdict?",
            "Can it distinguish an isomorphism within one carrier from a bridge between carriers?",
            "Which alleged substrate fact survives erasing labels and coordinate choices?",
            "Does the candidate return not-applicable rather than claiming successful migration?",
        ],
        "blocked_inferences": ["A new representation is not a new carrier by declaration alone.", "Exact isomorphism is not evidence of substrate independence.", "Same-carrier persistence is not cross-carrier transport.", "The control does not deny that representation changes can be scientifically useful."],
        "asset_focus": ["A-FS-01", "A-PR-01", "A-ON-01"],
        "question_focus": ["Q-TYP-003", "Q-TYP-004", "Q-TYP-009", "Q-CORE-002", "Q-ASM-003"],
    },
]

# The governing plan requires the first twenty canonical cases.  Fifteen
# supplemental controls close protocol/failure-mode gaps without assigning any
# transfer or lineage verdict.
SCENARIOS.extend(SUPPLEMENTAL_SCENARIOS)
CANONICAL_COUNT = 20
SUPPLEMENTAL_COUNT = len(SUPPLEMENTAL_SCENARIOS)
assert len(SCENARIOS) == 35, len(SCENARIOS)
assert [s["number"] for s in SCENARIOS] == list(range(1, 36))

CORE_QUESTIONS = [f"Q-CORE-{i:03d}" for i in range(1, 13)]


def scenario_probe(s: dict[str, Any], d: dict[str, Any]) -> str:
    sid = d["id"]
    context = f"Given {s['title'].lower()}, with {s['source_fate'].replace('_', ' ')} source fate and {s['fidelity'].replace('_', ' ')} fidelity at {s['granularity'].replace('_', ' ')} granularity"
    templates = {
        "D01": f"{context}, which source predictive fibers have target counterparts, and what continuation test would expose a mismatch?",
        "D02": f"{context}, does the candidate act on histories/transition laws or only endpoints, and are continuation matches admissible and compositional?",
        "D03": f"{context}, what causal coupling and clock relation spans the operational episodes, including any overlap, pause, gap, or external schedule?",
        "D04": f"{context}, what branchwise or joint information survives, and can local matches be glued into one package without adding a new axiom?",
        "D05": f"{context}, how are viability margin, resource ledger, repair apparatus, and maintenance obligations translated through handoff?",
        "D06": f"{context}, which episode receives credit/provenance for actions and maintenance, and does that allocation change under source deletion or relabeling?",
        "D07": f"{context}, do alternative routes or a round trip change a named predictive, temporal, memory, or lineage coordinate?",
        "D08": f"{context}, what happens after the scenario's withdrawal intervention `{s['autonomy_intervention']}`?",
        "D09": f"{context}, what exact equality or defect is being measured, how does it compose, and is the threshold stable near package/viability boundaries?",
        "D10": f"{context}, does the criterion return zero, one, many, fused, not-applicable, or underdetermined successors, and what data justify that cardinality?",
    }
    return templates[sid]


def relevance_for(s: dict[str, Any], d_id: str) -> str:
    if d_id in s["primary_discriminators"]:
        return "primary"
    # Preserve all ten discriminators while signaling lower leverage.
    if d_id in {"D08", "D10"}:
        return "mandatory"
    return "secondary"


def axis_dictionary_md() -> str:
    lines = [
        "# Protocol-axis dictionary",
        "",
        "**Status:** neutral scenario bookkeeping for CST-EXP-02; not a transfer criterion.",
        "",
        "Each axis records a stipulated feature of an operational protocol. Axis values are deliberately independent: no value carries a target-package, lineage, autonomy, recognition, or ontological verdict. Composite cases use one primary value plus a `secondary_change_modes` note in the matrix.",
        "",
    ]
    for i, (axis, spec) in enumerate(AXES.items(), 1):
        lines += [f"## {i}. `{axis}`", "", spec["question"], "", "| Value | Neutral meaning |", "|---|---|"]
        for value, meaning in spec["values"].items():
            lines.append(f"| `{value}` | {meaning} |")
        lines += ["", f"**Blocked inference:** {spec['blocked']}", ""]
    lines += [
        "## Independence audit",
        "",
        "A well-formed scenario must permit at least the following counter-combinations in principle:",
        "",
        "- gradual + branch-valued, gradual + no-lineage, and gradual + underdetermined outcomes;",
        "- destructive + positive, destructive + negative, and destructive + underdetermined outcomes;",
        "- exact + no target package at a finer granularity;",
        "- permanent bridge + valid distributed package, or permanent bridge + bridge-dependent shadow, depending boundary;",
        "- reversible transport + route-sensitive lineage;",
        "- public exactness + predictive mismatch;",
        "- predictive exactness + binding/action-credit mismatch; and",
        "- same-support re-encoding + `not_applicable_same_carrier` for cross-carrier candidates.",
        "",
        "If a candidate makes any of these combinations impossible, that restriction must be a visible theorem/definition of the candidate rather than an assumption hidden in the axis vocabulary.",
    ]
    return "\n".join(lines)


def neutral_schema_md() -> str:
    return dedent("""
    # Neutral source–target frame

    **Phase:** CST-EXP-02
    **Status:** bookkeeping schema; no preferred bridge, transported object, lineage criterion, or scenario verdict
    **Primary lanes:** methodological (`M`) with empty evaluation slots for `S-T`, `S-R`, `S-L`, `A`, and `R`

    ## 1. Purpose

    The frame makes heterogeneous transfer protocols comparable before the project chooses what, if anything, is transported. It records carrier episodes, package candidates, interfaces, route stages, overlap, handoff, source fate, target timing, branching/merging topology, bridge dependencies, and withdrawal tests. It **does not** contain a shared subject, identity token, or lineage edge.

    A compact visual of the frame is available as [SVG](neutral_transfer_frame.svg) and [PNG](neutral_transfer_frame.png); the editable source is [`neutral_transfer_frame.dot`](neutral_transfer_frame.dot).

    The decisive neutrality rule is:

    > An operational protocol edge records causal, informational, resource, or construction dependence. It is never a lineage edge merely because it points from a source episode to a target episode.

    A later candidate supplies a criterion `κ`; only then may a separate lineage graph be computed.

    ## 2. Separately typed records

    A scenario frame may be written schematically as:

    ```text
    NeutralScenarioFrame F = (
      carrier_specs       : {Σ_i : CarrierSpec},
      support_relations   : typed relations among support components,
      package_candidates  : {P_e : PackageCandidate(Σ_e)},
      package_status      : candidate/component/full/empty/unknown per episode,
      public_interfaces   : {I_pub,e},
      predictive_interfaces : {I_pred,e},
      privileged_audits   : {I_audit,e},
      local_times         : {T_e, ≤_e},
      clock_relation      : optional Θ among local times and route stages,
      operational_episodes: nodes E of a protocol graph G_op,
      protocol_stages     : typed edges R of G_op,
      responsibility      : allocation r(stage, clause/function, support),
      overlap_record      : optional jointly active interval/region Ω,
      handoff_record      : start/completion/absence plus operational success tests,
      branch_merge_shape  : cardinality/topology of G_op,
      dependencies        : source/bridge/decoder/controller/environment resources,
      withdrawal_tests    : interventions J with retained environment and horizon,
      instrument_set      : declared observations and inaccessible structure,
      scenario_facts      : stipulated inputs only,
      criterion_slots     : empty transport/target/lineage/autonomy/recognition fields,
      blocked_inferences  : scenario-specific anti-conflation rules
    )
    ```

    Source and target designations are **roles in a protocol**, not a pre-existing identity relation. In distributed or round-trip cases there may be several target-side episodes, no target-only episode, or a return to the original carrier type.

    ## 3. Operational episode graph versus lineage graph

    `G_op` is built before any candidate criterion. Its nodes are operational episodes such as source-active, mixed-support, record-only, target-active, branch, fusion, or empty-package episodes. Edges may mean scan, copy, causal influence, resource transfer, reconstruction, synchronization, repair, retirement, or representation translation.

    A later candidate defines:

    ```text
    κ : (F, candidate data) -> G_κ
    ```

    where `G_κ` may contain zero, one, many, or fused lineage edges. There is no requirement that `G_κ` reproduce `G_op`. For example:

    - one copy edge in `G_op` may yield two lineage successors, no successor, or underdetermination;
    - a record-mediated edge may yield structural transport but no lineage;
    - a permanently distributed episode may make target-only lineage not applicable;
    - a same-carrier representation edge may be outside a cross-carrier candidate's domain.

    ## 4. Package status and empty stages

    Every operational episode has a package-status field independent of its existence as a carrier episode:

    ```text
    unknown
    candidate_only
    component_witnesses_only
    simplified_certificate_satisfied
    full_C_package_satisfied
    empty_after_declared_failure
    not_applicable
    ```

    The frame permits routes through an interval where no full package is stipulated. That permission is bookkeeping only. A later criterion must say whether such a route is admissible for transport or lineage.

    ## 5. Interfaces and instruments

    A scenario distinguishes at least:

    - current/public interfaces;
    - predictive/continuation interfaces;
    - privileged audit interfaces;
    - complete-state access, when intentionally stipulated in a finite thought model.

    A fact such as “public-perfect” is always indexed to a declared interface/test family. It does not imply predictive or package equivalence. Instrumental underdetermination is recorded separately from structural underdetermination.

    ## 6. Histories and local clocks

    Source, bridge, and target histories may have distinct index sets. The neutral frame uses an optional relation `Θ`, not an assumed canonical synchronized `now`:

    ```text
    Θ ⊆ T_source × T_route × T_target
    ```

    `Θ` may be a function, partial relation, order embedding, time reparameterization, or left unspecified. Temporal overlap, a dormant gap, and time rescaling are protocol facts; none defines continuation.

    ## 7. Support overlap and responsibility

    During overlap, the frame records which support contributes to which package clause/function at each stage. A useful neutral form is:

    ```text
    r : Stage × ClauseOrFunction × SupportComponent -> ContributionRecord
    ```

    Contribution records can state causal role, resource provision, repair authority, clocking, audit, and whether a function would survive removal of that contributor. They do not sum to a subject or identity object.

    ## 8. Handoff

    A handoff record contains:

    ```text
    start_condition
    completion_condition or `no_sharp_handoff`
    responsibility changes
    source-retirement condition
    target-activation condition
    operational success tests
    dependencies still present
    ```

    Handoff is therefore a protocol interval/event, not the answer to “when did the same subject move?” Distributed scenarios may have no sharp handoff; copy scenarios may have a split rather than an exclusive handoff.

    ## 9. Branching and merging

    The neutral branch/merge field records only operational cardinality: `1→1`, `1→n`, `m→1`, or `m→n`. It can also record internal topology such as `1→2→1`. A later lineage criterion must independently return a lineage cardinality and explain any difference from the operational topology.

    ## 10. Fidelity and granularity

    Scenario fidelity is always a pair:

    ```text
    (quality class, comparison granularity)
    ```

    Examples include exact microstate record, exact predictive dynamics, residual-bounded package state, exact local event records with failed global glue, and certificate-only public match. No cross-granularity upgrade is licensed without a theorem.

    ## 11. Withdrawal and autonomy

    Every scenario contains an intervention slot:

    ```text
    J = (removed resources, retained environment, disturbance class, horizon/closure condition)
    ```

    The scenario may expose a removable bridge without stipulating the outcome. A later candidate must distinguish:

    - bridge scheduled to end;
    - bridge technically removable;
    - target package surviving removal;
    - a permanently distributed package whose declared boundary includes the bridge.

    ## 12. Typed candidate verdict record

    A candidate must populate a vector, not one metaphysically loaded label:

    ```text
    Verdict(F, candidate) = (
      v_ST : transport label,
      v_SR : target-package label,
      v_SL : lineage label,
      v_A  : autonomy label,
      v_R  : instrument/recognition label,
      assumptions_spent,
      underdetermination_basis,
      blocked_inferences,
      evidence/proof status
    )
    ```

    The outcome taxonomy supplies permitted labels. Ontological or personal-identity readings are not fields in this scenario verdict; they require separate `O` claims and named assumptions.

    ## 13. Scenario facts versus criterion outputs

    **Facts** are stipulated to define the thought experiment: number of targets, source deletion timing, exactness at a named granularity, existence of a predictive mismatch, or presence of a global-glue obstruction.

    **Outputs** are what a candidate decides: whether its transported object survives, whether a target package exists, how lineage is classified, whether post-withdrawal autonomy holds, and whether instruments can determine those facts.

    No card pre-fills an output vector. Even a negative-control scenario fixes only the control fact it is designed to expose.

    ## 14. Well-typed comparison rules

    - Never write `P_S = P_T` across distinct carriers without a common type or relation.
    - Never infer a history bridge from a state map without defining continuation compatibility.
    - Never infer global package existence from local bridge records without a gluing law.
    - Never infer lineage from source fate, overlap duration, exactness, or reversibility alone.
    - Never treat external decoding as target-native closure without a withdrawal audit.
    - Never treat a pure re-encoding as cross-carrier movement without passing the distinctness audit.

    ## 15. Nonclaims

    This schema does not define consciousness, personal identity, survival, death, uploading, or substrate indifference. It does not choose a transported object, a bridge morphology, a lineage relation, an autonomy horizon, a recognition protocol, or an ontology. It is a common language in which competing candidates can later disagree precisely.
    """)


def outcome_taxonomy_md() -> str:
    lines = [
        "# Typed outcome taxonomy",
        "",
        "**Status:** candidate-output vocabulary; no scenario is preclassified.",
        "",
        "## 1. Vector rule",
        "",
        "A candidate returns one label in each applicable lane (`S-T`, `S-R`, `S-L`, `A`, `R`). A flat verdict such as “successful upload,” “same person,” “mere copy,” or “death” is not permitted. Composite phrases from the governing plan are retained as aliases for typed vectors, not as primitive labels.",
        "",
        "| ID | Lane | Canonical label | Neutral meaning | Blocked inference |",
        "|---|---|---|---|---|",
    ]
    for oid, lane, label, meaning, blocked in OUTCOME_LABELS:
        lines.append(f"| `{oid}` | `{lane}` | `{label}` | {meaning} | {blocked} |")
    lines += [
        "",
        "## 2. Governing-plan minimum labels and their typing",
        "",
        "| Required phrase | Typed representation |",
        "|---|---|",
        "| no valid target package | `OT-SR-01` |",
        "| target package exists but no declared lineage relation reaches it | `OT-SR-02` + `OT-SL-01` |",
        "| structural successor | `OT-SL-02` |",
        "| one-to-one lineage continuation | `OT-SL-03` |",
        "| branch-valued continuation | `OT-SL-04` |",
        "| fusion-valued continuation | `OT-SL-05` |",
        "| public duplicate with hidden mismatch | `OT-SR-03`, plus the candidate's independent lineage/autonomy labels |",
        "| package-equivalent duplicate with unresolved token identity | `OT-SL-06` |",
        "| bridge-dependent shadow | `OT-A-01`, plus a separate target-package label |",
        "| autonomous target realization | `OT-SR-02` + `OT-A-02` |",
        "| indeterminate under the declared instruments | `OT-R-02`, plus structural labels or structural underdetermination as appropriate |",
        "| empty target after viability failure | `OT-SR-04` |",
        "",
        "## 3. Underdetermination is typed",
        "",
        "Every underdetermined label must identify one or more bases:",
        "",
        "- `criterion_underspecified`: the candidate has not defined the relevant relation/predicate;",
        "- `scenario_underspecified`: a scenario parameter needed by the criterion is intentionally left as a variant;",
        "- `symmetry_nonselection`: available structural facts do not break a target symmetry;",
        "- `route_dependence`: admissible routes yield different candidate outputs;",
        "- `instrument_nonidentifiability`: declared observations leave several structural possibilities;",
        "- `assumption_dependence`: different optional assumptions yield different outputs; or",
        "- `out_of_scope`: the candidate explicitly does not cover the scenario class.",
        "",
        "`underdetermined` is therefore an informative result only when its basis and scope are named.",
        "",
        "## 4. Cardinality and token caution",
        "",
        "`one_to_one_lineage_continuation` means cardinality one under a declared criterion, route family, and target domain. It does not mean personal identity. `branch_valued_continuation` and `fusion_valued_continuation` permit relation-valued structure without claiming that one numerical token is many tokens or vice versa.",
        "",
        "## 5. Label composition rules",
        "",
        "1. Exactly one applicable label is selected per lane; nonapplicable lanes require the explicit nonapplicable/not-tested label.",
        "2. A positive `S-T` label cannot fill `S-R`, `S-L`, or `A`.",
        "3. `OT-SR-02` and `OT-A-02` may coexist without any `S-L` edge.",
        "4. `OT-SL-02/03/04/05` may be returned only by a declared lineage criterion, not by the scenario title.",
        "5. `OT-R-02` reports instrument limits, not metaphysical indeterminacy.",
        "6. No label in this taxonomy licenses an `O` claim. Personal identity or phenomenal realization must be separately stated with assumptions.",
        "",
        "## 6. Unfilled template",
        "",
        "`ledgers/scenario_verdict_template.csv` contains one unfilled row for every scenario. Future candidates must populate all 35 rows or explicitly mark a lane underdetermined/not applicable with a reason.",
    ]
    return "\n".join(lines)


def scenario_card(s: dict[str, Any]) -> str:
    axis_rows = [f"| `{axis}` | `{s[axis]}` |" for axis in AXES]
    disc_rows = []
    for d in DISCRIMINATORS:
        rel = relevance_for(s, d["id"])
        disc_rows.append(f"| `{d['id']}` | {d['label']} | `{rel}` | {scenario_probe(s, d)} |")
    question_ids = sorted(set(
        CORE_QUESTIONS
        + s["question_focus"]
        + [q for d in DISCRIMINATORS for q in d["questions"] if d["id"] in s["primary_discriminators"]]
    ))
    lines = [
        f"# {s['id']} — {s['title']}",
        "",
        f"**Battery item:** {s['number']} ({'canonical' if s['number'] <= CANONICAL_COUNT else 'supplemental stress control'})  ",
        f"**Plan wording:** {s['canonical_prompt']}  ",
        f"**Cross-carrier/control status:** `{s['cross_carrier_status']}`  ",
        "**Outcome vector:** deliberately unfilled (`S-T=UNFILLED; S-R=UNFILLED; S-L=UNFILLED; A=UNFILLED; R=UNFILLED`)  ",
        f"**Machine records:** `scenarios/PROTOCOL_AXIS_MATRIX.csv` and `ledgers/scenario_discriminator_matrix.csv`, keyed by `{s['id']}`",
        "",
        "## 1. Discriminating purpose",
        "",
        s["purpose"],
        "",
        "## 2. Stipulated scenario facts",
        "",
    ]
    lines.extend(f"- {x}" for x in s["facts"])
    lines += [
        "",
        "These facts define the case. They do not preassign transport, target-package, lineage, autonomy, recognition, or ontological outputs.",
        "",
        "## 3. Neutral frame instantiation",
        "",
        "| Field | Record |",
        "|---|---|",
        f"| Operational episode graph | `{s['episode_graph']}` |",
        f"| Branch/merge topology | {s['branch_graph']} |",
        f"| Handoff shape | `{s['handoff_shape']}` |",
        f"| Causal structure | {s['causal_structure']} |",
        f"| Clock relation | {s['clock_relation']} |",
        f"| Fidelity scope | {s['fidelity_scope']} |",
        f"| Withdrawal/autonomy intervention | {s['autonomy_intervention']} |",
        f"| Instrument constraints | {s['instrument_constraints']} |",
        f"| Secondary modes | `{s['secondary_modes'] or 'none'}` |",
        "",
        "`G_op` above is an operational protocol graph only. It supplies no lineage edge.",
        "",
        "## 4. Protocol-axis profile",
        "",
        "| Axis | Value |",
        "|---|---|",
        *axis_rows,
        "",
        "## 5. Controlled variants",
        "",
    ]
    lines.extend(f"- {x}" for x in s["variants"])
    lines += [
        "",
        "A candidate may be sensitive to a variant, but it must name the sensitivity rather than silently changing the scenario.",
        "",
        "## 6. Discriminator audit",
        "",
        "| ID | Discriminator | Relevance | Candidate-facing probe |",
        "|---|---|---|---|",
        *disc_rows,
        "",
        "## 7. Scenario-specific stress questions",
        "",
    ]
    lines.extend(f"- {x}" for x in s["stress_questions"])
    lines += [
        "",
        "## 8. Required candidate response",
        "",
        "A later candidate must record, for this scenario:",
        "",
        "1. one `S-T` outcome label and the transported object/bridge scope;",
        "2. one `S-R` outcome label and target-package clause/gate scope;",
        "3. one `S-L` outcome label and lineage criterion/cardinality;",
        "4. one `A` outcome label under the declared withdrawal intervention;",
        "5. one `R` outcome label for the declared instruments;",
        "6. underdetermination basis where applicable;",
        "7. assumptions spent, especially any uniqueness, cross-carrier invariance, certificate-soundness, or identity premise;",
        "8. route and approximation sensitivity; and",
        "9. explicit nonclaims.",
        "",
        f"Relevant question-bank IDs: `{';'.join(question_ids)}`.",
        "",
        "## 9. Corpus assets that sharpen the case",
        "",
        f"`{';'.join(s['asset_focus'])}`",
        "",
        "These are methodological/discriminating imports at their source scope. They do not decide the scenario and retain their fixed-support/retyping warnings from CST-EXP-01.",
        "",
        "## 10. Blocked inferences",
        "",
    ]
    lines.extend(f"- {x}" for x in s["blocked_inferences"])
    lines += [
        "",
        "## 11. Nonclaims",
        "",
        "This card does not say whether a conscious subject moves, survives, dies, branches, fuses, or is recreated. It does not assert that the source or target is conscious. It defines an operational stress case for later structural candidates.",
    ]
    return "\n".join(lines)

def battery_md() -> str:
    counts = {axis: Counter(s[axis] for s in SCENARIOS) for axis in AXES}
    lines = [
        "# Canonical and supplemental thought-experiment battery",
        "",
        "**Phase:** CST-EXP-02  ",
        "**Battery size:** 20 governing-plan scenarios + 15 supplemental stress controls (35 total)  ",
        "**Rule:** no scenario defines transfer for the others; every later candidate must return a typed verdict vector or explicit underdetermination for all 35.",
        "",
        "## 1. Battery index",
        "",
        "| ID | Role | Scenario | Carrier relation | Mode | Source fate | Branching | Fidelity / granularity | Primary discriminators | Card |",
        "|---|---|---|---|---|---|---|---|---|---|",
    ]
    for s in SCENARIOS:
        lines.append(f"| `{s['id']}` | `{'canonical' if s['number'] <= CANONICAL_COUNT else 'supplemental'}` | {s['title']} | `{s['carrier_relation']}` | `{s['change_mode']}` | `{s['source_fate']}` | `{s['branching']}` | `{s['fidelity']}` / `{s['granularity']}` | `{';'.join(s['primary_discriminators'])}` | [card](cards/{s['id']}.md) |")
    lines += [
        "",
        "## 2. Governing-plan coverage",
        "",
        "S01–S20 instantiate, in order: gradual replacement; instantaneous destructive scan/reconstruction; nondestructive exact copy while the source continues; copy followed by later source deletion; two simultaneous exact targets; delayed activation after a temporal gap; long-lived source-target overlap; distributed extension with no sharp handoff; fission followed by independent divergence; fission followed by later fusion; a public/report-perfect but predictively different target; predictive matching with different binding or action-credit structure; target behavior maintained only by an external decoder/source; a route loop that restores public observables while changing predictive state; local pairwise matches that fail to glue globally; residual-bounded transfer near a viability boundary; lossy transfer followed by endogenous repair; an exact reversible round trip; a radically rescaled clock; and a pure representation/gauge change.",
        "",
        "## 3. Minimal contrast pairs",
        "",
        "The following comparisons isolate one or a small number of protocol changes. They are not claims that only those changes matter. No scenario is paradigmatic, and no candidate verdict is preassigned.",
        "",
        "| Contrast | Principal variable isolated |",
        "|---|---|",
        "| S01 vs S02 | staged overlap/order versus abrupt destructive reconstruction |",
        "| S02 vs S06 | ordinary delayed reconstruction versus a nonzero dormant gap |",
        "| S03 vs S04 | source persistence versus later source deletion after coactivity |",
        "| S03 vs S05 | one target plus source versus symmetric multiple targets without source |",
        "| S05 vs S09 | symmetric activation versus later branch divergence |",
        "| S09 vs S10 | persistent fission versus later many-to-one fusion/recombination |",
        "| S07 vs S13 | long overlap with moving responsibility versus continuing external generation/readout |",
        "| S07 vs S08 | eventual target-only handoff versus permanently distributed realization |",
        "| S03 vs S11 | declared package exactness versus public-only exactness with predictive mismatch |",
        "| S11 vs S12 | predictive mismatch versus predictive match with other package mismatch |",
        "| S08 vs S15 | coherent distributed package versus locally accepted records with failed global glue |",
        "| S14 vs S18 | route loop with predictive residue versus exact inverse round trip on named structure |",
        "| S16 vs S17 | defect near viability boundary versus defect followed by target-native repair |",
        "| S06 vs S19 | temporal absence versus continuous dynamics under radical time rescaling |",
        "| S20 vs every cross-carrier case | genuine support change versus pure representation/gauge change |",
        "| S06 vs S21 vs S33 | erased source gap versus paused recoverable source versus stale dormant backup |",
        "| S01 vs S22 vs S35 | staged replacement versus concurrent-update cutover versus route-order critical pair |",
        "| S10 vs S23 | fission-then-fusion versus independent many-source fusion |",
        "| S08 vs S24 | stable distributed extension versus many-to-many repartition |",
        "| S17 vs S25 | endogenous repair after loss versus explicit error-corrected support migration |",
        "| S03 vs S26 | source-derived exact copy versus independently built structural twin |",
        "| S01 vs S27 | complete replacement versus persistent-core partial replacement |",
        "| S13 vs S28 vs S29 | obvious bridge dependence versus delayed collapse versus external temporal scheduler |",
        "| S12 vs S30 | package-clause mismatch versus certificate-only counterfeit |",
        "| S15 vs S31 | generic gluing failure versus event-package pairwise-edge obstruction |",
        "| S18 vs S32 | exact round trip versus approximately reversible accumulated residual |",
        "| S16 vs S34 | target viability boundary versus source-degrading transfer cost |",
        "",
        "## 4. Axis coverage",
        "",
    ]
    for axis, c in counts.items():
        lines.append(f"### `{axis}`")
        lines.append("")
        lines.append("| Value | Scenario count | Scenarios |")
        lines.append("|---|---:|---|")
        for value in AXES[axis]["values"]:
            ids = [s["id"] for s in SCENARIOS if s[axis] == value]
            lines.append(f"| `{value}` | {len(ids)} | `{';'.join(ids)}` |")
        lines.append("")
    lines += [
        "## 5. What is fixed and what remains open",
        "",
        "Each scenario fixes only the operational facts needed to expose a discriminator. The following remain candidate outputs unless explicitly stated as a control fact:",
        "",
        "- what object is transported;",
        "- whether a target package exists;",
        "- whether operational edges become lineage edges;",
        "- whether lineage is zero, unique, branch-valued, fusion-valued, route-dependent, or underdetermined;",
        "- whether bridge withdrawal leaves a target-native package;",
        "- which defects matter and which thresholds are stable;",
        "- what declared instruments can identify; and",
        "- every ontological or personal-identity interpretation.",
        "",
        "## 6. Candidate completion rule",
        "",
        "A candidate has not completed the scenario phase merely by discussing famous cases. It must populate `ledgers/scenario_verdict_template.csv` for every row, cite the criterion used in each lane, and explain every underdetermined/not-applicable result. A candidate that uses one scenario to define its criterion and then treats the remaining cases as verbal exceptions fails the exit gate.",
    ]
    return "\n".join(lines)


def cards_index_md() -> str:
    lines = ["# Scenario-card index", "", "Every card separates stipulated facts from criterion outputs and includes all ten discriminator probes. S01–S20 are governing-plan cases; S21–S35 are supplemental stress controls.", "", "| ID | Title | Control role |", "|---|---|---|"]
    for s in SCENARIOS:
        lines.append(f"| [{s['id']}]({s['id']}.md) | {s['title']} | `{s['cross_carrier_status']}` |")
    return "\n".join(lines)


def coverage_audit_md() -> str:
    return dedent(f"""
    # CST-EXP-02 scenario coverage and exit-gate audit

    ## Required outputs

    | Requirement | Artifact | Result |
    |---|---|---|
    | Neutral source-target frame without a shared identity object | `scenarios/NEUTRAL_TRANSFER_SCHEMA.md` | PASS |
    | Ten independent protocol axes and controlled vocabulary | `scenarios/PROTOCOL_AXIS_DICTIONARY.md`; `scenarios/PROTOCOL_AXIS_MATRIX.csv` | PASS |
    | Metaphysically unloaded outcome labels | `scenarios/OUTCOME_TAXONOMY.md`; `scenarios/OUTCOME_LABEL_REGISTRY.csv` | PASS |
    | Twenty required thought experiments plus fifteen supplemental stress controls | `scenarios/CANONICAL_BATTERY.md`; `scenarios/cards/S01.md`–`S35.md` | PASS |
    | All ten discriminators applied to every scenario | `ledgers/scenario_discriminator_matrix.csv` ({len(SCENARIOS) * len(DISCRIMINATORS)} rows) | PASS |
    | Every later candidate forced to return typed verdict or explicit underdetermined result | `ledgers/scenario_verdict_template.csv`; `templates/SCENARIO_VERDICT_RECORD.yml` | PASS |
    | No preassigned scenario verdict | cards and verdict template contain only unfilled output slots | PASS |
    | No target/theorem/toy implementation | repository phase controls | PASS |

    ## Neutrality audit

    - `G_op` is operational only; no edge is called a lineage edge.
    - Scenario facts and candidate outputs are stored in separate sections/fields.
    - Source fate, overlap, graduality, exactness, reversibility, and target count have no default lineage interpretation.
    - Outcome labels are lane-typed; no label says “same person,” “survives,” “dies,” or “is conscious.”
    - S20 prevents relabeling one fixed support as a carrier transfer.
    - S11 and S12 prevent public or predictive matching from standing in for a full package.
    - S13 prevents external generation from standing in for target-native autonomy.
    - S14 and S15 prevent endpoint/local agreement from standing in for route/global coherence.
    - S05, S09, and S10 prevent a hidden function-valued lineage default.

    ## Exit-gate ruling

    **PASS subject to validator:** every later candidate has a common schema and a complete 35-scenario battery, and may return an explicit typed `underdetermined` result. No scenario has been allowed to define the meaning of transfer for the rest.
    """)


def verdict_template_yaml() -> str:
    return dedent("""
    schema_version: CST-EXP-02-v1
    record_type: scenario_verdict
    rule: >-
      One record is required for every candidate-scenario pair. Each applicable lane
      receives one taxonomy label; underdetermined/not-applicable labels require a basis.
    fields:
      candidate_id: required
      scenario_id: required; one of S01..S35
      candidate_version: required
      transported_object_id: required_or_not_applicable
      bridge_id: required_or_not_applicable
      lineage_criterion_id: required_or_not_applicable
      st_outcome_id: required; OT-ST-*
      sr_outcome_id: required; OT-SR-*
      sl_outcome_id: required; OT-SL-*
      autonomy_outcome_id: required; OT-A-*
      recognition_outcome_id: required; OT-R-*
      underdetermination_basis: required_when_any_lane_underdetermined
      criterion_sensitive_scenario_fields: required
      assumptions_spent: required; may_be_none
      evidence_or_argument: required
      route_sensitivity: required
      approximation_scope: required
      blocked_inferences: required
      nonclaims: required
      status: required; draft|audited|rejected
    prohibited_shortcuts:
      - derive lineage from operational graph edge
      - derive realization from transport
      - derive autonomy from scheduled bridge end
      - derive ontology from any scenario label
      - omit a scenario because it is inconvenient
    """)


def build(repo: Path) -> None:
    scenarios_dir = repo / "scenarios"
    cards_dir = scenarios_dir / "cards"
    cards_dir.mkdir(parents=True, exist_ok=True)

    # Canonical machine-readable registry.
    registry = {
        "schema_version": "CST-EXP-02-v1",
        "phase": PHASE,
        "generated_date": DATE,
        "neutrality_rule": "Operational edges are not lineage edges; outcome vectors are unfilled.",
        "axes": AXES,
        "discriminators": DISCRIMINATORS,
        "scenarios": SCENARIOS,
    }
    write_text(scenarios_dir / "SCENARIO_REGISTRY.json", json.dumps(registry, indent=2, ensure_ascii=False, sort_keys=False))

    write_text(scenarios_dir / "NEUTRAL_TRANSFER_SCHEMA.md", neutral_schema_md())
    write_text(scenarios_dir / "PROTOCOL_AXIS_DICTIONARY.md", axis_dictionary_md())
    write_text(scenarios_dir / "OUTCOME_TAXONOMY.md", outcome_taxonomy_md())
    write_text(scenarios_dir / "CANONICAL_BATTERY.md", battery_md())
    write_text(scenarios_dir / "EXIT_GATE_AUDIT.md", coverage_audit_md())
    write_text(cards_dir / "INDEX.md", cards_index_md())
    for s in SCENARIOS:
        write_text(cards_dir / f"{s['id']}.md", scenario_card(s))

    matrix_fields = [
        "scenario_id", "canonical_number", "title", *AXES.keys(), "secondary_change_modes",
        "cross_carrier_status", "handoff_shape", "branch_graph", "clock_relation",
        "causal_structure", "fidelity_scope", "autonomy_intervention", "instrument_constraints",
        "primary_discriminators", "card_path",
    ]
    matrix_rows = []
    for s in SCENARIOS:
        row = {
            "scenario_id": s["id"], "canonical_number": s["number"], "title": s["title"],
            **{axis: s[axis] for axis in AXES},
            "secondary_change_modes": s["secondary_modes"],
            "cross_carrier_status": s["cross_carrier_status"], "handoff_shape": s["handoff_shape"],
            "branch_graph": s["branch_graph"], "clock_relation": s["clock_relation"],
            "causal_structure": s["causal_structure"], "fidelity_scope": s["fidelity_scope"],
            "autonomy_intervention": s["autonomy_intervention"], "instrument_constraints": s["instrument_constraints"],
            "primary_discriminators": compact_list(s["primary_discriminators"]),
            "card_path": f"scenarios/cards/{s['id']}.md",
        }
        matrix_rows.append(row)
    write_csv(scenarios_dir / "PROTOCOL_AXIS_MATRIX.csv", matrix_fields, matrix_rows)

    axis_rows = []
    for axis, spec in AXES.items():
        for value, meaning in spec["values"].items():
            axis_rows.append({"axis": axis, "value": value, "neutral_meaning": meaning, "axis_question": spec["question"], "blocked_inference": spec["blocked"]})
    write_csv(scenarios_dir / "PROTOCOL_AXIS_REGISTRY.csv", ["axis", "value", "neutral_meaning", "axis_question", "blocked_inference"], axis_rows)

    outcome_rows = [
        {"outcome_id": oid, "claim_lane": lane, "label": label, "neutral_meaning": meaning, "blocked_inference": blocked}
        for oid, lane, label, meaning, blocked in OUTCOME_LABELS
    ]
    write_csv(scenarios_dir / "OUTCOME_LABEL_REGISTRY.csv", ["outcome_id", "claim_lane", "label", "neutral_meaning", "blocked_inference"], outcome_rows)

    disc_rows = []
    for s in SCENARIOS:
        for d in DISCRIMINATORS:
            disc_rows.append({
                "scenario_id": s["id"], "scenario_title": s["title"],
                "discriminator_id": d["id"], "discriminator": d["name"],
                "relevance": relevance_for(s, d["id"]),
                "scenario_specific_probe": scenario_probe(s, d),
                "claim_lanes": d["lanes"], "asset_ids": compact_list(d["assets"]),
                "question_bank_ids": compact_list(d["questions"]),
                "required_response": "answer; explicitly underdetermined; or not_applicable with scope reason",
            })
    write_csv(repo / "ledgers/scenario_discriminator_matrix.csv", [
        "scenario_id", "scenario_title", "discriminator_id", "discriminator", "relevance",
        "scenario_specific_probe", "claim_lanes", "asset_ids", "question_bank_ids", "required_response",
    ], disc_rows)

    # Every scenario gets all core questions plus tailored and discriminator-linked questions.
    qbank_path = repo / "ledgers/exploration_question_bank.yml"
    qtext = qbank_path.read_text(encoding="utf-8")
    # Avoid a PyYAML dependency in the rebuild: IDs are simple and can be extracted safely.
    qids = set()
    for line in qtext.splitlines():
        stripped = line.strip()
        if stripped.startswith("- id:"):
            qids.add(stripped.split(":", 1)[1].strip())
        elif stripped.startswith("id:"):
            qids.add(stripped.split(":", 1)[1].strip())
    question_rows = []
    for s in SCENARIOS:
        specific = set(s["question_focus"])
        for d in DISCRIMINATORS:
            if d["id"] in s["primary_discriminators"]:
                specific.update(d["questions"])
        selected = CORE_QUESTIONS + sorted(specific - set(CORE_QUESTIONS))
        for qid in selected:
            if qid not in qids:
                raise ValueError(f"Unknown question ID {qid} in {s['id']}")
            question_rows.append({
                "scenario_id": s["id"], "question_id": qid,
                "role": "core_all_scenarios" if qid in CORE_QUESTIONS else "scenario_specific",
                "why_relevant": "governing core question" if qid in CORE_QUESTIONS else f"targets the primary discriminators or protocol facts of {s['id']}",
                "response_rule": "candidate must answer globally and reflect scenario-specific consequences in its verdict record",
            })
    write_csv(repo / "ledgers/scenario_question_crosswalk.csv", ["scenario_id", "question_id", "role", "why_relevant", "response_rule"], question_rows)

    asset_rows = []
    for s in SCENARIOS:
        for aid in s["asset_focus"]:
            asset_rows.append({
                "scenario_id": s["id"], "asset_id": aid, "use": "discriminator/methodological control",
                "import_rule": "retain CST-EXP-01 source scope, fixed-support flag, and nonclaim; no scenario verdict imported",
            })
    write_csv(repo / "ledgers/scenario_asset_crosswalk.csv", ["scenario_id", "asset_id", "use", "import_rule"], asset_rows)

    verdict_rows = []
    for s in SCENARIOS:
        verdict_rows.append({
            "candidate_id": "<candidate_id>", "candidate_version": "<version>", "scenario_id": s["id"],
            "st_outcome_id": "UNFILLED", "sr_outcome_id": "UNFILLED", "sl_outcome_id": "UNFILLED",
            "autonomy_outcome_id": "UNFILLED", "recognition_outcome_id": "UNFILLED",
            "underdetermination_basis": "", "criterion_sensitive_scenario_fields": "",
            "assumptions_spent": "", "route_sensitivity": "", "approximation_scope": "",
            "evidence_or_argument": "", "blocked_inferences": "", "nonclaims": "", "status": "template",
        })
    write_csv(repo / "ledgers/scenario_verdict_template.csv", [
        "candidate_id", "candidate_version", "scenario_id", "st_outcome_id", "sr_outcome_id", "sl_outcome_id",
        "autonomy_outcome_id", "recognition_outcome_id", "underdetermination_basis",
        "criterion_sensitive_scenario_fields", "assumptions_spent", "route_sensitivity", "approximation_scope",
        "evidence_or_argument", "blocked_inferences", "nonclaims", "status",
    ], verdict_rows)

    write_text(repo / "templates/SCENARIO_VERDICT_RECORD.yml", verdict_template_yaml())

    # Compact phase statistics for validators/reports.
    summary = {
        "project": "CST-EXP",
        "phase": PHASE,
        "generated_date": DATE,
        "status": "assets_built_pending_freeze",
        "target_selected": False,
        "scenario_verdicts_selected": False,
        "theorem_or_program_implemented": False,
        "counts": {
            "battery_scenarios": len(SCENARIOS),
            "governing_plan_scenarios": CANONICAL_COUNT,
            "supplemental_stress_controls": SUPPLEMENTAL_COUNT,
            "protocol_axes": len(AXES),
            "axis_values": sum(len(x["values"]) for x in AXES.values()),
            "outcome_labels": len(OUTCOME_LABELS),
            "discriminators": len(DISCRIMINATORS),
            "scenario_discriminator_rows": len(disc_rows),
            "scenario_question_crosswalk_rows": len(question_rows),
            "scenario_asset_crosswalk_rows": len(asset_rows),
            "scenario_cards": len(SCENARIOS),
            "unfilled_verdict_rows": len(verdict_rows),
        },
        "next_phase": "CST-EXP-03",
    }
    write_text(repo / "manifests/EXP02_ASSET_SUMMARY.json", json.dumps(summary, indent=2, sort_keys=False))


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--repo", required=True, type=Path)
    args = parser.parse_args()
    build(args.repo.resolve())
