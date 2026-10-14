#!/usr/bin/env python3
"""Frozen data for CST-EXP-04 adversarial stress and external challenge."""
from __future__ import annotations

DATE = "2026-08-10"
PHASE = "CST-EXP-04"

HARD_CASES = [
    {"id":"HC-01","title":"Public-perfect behavior with a different predictive quotient","lanes":"S-T;R","probe":"Hold public reports and behavior fixed while varying future-sufficient hidden structure.","core_objection":"Public matching is not predictive transport.","no_go":"NG-01"},
    {"id":"HC-02","title":"Same predictive quotient with different binding structure","lanes":"S-T;S-R","probe":"Hold predictive quotient dynamics fixed while changing joint binding or event-package structure.","core_objection":"Predictive equivalence is not a full-package certificate.","no_go":"NG-03"},
    {"id":"HC-03","title":"Same predictive dynamics with different viability or autonomy","lanes":"S-T;S-R;A","probe":"Match transition behavior during support, then withdraw source, decoder, and migration controller.","core_objection":"Matched dynamics under support do not establish target-native maintenance.","no_go":"NG-05"},
    {"id":"HC-04","title":"Exact target copy while the source persists","lanes":"S-T;S-L","probe":"Create an exact target while leaving the source operational and causally independent after the copy event.","core_objection":"Structural success does not select one continuer.","no_go":"NG-09"},
    {"id":"HC-05","title":"Two exact targets with symmetric histories","lanes":"S-L","probe":"Construct two target tokens related by an automorphism fixing all admissible source-relative evidence.","core_objection":"No symmetry-invariant unique-choice rule can select one target without extra asymmetry.","no_go":"NG-02;NG-16"},
    {"id":"HC-06","title":"Destructive copy with no causal overlap","lanes":"S-T;S-L","probe":"Destroy the source before target activation and prohibit a live causal-process overlap witness.","core_objection":"Endpoint structure alone does not establish process continuation.","no_go":"NG-09"},
    {"id":"HC-07","title":"Gradual replacement with continuous overlap","lanes":"S-T;S-L;A","probe":"Move operational responsibility across support while retaining continuous bidirectional causal overlap.","core_objection":"A continuity-sensitive criterion should distinguish this case without assuming the conclusion.","no_go":"NG-11"},
    {"id":"HC-08","title":"Same endpoints reached through holonomically different routes","lanes":"S-T;S-L","probe":"Use two admissible bridge paths with identical endpoints but nontrivial loop action on retained history or predictive state.","core_objection":"Endpoint equivalence is not route-independent transport.","no_go":"NG-06"},
    {"id":"HC-09","title":"Branchwise matches without recombination preservation","lanes":"S-T;S-R;S-L","probe":"Match each branch separately while a joint recombination probe distinguishes source and target families.","core_objection":"Pairwise or branchwise matching need not preserve joint structure.","no_go":"NG-04"},
    {"id":"HC-10","title":"Fission with both branches claiming unique identity","lanes":"S-L;O","probe":"Produce two later branches with equal source-relative evidence and demand a unique-identity verdict for each.","core_objection":"Uniqueness, symmetry, and branch success cannot all be retained without qualification.","no_go":"NG-16"},
    {"id":"HC-11","title":"Fusion of two previously independent lineages","lanes":"S-L;S-R","probe":"Merge two sources carrying incompatible histories, self-coordinates, or action-credit ledgers into one target.","core_objection":"Fusion requires a conflict and provenance law, not mere state aggregation.","no_go":"NG-17"},
    {"id":"HC-12","title":"Locally admissible bridges with no global gluing","lanes":"S-T;S-R","probe":"Give valid local maps on every declared patch while denying a compatible global section or event package.","core_objection":"Local certificates do not imply one globally coherent target.","no_go":"NG-08"},
    {"id":"HC-13","title":"Target permanently dependent on an external decoder","lanes":"S-R;A","probe":"Keep the target's relevant organization available only through an external decoder or source-side service after nominal handoff.","core_objection":"Protocol-supported behavior is not target autonomy.","no_go":"NG-05;NG-18"},
    {"id":"HC-14","title":"Small global residual with a catastrophic local defect","lanes":"S-T;S-R;A","probe":"Make aggregate error arbitrarily small while placing the entire defect on a viability-, binding-, or credit-critical locus.","core_objection":"Average adequacy does not protect hard local gates.","no_go":"NG-07"},
    {"id":"HC-15","title":"Temporary viability failure followed by reconstruction","lanes":"S-L;A","probe":"Insert an interval with no maintained viable package and reconstruct an equivalent target later.","core_objection":"Reconstruction after an empty interval requires an explicit dormancy or ancestry rule.","no_go":"NG-10"},
    {"id":"HC-16","title":"Gauge-equivalent representation change mistaken for substrate migration","lanes":"S-T","probe":"Relabel or re-encode one support without changing the independently individuated carrier token.","core_objection":"Representation change is not cross-carrier transport.","no_go":"NG-11"},
    {"id":"HC-17","title":"Clock discontinuity or temporal gap","lanes":"S-T;S-L","probe":"Remove a canonical time map and insert a target activation delay or discontinuous local-clock relation.","core_objection":"There is no automatic transport of a privileged now.","no_go":"NG-10"},
    {"id":"HC-18","title":"Bridge composition disagrees with the direct bridge","lanes":"S-T;S-L","probe":"Compare S→M→T with S→T where intermediate route memory or support changes alter the verdict.","core_objection":"A usable criterion needs a typed composition or explicit non-functoriality law.","no_go":"NG-12"},
]

INTERNAL_LENSES = [
    {"id":"IL-01","title":"Hiddenness and current-versus-predictive mismatch","asset_focus":"predictive quotients; hidden determining structure","challenge":"Can the criterion distinguish public/current agreement from future-sufficient agreement?","required_response":"Name the hidden object, test family, and false-positive surface."},
    {"id":"IL-02","title":"Route holonomy and memory","asset_focus":"predictive transport; memory holonomy","challenge":"Does a closed route act trivially on every retained object?","required_response":"Supply flatness, report route dependence, or narrow the claim."},
    {"id":"IL-03","title":"Marking, erasure, and recombination","asset_focus":"recombination witnesses; branch information","challenge":"Does branchwise preservation survive erasure and later recombination?","required_response":"Add joint probes or concede branchwise insufficiency."},
    {"id":"IL-04","title":"Local consistency versus global obstruction","asset_focus":"closure; gluing; event package","challenge":"Do local witnesses glue into one target-native global object?","required_response":"Provide a gluing condition or return global underdetermination/failure."},
    {"id":"IL-05","title":"Protocol traps and fake arrows","asset_focus":"protocol dependence; fake transition controls","challenge":"Is the claimed structure generated by the target or supplied by staging infrastructure?","required_response":"Perform a withdrawal intervention and track every support dependency."},
    {"id":"IL-06","title":"No-overreading and matched-shadow limits","asset_focus":"public shadows; observational equivalence","challenge":"Is any conclusion stronger than the admitted instrument licenses?","required_response":"State the recognition ceiling and hidden alternatives."},
    {"id":"IL-07","title":"Promotion honesty and representative-selected packages","asset_focus":"strict promotion; representative dependence","challenge":"Are package witnesses intrinsic, or selected by a favorable representative/protocol?","required_response":"Exactify the carrier and prove representative invariance or expose the choice."},
    {"id":"IL-08","title":"Temporal closure and noncanonical now transport","asset_focus":"temporal closure; clock relations","challenge":"Who mints the target order and how are source and target clocks related?","required_response":"Give a target-native temporal law and gap/route semantics."},
    {"id":"IL-09","title":"Viability collapse and empty targets","asset_focus":"viability kernels; empty lineage target","challenge":"What happens when the maintained package disappears, even briefly?","required_response":"Return failure, empty target, or an explicit dormancy/recovery semantics."},
    {"id":"IL-10","title":"Confluence and critical-pair failure","asset_focus":"critical pairs; route composition","challenge":"Do different admissible replacement orders or bridge factorizations agree?","required_response":"Prove confluence/flatness on retained data or preserve path dependence."},
    {"id":"IL-11","title":"Adequacy residuals and blind spots","asset_focus":"residual vectors; hard gates","challenge":"Can a small scalar residual hide a decisive localized defect?","required_response":"Use typed residuals, local maxima, and non-negotiable gates."},
    {"id":"IL-12","title":"Object-persistence relation laws","asset_focus":"reflexivity; composition; fission/fusion","challenge":"Is the proposed persistence notion a function, relation, or process predicate, and which laws actually hold?","required_response":"State algebraic laws and counterexamples explicitly."},
    {"id":"IL-13","title":"Audited-emergence ceiling","asset_focus":"certificate soundness; no-go for overreading","challenge":"Does certificate satisfaction exceed what certificate soundness and ontology justify?","required_response":"Separate structural certificate, recognition, A1/A2-P, and personal-identity interpretation."},
]

CANDIDATE_PROFILES = {
"TS-01": {
    "disposition":"narrowed_to_component",
    "role":"predictive-invariant component",
    "family":"SF-03",
    "core_strength":"detects public/current counterfeits by comparing future-sufficient quotient dynamics",
    "fatal_boundary":"the quotient can agree while binding, action credit, viability, or full-package realization differs",
    "salvage":"Retain as the predictive-content module inside a broader ancestry or approximation family.",
    "required_amendment":"Declare a continuation-complete test family, add recombination probes, and never infer full package or identity from quotient equivalence.",
    "rationale":"Nontrivial and compositional at S-T, but not a standalone criterion for realization, autonomy, or same-subject continuation."
},
"TS-02": {
    "disposition":"survives_as_family_core",
    "role":"integrated target-realization core",
    "family":"SF-01",
    "core_strength":"requires one target-native, globally coherent C1–C8 realization and an explicit withdrawal audit",
    "fatal_boundary":"does not itself supply source ancestry, unique continuation, certificate soundness, or an integrated source instance",
    "salvage":"Use as the structural realization core of an integrated autonomous handoff family; keep lineage separate.",
    "required_amendment":"Import viability, gluing, route, temporal/provenance, and vector-residual gates as mandatory rather than optional adjuncts.",
    "rationale":"The strongest direct answer to what must exist on the target, provided it is not misreported as personal identity."
},
"TS-03": {
    "disposition":"survives_as_family_core",
    "role":"conservative process-lineage core",
    "family":"SF-02",
    "core_strength":"distinguishes live overlapping handoff from detached copying through one causally connected moving-support process",
    "fatal_boundary":"the selected process organization can be circular or too coarse, and the criterion deliberately rejects no-overlap copies and unlicensed gaps",
    "salvage":"Retain as a stringent lineage family, not as a universal substrate-independence theorem.",
    "required_amendment":"Specify the non-question-begging process invariant, target-native maintenance, temporal closure, and composition/confluence law.",
    "rationale":"It survives because its restrictive verdicts are coherent and falsifiable, not because gradual replacement has been assumed successful."
},
"TS-04": {
    "disposition":"narrowed_to_mandatory_gate",
    "role":"autonomy and viability gate",
    "family":"SF-01;SF-02",
    "core_strength":"tests endogenous maintenance, repair, resource closure, and post-withdrawal survival",
    "fatal_boundary":"viability can be shared by unrelated systems and does not fix predictive content, binding, or lineage",
    "salvage":"Make the withdrawal/viability audit mandatory for constructive families.",
    "required_amendment":"Bind viability to a declared package and critical local margins rather than a generic attractor or scalar score.",
    "rationale":"Essential as a veto and autonomy test; insufficient as the transported object or lineage criterion."
},
"TS-05": {
    "disposition":"narrowed_to_bridge_mechanism",
    "role":"engineering bridge and recovery mechanism",
    "family":"SF-01(optional)",
    "core_strength":"makes encoding, recovery, decoder dependence, and logical-versus-physical support explicit",
    "fatal_boundary":"the consciousness-relevant code space and recovery map are not given, and logical persistence does not imply subject persistence",
    "salvage":"Retain as an implementation pattern once a transported package and error model are independently justified.",
    "required_amendment":"Specify the code subspace, admissible errors, target-native decoder, and proof that recovery preserves every hard package gate.",
    "rationale":"A powerful analogy and bridge morphology, but not a standalone theory of consciousness continuation."
},
"TS-06": {
    "disposition":"narrowed_to_mandatory_gate",
    "role":"global coherence and gluing gate",
    "family":"SF-01",
    "core_strength":"blocks local-witness and branchwise-success fallacies by demanding compatible global realization",
    "fatal_boundary":"closure/gluing alone has no causal ancestry, autonomy, or personal-identity content and can depend on a chosen cover",
    "salvage":"Use as the global package-coherence gate in constructive candidates.",
    "required_amendment":"Prove cover/representative robustness, define closure intrinsically, and connect gluing to target-native support.",
    "rationale":"Survives as a necessary structural audit, not as an independent transfer criterion."
},
"TS-07": {
    "disposition":"narrowed_to_crosscutting_audit",
    "role":"route, branch, fusion, and recombination audit",
    "family":"SF-01;SF-02;SF-03",
    "core_strength":"represents path dependence, fission/fusion, recombination, and holonomy without forcing unique continuation",
    "fatal_boundary":"does not by itself establish a full target package, viability, or empirical recognition",
    "salvage":"Require its route/recombination checks across every survivor family.",
    "required_amendment":"Add typed approximation and autonomy interfaces and avoid treating a continuation functor as phenomenal identity.",
    "rationale":"The strongest route-sensitive audit; its value is crosscutting rather than standalone."
},
"TS-08": {
    "disposition":"narrowed_to_mandatory_gate",
    "role":"temporal, reflexive, and action-credit provenance gate",
    "family":"SF-01;SF-02",
    "core_strength":"tests whether self-coordinate, target-native time, and action-credit history are generated rather than copied as labels",
    "fatal_boundary":"ledger agreement can coexist with predictive, binding, viability, or recombination mismatch",
    "salvage":"Use as a provenance/temporal gate where a candidate claims historical continuation.",
    "required_amendment":"Define conflict resolution under fusion, dormant intervals, and the relation between ledger preservation and live process causation.",
    "rationale":"Necessary for historically thick claims; insufficient as a full transported object."
},
"TS-09": {
    "disposition":"narrowed_to_approximation_layer",
    "role":"approximation, falsifier, and stability layer",
    "family":"SF-01;SF-03",
    "core_strength":"forces vector defects, hard gates, horizons, and composition error rather than an undifferentiated similarity score",
    "fatal_boundary":"a residual bundle inherits the incompleteness of its selected probes and has no independent lineage or ontology",
    "salvage":"Use as the only permitted approximate relaxation of a fully typed exact candidate.",
    "required_amendment":"Prove stability near viability and binding thresholds, include local maxima, and register blind-spot families.",
    "rationale":"Essential for realistic transfer claims, but meaningful only after the exact target is fixed."
},
"TS-10": {
    "disposition":"survives_as_family_core",
    "role":"relation-valued branching lineage core",
    "family":"SF-03",
    "core_strength":"handles fission, fusion, empty targets, and symmetric duplication without inventing a unique continuer",
    "fatal_boundary":"ancestry can become too permissive or circular and does not guarantee integrated target realization or autonomy",
    "salvage":"Retain as the principal relation-valued lineage family with predictive, route, and approximation modules.",
    "required_amendment":"Give a finite noncircular ancestry generator, composition laws, counterexamples, and separate target-package/autonomy gates.",
    "rationale":"The most coherent branching semantics, provided it is not renamed strict numerical identity."
},
}

# S=survives, C=conditional, U=principled underdetermination, N=narrowed role, F=fails standalone.
HARD_CASE_STATUS = {
"TS-01": "S F F U U F C C F U U F F C F S C C".split(),
"TS-02": "S S S U U U S C S U C S S C F S C C".split(),
"TS-03": "C C C S U F S C F U C F C C F S F C".split(),
"TS-04": "F F S U U F C F F U C F S S F S C C".split(),
"TS-05": "C F C U U F C C F U C C F S F S C C".split(),
"TS-06": "C S C U U U C S S C C S F C F S C S".split(),
"TS-07": "C C C U S U C S S S S C F C F S C S".split(),
"TS-08": "C C C U U F S C C C C C F C F S S C".split(),
"TS-09": "S C S U U U C C C U C C C S F S C S".split(),
"TS-10": "S C C U S C C S C S S C F C U S C S".split(),
}

LENS_STATUS = {
"TS-01": "S C F C C S C C F C C C N".split(),
"TS-02": "S C S S S S S S S C C C C".split(),
"TS-03": "C C F C S C C S C C C S N".split(),
"TS-04": "F F F C S C C C S F S C N".split(),
"TS-05": "C C F C S C C C C C S C N".split(),
"TS-06": "C S S S C C S C F S C C C".split(),
"TS-07": "C S S C C C C S F S F S N".split(),
"TS-08": "C C C C S C C S C C C S N".split(),
"TS-09": "S C C C S S C C S C S C N".split(),
"TS-10": "S S C C C S C S F S C S N".split(),
}

STATUS_LABELS = {
    "S":("survives","The candidate directly contains a nontrivial response to this challenge, subject to its stated scope."),
    "C":("survives_conditionally","The candidate can answer coherently only after a named assumption, gate, or composition law is added."),
    "U":("principled_underdetermination","The candidate refuses a stronger verdict for a stated structural reason; this is counted as coherent, not as success of transfer."),
    "N":("narrowed_role_only","The challenge lies outside the component's proper scope; the component is retained only inside a larger family."),
    "F":("fails_as_standalone","The challenge provides a finite countermodel to treating this candidate as a complete criterion."),
}

SURVIVOR_FAMILIES = [
    {
        "id":"SF-01","title":"Integrated Autonomous Handoff","status":"survivor_family","core":"TS-02",
        "mandatory_modules":"TS-04;TS-06;TS-07;TS-08;TS-09","optional_mechanism":"TS-05",
        "claim_ceiling":"A heterogeneous episode can establish target-native integrated structural realization and autonomy under explicit package, gluing, route, provenance, residual, and withdrawal conditions.",
        "lineage_policy":"No source-target personal identity follows. Lineage must be supplied separately by SF-02 or SF-03, or left underdetermined.",
        "why_survives":"It is nontrivial, cross-carrier typed, blocks public-shadow and decoder counterfeits, and has exact finite failure conditions.",
        "principal_risk":"The integrated package may be unrealizable or circular, and certificate soundness remains external.",
        "kill_condition":"No finite nontrivial heterogeneous model satisfies the integrated gates, or the package definition presupposes the desired consciousness conclusion."
    },
    {
        "id":"SF-02","title":"Causal-Overlap Process Lineage","status":"survivor_family","core":"TS-03",
        "mandatory_modules":"TS-04;TS-07;TS-08","optional_mechanism":"TS-05",
        "claim_ceiling":"A source and target episode stand in a conservative structural-lineage relation when one noncircular causally connected process moves across support and remains target-autonomous.",
        "lineage_policy":"Rejects detached destructive copying and unlicensed temporal gaps; permits relation-valued fission only when the process law does.",
        "why_survives":"Its negative verdicts are principled, testable, and not derived from public equivalence or a same-subject premise.",
        "principal_risk":"The process invariant may smuggle biological continuity or be too coarse to protect the C-package.",
        "kill_condition":"Every proposed process invariant either reduces to endpoint equivalence, presupposes identity, or makes composition/confluence impossible."
    },
    {
        "id":"SF-03","title":"Relation-Valued Predictive Ancestry","status":"survivor_family","core":"TS-10",
        "mandatory_modules":"TS-01;TS-07;TS-09","optional_mechanism":"TS-05",
        "claim_ceiling":"A heterogeneous ancestry relation can connect histories across carriers while representing fission, fusion, empty targets, route dependence, and bounded predictive defects.",
        "lineage_policy":"Continuation is explicitly relation-valued; symmetric copies may both be successors, and no unique numerical identity is asserted.",
        "why_survives":"It gives coherent duplication/fission/fusion verdicts without arbitrary tie-breaking and has finite relational semantics.",
        "principal_risk":"The ancestry generator can become permissive, circular, or detached from integrated realization and autonomy.",
        "kill_condition":"No finite generator separates genuine ancestry from independently constructed twins without adding a conclusion-equivalent primitive."
    },
]

NO_GO = [
 {"id":"NG-01","title":"Public-shadow nonidentifiability","claim":"No criterion whose input is restricted to a public/report shadow can determine cross-carrier predictive transport or lineage over a class containing public-equivalent but predictively distinct systems.","witness":"Two finite machines share every admitted public trace but diverge on a hidden continuation probe after handoff.","proof_spine":"Construct observationally equivalent source/target pairs; swap the hidden transition; invoke input invariance of the criterion.","impacts":"TS-01;TS-02;TS-03;TS-09;TS-10","assumptions":"finite admitted interface; hidden alternatives allowed","falsifier":"A proof that the declared public interface is continuation-complete for the model class.","nonclaim":"Does not prove hidden structure is consciousness-relevant."},
 {"id":"NG-02","title":"Symmetric-duplication unique-selection impossibility","claim":"A source-relative rule invariant under target automorphisms cannot select exactly one of two perfectly symmetric qualifying targets.","witness":"One source and two isomorphic targets exchanged by an automorphism that fixes all admissible evidence.","proof_spine":"Assume unique selection; apply the automorphism; invariance forces the selected target to map to itself, contradicting target exchange.","impacts":"TS-01;TS-02;TS-03;TS-05;TS-06;TS-08;TS-09;TS-10","assumptions":"symmetry and evidence invariance","falsifier":"An admissible asymmetry not fixed by the automorphism.","nonclaim":"Does not decide whether both, neither, or a relation-valued pair should count as successors."},
 {"id":"NG-03","title":"Predictive-quotient insufficiency for the full package","claim":"Equality or bisimilarity of a selected predictive quotient does not imply preservation of independent binding, temporal-closure, action-credit, or viability predicates.","witness":"Two systems share quotient transitions but differ on a hidden joint-binding bit or repair dependency.","proof_spine":"Take a product extension invisible to quotient tests but visible to a package predicate.","impacts":"TS-01;TS-09;TS-10","assumptions":"package predicates not definable from the quotient","falsifier":"A definability theorem deriving every retained package clause from the quotient.","nonclaim":"Does not show predictive structure is unimportant."},
 {"id":"NG-04","title":"Branchwise preservation does not imply recombination preservation","claim":"Separate preservation of every branch marginal does not imply preservation of joint recombination information.","witness":"Matched branch states with different parity/correlation revealed only after recombination.","proof_spine":"Use two joint distributions or automata with identical marginals and distinct joint probe values.","impacts":"TS-01;TS-03;TS-05;TS-08;TS-09;TS-10","assumptions":"joint probes admitted","falsifier":"A factorization theorem showing all joint probes are determined by branch marginals.","nonclaim":"Does not require quantum structure; a finite classical witness suffices."},
 {"id":"NG-05","title":"Permanent decoder support is not target autonomy","claim":"A target whose relevant package exists only while an external decoder/controller remains active fails a target-native autonomy predicate defined by withdrawal.","witness":"Encoded state with correct decoded behavior during support and immediate collapse when decoder is removed.","proof_spine":"Evaluate the autonomy predicate under its declared intervention; the target-only trajectory exits the maintained set.","impacts":"TS-02;TS-04;TS-05;TS-09","assumptions":"autonomy defined by target-side maintenance after withdrawal","falsifier":"The decoder is included in the independently declared target carrier or is endogenously regenerated by it.","nonclaim":"Does not say externally supported systems are unconscious."},
 {"id":"NG-06","title":"Route independence requires trivial holonomy or equivalent confluence","claim":"Endpoint data alone cannot guarantee route-independent transport when admissible loops act nontrivially on retained state or history.","witness":"A two-route finite bridge whose closed loop flips a memory or predictive label.","proof_spine":"Compose one route with the inverse of the other; nontrivial loop action yields distinct transported results.","impacts":"TS-01;TS-02;TS-03;TS-05;TS-06;TS-07;TS-08;TS-09;TS-10","assumptions":"retained object carries the loop action","falsifier":"A flatness/confluence proof on the full retained object.","nonclaim":"Does not require every valid criterion to be route-independent."},
 {"id":"NG-07","title":"Small global residual can hide a catastrophic local defect","claim":"No scalar average error bound alone protects a hard local predicate over model classes permitting error concentration.","witness":"Move an epsilon-sized fraction of total state error onto the sole viability-critical transition.","proof_spine":"Construct a sequence with aggregate residual tending to zero while the hard predicate remains false.","impacts":"TS-02;TS-04;TS-05;TS-09","assumptions":"localized hard gates; aggregate metric permits concentration","falsifier":"A stability/Lipschitz theorem tying the global metric to every critical local margin.","nonclaim":"Does not rule out typed vector metrics or certified margins."},
 {"id":"NG-08","title":"Local certificates do not imply global gluing","claim":"Patchwise valid bridge or clause witnesses need not define one globally compatible target object.","witness":"A finite cover with pairwise local witnesses and a nontrivial cocycle/critical triple obstruction.","proof_spine":"Exhibit incompatible overlap equations despite local satisfaction.","impacts":"TS-01;TS-02;TS-03;TS-04;TS-05;TS-06;TS-07;TS-08;TS-09;TS-10","assumptions":"global compatibility is an independent predicate","falsifier":"A sheaf/closure theorem proving local-to-global extension for the chosen package.","nonclaim":"Does not say local tests are useless."},
 {"id":"NG-09","title":"Endpoint equality does not establish process lineage","claim":"A criterion depending only on source and target endpoint structures cannot distinguish a live handoff from an independently constructed duplicate with the same endpoints.","witness":"Two episodes share identical endpoint states; only one contains causal overlap or a source-generated process path.","proof_spine":"Endpoint inputs are equal, so endpoint-only criteria return equal verdicts despite different histories.","impacts":"TS-01;TS-02;TS-05;TS-06;TS-09","assumptions":"lineage may depend on history","falsifier":"A theorem that lineage is fully supervenient on the declared endpoints.","nonclaim":"Does not establish that causal overlap is sufficient."},
 {"id":"NG-10","title":"Temporal-gap underdetermination without dormancy semantics","claim":"A gap containing no maintained target package is neither continuation nor failure by structural data alone unless a dormancy/recovery rule is added.","witness":"Two reconstructions after identical empty intervals, one source-derived and one independently generated, with equal endpoint state.","proof_spine":"Remove history/dormancy data; the endpoint evidence is identical while intended ancestry differs.","impacts":"TS-02;TS-03;TS-04;TS-05;TS-07;TS-08;TS-09;TS-10","assumptions":"no canonical now or persistence through emptiness","falsifier":"A noncircular dormancy token and recovery law that uniquely carries the relevant object.","nonclaim":"Does not prove gaps are fatal under every ontology."},
 {"id":"NG-11","title":"Carrier-individuation trivialization","claim":"If carrier identity is defined by whatever preserves the desired object, cross-carrier transport becomes circular or collapses to same-carrier re-encoding.","witness":"Choose carrier equivalence after observing the desired verdict so every successful episode is redescribed as one carrier.","proof_spine":"Show the transport predicate is invariant by definition rather than theorem, eliminating falsifying cases.","impacts":"TS-01;TS-02;TS-03;TS-04;TS-05;TS-06;TS-07;TS-08;TS-09;TS-10","assumptions":"carrier tokens must be individuated independently","falsifier":"An exogenous carrier rule fixed before candidate evaluation.","nonclaim":"Does not privilege biological or spatial carrier boundaries."},
 {"id":"NG-12","title":"Bridge-composition noncongruence under route memory","claim":"Pairwise admissible bridges need not compose to the same verdict as a direct bridge when the retained object contains route memory or intermediate-support effects.","witness":"S→M and M→T each preserve local data, while S→T loop comparison flips a retained marker.","proof_spine":"Compute direct and composite actions; their difference is the holonomy/critical-pair residue.","impacts":"TS-01;TS-02;TS-03;TS-05;TS-06;TS-07;TS-08;TS-09;TS-10","assumptions":"route memory admitted","falsifier":"A functoriality or confluence theorem on all retained data.","nonclaim":"Does not require composition to be total."},
 {"id":"NG-13","title":"Finite-instrument nonidentifiability over an open continuation class","claim":"A finite set of probes cannot identify a unique continuation structure over an unrestricted class closed under hidden extensions.","witness":"Extend any probed finite machine with an unprobed state reached after the last admitted horizon.","proof_spine":"Diagonalize beyond the finite probe set while preserving every observed answer.","impacts":"TS-01;TS-02;TS-03;TS-04;TS-05;TS-06;TS-07;TS-08;TS-09;TS-10","assumptions":"open class; finite instrument; hidden extensions","falsifier":"A finite model class with a proved complete distinguishing set.","nonclaim":"Does not preclude exact finite toy theorems."},
 {"id":"NG-14","title":"Certificate match is independent of certificate soundness","claim":"Matching a structural certificate across carriers does not entail that the certificate tracks consciousness unless certificate soundness is separately assumed or established.","witness":"Two interpretations of the same formal certificate, one psychophysically sound and one not, share all structural facts.","proof_spine":"The structural premises are invariant while the ontological interpretation varies.","impacts":"TS-02;TS-05;TS-06;TS-09","assumptions":"certificate soundness not derivable from structural syntax alone","falsifier":"A valid soundness theorem connecting the certificate to the intended ontological predicate.","nonclaim":"Does not refute the certificate's structural usefulness."},
 {"id":"NG-15","title":"Structural lineage does not entail numerical personal identity","claim":"Any structural lineage relation that permits nontrivial fission or fusion cannot be identical to strict numerical identity, which is one-one and transitive in the ordinary sense.","witness":"One source relates to two symmetric successors, or two sources relate to one fusion target.","proof_spine":"Compare the arity of the relation with identity's uniqueness laws.","impacts":"TS-03;TS-07;TS-08;TS-10","assumptions":"ordinary numerical identity laws","falsifier":"A revised identity concept explicitly relation-valued and no longer numerical identity.","nonclaim":"Does not decide what matters for survival."},
 {"id":"NG-16","title":"Symmetry–uniqueness–branch-success trilemma","claim":"In exact symmetric duplication, no criterion can simultaneously be symmetry-invariant, award success to each qualifying branch, and return exactly one unique continuer.","witness":"One source, two symmetric exact targets, both satisfying all branch-local gates.","proof_spine":"Symmetry gives equal verdicts; branch success makes both positive; uniqueness forbids both.","impacts":"TS-01;TS-02;TS-03;TS-05;TS-06;TS-07;TS-08;TS-09;TS-10","assumptions":"exact symmetry; branch-local success","falsifier":"Reject one horn: add asymmetry, deny one branch, or make continuation relation-valued.","nonclaim":"Does not privilege a particular horn."},
 {"id":"NG-17","title":"Fusion conflict for exclusive action-credit ledgers","claim":"Two source histories assigning exclusive credit or incompatible self-coordinates cannot be naively fused into one coherent ledger without a conflict-resolution rule that changes at least one input claim.","witness":"Sources credit incompatible agents for the same exclusive event; target copies both ledgers.","proof_spine":"The conjunction violates exclusivity; any coherent target must revise, contextualize, or branch the claims.","impacts":"TS-02;TS-07;TS-08;TS-10","assumptions":"exclusive credit predicates retained","falsifier":"A typed provenance algebra that embeds both claims without contradiction.","nonclaim":"Does not rule out fusion with transformed provenance."},
 {"id":"NG-18","title":"Essential external support precludes target-native autonomy","claim":"If removal of an external support process necessarily destroys every realization of the declared package, the package is not autonomous on the declared target carrier.","witness":"A target whose temporal order, decoding, repair, or resource regulation is permanently supplied from outside the carrier boundary.","proof_spine":"Apply the declared withdrawal intervention and show no target-only invariant region remains.","impacts":"TS-02;TS-03;TS-04;TS-05;TS-08;TS-09","assumptions":"declared target boundary; target-native autonomy definition","falsifier":"Redraw the carrier boundary before evaluation or prove endogenous regeneration after finite bootstrapping.","nonclaim":"Does not settle consciousness of extended or distributed systems; it tests the declared boundary."
 }
]

RED_TEAMS = [
 {"id":"RT-01","title":"Strict functionalist","thesis":"Exact preservation of the right causal organization should already be sufficient; extra lineage and biological continuity demands risk mystification.","best_hit":"TS-03 may overvalue overlap; TS-04 and TS-08 may duplicate functional organization under new labels.","concession":"A structural project may legitimately seek organizational invariants and reject substrate chemistry as primitive.","required_answer":"Specify exactly which organization is complete enough, how implementation is nonvacuous, and why duplication yields relation-valued rather than unique conclusions.","unresolved":"Organizational invariance remains a philosophical/psychophysical premise, not a theorem derived from SBT."},
 {"id":"RT-02","title":"Biological or dynamical continuity critic","thesis":"A translated abstract structure may be a replica; continuation may require the living, embodied, temporally continuous process itself.","best_hit":"TS-01, TS-02, TS-05, TS-06, TS-09, and TS-10 can succeed without live overlap.","concession":"Process continuity must be specified without simply saying 'the same subject continues.'",
  "required_answer":"Offer a noncircular process invariant, model embodiment/environmental closure explicitly, and explain gaps, destructive copies, and gradual replacement.","unresolved":"SF-02 can represent this view, but no corpus theorem establishes that its process criterion is necessary for consciousness."},
 {"id":"RT-03","title":"Duplication critic","thesis":"Any criterion that says an upload is uniquely me fails when an exactly symmetric second upload is added.","best_hit":"Every function-valued or uniqueness-seeking interpretation of TS-01 through TS-09.","concession":"The symmetry objection is decisive against unpriced unique selection.","required_answer":"Return a relation, branch-valued successor set, principled underdetermination, or an independently justified asymmetry.","unresolved":"Relation-valued lineage avoids contradiction but does not by itself answer first-person anticipation or numerical identity."},
 {"id":"RT-04","title":"SBT audit critic","thesis":"Most attractive results are fixed-support theorems being renamed cross-carrier transport.","best_hit":"TS-01, TS-02, TS-06, TS-07, and TS-09 import quotient, promotion, closure, or holonomy assets.","concession":"The corpus supplies valuable forms and counterexamples, but heterogeneous retyping is new work.","required_answer":"Individuate carriers first, type every leg, register mixed-support stages, and prove that no representative or protocol choice does the transport work.","unresolved":"Whether a nontrivial heterogeneous instance exists remains open for CST-EXP-05/implementation."},
 {"id":"RT-05","title":"Empirical critic","thesis":"Hidden predictive, binding, or lineage structures may be unobservable, so candidates could be empirically indistinguishable.","best_hit":"TS-01, TS-02, TS-07, TS-08, and TS-10 rely on privileged or continuation-complete access in exact toys.","concession":"Finite theorem targets can use complete state access without claiming an immediate biological instrument.","required_answer":"Separate exact toy decidability from empirical recognition; specify probe completeness, error bounds, and underdetermination when access is insufficient.","unresolved":"No empirical certificate-soundness or recognition bridge has been established."},
 {"id":"RT-06","title":"Formal-methods critic","thesis":"The objects may not compose, quotient choices may be noncanonical, and approximate errors may explode at critical pairs.","best_hit":"TS-01, TS-03, TS-06, TS-07, TS-09, and TS-10.","concession":"CST-EXP-03 supplied signatures and falsifiers, but not proofs.","required_answer":"Provide finite exact semantics, total/partial composition laws, confluence or holonomy witnesses, representative invariance, and local stability bounds.","unresolved":"These are theorem-reconnaissance obligations, not results of this phase."},
 {"id":"RT-07","title":"Ontological skeptic","thesis":"Even perfect structural transport and lineage may prove only structural facts, not consciousness, survival, or personal identity.","best_hit":"All candidates whenever structural outputs are narrated ontologically.","concession":"The separation of S-T, S-R, S-L, A, R, and O is the correct discipline.","required_answer":"Price certificate soundness, A1, A2-P, recognition, and personal-identity interpretation separately; state the exact structural ceiling.","unresolved":"The project can land strong conditional mathematics without resolving the metaphysics."
 }
]

EXTERNAL_SOURCES = [
 {"id":"EXT-001","category":"organizational_invariance","year":"1995","authors":"David J. Chalmers","title":"Absent Qualia, Fading Qualia, Dancing Qualia","venue":"Conscious Experience (Metzinger, ed.)","identifier":"author manuscript","source_type":"philosophical argument; author primary text","challenge":"Provides the strongest organizational-invariance case, but explicitly functions as an argument rather than a cross-carrier transport theorem.","supports":"SF-01;TS-01;TS-02","presses":"RT-01;NG-14","url":"https://consc.net/papers/qualia.html"},
 {"id":"EXT-002","category":"computation_and_implementation","year":"2012","authors":"David J. Chalmers","title":"A Computational Foundation for the Study of Cognition","venue":"Journal of Cognitive Science 13(4)","identifier":"author manuscript; written 1993","source_type":"philosophical/formal framework; author primary text","challenge":"Demands a nonvacuous implementation relation in which physical causal structure mirrors formal computation; computational sufficiency still spends organizational invariance.","supports":"TS-01;TS-05","presses":"NG-11;RT-01;RT-06","url":"https://consc.net/papers/computation.html"},
 {"id":"EXT-003","category":"branching_identity","year":"2015","authors":"Michael A. Cerullo","title":"Uploading and Branching Identity","venue":"Minds and Machines 25:17–36","identifier":"doi:10.1007/s11023-014-9352-8","source_type":"peer-reviewed philosophy","challenge":"Shows how branching accounts can let original and upload both continue after nondestructive uploading, while exposing timing and merger difficulties.","supports":"SF-03;TS-10","presses":"NG-15;NG-16;RT-03","url":"https://doi.org/10.1007/s11023-014-9352-8"},
 {"id":"EXT-004","category":"mind_uploading_identity","year":"2023","authors":"Sebastian Gäb","title":"Should You Upload Your Mind?","venue":"Religious Studies","identifier":"doi:10.1017/S0034412523000128","source_type":"peer-reviewed philosophy","challenge":"Separates technical emulation from the prudential and identity question and surveys continuity objections.","supports":"","presses":"SF-01;SF-02;SF-03;RT-07","url":"https://doi.org/10.1017/S0034412523000128"},
 {"id":"EXT-005","category":"mind_uploading_identity","year":"2016","authors":"Keith B. Wiley; Randal A. Koene","title":"The Fallacy of Favoring Gradual Replacement Mind Uploading Over Scan-and-Copy","venue":"Journal of Consciousness Studies 23(3–4):212–235","identifier":"arXiv:1504.06320","source_type":"peer-reviewed philosophy of uploading","challenge":"Argues for metaphysical parity across a replacement/copy spectrum, forcing any process-sensitive criterion to identify a principled non-question-begging difference.","supports":"TS-01;TS-02","presses":"SF-02;RT-02","url":"https://arxiv.org/abs/1504.06320"},
 {"id":"EXT-006","category":"whole_brain_emulation","year":"2008","authors":"Anders Sandberg; Nick Bostrom","title":"Whole Brain Emulation: A Roadmap","venue":"Future of Humanity Institute Technical Report 2008-3","identifier":"Oxford ORA uuid:a6880196-34c7-47a0-80f1-74d32ab98788","source_type":"technical roadmap","challenge":"Clarifies that WBE is an engineering/research program requiring acquisition, modeling, and execution fidelity; it does not settle consciousness or personal identity.","supports":"TS-05;TS-09","presses":"RT-05;NG-14","url":"https://ora.ox.ac.uk/objects/uuid:a6880196-34c7-47a0-80f1-74d32ab98788"},
 {"id":"EXT-007","category":"whole_brain_emulation","year":"2025","authors":"Niccolò Zanichelli; Maximilian Schons; Isaak Freeman; Philip K. Shiu; Anton Arkhipov","title":"State of Brain Emulation Report 2025","venue":"arXiv","identifier":"arXiv:2510.15745","source_type":"current technical survey/preprint","challenge":"Updates the practical bottlenecks in recording, reconstruction, biological knowledge, and simulation; reinforces that structural targets must state acquisition and approximation assumptions.","supports":"TS-09","presses":"RT-05;NG-13","url":"https://arxiv.org/abs/2510.15745"},
 {"id":"EXT-008","category":"enactivism_autonomy","year":"2017","authors":"Xabier E. Barandiaran","title":"Autonomy and Enactivism: Towards a Theory of Sensorimotor Autonomous Agency","venue":"Topoi 36:409–430","identifier":"doi:10.1007/s11245-016-9365-4","source_type":"peer-reviewed philosophy/theory","challenge":"Makes autonomy and sensorimotor organization central, pressing against snapshot or externally sustained transfer criteria.","supports":"TS-04;SF-02","presses":"TS-01;TS-05;NG-18","url":"https://doi.org/10.1007/s11245-016-9365-4"},
 {"id":"EXT-009","category":"enactivism_autonomy","year":"2018","authors":"Mario Villalobos; Joe Dewhurst","title":"Enactive Autonomy in Computational Systems","venue":"Synthese 195:1891–1908","identifier":"doi:10.1007/s11229-017-1386-z","source_type":"peer-reviewed philosophy/formal example","challenge":"Shows that computational systems can be analyzed using operational closure and structural determinism, so autonomy cannot simply be reserved for biology; precariousness remains an additional issue.","supports":"TS-04;SF-01;SF-02","presses":"RT-02","url":"https://doi.org/10.1007/s11229-017-1386-z"},
 {"id":"EXT-010","category":"causal_structure_consciousness","year":"2023","authors":"Larissa Albantakis et al.","title":"Integrated Information Theory (IIT) 4.0: Formulating the Properties of Phenomenal Existence in Physical Terms","venue":"PLOS Computational Biology 19(10):e1011465","identifier":"doi:10.1371/journal.pcbi.1011465","source_type":"peer-reviewed theory","challenge":"Offers a sharply specified intrinsic causal-structure target applicable in principle to arbitrary systems, but its postulates and exclusion/uniqueness commitments collide with copying and alternative certificate choices.","supports":"TS-02;TS-06","presses":"NG-14;RT-07","url":"https://doi.org/10.1371/journal.pcbi.1011465"},
 {"id":"EXT-011","category":"consciousness_empirical","year":"2025","authors":"Cogitate Consortium; Lucia Melloni et al.","title":"Adversarial Testing of Global Neuronal Workspace and Integrated Information Theories of Consciousness","venue":"Nature 642:133–142","identifier":"doi:10.1038/s41586-025-08888-1","source_type":"peer-reviewed preregistered adversarial experiment","challenge":"Theory-neutral preregistered tests supported some predictions while substantially challenging key tenets of both IIT and GNWT, warning against treating any present certificate as settled.","supports":"RT-05","presses":"TS-02;NG-14","url":"https://doi.org/10.1038/s41586-025-08888-1"},
 {"id":"EXT-012","category":"causal_structure_consciousness","year":"2019","authors":"Adrien Doerig; Aaron Schurger; Kathryn Hess; Michael H. Herzog","title":"The Unfolding Argument: Why IIT and Other Causal Structure Theories Cannot Explain Consciousness","venue":"Consciousness and Cognition 72:49–59","identifier":"doi:10.1016/j.concog.2019.04.002","source_type":"peer-reviewed argument","challenge":"Presses causal-structure theories with functionally equivalent unfolded systems and demands clarity about which internal properties are empirically discriminable.","supports":"RT-01;RT-05","presses":"TS-02;TS-06;NG-01","url":"https://doi.org/10.1016/j.concog.2019.04.002"},
 {"id":"EXT-013","category":"causal_structure_consciousness","year":"2026","authors":"Vikas N. O'Reilly-Shah; Alessandro Maria Selvitella; Aaron Schurger","title":"A Caveat Regarding the Unfolding Argument: Implications of Plasticity","venue":"Neuroscience of Consciousness 2026(1):niag027","identifier":"doi:10.1093/nc/niag027","source_type":"peer-reviewed mathematical analysis","challenge":"Shows rapid plasticity/history dependence can break static feedforward functional equivalence, but explicitly does not prove recurrence, plasticity, or process necessary for consciousness.","supports":"TS-03;TS-08","presses":"RT-01;NG-09","url":"https://doi.org/10.1093/nc/niag027"},
 {"id":"EXT-014","category":"causal_abstraction","year":"2019","authors":"Sander Beckers; Joseph Y. Halpern","title":"Abstracting Causal Models","venue":"AAAI 33:2678–2685","identifier":"doi:10.1609/aaai.v33i01.33012678","source_type":"peer-reviewed formal methods","challenge":"Provides increasingly strict exact abstraction notions and intervention maps, useful for preventing arbitrary label isomorphisms from masquerading as implementation.","supports":"TS-01;TS-05;TS-09","presses":"NG-11;RT-06","url":"https://doi.org/10.1609/aaai.v33i01.33012678"},
 {"id":"EXT-015","category":"causal_abstraction","year":"2020","authors":"Sander Beckers; Frederick Eberhardt; Joseph Y. Halpern","title":"Approximate Causal Abstractions","venue":"UAI/PMLR 115:606–615","identifier":"PMLR v115:beckers20a","source_type":"peer-reviewed formal methods","challenge":"Supplies explicit approximation between causal levels and shows where discrepancy and uncertainty enter; supports vectorized, intervention-aware residuals rather than raw state similarity.","supports":"TS-09","presses":"NG-07;RT-06","url":"https://proceedings.mlr.press/v115/beckers20a.html"},
 {"id":"EXT-016","category":"causal_abstraction","year":"2025","authors":"Atticus Geiger et al.","title":"Causal Abstraction: A Theoretical Foundation for Mechanistic Interpretability","venue":"JMLR 26(83):1–64","identifier":"JMLR 26/23-0058","source_type":"peer-reviewed formal framework","challenge":"Generalizes causal abstraction to mechanism transformations and graded faithfulness, reinforcing the need for intervention-preserving maps and explicit granularity.","supports":"TS-01;TS-09","presses":"NG-13;RT-06","url":"https://jmlr.org/papers/v26/23-0058.html"},
 {"id":"EXT-017","category":"bisimulation_dynamics","year":"2004","authors":"A. J. van der Schaft","title":"Equivalence of Dynamical Systems by Bisimulation","venue":"IEEE Transactions on Automatic Control 49(12):2160–2172","identifier":"doi:10.1109/TAC.2004.838497","source_type":"peer-reviewed formal systems","challenge":"Demonstrates that dynamic equivalence requires a typed relation respecting trajectories, not endpoint matching; also sharpens composition obligations.","supports":"TS-01;TS-03","presses":"RT-06","url":"https://doi.org/10.1109/TAC.2004.838497"},
 {"id":"EXT-018","category":"bisimulation_dynamics","year":"2007","authors":"Antoine Girard; George J. Pappas","title":"Approximation Metrics for Discrete and Continuous Systems","venue":"IEEE Transactions on Automatic Control 52(5):782–798","identifier":"doi:10.1109/TAC.2007.895849","source_type":"peer-reviewed formal systems","challenge":"Provides approximate bisimulation-style metrics, emphasizing declared outputs, trajectories, and error propagation rather than vague similarity.","supports":"TS-09;TS-01","presses":"NG-07","url":"https://doi.org/10.1109/TAC.2007.895849"},
 {"id":"EXT-019","category":"logical_object_persistence","year":"2024","authors":"C. Ryan-Anderson et al.","title":"High-fidelity and Fault-tolerant Teleportation of a Logical Qubit Using Transversal Gates and Lattice Surgery","venue":"arXiv; trapped-ion experiment","identifier":"arXiv:2404.16728","source_type":"experimental quantum information","challenge":"Shows a logical object can be moved with explicit code, syndrome, correction, and process-fidelity audits; the analogy highlights how underspecified the consciousness code/recovery map remains.","supports":"TS-05","presses":"NG-14;RT-06","url":"https://arxiv.org/abs/2404.16728"},
 {"id":"EXT-020","category":"logical_object_persistence","year":"2025","authors":"Google Quantum AI and Collaborators","title":"Quantum Error Correction Below the Surface Code Threshold","venue":"Nature 638:920–926","identifier":"doi:10.1038/s41586-024-08449-y","source_type":"peer-reviewed experimental quantum information","challenge":"Demonstrates below-threshold logical error suppression with explicit code distance and decoder performance, reinforcing the need for a declared error model and scaling law.","supports":"TS-05;TS-09","presses":"NG-07","url":"https://doi.org/10.1038/s41586-024-08449-y"},
 {"id":"EXT-021","category":"process_migration","year":"2005","authors":"Christopher Clark et al.","title":"Live Migration of Virtual Machines","venue":"NSDI 2005","identifier":"USENIX NSDI 05 paper 269357","source_type":"peer-reviewed systems engineering","challenge":"Shows service/process migration depends on iterative state transfer, bounded downtime, and explicit resource handling; operational continuity is engineered rather than inferred from endpoint similarity.","supports":"TS-03;TS-05","presses":"NG-12;RT-06","url":"https://www.usenix.org/conference/nsdi-05/live-migration-virtual-machines"},
 {"id":"EXT-022","category":"distributed_state","year":"1985","authors":"K. Mani Chandy; Leslie Lamport","title":"Distributed Snapshots: Determining Global States of Distributed Systems","venue":"ACM Transactions on Computer Systems 3(1):63–75","identifier":"doi:10.1145/214451.214456","source_type":"peer-reviewed distributed systems","challenge":"Provides a consistent-cut method for global state without a universal clock, directly relevant to mixed-support handoff and noncanonical now.","supports":"TS-06;TS-08","presses":"NG-08;NG-10","url":"https://doi.org/10.1145/214451.214456"},
 {"id":"EXT-023","category":"distributed_state","year":"2010","authors":"Leslie Lamport; Dahlia Malkhi; Lidong Zhou","title":"Reconfiguring a State Machine","venue":"SIGACT News 41(1):63–73","identifier":"doi:10.1145/1753171.1753191","source_type":"peer-reviewed distributed systems","challenge":"Treats membership/support change as a protocol with safety obligations, a useful analogue for carrier reconfiguration and bridge composition.","supports":"TS-03;TS-06;TS-07","presses":"NG-12","url":"https://doi.org/10.1145/1753171.1753191"},
 {"id":"EXT-024","category":"copying_and_observers","year":"2018","authors":"Charles T. Sebens; Sean M. Carroll","title":"Self-Locating Uncertainty and the Origin of Probability in Everettian Quantum Mechanics","venue":"British Journal for the Philosophy of Science 69(1):25–74","identifier":"doi:10.1093/bjps/axw004","source_type":"peer-reviewed philosophy of physics","challenge":"Formalizes epistemic uncertainty among qualitatively identical post-branch observers; useful as a warning that branch-local indistinguishability does not restore one unique pre-branch location.","supports":"TS-10;SF-03","presses":"RT-03;NG-16","url":"https://doi.org/10.1093/bjps/axw004"},
 {"id":"EXT-025","category":"personal_identity","year":"2018","authors":"Michael Otsuka","title":"Personal Identity, Substantial Change, and the Significance of Becoming","venue":"Erkenntnis 83:1229–1243","identifier":"doi:10.1007/s10670-017-9949-7","source_type":"peer-reviewed philosophy","challenge":"Distinguishes rational anticipation in fission from mere replication, pressing candidate lineages to explain rather than stipulate the source of ancestry.","supports":"SF-02;SF-03","presses":"NG-09;RT-03","url":"https://doi.org/10.1007/s10670-017-9949-7"},
 {"id":"EXT-026","category":"personal_identity","year":"1984","authors":"Derek Parfit","title":"Reasons and Persons, Part III","venue":"Oxford University Press","identifier":"ISBN 9780198249085","source_type":"major philosophical monograph","challenge":"Makes fission, psychological continuity, and the possibility that identity is not what matters central to the modern debate.","supports":"SF-03","presses":"NG-15;NG-16;RT-07","url":"https://global.oup.com/academic/product/reasons-and-persons-9780198249085"},
]

PHASE_DECISIONS = [
 ("D04-001","stress_before_selection","No candidate is selected; all ten are attacked before survivor-family synthesis.","Prevents favored-candidate rescue and preserves the planned ordering."),
 ("D04-002","component_salvage","A candidate may fail as a complete criterion while surviving as a mandatory gate, bridge mechanism, or approximation layer.","The strongest reusable content should not be lost with an overbroad claim."),
 ("D04-003","underdetermination_is_typed","A principled underdetermination result counts as coherent only when the missing data and blocked inference are named.","Silence or vagueness is not a valid verdict."),
 ("D04-004","symmetry_rule","No survivor may select one of two exact symmetric targets without an independently declared asymmetry.","Otherwise the selection is arbitrary or conclusion-equivalent."),
 ("D04-005","external_literature_role","External literature challenges and retypes internal candidates; it does not define the project target.","Maintains independence of candidate generation while confronting prior art."),
 ("D04-006","no_go_status","All NG records are conjecture/prospectus items unless a later phase supplies a proof.","This phase mines theorem shapes but does not claim proofs."),
 ("D04-007","survivor_family_count","Freeze three survivor families and seven component/mechanism roles; do not rank the three families.","The families answer different lanes and will be tested for finite landability in CST-EXP-05."),
 ("D04-008","ontology_ceiling","A1, A2-P, certificate soundness, recognition, and personal-identity interpretation remain separately priced and do not rescue structural failures.","Avoids hidden ontological expenditure."),
]

UNRESOLVED = [
 "Can SF-01 be instantiated nontrivially in a finite model without defining the C-package by its desired verdict?",
 "Which minimal process invariant lets SF-02 distinguish live handoff from copying without privileging biology by fiat?",
 "Can SF-03 generate ancestry from finite operational facts while excluding independently constructed structural twins?",
 "Which route/recombination data are minimally necessary across all three survivor families?",
 "Can target autonomy be stated over a distributed carrier boundary without making the boundary verdict-dependent?",
 "What exact stability assumptions prevent local catastrophic defects under approximate transport?",
 "Can one theorem family connect SF-01 target realization with either SF-02 or SF-03 lineage without conflating the lanes?",
 "Which no-go prospectus has the smallest finite witness and the strongest implementation-independent statement?",
 "What finite complete-instrument assumptions are acceptable for toys while remaining honest about empirical nonidentifiability?",
 "Can fusion provenance be made coherent without erasing exclusive action-credit information?",
]
