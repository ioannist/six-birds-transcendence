
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
