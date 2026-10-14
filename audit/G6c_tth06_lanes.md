# G6c — POS-04-family Temporal-FIACH evidence, versions F and O

## Statement, domain and ceiling

TTH-06 keeps its exact text: “A valid Temporal-FIACH certificate entails, as
separate fields, integrated target realization, strict temporal lineage, and
post-withdrawal autonomy; none of the three is inferred from either of the others.”

The new POS-04-family theorem quantifies over **every raw assignment and withdrawal
rule in the declared finite typed POS-04 primitive interface**, not just the
canonical model or the three controls. The finite factor is the tagged T1
carrier. The counter-bearing runs and disturbance words are unbounded. This is
not a theorem for arbitrary unrelated carrier alphabets, cells, actions, events,
routes, stages, covers or audit domains. **TTH-06 remains `conditional`: this
does not discharge G0's broader `RawHandoff` contract.** The owner chose to
prove that stronger contract in follow-up packets, not narrow or split the row. The nominal disturbance
interface is explicitly a singleton; responses are robust over their **entire
positive-probability support**, not over resource shocks. C4–C7 retain their
surrogate grades. Neither full P05 realization, T17-I, recognition, nor a physical
system is claimed.

**Further kernel-proved limitation (G6d semantic seam):** the legacy G6c
lineage lane omits complete actual-execution transport. The theorem
`CSTTT.TargetTheory.GenericHandoff.POS04LineageFutureBoundary.legacy_readout_does_not_imply_complete_bridge`
exhibits an assignment accepted by the legacy named lineage readout while an
actual supported, audited branch has source probability **1** and target
probability **0**. Its lethal outcomes `exit2` and `exit5` differ in the full
C6 observation, but the legacy `FiniteActionMap` checks only destinations
inside K. The legacy `temporalFIACH_sound_F` and `temporalFIACH_sound_O`
remain correct for their **weaker defined conclusion**; they are not evidence
for complete execution transport. Keep these declarations and the regression
with that limit. The strengthened family lineage and F/O soundness are now
proved separately in `POS04CompleteLineage` and `POS04CompleteFIACH` (see
`G6d_complete_lineage.md`). TTH-06 remains `conditional` pending the polymorphic
`RawHandoff` assembly; the strengthened family result does not discharge it.

For F, “none inferred” means **proof-structural separation**, as explicitly
chosen in G6a: each lane is derived from its own computed check. The logical
implication `AF → P` is proved and disclosed. For supplementary O, autonomy means
operational C8 viability (N3), and the three lanes are logically independent.
The original schema-level `temporalFIACHCertificateSoundness` is retained and
is not used as the new generic evidence.

## POS-04-family certificate and separate readouts

`Assembly.lean` defines `FiniteFIACHCertificate` with **one raw `model` field**.
It contains no proof field, free proposition, stored safe set, derived object,
or expected verdict. Its inhabitation alone is not evidence: `validF`/`validO`
are computed validity checks. `full_certificate_satisfiable` and
`operational_certificate_satisfiable` prove valid inhabitation.

```lean
temporalFIACH_sound_F (c : FiniteFIACHCertificate) (h : validF c = true) :
  IntegratedTargetRealization c.model ∧ StrictTemporalLineage c.model ∧
    PostWithdrawalFullAutonomy c.model

temporalFIACH_sound_O (c : FiniteFIACHCertificate) (h : validO c = true) :
  IntegratedTargetRealization c.model ∧ StrictTemporalLineage c.model ∧
    PostWithdrawalOperationalAutonomy c.model
```

| Readout | Computed subcheck | Derivation; other lanes unused |
|---|---|---|
| P / integrated realization | `packageLaneCheck` | `derive_package_lane`: G2c total/value/edge checks, exact mapped restrictions, clause locality and all eight clauses on the **constructed** global assignment |
| L / strict lineage | `lineageLaneCheck` | `derive_lineage_lane`: constructed G4 atomic corridor, full assignment-indexed G1c frozen-signature result for all four snapshots, typed endpoint link, computed route-indexed status |
| AF / full autonomy | `fullAutonomyCheck` | `derive_full_autonomy_lane`: package-filtered greatest set, every derived entry inside, actual TTH-05 certificate for every entry |
| AO / operational autonomy | `operationalAutonomyCheck` | `derive_operational_autonomy_lane`: C8's generic greatest viable set |
| source package / staging | separate source and staging checks | `validF_source_and_staging`; G2c's `image_eq_assembled`, `image_values`, `image_edges`, `image_total`, `image_mapped` establish the raw equations |
| recognition | defined `.notAddressed` | `certificate_recognition_not_addressed`; outside the structural claim |

`fullAutonomy_implies_package` is not used to obtain the P conclusion in either
soundness proof. `AF_each_entry_nominal_words` and
`temporalFIACH_full_nominal_words` transport the existing TTH-05 theorem to
**every** entry and **every finite nominal disturbance word**. The controlled
response has an existential successor, as TTH-05 requires; the separate
`response_all_support`/`greatestF_all_support_responses` theorems prove that all
positive-probability successors are safe. Run-level advancement is supplied by
`greatestF_c6_advancement`, not by strict growth on a recurrent finite factor.

## One assignment, one acquisition, real dynamics

`image a := exchangeAssignment a`; `image_eq_assembled` equates it to G2c's glued
assignment for every assignment, including partial ones. `checkedAcquisition`
checks its complete dependency scope and returns exactly that image. It never
accepts an independently supplied acquisition adapter.

- `AtomicAcquisition.lean`: G4 stages, vertices, edges, realization, support,
  interventions, owner and residue come from that same view. The frozen G6b A2
  stage-position geometry interpretation is retained: deleting an event support
  bit removes the owned event vertex, not the fixed stage position.
- `SnapshotExecution.lean`: every raw history edge is supported; its positive
  probability, quotient outcome, exact representative and **whole updated run**
  are checked. All four snapshots (both routes, `afterFirst` and `endpoint`)
  have executed roots and prefixes. `acquisition_execution_sound` links them
  to the computed future closure and observations.
- `AssignmentBridge.lean`: `assignmentRawBridge` constructs every RawBridge
  field from the staged assignment. `acquisition_factor_bridge_laws` proves
  the raw coordinate, strict-step, successor, tick, progress, record, route,
  maintenance and owner laws. Raw predictive classes are computed from actual
  action supports, hazards and positions; the canonical M-link remains proved.
- `BridgeReadouts.lean`: weights equal the assigned action-row class masses;
  updater, code and full eight-component observation are defined. The owner
  readout prevents invalid cross-tag code equality. The all-state bisimulation
  yields `assignment_bridge_all_words` by the generic induction, not a bounded
  horizon. Counter/ledger/writer/readout laws hold on **all runs**, which is
  stronger than the required computed-closure restriction.
- `BridgeCoherence.lean`: finite raw-row, representative and tick checks derive
  `BridgeRunCoherence`. `SnapshotExecutionEquations` pins the RawBridge roots
  to the actually executed assignment snapshots. `acquisition_bridge_frozen`
  constructs every frozen signature field, exact finite-image codecs, typed
  transport and the attached full-interface future-sufficiency theorem.
- `Endpoint.lean`: `TypedAcquisitionEndpointPass` checks the raw receiver,
  source/target history terminal, predictive class, actual corridor exit,
  ownership and final atomic frontier. Route status uses supported raw tuples,
  a nonempty comparison domain, shared endpoint, distinct retained provenance
  and defined distinct readouts; it is not a stored label.

The wheel-coordinate receiver makes class transport near-automatic, and the
first-phase route readout is designed, as disclosed in G6/M3. No new causal
claim is attributed to those displays.

## Autonomy construction and exact controls

`ExactAutonomyTransport.lean` constructs `computedAutonomySystem`, withdrawal,
resources, response relation, packageInside and `computedExactAutonomy` from
raw assigned data. The six role codes are enum positions; the recharge code is
the next enum position, not a tuned constant. `AF_exact_certificate` constructs
the existing `ExactAutonomyCertificate` using actual resource closure and
ownership, all-support responses and assigned ledger/advancement checks.

The fixed-point arguments are generic: `pruneF_mono`, `greatestF_fixed`,
`greatestF_viable`, `greatestF_contains_viable`; O reuses the corresponding
assigned C8 results. No invariant set is supplied.

The lane columns below hold both for the computed acceptance predicates and
for the named readout propositions, proved by the new readout vector theorems.

| Registered raw intervention | P | L | AF | AO | SF | SO |
|---|---|---|---|---|---|---|
| Baseline | T | T | T | T | K | K |
| Delete `.publishedC` | F | T | F | T | empty | K |
| Clear only `mix2.sourceSupport` | T | F | T | T | K | K |
| Remove only retained target recharge | T | T | F | F | empty | empty |

`F_control_vectors` proves F's `(F,T,F)`, `(T,F,T)`, `(T,T,F)`; the first is the
registered logical dependence, not an isolation control. `O_control_vectors`
proves `(F,T,T)`, `(T,F,T)`, `(T,T,F)`.
`operational_lanes_logically_independent` supplies the three raw existential
witnesses **for the acceptance predicates**. The new
`operational_readouts_logically_independent` exports independence of the actual
named readouts `IntegratedTargetRealization`, `StrictTemporalLineage`, and
`PostWithdrawalOperationalAutonomy`. `F_readout_control_vectors` and
`O_readout_control_vectors` prove the same registered vectors for those readouts
(F uses `PostWithdrawalFullAutonomy`). Their negative cases are proved directly:

- `package_deletion_no_realization`: required `MapTotal` would require a value
  at deleted `.publishedC`; this is impossible.
- `lineage_deletion_no_strict_lineage`: its corridor witness requires the
  atomic audit vertex that `mix2.sourceSupport` deletion removes.
- `package_deletion_no_full_readout`, `withdrawal_deletion_no_full_readout`,
  and `withdrawal_deletion_no_operational_readout`: the corresponding named
  autonomy readout includes the rejected AF/AO obligation itself.

No negative conclusion is inferred merely from failure of a sufficient check. Package/withdrawal deletion leave acquisition unchanged by proved
cell/locality equations. Lineage deletion's package checks inspect the changed
C6/C7 events explicitly; untouched clauses use locality. No acceptance rule
was changed to make a proof normalize.

The reversal regression exchanges the two genuine source histories. Computed
route outputs become **1/0** and full corridor, bridge, endpoint and lineage
still pass. Baseline **0/1** is a theorem, never a gate.

## Missing inputs and guards

Phase-2 execution has its own completeness check covering staged source and
target rows, policy, target ticks/resources, ledger, histories, events,
realization, receiver, routes and writers. `phase2_missing_dependency` and its
no-entry/F/O consequences reject **each** consumed dependency before decoder
defaults can support an acceptance result. In particular, deleting original
target rows removes staged source rows and rejects O. Missing receiver inputs
also reject phase-2 execution. The wider acquisition completeness gate covers
both C6 scopes.

| Raw field family | Constraint | Guard theorem |
|---|---|---|
| primitive presence / 160 coordinate views | Complete assignment; shared cells and clause-local decoding | `package_lane_missing`, quantified over every cell |
| coordinate/value maps, scopes/cover/adjacency | Defined exchange and checked G2c arrival cover; independent gluing equations | G2c non-total/value/overlap guards; `image_eq_assembled` |
| source/target rows, policy | Every supported raw history edge; normalization, class mass and representatives; P unchanged under withdrawal | `empty_acquisition_rows_reject_execution`; quantified `acquisition_execution_missing_dependency` |
| hazards/positions and computed M | Assigned raw predictive calculation and finite factor/map checks | quantified `acquisition_bridge_missing_dependency`; existing C1–C3 raw-field guards |
| histories/routes | Actual route tuples; complete prefixes; all four snapshots | `truncated_acquisition_histories_reject_execution`; missing history/route guards |
| receiver activation/availability | `active7`, realized phase-2 path before entries | `source_absent_no_entries`, `source_absent_not_AF`, `source_absent_not_AO`, `source_absent_reject_execution` |
| realization, strict events, support/interventions | Assigned C6 trace and actual G4 atomic expansion | `lineage_deletion_not_lineage_lane`; assigned realized-stage/strict-step guards |
| resources, ownership and ledger | Assigned funded positive unit conservation; actual retained recharge | `withdrawal_deletion_not_AF`, `withdrawal_deletion_not_AO`; assigned C6/C8 resource/zero-ledger guards |
| every withdrawal role | All six required roles, exact declared role domain | `missing_withdrawal_role_rejects` for **each** role; `withdrawal_failure_rejects_F_O` |
| post-withdrawal source availability | Source must be absent, independently checked | `source_available_after_withdrawal_rejects`; `withdrawal_failure_rejects_F_O` |
| route comparison and endpoint | Shared endpoint; supported nonempty domain; defined distinct computed outputs | `acquisition_equal_route_outputs_reject`, `acquisition_undefined_route_output_reject`; reversal passes |

## Closure-wide readout coverage

The following laws are fields of `BridgeReadoutUpdateAt`; they are derived by
`assignment_bridge_readout_updates` from assigned C6 acceptance, and therefore
checked throughout the computed closure (indeed on all runs). Every corrupted
proposal changes **only** the named readout, retaining the raw dynamics and
update recipes. `acquisition_every_bridge_readout_guard` dispatches over all 13
fields; none can silently disappear. These proposals are sensitivity guards,
not new scientific models or inputs to validity.

| Readout | Update/preservation law | Guard in `Guards.lean` |
|---|---|---|
| predictive | Class of actual assigned successor representative | `acquisition_predictive_readout_guard` |
| event counter/order | Counter + 1 | `acquisition_counter_readout_guard` |
| ticks | Counter + actual assigned action delta; positive on supported steps | `acquisition_ticks_readout_guard` |
| tick phase | Updated ticks modulo the declared period | `acquisition_tickPhase_readout_guard` |
| progress | Unbounded progress + 1 on supported steps | `acquisition_progress_readout_guard` |
| writer | Assigned route writer under translated owner | `acquisition_writer_readout_guard` |
| record | Funded/writer counter + 1; no capped value | `acquisition_record_readout_guard` |
| residue | Raw register preserved by funded update | `acquisition_residue_readout_guard` |
| maintenance | Assigned positive conserved ledger, updated funding | `acquisition_maintenance_readout_guard` |
| owner | Actual assigned typed owner preserved | `acquisition_owner_readout_guard` |
| enabled | Updated maintenance/owner rule | `acquisition_enabled_readout_guard` |
| source factor | Actual updater factor with source tag projection | `acquisition_sourceFactor_readout_guard` |
| target factor | Actual updater factor with target tag projection | `acquisition_targetFactor_readout_guard` |
| budget (assigned C6, not an extra frozen field) | Positive unit budget/cost/recharge conservation | `assigned_ledger6_guard`, zero-ledger rejection, `greatestF_c6_advancement` |

## Argument classification

| Argument | Classification | Check or definition |
|---|---|---|
| `RawLaneModel.assignment` | raw data | Immutable typed primitives; shared references are views of the same cells |
| `retained`, `removed`, `sourcePresentAfterWithdrawal` | raw data | Effective recharge and explicit six-role/source-absence checks |
| `FiniteFIACHCertificate.model` | raw data | Exactly the above record; no validity evidence stored |
| `h : validF/O c = true` and subcheck hypotheses | evidence on raw data | Defined finite checks, not supplied arbitrary propositions |
| comparison set `S` in greatest-ness | raw comparison data plus viability evidence | Generic monotonicity/containment; never used as the certified invariant |
| source/target maps, cover and disturbance alphabet | defined declared interface | G2c exchange/cover; singleton nominal G6 domain, not optional candidate arguments |
| mapped locals / global / acquisition view | defined objects | Derived from assignment; exact exchange/gluing equation and completeness |
| atomic leg, G1c bridge, four snapshots and typed link | defined objects | Same checked acquisition cells; no fixed positive adapter conjoined |
| dynamics / weights / updater / code / observer / closure | defined objects | Assigned C6 and constructed RawBridge; no candidate freedom |
| SF/SO, packageInside, entries and responses | defined objects | Finite fixed-point computation, activated raw all-support execution |
| `computedExactAutonomy` / frozen signatures | defined objects | Constructed from those computed data and readouts |
| readout-corruption proposals | guard-only objects | Cannot be supplied to certificate validity |

## Transcription, status and statement classification

`check_tth06_transcription.py` obtains fresh Lean-evaluated JSON through a `/tmp`
probe. Expensive lane/GFP exports are reduced using **Lean-checked equality proofs**
to the original computations, not trusted expected outputs; the probe rejects
any candidate without such an equation. It compares all four F/O vectors,
both computed greatest sets, every
phase-2 support entry (exact rational probability/budget, factor, tick, counter,
register), effective ledgers, funded route readouts, and four snapshot coordinate
checks/occurrences against **frozen G6b results**. Planted lane, `3/8` probability,
invariant, readout and intermediate-snapshot drift must each be caught. The
existing L5 checker covers raw POS-04 transcription. This finite comparison is
not substituted for unbounded-word or generic greatest-ness proofs.

**Decision after Eddy CR3: revert TTH-06 to `conditional`.** The exact text
is unchanged and is neither narrowed nor split. The soundness theorems, valid
positive certificates, TTH-05 entry transport, AF→P, acceptance and readout
control vectors, and O readout independence remain in `kernel_evidence` as
**POS-04-family evidence**. The ceiling states that assignments vary within a
fixed interface, carrier family, stage, cover and audit domain. The rationale
records the broader generalization still required. No
exact-statement narrowing is applied; the ceiling records the declared finite
interface, nominal/all-support robustness, C4–C7 surrogates and the F/O readings.
All new declarations are **(b) mathematical additions for TTH-06** implementing
the accepted G6 contract. Existing committed declarations are unchanged; no
(a) rename occurs. G6a/G6b, POS-04 and CST-TT-08 remain byte-identical.

## Prior continuation checks (historical)

- `cd lean && lake build`: exit 0, 350 jobs, 16.23 seconds for the final
  incremental build (including the added supported guard-step theorem). First builds of `BridgeCoherence`, `Endpoint`, `Assembly`
  and `Guards` took 109, 20, 69 and 11 seconds respectively (13 seconds on the
  final Guards rebuild). No new warnings;
  existing vendor/CSTTT linter warnings are replayed.
- `python3 -B scripts/check_tth06_transcription.py`: exact comparison passes;
  all five planted drifts caught (lane, probability, invariant, route readout,
  intermediate snapshot). `check_pos04_transcription.py` also passes its full
  raw coverage and planted rule/rational drifts.
- `/tmp/G6c_complete_axioms.lean`: all 104 newly added theorem declarations checked;
  only standard `propext`, `Quot.sound`, `Classical.choice` (or fewer).
- Inventory regenerated from the 09 surface. `scripts/validate_lean.sh`: exit 0, overall pass; 39 rows, 207 declaration
  entries / 206 unique; 198 theorem-kind, 8 statement-only and 1 other row
  entries. Zero issues, placeholders, high-confidence vacuity findings or
  untrusted axioms; 28 non-gating heuristic leads. Receipt:
  `lean/.validate-logs/run-20261001T085025-654697Z/report.json`.
  The new lead is `retainedResourceCodes`: its ignored enum argument is honest
  because the declared retained-resource type has exactly one constructor,
  target recharge. Empty retention still rejects F/O as proved.
- Frozen G6 declarations/results, POS-04, all CST-TT-08 files, and committed
  clause/generic transport modules are unchanged. Only TTH-06 changes in 09.

## CR3: remaining generalization plan

The substance of the family construction is retained. Its domain is the blocker
to generic TTH-06 promotion, not the validity of its lane proofs.

1. Parameterize raw component interfaces over finite carrier and cell types,
   typed primitive values, actions, disturbances, events and routes. Define
   every decoder, transition, code, observation and update from those raw data;
   preserve complete-input rejection, locality and closure-wide laws.
2. Parameterize the typed stage, independently checked cover/gluing data,
   corridor composition and audited bridge frontier. Reuse G2/G4/G1c proofs
   through explicit adapters; no fixed POS-04 stage, cover or audit selectors
   may remain in the broader theorem's signature.
3. Lift F/O invariants, entry execution, TTH-05 transport and soundness to that
   interface; prove the POS-04 family is an instance. Preserve separate lane
   derivations, AF→P, named-readout controls and O independence. Promotion waits
   for this broader `RawHandoff` result and its non-vacuous instance.

The CR3 Lean additions are **(b), TTH-06**: new direct negative readout theorems,
F/O readout vectors, and readout independence. No existing definition or theorem
statement is weakened or changed. The status reversion corrects the evidence
scope; it does not change the row's exact statement. No (a) changes.

## CR3 verification

- `cd lean && lake build`: exit 0, 350 jobs, 66.33 seconds; Assembly rebuilt
  in 55 seconds. No new module warnings; existing linter warnings are replayed.
- All eight added readout declarations resolve and `#print axioms` shows only
  `propext`, `Quot.sound`, `Classical.choice` (read-only
  `/tmp/G6c_CR3_axioms.lean`).
- `python3 -B scripts/check_tth06_transcription.py`: passes unchanged against
  frozen G6b; all five planted drifts caught. No predicate definition changed.
- `python3 -B scripts/validate_lean.py --write-inventory`: regenerated 39 rows,
  210 evidence entries. TTH-06 is `conditional` with family evidence retained.
- `scripts/validate_lean.sh`: exit 0, overall pass; 210 entries / 209 unique,
  201 theorem-kind entries, 8 statement-only, 1 other. No issues, placeholders,
  gating vacuity findings or untrusted axioms; 28 non-gating heuristic leads.
  Receipt: `lean/.validate-logs/run-20261001T091828-290183Z/report.json`.
- Status totals: **7 proved, 14 checked finite countermodels, 10 conditional,
  8 open**. Only TTH-06's 09 status/evidence/ceiling/rationale change.
- `git diff --check` passes. G6/POS-04 declarations/results and all CST-TT-08
  files remain unchanged. The broader RawHandoff generalization remains open.
