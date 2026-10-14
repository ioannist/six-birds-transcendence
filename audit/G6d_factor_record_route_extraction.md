# G6d factor, record, and executed-route extraction seam

TTH-06 remains **conditional**. This is a proved component boundary, not the
final `RawHandoff` binding or promotion. No existing theorem, registry row,
inventory entry, frozen model, or prediction is changed. All new mathematical
definitions/theorems are **(b)** additions for TTH-06.

## Proved

- `FactorTransport`: arbitrary source/target factor, action and outcome types.
  Classes are computed from positions and raw action/hazard observations;
  policy/action weights are computed from actual destination tables. Typed raw
  map equations derive policy-step, exact probability, and all finite action-word
  M-probe transport. The row denominator has its own checked equality. A raw
  row bisimulation derives representative sufficiency. This finite probe does
  not replace the already-proved eight-component run future.
- `POS04FactorTransport`: a minimal, eager seven-family decoder, locality inherited
  from `StaticView`, missing-input rejection, exact primitive/readout equations,
  `factor_equations_iff` and `pass_iff`, **for arbitrary partial assignments**.
  `pass_iff` equates the component gate with completeness and the existing
  assignment-owned bridge's finite factor fields/action-map equations; it does
  not claim equivalence to the entire lineage lane. `linked_M` links computed
  classes to imported `mClass` whenever the independently checked C2 gate holds;
  `canonical_M_link` and `canonical_equations` supply non-vacuous instances.
- `RecordComponent`: edges are computed from event contiguity, raw source/target
  support, realization, strict clock increments and writers. Ranks are actual
  event-clock values; the numerical increment is their difference. The optional
  `Check` additionally requires a nonempty source arrow, and is therefore a
  stronger audit than the conditional record-transport law alone. `sound` and
  `nonempty_arrow` prove its consequences. This audit is **not identified with**
  the old bridge gate or imposed here on every generic handoff.
- `POS04RecordComponent`: an eager three-cell decoder; `transport_equation`
  identifies the complete computed record object with the existing bridge's
  object for every partial assignment. `pass_iff` is a biconditional;
  `arrow_equivalences` transfers both named arrow predicates. The positive
  nonempty arrow is proved. These are finite acquisition record equations;
  post-exit closure-wide record advancement remains the separate run-law gate.
- `RouteComponent`: route-attributed `Result` is an actual activated arrival,
  followed by a normalized positive-support response and the shared updater.
  `result_entry_iff` proves that existentially forgetting the route yields
  exactly `AcquisitionExecution.Entry`. `Retained` checks **every** resulting
  support branch, reading the register, future probe and owner from that result.
  The comparison checks raw history-word/path distinction, a shared computed
  arrival endpoint, nonempty results, and different retained provenance/readouts.
  `statusOf` is computed from this check and can never yield `.flat`.
  `route_memory_sound` derives the named `ExecutedMemory` readout; constant
  registers directly refute that readout. The POS-04 route specialization and
  arbitrary-partial equivalence are **not yet proved**.
- `POS04LineageBoundary.missing_atomic_readout_rejected`: deleting the actual
  shared event table directly refutes the existing named
  `ComputedFIACH.StrictTemporalLineage`, without inferring conclusion failure
  merely from a failed sufficient check.

## Argument classification

| Argument | Classification | Binding/check |
|---|---|---|
| Factor source/target schemas | Raw finite domain and rule data | Reused approved temporal/profile schemas; denominator equation checked here; domain/row validity belong to the enclosing dispatcher |
| Factor `Data` | Decoded raw primitives | Rows, positions, hazards, policy, ticks, resource and ledger; no interface/history/writer over-read |
| Typed factor `Maps` | Raw typed maps/instructions | Coordinate, predictive, policy/action, state-domain, tick, resource and ownership equations |
| Assignment / binding | Raw cells and typed read instructions | Eager Option evaluation, locality and missing-input rejection |
| Classes, weights, policy steps, probes | Defined objects | `classOf`, `actionWeight`, `canonicalWeight`, `actionProbability`, `word` |
| Factor equations / row bisimulation | Evidence on raw data | Checked pointwise equations, not flags or supplied future answers |
| Record schema and decoded `Data` | Raw event domain, events, realization, writers, clock | Support/contiguity/clock checks; shared-cell POS-04 projection |
| Record edges, rank, increment, transport | Defined objects | `edges`, `rank`, `transport`; never arguments to the raw decoder |
| Route acquisition | Raw initializer, histories, events, realization, receiver, rows, updater, response instructions | Existing `AcquisitionExecution.Ready`, `Arrival`, normalization and actual positive support |
| Provenance encoder / register, readout, owner, endpoint instructions | Raw typed instructions | Declared in `RouteComponent.Raw`; evaluated on the same assignment/execution; completeness and pointwise retention/equality gates |
| Expected provenance, path identity, results, route status | Defined objects | Option binds and actual execution; no route-name verdict or endpoint label |
| Ready / equation / comparison proofs | Evidence on raw data | Not stored lane readouts |

The final `RawHandoff` must own these schema/instruction bindings. This seam
introduces no final theorem taking a free interpretation parameter in place of
that ownership.

## Field coverage and guards

Names below are under `GenericHandoff` and the stated module namespace.

| Raw field/readout | Law/check | Guard |
|---|---|---|
| Every consumed factor cell | Eager seven-family decoder; `Pass` read equations | `FactorTransport.missing_rejected`; `POS04FactorTransport.missing_rejected` |
| Factor state map/domain order | `Equations.states` | `states_mismatch_rejected`; `collapsed_state_map_guard` |
| Positions / coordinate map | `Equations.coordinate` | `coordinate_mismatch_rejected`; `coordinate_erasure_guard` |
| Rows / action map / probabilities | `Equations.action`, `scale`; actual destination fold | `action_mismatch_rejected`, `scale_mismatch_rejected`; `erased_target_rows_rejected`, `collapsed_action_map_guard` |
| Hazards / computed predictive map | `Equations.predictive`, `classInjective` | `predictive_mismatch_rejected`, `class_collapse_rejected`; `hazard_erasure_guard`, `collapsed_predictive_map_rejected` |
| Policy | `Equations.policy` | `policy_mismatch_rejected`; `policy_erasure_guard` |
| Tick | `Equations.tick` | `tick_mismatch_rejected`; `tick_erasure_guard` |
| Resources / ledger / maintenance | Computed available, solvent, correctly owned factor resource; `Equations.maintenance` | `maintenance_mismatch_rejected`; `resource_erasure_guard`, `ledger_erasure_guard` |
| Owner translation | `Equations.owner` | `owner_mismatch_rejected`; `owner_relabel_guard` |
| Every consumed record cell | Eager event/realization/writer view | `RecordComponent.missing_rejected`, POS-04 specialization |
| Record event references / realization | Required events exist and satisfy `strict` | `unrealized_rejected`; `event_erasure_guard`, `realization_erasure_guard` |
| Record source/target support | Computed edges; nonempty source audit and target-edge inclusion | `source_support_erasure_guard`, `target_support_erasure_guard`; `nonempty_arrow` derives actual strictness |
| Writer | Both raw writer tables checked | `writer_rejected`; `no_writer_guard` |
| Event clock | Positive raw increment/contiguity; computed record ranks | `zero_clock_rejected`; `zero_clock_guard` |
| Every consumed route/display cell | Acquisition readiness and readout/provenance scope completeness | `missing_acquisition_rejected`, `missing_readout_rejected`, `encoded_provenance_missing` |
| Route activation / source presence | Actual `Arrival` in every `Result` | `source_absent_rejected`, `no_result_rejected` |
| Actual phase-2 support / updater | `Result`, exact `result_entry_iff`, `result_actual_update` | `no_result_rejected`; existing acquisition missing-row/updater/initializer guards |
| Comparison domain / raw paths | Declared route membership and raw word/path distinction | `empty_comparison_rejected`, `constant_paths_rejected` |
| Post-step provenance/register | Expected raw provenance and every actual result register | `constant_register_rejected`; direct `constant_register_no_memory` |
| Post-step future probe | Defined and unequal on compared routes | `undefined_probe_rejected`, `constant_probe_rejected` |
| Post-step owner | Equals declared target on every result | `owner_mismatch_rejected` |
| Shared endpoint | Every actual arrival endpoint reads as the same decoded value | `endpoint_mismatch_rejected`; dedicated POS-04 endpoint sensitivity instance remains to be supplied with the adapter |
| Named strict lineage, missing atomic witness | Constructed corridor must use actual checked event table | `POS04LineageBoundary.missing_atomic_readout_rejected` |

There is no new closure-wide evolving-readout claim in this seam. Full run
updates, the eight-field observer, closure and future links continue to use the
committed execution/readout-law machinery; their joint binding remains below.

## Gate versus named readout: a concrete regression

`emptyInterface` changes only the assigned interface declaration to `[]`.
`unchanged_bridge` is definitional equality. `empty_interface_readout` proves
that the existing named strict-lineage readout still holds, while
`empty_interface_gate_rejected` proves that the C6-dependent lane gate fails.
Consequently `readout_does_not_imply_gate` refutes conflating them. This is
consistent with the accepted design's **two separate** adapter equivalences.
It is not a reason to narrow either legacy predicate. The new factor decoder
explicitly proves that this unused interface cell is not consumed.

## Remaining promotion work

1. Specialize the executed route comparison to POS-04, including exact
   arbitrary-partial phase-2/result/readout equations and the endpoint guard.
2. Bind the factor/record/route components with the committed G4 execution
   corridor and full eight-component G1c execution/snapshot/run laws. Prove
   both the complete lane-gate equivalence and the **separate** named
   `StrictTemporalLineage` equivalence for arbitrary partial assignments.
3. Finish the target/receiver runtime specialization and the enclosing
   `RawHandoff`, owning every interpretation parameter. In particular source
   history execution and the post-receiver target row must use their actual
   respective assigned tables, even when those tables differ. No canonical
   table equality or representative selection may stand in for that binding.
4. Final generic F/O soundness, named O separation, F dependence, POS-04
   controls, extended transcription, tables and the FAITHFUL registry gate.

The already-committed TTH-05 game transport is reused. No new finite-context
premise, restriction of the recipe language, status promotion, or narrowing is
introduced here.

## Checks for this seam

- `cd lean && lake build`: exit 0, 458 build jobs; no new warnings. The
  existing vendor and temporal-factor linter warnings are unchanged.
- `/tmp/g6d_extraction_axioms.lean`, through `lake env lean`: all 92 new public
  theorem names resolve; axiom union exactly `propext`, `Quot.sound`,
  `Classical.choice` (no untrusted axiom).
- `scripts/validate_lean.sh`: exit 0. Its new non-gating ignored-input lead
  is `POS04FactorTransport.maps`: the raw ownership translation sends every
  source ownership label to the declared target tag. This is a raw map, not a
  constant acceptance predicate; `owner_relabel_guard` checks its use.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0; all existing G6b
  comparisons and all five planted drift probes pass. This checker is not yet
  extended for the unfinished final generic binding.
- Forbidden-construct scan of the new modules: no matches; `git diff --check`
  clean. CST-TT-08/09 surfaces, inventory, frozen declarations, scripts and
  `paper/` received no edits.

All changes are uncommitted.
