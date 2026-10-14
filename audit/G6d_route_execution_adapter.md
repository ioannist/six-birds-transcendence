# G6d: actual source/receiver/target route boundary

TTH-06 stays **conditional**. This completes the POS-04 executed-route
component and its semantic adapter, not the whole named-lineage equivalence or
the final `RawHandoff` assembly. No registry, inventory, frozen declaration,
result, or existing theorem is changed. All new definitions and theorems are
**(b) mathematical additions for TTH-06**; there is no row narrowing.

## Proved

- `RunFrame` embeds arbitrary typed register instructions in a run frame.
  `dependencies` and `evaluation` prove exact preservation of static reads and
  instruction semantics. Missing reads still reject, including unselected
  branches of the eager interpreter.
- `POS04RouteExecution` uses **one** acquisition execution. Its frame is
  `Tag × Run6`. Source histories execute the assigned source rows; the raw
  coordinate receiver switches to target mode; every post-arrival branch then
  executes the assigned target row and target updater. `rows_eq`, `update_eq`,
  `initial_eq`, `receive_eq`, `fold_eq`, and `result_target_step` hold for
  arbitrary assignments once their consumed primitives are present. No equality
  between source and target transition tables is assumed.
- `ArrivalReadout` and `ResultReadout` describe execution independently:
  realized atomic path, receiver activation, supported raw source history,
  computed receiver result, normalized target response, actual positive support,
  and actual target update. `arrival_readout_iff` and `result_readout_iff` prove
  their correspondence with the generic acquisition/route relations.
- The receiver copies raw coordinates, never a predictive-class label.
  Reception starts the declared **probe-local** phase-2 counter and tick at
  zero; the funded response advances them to one. This is the G6 phase-2
  convention, not a reset of the corridor event order. The raw path register
  retains the acquisition history. It is not post-withdrawal support.
- `POS04RouteReadout.RouteReadout` retains distinct **raw history-word/path
  tuples**, different provenance and future probes, a **shared computed
  arrival endpoint**, nonempty executed results, and register/probe/owner
  equations on **every** resulting support branch. It is stronger than
  `ExecutedMemory`; the latter is not substituted for the comparison.
- `route_readout_partial_iff` is the exact adapter for arbitrary partial
  assignments:

  ```lean
  RoutePass a ↔ Complete dependencies a ∧ RouteReadout a
  ```

  `ready_route_iff` proves that the listed dependencies are exactly the route
  interpreter's readiness requirements. They are the 13 cells for source/target
  rows, ticks and resources; the ledger, policy, histories, route table,
  receiver, events and realization. There is no interface, hazard, predictive
  coordinate or writer-table requirement in this route component. Other
  components retain their own obligations for those fields.
- `semantic_status_partial_binding` proves `.routeIndexed` iff that complete
  semantic comparison holds. Thus the status binding preserves
  `Indexed`/`Retained`, including the shared endpoint and universal support
  quantifier.
- `positive`, `canonical_retained`, and `every_result_retains_provenance` supply
  a genuine positive witness and every-branch retention. `reversed_pass` and
  `reversed_retained` prove the existing reversal regression with probes **1/0**.
  Definedness and distinction gate the result; baseline **0/1** is a theorem,
  never a requirement on arbitrary assignments.

The copying receiver and first-phase route probe remain deliberately designed,
near-automatic POS-04 operations. This does not upgrade C4–C7's grades or supply
physical transfer evidence.

## Guards and direct negative readouts

`erasedTargetRows` changes only the target rows to empty lists, by the stated
row-erasure rule. `erased_target_source_history_still_supported` proves that
source acquisition still executes, while `erased_target_rejected` and
`erased_target_no_readout` directly reject the target response/comparison.
This tests the real mode switch rather than rejecting an already-broken source.

Source absence directly refutes semantic arrival and route memory
(`source_absent_no_arrival`, `source_absent_no_readout`). A constant register
directly refutes `ExecutedMemory` (`constant_register_no_named_memory`), as
well as the stronger comparison. A constant probe fails distinction. Missing
dependencies reject before helpers can use defaults: `missing_dependency_rejected`
quantifies over **every** consumed cell. Missing source rows, target rows,
atomic events and owner have explicit component guards too.

## Argument classification

| Argument | Classification | Constraint |
|---|---|---|
| Assignment `a` | Raw immutable typed cells | Exact 13-cell readiness; decoder/eager Option propagation |
| Source/target mode and run registers | Defined representation of actual execution | Raw source initializer; receiver switches to target; update retains mode |
| Receiver, row, update and provenance expressions | Raw instructions owned by `routeRaw` | No supplied endpoint class, future, entry set, observation or verdict |
| Routes, histories, events, realization, ledger and resources | Raw assigned primitives | The same cells feed history, receiver and target response |
| `hc`, readiness, support, normalization | Evidence on raw data | Presence and actual raw-row equations, not lane conclusions |
| Endpoint, arrival run, supported word, result, residue, probe, status | Defined objects | Executed folds, receiver instructions, actual updater and raw readouts |
| Positive endpoints/probes | Computed theorem conclusions | `canonical_source_terminal`, `canonical_retained`; not generic gate constants |

The generic `RunFrame` decoder is a raw register representation map, not an
independently supplied future observer. Its evaluation theorem applies to any
instruction and any frame. The final `RawHandoff` must still own the assembled
component instructions and prove their shared-execution bindings.

## Field/readout coverage

| Field | Equation or semantic check | Guard |
|---|---|---|
| Source rows | `rows_eq` in source mode; `supported_word_iff` | `missing_source_rows_rejected`; the target-erasure regression preserves source support |
| Target rows | `rows_eq` in target mode; `result_target_step` | `missing_target_rows_rejected`, `empty_target_support_rejected`, `erased_target_no_readout` |
| Source/target ticks | `update_eq` with the assigned tag's `actualUpdate6` | `missing_dependency_rejected` for either tick cell; existing temporal tick-law guards remain separate |
| Ledger/funding and resources | Enabled rows and exact updater; normalized actual target support | `missing_dependency_rejected`; `empty_target_support_rejected`; resource ownership guard below |
| Policy | `words_read`, `response_eq` from the assigned policy | `missing_dependency_rejected` at `.policy` |
| Histories and route table | `words_read`, `routes_read`, `expected_eq`, `path_identity_eq` | `missing_dependency_rejected`; generic `RouteComponent.constant_paths_rejected` |
| Events and realization | `ArrivalReadout` path/activation; `arrival_readout_iff` | `missing_atomic_rejected`; generic acquisition un-realized/non-strict path guards |
| Receiver/source availability | `receive_eq`, `receiver_read`, semantic activation | `source_absent_rejected`, `source_absent_no_arrival`, `source_absent_no_readout` |
| Carrier mode | Source initialization, target reception, mode-preserving `update_eq` | Target-row erasure separates supported acquisition from absent target response |
| Post-step register | `fold_preserves_register`; `every_result_retains_provenance` on all branches | `constant_register_readout_rejected`, `constant_register_no_named_memory` |
| Future probe | Declared first-phase rule evaluated on the resulting register | `constant_probe_rejected`; reversal proves no fixed 0/1 gate |
| Target owner | `owner_eq` and every-branch ownership | `missing_owner_rejected`, `wrong_owner_rejected` |
| Shared arrival endpoint | `RetainedReadout` quantifies over actual arrivals | Generic `RouteComponent.endpoint_mismatch_rejected` |
| All positive-support outcomes | `ResultReadout`, `result_readout_iff` | Target-row erasure; transcription branch/probe drifts |

This seam does not claim new post-withdrawal closure laws. Those are the
committed actual-support temporal/game laws, which still need their final
shared-interface binding. Route retention here covers every phase-2 branch;
unbounded subsequent run preservation is not inferred from that finite check.

## Transcription and checks

`scripts/check_tth06_transcription.py` additionally exports the new computed
source support, receiver factors, response actions, raw tuples, **every actual
target branch/update**, and each resulting probe. They agree exactly with
G6b for all four registered controls. It does not export a stored route-pass
label. Eight planted drifts are caught, including the new receiver endpoint,
actual target branch and retained probe controls.

- `cd lean && lake build`: exit 0, 461 jobs. New modules have no warnings;
  existing vendored/`TemporalFactorRules` warnings are replayed.
- All **77** new public theorems resolve through `/tmp/g6d_route_axioms.lean`;
  their axioms are only `propext`, `Quot.sound`, and `Classical.choice`.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0; eight drifts caught.
- `scripts/validate_lean.sh`: exit 0; all 39 rows / 210 declarations pass
  resolution and axiom checks. Placeholder and high-confidence vacuity counts
  are zero. There are 36 heuristic ignored-input leads (31 previously).
  The five new leads are the singleton-register `Values`/`pack` functions and
  the three singleton-coordinate programs; ignoring their sole `Unit` index
  does not ignore their assigned data or run state.
- Forbidden-construct scan and `git diff --check`: clean. CST-TT-08, the 09
  registry/inventory, and the frozen G6 files remain byte-identical to HEAD.

## Still required for promotion

1. **Complete named semantic lineage**, not just its route component:
   independently defined corridor, all frozen signature fields, bridge laws,
   snapshots and full-future execution links; prove its separate exact adapter
   for arbitrary partial POS-04 assignments. No gate/readout converse is assumed
   and no unused interface bookkeeping is added to the readout.
2. Bind all those interpretations and the package/resource/game components in
   the fully polymorphic `RawHandoff`, preserving the full route comparison.
3. F/O soundness, named O separation and F dependence, POS-04/control transfers,
   final transcription/tables, and the registry promotion gate.

There is no mathematical infeasibility finding in this seam. The boundary is
proved, but these remaining obligations have **not** been discharged.
