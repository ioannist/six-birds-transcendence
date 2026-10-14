# G6d: polymorphic package / acquisition / resource binding

**Proved boundary; TTH-06 remains conditional.** This seam binds the generic
closed eight-schema dispatcher and constructed typed staged global to the
polymorphic acquisition/resource game components. It is not the final
`RawHandoff`, complete generic lineage, or three-lane soundness theorem.

## What is proved

`PackageRuntime.Raw` is polymorphic in source/target cells and their dependent
values, run registers, factors, resources, actions, disturbances, outcomes,
predictive values, residues, stages, events, histories and routes. It contains
raw syntax/data, not package/autonomy predicates or independently supplied
entries, rows, dynamics or observations.

The source assignment is the only supplied assignment. `target` is the
`DispatchedPackage.global` constructed by typed staging and dependent gluing.
Acquisition, resources and run-indexed clauses all read that same target.
Acquisition and resource transitions use the same `runtime.execution`.
`runAssignment` interprets the typed primitive instructions at the actual run;
`PackageAt` requires the coherent arrival package, the actual factor to be
inside, and all eight raw clause rules re-evaluated on those run cells.

- `package_soundness` constructs the integrated target realization by the
  existing TTH-02 dependent gluing/locality engine.
- `full_soundness` and `operational_soundness` derive their respective semantic
  games by induction on the plays of the constructed causal strategy. Each
  consumes its own raw component certificate.
- `full_pass_iff_readout` / `operational_pass_iff_readout` are exact
  **proof-bearing invariant/game** equivalences. Reverse construction uses
  the reachable-play invariant. They are not a decision-completeness claim
  about a finite algorithm.
- `full_autonomy_implies_package` obtains P at a genuine activated entry;
  it is not used in `package_soundness`.
- `full_autonomy_implies_operational` keeps the same causal strategy, removing
  only the additional package constraints.
- `full_answers_every_word` constructs a response execution for every finite
  disturbance word, with the package re-evaluated on its actual terminal run.
  No finite horizon is enumerated. Safety still quantifies over every
  positive-support successor of selected responses, not unselected actions.
- Both games require a nonempty, covering declared disturbance interface.
  Source absence, invalid withdrawal, missing entry views, missing dependencies,
  entry resource failure and missing responses reject the semantic readouts.

## Exact POS-04 package specialization

`POS04DispatchedStage.raw` uses the committed typed stage and declared cover,
reindexed from clause names to the dispatcher's eight kinds. No new model or
cover is introduced. It uses `POS04Dispatcher.package .target`.

For **every partial assignment**:

- `global_eq_image` identifies the constructed global with the actual staged
  `image`; no validity premise is required for the equation.
- `valid_iff` identifies the complete typed stage/cover/dispatcher check with
  `ComputedFIACH.PackageLane`.
- `realization_iff` and `realization_iff_named` identify the independently
  defined generic P readout with the family package lane and its named
  `IntegratedTargetRealization` respectively. The reverse direction recovers
  source completeness from actual map totality.
- `deleted`, `controls`, and `deletion_no_realization` transfer primitive
  deletion and the committed package controls. The last is a **direct semantic
  negative**, not failure of a sufficient gate used to negate its conclusion.
- `positive` proves a genuine canonical staged-package instance.

`bind` is deliberately an **internal package adapter with raw runtime
parameters**. It is not the promised concrete POS-04 `RawHandoff` value. No
canonical F/O game instance of this new multi-resource interpreter is claimed.

## Argument classification

| Argument | Classification | Construction / constraint |
|---|---|---|
| Dependent cell/value types and component domains | Raw interface types | Arbitrary; no POS-04 family fixed in `PackageRuntime` |
| Source assignment | Raw data | All component reads use its defined staged global |
| Typed language, stage, reference map, source scopes, cover, closed clause schemas | Raw data | `DispatchedPackage.Valid`: totality, raw value equations, scope coverage, edge compatibility and local raw checks |
| Runtime schema: carriers, finite domain lists, entry/exit stages, clock | Raw data | Acquisition/domain/resource checks; carrier distinction remains an enclosing handoff obligation |
| Shared rows and register-update programs | Raw instructions | Acquisition/resource interpreters use the same `execution`; readiness before decoding |
| Resource, acquisition and predictive/readout instructions | Raw instructions | Exact dependency readiness and actual interpreted legal/step/package checks |
| `runCells` primitive instructions | Raw instructions | Evaluated on the actual run, never an assignment or verdict argument; full cross-component dynamics coherence remains a final binding obligation |
| Acquisition/resource readiness | Evidence on raw inputs | Complete exact consumed scopes, checked before total helpers |
| Auxiliary invariant and response evidence | Evidence on defined raw semantics | Hybrid architecture; induction derives games; no stored game proof |
| Global, locals, run assignment, entries, rows, updater and games | Defined objects | Not supplied parameters |
| Audit counterexamples used by guards | Evidence on raw semantics | Actual missing cell, failed resource, legal-response or withdrawal check |

## Coverage and guards

Names below are under `PackageRuntime` unless a namespace is shown. The table
covers this **P/A component boundary**, not the pending complete lineage gate.

| Field / obligation | Gate or law | Guard / exact adapter |
|---|---|---|
| Coordinate/value maps, clause scopes, cover and adjacency | Complete `DispatchedPackage.Valid`; dependent gluing/locality | Existing G6d substrate/stage/cover guards; `valid_iff`, `scope_check`, `source_coverage`, `edges` |
| Source primitive totality / target package | Defined mapped locals and glued global; closed dispatcher | `POS04DispatchedStage.deleted`, `deletion_no_realization`, `controls` |
| All eight run-indexed clause schemas | `PackageAt`: closed rules on actual interpreted primitives | `missing_run_primitive_no_full`, `failed_target_clause_no_full` |
| Histories, routes, events, realization, receiver | Acquisition's own complete dependency check and actual phase-2 execution | `missing_acquisition_no_games`, `missing_entry_view_no_games` |
| Initializer / receiver programs | Exact program dependency readiness | `missing_initializer_no_games`, `missing_receiver_program_no_games` |
| Actual rows / every update register | Shared execution; raw row and program readiness | `missing_row_no_games`, `missing_update_no_games`, `acquisition_resource_update` |
| All resource instruction inputs | Resource readiness, independent of acquisition | `missing_resource_no_games` |
| Nonempty disturbances / six-role withdrawal | Defined `Withdrawal`; role removal, retained/removed support checks | `full_disturbances_nonempty`, `operational_disturbances_nonempty`, `invalid_withdrawal_no_games` |
| Genuine activated entries / source presence | Defined `Entries`; game requires nonempty entries | `source_absent_no_full`, `source_absent_no_operational`, `missing_entry_view_no_games` |
| Target-owned responses, positive funded accounts, writer availability | Interpreted `ResourceClosed` / `Legal` throughout generated plays | `entry_resource_failure_no_full/operational`, `missing_response_no_games`; existing `ResourceRuntime` owner/depletion/writer guards |
| Order, tick, progress, record, account updates, residue retention | `ResourceRuntime.StepLaw` on the actual updater for every positive-support selected response | Existing `nonadvancing_field_rejected`, `changed_residue_rejected`, `game_growth`; `full_answers_every_word` retains actual runs |
| Predictive/code/full-future/route/bridge readout coherence | **Pending enclosing lineage and temporal binding** | Existing engines exist, but this seam does not substitute them for their shared-model binding |

The missing-input guards reject **existence of** ready games or entries. They
do not assume readiness and a missing input together. The same applies to
entry-resource negatives: acquisition availability is distinct from failed
resource closure, so their premises are not contradictory by construction.

## Statement changes and remaining gate

All new definitions/theorems are **(b) mathematical additions for TTH-06**:
polymorphic P/A interpretation and soundness, game implications, unbounded word
responses, exact stage/dispatcher adapters and direct semantic guards. No
existing Lean declaration is renamed or restated; there are no (a) changes.
No registry text, ceiling, evidence or status is changed.

**Still required before promotion:**

1. Complete source/receiver/target lineage binding on the same primitive and
   runtime interface, including actual execution transport and **Indexed plus
   Retained** route status. Existing family lineage is not a substitute.
2. Checked coherence between clause primitive interpretations and the actual
   temporal/factor/resource execution. `runCells` is raw instruction syntax;
   this seam does not yet prove all those interpretation equations.
3. A raw finite-factor interpreter, with explicit proved per-instance lift
   laws, for the frozen TTH-05 certificate. Its interpretation-parametric
   `FactorData` engine must not be exposed as free semantic callbacks at the
   final `RawHandoff` boundary.
4. The concrete multi-resource POS-04 runtime and arbitrary-partial F/O
   equivalences, final generic `RawHandoff` F/O soundness, named O separation,
   all controls, and the final transcription/promotion gate.

No finite-context closure premise has been added. No finding has been fixed by
narrowing. TTH-06 stays **conditional**, with its committed family evidence and
legacy-lineage limitation intact.

## Verification

- `cd lean && lake build`: exit 0, 471 jobs, 3.24s for the final cached build.
  The new modules rebuilt in 3.1s (`PackageRuntime`) and 4.8s
  (`POS04DispatchedStage`). No new warnings; existing vendor and
  `TemporalFactorRules` warnings remain.
- All **44 new public theorem names** resolve; their `#print axioms` outputs
  contain only the permitted standard axioms `propext`, `Quot.sound` and `Classical.choice` (no others).
- `python3 -B scripts/check_tth06_transcription.py`: passes. Route execution
  now reads the constructed dispatcher global. The four frozen legacy G6b
  controls, actual entries and every retained branch remain unchanged. The
  twelve-outcome complete-execution regression agrees; all nine planted drifts
  are caught. These regression booleans remain explicitly limited to the
  weaker legacy lineage; complete family lineage is separately kernel-proved.
- `python3 -B scripts/validate_lean.py --write-inventory`: 39 rows / 210
  registered declaration entries; regenerated inventory is byte-identical.
- `scripts/validate_lean.sh`: exit 0; inventory agrees, no untrusted axioms,
  no placeholders or high-confidence vacuity findings, 36 unchanged heuristic
  leads. Report: `lean/.validate-logs/run-20261009T001433-662907Z/report.json`.
- `git diff --check` and the comment-aware forbidden-construct scan pass.
  Frozen CST-TT-08, model declarations/results, the 09 surface, and unrelated
  `paper/` are unchanged. The five changed/new files are left uncommitted.
