# G6d-4b: constructed G4 corridor and executed seed binding

## Proved boundary

This continues the accepted execution-frontier seam. **TTH-06 stays
conditional.** No registry, inventory, declaration, or frozen science file changes.

- `AcquisitionCorridor` interprets the assigned routes, events, realization,
  receiver and seed instructions eagerly. Missing inputs reject before any
  totalized helper can be used. Initializer, row, successor and receiver
  dependencies also remain required by `AcquisitionExecution.Ready`.
- A leg's stages are the **actual route's** entry and event destinations. Its
  owned event vertices come from that route's actual source/target support
  bits; its edges connect successive stages. This avoids assuming that every
  stage/event in the whole interface belongs to every route.
- The last actual mixed atomic event supplies the intervention audit. Source
  and target deletion use G4's mixed-support rule. No audit verdict is stored.
- Frontiers use the declared acquisition clock, interpreted predictive seed,
  raw history residue and actual event prefixes. Update recipes use the raw
  event's independently checked positive increment, append its event name,
  and derive the next owner. `AtomicLegPass` checks all G4 laws, realization,
  route execution and nonredundancy on these constructed objects.
- `constructs` yields `StrictCorridorWitness`. `chain` interprets a nonempty
  list of raw component/route requests on **one assignment**; `constructs_chain`
  applies the already-proved G4 inductive chain theorem to the constructed list.
  Exact adjacent-frontier checks are recomputed, including all eight fields,
  support and ownership. `adjacent_rejected` rejects a mismatched join.
- `RuntimeComponents.corridor` uses the **same acquisition and execution** as
  its resource/frontier projections. The sharing equations are definitional.
- `ExecutedAcquisitionCorridor` additionally binds predictive and history
  seeds, and the completed route residue, to the **actual supported terminal
  executions**. Audit terminal coverage gives an executed seed for every
  declared history. The predictive coordinate is an assigned static instruction;
  its injectivity is checked on actual audited values, not postulated on
  unrepresented values of the ambient readout type.
- Its soundness derives the constructed corridor and full-interface all-word
  future sufficiency separately, reusing the committed closure-law gate.

### Clock convention

The G4 acquisition clock is the declared event-path clock, as in
`G6_lane_spec.md:104–145` and the previous `ComputedFIACH.AtomicAcquisition`.
Its tick/progress/record coordinates count funded acquisition events. The
source-history occurrence clock and post-exit tick phase are separate. No
theorem equates these clocks or claims that the event projection replaces the
run-level C6 readouts. Those run readouts retain the committed whole-closure
laws. Binding the clocks at the typed receiver endpoint remains part of G1c.

## POS-04 instance and exactness

`POS04AcquisitionCorridor` reads the existing event/receiver/route views and
the same assigned source rows, positions and hazards. Its predictive seed is
the first-occurrence rank of the **computed** predictive values. The raw
equation and canonical imported-M link are proved.

- `read_eq` and `pass_iff` are exact for arbitrary partial assignments with
  consumed cells present. They characterize the new generic G4 gate on those
  assigned values, **not** the entire legacy G6c lineage predicate.
- `canonical_leg` identifies the constructed baseline leg with the existing
  `pos04AtomicLeg`; `positive`, `positive_corridor` and `positive_chain` supply
  the single-leg instance. POS-04 is not represented as two carrier changes.
- Missing events, deleted mixed source support, and a removed realized stage
  directly refute the existential **constructed-corridor readout**. These
  proofs do not infer a failed conclusion from a failed sufficient check.
- Swapping the histories still passes. No `0/1` route-output baseline is a gate.
- `POS04ExecutedCorridor.fold_equation` and `snapshot_equation` are exact for
  arbitrary partial assignments under dependency presence. They retain actual
  Ambient successors, including every possible branch in the raw row semantics;
  no predictive representative replaces a destination.
- `POS04ExecutedCorridor.positive` proves the executed seed/route binding on
  all four existing snapshots, including both `afterFirst` selectors. Its
  terminal equations check the complete raw `(history,path)` register.
- A false constant predictive seed is rejected against the actual executed
  endpoint while the row, updater and observation remain fixed.

## Argument classification

| Argument | Classification | Constraint/construction |
|---|---|---|
| Cell/value/register/action/outcome/stage/event/history/route types | Raw typed interface | No POS-04 types in generic definitions |
| Immutable partial assignment | Raw data | Eager views and acquisition readiness reject absent dependencies |
| Acquisition schema, event names, carrier identifiers | Raw interface data | Reference/path checks, distinct carriers, unique stage/name checks and G4 atomic checks |
| Initializer, history, row, update and receiver instructions | Raw instruction data | Shared execution; no candidate terminal or future argument |
| Predictive/history seed and coordinate instructions | Raw coordinate instructions | Actual executed terminal equations; image injectivity; missing-input guards |
| Frontier raw object | Bridge-owned raw instructions/interface | Committed execution, bisimulation, closure and readout-law gates |
| Readiness, path, atomic, seed and join proofs | Evidence on raw checks | No free lane verdict field |
| Decoded view, legs, events, edges, updates, chain, snapshots, futures | Defined objects | Option interpretation, folds, projections and exact image codecs |
| Lists in `compose`, ready runs/views in guard lemmas | Internal theorem arguments | Computed objects/evidence identified by interpretation equations |

## Field coverage and guards

| Field/family | Law/check | Guard/evidence |
|---|---|---|
| History words, initializer, rows, updater, receiver instructions | Acquisition readiness and actual prefix execution | `missing_acquisition_dependency`; committed initializer/program/row guards |
| Event table | Eager interpretation, supported owned vertices, path and atomic checks | `missing_atomic`; `missing_atomic_no_corridor` |
| Source/target support | Actual vertex expansion and deletion intervention | `detached_rejected`; `detached_no_corridor` |
| Realization | Specific path stages and constructed stages must be realized | `unrealized_path`; `gap_no_corridor` |
| Receiver availability/funding | Its own activation and funded stage gate | `inactive_receiver` for every ActivationField; `no_funding_rejected` |
| Source and target IDs | Distinctness and exact boundary ownership | `geometry_field_guard .source/.target` |
| Stage clock | Raw positive event equation and G4 strict readout updates | `geometry_field_guard .clock` |
| Event names and entry name | Nonempty names, injection, unique actual vertex IDs | `geometry_field_guard .eventName/.entryName` |
| Route tuple and audit selection | Actual path endpoints/support; last actual mixed audit | `broken_leg`; atomic/path checks; missing acquisition dependency guard |
| Predictive seed | Assigned raw M computation and executed endpoint equation | `false_seed_rejected`; `seed_mismatch_guard` |
| History/residue seed | Assigned history and executed register equation | `no_history_residue_rejected`; `seed_mismatch_guard` |
| Predictive coordinate instruction | Eager read and audited-image injection | `missing_coordinate_guard`, `missing_coordinate_rejected` |
| Order/tick/progress/record acquisition coordinates | Checked raw increments across every constructed edge | G4 `readout_step_strict` via `StrictCorridorWitness.strictSteps` |
| Acquisition route residue | Actual event appends; whole exit-register equation | `SeedCoherence`; G4 `routeStatusOf` execution check |
| Acquisition maintenance and owner | Receiver-funded label and raw carrier/support equations | Funding/ID guards; G4 edge laws and support membership |
| All evolving **run** readouts | Committed independent recipes on the whole defined closure | Existing nine-field `ExecutionFrontier` guards, including the capped-progress example |
| Adjacent frontier | Exact G4 stage/frontier/residue/owner equality | `adjacent_rejected` |

Legal constant predictive/owner values are not rejected solely for being
constant. The guard must break a required raw equation. The remaining G1c
primitive binding must constrain their meanings; this seam does not claim that
its geometric gate alone establishes heterogeneous temporal transport.

## Statement changes

All new definitions/theorems are **(b), TTH-06**: polymorphic acquisition-to-G4
construction, actual executed-coordinate links and POS-04 instances/guards.
No old statement is changed or weakened, no declaration is renamed, and no
row text/ceiling/status is changed. No additional finite-context premise is
introduced. This is a sound constructor, not a completeness assertion for
arbitrary raw instruction grammars.

## Remaining work, in packet order

1. Full G1c construction from these shared cells, including primitive factor
   and class bindings, record/route/owner laws and typed endpoint alignment.
   Prove the **full** arbitrary-partial G6c `StrictTemporalLineage`
   biconditional and its direct missing-atomic-witness negative. The direct
   negative here concerns the constructed G4 corridor component only.
2. Target/receiver specialization and two-sided frozen-signature transport.
3. TTH-05 transport from the generic game readout for every entry.
4. Final RawHandoff F/O soundness, named separation/dependence, controls,
   transcription and registry promotion gate.

The new G4 gate intentionally is not advertised as already equivalent to
`ComputedFIACH.AcquisitionCorridorPass`: that family gate additionally reads
phase-2 outputs and both carriers' clause/resource checks. Their runtime
extraction belongs to the enclosing bridge/acquisition adapter. Conjoining
fixed positive proofs would not discharge that obligation.

## Files and verification

New Lean modules under `lean/CSTTT/Targets/GenericHandoff/`:
`AcquisitionCorridor.lean`, `RuntimeAcquisitionCorridor.lean`,
`POS04AcquisitionCorridor.lean`, `ExecutedAcquisitionCorridor.lean`, and
`POS04ExecutedCorridor.lean`. `lean/CSTTT.lean` adds their transitive imports;
this note is the only audit addition.

- `cd lean && lake build`: exit 0, 446 jobs, final incremental build 8.95 s;
  the executed POS-04 module built in 6.5 s. No new-module warnings; existing
  warnings replay.
- `scripts/validate_lean.sh`: pass; all 39 rows / 210 declaration references
  resolve. No placeholders, untrusted axioms or high-confidence vacuity;
  30 existing non-gating heuristic leads.
- All **55** new public theorems resolve and print only the standard three
  axioms or fewer (two are axiom-free), via a `/tmp` probe.
- `git diff --check` and the new-module forbidden-construct scan are clean.
  Frozen science/models, registry and inventory are unchanged; `paper/` was
  not touched. No pytest, new-model evaluation, install or commit was run.

Reproduce with `cd lean && lake build`, `scripts/validate_lean.sh`, and
`lake env lean` probes importing `CSTTT` and printing the new theorem axioms.
