# G6d-2c: actual-support lift and positive games

## Proved boundary

The new autonomy binding is `GenericHandoff.POS04ActualGame`. Its outcomes are
actual `Ambient` destinations. `Assigned.actualRows6` retains each raw branch
and its exact rational weight; `actualUpdate6` stores that destination directly.
The committed `POS04GameBinding` remains the quotient-observer schema. New
positive certificates use the actual-support binding.

### Support and C6 reconciliation

- `actual_probability_pushforward6`: for arbitrary decoded rows, the exact
  actual probabilities pushed forward to a predictive class equal `weight6`.
  The proof is by rational/list induction.
- `actual_quotient_step6`: each actual step's code and eight-component observer
  agree with its quotient image. This does not identify their factors.
- `canonical_actual_successors6`: every successor of every canonical POS-04
  action is already its predictive-class representative. No relevant canonical
  branch is lost. This is not extended to arbitrary assigned rows.
- `canonical_actual_step6`, `canonical_branch_mass`, and
  `baseline_branch_simulation`: every actual positive branch has exactly the
  same destination, numerator and counter/ledger/register update in its
  quotient image. `baseline_play_simulation` inducts over plays, keeping the
  same run states. Its context is supplied by the invariant lift below.
- `actualFuture6` is defined from assigned raw rows, actual updater, code and
  observer. `canonical_actual_bisim6` proves an outcome-resolving bisimulation;
  `canonical_actual_all_words6` derives full-interface sufficiency on **all
  states and all finite words**, without a horizon bound. Arbitrary-assignment
  equality with the quotient word law is not claimed.
  `actual_future_readouts6` links both readouts exactly to the assigned
  observer/code, and `canonical_actual_coarser6` retains the distinct
  p0w0/p0w1 merged-pair witness.

### Finite lift and soundness

`baseline_full_lift` and `baseline_operational_lift` instantiate
`GameFiniteConstructor.LiftWitness`. F uses `retainF baseline`; O uses
`retain8 (withdrawnInputs baseline) .target`. The greatest sets agree with the
existing finite engines via `full_engine_eq` and `c8_engine_eq`.

The context is funded maintenance, an available writer for the actual retained
register, and an actual K factor. The projection's extension at exits cannot
hide exits: context excludes them and response closure rejects exit branches.
The lift quantifies over **every viable factor set and every matching run
context**, including unbounded counters and ticks. `baseline_support_lift`
retains every actual branch in that set and proves solvency, advancement,
register retention, and ownership against the actual updater.
`baseline_normalized` proves exact rational normalization and nonempty positive
support. Only selected responses are required safe.

`baseline_full_certificate` and `baseline_operational_certificate` are built
by the finite constructor. Their `baseline_full_autonomy` and
`baseline_operational_autonomy` readouts use `invariant_game_soundness`, which
constructs the causal strategy and inducts over its plays. No game verdict or
stored game proof is unpacked. `full_implies_arrival` derives the same-package
consequence at a genuine entry using `game_same_package_implies_arrival`.

### Registered controls

| Model | F game | O game | Proof |
|---|---|---|---|
| baseline | holds | holds | `positive_comparison` |
| packageDeletion | fails | holds | `package_control_games` |
| lineageDeletion | holds | holds | `lineage_deletion_full_game`, `lineage_deletion_operational_game` |
| withdrawalDeletion | fails | fails | `withdrawal_deletion_rejects_both` |

`actual_game_control_vectors` combines these direct autonomy readout outcomes;
the package and lineage lane results remain the established G6c controls.
The lineage package is recomputed on its edited event assignment using
`lineage_assigned_package`, not a fixed positive side condition.
`missing_rejects_both` covers every consumed dependency before defaults;
`missing_acquisition_rejects_both` covers every phase-2 dependency;
`source_absent_rejects_both` rejects unavailable acquisition. These refute the
game readouts directly, not merely their sufficient checks.

## Finding: arbitrary-partial AO equivalence is false

`missingHazard` is exactly
`{baseline with assignment := put canonical .hazards none}`. Kernel proofs:

- `missing_hazard_legacy_AO`: G6c `AO missingHazard` holds; its operational
  scope does not consume hazards.
- `missing_hazard_no_game`: the full-future game completeness gate rejects
  the missing primitive before predictive decoder defaults can be used.
- `arbitrary_partial_AO_equivalence_false`:
  `¬ (∀ m, OperationalAutonomy m ↔ AO m)`.

Canonical truth does not establish arbitrary-partial equivalence. No narrowing
to complete assignments is substituted. An owner decision is needed: use a
separate exact operational dependency interpreter for O (not consuming
predictive hazards), or strengthen the legacy O completeness gate, which would
change its outcomes. Neither choice is applied. Arbitrary-partial F equivalence
also remains unproved.

## Argument classification

| Argument/object | Class | Check/construction |
|---|---|---|
| `RawLaneModel`, assignment, withdrawal | raw data | completeness and six-role withdrawal |
| actual rows/probabilities/updater | defined | raw action rows and assigned ledger |
| code/observer/future | defined | `actualFuture6`; no candidate supplied |
| entries | defined | phase-2 completeness, activation, realization |
| greatest F/O set | defined | committed ViableSet engine |
| auxiliary context/lift | evidence on raw data | quantified lift obligations |
| strategy | derived | invariant-game soundness |

## Readout coverage

| Readout | Law/check | Proof |
|---|---|---|
| factor/predictive | actual successor/raw class | `actual_factor_preserved6`, `actual_quotient_step6` |
| counter/order/progress | +1 | `actual_update_laws6`, `baseline_step` |
| tick/phase | assigned increment/mod 2 | `actual_update_laws6`, `baseline_step` |
| writer/record | actual register writer/funded counter | `baseline_entry_context`, `baseline_support_lift` |
| residue | register unchanged | `actual_update_laws6`, `baseline_support_lift` |
| funding/resources/ledger | assigned unit ledger, recharge | `baseline_resource`, `baseline_step` |
| owner | assigned target owner | `baseline_resource`, `baseline_step` |
| package | assigned clauses/actual factor view | `baseline_package`, `lineage_deletion_run_package` |

The lift covers all generated plays. Constant/capped observers are not supplied
arguments. Existing assigned guards remain intact; new missing-input and
withdrawal guards reject semantic readouts directly.

## Changes and remaining work

All additions are **(b)** for TTH-06/C6: actual-support dynamics, probability
simulation, lifts, positive game certificates, controls and the counterexample.
No (a) rename or existing statement redefinition. No model, registry or status
changes; TTH-06 remains conditional. `paper/` is untouched.

Remaining: owner resolution of the O-equivalence finding, arbitrary-partial F
equivalence, and fully polymorphic temporal/game extraction. Positive lifting
is proved for canonical POS-04 and registered control transports. No decision
completeness is claimed for unrestricted run recipes.

## Self-review and checks

Self-review traced each raw row through normalization, support membership,
actual update, factor projection, viability membership, resource and package
preservation, finite-certificate construction, and strategy-play induction.
Exit exclusion is independent of projection defaults. All finite support branches
of the chosen response are retained. Non-vacuity is the constructed positive F/O
certificates, not only a conditional invariant theorem. The partial-assignment
AO counterexample is a substantive boundary, not an implementation pass.

- `cd lean && lake build`: exit 0; 381 jobs. New actual-support module built
  in 3.8s; final game/control module rebuilds in 6.5s and 19s. No new module
  warnings; existing vendored warnings remain.
- `/tmp/actual-axioms.lean`: 64 probes (all new public theorems plus five
  lift/certificate definitions), standard three axioms only; two use none.
- Forbidden-construct scan of the new modules and `git diff --check`: clean.
- `scripts/validate_lean.sh`: final rerun exit 0; inventory matches, all
  210 registered declarations resolve, no untrusted axioms or gating scan
  findings; 29 existing heuristic leads remain.
- No registry, inventory, frozen science, existing Lean declarations or
  `paper/` changes. All edits left uncommitted.
