# G6d-2c: exact F/O games and actual-support futures

## Proved boundary

Eddy's ruling is applied: **legacy `AO` is unchanged**. Frozen Version O
(`G6_lane_spec.md:307–319`) does not consume hazards. The exact O entry point is
`GenericHandoff.POS04OperationalGame.Autonomy`; the exact F entry point is
`GenericHandoff.POS04FullGame.Autonomy`.

Both equivalences quantify over **every `RawLaneModel`**, including arbitrary
partial assignments, arbitrary assigned rows/ledger/receiver/history data, and
withdrawal edits:

```lean
POS04OperationalGame.game_iff_ao (m : RawLaneModel) :
  POS04OperationalGame.Autonomy m ↔ ComputedFIACH.AO m
POS04FullGame.game_iff_af (m : RawLaneModel) :
  POS04FullGame.Autonomy m ↔ ComputedFIACH.AF m
```

These remain POS-04-interface specializations. They do not complete the fully
polymorphic raw temporal decoder or the broader `RawHandoff` contract.
**TTH-06 stays conditional; no registry or inventory change.**

### O interpreter and rejection before defaults

The operational decoder reads rows, policy, resources, maintenance, ticks,
histories, routes and writers. Its completeness gate is exactly the union of
`autonomyInputs` and `phase2Dependencies`: acquisition additionally needs source
rows, events, realization and receiver inputs. Both sets are already required
by legacy O. `dependencies_no_hazards` proves hazards are absent.

`Protocol` checks completeness, six-role withdrawal, advancement, unchanged P,
and **all** declared phase-2 routes. Entries are defined by phase-2 execution;
every entry is quantified, without filtering away an invalid branch.
`entry_execution` and `entry_facts` derive positive numerators, nonempty raw
provenance, activation funding and an available writer. Each consumed cell has
`missing_dependency_rejects`; the combined F/O guard also covers each one.

`viability_eq`, `operational_projections`, and `advancement_operational_eq`
prove exact agreement with legacy operational rules on partial assignments.
The advancement equation exhibits only O's actual dependencies, despite the
legacy helper constructing a larger record whose other fields are unused.
There is no full-C6 readiness or all-unselected-action row-validity requirement.

The old `POS04ActualGame.OperationalAutonomy` and its missing-hazard
counterexample remain valid **historical full-C6-schema** declarations. They
are not the Version O entry point. No old theorem is redefined or erased.

### Independent strategy semantics and both directions

Neither game contains a greatest-set membership predicate. O's state safety
requires an actual K factor. F additionally computes `packageAtCheck` there
and the same coherent arrival package. Both use raw target-owned resources,
actual four-unit response rows, actual destinations, and the actual unbounded
counter/tick/record/register updater. Only selected responses must be safe;
every positive-support successor of each selected response is quantified.

- Finite check → game: construct an invariant from the greatest viable set,
  funded runs and retained-register writers. `certificateOfAO`/`certificateOfAF`
  prove every legal response normalized and preserve every actual branch.
  `soundness` invokes `invariant_game_soundness` (strategy construction and play
  induction), not a stored autonomy proof.
- Game → finite check: `game_invariant_completeness` derives the actual
  strategy-reachable run invariant. Project this invariant onto K, prove that
  projection viable, and invoke greatest containment. This supplies membership
  for **every** actual entry. Completeness, all-route acquisition and unchanged-P
  are independent raw protocol checks, not inferred from a lucky entry.
- `rows_actual_of_resource` and `actual_update_eq` bind the game to assigned
  C6's actual rows/updater on every resource-valid run. `record_actual_observer`
  links the operational record to the corresponding full-observer component.

`game_iff_named_readout` is proved for F and O. F also exports
`game_each_entry_exact_autonomy`, applying the existing, arbitrary-assignment
`AF_each_entry_exact_autonomy` to every actual entry. This reuses the genuine
G6c TTH-05 transport; it is not yet its polymorphic RawHandoff extraction.
`full_implies_arrival` derives same-package dependence at a genuine entry;
`af_implies_ao` is additionally derived through the games.

### Generic extraction, without an automatic finite-context assumption

- `StrategyGame.game_iff_run_invariant`: exact proof-bearing run-space
  invariant/game equivalence over arbitrary types and context-dependent rows.
- `GameFiniteProjection`: project the actual invariant, prove viability and
  entry containment using a **proved** interpretation law. Combined with the
  existing `GameFiniteConstructor`, this provides both engine directions.
- `POS04GameProjection.projection_laws` (F/O namespaces): prove these laws for
  every assigned table and every relevant run context. Exit states are excluded
  by state safety and raw row closure; a total projection cannot hide an exit.
- `ScaledRows`: positivity and normalization for arbitrary natural rows and
  positive scales, with exact `Rat` arithmetic.

The projection laws are family proof obligations. No finite-context closure,
context irrelevance, or decision completeness is assumed for unrestricted
recipes. The hybrid run-space game remains available without a finite lift.

### C6 full futures on actual support

`Transport.LumpedFuture.future_eq_quotient` is polymorphic in state, action,
outcome, class, code and observation. It groups exact outcome weights by class
and inducts over **all finite words**. The links concern observations, class
probabilities and successor codes on all states, not only audit roots.

On assigned POS-04 data:

- `outcomes6_nodup`: computed class enumeration has no duplicates for any data.
- `actual_weight_class_sum6`: actual outcome weights pushed to a class equal the
  existing class weight, including repeated destinations in raw rows.
- `actual_word_law6`: under the **existing** `FiniteBisim6`, actual and quotient
  full eight-component trace laws agree on every run and every finite word.
- `actual_all_words6` / `accepted_actual_all_words6`: derive actual-support
  full-interface sufficiency without adding the stronger `ActualBisim6` check.

Thus no new hidden-branch equality assumption narrows C6 acceptance. Individual
actual factors need not equal chosen representatives. The quotient is an exact
observation model; autonomy continues to execute the actual factor.

## Controls

| Model | F game | O game | Evidence |
|---|---|---|---|
| baseline | pass | pass | `positive_games` |
| packageDeletion | fail | pass | `registered_game_vectors` |
| lineageDeletion | pass | pass | `registered_game_vectors` |
| withdrawalDeletion | fail | fail | `registered_game_vectors` |
| missingHazard | fail | pass | `missing_hazard_full_rejected`, `missing_hazard_game` |

The old O scope failure is repaired, not transferred to legacy O. All registered
vectors transfer through exact arbitrary-partial equivalence. Negative game
readouts are necessary-condition/equivalence proofs, not failures of sufficient
checks. The existing P/L control results are unchanged.

## Argument classification

| Argument/object | Class | Constraint |
|---|---|---|
| `m : RawLaneModel` | raw assigned data | own dependencies, reference execution, withdrawal |
| `h : AO m` / `AF m` / game readout | evidence on computed semantics | exact checks / strategy plays |
| inputs, rows, updater, record, entries | defined | same assignment and raw phase-2 execution |
| package/readouts | defined | raw clause checks and actual run factor |
| safe set, projected set, selected strategy | constructed | viability or actual strategy-reachable invariant |
| auxiliary run invariant/certificate | proof witness | package, resources and every selected supported step proved |
| generic engine interpretations / projection laws | internal theorem arguments and evidence | adapters define interpretations; prove all-context lifting laws |
| actual/quotient future in generic lumping engine | internal mathematical interpretations | assigned adapter defines both; proves all-state one-step links |

No certificate accepts a separately supplied future, observer, code or updater
at these raw family entry points. Generic engine parameters do not constitute
an assembled polymorphic `RawHandoff` boundary.

## Field and readout coverage

Names below are in `POS04OperationalGame`, `POS04ExactGames`, or Assigned unless
qualified. Missing-input guards are universally quantified over each consumed
cell, rather than a single selected deletion.

| Field/readout | Law/check | Guard |
|---|---|---|
| source rows, history, realization, receiver | complete supported activated phase-2 execution | `missing_input_rejects_both`, `source_absent_rejects_both` |
| target rows / actual factor | `rows_actual_of_resource`, `actual_update_eq`, all-support closure | `no_safe_row_rejected`, missing row guard |
| policy / canonical P | raw `PUnchanged8` in Protocol | missing policy guard; false raw P equation contradicts Protocol |
| ledger/cost/recharge | unit conservation, strictly positive availability in `protocol_resources` | `invalid_ledger_rejected` |
| owner | raw resource owner checked target, `step_preserves` | `wrong_owner_rejected` |
| ticks / phase | raw unit tick on every nonempty row, actual addition | `wrong_tick_rejected` |
| order / progress | actual counter +1 (`run_readout_laws`) | updater/readout defined; no independent capped function accepted |
| writer | assigned writer at actual retained tuple, `protocol_writer` | `missing_writer_rejected`, missing writer cell guard |
| endogenous record | funded writer, `record_actual_observer`, +1 in `step_preserves` | `capped_record_differs` |
| route/register | `entry_execution`, raw tuple identity, actual retention | missing history/route guard; no independent supplied register |
| maintenance / funded bit | positive conserved ledger, `step_preserves` | `unfunded_entry_rejected`, withdrawalDeletion negative |
| six-role withdrawal | Protocol's raw `withdrawalCheck` | `invalid_withdrawal_rejected` |
| package primitives / state views | actual factor `packageAtCheck`, same-package F | packageDeletion / missingHazard F negatives |
| predictive classes / future weights | raw computed M, `actual_weight_class_sum6` | existing assigned C6 reference/bisimulation guards |
| full eight-field future / code | defined Assigned readouts; `actual_quotient_step6`, `actual_word_law6` | existing C6 readout guards; no supplied candidate |

## Classification, remaining work and checks

All mathematical additions are **(b)** for TTH-06/C6: corrected O interpretation,
exact F/O equivalences, projection/invariant engines, controls and actual-future
probability lumping. No existing definition/theorem statement changed; no (a)
rename. The root imports are wiring only. No new model or frozen data changes.

This boundary closes the O dependency finding and both arbitrary-partial game
equivalences. It does **not** finish G6d-2c: the fully polymorphic temporal
primitive/recipe decoder and combined raw game binding remain. In particular,
the generic engine's freely parameterized component interpretations must be
bound to the common polymorphic raw cells, not presented as `RawHandoff` itself.
Then proceed in order to G6d-3 package construction, G6d-4 acquisition/bridge,
G6d-5 autonomy transport and G6d-6 soundness/registry gate. No promotion now.

Self-review traced every entry and response through completeness, activation,
normalization, actual support, ledger and writer context, invariant induction,
finite projection and greatest containment. It also checked class enumeration,
duplicate destination accounting and all-word trace equality. Empty entries
reject; exits cannot be hidden; missing hazards distinguish F from O as required.

- `cd lean && lake build`: exit 0, 393 jobs. New modules compile without
  warnings; pre-existing CSTTT/vendor warnings remain. Representative module
  times: O equivalence 5.1s; F equivalence 5.4s; actual-future equivalence 3.2s.
- `cd lean && lake env lean /tmp/g6d-close-axioms.lean`: 105 public theorem/
  definition probes, exit 0; only the standard three axioms or fewer (five
  declarations have no axioms).
- `scripts/validate_lean.sh`: exit 0; inventory matches and registered evidence
  is axiom-clean. No gating findings. Existing heuristic leads remain.
- Forbidden-word scan of new Lean files: no matches; `git diff --check`: clean.
- `git diff --exit-code -- cst-tt/ lean/row_inventory.json`: exit 0. Frozen
  declarations/models, 08/09 surfaces and inventory are unchanged. `paper/`
  remains untouched. All changes are uncommitted.
