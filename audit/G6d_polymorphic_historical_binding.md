# G6d: polymorphic historical acquisition and P/A binding

## Proved boundary; TTH-06 remains conditional

This seam adds five imported modules under `Targets/GenericHandoff/`:

| Module | Result |
|---|---|
| `HistoricalAcquisition` | Historical action support, typed source-to-target historical coordinates, defined receiver reset, and every actual positive-support target entry. |
| `HistoricalPackageRuntime` | Shared staged/glued assignment and target execution for the closed eight-schema package and resource/game interpreters; generic F/O game soundness and `AF → P`. |
| `HistoricalExecutionProjection` | Checked probability and successor equations throughout funded actual execution's closure; word induction preserves the projected actual terminal and each supported branch. |
| `POS04HistoricalAcquisition` | POS-04 acquisition instance, nonempty canonical entries, exact arbitrary-partial row/update equations, arbitrary-row/history and activation-rule equivalences, locality and guards. |
| `POS04HistoricalDuplicateEvents` | Duplicate-ID diagnostic: first record non-mixed, appended record activates, new entries exist, legacy AO and committed historical O accept. |

These are **components**, not the completed `RawHandoff`, complete generic lineage, or final TTH-06 theorem. The registry and inventory are unchanged. No new model data or prediction is declared. The committed POS-04 family remains the evidence surface.

### Acquisition semantics

The historical interpreter reads raw source histories and action support, retains the actual terminal coordinate and raw past/path, executes receiver initialization instructions, and retains **every positive-support branch** of the target response. Source funding and source ticks are not intrinsically required. Policies are raw recipes indexed by history, edge index, and factor: the generic construction does not require a stationary policy.

Source and target historical factor types may differ. `targetCoordinate` is a raw typed coordinate instruction; target support is checked on the mapped history. POS-04 instantiates it with the identity between its isomorphic K-coordinate types. The receiver reset is separately interpreted from raw instructions. Identifying that reset with the typed source-to-target history map belongs to the enclosing lineage coherence gate, not an assumed consequence of historical support.

The historical K-table pullback in the POS-04 instance is **only** for validating recorded histories. Target execution uses `actualRows6` and `actualUpdate6` over `Ambient`, including exits. `actual_supported_branch_entry` proves this for arbitrary partial assignments. Unsafe acquisition branches are not filtered to make an invariant pass.

Funded source execution remains a separate, stronger lineage obligation. `HistoricalExecutionProjection.Laws` checks exact row-list equations, including probabilities, and every actual supported successor over `ExecutionFrontier.Closure`. `fold_projects` is word induction; `support_projects` retains the probability witness of each individual actual branch. Historical support alone never establishes these laws.

## Generic P/A results

`HistoricalPackageRuntime.Raw` defines one target assignment through `DispatchedPackage.global`. The package dispatcher, historical reset/entries, and resource rules read this assignment. The target row/updater is one `execution` field shared **by definition** by acquisition and the resource game (`acquisition_resource_rows`, `acquisition_resource_update`).

- `package_soundness`: `PackagePass m a → IntegratedTargetRealization m a`, using the committed dependent gluing/dispatcher construction.
- `full_soundness` and `operational_soundness`: proof-bearing validity yields the corresponding independently defined causal game readout by `invariant_game_soundness`/`ResourceRuntime.soundness`.
- `full_pass_iff_readout` and `operational_pass_iff_readout`: semantic completeness of proof-bearing invariants, using `game_invariant_completeness`. **No decision completeness** is claimed for an unrestricted finite constructor.
- `full_autonomy_implies_package`: a full game supplies a genuine entry; its entry safety entails the same staged package's arrival realization.
- `full_implies_operational`: full package safety includes operational inside safety.
- `full_answers_every_word`: the strategy answers every finite declared disturbance word, preserving package and resources on its generated plays. Safety is not demanded under every available action.

`PackageAt` evaluates the closed dispatcher on `runAssignment`, interpreted from the same primitive assignment and actual run registers. It also checks the same arrival package and finite inside coordinate. Neither package validity, entries, dynamics, strategies' safety, nor game readouts are free verdict fields.

The enclosing layer still needs complete temporal/package-runtime coherence, the shared complete lineage binding, the POS-04 **whole-game** equivalences, and finite-factor TTH-05 transport with this entry definition. None is inferred from these component theorems.

## Argument classification

| Argument | Classification and use |
|---|---|
| Carrier, source/target cell/value, factor, action, disturbance, outcome, resource, stage/event/history/route and register types | Raw typed interfaces. They are polymorphic, not POS-04 enumerations. Exhaustive/nonempty domains are checked where consumed. |
| Package language, stage, cover, closed eight-schema dispatcher | Raw rules/maps/data interpreted by the committed package engine. `PackagePass` checks them. |
| Histories, source/target rows and edge action recipes, typed historical coordinate map | Raw static instruction recipes; dependencies must be complete. Historical support is computed, never supplied as a verdict. |
| Route/event/realization/receiver views; reset and response instructions | Raw views/instructions; missing cells/references reject. Arrival and entry relations are defined. |
| Target execution, resource schema and binding instructions, run-cell instructions | Raw data on the shared target assignment. Resource predicates and run assignments are defined interpretations. |
| Funded execution frontier, factor projection, outcome decoder, historical table recipe | Raw instructions for the comparison component. The enclosing layer must identify them with its acquisition/lineage data. |
| Readiness, exact row/successor equations, package and withdrawal checks | Evidence on raw data. No assumed boolean simulation or autonomy flag. |
| Auxiliary invariant/strategy and its obligations | Proof-bearing certifier allowed by the hybrid architecture; soundness derives the game readout by induction. |
| Staged/global assignment, decoded values, entry set, rows, updater, run package and game readouts | **Defined objects**, never independently supplied candidates. |

## Field/readout coverage and guards

Names below omit each module's namespace. These are the coverage of **this component seam**, not the final RawHandoff promotion table.

| Raw field/readout | Check/law | Guard or exact equation |
|---|---|---|
| Histories, source rows and source edge actions | Successful reads; nonempty history; positive support on every recorded edge | `missing_view_no_entry`, `missing_dependency_rejected`, `unsupported_source_edge_no_arrival` |
| Typed historical coordinate map, target rows and target edge actions | Successful reads; positive target support on the computed mapped history | `missing_view_no_entry`, `missing_dependency_rejected` |
| Route domain and disturbance domain | Nonempty and exhaustive declared lists | `DomainCheck`, `empty_disturbances_no_entry` |
| Event references, realization and path continuity | Declared/resolved events; every stage realized; contiguous strict steps; entry/exit boundary and support | `missing_event_rejected`, `unrealized_path_no_arrival`, `nonstrict_event_rejected` |
| Receiver availability/activation | Source presence and target funding; any eligible realized mixed raw record when required | `source_absent_no_entry`, `source_absent_no_games`, POS-04 `absent_source_no_entries` |
| Receiver factor/past/path and reset registers | Defined instruction interpretation with complete dependencies | `arrival_terminal_defined`, `missing_reset_rejected`, POS-04 `reset_computed` |
| Response instruction and target branch probabilities | Successful instruction; declared disturbance/action; normalized row; actual positive support | `missing_dependency_rejected`, `missing_target_row_rejected`, `every_supported_branch_is_entry` |
| All target successor registers | Defined checked execution; no branch discarded | `missing_target_update_rejected`, POS-04 `updater_computed`, `actual_supported_branch_entry` |
| Package cells, scopes, cover and gluing | Committed `DispatchedPackage.Valid`; global restrictions and closed dispatcher acceptance | `package_soundness`; `failed_clause_no_full`; committed package-engine locality/deletion guards |
| Resource ownership, ledger, retained residue and withdrawal | Defined `ResourceRuntime` predicates; invariant obligations against actual execution on every generated play | `missing_resource_no_games`; generic `full_soundness`/`operational_soundness` |
| Run-context package inputs | `runCells` instruction evaluation of the same assignment; dispatcher checks on every safe run | `PackageAt`; `game_entry_package` and `full_answers_every_word` |
| Funded source factor and every future branch | Exact projection/update and row equations on **the whole actual closure** | `row_mismatch_rejected`, `successor_mismatch_rejected`, `fold_projects`, `support_projects` |
| Comparison instruction inputs | Complete factor, decoder and history-table dependencies | `missing_projection_rejected`, `missing_decoder_rejected`, `missing_table_rejected` |
| Any POS-04 acquisition dependency | Syntactic union of every consumed static/reset/row/update dependency | `ready_iff`, `missing_consumed_no_entries`, `entries_locality` |
| Unconsumed POS-04 source context | Proved scope exclusion and locality, not an assumed relevance flag | `unconsumed_replacement_entries`, `missing_past_ticks_entry`, `unavailable_source_recharge_entry` |

Missing-input guards reject existence of readiness/entries or games. They do not assume readiness alongside an incompatible missing-view premise.

## POS-04 instance and limits

`canonical_arrival` and `canonical_entry` instantiate both different-past routes; `entries_nonempty` supplies a concrete witness. Their supported edge probabilities come from `actionRow` by exact division by four. `actual_row` and `updater_computed` apply to arbitrary partial assignments with exactly this component's consumed dependencies. No source tick/resource/hazard completeness is added.

`missing_past_ticks_entry` and `unavailable_source_recharge_entry` preserve reception and target branches. They are acquisition regressions, **not** claims of full package acceptance or complete lineage. For example, full F can still reject a missing package primitive.

The acquisition component does not alone enforce the entire frozen phase-2 writer/ledger/strict-positive-target-row protocol. Those checks must be bound to the resource/package/entry gate and proved in the whole-instance equivalence. Its target-history/receiver coherence likewise remains a checked enclosing obligation. Thus canonical acquisition truth is not substituted for arbitrary-partial AF/AO equivalence.

## Remaining promotion gates

1. Combine complete generic corridor, execution bridge, typed endpoint, and `Indexed`/`Retained` route semantics from the same runtime cells. Preserve distinct paths, a shared computed endpoint, and retention across every supported branch.
2. Bind historical table/map/reset recipes to that runtime by checked equations; bind full temporal dispatcher/code/readout laws as well. Keep historical autonomy acquisition distinct from funded actual lineage acquisition.
3. Instantiate the complete historical package/resource binding on POS-04, prove arbitrary-partial AF/AO and complete lineage equivalences, transfer controls and the relabeling separator.
4. Transport the finite-factor TTH-05 certificates from every new derived entry with proved lifting laws.
5. Finish `RawHandoff`, generic F/O soundness, O named-readout separation, F dependence, transcription and the full argument/readout tables. Only then consider promotion.

Eddy found an obstruction to the pending arbitrary-assignment equivalence: disabling source support on the original event records and appending the original `mix1` preserved AO but destroyed the new entries. Activation incorrectly used first-record lookup and route membership, whereas frozen `mixed7` scans all non-exit records. This is resolved by a separate raw activation-record instruction reading the same event cell; it scans every non-exit record. Path lookup stays first-match, exactly as frozen `event6` requires. No ID-uniqueness condition is introduced.

`activation_iff_active7` is exact for arbitrary decoded inputs, including duplicates and records outside the selected route. `POS04HistoricalDuplicateEvents.duplicate_regression` proves new entries and legacy AO / committed historical O acceptance. It does not substitute for the pending whole polymorphic game equivalence. TTH-06 remains **conditional**.

## Statement changes and verification

All additions are **(b) mathematical additions for TTH-06**: polymorphic historical acquisition, shared package/resource game binding, checked actual-execution projection, and the POS-04 component instance. The new historical `Activated` signature/definition, and consequently `Arrival`/`Entry`, change to the all-record interpretation: **(b) semantic repair for TTH-06**. POS-04 `eventProjection.strictStep` now includes the declared unit clock law rather than only the raw flag: another **(b) semantic repair** needed by the arbitrary-partial adapter. Committed legacy statements, registry text/status are unchanged. No (a) renames.

Verification: full `lake build`; `scripts/validate_lean.sh`; the existing `check_tth06_transcription.py` family regression; explicit `#print axioms` for all 79 seam theorems; forbidden-construct and frozen-file checks. The transcription regression remains limited to its committed family result, not a claim that the unfinished generic assembly has been transcribed.

## Lookup sweep and continuation

| Lookup | Frozen semantics | Sweep result/evidence |
|---|---|---|
| Activation events | `mixed7` scans every non-exit record, without route membership or unique IDs | **Fixed**: `activationEvents` raw instruction on the same event cell; `activation_iff_active7`, `activated_append_right`, `no_mixed_record_rejected`, `missing_activation_no_entry`; duplicate-ID regression. |
| Path events | `event6` first match; `strictEvent6` requires unit clock and realization | First match retained. An additional unit-clock discrepancy was **fixed** in `eventProjection`; `path_event_rule_iff` is exact for arbitrary decoded inputs. |
| Routes | `routeTuple` first matching route | `routeView` and `pathExpr` use the same `find?`. Absent routes produce empty paths/histories and are rejected, not replaced by canonical routes. |
| Rows | `rowWeight` sums all matching nonnegative numerators | `historyRows` keeps every K-destination entry. `row_weight_support_iff` and `historical_row_support_iff` prove arbitrary-row equivalence, including duplicate destinations and zero entries. |
| Histories | Typed history function, selected by first route | Same function; no record-list resolution. `recorded_support_iff` proves exact indexed-history support equivalence for arbitrary data/history. Missing cells reject. |
| Writers | Typed `Tag → RouteId → Bool`; resource writer selection uses frozen tuple priority | No first-match/all-record list divergence. Acquisition alone does not certify writers; the resource binding uses the frozen writer interpreter. Whole-game equivalence remains open. |

The additional activation instruction consumes the event-table cell, which was already required; it adds no POS-04 completeness premise. The duplicate diagnostic changes one raw field, without touching frozen data or introducing a new positive model.

Continuation completed the arbitrary-row/history support, activation, and strict-event adapters. They must still be composed with the phase-2 ledger/writer protocol into the whole arbitrary-partial runtime equivalence. Shared complete generic lineage, TTH-05 entry transport, final RawHandoff soundness/separation, transcription extension, and promotion remain open.

Reproduce:

```sh
cd lean && lake build
cd .. && scripts/validate_lean.sh
python3 -B scripts/check_tth06_transcription.py
```

Verification after the repair: full build **487 jobs, exit 0**; validator **exit 0**, 210 registry declarations, zero placeholders and zero gating vacuity findings (38 non-gating heuristic leads); existing family transcription regression and planted-drift checks **pass**; **79/79** explicit seam theorem probes are axiom-clean; forbidden scan and `git diff --check` clean. All tracked `cst-tt/` files are byte-identical to HEAD; `paper/` is untouched. New-module builds: historical acquisition 5.5 s, acquisition adapter 8.4 s, duplicate regression/guards 13 s (incremental measurements). Replayed warnings are from existing modules; these modules emit no new warnings.
