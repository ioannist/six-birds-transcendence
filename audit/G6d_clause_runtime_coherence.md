# G6d: temporal clause/runtime coherence and raw finite autonomy transport

**Proved component boundary; TTH-06 stays conditional.** No registry, frozen
declaration, result, or existing theorem statement changes. The complete shared
runtime lineage and final `RawHandoff` assembly are not supplied by this seam.

## Proved

`TemporalRuntimeCoherence.Raw` is polymorphic in cells, dependent values,
registers, states, actions, outcomes, histories, routes, stages, event IDs,
owners and disturbances. It binds the closed dispatcher's C6 constructor to
raw register instructions. The decoded data, projection, both futures, code
and observer are **defined**, not candidate arguments. `Laws.rows` preserves
the exact actual outcome list with rational weights, not just class masses;
`successor` preserves every actual branch and run update. All equations range
over **all run contexts**, hence cover any computed reachable closure.

- `valid_clause`: validity implies acceptance by this exact C6 constructor.
- `weight_link`, `code_link`, `word_law`, `soundness`: exact full-observation
  probabilities for every finite word and full future sufficiency, with the
  all-state quantifier retained. Word induction reuses `FutureReindex` and the
  accepted finite rule's class-mass theorem; no representative replaces a branch.
- `actual_readout_updates`: actual updater equations for all eight observations,
  plus factor, absolute ticks and writer.
- `actual_coarser`: lifts the accepted factor's strict merge to two distinct
  actual register contexts. `Laws.roots` checks representation of every decoded
  root, so an empty runtime carrier cannot pass by vacuous universal equations.
- `actual_funded_advancement`: actual funded progress and record advancement
  when the projected run lies in the rule's computed closure. Connecting actual
  acquisition entries to that closure remains an enclosing binding obligation.

`POS04TemporalCoherence.valid_iff` proves **both directions for every partial
assignment on both tags**, against assigned `C6Accept`. `dispatcher_rule` binds
the actual dispatched constructor by equality. `laws` holds for every complete
input assignment, even a rejected one; acceptance is not used to assume the
simulation. `canonical_valid` supplies concrete nonemptiness. `per_tag_controls`
retains canonical `(T,T)`, future-break `(T,F)`, record-break `(T,F)` and
un-realized-mix `(F,F)`. Missing cells and the zero ledger reject. Empty-row,
identity-updater and capped-progress proposals reject the coherence gate while
leaving the decoded clause fixed. These are sensitivity guards, not new model
versions. Prediction/owner alphabet changes are proved injective relabelings.

`RawFiniteAutonomy` constructs the frozen TTH-05 system from the existing
`PackageRuntime` raw package/acquisition/resource interface and typed finite
frame instructions. The factor step relation is the **exact image of actual
legal positive-support transitions**, not an independently supplied table.
Factor clause inputs must equal the actual run's primitive assignment, and
its required-resource table must equal the runtime's table on relevant runs.
Resources therefore cannot disappear through a projection. Six withdrawal
roles come from the decoded raw withdrawal, with injective resource IDs and
proved removed/retained disjointness. Owner instructions are checked against
actual target-owned responses and every retained resource's interpreted account
on relevant runs. `retained_actual_ownership` derives the actual account owner;
a table merely declaring target ownership cannot hide a foreign account.

- `projection_laws`: derives the existing `GameAutonomyTransport` obligations.
- `each_entry_exact`: constructs an `ExactAutonomyCertificate` for every genuine
  entry from the semantic game and its constructed reachable-play invariant.
- `each_entry_words`: applies the existing TTH-05 theorem to every finite
  declared disturbance word.
- `all_support`: retains **every** positive-support successor before projection.

The finite `antiStall` and `budgetSolvent` relations both require an actual
updater/`ResourceRuntime.StepLaw` witness: that stronger computed law checks
strict run advancement and solvency. Counters are not placed on recurrent
finite states. The inside set is the image of the actual game invariant.
These theorems are semantic projection results, **not** finite algorithm
decision-completeness claims. In particular, the factor step may involve
existential unbounded run contexts.

## Argument classification

| Argument | Classification | Constraint |
|---|---|---|
| Temporal schema/bindings and owner-ID map | Raw data | Closed C6 rules, decoding presence, injective IDs |
| Runtime rows/program/readout instructions | Raw data | Exact row, successor, full-observation, ticks and writer equations on all contexts |
| Runtime projection instruction | Raw data | Complete reads and exact actual-update simulation |
| Source assignment / staged target | Raw input / defined object | The target is `PackageRuntime.target`, built by staging/gluing |
| Temporal `Ready`, acceptance, `Laws` | Evidence on raw data | No independently supplied future, code, observer or verdict |
| Temporal decoded data/futures/code/observer | Defined objects | Decoder and interpreter only |
| Finite frame enums/primitive, maintenance and owner instructions / ID map | Raw data | Complete reads, execution enum agreement, injective IDs |
| Finite `Checked` and `Lift` | Evidence on raw data | Actual primitive/resource equations on every relevant context; owner equations |
| `FullGame` | Previously derived semantic readout | Existing causal strategy against all declared disturbances and all support branches |
| Frozen system, withdrawal, advancement, inside and certificate | Defined/constructed objects | Shared interpreter, game invariant and proved projection laws |

## Readout and field coverage

`TR` below is `TemporalRuntimeCoherence`; `RF` is `RawFiniteAutonomy`.
All TR readout laws are exported together by `actual_readout_updates`.

| Field | Checked law | Guard |
|---|---|---|
| Decoded C6 primitives / every binding | Complete decoder, exact dispatcher constructor | `TR.missing_clause_input`; POS-04 `missing_cell_guard` |
| Actual action rows / probabilities | Exact row-list equality; summed weights derived | `TR.row_guard`; POS-04 `empty_rows_rejected` |
| Actual factor successor / counter / ledger context | Projection commutes with actual updater on all contexts | `TR.successor_guard`; POS-04 `stationary_rejected` |
| Predictive now | Finite raw predictive value of actual outcome | `TR.observation_field_guard` with `.predictive` |
| Event order | Previous counter plus declared advance | Same guard with `.order` |
| Tick phase / absolute ticks | Raw tick increment, modular observation; exact absolute read | Same guard with `.tickPhase`; `TR.ticks_guard` |
| Progress | Previous counter plus advance; strict when accepted/funded | Same guard with `.progress`; POS-04 `capped_progress_rejected` |
| Writer | Route tuple matching and preserved residue | `TR.writer_guard` |
| Record | Actual funding/writer/counter formula; accepted advancement | `TR.observation_field_guard` with `.record` |
| Route residue | Actual register preserved by updater | Same guard with `.residue` |
| Maintenance | Actual conserved positive-funding update | Same guard with `.maintenance`; POS-04 `zero_ledger_guard` |
| Owner | Raw resource owner through injective typed map | Same guard with `.owner` |
| Each runtime row, readout or program input | Presence before interpretation | `TR.missing_runtime_row`, `missing_runtime_readout`, `missing_runtime_update` |
| Projection inputs | Presence before interpretation | `TR.missing_projection_input`; `RF.missing_field_guard .projection` |
| Represented temporal roots | Each decoded root has an actual run preimage | `TR.missing_root_guard`; POS-04 `laws` proves it by the register bijection |
| Finite factor primitive cells | Exact equality to actual run assignment, before clause evaluation | `RF.changed_factor_cell_guard`, `missing_factor_cell_guard` |
| Finite required resources | Exact raw required-table equation and retention | `RF.changed_resource_table_guard`, `omitted_resource_guard`, `missing_field_guard .maintenance` |
| Action owner | Exact owner instruction against actual legal response | `RF.wrong_action_owner_guard`, `missing_field_guard .actionOwner` |
| Retained resource owner | Raw owner instruction equals target and matches actual interpreted account on retained resources | `RF.wrong_resource_owner_guard`, `changed_account_owner_guard`, `missing_field_guard .resourceOwner` |
| Resource IDs | Injective relabeling, disjoint withdrawal lists | `RF.aliased_resource_guard` |
| Disturbances / actions | Exact execution enumeration; nonempty disturbances | `RF.empty_disturbance_guard`; enumeration equalities in `Checked` |

Parameterized mismatch guards reject the check when a required equation is
broken. They do not claim that intrinsically constant lawful owners must vary,
or constitute exhaustive isolated sensitivity tests. Missing-input guards
conclude rejection; none assumes readiness together with its incompatible
missing dependency.

## Remaining gate and next construction

1. Complete the concrete **multi-resource F/O runtime adapters** to
   `RuntimeComponents`/`PackageRuntime`, including withdrawal as raw data,
   the unit-ledger protocol and the shared acquisition/post-exit frame. The
   already committed single-ledger register game is not silently substituted.
2. Instantiate the new finite frame and prove its primitive/resource lift laws
   for POS-04 arbitrary partial assignments. No automatic finite-factor lift
   of unrestricted recipes is asserted.
3. Bind complete generic lineage to the same runtime cells, with the actual
   bridge execution laws and the route `Indexed`/`Retained` obligations (distinct
   paths, shared endpoint, every retained branch). The complete family seam is
   still the reference; the weaker legacy lineage is not used as an implication.
4. Final `RawHandoff`, F/O soundness, O separation and all control equivalences,
   then extend transcription and apply the registry gate.

All additions are **(b) mathematical additions for TTH-06**, implementing the
accepted hybrid extraction. No existing statement is weakened or renamed.
There is no status/ceiling change or narrowing in this seam. The raw finite
transport is not yet a POS-04 nonempty instance; it is not evidence for promotion
until that adapter and the complete generic assembly are proved.

## Checks for this boundary

`cd lean && lake build` succeeds (474 jobs), with no warnings in the new
modules; pre-existing CSTTT/vendor warnings remain. All 60 new public theorem
axiom probes use only `propext`, `Quot.sound` and `Classical.choice` (or fewer).
The inventory regenerates byte-identically: 39 rows / 210 declaration entries.

`scripts/check_tth06_transcription.py` now additionally evaluates the new raw
temporal interpreter's rows on both tags, all twelve ambient states and all
declared actions, in funded and unfunded contexts. Exact `Fraction` comparison
uses the frozen imported action tables, not a Python reimplementation of the
interpreter. In-memory probability drift and a missing-result drift are tested.
The earlier G6b vectors and complete-execution relabeling regression retain
their stated coverage and limitation; they are not evidence for the unfinished
generic lineage/RawHandoff binding.

`scripts/validate_lean.sh` exits 0: no placeholders or high-confidence vacuity
findings, and 37 non-gating ignored-input heuristic leads. The new lead on
`factorAssignment` is its dummy `Unit` register argument; the finite state is
used by the assigned primitive expressions. This is not a constant package
predicate. The two new transcription drifts are caught. Frozen records and
`paper/` are untouched.
