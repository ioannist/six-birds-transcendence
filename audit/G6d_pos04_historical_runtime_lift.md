# G6d: POS-04 historical runtime and concrete finite lift

## Proved boundary

This seam instantiates the committed polymorphic `HistoricalPackageRuntime` and
`HistoricalFiniteAutonomy`. It does **not** complete the final `RawHandoff`
assembly or promote TTH-06. Its new definitions/theorems are (b) mathematical
constructions for TTH-06 and TTH-05 reuse; no existing theorem, frozen model,
registry statement, or status changes.

Modules:

- `lean/CSTTT/Targets/GenericHandoff/POS04HistoricalRuntime.lean`
- `lean/CSTTT/Targets/GenericHandoff/POS04HistoricalRuntimeInstance.lean`

The historical source past is checked against assigned source action support.
The receiver retains terminal coordinates and actual history/event provenance,
resets acquisition counters, and executes the assigned target updater. Acquisition
and the resource game share **one** `execution` field by definition. The target
updater preserves the input carrier tag; receiver entries have target tag and
resource legality enforces target ownership. Funded source execution remains a
separate obligation of complete lineage, not an autonomy premise.

### Concrete lifting obligations

In namespace `POS04HistoricalRuntime`:

| Obligation | Proof | Scope |
|---|---|---|
| Same staged assignment | `target_eq` | Every partial source assignment; target equals the defined staged image |
| Run primitives equal finite-factor primitives | `finite_cells_eq`, `primitive_lift` | Every run context, including absent cells; retention follows the assigned withdrawal |
| Maintenance resources agree | `required_eq`, `resource_lift` | Every relevant run; same recharge requirement |
| Withdrawal metadata agree | `withdrawal_eq` | Interpreted six-role withdrawal and retained/removed resources |
| Account owners agree | `account_owner_lift` | Every resource-closed run and retained resource |
| Retained resources and responses are target-owned | `lift`, `ownership_of_resource_closed`, `lift_of_game` | Owner read from the same assigned resource cell; the public game supplies a genuine entry from which ownership is derived |
| Actual rows/update agree | `rows_eq`, `update_eq`, `rows_from_registers`, `update_from_registers` | Every ambient outcome, not a predictive-class representative |
| Every historical entry transfers | `entry_from_registers` | Every actual positive-support branch |

`positive_lift` discharges the concrete `HistoricalFiniteAutonomy.Lift` instance.
`checked_of_full_game` and `full_readout_transport` also discharge `Checked` and
`Lift` from the public historical full-game readout for **arbitrary partial
assignments**. The latter constructs a TTH-05 `ExactAutonomyCertificate` for
every derived entry. It does not assume a supplied ownership verdict or a
finite-context irrelevance flag.

The finite system is the image of actual legal response branches. The generic
`HistoricalFiniteAutonomy.projection_laws` supplies the support/advancement
projection; the concrete primitive, resource, and ownership equations above
complete it. Acquisition history is retained provenance, not post-withdrawal
resource support. No decision-completeness claim is made.

### Positive causal game

In namespace `POS04HistoricalRuntimeInstance`:

- `canonical_arrival_unique`, `raw_entries_inside`, `entries_nonempty`: entries
  come from actual supported source histories, activation, receiver reset, and
  funded target execution. Every entry is covered, and an entry actually exists.
- `row_exact`, `policy_normalized`, `policy_supported`, `policy_update`,
  `policy_step`: the target canonical policy uses `actionRow`, preserves every
  positive-probability branch, conserves the ledger, advances counters/ticks/
  records, and retains the register.
- `positive_certificate`: constructs the run invariant and responses from those
  laws. The strategy is causal; safety is required for every branch of its chosen
  response, not for every available action.
- `positive_full`, `positive_operational`: derive the named game readouts by the
  committed generic soundness theorem.
- `positive_each_entry_exact`, `positive_each_entry_words`: instantiate TTH-05
  at every entry, for all finite nominal disturbance words.

## Argument classification

| Argument/object | Classification | Binding |
|---|---|---|
| Partial source assignment, retention/removal lists, source-presence metadata | Raw data | `RawLaneModel` and its raw `protocol` projection |
| Primitive instruction syntax, cell maps, dispatcher, finite state/resource enumerations | Raw interface data | Committed POS-04 component definitions |
| Target assignment, received state, target rows and updater, entry set, run assignment | Defined objects | `model`, `execution`, `historical`, `target`, `Entries`, `runAssignment` |
| `Ready`, `Checked`, completeness, evaluated-cell equations | Evidence on raw data | Proved before expression totalization |
| Run invariant and response strategy | Auxiliary proof-bearing objects | Constructed in `positive_certificate`; all obligations proved against defined semantics |
| Projection and finite controlled system | Defined objects | `HistoricalFiniteAutonomy.project`/`factor`; concrete lifting laws proved |
| Full/operational readout, TTH-05 certificate | Derived conclusions | Game soundness and `each_entry_exact`; never supplied as raw verdicts |

## Readout and dependency coverage

| Readout/input | Law/check | Guard or regression |
|---|---|---|
| Source action support and policy, histories | Historical supported-history execution; `canonical_arrival_unique` | `missing_acquisition_no_games` for every consumed cell; concrete `missing_source_rows_no_games` |
| Events, realization, receiver, route table | Historical readiness and all-record activation; exact reset/entry adapter | `missing_acquisition_no_games`; `duplicate_event_entry` |
| Target rows and actual factor successor | `rows_eq`, `update_eq`, `policy_supported`; all ambient branches quantified | `missing_acquisition_no_games`, `missing_resource_no_games` |
| Tick/counter/progress | Exact updater identity; `policy_update`, `policy_step` | Missing target tick input rejects; `missing_past_ticks_entry` confirms unused source ticks are not required |
| Record/writers and route residue | Actual register retained; resource `StepLaw`; `policy_step` | Missing writer/route/history inputs reject before defaults |
| Ledger/maintenance/owner | `resource_inside`, `legal`, `policy_step`; all relevant run contexts | `missing_resource_no_games`; `withdrawal_no_games` directly refutes both game readouts |
| Package primitives at run context | `run_assignment_eq`, `primitive_lift`, `package_inside` | Package interpreter's committed missing-input checks; no absent cell is filled |
| Withdrawal resources and six roles | `withdrawal_eq`, `withdrawal_of_protocol`, `canonical_withdrawal` | `withdrawal_no_games` |

The missing-input guards quantify every syntactically consumed dependency and
have no contradictory `Ready` premise. Source ticks, source resources, and
hazards are proved absent from historical execution's dependency scope
(`no_source_ticks`, `no_source_resources`, `no_hazards`). The two acquisition
regressions establish actual entries; they are not yet whole arbitrary-partial
AF/AO equivalence theorems.

## Still required

1. Whole arbitrary-partial F/O equivalence: bind the already-extracted nominal
   `POS04HistoricalRuntimeProtocol.check` at the enclosing runtime validity
   boundary and prove the two directions to frozen AF/AO. The raw resource/game
   component alone is more general than the frozen nominal protocol: its
   withdrawal/resource game does not by itself enforce every-route phase-2
   readiness, the prescribed unit ledger, or every canonical P row. Positive
   game truth is **not** advertised as this equivalence.
2. Shared complete generic lineage, including funded source execution,
   corridor, bridge, typed endpoint, complete execution transport, and route
   `Indexed`/`Retained` facts.
3. Final polymorphic `RawHandoff` binding, generic F/O soundness, O separation,
   POS-04 controls, extended transcription, and the TTH-06 promotion gate.

TTH-06 remains `conditional`; the registry and inventory are unchanged. The
existing transcription script is a regression check for its existing scope,
not evidence that the unfinished final generic binding is transcribed.

## Checks

- `cd lean && lake build`: exit 0; 493 jobs, 28.86 seconds. New modules:
  19 seconds and 5.7 seconds. Existing linter warnings replayed; no new-module
  warnings.
- `scripts/validate_lean.sh`: exit 0; 39 rows, 209 unique declarations, no
  untrusted axioms, placeholders, or high-confidence vacuity findings. The 39
  non-gating heuristic leads contain no finding in either new module.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0 at its existing
  coverage, including its planted-drift checks.
- A `/tmp` `lake env lean` probe of all 70 new theorems: only `propext`,
  `Quot.sound`, and `Classical.choice` (or fewer).
- Forbidden-construct and whitespace checks clean. `cst-tt/` and the inventory
  unchanged relative to HEAD. No edits to `paper/`.
