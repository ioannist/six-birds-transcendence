# G6d: historical-support F/O autonomy

## Proved seam and remaining boundary

Implemented the manager/Eddy ruling: autonomy validates recorded source history
against **raw source action support**, applies the receiver reset, and executes
the funded **target** response. Complete lineage keeps its stronger actual
funded-source interpretation. No existing AF, AO or lineage definition changes.

New modules in `lean/CSTTT/Targets/GenericHandoff/`:

- `HistoricalSupport.lean`: polymorphic raw-table support and history folding.
- `POS04HistoricalAutonomy.lean`: explicit historical acquisition and actual
  target entries; arbitrary-partial strategy-game equivalences and controls.
- `POS04HistoricalFIACH.lean`: the complete **POS-04-family** assembly with the
  new autonomy interpretation, semantic control vectors and O separation.

The fully polymorphic RawHandoff binding remains open. These family theorems
do not discharge that promotion gate. TTH-06 stays conditional; the registry
and inventory are unchanged. There is no new mathematical blocker in this seam.

## Acquisition and exact equivalences

The staged assignment is `image m.assignment`. `arrival` first requires the
computed `phase2Check` from frozen `G6_lane_spec.md` §§3/4F/4O. `phase2_facts`
proves input completeness, nonempty history, raw source support, activation and
realized strict path checks. `sourceTerminal` folds the raw history's actual
coordinates, and `source_terminal_eq` proves equality to its actual last state.
No predictive representative or stored endpoint class enters.

`receiveRetained` reads the actual receiver cell and performs the declared reset.
`phase2Execution` executes `actualUpdate6` for **every** target row element,
retaining its exact numerator. Exits are not filtered. `target_response_row` and
`target_response_all_support` prove these are the actual enabled probabilities
and every positive-support branch. `HistoricalEntries` is defined from that
computed list, not supplied as a predicate argument.

In `POS04HistoricalAutonomy`:

```lean
full_game_iff_af (m : RawLaneModel) : FullAutonomy m ↔ AF m
operational_game_iff_ao (m : RawLaneModel) : OperationalAutonomy m ↔ AO m
```

These quantify **all partial assignments**, not merely canonical truth.
`phase2_execution_eq`, `execution_entries_eq`, and `entries_iff` identify the
new execution with the committed entry semantics under the independently
checked raw `Protocol`. The existing exact F/O strategy construction and
converse then apply. Every target resource-safe run has the actual target row
(`responses_are_actual_rows`); the updater is the committed actual updater.
No supplied autonomy proof is a raw field. The family handoff gates check AF/AO
and derive the games through the proved invariant/strategy induction.

The twelve acquisition cells are exactly:
`rows.source, rows.target, policy, ticks.target, resources.target, maintenance,
histories, eventTable, realized, receiverInput, routeTable, writers`.
`exact_dependency_scope` proves equality to the complete O dependency union.
Withdrawal metadata, unit/conserved ledger, whole-domain tick/writer checks and
target-P preservation remain the existing computed protocol checks.

`all_consumed_missing_inputs_reject` and `missing_acquisition_no_games` reject
**every** consumed missing cell before decoder defaults can support acceptance.
Source ticks, source resources, hazards and the unused full C6 interface are not
added to O. F additionally re-evaluates the package on the actual run factor and
requires package primitive completeness as frozen AF does.

## Agreement with the stronger runtime

`FundedSourceExecution a rid` checks:

1. the complete full acquisition updater scope (including source ticks and
   resources);
2. `supportedWord` at every actual source history step: declared action and
   disturbance, enabled source row (funding/recharge/affordability), and positive
   probability for the actual destination, recursively after the actual updater.

`funded_source_executes` constructs the supported history by induction through
the generic execution checker. `reception_agrees_funded_execution` proves exact
received-value equality, for arbitrary assigned histories. `target_step_agrees_runtime`
proves exact target row and update equality for **all** outcomes.

For a genuine stronger-runtime arrival, `stronger_arrival_agreement` also
requires its independently computed `PathCheck` and `Activated` checks on the
specific route (including mix on **that** path). These are necessary comparison
conditions, not new AF/AO premises. The weaker historical interpretation is not
claimed to imply funded source execution or complete lineage.

## Regressions and named controls

| Raw proposal | Historical arrival | F game | O game | Complete lineage |
|---|---|---|---|---|
| baseline | passes | passes | passes | passes (existing proof) |
| `missingPastTicks` | passes on both routes | fails: package primitive missing | passes | fails |
| `sourceRechargeUnavailable` | passes on both routes | passes | passes | fails: no funded source history |

Thus both diagnostics pass **historical acquisition**. A missing package cell
still rejects F for its proper extra obligation. The source-recharge diagnostic
passes F too; its target package remains intact. These are committed diagnostics,
not revised frozen models/predictions. The old mismatch theorems remain valid
for the unchanged, stronger source-execution runtime.

`POS04HistoricalFIACH.F_control_vectors` proves `(F,T,F)`, `(T,F,T)`, `(T,T,F)`.
`O_control_vectors` proves `(F,T,T)`, `(T,F,T)`, `(T,T,F)` on the **named semantic
readouts**. `operational_three_lane_separation` exports the three existential O
witnesses. `relabel_F_vector` / `relabel_O_vector` keep the complete execution
transport failure; weaker legacy lineage never supplies L.

Additional direct guards reject erased raw source rows, an unrealized mix2,
source absence, invalid ledger/withdrawal, wrong target owner, wrong unit tick,
and unavailable writers. Negative games follow nonempty-entry/resource/strategy
necessities or exact equivalence, not failure of a sufficient constructor.

## TTH-05 and dependence

`full_each_entry_exact` transports a genuine `ExactAutonomyCertificate` for
**every** derived historical phase-2 entry. `full_each_entry_words` supplies
every nominal disturbance word and the terminal package. These reuse the proved
`POS04GameAutonomyTransport` finite-factor lifting laws on the actual support;
no omitted-context irrelevance or generic finite-context premise is assumed.

`full_implies_package` / `POS04HistoricalFIACH.full_dependence` derive AF⇒P at
a genuine entry using the same-package game theorem. That implication is
disclosed and is not used to derive the separate P field in family soundness.

## Argument classification

| Argument/object | Classification | Binding |
|---|---|---|
| `m : RawLaneModel` | raw assignment and withdrawal metadata | existing immutable typed cells |
| route ID/history/action-outcome word | raw execution domain/data | extracted from the same assigned histories/routes/policy |
| source terminal, receiver result, entries | defined objects | history fold, Option receiver instruction, actual target update |
| target dynamics/resources/package rules | defined interpreters | committed exact assigned F/O rules; actual-row equations |
| protocol and phase-2 check proofs | evidence on raw data | completeness, raw support, activation, ledger/owner/tick/writer checks |
| funded-source/path/activation hypotheses | evidence for comparison only | actual full runtime checks; not autonomy premises |
| invariant/strategy certificate | auxiliary proved evidence | existing greatest-set constructor and game induction |
| finite-factor lift | per-instance proved evidence | `POS04GameAutonomyTransport.projection_laws` |
| family handoff certificate | raw model only | computed P/L/AF or P/L/AO gates; no stored readout |

## Field/readout coverage

| Field | Law/check | Guard/evidence |
|---|---|---|
| source rows + policy | raw recorded edge support | `phase2_facts`, erased-source guard, every-cell missing guard |
| histories/routes | nonempty lookup; actual terminal/provenance | `source_terminal_eq`, `arrival_computed`, missing guard |
| events/realization | strict realized paths, activation | unrealized-path guard, source-absent guard, missing guard |
| receiver | checked raw reset; no canonical fallback | missing guard; reception agreement |
| target rows | exact actual probabilities; every branch retained | `target_response_all_support`, actual-row equation, branch-deletion transcription probe |
| target tick | unit tick from assigned table; reception starts at zero | `wrong_tick_no_games`; old exact readout laws |
| counter/progress | actual update adds one | committed `run_readout_laws`; game StepLaw on every generated play |
| funding/ledger | positive conserved unit funding on target steps | `protocol_arrival_budget`, invalid-ledger guard, `execution_entries_positive` |
| writers/record | required writer; record advances with funded counter | writer guard; game StepLaw on every play |
| residue | exact raw tuple retained by actual update | entry construction, actual readout laws and TTH-05 lift |
| owner/resources | target ownership, six-role removal, retained recharge | wrong-owner/withdrawal guards; resource/game and lift laws |
| package | assigned primitive checks on actual run factor | F↔AF, deletion negative, same-package entry theorem |
| source tick/funding | full source runtime only | missing-source-tick lineage regression; no-funded-execution diagnostic |

No candidate observation, code, successor, entry set or verdict is supplied.
Future C6 sufficiency remains a separate clause/execution obligation; autonomy
does not infer it from operational viability.

## Status, checks, and next work

All new mathematical definitions/theorems are **(b), TTH-06**. No (a) changes,
no existing statement changes, no narrowing and no status change.

The transcription extension compares Lean-evaluated historical entries,
probabilities, funding and F/O outcomes against frozen G6b for all four controls.
The two committed diagnostics are compared to the unchanged baseline entry
data, with their separately kernel-proved outcomes. Expensive Boolean checks
use kernel-proved computation equalities, as the existing checker does; game
readouts are not evaluated by Python. Six new planted drift checks are caught.

Verification:

- `cd lean && lake build`: exit 0, 482 jobs. The final fresh historical autonomy
  module took 24 s; family assembly 2.0 s. No new-module warnings; existing
  linter warnings are replayed.
- `scripts/validate_lean.sh`: exit 0; 39 rows, all 210 names resolve, clean
  axioms, matching inventory, zero placeholders/high-confidence vacuity;
  38 heuristic ignored-input leads remain reported.
- Supplemental `/tmp` `#print axioms` probe: all 71 new theorems use only the
  standard three or fewer.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0; existing exact
  comparisons remain green and all six new historical drift probes are caught.
- New-module forbidden-construct scan and `git diff --check`: clean.

No frozen data, registry, inventory or `paper/` is edited. An exploratory
unoptimized Boolean export was stopped; the final exporter uses independently
kernel-checked reductions and completes end to end.

Next: extract/bind the historical acquisition and target-only interpreter at
the polymorphic RawHandoff level, with shared cells and checked target execution
equations to the stronger lineage runtime. Then complete generic soundness,
the POS-04 adapters/controls and promotion. The distinction between historical
admissibility and funded-source lineage must remain explicit in that binding.
