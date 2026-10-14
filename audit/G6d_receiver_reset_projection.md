# G6d: receiver-reset value projection and acquisition-support boundary

## Proved boundary; no promotion

The receiver-reset **value** projection is proved. The repaired O runtime game
and arbitrary-partial F/O adapters are **not** yet proved. TTH-06 remains
`conditional`; its registry and inventory are unchanged. The preceding
`POS04RuntimeEquivalenceBoundary` counterexample is retained as regression
evidence. This note adds no model declaration or frozen prediction.

New module: `lean/CSTTT/Targets/GenericHandoff/POS04ReceiverResetProjection.lean`.
Every name below is in that module's namespace.

## Exact reset projection

`retain x := (x.factor, x.residue)` retains the **actual** outcome, not a selected
predictive representative. `retainedStep` writes the actual outcome and retains
the raw history/event tuple. `retainedFold` iterates this instruction.
`receiveRetained` reads the assigned receiver through `Option.map`, and performs
the declared coordinate copy, counter/tick reset, and receiver funding write.
A missing receiver stays missing.

Proved:

- `actual_step_projects`: projection commutes with the actual updater.
- `actual_fold_projects`: projection commutes with execution for **all finite
  words**, by induction, without a bounded horizon.
- `receive_expression_projects`: the projection equals the existing receiver
  instruction evaluator.
- `checked_execution_reception_projects`: full **checked** execution followed
  by reception equals projected execution followed by reception whenever the
  full updater is defined.
- `supported_execution_reception_projects`: the same equation for every
  actually supported history.
- `receiver_missing_rejected`: the projection cannot replace a missing receiver
  with a default.
- `source_ticks_not_consumed`: deleting source ticks does not change the reset
  value.
- `canonical_projected_arrival_value` and
  `missing_past_ticks_projected_arrival_value`: both routes produce exactly the
  declared arrival value, including on the reported tick-deletion assignment.

These are instruction/value equations, **not** a new support gate or game
certificate. In particular the last theorem does not claim that the current
multi-resource runtime game now accepts `missingPastTicks`. That remaining
requirement is explicitly open.

### F and complete lineage separately

`missing_past_ticks_full_and_lineage_rejected` proves both rejections directly.
F requires the package primitive through the committed
`fullAutonomy_implies_package` theorem. Complete lineage retains the source tick
primitive for its source temporal interpretation and execution transport;
`POS04CompleteLineage.StrictTemporalLineage` requires completeness of
`POS04RouteExecution.dependencies`, which includes source ticks.
O's overwritten probe-local ticks are not evidence that this stronger source
run signature can be decoded without its tick table. Neither AF nor complete
lineage is weakened.

## Additional support discrepancy, with all cells present

Before computing the diagnostic, fix this one-field rule:
**disable pre-stage target recharge availability; preserve its canonical owner
and every other primitive and protocol field**. Staging turns this into disabled
**source** recharge. This defines `sourceRechargeUnavailable`.

The kernel proves:

1. `diagnostic_complete` / `diagnostic_ready`: every staged primitive is present,
   and the full acquisition interpreter is ready. This is not another
   missing-input/default example.
2. `diagnostic_owner_preserved`: both owners remain canonical.
3. `diagnostic_legacy_operational_unchanged`: frozen O's entire computation is
   definitionally equal to the baseline. `diagnostic_legacy_operational_accepts`
   and `diagnostic_legacy_operational_game_accepts` establish the accepted
   predicate and its committed semantic game.
4. `diagnostic_source_rows_empty`: every source-mode acquisition row is empty,
   for every run, disturbance, and action in the current shared runtime.
5. `diagnostic_no_source_history`, `diagnostic_no_arrival`, and
   `diagnostic_no_entry`: neither declared nonempty history can execute; there
   is no actual arrival or entry.
6. `diagnostic_runtime_no_games`: neither current runtime semantic game exists,
   directly from its nonempty-entry requirement.
7. `total_assignment_operational_obstruction`: a **total**, owner-preserving
   raw assignment has AO but not the current runtime operational game.
8. `diagnostic_support_preserving_projection_empty`: any proposed entry
   projection that preserves the current supported-entry semantics still has
   no entry here. Reset-value equality alone cannot provide supported arrival.

### Exact source of the discrepancy

- Frozen `G6_lane_spec.md:307–319` uses operational target viability; the shared
  entry construction validates source history with raw action support.
- `ComputedFIACH/Entries.lean:23–25` requires source rows but not source recharge
  or source ticks; `:39` uses `pathSupported` on those raw source rows.
- `GenericHandoff/POS04RouteExecution.lean:43–46` instead interprets
  `enabledRow .source` during acquisition.
- `POS04RegisterFuture.lean:17–22` disables that row when **source** recharge is
  unavailable. Reception cannot undo a disabled history branch.

This finding concerns the NEW runtime adapter, not a falsity finding about
generic TTH-06 or frozen AO. No claim of isolated package/lineage side effects is
made for this diagnostic, and it is not substituted for any registered control.

## Repair boundary and remaining work

Removing dead source-tick reads is sound for the receiver result. The O
acquisition interpreter must also distinguish the frozen **raw source-history
support check** from funded **target response execution**. It cannot reuse the
current funded source-row gate unchanged and claim arbitrary-partial AO
equivalence.

There are two different assertions to keep explicit:

1. Receiver-reset **values** agree whenever the full execution is defined:
   proved here, including on supported full histories.
2. Projected and current full **supported-entry relations** agree on all total
   assignments: false by the new diagnostic if projected O is to agree with AO.

Thus a faithful O acquisition repair needs an explicit support interpretation,
not just the omission of decoder dependencies. This is the next interpreter
seam; replacing the enabled source rows with raw history validation must be
disclosed as a semantic adapter correction. Do not strengthen AO, fill any
missing live primitive with a default, or infer a game from the pure fold.
The playbook conflict rule stops assembly before silently claiming the stronger
supported-execution equivalence. The pure/value projection is retained.

The O game repair, arbitrary-partial F/O equivalences, shared generic lineage,
RawHandoff soundness, separation/dependence, controls, transcription extension,
and promotion gate remain open. No narrowing or status change is applied.

## Argument and field coverage

| Object | Classification | Equation/check |
|---|---|---|
| shared assignment | raw data | existing staged assignment; missing receiver stays `none` |
| initial run, action/outcome word | execution inputs of the algebraic lemma | the checked/supported corollaries tie them to the full interpreter |
| retained factor/register, folds, reception | defined objects | `actual_step_projects`, `actual_fold_projects`, `receive_expression_projects` |
| full interpreter readiness | evidence on raw data | `Complete dependencies a`; not an independent dynamics argument |
| supported history | evidence on raw execution | `HistoryExecution`; used by the supported corollary |
| diagnostic resource change | raw transformation | one availability edit; owner-preservation and completeness proofs |
| proposed entries in the negative lemma | proposal, not accepted handoff data | support-preservation implication forces emptiness |

| Field | Reset value / support role | Coverage/guard |
|---|---|---|
| actual factor | retained; source support remains necessary | `actual_step_projects`; `diagnostic_no_source_history` |
| raw residue tuple | retained exactly | `actual_fold_projects` |
| source counter/progress | overwritten by reception | `checked_execution_reception_projects` |
| source ticks | overwritten for O; retained requirement for F/lineage | `source_ticks_not_consumed`; `missing_past_ticks_full_and_lineage_rejected` |
| source funding | overwritten VALUE; affects current enabled source support | `receive_expression_projects`; `diagnostic_source_rows_empty` |
| receiver rules/funding | assigned cell, not a fallback | `receiver_missing_rejected` |
| source recharge availability | live gate in current interpreter, absent from frozen O acquisition rule | `total_assignment_operational_obstruction` |
| target updates/resources | unchanged | existing actual-support and multi-resource proofs; no new equivalence claim |

No supplied observation, code, future dynamics, endpoint class, or autonomy
verdict enters a positive result in this seam.

## Statement changes and checks

All additions are **(b) mathematical** for TTH-06: reset-projection definitions,
their all-word equations, F/lineage regression, and the total-assignment support
counterexample. There are no (a) renames and no changed existing statements.

- Full `cd lean && lake build`: exit 0, 479 jobs; new projection module 6.1 s.
- `#print axioms`: all 34 theorems across the prior boundary and new projection
  modules use only the standard three or fewer.
- `python3 -B scripts/check_tth06_transcription.py`: passes, including existing
  exact comparisons and drift probes; no new interpreter transcription claimed.
- `scripts/validate_lean.sh`: exit 0, overall pass; all 210 registered names
  resolve with clean axioms and the inventory matches. TTH-06 is conditional.
- Forbidden-construct scan on both seam modules: no matches.
- `git diff --check`: clean; no frozen/registry/inventory changes or `paper/`
  edits.
- Byte comparison against committed `cst-tt/`: all 1,446 paths unchanged.

Reproduce:

```bash
cd lean && lake build
# From the repository root:
scripts/validate_lean.sh
python3 -B scripts/check_tth06_transcription.py
```

For the supplemental axiom check, a `/tmp` file imports `CSTTT` and runs
`#print axioms` on every theorem in `POS04RuntimeEquivalenceBoundary` and
`POS04ReceiverResetProjection`, through `cd lean && lake env lean /tmp/<probe>.lean`.
