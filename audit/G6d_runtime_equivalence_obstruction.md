# G6d: arbitrary-partial operational runtime equivalence obstruction

## Proved finding and stop boundary

The first requested gate is false for the committed
`POS04ResourceRuntime.model`: there is a partial assignment with committed `AO`
**true** and the new multi-resource operational game readout **false**. The
playbook's conflict rule stops the final assembly at this finding. TTH-06 stays
conditional; the positive lift and F/O game certificates remain valid.

New module:
`lean/CSTTT/Targets/GenericHandoff/POS04RuntimeEquivalenceBoundary.lean`.
Headline theorems (in its namespace):

```lean
operational_equivalence_counterexample :
  ∃ m : RawLaneModel, AO m ∧
    ¬ PackageRuntime.PostWithdrawalOperationalAutonomy
      (POS04ResourceRuntime.model (POS04ResourceRuntime.protocol m)) m.assignment

not_arbitrary_partial_operational_equivalence :
  ¬ (∀ m : RawLaneModel,
    PackageRuntime.PostWithdrawalOperationalAutonomy
      (POS04ResourceRuntime.model (POS04ResourceRuntime.protocol m)) m.assignment ↔ AO m)
```

These are (b) mathematical additions for TTH-06. No existing definition, theorem,
frozen declaration/result, registry entry or status changes.

## Exact diagnostic

`missingPastTicks` is `baseline` with only
`assignment := Assigned.put canonical (.ticks .target) none`.
Staging exchanges tags: the missing cell becomes **source** ticks in the
acquisition namespace, while the target response ticks remain available.
`staged_source_ticks_missing` proves the Option-level absence.
No history, row, receiver, resource, ledger, route or withdrawal metadata changes.
This is a diagnostic of the arbitrary-partial theorem, not a new pre-registered
positive model or a revision of a frozen prediction.

### Why committed O accepts

- `ComputedFIACH/Entries.lean:21` defines phase-2 dependencies, containing source
  rows and target ticks, but not source ticks.
- `Entries.lean:68` defines the autonomy dependencies, also without source ticks.
- `POS04OperationalGame.lean:15` uses their union. Supported source histories
  are checked against raw source action support; reception resets the probe-local
  ticks before the target response.
- `legacy_operational_check_unchanged` proves the entire AO computation is
  definitionally equal to the baseline computation, not merely sampled.
- `legacy_operational_game_accepts` and `legacy_named_operational_accepts`
  prove the accepted semantic game and named readout through the exact committed
  adapters. Thus the finding is not just a passing sufficient check.

### Why the new runtime rejects

- `POS04RouteExecution.lean:32` builds all five source/target run fields.
- `POS04RouteExecution.lean:39` selects their complete updater.
- `POS04RegisterDynamics.lean:47` reads the carrier's assigned tick table.
- `ResourceRuntime.lean:87` requires updater dependency completeness.
- `source_tick_is_consumed` derives membership in the actual instruction's
  dependency domain, not an extra handwritten scope.
- `runtime_games_reject` uses the generic `missing_update_no_games` theorem to
  reject both semantic games directly. There is no readiness assumption beside
  incompatible absence, and no inference from failure of a sufficient check.

`legacy_full_rejects` shows F also rejects this diagnostic because its package
requires every primitive. This witness disproves O equivalence **only**; F
arbitrary-partial equivalence remains unsettled.

## Argument and field coverage

| Object | Classification | Check / theorem |
|---|---|---|
| canonical assignment and metadata | existing raw data | unchanged committed definitions |
| one-cell deletion | raw transformation | `missingPastTicks` |
| staged assignment | defined object | `staged_source_ticks_missing` |
| frozen O computation | defined object | `legacy_operational_check_unchanged` |
| frozen game / named readout | derived evidence | committed exact adapters |
| updater dependency domain | defined from raw instructions | `source_tick_is_consumed` |
| missing updater input | computed absence | generic semantic rejection theorem |
| counterexample / universal negation | proved conclusions | headline theorems |

No supplied dynamics, observations, entries or game verdicts occur. The cell
transformation is also the per-field guard: this actual updater consumes source
ticks, whereas the frozen O semantics intentionally does not. No missing value
is replaced with a default in the proof.

## Repair before continuation

Do **not** add source-tick completeness to AO (a narrowing), use canonical
fallbacks, or present a readiness-restricted biconditional as the unrestricted
requested theorem.

The stronger repair is an O-specific acquisition interpretation with exactly its
live dependencies, preserving the shared raw execution semantics:

1. Define its acquisition projection from the shared instruction program. Retain
   factor support, activation, realization and provenance; discard only run
   components actually overwritten by reception.
2. Prove the receiver-reset/dependency elimination law for arbitrary partial
   assignments. Missing source ticks cannot affect the post-receiver entry;
   missing genuinely consumed rows, receiver, support or resources must reject.
3. Prove equality with full actual execution when its inputs are present and a
   partial-execution projection law when dead source readouts are absent. If a
   partial-register interpreter is needed, unknown values remain absent until
   the receiver writes its declared zero; absence is never a fallback.
4. Use that interpretation for O entries and prove both directions against AO.
   Complete lineage must still require source tick data and its closure-wide
   laws; it cannot inherit weaker O semantics.
5. Bind the other declared family checks (unit ledger, whole-domain ticks, P
   preservation, phase-2 branch coverage) before claiming either equivalence.
   The generic resource game is broader than those checks; canonical agreement
   is insufficient.

This is an interpreter/architecture repair, not a new model or contract
narrowing. It must be reviewed before the shared binding enters final RawHandoff.
The finding does not establish that generic TTH-06 is false; the current
arbitrary-partial runtime adapter is false.

## Remaining goals

The exact F/O adapters, complete shared generic lineage (including full actual
execution transport and Indexed/Retained route facts), final RawHandoff,
soundness, separation/dependence, controls, transcription and promotion gate
remain outstanding. No registry/inventory changes and no work on `paper/`.

## Verification

- `cd lean && lake build`: exit 0, 478 jobs; new module 5.4 s, final
  whole build 2.84 s. No new-module warnings; replayed existing linter warnings.
- `scripts/validate_lean.sh`: exit 0; inventory match, all 210 row declarations
  resolve, no untrusted axioms, zero placeholders/high-confidence vacuity.
- `#print axioms` on all ten new theorems: standard three or fewer.
- `python3 -B scripts/check_tth06_transcription.py`: passes, including all
  existing exact comparisons and planted drift probes.
- New-module forbidden-construct scan and `git diff --check`: clean.

Frozen CST-TT files, declarations, results, registry and inventory are unchanged.
