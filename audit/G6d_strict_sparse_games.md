# G6d: StrictSparse historical games and whole AF/AO equivalence

## Proved boundary

This seam implements the manager's Resolution in
`audit/G6d_zero_support_obstruction.md`. The chosen repair is **(b),
representation-sensitive selected-response legality**, for TTH-06. The old
positive-support games, frozen AF/AO, all declaration JSON, and all recorded
results remain unchanged. No duplicate-freedom or ordering condition is added.

In `CSTTT.TargetTheory.GenericHandoff.StrictSparseGame`:

```lean
StrictSparse row := ∀ e ∈ row, 0 < e.2
Legal rows legal r d a := legal r d a ∧ StrictSparse (rows r d a)
```

`Readout` is the committed causal strategy game with that legal-response
predicate. `selected_sparse` checks only the strategy's selected action, for
every disturbance at every generated play. Normalization and successor plays
continue to use actual positive support. `SupportOnlyReadout` identifies the old
readout, and `implies_support_only` forgets only the format obligation.
`null_at_entry_no_game` directly refutes the named readout when every possible
selected response at a genuine entry has a null entry. Empty responses fail
normalization. `perm_iff` proves the format check ignores row ordering;
`duplicate_positive` proves positive duplicate entries are not excluded.

The historical raw runtime defines F/O rows, updater, entry relation, package,
resources, legality and advancement from the same assignment. Its new
`SparseFullAutonomy` and `SparseOperationalAutonomy` use this format gate.
Their soundness is still derived by induction over causal strategy plays.
The unchanged support-only historical readouts are separate named definitions.

### Whole arbitrary-partial adapters

In `POS04HistoricalSparseEquivalence`, with no assignment restriction:

```lean
full_iff_af (m : RawLaneModel) : FullAutonomy m ↔ AF m
operational_iff_ao (m : RawLaneModel) : OperationalAutonomy m ↔ AO m
```

The two left-hand sides include the **computed** nominal protocol interpreter
and the corresponding generic historical runtime game. They do not accept a
protocol verdict argument. `protocol_failure` proves both sides reject whenever
that interpreter does not return `some true`, including missing consumed
inputs. `missing_protocol_dependency` covers every frozen phase-2 dependency;
`missing_package_primitive` additionally rejects any absent primitive in F.

The converse is substantive: `toLegacy` reconstructs a finite response invariant
from an arbitrary raw run-space invariant. Every successor in positive support
is preserved. `SparseScaledRows.closed_iff` derives finite row closure from
strict positivity, normalization, and all-support invariant safety. Resource
legality alone never supplies row closure. `toRaw` proves the converse invariant
transport, including actual updates and ledger/counter/tick/record laws.

Every use of `response_rows_eq` is at a run proved `ResourceClosed` by the
invariant. The theorem is not applied at unfunded contexts. A selected row's
nonemptiness is derived from normalization/finite closure; `raw_step` derives
solvency and advancement from the interpreted unit ledger, tick and writer
checks and the actual updater. No safe row or step law is supplied as a flag.

## Representation regressions

Rules are declared before their kernel checks in `POS04SparseRegressions`.
Only reached target rows at `p2w1` change; the assignment edit is in the source
namespace before staging. The inside null appends `(p1w0,0)`; the outside null
reuses the committed append of `(p2w0,0)`. Empty erases these responses.
Duplicate splits a weight `n>1` into `1` and `n-1` on the **same outcome**.
Permutation reverses these lists. The raw rule and predicate are fixed across
all cases. No new prices or thresholds are chosen.

| Raw edit | Format-qualified F | Format-qualified O | Evidence |
|---|---|---|---|
| Baseline | holds | holds | `baseline_full`, `baseline_operational` |
| Zero listed entry, inside K | fails | fails | `zero_full_rejected`, `zero_inside_rejected` |
| Zero listed entry, outside K | fails | fails | `zero_full_rejected`, `zero_outside_rejected` |
| Empty responses | fails | fails | `empty_rejected`, `empty_protocol_rejected` |
| Split into duplicate positive entries | holds | holds | `duplicate_full`, `duplicate_operational` |
| Row permutation | holds | holds | `permuted_full`, `permuted_operational` |

F's positive duplicate/permutation cases separately check the actual assigned
package and reconstruct a full invariant using `operational_and_package_full`.
They are not inferred from format validity or O alone. The entire package
schema is not claimed invariant under arbitrary representation edits.

`representation_sensitive_separation` retains the old obstruction: the outside
zero diagnostic **does** satisfy the support-only O game but **does not** satisfy
the new format-qualified O game. This is a representation distinction, not loss
of a stochastic support branch. The old counterexample remains true.

## Complete family binding and controls

`POS04HistoricalSparseFIACH` gives exact F/O family-gate equivalences with the
committed `POS04HistoricalFIACH` for arbitrary partial assignments. Its soundness
derives P from the package subcheck, L from `POS04CompleteLineage.Valid`, and A
from its own computed protocol and StrictSparse game. It does not infer the
complete lineage from the weaker legacy lineage predicate.

The direct **named-readout** vectors are:

| Control | P | Complete L | Sparse F | Sparse O |
|---|---|---|---|---|
| Package deletion | false | true | false | true |
| Lineage deletion | true | false | true | true |
| Post-exit withdrawal deletion | true | true | false | false |
| Relabeling/execution-transport diagnostic | true | false | true | true |
| Missing source recharge during recorded acquisition | true | false | true | true |

`F_control_vectors`, `O_control_vectors`, `operational_named_separation`,
`relabel_vectors` and `source_recharge_diagnostic` prove these readout outcomes,
including direct negative conclusions. `missing_past_ticks_diagnostic` records
F rejection and O acceptance; F consumes those package primitives, while O's
receiver-reset/historical execution does not. `duplicate_event_operational`
retains the all-matching-record activation regression.

The lineage in these family theorems is the already committed complete semantic
readout: funded actual source execution, corridor, four-snapshot bridge,
endpoint, complete execution transport and **Indexed/Retained** route comparison.
It is not replaced with `ExecutedMemory`. No new generic lineage equivalence is
claimed by these wrappers.

## TTH-05 and dependence

`HistoricalFiniteAutonomy.sparse_full_each_entry_exact` and
`sparse_full_each_entry_words` transport the format-qualified generic raw game
to TTH-05 for **every genuine entry** and every finite declared disturbance word.
The primitive/resource/ownership and support lifting obligations remain explicit
proved instance evidence. Forgetting StrictSparse leaves the same rows, updater,
package, entries, withdrawal and support; it does not assume forgotten run
context is irrelevant.

`HistoricalPackageRuntime.sparse_full_implies_package` proves generic AF ⇒ P
at a genuine entry. `POS04HistoricalSparseFIACH.full_dependence` exposes the same
consequence on the family's integrated-realization readout. Neither consequence
is used as the separate package soundness derivation.

## Argument classification

| Argument/object | Classification and origin |
|---|---|
| Polymorphic `HistoricalPackageRuntime.Raw` | Raw typed interface, stage/cover, dispatcher rules, histories, receiver, resource/withdrawal/update instructions; existing interpreter |
| Source assignment | Raw immutable partial assignment; shared references and missingness preserved by staging |
| POS-04 `RawLaneModel m` | Raw assignment plus withdrawal metadata; no assigned result fields |
| Nominal protocol | Defined eager interpreter from the same staged cells/metadata, not supplied |
| Rows, scaled probabilities, entry relation, updater | Defined from raw acquisition/resource instructions |
| F package / O factor safety | Defined raw interpreter; the internal Bool version selector chooses only F or O |
| Code, observations, complete lineage | Existing defined raw execution objects; not new candidate arguments |
| Ready/resource/protocol proofs | Evidence on raw data; never manufacture missing input |
| Auxiliary invariant and response selector | Constructed proof witnesses; all obligations checked against defined rows/updater |
| `toRaw` / `toLegacy` certificates | Constructed invariant proofs, not stored game readouts |
| TTH-05 `Checked` / `Lift` | Explicit proved per-instance lifting laws, including every response/resource context |
| Package hypotheses in regression helper | Evidence on independently computed assigned package, not freely chosen predicates |

`StrictSparseGame` itself is an interpretation-parametric proof engine. Its
abstract component predicates are not the final raw binding; its historical
specialization binds them to the existing explicit raw interpreters. The final
polymorphic shared-lineage/RawHandoff assembly remains to be done.

## Field/readout coverage and guards

| Raw field/readout | Check/law used | Guard or regression |
|---|---|---|
| Every listed selected-row weight | Defined StrictSparse, exact scale-four `closed_iff` | `zero_entry_rejected`, `null_at_entry_no_game`, both zero regressions |
| Selected-row mass and support | Normalized, `mass_iff`, all-support invariant preservation | `empty_not_normalized`, `empty_rejected`; duplicate positive regression |
| Row order | No order gate; StrictSparse permutation equivalence | `perm_iff`, `permuted_full`, `permuted_operational` |
| Source history rows, receiver and phase-2 acquisition cells | Computed nominal protocol and existing eager historical readiness/entry laws | `missing_protocol_dependency`, duplicate-event and source-recharge diagnostics |
| Target response rows | `response_rows_eq` under invariant resource closure | `row_closed_iff`, zeros/empty/duplicates/permutation |
| Actual factor successor | `update_eq` and every positive-support response branch | `toRaw.response`, `toLegacy.response`; no representative choice |
| Budget/account/resource ownership | `resource_closed_iff`, `accounts_eval`, `charge_eval`, unit protocol equations | `protocol_failure`; withdrawal named-readout controls |
| Event counter/order and progress | Actual updater and `step_preserves` | `raw_step`; existing committed resource/execution law guards retained |
| Tick | Assigned tick, nonempty selected row ⇒ `protocol_tick` | `raw_step`; protocol-failure rejection |
| Record and writer availability | Assigned writer plus conserved funding and actual update | `raw_step`, `record_eval`; missing protocol guard |
| Residue and route register | Exact updater; every support branch retains residue | `update_eq`, `step_preserves`; complete family route readout unchanged |
| Maintenance and owner | Target-owned resource closure through every play | `resourcesInside`, `raw_step`; withdrawal control |
| Same-package primitives at each run | Assigned dispatcher on actual run assignment; exact `package_iff` | `missing_package_primitive`, package-deletion F negative |
| Post-withdrawal absence/retention | Computed raw withdrawal metadata and ownership legality | `protocol_failure`, F/O withdrawal vectors |
| Acquisition semantics versus complete lineage | Historical raw support for autonomy; funded actual execution for L | Source-recharge and missing-past-tick diagnostics; relabeling vector |

No new primitive-cell family or readout recipe is introduced. Existing generic
closure-law and missing-input guards remain in force; only selected-row strict
positivity is new. These are sensitivity/semantic controls, not a claim that
an exhaustive isolation test was performed for every old clause field.

## Remaining promotion gate

**TTH-06 remains `conditional`.** This seam completes the two whole arbitrary-
partial AF/AO adapters and their controls. It also carries the complete family
lineage unchanged into the StrictSparse family assembly and gives generic
TTH-05 transport. It does **not** yet provide the complete shared polymorphic
lineage binding or the final `RawHandoff` value/theorems. Those are the next
proved boundary, not a newly discovered impossibility.

Still required: generic complete lineage from the runtime execution and shared
component instructions (including Indexed/Retained), its exact POS-04 instance,
then final RawHandoff F/O soundness, O separation, transcription extension and
registry gate. No narrowed row text or premature promotion is applied.

The eventual ceiling must disclose finite typed raw interfaces, nominal
all-support robustness, C4–C7 surrogate content, AF ⇒ P with F proof-structural
separation, supplementary O independence, **historical-support acquisition for
autonomy versus funded actual acquisition for lineage**, and the adopted
**representation-sensitive StrictSparse** qualifier. This is not a stronger
stochastic-autonomy claim.

## Statement changes

| Class | Row | Change |
|---|---|---|
| (b) | TTH-06 | Add selected-response StrictSparse legality and named format-qualified generic F/O games, per manager Resolution; support-only definitions unchanged |
| (b) | TTH-06 | Add exact arbitrary-partial format-qualified AF/AO biconditionals and protocol/missing-input rejection |
| (b) | TTH-06 / TTH-05 reuse | Add generic exact-certificate and all-word transport by forgetting only the format qualifier, with proved lifting laws |
| (b) | TTH-06 | Add family soundness/control transfer and representation regressions; no new generic promotion claim |

(a): none. Existing theorem/definition statements are unchanged. Imports expose
the new declarations. No registry/inventory, frozen model, evaluation result,
CST-TT-08 or paper file is changed.

## Checks

- `cd lean && lake build`: exit 0, 506 jobs, 69.57 s. The expanded
  representation-regression module built in 66 s; generic equivalence and
  family assembly modules built in 5.0 s and 4.5 s. Existing vendor/core linter
  warnings replayed; no new-module build warnings.
- `scripts/validate_lean.sh`: exit 0; 39 rows, 210 declaration entries /
  209 unique declarations. Zero placeholders, high-confidence vacuity findings,
  untrusted axioms or issues. Forty non-gating heuristic leads remain. One new
  lead is `POS04SparseRegressions.lean:26`, the intentional `fun _ => []`
  empty-response control, whose named games are proved false.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0 at its unchanged
  documented coverage, with its existing planted-drift checks. This is the
  legacy/family regression; no final generic transcription extension is claimed.
- `/tmp` `lake env lean` probes: all **72** new theorem names resolve;
  `#print axioms` shows only `propext`, `Quot.sound`, `Classical.choice` or fewer.
- Whole-CSTTT forbidden-construct search and `git diff --check`: clean.
  No changes to registry, inventory, CST-TT-08, declaration/evaluation files,
  or `paper/`. Work is uncommitted.

Self-review (mathematics-proof-review): reconstructed both directions through
actual entries, package/context equivalence, resource-closed row transport,
actual update equations, strict positivity and all-support invariant safety.
The converse recovers every listed-row closure obligation from those laws; it
never infers successor safety from resource legality. The invariant is inhabited
by the baseline and its entries; zero and empty controls directly refute named
readouts. The duplicated/permuted F cases separately prove assigned package
acceptance. Historical/support-only, format-qualified, legacy lineage and
complete lineage are not conflated. The final polymorphic target remains
explicitly incomplete; there is no new equivalence obstruction or silent
narrowing.

Reproduce:

```bash
cd lean && lake build
# Repository root:
scripts/validate_lean.sh
python3 -B scripts/check_tth06_transcription.py
```

Headline theorem probes (through a `/tmp` file importing `CSTTT`):

```lean
#check CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseEquivalence.full_iff_af
#check CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseEquivalence.operational_iff_ao
#check CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseEquivalence.protocol_failure
#check CSTTT.TargetTheory.GenericHandoff.POS04SparseRegressions.full_and_operational_regression_vectors
#check CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseFIACH.operational_named_separation
#print axioms CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseEquivalence.full_iff_af
#print axioms CSTTT.TargetTheory.GenericHandoff.POS04HistoricalSparseEquivalence.operational_iff_ao
```
