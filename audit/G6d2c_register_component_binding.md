# G6d-2c: typed register component and exact POS-04 interpretation

## Proved boundary

This seam extracts instruction interpretation, temporal dynamics, readout laws,
and a priced operational-game component over arbitrary typed cells, dependent
registers, factor/action/disturbance/outcome types, and residue types. It also
proves exact POS-04 family interpretation. It does **not** yet assemble the
polymorphic `RawHandoff` or complete G6d-3 through G6d-6. TTH-06 remains
`conditional`; no registry, inventory, declaration, or existing theorem changes.
All new mathematical definitions/theorems are (b) component extraction for
TTH-06 and its C6/autonomy prerequisites. There are no (a) renames.

New modules under `lean/CSTTT/Targets/GenericHandoff/`:

| Module | Boundary |
|---|---|
| `RegisterInterpreter` | Immutable typed registers; raw expressions, dependencies, locality, missing-input rejection, simultaneous execution |
| `RegisterFuture` | Defined probabilities/updater/code/eight-field observer/closure; all-word induction from raw one-step equations |
| `RegisterReadoutLaws` | Nine independent step recipes, checked throughout nonempty computed closure; supported strict advancement; parameterized per-field guards |
| `RegisterOperational` | Raw row/resource/ownership/ledger/writer/advancement interpretation for a conserved priced ledger; game soundness |
| `GameReindex` | Exact bijective run representation transport of invariants and causal game readouts |
| `FutureReindex` | Exact all-word probability law and sufficiency transport through state/action maps and an injective observation representation |
| `POS04RegisterDynamics` | Register bijection with Run6; actual ambient successor and decoded raw-input equations |
| `POS04RegisterFuture` | Funded temporal rows, all eight readout equations, code/weight/updater links on all runs, actual and quotient word-law equality |
| `POS04RegisterReadoutLaws` | Actual POS-04 per-field update equations; nonempty-root gate on every accepted partial assignment; capped-progress rejection |
| `POS04RegisterOperational` | Exact operational row/update/resource/legal-response/advancement equivalences under the computed protocol, without hazards |
| `POS04RegisterGames` | Arbitrary-partial F/O game and named-readout equivalences; positive/control results and family TTH-05 transport |

## Raw binding, missing inputs, and dynamics

`Expr` has typed cell/register/environment reads, literals, pure operations,
pairs, and conditionals. Pure value operations are raw instructions, as in the
committed translation language; they may inspect unbounded values. No aggregate
updater, observer, code, or semantic predicate is a raw field. `choose` reads
both branches eagerly: a missing declared input cannot hide in an unchosen
branch. Static dependencies are structurally computed from the instruction.

`checkedExecute` and `read` are downstream total interpretation helpers with
proved dependency completeness. They select the unique value of a successful
Option evaluation; there is no missing-input default. `execute_present`,
`checked_execute_eq`, and `read_eq` bind them to the interpreter. The operational
row helper uses `[]` for an absent row, but its public certification requires
`Ready` first; missing rows cannot certify a response.

The POS-04 temporal row includes funded state, recharge availability and the
assigned budget/cost inequality, exactly as `actualRows6` does. Operational
rows are accompanied by the separate actual resource/legality gates. Both
updates write the **actual Ambient outcome**, not a predictive representative.
Duplicate raw destinations contribute their entire summed probability.

`POS04RegisterFuture.word_law` relates the new trace law to `actualFuture6` on
all runs. `quotient_word_law` uses the committed exact probability-lumping
argument to reach `future6`, under its existing `FiniteBisim6`. No stronger
`ActualBisim6` premise replaces C6 acceptance. `all_words` and
`accepted_full_interface` retain all-state and unbounded-word quantifiers.
The only interface representation change is the proved injective Tag-to-carrier
owner conversion. `strictly_coarser` transports the existing p0w0/p0w1 witness.

## Argument classification

| Argument/object | Classification | Binding/check |
|---|---|---|
| Cell, Value, Register, RegisterValue, factor/action/disturbance/outcome/readout types | Raw structural data | Independent types; no POS-04 types in the generic interpreter/component |
| Assignment | Raw data | One immutable partial typed namespace |
| Expr/Program, row, readout and resource instructions | Raw instruction data | Structural dependencies; same assignment and prior run; exact Option evaluation |
| Pure operation and explicit environment-read instructions | Raw instruction data | Ordinary value operations, not aggregate semantic predicates or future models |
| Numerical scales, declared lists, target ID, increment parameters | Raw component schema | Interpreted normalization, ownership, price and advancement checks; no generic unit price or carrier constant |
| Independent step-law recipes | Raw instruction data | All nine equations compared with actual interpreted updates on the whole computed closure |
| Ready/Complete, field laws, one-step bisimulation, lift equations | Evidence on raw data | Actual decoded instruction equations, not acceptance flags |
| Auxiliary game invariant and its response witness | Proof-bearing evidence | Existing strategy engine checks entries, package/resources, every disturbance and every supported successor |
| Observer, code, weights, updater, closure | Defined objects | `RegisterFuture.observation/future/dynamics` and the immutable program interpreter |
| POS-04 acquisition protocol, entries, package | Defined family objects, not yet generic | The committed ComputedFIACH interpreters read m; these are not supplied candidate arguments at `Full`/`Operational` |
| Engine-level entries/withdrawal/package arguments in transport lemmas | Internal interpreted relations | Not Raw fields; public family functions instantiate them with computed definitions; enclosing generic acquisition/package extraction remains pending |
| POS-04 encode/decode | Defined objects | Two-sided inverse theorems; no quotienting of actual support |

## Readout coverage and guards

All `FieldLaw` checks range over every state of `RegisterFuture.Closure`,
every declared disturbance/action, and every enumerated outcome. Positive
numeric RHS recipes are additionally checked on supported steps. The root,
action and disturbance domains are nonempty, outcomes are duplicate-free,
and the tick modulus is positive. The code is the fixed six-component
projection of the full eight-component observation.

| Readout | POS-04 independent RHS recipe | Generic law/guard |
|---|---|---|
| predictive | Compute raw predictive value of actual outcome from positions, rows and hazards | `field_laws .predictive`; `field_guard`/`constant_field_guard .predictive` |
| order counter | Old counter + 1 | `.order`; parameterized field guards; `supported_advancement` |
| ticks/phase | Old ticks + assigned delta; modulo the declared period | `.ticks`; parameterized field guards |
| progress | Old counter + 1, without a cap | `.progress`; parameterized guards; concrete `capped_progress_rejected` |
| writer | Same raw writer lookup on retained provenance | `.writer`; parameterized guards and missing RHS guard |
| endogenous record | (Old funded AND positive next budget) AND available writer, then old counter + 1 | `.record`; parameterized guards; supported advancement derived through the update equation |
| route residue | Retain raw history/event tuple | `.residue`; parameterized field guards |
| maintenance | Old funded AND positive computed next budget | `.maintenance`; parameterized field guards |
| owner | Read the same assigned resource owner | `.owner`; parameterized field guards |

`constant_field_guard` changes just the chosen readout instruction; weights,
program, roots and independent RHS recipes stay fixed. Its mismatch premise
names a reached state and a distinct wrong value. It is parameterized over all
nine fields, not an exhaustive finite mutation enumeration. The concrete cap
probe reaches counter 2, whose next raw progress is 3 while the proposal emits
2, and proves rejection on both tags. `field_laws` holds on every run;
`readout_gate` holds throughout the computed closure for every `C6Accept`
assignment. The latter derives funded writer retention and positive supported
tick/record advancement, rather than supplying them as fields.

| Raw component field | Check | Guard |
|---|---|---|
| Every consumed static cell | Structural dependency completeness | `Expr.missing`, `missing_program_rejected`, `missing_row_rejected`, `missing_readout_rejected`, `missing_rhs_guard` |
| Every update register | Option instruction equation | `execute_missing`, `checked_execute_eq`, `missing_update_rejected` |
| Temporal row | Exact enabled assigned row and probability summation | `enabled_row_eval`, `row_eq`, `weight_eq`; missing row guard |
| Each temporal field recipe | Exact all-closure update equation | Parameterized `field_guard`, `constant_field_guard`; capped-progress instance |
| Closure roots | Nonempty derived audited roots in the family | `roots_nonempty`, `empty_roots_rejected` |
| Finance ownership/price/recharge | Actual decoded ledger checks | `finance_eval`, `resource_iff`, `missing_resource_rejected`; existing owner/ledger/resource guards transfer through `operational_iff_game` |
| Response rows and domains | Legal normalized all-support raw rows, nonempty declared disturbances | `rows_eq`, `legal_iff`, `empty_disturbance_rejected` |
| Solvency/record/order/tick/provenance | Computed successor checks | `step_iff`; existing step guards transfer by exact game equivalence |
| O dependency scope | Exactly acquisition and operational inputs | `no_hazard_dependency`; `missing_hazard_operational` versus `missing_hazard_full`; `missing_dependency_rejected` |

## Exact family games and controls

For **every partial** `m : ComputedFIACH.RawLaneModel`:

- `Operational m ↔ POS04OperationalGame.Autonomy m ↔ AO m`;
- `Full m ↔ POS04FullGame.Autonomy m ↔ AF m`;
- both also equal their named post-withdrawal readouts;
- `Full m → PackageLane m.assignment`;
- `full_each_entry_exact_autonomy` transports the committed genuine
  TTH-05 certificate for every derived phase-2 entry.

`positive` supplies both games. `control_vectors` preserves the registered
package-deletion (F false/O true), lineage-deletion (both autonomy lanes true),
and withdrawal-deletion (both false) outcomes. Missing hazards leave O true and
F false. These are consequences of exact kernel/representation equivalence,
not merely equality of canonical truth values. Full three-lane vectors still
use the committed family package and lineage; generic versions await extraction.

## Remaining boundary, in plan order

1. This is a **component seam**, not a complete `RawHandoff` binding. The
   operational component currently interprets one conserved priced ledger,
   with arbitrary schema prices/increments. It is a sound specialization,
   **not** a replacement for the hybrid architecture's unrestricted resource
   and run-context recipes. Extract the general resource/withdrawal bundle
   and connect interpreted components at the enclosing raw interface. Do not
   promote from this one-ledger constructor or impose conservation generically.
2. Extract the package rule aggregator from all eight generic raw schemas,
   including the remaining enclosing temporal gate/finite-factor connection;
   construct it through arbitrary typed stages and covers (G6d-3).
3. Derive acquisition entries and the G4/G1c lanes from the same generic
   assigned cells (G6d-4a/4b). The family protocol/entries in this seam are
   reused definitions and remain visibly family-specific.
4. Extract the generic finite constructor's exact-lift proofs and TTH-05
   transport (G6d-5). No finite-context irrelevance is assumed here. Existing
   actual-support lift and game-invariant theorems remain the per-instance
   proof obligations and reused POS-04 proofs.
5. Only then assemble the generic F/O RawHandoff certificates, named lane
   separation, full instance/control equivalences and transcription, and
   reconsider the TTH-06 registry promotion (G6d-6).

There is no new finite-context assumption, no new model declaration/evaluation,
and no weakening of AO or AF. The priced-ledger and family boundaries above are
open implementation work, not narrowing proposals.

## Checks

- `cd lean && lake build`: exit 0, 404 jobs, 4.21 seconds for the final
  incremental build; no warnings from the new modules. Existing vendor and
  `Targets/Composition` / `Prospects/Statements` linter warnings remain.
- `scripts/validate_lean.sh`: exit 0, OVERALL pass; no gating source findings.
- Read-only `/tmp/G6dRegisterAxioms.lean` probes: all 101 new public theorems
  resolve, with only `propext`, `Quot.sound`, `Classical.choice`, or fewer.
- Forbidden-construct scan of the eleven new modules: no matches.
- `git diff --check`: clean; `cst-tt/` and the row inventory have no diff.
- All changes remain uncommitted. The unrelated `paper/` tree is untouched.
