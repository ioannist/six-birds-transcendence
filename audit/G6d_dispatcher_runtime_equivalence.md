# G6d: exact dispatcher equivalence and C6 runtime soundness

## Proved boundary

This seam completes the arbitrary-partial dispatcher equivalences and binds the
finite C6 constructor to its actual runtime. TTH-06 remains **conditional**.
There is no registry, inventory, declaration-model, or paper change.

`POS04Dispatcher.clause_accept_iff a tag k` is a biconditional for **every partial
assignment**, both tags, and all eight clause kinds. `package_accept_iff` gives
the eight-clause biconditional. `p_iff` and `p_engine_iff` identify the staged P
with ComputedFIACH and the committed constructive gluing engine, respectively.
`constructs` exports restriction equality, global completeness, and closed
**dispatcher** acceptance of that constructed global. `positive` and
`deletion_failure` supply a genuine instance and direct missing-primitive failure;
`package_control_failure` transfers all declared package-breaking adapters.

| Clause | Exact equivalence used | Completion in this seam |
|---|---|---|
| C1 | `POS04ObjecthoodReference.generic_c1_iff` | Existing checked fixed-point/protocol equivalence |
| C2 | `POS04ProfileRules.generic_c2_iff` | Existing raw promotion equivalence |
| C3 | `generic_c3_iff`, `accepted_completion` | Genuine normalized partition fixed point and support-block coverage derived for arbitrary accepted assignments |
| C4 | `POS04Exposure.generic_c4_iff` | Existing surrogate equivalence |
| C5 | `POS04ProtocolCredit.generic_c5_iff` | Existing surrogate equivalence |
| C6 | `POS04TemporalFactor.generic_c6_iff` | Complete decoder, trace, funding, finite bisimulation, and strict merge equivalences |
| C7 | `POS04Joint.generic_c7_iff` | Existing operational/transport surrogate equivalence |
| C8 | `POS04OperationalViability.dispatcher_c8_iff` | Extra dispatcher row check proved equivalent, including arbitrary missing inputs |

### C3 completion

`ProfileRules.normalized_adjacent_fixed` proves that first-occurrence class
numbering turns adjacent partition agreement **after a refinement** into an exact
fixed point. `POS04ProfileRules.genuine_stabilization` applies this at POS-04's
positive depth; `support_blocks` proves coverage of active and external outcome
blocks for arbitrary raw inputs. The depth-zero counterexample is not erased:
no general claim that unnormalized adjacent agreement implies stabilization is
made. The extra dispatcher completion is derived from legacy acceptance, not a
new assumption on assignments.

## C6: actual branches and unbounded words

`TemporalFactorRules.future`, `actualRows`, `weight`, `update`, `roots`, and
`Closure` are defined from raw primitives. Outcomes remain actual factor outcomes;
no predictive representative replaces a branch. Repeated destinations in raw
rows have their probabilities summed exactly as rationals.

`predictive_fiber` proves the actual-support probability regrouping equation.
`one_step` proves equal one-step observations and equal next-code fiber masses.
Successor-code alignment is derived from the checked raw tick equation
(`successor_code_alignment`), not assumed as a flag. `all_words` then uses the
committed word induction. Its quantifier covers **all run states and all finite
words**, not just a bounded horizon or only the root closure.

`ClauseDispatcher.c6_runtime_soundness` exports, from dispatched C6 acceptance:

- the uniquely decoded raw inputs and their acceptance;
- all-state full-interface future sufficiency;
- closure-wide readout update laws;
- two distinct actual roots with equal code, so the closure is nonempty;
- positive conserved funding, strict progress, and record advancement throughout
  the computed closure.

For arbitrary partial POS-04 assignments, `code_eq`, `observation_eq`, `weight_eq`,
and `updater_eq` equate the generic constructor with `actualFuture6` on **all**
runs, actions, and actual outcomes. `word_law` equates the full probability law
for every finite word through an injective eight-component observation encoding.
`accepted_all_words` transfers the **generic** induction through these equations.
`accepted_register_laws` also binds acceptance to the existing shared-register
interpreter's independent recipes over its whole computed closure. The former
outcome-enumeration ordering difference is handled by actual-outcome regrouping;
no branch or observation component is dropped.

## Argument classification

| Argument | Classification | Binding/check |
|---|---|---|
| Carrier/action/outcome/history/route/stage/event/owner types and equality instances | Raw interface | No cardinality or POS-04 family is fixed by the generic constructor |
| Schema enumerations, destination map, scale, policy reference, coarse pair, stage advance | Raw data | Domain coverage/distinctness, reference reconstruction, positivity, trace, and coarseness gates |
| Typed cell bindings and immutable partial assignment | Raw data | Sixteen-input Option decoder; every consumed cell must be present |
| Raw decoded tables, hazards, positions, policy, ticks, ledger/resources, histories/events/routes/writers | Defined extraction of assigned raw data | Decoder equation, row/reference/trace/funding/bisimulation checks |
| Acceptance proofs | Evidence on raw checks | No stored future or lane verdict is unpacked |
| Future, code, observer, weights, successor, roots, closure | Defined objects | Not theorem inputs; constructed from the decoded primitives |
| Period | Raw observation parameter | Constructor theorem applies to any period; POS-04 specialization fixes its declared period 2 |
| POS-04 run/readout embedding | Defined object | Inverses and exact equations, no candidate runtime is supplied |
| Altered expression and readiness in the guard theorem | Proposed defective object and evidence on its dependencies | Used only to prove rejection by an independent recipe, never as a certified future |

## Readout coverage

`TemporalFactorRules.UpdateLaws` and `closure_laws` cover every row below on the
whole actual computed closure. The POS-04 register gate is additionally derived
by `accepted_register_laws`. `constant_readout_guard` is parameterized over each
`RegisterFuture.Field`: at a genuine closure state, a replacement constant that
differs from the independently computed recipe is rejected. A constant owner is
lawful when it equals the declared owner; the guard requires an actual mismatch.

| Readout | Defined update law | Guard |
|---|---|---|
| Actual factor | Next factor is the actual outcome | `updater_eq`; no supplied successor; `update_proposal_guard` at projection `Run.factor` |
| Predictive | Recompute prediction from that outcome's raw support | `constant_readout_guard` at `.predictive` |
| Event order/counter | Add independently declared positive stage advance | field guard `.order` |
| Tick phase | Add raw action delta, then reduce modulo period | field guard `.ticks`; existing `tick_alignment_rejected` |
| Genuine progress | Counter plus positive stage advance | field guard `.progress`; `capped_progress_guard` |
| Writer availability | Re-evaluate raw route writer; retained residue preserves it | field guard `.writer`; record-negative adapter |
| Endogenous record | Funded writer advances record by stage advance | field guard `.record`; `accepted_advancement` |
| Route residue | Retain the raw history/event tuple | field guard `.residue` |
| Maintenance | Next funding follows actual conserved ledger | field guard `.maintenance`; `zero_ledger_guard` |
| Owner | Declared resource owner preserved | field guard `.owner` |
| Enabled response | Next funding, recharge availability, and affordability | `update_proposal_guard` at projection `enabled`; `zero_ledger_guard` |

The nine named register-field guards use the actual `RegisterFuture.Field`
constructors. Factor and enabled are updater projections, not register readout
constructors; their proposal guard rejects closure-wide updater equality at a
genuine mismatching state.
The finite constructor's laws are structural equations of its **defined**
updater; arbitrary candidate capped readouts cannot be supplied to that updater.
The register guard additionally demonstrates rejection of expressible proposals
by the independent update-law interpreter.

## Primitive coverage and controls

| Primitive family | Raw check | Rejection/transfer evidence |
|---|---|---|
| Rows, positions, hazards, policy, class labels, published P | Row validity and reference reconstruction; computed prediction/bisimulation | `Rule.missing_rejected`, `class_mass_rejected`, `per_tag_controls` |
| Tick deltas | Checked same-class delta equation | `tick_alignment_rejected`; actual `delta_eq` |
| Resource and ledger | Correct owner, availability, unit ledger, positive conserved funding | `zero_ledger_guard`; `generic_c6_iff` |
| Eight-component interface | Exact declared interface, injective readout image | `interface_iff`, `observation_eq`, decoder missing guard |
| Histories, events, realized stages, routes | Supported, strict realized paths and route tuples | `per_tag_controls` includes rejection of unrealized mix on both tags |
| Receiver funding and writers | Funded realized trace and writer availability | Missing-input guards; record-negative rejection |
| Cover, stage, source assignment | Committed checked dependent gluing and raw map laws | `constructs`, `deletion_failure`, `package_control_failure` |

`per_tag_controls` preserves the exact M3b C6 outcomes: positive passes both tags;
future-break and record-break pass source and fail target; unrealized mix fails
both. Every equivalence is arbitrary-partial, so all existing clause controls
transfer, including controls under which C3 remains accepted. Missing values
cannot use decoder defaults to support new acceptance.

## Scope and changes

All additions are **(b) mathematical additions for TTH-06**: exact decoder/rule
biconditionals, derived C3 completion, actual-support full-word induction,
closure/nonemptiness/advancement consequences, package construction readout, and
controls. No existing theorem, clause definition, model, or row statement is
changed; there are no (a) renames or new hypotheses on the POS-04 family.

The finite temporal constructor is sound, potentially incomplete for unrestricted
raw run-context recipes. This seam does not assert a universal finite-factor lift
for those recipes. Their per-instance lifting proof remains required by the
adopted hybrid architecture.

## Not yet proved / next boundary

1. Generic G4 corridor and G1c bridge construction from the **same generic runtime
   cells**, with exact arbitrary-partial POS-04 equivalences and a direct missing
   atomic-witness negative. Existing ComputedFIACH adapters are family-specific.
2. TTH-05 certificate transport from that generic runtime game readout.
3. The enclosing RawHandoff F/O soundness, named-readout separation/dependence,
   instance/control transcription, and the registry promotion gate.

The package and C6 boundary is fully proved; it does not discharge these remaining
handoff obligations. TTH-06 remains conditional, without narrowing its row.

## Verification

- `cd lean && lake build`: exit 0, 433 jobs, final incremental run 7.24 s.
  No warnings in the nine new modules; existing CSTTT/vendor warnings replay.
- `scripts/validate_lean.sh`: exit 0; 39 rows and 210 registered declarations
  resolve, no untrusted axioms, no placeholders or high-confidence vacuity
  findings. Thirty existing ignored-input heuristic leads remain non-gating.
- `/tmp/g6d-runtime-axioms.lean` through `lake env lean`: all 77 new public
  theorem names resolve, with `#print axioms` using only `propext`, `Quot.sound`,
  and `Classical.choice` or fewer.
- Forbidden-construct grep on the new modules: no matches. `git diff --check`
  passes. CST-TT files and the row inventory are unchanged; `paper/` untouched.

### Files added

Under `lean/CSTTT/Targets/GenericHandoff/`:
`ProfileNormalization.lean`, `POS04ProfileCompletion.lean`,
`POS04OperationalCompletion.lean`, `POS04TemporalEquivalence.lean`,
`POS04DispatcherEquivalence.lean`, `TemporalFactorWords.lean`,
`TemporalFactorClosure.lean`, `POS04TemporalRuntime.lean`, and
`TemporalDispatcherSoundness.lean`. The root `lean/CSTTT.lean` imports them;
this note is the only new audit file. All changes are uncommitted.
