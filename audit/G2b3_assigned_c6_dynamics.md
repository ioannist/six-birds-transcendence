# G2b-3 — assigned C6 dynamics and closure seam

## Scope and completion boundary

This packet takes the explicitly authorized natural split: **defined dynamics
and closure first; sufficiency, acceptance, equivalence and controls next**.
The new modules implement the assignment-owned substrate of C6 and its full
readout equations. They do **not** assert an assigned C6 acceptance theorem,
a bisimulation, or an all-word sufficiency result. TTH-02 remains conditional;
registry, inventory, frozen model/spec/predictions, and existing clauses are
unchanged.

Authority: frozen `audit/M3_model_spec.md:22,30–33`; L6a
`lean/CSTTT/POS04/C6.lean:120–130,163–209,224–273,370–397`; G1b
`POS04/FullFutureBridge.lean:14–43`; G1c `POS04/RawRunDynamics.lean:21–45`
and `Transport/FutureDynamics.lean:10–24`. The readout guard method follows
`Transport/RawBridge.lean:238–335` and `POS04/ReadoutGuards.lean`.

All new definitions/theorems are **(b) mathematical**, supporting TTH-02's
assignment-sensitive C6 clause, at its existing surrogate ceiling. There is no
T18/NOTCH upgrade, full P05 package or T17-I claim.

### Changed files

- New `Assigned/C6Dynamics.lean`: scoped raw decoding, exact class images and
  representative choice, exact action-row pushforward, run lift, full observer,
  code, finite roots and unbounded closure; locality and component update laws.
- New `Assigned/C6DynamicsLinks.lean`: canonical class/M, observer/code,
  weight/successor links to L6a and G1b/G1c; nonempty merged roots and a supported
  three-step closure witness.
- New `Assigned/C6ReadoutGuards.lean`: typed per-field proposal equality on the
  entire closure; constant/cap guards for every readout; closure ledger evidence.
- `CSTTT.lean`: imports the guards module.
- This audit note.

No new primitive cell, raw scientific value, threshold, model or mutation is
introduced. Source values come from the existing canonical assignment. The
method cap two is the existing G1c audited endpoint bound; the three-step
witness is computed from actual T1 responses, not fabricated evidence.

## Defined object chain

Namespace: `CSTTT.POS04.Assigned`.

`runInputs6 a tag` decodes the existing C6 scope, reading the actual action
rows/positions/hazards, tick table, resources/ledger, histories/routes/writers,
receiver/event/realization data and declared interface through shared cells.
Its `ExtraInputs` and the other fields are defined records, not theorem inputs
supplying derived functions. Unused extra fields remain for the next trace gate.

### Classes and probabilities

`predictive6 d (.inK s)` is `.active (predictive d.base.base s)` using assigned
public positions and assigned action-support hazard profiles. Ambient exits
have the two fixed typed exit values. No imported M label determines classes.

`representatives6` retains exactly the first state in `ambientStates` with
that assigned predictive value. `outcomes6` maps those representatives to their
values. `outcomes6_cover` proves that every raw factor's class occurs;
`representative6_exact` proves that decoding any enumerated outcome yields its
actual raw value. This is a finite exact image, not a truncation or a stored
nine-class table. Its cardinality may change with assigned primitives.

`row6` reads the assigned action row on K; exit rows are **empty**, as in L6a
`c6Row`. `mass6` filters that actual row by computed predictive equality and
sums its exact integer weights. `weight6` divides the resulting integer by the
model's declared denominator four, with the assigned funding/resource/budget
gate. No uniform distribution is substituted.

### Run update, observer and code

`Run6` carries the raw factor, unbounded event counter, unbounded tick counter,
retained raw route tuple and funded bit. It omits a duplicated tag because each
assigned model is indexed by its tag.

`update6` selects the defined representative, increments the event counter,
adds the assigned tick delta, retains residue, and updates the funded bit using
the raw post-action budget equation. Exit tick deltas are zero, matching L6a;
this does not assert strict tick growth for exits with no supported responses.

Budget uses exactly the declared POS-04 **constant-budget lift** from G1c, not
an invented variable-budget controller. `budget6` reads initial budget;
`budgetAfter6` computes cost/recharge; `LedgerConservation6` checks their
equality. Invalid ledgers cannot be certified by the eventual acceptance gate.
The canonical equation holds globally, and zero recharge fails it. This model
makes no claim of arbitrary changing-budget dynamics.

`writer6` resolves residue against the computed raw route tuples in the fixed
a-then-b priority order and reads the assigned writer bit. This matches the
frozen writer rule on canonical data; it does not consult stored route names
as provenance values.

`code6` is the fixed declared six-field code (computed predictive value,
event counter, tick parity, raw residue, funded state, resource owner).
`observation6` has all eight frozen-interface components, with progress and
funded writer record count derived from the event counter. These are fixed
functions of decoded inputs/run state; none may be supplied by a caller.

`future6` is the G1b `FullFutureModel` built from exactly these definitions.
`dynamics6` is the G1c raw dynamics built from the same weight/updater.
`dynamics6_check` identifies them everywhere and hence on the whole closure.
There are no candidate weight, successor, observer or code arguments.

### Roots and closure

`roots6` is defined from the clause's ten-state factor domain and each available
raw route tuple, with occurrence/tick zero as in L6a `c6Witness`. Its funded
bit comes from the assigned receiver. Missing route references produce no
corresponding roots. This is the clause's factor audit context, not a claim
that every factor is a handoff arrival.

`Closure6` reuses G1c `FutureClosure` from these defined roots/dynamics. It
covers arbitrary finite iteration, including zero-weight enumerated successors
(as the G1c closure deliberately does). It is not a bounded-horizon search.
The guard witness below uses **positive-weight** steps, so it does not exploit
the additional zero-weight closure states.

## Locality and canonical component links

- `run_inputs6_locality`, `future6_locality`, `dynamics6_locality`,
  `roots6_locality`, `closure6_locality`: agreement on the fixed C6 scope
  identifies the defined objects and closure membership.
- `canonical_predictive6`: decoded predictive values equal L6a's raw
  `predictiveNow`; `canonical_M6_link` proves pairwise equality agrees with
  imported `taggedMClass`, meeting the L5 rule.
- `canonical_outcomes6`: the raw image order is
  `m0,m1,m2,exit2,m3,m4,m5,m6,exit5`. L6a's list puts both exits last.
  **This is an enumeration-order difference, not a class difference.** The
  remaining word-law equivalence must transport finite sums across this order;
  literal list equality is not falsely asserted.
- `canonical_representative6`, `canonical_mass6`: representatives and exact
  raw class masses equal L6a's corresponding data, for every factor/action/class.
- `canonical_code6`, `canonical_writer6`, `canonical_observation6`: exact
  links on every run, not only audit roots.
- `canonical_weight6`, `canonical_update6`: links to G1c's actual raw
  action-row probabilities and counter/ledger updater on every run.
  `canonical_weight6_fullfuture` / `canonical_update6_fullfuture` also link
  directly to the G1b full-interface model.
- `canonical_initial6_root`, `canonical_merged_roots6`: roots are nonempty on
  both tags; p0w0 and p0w1 are distinct roots with equal computed code.
- `canonical_three_step_closure6` and `canonical_three_steps_supported6`:
  p1w0 —cw→ p2w1 —stay→ p1w0 —cw→ p2w1, with exact probabilities
  **1, 3/4, 1**, reaches event/tick count three. These follow the published raw
  rows via the canonical links. Neither probability is a chosen threshold.

These are **component links**, not yet canonical equivalence of C6 acceptance
or a proof of all-word future sufficiency. No new `C6Accept` is defined.

## Argument classification

| Argument/object | Classification | Treatment |
|---|---|---|
| `a : Assignment`, `tag : Tag` | Raw data/index | One shared immutable namespace and defined C6 scope. |
| `d : RunInputs6` in algebraic helper lemmas | Raw data | Tables and primitive projections, never future functions or accepted verdicts. Public model/closure constructors take the assignment, not d as a candidate model. |
| `x : Run6`, action, outcome, factor | Raw execution values | Exact states/counters and typed finite action/ambient values. |
| `Agrees`, outcome membership, closure membership | Evidence on raw/defined objects | Equations and exact inductively generated membership. |
| Class alphabet, representative map and probabilities | Defined objects | Constructed from assigned raw positions/hazards/action rows and the fixed ambient domain. |
| Updater, code, full observation, roots, closure, ledger equation | Defined objects | No supplied derived object accepted. |
| Proposal in `ProposedReadoutAgrees6` / `readout6_guard` | Diagnostic proposal only | Not an argument of `future6`, `dynamics6` or any certification theorem. Equality is required on the **whole** defined closure. |
| Arbitrary frontier/observation/weight/code/closure | Absent | No such candidate argument. |

## Readout coverage table

`UpdateLaws6` checks the numerical equations on a run step;
`closure_readout_laws6` proves them throughout the defined closure. The same
laws hold globally because their functions are defined from the updater.
The typed parameterized guard `canonical_each_readout6_guard tag field`
rejects each listed capped/constant proposal on the whole closure, at the
supported three-step witness. These are per-field proposal guards, **not**
raw-mutation C6-acceptance theorems.

| Field | Update/readout law | Check/theorem | Guard field |
|---|---|---|---|
| Raw factor | Successor = computed representative | `UpdateLaws6.factor` | `.factor` (exit constant) |
| Predictive now | Successor's predictive value = selected outcome when enumerated | `UpdateLaws6.predictive`, `representative6_exact` | `.predictive` (exit-class constant) |
| Event order/counter | counter + 1 | `UpdateLaws6.counter` | `.counter` (cap two) |
| Tick counter | ticks + assigned delta | `UpdateLaws6.ticks` | `.tickCounter` (cap two) |
| Tick phase | updated ticks modulo two | `UpdateLaws6.tickPhase` | `.tickPhase` (parity of capped ticks) |
| Genuine progress | updated event count | `UpdateLaws6.progress` | `.progress` (cap two) |
| Record writer | same assigned writer of retained raw residue/owner tag | `UpdateLaws6.writer` | `.writer` (false constant) |
| Endogenous record | funded assigned writer → updated count, else zero | `UpdateLaws6.record` | `.record` (cap two) |
| Route residue | retained actual raw tuple | `UpdateLaws6.residue` | `.residue` (empty tuple) |
| Maintenance | funded bit and positive raw post-action budget | `UpdateLaws6.maintenance` | `.maintenance` (false constant) |
| Owner | fixed assigned resource owner | `UpdateLaws6.owner` | `.owner` (opposite tag) |
| Budget | raw cost/recharge conservation in declared constant-budget lift | `LedgerConservation6`; `canonical_budget6_closure`; `assigned_ledger6_guard` | `.budget` (zero constant); zero-return raw ledger guard |
| Enabled | funded/recharge/budget availability recomputed after update | `UpdateLaws6.enabled` | `.enabled` (false constant) |

Progress/record do not have independent supplied candidate fields to cap. The
proposal guard detects disagreement with their defined functions, closing the
G1c loophole rather than creating another unchecked readout slot.

## Raw field coverage and remaining promotion blockers

| Raw cells/family | Defined consumer / established link | Remaining evaluator check (next seam) |
|---|---|---|
| Rows, positions, hazards | `predictive6`, representatives, `mass6`, `canonical_M6_link` | Row validity and computed lumpability/bisimulation; raw cell guards. |
| Tick table | `delta6`, actual updater, exact canonical update link | Funded tick rule, NEG-C6-FUTURE, positive tick/growth gates. |
| Resource/ledger | `enabled6`, budget update, canonical conservation and raw zero-return guard | Funding/owner gates and completeness in C6 acceptance. |
| History/route table | Actual tuple roots/residue/writer resolution | Coverage, nonempty supported history, realized route execution and reference guards. |
| Writers | Actual assigned writer and record readout | Writer availability, NEG-C6-RECORD. |
| Events/realized stages | Decoded in raw inputs; not yet used by the future lift | Strict realized event/path gate, missing-mix guard. **Pending**, not silently inferred from corridor. |
| Receiver funded bit | Root funded value | Trace funding/completeness gate; do not add source-presence to package clauses. |
| Declared interface | Decoded raw list; observer defined with all eight components | Interface equals frozen ordered component list. |
| Policy/published P/M | Shared cells in the C6 scope | Canonical-response/P reconstruction and raw/imported M coherence in the clause gate. |

An absent primitive can currently be totalized by the decoder; these total
functions are **not acceptance evidence**. The next seam must include the
completeness gate rejecting all missing inputs, as in C1–C5/C7/C8.

## Remaining seam and done-bar

1. Define funded strict trace/event/path checks using the decoded events,
   realization, histories, routes, ticks, resources and writer fields.
2. Define a raw-checkable one-step bisimulation gate for the **defined**
   `future6`, on the computed closure. Prove the finite factor equations imply
   it, and prove all-word sufficiency by induction / FullFuture machinery.
   Do not replace it with a stored future-sufficiency field.
3. Define final C6 gate/acceptance with all completeness/interface/funding/
   writer/coarseness checks; prove locality and canonical C6Pass equivalence
   on both tags. Transport the raw class order in the G1b word-law link.
4. Apply exact declared raw adapters for future tick, writer availability and
   missing realized mix; prove per-tag M3b outcomes and raw-field guards.

Size: **L**, dominated by the factor bisimulation/closure lift and canonical
word-law equivalence. No new scientific model or declaration is needed. None
of these pending checks is described as passed in this note.

## Proof-review self-check

Trace: assignment → scoped raw tables → exact predictive image → integer
pushforward weights → defined run lift → defined code/observer → computed
unbounded closure → component laws and canonical links. Proposal guards cover
all closure states and use an actual supported witness beyond the audit cap.
No independence/sufficiency claim is inferred from the mere existence of the
code, and no trace realization is inferred from a sibling lane.

The canonical merged roots establish nontrivial coarseness, but do not alone
establish sufficiency. No verdict or law certificate is stored in the assignment.
No existing theorem or frozen source is modified. Verification receipts follow.

## Verification receipts

- `cd lean && lake build`: exit 0, 314 jobs. New modules built in about
  2.5 s (C6Dynamics), 7.0 s (C6DynamicsLinks), 2.8 s (C6ReadoutGuards).
  No new warnings; existing replayed warnings remain.
- `scripts/validate_lean.sh`: exit 0, OVERALL pass; all 39 rows / 174 registered
  declaration entries resolve and are axiom-clean. Source scan: 0 placeholders,
  0 high-confidence vacuity findings, 23 non-gating ignored-input leads.
- Read-only `/tmp/g2b3-axioms.lean` probes: all **34** new theorem names resolve;
  axiom union contained in `propext`, `Quot.sound`, `Classical.choice`.
- Forbidden-construct scan of the new C6 modules: no matches.
- `git diff --check`: clean. Registry, inventory, CST-TT-08 and frozen model
  declaration/spec/predictions remain untouched. No commits made.
