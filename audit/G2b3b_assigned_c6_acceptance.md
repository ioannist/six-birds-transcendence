# G2b-3b — assignment-indexed C6 completion

## Result and scope

The second seam completes assigned C6 at its **declared surrogate ceiling**.
Authority: frozen [M3_model_spec.md](M3_model_spec.md:22), clause C6, and its
funded event/run mechanics at lines 30–33. No T18/NOTCH upgrade, full P05
package, T17-I or physical claim is made. TTH-02 stays conditional; there is
no registry or inventory edit.

Files: five new modules `Assigned/C6Sufficiency.lean`, `C6Acceptance.lean`,
`C6Adapters.lean`, `C6Guards.lean`, `C6FrozenLinks.lean`, their root import,
and this note. All new definitions/statements are **(b) mathematical** for
TTH-02's assignment-indexed C6 substrate. No existing declaration is changed
or renamed; (a) list empty. The first seam's definitions remain unchanged.

## Acceptance and its actual dependencies

[C6Acceptance.lean](../lean/CSTTT/POS04/Assigned/C6Acceptance.lean:48) defines:

```lean
C6Gate a tag :=
  Ready a tag .c6 ∧ Reference6 (runInputs6 a tag) ∧
  Trace6 (runInputs6 a tag) tag ∧ LedgerConservation6 a tag ∧
  (runInputs6 a tag).interface = futureInterface ∧ UnitFunding6 (runInputs6 a tag)
C6Accept a tag :=
  C6Gate a tag ∧ FiniteBisim6 (runInputs6 a tag) ∧ Coarser6 a tag
```

`Ready` requires every scoped cell and valid exact integer action rows.
`Reference6` checks computed M against the imported partition and reconstructs
canonical P from the assigned action rows and policy. Imported M/P are
comparison targets, not future readouts. The remaining functions are defined
from scoped assigned primitives:

- `Trace6`: funded receiver, own recharge, budget ≥ price, funded unit ticks,
  both route writers, realized strict atomic event paths, own resource owner.
- `paths6`: both nonempty routes resolve to nonempty supported histories;
  event references resolve; **every certified step** is strict, atomic and
  realized at both endpoints; endpoints compose; the realized stage list
  matches the declaration and every event id is covered. There is no call to
  a corridor verdict or to default `eventOf` on a missing id.
- `LedgerConservation6`: the raw `budget - cost + recharge = budget` equation.
  This is mandatory for the inherited constant-budget lift; changing return
  to zero rejects acceptance. `UnitFunding6` also requires the declared initial
  budget, action cost and recharge to each equal one, and requires strictly
  positive initial and post-step funding (M3 line 32; same unit equations as
  assigned C8 `Ledger8`). Conservation alone was insufficient: the all-zero
  ledger conserved zero but lost maintenance and record growth. The defined
  observation reads maintenance,
  owner and the route register as well as the five temporal/predictive fields.
- `Coarser6`: the assigned p0w0/p0w1 roots have equal code and distinct factors.
  This is not merely an inhabited witness type.

`canonical_accept6` proves acceptance on each tag. Missing inputs cannot be
rescued by decoder defaults (`c6_missing_rejected`, for any scoped cell and
any assignment). `c6_gate_locality` and `c6_accept_locality` derive locality
from the generic decoder theorem, including the future and root definitions.

## All states, all finite words

[C6Sufficiency.lean](../lean/CSTTT/POS04/Assigned/C6Sufficiency.lean:9)
checks class-aggregated **integer masses**, not raw row ordering, and tick
deltas for every equal-predictive factor pair and each action. The class
alphabet is the exact image of the assigned raw factor readout. An outcome
outside that image has zero mass (`mass6_absent`), so the proof also covers
outcomes not selected for enumeration.

```lean
bisim6_all_states (a : Assignment) (tag : Tag)
  (h : FiniteBisim6 (runInputs6 a tag)) : FullOneStepBisim (future6 a tag)
assigned6_all_words (a : Assignment) (tag : Tag)
  (h : FiniteBisim6 (runInputs6 a tag)) : FullFutureSufficient (future6 a tag)
```

Code equality supplies equality of predictive factors, counters, tick parity,
registers and maintenance. Observations agree (writer is a defined function
of the same register), masses agree, and successor codes agree using modular
addition. The existing `full_future_sufficient_of_bisim` inducts over words.
**These results quantify over all `Run6` states**, with arbitrary counters,
residues and funded bits. They are not restricted to `Closure6`; we do not
claim that every possible run is reachable. `closure6_all_words` is only an
additional consequence. No bounded enumeration proves an unbounded claim.

`canonical_future6_legacy_quantifier` proves exactly:

```lean
(∀ tag, FullFutureSufficient (future6 canonical tag)) ↔
  C6FutureSufficient .positive
```

The legacy state includes a tag; equality of its code forces equal tags.
`eraseTag6`/`legacyRun6` translate arbitrary states, preserving the quantifier.

## Exact canonical links and outcome order

`canonical_c6_equivalence` gives `C6Accept canonical tag ↔ C6Pass .positive tag`.
It is a canonical truth equivalence backed by the independent raw gate proof,
not an assertion that arbitrary assignments equal a fixed table.
The stronger semantic links are:

- `canonical_word_law6`: assigned word probability equals the G1b
  `pos04FullFuture` probability for **every** run, word and observation trace.
- `canonical_word_law6_L6a`: the same exact equality to `F .positive`.
- `canonical_word_law6_G1c`: the same equality to G1c's **bridge-owned**
  `bridgeFuture pos04SnapshotBridge`, translating the complete trace by
  `frozenObservation6`. This translates Tag ownership to carrier ids and
  preserves all eight fields, including exit observations. The translation
  is injective, and its observation, weight and successor links are proved.

The assigned exact-image order puts exit2 before m3; legacy outcome order puts
exit2 after m6. The nine per-outcome summands are identified using the first
seam's raw mass/representative/update links, then rational associative and
commutative addition resolves the permutation. **No outcome is dropped or
probability approximated.** The G1c equality uses its own dynamics links and
an induction on words after the observation embedding.

## Controls and the legacy negative quantifier

[C6Adapters.lean](../lean/CSTTT/POS04/Assigned/C6Adapters.lean:5)
mutates cells, leaving every derived object to be recomputed:

| Intervention | Raw change | Assigned source acceptance | Assigned target acceptance | Additional result |
|---|---|---|---|---|
| Positive | Canonical assignment | pass | pass | All-state sufficiency on both tags |
| NEG-C6-FUTURE | Target p0w1/stay tick becomes 2 | pass | fail | Equal-code p0 pair has unequal actual one-word probabilities; `neg_future6_not_sufficient` |
| NEG-C6-RECORD | Target route B writer becomes unavailable | pass | fail | `neg_record6_all_words`: sufficiency still holds; trace writer check fails |
| Realized-stage sensitivity control | Remove mix1 from realized stages | fail | fail | `missing_realized6_assigned` directly fails the path gate |

`controls6_ticks`, `controls6_writers`, `controls6_realized` compare raw
changed fields pointwise with legacy intervention data. `controls6_rows`,
`controls6_predictive`, `controls6_mass` prove unchanged transition/class
content. `controls6_trace_equivalence` gives the exact trace-control outcomes;
`c6_m3b_per_tag_outcomes` collects the package acceptance results.

M3b records target future/C6 and trace failure for NEG-C6-FUTURE; for
NEG-C6-RECORD **only target trace fails**, not future sufficiency. This
separation is preserved. These are C6-only results, not a new full mutation
side-effect attribution across other clauses or handoff lanes.

**Legacy negative limitation:** `C6FutureSufficient .negFuture` quantifies
across both tags. Consequently the legacy *source* `C6Pass .negFuture` also
fails through a target counterexample. M3b evaluates the source future per
tag, which stays sufficient. We preserve the legacy all-state quantifier for
canonical equivalence and explicitly do **not** claim negative source
`C6Pass` equivalence. No legacy definition or frozen result is altered.

## Argument classification

| Argument or object | Classification | Constraint / construction |
|---|---|---|
| `a : Assignment` | Raw immutable data | Typed shared cell namespace; scoped decoding |
| `tag : Tag` | Raw carrier selector | Same cell identities as L5; owner gate |
| `h : C6Accept a tag` / finite mass equations | Evidence on raw data | Conjunction of computed checks; no free predicate/verdict field |
| `x,y : Run6`, `act`, `word`, `trace` | Raw run/query data | Universal quantifiers, not a supplied future |
| Scoped inputs, predictive classes, ordered representatives, probabilities | Defined objects | `runInputs6`, raw support/hazard readout, exact image/mass computation |
| Run updater, code, eight-field observation | Defined objects | `update6`, `code6`, `observation6`; no candidate parameter |
| Roots and closure | Defined objects | Assigned route/history/register and receiver fields; `FutureClosure` |
| Gates, acceptance, coarser roots | Defined objects | The formulas above; absence rejects |
| Legacy/G1b/G1c comparison models | Existing fixed objects | Exact canonical word-law transport, not acceptance inputs |
| Proposed capped readout in a guard | Method control/query | Must equal the defined readout on the whole closure; never accepted as model data |

## Raw field coverage

All guards below actually reject assigned acceptance unless explicitly marked
as a readout proposal check. They alter one named raw cell/family; event
subfield guards target only the indicated member.

| Cell/family used by C6 | Law/check | Guard theorem |
|---|---|---|
| Own action rows | `Ready` row validity; P reconstruction; mass bisimulation | `c6_rows_guard` |
| Positions | Computed predictive readout / imported-M partition link | `c6_positions_guard` |
| Hazards | Computed action support law / imported-M partition link | `c6_hazards_guard` |
| Canonical policy | Raw row reconstruction against P | `c6_policy_guard` |
| Published P | Comparison against reconstructed canonical rows | `c6_P_guard` |
| Published M | Label fidelity and pairwise equality with computed M | `c6_M_guard` |
| Own tick table | Funded nonempty responses tick once; bisimulation deltas | `neg_c6_future_assigned`, `neg_future6_bisim_fails` |
| Full interface list | Exactly the eight declared components | `c6_interface_guard` |
| Own resource recharge | Funded availability | `c6_resource_funding_guard` |
| Own resource owner | Equals own tag | `c6_owner_guard` |
| Ledger initial budget | Exactly one token, positive and covers raw action cost | `c6_initial_budget_guard`, `c6_zero_ledger_rejected` |
| Ledger action cost | Exactly one token, funding and conservation | `c6_action_cost_guard` |
| Ledger return | Exactly one returned token, mandatory positive conservation | `c6_budget_conservation_guard` |
| Histories | Nonempty and supported by assigned canonical action rows | `c6_histories_guard` |
| Event table / references | Resolved lookup on every path step | `c6_events_guard` |
| Event atomic flag | Raw atomicity on realized path | `c6_atomic_guard` |
| Event strict flag | Raw strictness on realized path | `c6_strict_step_guard` |
| Event stage endpoints | Realization, stage-order increment, adjacency | `c6_endpoint_guard` |
| Realized stages | Realized at every step; complete declared path domain | `missing_realized6_assigned`, `c6_realization_guard` |
| Receiver funded bit | Trace starts funded | `c6_receiver_funding_guard` |
| Route table/history references | Every declared route resolves | `c6_routes_guard` |
| Route event paths | Nonempty, complete, connected strict realized execution | `c6_route_path_guard` |
| Per-tag writers | Available on both declared routes; resolved register writer | `neg_c6_record_assigned`, `c6_writers_guard` |
| Any missing scoped cell | Completeness before totalized decoding can accept | `c6_missing_rejected` |

Receiver source-presence/target-display flags, event support flags and route
names are not extra C6 requirements. Source withdrawal is a handoff/autonomy
check, not a dependency of this package clause. No guard falsely claims
that altering an unused field must reject C6.

## Closure-wide evolving readout coverage

The first seam's closure includes all enumerated successors, including zero-weight
ones. Its laws therefore cover more than just supported execution.
`update_laws6` applies to **every** run update, and
`closure_readout_laws6` restricts it to the entire computed closure.
`c6_accept_closure_laws` exposes this consequence of acceptance. The readouts
are definitions, not additional fields to supply to acceptance.

For every row below, the proposal guard is
`canonical_each_readout6_guard tag field`, witnessed by the supported third
step in the closure; its field argument names the row. The generic witness
rule is `readout6_guard`. Proposals never substitute for defined readouts.

| Readout (`Field6`) | Update law / definition | Gate or theorem | Per-field constant/capped guard argument |
|---|---|---|---|
| Factor (`factor`) | Computed representative of raw outcome | `UpdateLaws6.factor` | `.factor` |
| Predictive (`predictive`) | Raw predictive of next representative = enumerated outcome | `UpdateLaws6.predictive` | `.predictive` |
| Order/counter (`counter`) | Counter + 1, no cap | `UpdateLaws6.counter`, raw strict path gate | `.counter` |
| Tick counter (`tickCounter`) | Ticks + assigned factor/action delta | `UpdateLaws6.ticks`, `ticks6` | `.tickCounter` |
| Tick phase (`tickPhase`) | Updated ticks modulo 2 | `UpdateLaws6.tickPhase` | `.tickPhase` |
| Progress (`progress`) | Next counter, hence old counter + 1 | `UpdateLaws6.progress` | `.progress` |
| Writer (`writer`) | Assigned writer of unchanged raw residue | `UpdateLaws6.writer`, `writers6` | `.writer` |
| Record (`record`) | Next counter iff maintained and writer available; otherwise zero | `UpdateLaws6.record` | `.record` |
| Route register (`residue`) | Retained exactly | `UpdateLaws6.residue` | `.residue` |
| Maintenance (`maintenance`) | Funded AND raw post-budget positive | `UpdateLaws6.maintenance`, conservation | `.maintenance` |
| Owner (`owner`) | Own assigned resource owner | `UpdateLaws6.owner`, owner gate | `.owner` |
| Budget (`budget`) | Declared positive unit lift; raw post-budget equals it | `LedgerConservation6`, `canonical_budget6_closure` | `.budget` |
| Enabled (`enabled`) | Maintained AND recharge AND budget covers price | `UpdateLaws6.enabled`, funding gates | `.enabled` |

There is no uncovered evolving readout. In particular progress cannot be
replaced by `min counter 2`, and record/owner/maintenance/residue cannot be
supplied independently. Constant-budget semantics remain an explicit
restriction of the declared model family, not a generic variable-budget law.

## Proof-review check and verification

Trace: assignment → scoped primitives → computed factor partition and integer
masses → defined run lift/closure → raw finite equations → all-state
bisimulation → induction on every finite word → canonical links and controls.
The canonical p0 pair proves genuine coarseness and distinctness; the tick
control supplies an actual unequal-probability witness. Writer removal
rejects availability without falsely disproving sufficiency. Missing or
unrealized objects are rejected by the clause itself. Readout laws are built
into the updater/readouts, never arbitrary proof fields.

### Verification receipts

- `cd lean && lake build`: exit 0, **319 jobs**, green. Representative
  module build times: sufficiency 7.5 s, acceptance 3.4 s, adapters about
  10 s, guards 5.2 s, frozen links 2.1 s. These are module compile timings,
  not a summed wall-clock benchmark. No new warnings; existing vendor and
  older CSTTT warnings are replayed.
- `scripts/validate_lean.sh`: exit 0, **OVERALL pass**, all 39 rows / 174
  registry entries resolve, axiom-clean. Source scan: 0 placeholders,
  0 high-confidence vacuity findings, 23 non-gating ignored-input leads.
- `/tmp/c6-cr1-axioms.lean` read-only `lake env lean` probes: **75 new theorems**
  resolve and print axioms; union contained in `propext`, `Quot.sound`,
  `Classical.choice`. No probe errors or untrusted axiom.
- Forbidden-construct scan of the five new modules: no matches.
- `git diff --check`: clean. The only existing file changed is the root
  import; registry/inventory, CST-TT-08, frozen models and evaluator results
  remain unchanged. No commits made.

Reproduce the required gates with:

```bash
cd lean && lake build
# From repository root:
scripts/validate_lean.sh
# Read-only theorem probes (this session's /tmp file):
cd lean && lake env lean /tmp/c6-cr1-axioms.lean
```

Open issues: no completion blocker for this seam. The C6 surrogate grade,
constant-budget family, and the legacy negative cross-tag quantifier
limitation above remain disclosed. G2c package/gluing assembly remains the
next packet; no status promotion is made here.


## Eddy CR1 — positive conserved unit funding

**Finding fixed:** the earlier acceptance gate admitted a zero budget/price/
return assignment. Its conservation equation held but its post-step funding
was not positive. This was a defect; no earlier record-growth claim is used
as evidence for the repaired result.

Changes in this request are restricted to `C6Acceptance.lean`,
`C6Adapters.lean`, `C6Guards.lean` and this note. Statement changes are **(b)**
for TTH-02's assignment-indexed C6: `C6Gate`/`C6Accept` now include computed
`UnitFunding6`, enforcing the POS-04/C8 unit ledger and strict positivity.
No dynamics, code, observation, frozen data or registry is changed. Existing
canonical equivalence and per-tag control statements are unchanged and their
proofs are rechecked under the stronger gate.

Derived results, for any accepted assignment:

- `accepted_writer6`: each registered raw route tuple resolves to an available
  writer, including the case of coincident route tuples.
- `c6_accept_funded_writer`: inducting over the **entire computed closure**,
  every root starts funded with its assigned route writer; updates retain
  funding and that writer. There is no supplied maintenance/writer field.
- `c6_accept_record_advancement`: for every closure state and every update,
  the conserved post-budget is positive, the successor is funded, and the
  successor's endogenous record is exactly the previous record plus one.
  This includes every positive-probability supported execution step. The
  theorem is stronger: it also covers enumerated zero-weight updates.

Record advancement is an execution claim rooted in the audited route domain;
we do not claim it for arbitrary runs with unregistered residues. **Future
sufficiency still quantifies over all run states**, exactly as before.

`zeroLedger6` changes only the shared raw ledger to budget=cost=recharge=0;
`c6_zero_ledger_rejected` proves rejection on both tags. The canonical source
and target acceptance, exact L6a/G1b/G1c equivalences, and the per-tag M3b
control outcomes are retained. No new narrowing or status change is made.


CR1 verification: the full `lake build` is green (319 jobs); all 75 C6 seam
proofs resolve and their axiom union is contained in `propext`, `Quot.sound`,
`Classical.choice`. The targeted rebuild rechecked canonical acceptance,
canonical L6a/G1b/G1c equivalences and all per-tag outcomes (no change to
those outcomes). New module timings for this fix were 3.6 s (acceptance),
12 s (adapters), 4.1 s (guards), 1.5 s (frozen links). No new warnings.
The forbidden scan and `git diff --check` are clean.
The CR1 validator rerun also exits 0 (`OVERALL pass`): all 39 rows / 174
registered entries resolve and are axiom-clean; scans report 0 placeholders,
0 high-confidence vacuity findings and 23 non-gating ignored-input leads.
Reproduce with `cd lean && lake build`, `scripts/validate_lean.sh` from the
repository root, and `cd lean && lake env lean /tmp/c6-cr1-axioms.lean` for
this session's direct theorem probes.
