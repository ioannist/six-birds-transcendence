# G2b-2 — assigned C8, and C6 scope report

## Delivery boundary

**C8 is implemented fully. C6 is deferred under the packet's explicit sizing
exception.** This is not a completion claim for C6 or G2. TTH-02 remains
conditional; no registry, inventory, frozen model, or old clause declaration
changes. The existing fixed-table C6 theorems remain intact.

Authority for C8: frozen `audit/M3_model_spec.md:24,32`,
`lean/CSTTT/POS04/C8.lean:14–68,192–322`, and the withdrawal control in
`lean/CSTTT/POS04/Bridge.lean:219–239`. The C8 content remains the operational,
funded maintained-kernel clause, without upgrading C4–C7's surrogate grades.

### Files and (b) statement changes

All additions are **(b) mathematical**, supporting TTH-02 assignment-sensitive
package acceptance; no existing theorem statement is weakened.

- `Assigned/Substrate.lean`: package C8 scope contains only rows, policy,
  resource and ledger cells. Receiver source presence is read by a separate
  receiver-specific evaluator, with its own enlarged scope. C1–C7 scopes are
  unchanged. The CR1 correction removes the earlier erroneous package
  source-presence premise (a disclosed **(b)** semantic correction).
- `Assigned/C8.lean`: assignment-derived raw viability, finite greatest-set
  algorithm, universal monotonicity/fixed-point/greatest-ness and locality.
- `Assigned/C8Adapters.lean`: exact legacy/control equivalence, canonical
  positive evidence, actual resource-deletion and withdrawal transformations,
  funded-row preservation.
- `Assigned/C8Guards.lean`: missing-cell/subfield guards and a proper singleton
  greatest-set instance for arbitrary raw rows.
- `CSTTT.lean`: imports C8Guards and therefore these new modules.

The subset enumeration is an algorithm refinement: it computes the **same
greatest viable set**, rather than assuming that a named variant's ten-round
pruning receipt establishes convergence for arbitrary assigned data.
The unit ledger conditions and row denominator four are unchanged POS-04 raw
rules, not tuned values. The method singleton example derives its weight four
from that denominator. It is not a new scientific model declaration.

## Defined C8 evaluator

Namespace below: `CSTTT.POS04.Assigned`.

`ViabilityInputs` contains assigned action rows, canonical-policy choice,
tag-owned resource and ledger. `clause8 a tag`
decodes the C8 scope and constructs those inputs. Missing fields cannot be
accepted: `C8Gate = Ready a tag .c8` requires completeness and well-formed raw
rows. The package decoder never consults receiver presence. The separate receiver
decoder totalizes an absent presence input to false and rejects missing receiver
inputs through its own completeness gate.

`available8` computes recharge availability, budget sufficiency, positive
remaining budget and resource ownership. Both tags' **package** responses are
independent of receiver source presence. `receiverData8` derives a separate
effective resource: recharge is available for a source receiver response only
when the source is present. `ReceiverC8Accept` uses that derived input and the
shared `greatest8` algorithm; it checks the original package ledger separately.
For target responses, `receiver_data8_target` proves this input equals the
package input exactly.

`rowClosed8 d s act S` checks a nonempty raw action row, exact total weight four,
positive entries, and support entirely inside S (ambient exits fail).
`retain8` requires available funding and some closed response. `prune8` filters
S by `retain8`. `Viable8` requires every member to survive this same raw test.

The finite algorithm:

```lean
def greatest8 (d : ViabilityInputs) (tag : Tag) :=
  kernel.filter fun s => candidates8.any fun S =>
    decide (s ∈ S) && viableTest8 d tag S
```

`candidates8` is the recursively computed powerset of the ten-state kernel,
not a supplied candidate/certificate. The function enumerates 2^10 subsets;
there is no unbounded search or installed library. Duplicated lists supplied to
the universal viability theorem are normalized to kernel order before using
this enumeration.

`C8Accept a tag` is the conjunction of the gate, nonempty computed greatest
set, availability, the raw unit ledger equations, and `PUnchanged8`. The latter
checks the assigned policy's action rows against T1's exact P. No Boolean
verdict or `accepted : Tag → Prop` field is supplied. Receiver presence is not
a package C8 condition, matching M3b.

### Universal fixed-point proof

All the following quantify over **every `ViabilityInputs`**, without restricting
to funded/underfunded named variants or demanding canonical raw rows:

| Theorem | Statement/content |
|---|---|
| `row_closed8_mono` | A closed response stays closed when its candidate set grows. |
| `retain8_mono` | Funding is candidate-independent; the closed-response witness transports along inclusion. |
| `prune8_mono` | A ⊆ B implies prune(A) ⊆ prune(B). |
| `filter_mem_subsets8` | Every normalized subset appears in the defined enumeration. |
| `greatest8_contains_viable` | Every `Viable8 d tag S` is contained in `greatest8 d tag`, using that viability hypothesis. |
| `greatest8_viable` | Each retained state has a viable-subset witness; monotonicity moves its response into the union. |
| `greatest8_fixed` | `prune8 d tag (greatest8 d tag) = greatest8 d tag`. |
| `prune8_fixed_iff_viable` | Fixed subsets are exactly viable subsets. |
| `greatest8_contains_every_fixed` | Every pruning fixed subset lies in the computed greatest one. |
| `unavailable8_empty`, `unavailable8_no_viable` | Unavailable funding forces the greatest set, and every viable set, to be empty. |

This proves greatest-ness substantively, not by the positive model's kernel
being the whole state domain. `singleton8_greatest_membership` supplies a
separate method instance where membership in the computed set is exactly
`s = p0w0`: a nonempty proper subset.

### Locality, canonical equivalence, and controls

- `clause8_locality`: agreement on C8 scope implies identical decoded inputs.
- `c8_gate_locality`, `c8_accept_locality`: gates and acceptance are local.
- `controls8_raw`: each adapter's decoded raw inputs equal the corresponding
  legacy raw data. `legacy8_available`, `legacy8_row_closed`, `legacy8_retain`,
  and `legacy8_viable` link the actual operator, not only the final verdict.
- `controls8_greatest`: the defined enumeration equals the legacy deletion
  result on every declared C8 variant and tag. Its proof uses the universal
  greatest-set theorem plus legacy viable/empty evidence, not enumeration of
  an unproved stored answer.
- `controls8_equivalence`: assigned acceptance iff the legacy `C8Pass`.
  `c8_canonical_equivalence` specializes this on **both tags**;
  `c8_canonical_accepts` proves both positive instances.
- `funded_row8_unchanged`: available funding leaves **every** assigned raw action
  row unchanged. `accepted_funded_P_unchanged` and `c8_canonical_funded_P` link
  canonical responses to `taggedPNum`, following the L5 transition rule.

| Declared intervention | Actual transformation | Outcome theorem |
|---|---|---|
| NEG-C8-UNDERFUND | `underfund8`: set only target resource recharge to false. | `neg_c8_underfund_outcome`: target greatest empty, target acceptance false, source acceptance true; `neg_underfund8_no_viable`: every viable target set empty. |
| NEG-AUTONOMY-WITHDRAW | Apply the same recharge removal with explicit `withdraw8`: set receiver source presence false. | `neg_autonomy_withdraw_assignment`: withdrawn target greatest empty; both package and receiver acceptance false on target; **source package acceptance true**. |
| Positive withdrawal / NEG-ACTIVATION-SOURCE-ABSENT C8 outcome | `withdraw8 canonical`; source is explicitly absent. | `c8_target_only_assignment`: absence, target greatest=kernel, viability, receiver and package acceptance all proved. `c8_m3b_per_tag_outcomes`: package C8 passes on **both** tags. |

`clause8_withdraw` proves both tags' package inputs are unchanged by source
withdrawal. `package8_ignores_receiver` proves package acceptance is unchanged
even by replacement or deletion of the whole receiver cell. This is a generic
separation theorem, not just a canonical receipt.

`receiver_data8_target` identifies the target receiver input with its package
input. `withdrawn8_equivalence` links the receiver evaluator to the old
`C8ReceiverPass c8WithdrawnReceiver` on both recharge variants.
`withdrawn8_package_equivalence` links the package evaluator to old `C8Pass`
on **both tags and both variants**, including source under autonomy withdrawal.
No proof reads `ledger.sourceAvailableAfterWithdrawal = false` as withdrawal
evidence. Receiver decoding/acceptance have their own locality theorems.

`c8_m3b_per_tag_outcomes` gives the complete C8 per-tag table for the two
C8-targeting controls and the source-absence intervention:

| Intervention | Source package C8 | Target package C8 |
|---|---|---|
| NEG-C8-UNDERFUND | passes | fails |
| NEG-AUTONOMY-WITHDRAW | passes | fails |
| NEG-ACTIVATION-SOURCE-ABSENT / presence removal alone | passes | passes |

These agree with `M3b_results.json`'s `clause_pass_changes`. They do not claim
full C7/lane attribution; the recorded source C7 failure remains a C7 outcome.

## Argument classification table

| Argument/object | Classification | Treatment |
|---|---|---|
| `a : Assignment`, `tag : Tag` | Raw data/index | Immutable typed cells and shared namespace. |
| `d : ViabilityInputs` in universal operator lemmas | Raw data | Arbitrary tables, ledger and resource. Not a stored predicate or verdict. |
| `S`, `A`, `B : List KState` in universal lemmas | Raw candidate sets | Checked with the same response operator; they are not supplied as the computed greatest set. |
| Inclusion, `Agrees`, viability, funding hypotheses | Evidence on raw data | Each is an explicit equation/predicate on the preceding raw objects. |
| Variant enumerand in `controls8` | Adapter selector | Defines an actual assignment edit; no variant enumerand enters acceptance. |
| Scopes, decoded records, availability, response support, prune, powerset, greatest set, ledger checks and P check | Defined objects | Constructed from raw cells or the fixed typed finite domain; never supplied. |
| Receiver presence and `receiverScope8` | Raw receiver projection / defined scope | Read only by the separate receiver evaluator; completeness checked there. Package scope excludes it. |
| Receiver effective resource | Defined object | Computed from package resource and receiver presence; not supplied. |
| Source presence after withdrawal | Defined raw transformation | Receiver cell updated; absence shown in the result. |
| Imported T1 P | Fixed raw reference | Comparison uses actual assigned action rows; does not replace them in funded responses. |
| Lineage/corridor/bridge proofs | Absent | No lane premise in C8 package acceptance. |

## Field coverage and guards

The guards are concrete method-level perturbations, not claims that every
constant field is always invalid.

| Raw field | Law/gate | Guard theorem |
|---|---|---|
| Required cells/scopes | `Complete` plus scoped decoder | `c8_missing_rejected`, parameterized over **every** required cell; generic `decoder_outside`/`dropped_scope_read` remain available. |
| Action rows | Ready row validity; exact closed-response support/weight; funded P reconstruction | `c8_rows_guard`: empty all responses cannot reconstruct P. `singleton8_greatest_membership` also exercises nontrivial support-dependent pruning. |
| Canonical policy | Assigned selected row must equal P | `c8_policy_guard`: constant stay fails the actual p1→p2 response equation. |
| Resource owner | Owner equals the evaluated tag | `c8_owner_guard`: opposite tag fails funding. |
| Resource recharge | Recharge available | `c8_recharge_guard`: false fails; universal collapse proved. |
| Ledger initial budget | Budget≥cost and positive post-action budget | `c8_budget_guard`: zero budget fails. |
| Ledger action cost | Same budget check and unit/ledger equation | `c8_cost_guard`: doubling the declared unit cost fails. |
| Ledger recharge amount | Positive remaining budget and exact ledger equation | `c8_return_guard`: zero return fails. |
| Receiver source presence (**receiver-specific only**) | Source receiver responses require availability; package C8 does not | `c8_source_presence_guard`: withdrawn source **receiver** fails; `c8_target_only_assignment` proves target receiver survives. `package8_ignores_receiver` proves package independence on both tags. |
| Required receiver cells | Separate `Complete (receiverScope8 tag)` | `receiver_c8_missing_rejected`, parameterized over every receiver-scope cell. |

`Ledger.sourceAvailableAfterWithdrawal` is an unused documentary field, not
part of any computed C8 decision. All receiver fields are excluded from package C8. Source presence is the only
receiver projection read by the separate receiver evaluator. No false guard is
claimed for an ignored field. C6 and C7/handoff consumers have their own actual
receiver/event dependencies.

## C6 scope report — remaining work (L)

This delivery does **not** introduce an `Assigned.C6Accept`, nor pretend that
`FutureReferenceGate` already evaluates C6. That G2b-1 gate only checks reference
availability. C6's remaining work is a substantial assignment-derived run
semantics/proof layer, not merely replacing a few table identifiers.

Concrete obstruction to a small adapter: legacy `C6.lean:98–157` uses a fixed
seven-class `classOf`/`classRepresentative`, and `positive_bisim` at line 301
checks fixed `classMass`. Arbitrary assignments can change action supports,
hazards and therefore predictive classes. Reusing those fixed representatives
without proving their relation to **decoded** predictive data would reintroduce
the stale-dynamics error the packet forbids. Similarly, `RawRunDynamics.lean:21–41`
uses the fixed ledger/action data. The generic G1c bridge machinery has raw
run-level component/update recipes, but no assignment→bridge adapter that
constructs all of them from this substrate.

Required next implementation, without new scientific data or a changed ceiling:

1. **Defined assigned factor/run model (M).** Compute predictive classes from
   scoped action supports/hazards/positions; construct a finite outcome alphabet
   and exact aggregated action probabilities from those same rows (or prove a
   checked canonical class transport). Define the unbounded counter/ledger run
   updater, code, complete observer, and route/writer readouts from cells.
   No future/code/observer/representative function may be an input candidate.
2. **Closure-wide laws and full-word theorem (L).** Define the supported closure
   from the actual assigned roots and updater. Check every readout law on it,
   reusing `Transport.FullFuture.full_future_sufficient_of_bisim` and the
   `RawBridge`/`FrozenSnapshotBridge` law/guard pattern. Derive sufficiency by
   induction, with no horizon bound. Prove canonical dynamics/observer/code links
   and reuse `positive_bisim` only after those links are established.
3. **Equivalence/adapters/guards (M).** Exact `C6Pass` equivalence on both tags;
   raw tick and writer deletions for NEG-C6-FUTURE/RECORD; realized-stage guard;
   the actual p0 pair's distinct-state/equal-code witness.

### Required C6 readout coverage (all pending; no invented theorem receipts)

| Readout | Required assigned law/check | Required sensitivity |
|---|---|---|
| Predictive/factor | Actual supported transition and predictive-class transport | Changed row/hazard; an independently altered predictive display rejected. |
| Event order/counter | Actual realized path and counter+1 update | Unrealized mix; constant/capped order. |
| Tick | Assigned tick increment and parity update | NEG-C6-FUTURE raw tick mutation; capped tick. |
| Progress | Declared advancing-step increment, tied to counter | Capped progress at two. |
| Writer | Assigned writer at the decoded route residue/owner | NEG-C6-RECORD; constant false writer. |
| Record | Enabled writer yields advancing record count | Capped record; false writer. |
| Route residue | Decoded path/register and declared persistent update | Deleted raw path/write; independently altered residue. |
| Maintenance/ledger | Assigned funded budget action/recharge equation | Removed resource or altered ledger update. |
| Owner | Assigned tag owner preserved on future steps | Wrong resource owner or altered owner readout. |
| Enabled state | Assigned funding/availability rule | Availability inconsistent with ledger/resource. |

These are **completion blockers**, not optional leads. There is no mathematical
impossibility claim: the canonical instance already has the needed old results.
The work is to obtain their faithful assignment-indexed, closure-wide bridge
without supplied derived objects. C6 and the eventual G2c promotion are still
open. Splitting this off keeps the completed arbitrary-data C8 proof reviewable.

## Self-review

Trace: typed assignment → scoped inputs → funded row/support operator → computed
powerset union → universal fixed/viable/greatest proofs → canonical/control
operator equality → acceptance equivalence. The full-kernel case is not used to
prove universal greatest-ness. Empty rows are not viable; ambient exits reject
closure. The singleton example checks that the generic algorithm need not
return either all or nothing. Missing input never accepts a fallback.

Withdrawal explicitly changes presence and reruns the same target evaluator;
it does not infer target autonomy from source availability or a documentary
ledger flag. Package acceptance is unaffected by withdrawal on both tags; the
source-presence guard certifies receiver availability, not a package ablation. No old theorem, registry text, status, or surrogate ceiling changes.
The original verification receipts below are historical; CR1 receipts follow them.

## Verification receipts

- `cd lean && lake build`: exit 0, 311 jobs. New modules built in approximately
  2.0 s (C8), 2.1 s (C8Adapters), 2.4 s (C8Guards); root import 1.0 s.
  No new warnings; existing replayed warnings remain.
- `scripts/validate_lean.sh`: exit 0, OVERALL pass; all 39 rows and 174 registry
  declaration entries resolve and are axiom-clean. Scan: 0 placeholders,
  0 high-confidence vacuity findings, 23 non-gating ignored-input leads
  (including the deliberately constant stay-policy guard).
- `/tmp/g2b2-axioms.lean`, through `lake env lean`: all **53** new theorem names
  resolve. `#print axioms` union is contained in `propext`, `Quot.sound`,
  `Classical.choice`; no untrusted dependency.
- Forbidden-construct scan of the three new modules: no matches.
- `git diff --check`: clean. Registry, inventory, frozen models and CST-TT-08
  remain untouched. No commits were made.

## CR1 correction and proof self-review

The prior delivery conflated package funding with source availability. CR1
removes source presence from `ViabilityInputs`/`available8` and from package
scope. It adds the derived `receiverData8`/`ReceiverC8Accept` layer. The shared
pruning and greatest-set algorithms and their arbitrary-data proofs remain.
`c8_source_presence_guard` now states failure of **receiver** acceptance; it
no longer incorrectly rejects source package C8. `c8_target_only_assignment`,
`neg_autonomy_withdraw_assignment`, and `withdrawn8_equivalence` now distinguish
receiver acceptance from package acceptance explicitly. These are **(b)** changes
for TTH-02's package semantics and related TTH-05 receiver evidence, with no
status change.

Self-review: package assignment → package funding/gfp is independent of every
receiver field; receiver availability → effective resource → same gfp is a
separate computation. M3b source C8 remains passing under withdrawal plus target
underfunding; no claim is made that source receiver responses remain available.

CR1 verification receipts:

- `cd lean && lake build`: exit 0, 311 jobs; no new warnings.
- `scripts/validate_lean.sh`: exit 0, OVERALL pass; 39 rows / 174 registry
  declaration entries resolve and are axiom-clean. No placeholders or gating
  high-confidence vacuity findings; 23 non-gating heuristic leads.
- Read-only `/tmp/g2b2cr1-axioms.lean`: all 57 C8 theorem names resolve, with
  dependencies only within `propext`, `Quot.sound`, `Classical.choice`.
- Source scan of C8 modules: no forbidden constructs. `git diff --check` clean.
- The correction edits only C8 modules, C8's substrate scope, and this note.
  Registry, inventory, model declarations, old clause predicates and status
  remain unchanged. C6 remains deferred with the scope above.
