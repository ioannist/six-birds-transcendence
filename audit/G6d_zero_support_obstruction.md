# G6d: zero-support obstruction to whole O equivalence

## Verdict and proved boundary

**The requested unrestricted O equivalence is false**, even with the computed
nominal protocol and every primitive present. TTH-06 remains `conditional`.
No frozen definition, model, result, registry, or inventory has been changed.

In `CSTTT.TargetTheory.GenericHandoff.POS04HistoricalZeroSupport`:

```lean
counterexample :
  (POS04HistoricalRuntimeProtocol.check diagnostic).read (image assignment) = some true ∧
  HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy M assignment ∧
  ¬ AO diagnostic
```

`whole_operational_equivalence_false` negates the proposed biconditional for
all partial assignments satisfying that check. The positive game readout is
proved by constructing `operational_certificate` and applying the generic
causal-strategy soundness theorem. It covers all plays and every positive-support
successor; it is not a bounded check or a stored verdict.

This refutes **the adapter contract**, not the possibility of a generic TTH-06
soundness theorem. The F biconditional has not been decided by this diagnostic;
no full-package truth or falsity is claimed for it. Lineage and the final
RawHandoff assembly remain pending the resolution of the equivalence contract.

## Rule fixed before computation

Append `(.p2w0, 0)` to every target action row at `.p2w1`, the factor actually
reached by the baseline phase-2 response. Everything else is unchanged.
Because staging exchanges row namespaces, apply the source-assignment edit to
`.rows .source`. This is a null-entry representation diagnostic, not a new
positive model declaration or an edit to the frozen POS-04 JSON.

The mass is **zero by this rule**, not a fitted constant. The probability scale
four is the existing T1/POS-04 action-row denominator. `mass_unchanged` and
`probabilities_unchanged` prove, for every action and ambient outcome, that its
probability is unchanged. `canonical_p_unchanged` also proves the declared
canonical `PUnchanged8` check. No price, threshold, policy, resource, event,
history, withdrawal, or positive-support branch is altered.

| Computed/proved fact | Result | Declaration |
|---|---|---|
| All primitive cells present | yes | `assignment_complete` |
| Nominal protocol | passes | `nominal_protocol` |
| Canonical P reconstruction | unchanged | `canonical_p_unchanged` |
| Every action/outcome probability | unchanged | `probabilities_unchanged` |
| Every acquisition entry | unchanged | `entries_unchanged` |
| Positive support on the maintained run invariant | unchanged | `supported_unchanged` |
| Funded target updater, resources, ownership, and record/ledger laws | unchanged | `update_unchanged`, `resources_unchanged`, `legal_unchanged`, `step_unchanged` |
| Generic historical O game | holds | `operational_game_accepts` |
| Frozen AO | fails | `frozen_ao_rejects` |

The game uses the same explicit target run invariant and canonical policy as
the committed positive instance. Normalization includes zero entries without
changing total mass. The zero exit is proved **not** to be a positive-support
branch (`null_entry_support`); every positive branch is still preserved.
There is no dropped real exit or lucky-branch argument.

## Exact source of the disagreement

Frozen Version O is specified in `audit/G6_lane_spec.md:307–319`. Its Lean
implementation calls `rowClosed8` (`lean/CSTTT/POS04/Assigned/C8.lean:25–30`):

```lean
!row.isEmpty && decide ((row.map Prod.snd).sum = 4) &&
row.all (fun e => e.2 > 0 && match e.1 with
  | .inK t => decide (t ∈ S)
  | .p2w0 | .p5w1 => false)
```

This requires **every listed entry**, including a null entry, to be positive
and inside the set. The diagnostic therefore leaves `.p2w1` with no accepted
response, so the endpoint is excluded by the frozen greatest-set check.

The game definitions (`lean/CSTTT/Targets/GenericHandoff/StrategyGame.lean:25–33`)
instead use:

```lean
PositiveSupport rows r d a o := ∃ weight, (o,weight) ∈ rows r d a ∧ 0 < weight
Normalized rows r d a :=
  (∀ e ∈ rows r d a, 0 ≤ e.2) ∧
  ((rows r d a).map Prod.snd).sum = 1 ∧
  ∃ o, PositiveSupport rows r d a o
```

Zero probability is legal in a normalized row and creates no successor play.
Thus the frozen finite check has an additional strict sparse-format requirement.
The computed nominal protocol does not impose that requirement throughout the
future response domain. This is not a missing-input, source-funding, or
row-transport-at-an-unfunded-context issue.

## Adjudication and owner decision

A proof-script repair cannot establish the proposed biconditional.

**Recommended:** retain the causal positive-support semantics and introduce a
support-based finite response check: nonnegative weights, total mass four,
nonempty positive support, and every **positive** branch inside S. Re-prove the
finite constructor/game equivalence and its controls. Preserve frozen AO and
its historical results under their current names, recording this as a (b)
semantic/verifier revision. Review other clause uses separately; do not replace
`rowClosed8` globally without tracing them.

**Alternative:** explicitly make strict sparse-format validity part of the
new game's legal-response rule for the selected action. It must be computed
from its raw row, not supplied as a flag. This is a (b) change to the new game
semantics and makes the readout representation-sensitive. It is not the current
positive-support-only readout, and must be disclosed at the ceiling.

Adding an unannounced positive-row hypothesis to the arbitrary-partial
biconditional would narrow it. Restricting to the baseline or only the three
registered controls would also fail the requested done-bar. Neither was done.
The requested gate is stopped here for a decision; no semantic repair was
chosen or applied.

## Argument classification

| Object | Classification |
|---|---|
| `assignment`, `diagnostic` | Raw assignment transformation and unchanged withdrawal metadata |
| Received entries, rows, probabilities, updater and readouts | Defined by committed raw interpreters |
| Nominal check/completeness/ready evidence | Proved on the transformed raw assignment |
| Maintained run invariant and chosen canonical policy | Constructed auxiliary witnesses; obligations proved against the actual rows/updater |
| `operational_certificate` | Proof-bearing invariant, not an autonomy proof field |
| `operational_game_accepts` | Derived by causal-strategy induction |
| Frozen AO outcome | Kernel computation of the unchanged finite checker |
| Locality equations | Evidence on actual instruction dependencies; no supplied dynamics or observations |

## Coverage and guards

| Field/domain | Binding and check |
|---|---|
| Target rows | `rows_on_kernel`; exact list change, unchanged outcome masses |
| Positive support and normalization | `null_entry_support`, `null_entry_normalized`, `supported_unchanged`, `normalized_unchanged` |
| All activated entries | `entries_unchanged`; phase-2 execution untouched, no filtered entry |
| Updater | `program_agreement`, `update_unchanged`; all run contexts and outcomes |
| Resources/withdrawal/owners | `resource_agreement`, `resources_unchanged`, `legal_unchanged` |
| Counter/tick/progress/record/residue/ledger | `step_unchanged`; all run contexts, actual updater shared |
| Missing inputs | `assignment_complete`; committed rejection guards remain unchanged |
| Zero-entry sensitivity | `frozen_ao_rejects` versus `operational_game_accepts`: direct named-readout separation |
| Protocol-failure cases, both versions | `protocol_failure_cases`: the protocol-bound readouts and frozen AF/AO all reject |

The reusable `ResourceGameLocality` helper proves `inside_locality`,
`legal_locality`, and `step_locality` over arbitrary raw interfaces. It does
not assume row equality. This respects Eddy's qualification: row transport
uses resource closure along actual maintained runs; there is no claim of
unrestricted row equality at an unfunded run.

## Changes

(a): none. (b): additive mathematical locality laws and a kernel counterexample
to the requested TTH-06 O adapter. Existing statements/semantics unchanged.
No claim is made that the final generic TTH-06 promotion gate has been met.

## Checks and self-review

- `cd lean && lake build`: exit 0; 498 jobs, 51.19 s. Counterexample module:
  43 s. Existing linter warnings replayed; no new-module warnings.
- `scripts/validate_lean.sh`: exit 0; 39 rows, 209 unique declarations; zero
  placeholders, high-confidence vacuity findings, or untrusted axioms. No
  heuristic finding in either new module.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0 at its unchanged
  coverage, including its planted-drift checks. Frozen model/results untouched.
- `/tmp` `lake env lean` axiom probes: all 33 new theorem names resolve;
  dependencies are only `propext`, `Quot.sound`, and `Classical.choice` or fewer.
- Forbidden-construct and whitespace checks clean; `cst-tt/`, inventory, and
  `paper/` unchanged. Work left uncommitted.
- Self-review checked a genuine entry, resource-safe run contexts, all positive
  support branches, probability normalization, causal response selection, and
  nonempty auxiliary invariant. The null entry is not a real successor being
  suppressed. No F/package/lineage preservation claim is inferred from it.

Reproduce the built counterexample and scans:

```bash
cd lean && lake build
# From the repository root:
scripts/validate_lean.sh
python3 -B scripts/check_tth06_transcription.py
```

The headline counterexample is imported by `CSTTT`; `#check` or `#print axioms`
on `CSTTT.TargetTheory.GenericHandoff.POS04HistoricalZeroSupport.counterexample`
and `.whole_operational_equivalence_false` exposes the exact statements.

## Resolution (manager; Eddy ACCEPT-WITH-FIXES)

Adopted: the **alternative**, a disclosed **(b) representation-sensitive restriction**.
- Define `StrictSparse(row)` from the interpreted raw row: every listed weight is strictly positive.
- The generic F and O games require `StrictSparse` for the **selected response** only, at every generated play and every declared disturbance. Unselected actions are not checked.
- Normalization and positive-support successor quantification are unchanged.
- The positive-support-only readout stays identifiable, and the format-qualified game is proved to imply it.

Frozen `AO`/`AF` and all of their results are unchanged. Exact equivalence to the frozen verifiers remains a theorem to prove. Restoring equivalence with a representation-sensitive verifier is not a stronger stochastic autonomy claim, and this must be disclosed at the ceiling.

This diagnostic is an O obstruction only. C6, the package, AF, generic F and complete lineage all reject the zero-entry variant. Predictive classes read hazard lists in order without filtering weights. Duplicate-freedom and canonical ordering must **not** be added.
