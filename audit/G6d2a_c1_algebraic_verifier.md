# G6d-2a first seam: checked generic fixed-point uniqueness

## Completed boundary and remaining scope

This is the explicitly permitted **C1 algebraic verifier split**, not completion
of G6d-2a/2b/2c. It proves a generic checked fixed-point theorem, instantiates it
on the exact T1 operator, and bridges it to reconstructed POS-04 assignment data.
The full polymorphic C1 primitive/decoder/reconstruction layer, C2/C3, C4/C5/C7,
and temporal/C8 clause extraction remain. TTH-06 stays **conditional**; no status,
inventory, registry, model, evaluator or existing clause definition changes.

All new definitions and theorems are **(b) mathematical additions**, supporting
TTH-06/C1. There are no (a) renames or changes to existing theorem statements.

## Generic construction and theorem

`Targets/GenericHandoff/FixedPointVerifier.lean` uses an arbitrary state type X,
a complete finite enumeration, and an exact rational matrix E. It has no T1 or
POS-04 dependency. Rational probability vectors match the scalar domain of L4
and `T1Audit`; this is not a new claim about a separately formalized real field.

For a raw anchor index, define the normalized square system by replacing that
stationary equation with the mass-one equation. The other rows are
`E[j,i] - δ[i,j]`. Its RHS is one at the normalization row and zero elsewhere.
Every probability fixed distribution satisfies this system
(`normalized_of_fixed`). The dropped stationary equation is still checked in
original-matrix residual validation; it is not dropped from the conclusion.

A raw trace comprises swap, scale and add operations. Each acts on both matrix
and RHS. `operation_preserves_solution` proves preservation for every symbolic
solution; `reduction_preserves_solution` inducts over the whole trace. The
candidate is **defined** as the resulting RHS. No candidate distribution or
inverse is supplied, and no uniqueness flag exists.

`check` rejects duplicate enumerations, then checks:

1. the reduced matrix is the identity, entry by entry;
2. the derived candidate is nonnegative at every state;
3. its total mass is one;
4. every original stationary equation holds for that candidate.

```lean
theorem check_sound (xs : List X) (hc : ∀ i, i ∈ xs)
    (E : Matrix X) (anchor : X) (ops : List (RowOperation X))
    (h : check xs E anchor ops = true) :
    Probability xs (candidate E anchor ops) ∧
    Fixed xs E (candidate E anchor ops) ∧
    (∀ x, Probability xs x → Fixed xs E x → x = candidate E anchor ops)
```

Completeness is structural evidence on the finite presentation. Nodup is
checked, not assumed. The proof transports an arbitrary fixed probability vector
through every raw operation, then uses the identity matrix and completeness to
identify every coordinate with the derived RHS. No finite enumeration of
probability vectors is attempted. Scale-zero operations are not independently
forbidden: the checker requires final identity and original residual anyway.
The theorem needs only sound forward preservation. A zero-scale corruption of
the T1 trace is explicitly rejected.

This verifier establishes probability, fixedness and uniqueness. It does **not**
alone establish stochasticity, nonuniformity, CORE retention, closure provenance,
P/C/U reconstruction, TV or defect. Those remain explicit C1 rule obligations;
none is silently replaced by a successful uniqueness check.

## T1 data, exact operation derivation and non-vacuity

`FixedPointT1.lean` defines its matrix from **T1Audit.E2eps.num/den**. It neither
stores a substitute matrix nor supplies π. The operation rule is fixed:
normalization anchor 0; columns in published order; first nonzero pivot; scale
to one; clear every other row in order. Applying this exact Gauss–Jordan rule
produces **35** operations. Their rational constants are algebraic consequences
of the already-published, kernel-computed matrix, not new model parameters.

`scripts/derive_t1_fixed_point_trace.py` reads Lean-evaluated T1 entries from a
probe under `/tmp`, uses standard-library `Fraction`, and compares the resulting
operations to the Lean trace. It writes no repository data. This is computation
on published T1, not evaluation of a newly designed model.

`FixedPointT1.checked` checks the whole certificate in the kernel.
`universal_unique` instantiates the generic soundness theorem. `probability_iff`
and `fixed_iff` equate the new definitions with T1Audit's actual definitions.
`candidate_eq_pi` applies the **generic** uniqueness theorem to T1's already
proved probability/residual facts; it does not use `T1Audit.pi_unique`.
`checked_uniqueness_in_T1_terms` proves that exact old uniqueness conclusion by
the new argument. `candidate_nonuniform` then reuses T1's nonuniformity proof.

Kernel computation uses `decide +kernel`, **not** native evaluation. Local
recursion/heartbeat bounds affect computation only. T1 module build receipts
are recorded below; this calculation required no stand-in.

## Assignment bridge and controls

`FixedPointAssignedT1.lean` is labelled **fixed-family specialization**, never
advertised as a generic C1 schema. `matrixFromInputs` reads the assignment's
computed E. `reconstructed_operator` and `matrix_link` derive equality with T1
from the actual raw P/C/U reconstruction and T1-anchor checks.

- `assigned_check`, `assigned_universal_unique`, `assigned_candidate_eq_pi`:
  checked candidate/probability/fixedness/uniqueness from reconstructed inputs.
- `assigned_uniqueness_legacy`, `assigned_audit_via_verifier`: the legacy C1
  audit, with uniqueness supplied by the generic verifier. The other components
  use their separate T1 proofs, not the old aggregate uniqueness proof.
- `VerifiedT1Accept`: existing computed C1Gate plus this checked trace.
- `verified_iff_legacy`: exact equivalence with C1Accept for **all** assignments
  and both tags, including partial assignments.
- `verified_locality`: uses the clause's actual scoped dependencies.
- `canonical_verified`: concrete positive instance on each tag.
- `missing_dependency_rejected`: every consumed C1 cell is rejected when absent,
  before decoder defaults can support any acceptance.

Transferred C1 outcomes are exact:

| Existing raw mutation | Source C1 | Target C1 | Transfer theorem |
|---|---|---|---|
| NEG-C1-TABLE | pass | fail | `neg_c1_table_transferred` |
| NEG-C2-SPLIT | pass | pass | `neg_c2_split_preserves_c1` |
| NEG-C3-PROFILE | pass | fail | `neg_c3_profile_c1_transferred` |

These state C1 outcomes only. They do not claim C2/C3 generic-rule extraction or
full cross-clause attribution. C1 table/profile mutations can fail reconstruction
rather than uniqueness; that distinction is retained.

## Argument classification

| Argument / object | Classification | Constraint |
|---|---|---|
| X and DecidableEq X | structural types/evidence | Arbitrary state alphabet; no fixed carrier |
| xs and hc | raw finite presentation / coverage evidence | Every state enumerated; duplicates checked before matrix work |
| E | raw rational matrix at verifier seam | Full C1 layer must define it from assigned kernel/quotient/perturbation data |
| anchor | raw system-presentation choice | Only normalization row selection; original residual still checks all rows |
| ops | raw verification trace | Every elementary operation is interpreted on constructed matrix and RHS |
| h: check = true | evidence on raw computation | Not a uniqueness assertion |
| arbitrary x, its probability/fixedness | quantified comparison vector and hypotheses | Never a candidate field or enumerated test sample |
| normalized system, reduced matrix/RHS, candidate | defined objects | Derived from E/anchor/ops |
| assignment/tag in specialization | raw fixed-family data | Actual scoped assignment, no positive replacement |
| C1Gate proof | evidence on assigned primitives | Completeness, raw rows, T1 anchors and P/C/U reconstruction |
| assigned matrix/candidate | defined objects | Computed from actual clause inputs |

## Field coverage and guards

| Field | Check/law | Guard |
|---|---|---|
| enumeration | coverage evidence, checked Nodup | `missing_enumeration_rejected`, `duplicate_enumeration_rejected` |
| raw E entries | normalized matrix and original residual | `changed_reduction_rejected`, T1 `zero_matrix_rejected` |
| normalization anchor | constructed system agrees with trace | T1 `changed_anchor_rejected` |
| trace operations/coefficients | symbolic operation law, checked final identity | T1 `empty_trace_rejected`, `zero_scale_rejected` |
| candidate probability/residual | derived RHS checked for each state and mass | `negative_candidate_rejected`, `bad_mass_rejected`, `bad_residual_rejected`; no free candidate can evade them |
| assigned primitive cells | existing raw reconstruction plus scope completeness | `missing_dependency_rejected` for **every** consumed cell; transferred table/profile failures |
| derived matrix and candidate | raw reconstruction equation | `matrix_link`, `assigned_candidate_eq_pi`; no alternate object argument |

These are sensitivity guards, not newly pre-registered physical controls.

## Remaining work and stop-rule receipt

Next is the complete generic C1 typed-cell rule/decoder/reconstruction layer,
then C2/C3 and the remaining G6d-2 schemas. This algebraic seam removes the
specific uniqueness obstacle; it does not make the remaining rule extraction
small or already proved. Scope estimates remain those of the accepted design.

The run-to-factor lift has **not been used**. No new finite-context hypothesis
has been introduced. G6d-2c must prove coverage of every response/resource-relevant
run context before finite viability is applied. If that requires a premise beyond
G0/G6, stop and report it for the owner rather than narrowing the theorem.

## Checks

Final receipts follow after the build, validator, trace derivation and axiom probes.

- `cd lean && lake build`: **exit 0**, 357 jobs. New module build times:
  verifier 1.8 s, T1 instance 6.2 s, assignment bridge 2.4 s. No new warnings;
  existing replayed warnings remain.
- `python3 -B scripts/derive_t1_fixed_point_trace.py`: **PASS**, all 35 exact
  operations match the declared deterministic rule.
- A `/tmp/g6d2-axioms.lean` probe imports CSTTT and prints axioms for **all 41
  new theorems** through `lake env lean`: 41/41 clean; union is a subset of
  `propext`, `Quot.sound`, `Classical.choice`.
- `scripts/validate_lean.sh`: **exit 0**, overall PASS. Receipt:
  `lean/.validate-logs/run-20261001T105320-040407Z/report.json`.
- Forbidden-construct scan of the three new modules: no matches.
- `git diff --check`: clean. Only the three new modules, derivation script,
  this audit note, and the aggregate import changed. Frozen files unchanged.
