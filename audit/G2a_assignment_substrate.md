# G2a — assignment substrate and C1–C3

## Scope and statement changes

This implements the first review packet in `G2_assignment_refactor_scope.md`.
TTH-02 remains **conditional**. No registry, inventory, existing theorem statement,
frozen model, or CST-TT-08 file changes. All new definitions and theorem statements
below are **(b) mathematical additions** for TTH-02: assignment-sensitive semantics
and their locality, equivalence, reconstruction, and control proofs. They do not
replace the existing declarations or promote a full package claim.

Authority: frozen `M3_model_spec.md:17–19,30–31`. C1–C3 retain the substantive
**exact T1 factor component** grade. C4–C8 evaluation is reserved for G2b; their
namespace payloads here do not claim an implemented evaluator. The eventual
package retains C4–C7 surrogate ceilings.

## One namespace, one assignment

`Assigned/Substrate.lean` defines `Cell`, its dependent raw value type `Value`,
and `Assignment := (k : Cell) → Option (Value k)`. A cell stores a raw table,
rule enumerand, or resource record, never acceptance evidence. A table is a
single immutable cell; it is not copied into each state/clause slot.

The existing 160 `Coordinate`s are retained unchanged. `viewScope` maps each
slot to cells, and `resolveRef` maps every original primitive reference to the
same namespace. `view_references_resolve` proves all those pointers occur in
the view's scope. `views_160` retains completeness/distinctness of the logical
slots. `views_share_cells`, `shared_rows`, `global_P_shared`, and
`shared_reference_identity` prove sharing. Imported P/C/U/M references resolve
to global cells across both tags; action rows and lower rules are tag-specific.
The computed predictive M is **not** the stored published M reference: it is
`predictive`, calculated from assigned public positions and assigned action
supports labeled by assigned hazards.

Scopes are defined dependency closures, not supplied arguments of acceptance.
C1 reads rows, positions, hazards, canonical policy, ordered prototypes,
published P/C/U, and audit parameters. C2/C3 read rows, positions, hazards,
lower rule, and the published M fidelity reference. In particular, C2's old
reference list is closed under the action/hazard dependencies of its promoted
readout.

`decode scope assignment` returns the assignment on the scope and `none`
elsewhere. `decoder_locality` holds for **any scope and assignments** agreeing
there. `inputs_locality` lifts it to clause decoding. `Complete` rejects every
missing required cell. `inputs` uses canonical defaults solely to totalize
absent reads; acceptance always gates completeness first. Out-of-scope fields
in the common `Inputs` record are unused by that clause's algorithms, so they
cannot authorize a successful missing read. `decoder_outside`,
`dropped_scope_read`, `scope_deletion_rejected`, and the three universal
`c*_missing_rejected` theorems check this explicitly.

## Computed clause rules

### C1

`predictive`, `classOrder`, `fiberSize`, `rawC`, `rawU`, and `rowP` reconstruct
M, its ordered fibers, C, U, and the policy's P from assigned inputs.
`TablesReconstructed` checks the ordered prototype cover, reconstruction
against the assigned published tables, and CU multiplication.
`T1Anchors` separately identifies those comparison tables and audit parameters
with the exact T1 protocol. Raw class values never come from imported class
numbers. `RowsValid` checks positive support entries and the four-unit row
scale (empty rows are unavailable actions).

`computedP`, `computedPeps`, `computedCU`, `computedE`, and `computedEzero`
are definitions over decoded inputs. The epsilon formula is the exact T1
1/16 mixture; the tau and epsilon checks reject a different protocol rather
than pretending this fixed formula audits it. The CORE and candidate pi are
T1's published data. `C1Audit` quantifies over **all** probability distributions
fixed by the computed E, in addition to probability, fixedness, nonuniformity,
retention, TV, and both defects.

`reconstructed_matrices` proves equality of the computed P/Peps/CU with T1.
`c1_audit_from_reconstruction` then applies `T1Audit.pi_unique` and the other
L4 audit theorems to the computed matrices. No uniqueness flag is read.
`c1_accept_iff_gate` shows the universal audit is derived by the finite raw
reconstruction checks, not an independent hypothesis of acceptance.

### C2

`lower` runs the assigned public-channel rule. `predictive` runs the assigned
raw support/hazard rule. `C2Rule` checks the pinned `p1w0/p1w1` split.
`MLinked` checks the published reference and pairwise agreement of the
computed M with it. Acceptance is readiness, M linkage, and this computed
factorization defect. Missing inputs or invalid rows reject.

### C3

`seed`, `mass`, `signature`, `step`, `first`, and `second` run the iterative
public profile algorithm on assigned rows. `blockOf` retains the two distinct
ambient exit labels. `C3Rule` checks 6→7→7, stabilization, and terminal
agreement with computed M; its gate also checks linkage to imported M.
The K/action/exit domains, class-count algorithm, and weight scale are the
fixed finite T1 protocol, not freely supplied derived objects.

## Locality and canonical equivalence

For each clause there are both `c*_gate_locality` and
`c*_acceptance_locality` theorems. Their only premise is assignment agreement
on its defined scope. They follow from decoder locality; no accepted-value
parameter or independent locality verdict is stored.

`c1_canonical_equivalence`, `c2_canonical_equivalence`, and
`c3_canonical_equivalence` identify acceptance on the actual canonical
assignment with `C1FactorPass`, `C2Pass`, and `C3Pass` respectively.
`canonical_c123` transports the existing positive proofs on **both tags**.
`assigned_M_iff_imported` proves pairwise imported-M agreement.

## Mutation adapters and computed outcomes

`editRow` is an immutable raw single-row update; `editRow_other_cell` and
`editRow_other_row` establish its footprint. `negC1Table`, `negC2Split`, and
`negC3Profile` implement precisely the existing declared interventions.
`controls` is a compatibility adapter applying edits to the canonical
assignment. The acceptance functions do not receive its variant names.
`controls_rows` and `decoded_c1`/`decoded_c23_for` prove the raw-data bridge.

| Declared intervention | Source C1/C2/C3 | Target C1/C2/C3 | Proving theorem |
|---|---|---|---|
| None | pass/pass/pass | pass/pass/pass | `canonical_c123` |
| `NEG-C1-TABLE` | pass/pass/pass | fail/pass/pass | `neg_c1_table_outcomes` |
| `NEG-C2-SPLIT` | pass/fail/fail | pass/fail/fail | `neg_c2_split_outcomes` |
| `NEG-C3-PROFILE` | pass/pass/pass | fail/pass/pass | `neg_c3_profile_outcomes` |

This is C1–C3 coverage, not a claim about the other clauses/lanes.
`NEG-C3-PROFILE`'s failed prediction remains failed: C3 still holds, while the
changed canonical P row breaks C1. `c1_controls_equivalence` proves equivalence
to the legacy C1 predicate for the entire adapter family; C2/C3 adapter
equivalences cover the legacy profile/lower controls, and the separate C1-row
control is checked directly on all three evaluators.

## Argument classification

All names in the tables are in namespace `CSTTT.POS04.Assigned`.

| Argument | Classification | Role |
|---|---|---|
| `a, b : Assignment` | Raw data | Immutable optional typed primitive tables/records. |
| `tag : Tag`, `c : Clause`, `k : Cell` | Raw indices | Enumerated identities; no verdicts. |
| `scope : List Cell` in decoder/locality lemmas | Raw domain data | The generic decoder filters reads to it; acceptance instead uses **defined** `clauseScope`. |
| `h : Agrees scope a b` | Evidence on raw data | Pointwise equality on the declared scope. |
| Membership/inequality hypotheses in footprint/deletion lemmas | Evidence on raw data | Tested keys, scope membership, or exclusion of the edited row. |
| `d : Inputs` in reconstruction lemmas | Raw table representation | No proof fields. Acceptance always **defines** d by scoped decoding of a. |
| `ha : T1Anchors d`, `hr : TablesReconstructed d` | Evidence on raw data | Explicit raw table/parameter equations and reconstruction checks. |
| `v, p, l` in compatibility theorems | Raw intervention choices | Select the fixed declared raw edits; never parameters of acceptance. |
| New row/value in `put`, `editRow` | Raw data | Typed immutable edits used by controls and guards. |
| Scope closure, decoded inputs, M, profiles, C/U/P, E, verdicts | Defined objects | Computed functions; not supplied as candidate arguments to acceptance. |
| Fixed-point distribution mu in uniqueness conclusion | Universally quantified mathematical object | The theorem quantifies over **every** probability fixed distribution. |
| Lineage/autonomy evidence | Absent | No such input to this substrate or these clause acceptance functions. |

## Field coverage and guards

A guard corrupts just the named cell in the canonical assignment. Table entries
remain typed. The malformed-row guard also tests probability support validity.
These are sensitivity probes, not new model declarations or an exhaustive
isolation panel. All guards are Lean theorems.

| Raw field | Rule/gate constraining it | Guard theorem(s) |
|---|---|---|
| Optional availability of each scoped cell | `Complete` before acceptance | `c1_missing_rejected`, `c2_missing_rejected`, `c3_missing_rejected` (all assignments/required cells) |
| Scope of reads | `decode`, fixed dependency closure | `scope_deletion_rejected`, `dropped_scope_read` |
| Action rows (each tag) | `RowsValid`, policy P reconstruction, raw M, profile mass | `malformed_rows_gates_reject`; `c1_rows_guard`, `c2_rows_guard`, `c3_rows_guard` |
| Public position table | Computed M fibers and public profile seed | `c1_positions_guard`, `c2_positions_guard`, `c3_positions_guard` |
| Hazard table | Raw continuation labels, M linkage/reconstruction | `c1_hazards_guard`, `c2_hazards_guard`, `c3_hazards_guard` |
| Canonical action policy | P reconstruction from assigned action rows | `c1_policy_guard` |
| Ordered prototypes | Seven distinct covered classes and raw C column order | `c1_prototypes_guard` |
| Published P | T1 anchor **and** raw policy reconstruction | `c1_P_guard` |
| Published C | T1 anchor **and** ordered raw M indicator reconstruction | `c1_C_guard` |
| Published U | T1 anchor **and** raw M fiber-uniform reconstruction | `c1_U_guard` |
| Audit tau | Exact T1 protocol equality | `c1_tau_guard` |
| Audit epsilon | Exact T1 protocol equality | `c1_epsilon_guard` |
| Audit retention threshold | Exact T1 protocol equality and computed-pi retention | `c1_retention_guard` |
| Lower rule (each tag) | Pinned split / six-class profile seed | `c2_lower_guard`, `c3_lower_guard` |
| Published M reference | Imported-label fidelity and pairwise computed-M linkage | `c2_M_guard`, `c3_M_guard` |

Namespace typing, reference resolution, fixed algorithms/domains, and logical
view identities are **definitions**, not mutable fields accepted on an assumed
law. They therefore have no independent candidate argument to substitute.
Their coverage theorems are `view_references_resolve`, `views_160`,
`shared_reference_identity`, and decoder locality. Deleting a required cell or
required scoped read supplies the substrate's negative, rather than attempting
to corrupt a type definition. C4–C8 payloads are not read by C1–C3; their
semantic gates/guards belong to G2b. Coordinate/value maps and gluing belong
to G2c and are not claimed here.

## Self-review and remaining work

Premises → scoped decode → raw rule → computed matrix/profile → imported
mathematical theorem is explicit. No old package proof is conjoined with a
label check to manufacture assignment sensitivity. Changes to shared rows
reach all three evaluators. The exact T1 audit is a pinned-factor audit,
**not** a theorem for arbitrary stochastic objects or audit parameters.
C1 uniqueness is retained with its universal quantifier. The namespace's
function-valued raw tables are immutable data, not stored propositions.

G2b still needs C4–C8 decoding/evaluation and locality/equivalence. G2c still
needs mapped assignments, staged raw equations, gluing, locality transfer,
controls and the no-lineage/no-autonomy assembly signature. TTH-02 is not
promoted by this packet.

Verification receipts are appended after the final checks.

## Verification receipts

- `cd lean && lake build`: **exit 0**, 304 jobs. Recorded module builds:
  Substrate 1.9 s, C123 2.2 s, Adapters 17 s, Guards 3.5 s; root CSTTT 2.1 s.
  These are individual build receipts, not a clean total-wall-time benchmark.
  No warnings in the new modules; existing vendor/CSTTT linter warnings remain.
- `scripts/validate_lean.sh`: **exit 0**; 39 rows, 174 row declaration entries
  (165 theorem-kind, 8 statement-only, 1 other). Inventory matches. No untrusted
  axioms. No placeholders or high-confidence vacuity findings.
- The heuristic scan reports 13 ignored-input leads: the previous nine plus
  `flatPositions`, `noHazards`, `stayPolicy`, and `flatM` in Guards. These four
  deliberately construct constant raw-field sensitivity probes; their failed
  acceptance is proved above. They are not positive predicates or evidence.
- Independent of the unchanged registry probe, `/tmp/g2a_axioms.lean` imports
  CSTTT and runs `#check` and `#print axioms` on **all 81 new theorem names**.
  All resolve; the union of dependencies is only `propext`, `Quot.sound`,
  `Classical.choice`. Probe output: `/tmp/g2a_axioms.log`.
- Forbidden-token scan of `lean/CSTTT/POS04/Assigned/`: no matches.
- `git diff --check`: exit 0. The only existing file changed is CSTTT.lean's
  import addition; all implementation modules and this note are new files.
  Registry, inventory, frozen declarations/models, and existing Lean APIs are
  unchanged.

Validator JSON receipt:
`lean/.validate-logs/run-20260930T125153-071996Z/report.json` (gitignored).

Reproduce the build and registry validation:

```bash
(cd lean && lake build)
scripts/validate_lean.sh
(cd lean && lake env lean /tmp/g2a_axioms.lean)
```
