# G6d-2a continuation: generic C2/C3 rule seam

## Proved

`ProfileRules.lean` has no POS-04 or T1 dependency. State, action, outcome,
cell and dependent cell-value types are arbitrary. The raw schema declares
finite domains, outcome-to-state references, external block numbers, the ordered
block probe domain, the split pair, refinement depth and expected count audit.
`DomainCheck` checks complete, duplicate-free state/action/outcome enumerations.
It is part of the acceptance and gate predicates.

The decoder reads five typed primitive views: action rows, public positions,
hazards, label-exposure mode and comparison-class table. It returns an Option;
there is **no default** and no acceptance callback. Views may share cells.
Every consumed missing cell rejects both clauses and their gate
(`missing_consumed_cell`, `missing_cell_rejected`).

- C2 computes public lower and raw predictive readouts, then checks the declared
  split. `c2_nonfactorization` derives actual nonfactorization for the decoded
  inputs, quantifying over every proposed factor map.
- C3 iterates the raw profile algorithm at an arbitrary declared depth. Its
  audit checks initial/current/next counts, current/next partition equality and
  terminal predictive partition equality. Nothing requires ten states, seven
  classes, depth one or the 6→7→7 trajectory in the generic module.
- `RowsValid` recomputes positivity, outcome references and row totals;
  `Linked` compares the assigned class table against the declared reference
  table and against the computed predictive partition. Neither is a verdict cell.
- Decoder, gate and acceptance locality hold on the **computed five-view scope**.

`POS04ProfileRules.lean` instantiates the raw schema and bindings. Theorems
`generic_c2_iff` and `generic_c3_iff` quantify over **all assignments**, including
partial assignments, on both tags. They equate the complete generic evaluators
with the existing assigned C2/C3 acceptance predicates. Intermediate equations
identify lower/predictive readouts, seed, block mass, signatures, refinement
steps, scopes and successful decoding. No positive table replaces changed data.

`generic_canonical` supplies both positive instances. Control transfers:

| Assignment intervention | Source C2/C3 | Target C2/C3 | Theorem |
|---|---|---|---|
| NEG-C1-TABLE | pass/pass | pass/pass | `generic_table_control` |
| NEG-C2-SPLIT | fail/fail | fail/fail | `generic_exposed_control` |
| NEG-C3-PROFILE | pass/pass | pass/pass | `generic_profile_control` |

The failed C3 prediction remains recorded as passing C3. C1 control outcomes
remain in the committed `FixedPointAssignedT1` seam; these new transfers do not
claim additional C1 work.

## Arguments and guards

| Argument | Classification |
|---|---|
| State/action/outcome/cell/value types and equality instances | structural interface/evidence |
| schema domains, references, blocks, split, depth, count audit | raw audit data |
| typed primitive views and their projections | raw binding instructions |
| immutable assignment | raw data |
| locality equality and gate proofs | evidence on raw data |
| decoded record, classes, profiles, acceptance | defined objects; never supplied |

| Field family | Raw check or law | Guard |
|---|---|---|
| all five consumed cell views | Option decoding; exact scope locality | `missing_cell_rejected`, for every consumed cell |
| rows/weights/references | `RowsValid`; raw signature and predictive computation | `invalid_rows_rejected`; POS-04 `rows_guard` |
| positions | lower/seed/predictive computation and terminal partition check | POS-04 `positions_guard` |
| hazards | predictive readout and linked terminal partition | POS-04 `hazards_guard` |
| label exposure | lower and seed computation | `exposed_split_rejected`; `generic_exposed_control` |
| comparison-class table | `Linked`, against reference and computed partition | `changed_classes_rejected`; POS-04 `classes_guard` |
| finite domain | `DomainCheck` complete and duplicate-free | `missing_domain_state` |
| count audit | raw profile-count equations | `wrong_trajectory_rejected` |
| split/predictive distinction | computed lower equality and predictive inequality | `constant_predictive_rejected` |

The ordered blocks and external block numbers are explicit raw probe semantics,
matching the existing POS-04 algorithm even for arbitrary family assignments.
This seam does not establish that an arbitrary such probe lists every possible
semantic block, or that every schema has an accepted instance. Nor does the legacy assay
establish convergence at every depth: acceptance checks adjacent partition agreement
at the declared depth. Eddy supplied a depth-zero 2→2→2 instance that splits
into three classes one iteration later, so this does not certify stabilization.
Genuine fixed-point and block-coverage verification is a completion gate for
the enclosing layer, required before any TTH-06 promotion. Complete schema-level sensitivity coverage and the
continuation-coordinate integration remain for the enclosing rule layer.

Continuation 2 adds `StableProfile`: the computed second profile is exactly
fixed by one more raw refinement, and all positive row-support blocks are
covered for both compared profiles. `stable_forever` proves equality for every
subsequent iteration by induction. `canonical_genuine_stabilization` checks it
on both POS-04 tags. `unstable_rejected` and `omitted_block_rejected` are the
additional gates. The old `RecursiveProfile` and its arbitrary-family
equivalences are unchanged: they certify adjacent partition agreement only.
The enclosing layer must use the stronger gate before promotion, with the
remaining continuation-coordinate bridge still required.

## Not yet proved

The **full C1 primitive/decoder/reconstruction extraction** remains, beyond the
committed algebraic verifier and T1 assignment adapter. G6d-2b (C4/C5/C7),
G6d-2c (temporal/C8), and the enclosing RawHandoff clause layer remain. This is
a reviewable C2/C3 seam, not completion of G6d-2 or TTH-06 promotion.

No run-to-factor lift was used, and no new finite-context premise was introduced.
The §7.4 stop rule still applies before any generic finite viability claim.
No registry, inventory, model, existing clause statement or status changes.
All additions are **(b) mathematical additions** supporting generic TTH-06;
there are no (a) renames or weakenings of existing declarations.

## Checks

- `cd lean && lake build`: exit 0, **359 jobs**. Generic rule module about
  1–5 s; POS-04 equivalence module about 8–14 s across the incremental builds.
  No new warnings; existing replayed warnings remain.
- `/tmp/g6d2-profile-axioms.lean` through `lake env lean`: **55/55** new theorem
  probes clean; dependencies are a subset of the standard three.
- `scripts/validate_lean.sh`: exit 0, **PASS**, no issues. Receipt:
  `lean/.validate-logs/run-20261001T112327-786399Z/report.json`.
- Forbidden-construct scan of both new modules: no matches.
- `git diff --check`: clean. Only the two new modules, aggregate import and
  this note changed; frozen files and registry/inventory are unchanged.


## Continuation 2: C1 operator/decoder boundary

`ObjecthoodRules.lean` computes P from raw rows, destination references, policy
and a declared probability scale; C and U from the **computed** predictive
readout and the ordered prototypes (exact rational uniform fibers); CU, the
uniform perturbation, P^τ CU, and the unperturbed operator from these tables.
The fixed-point candidate is the checked trace's RHS, never a supplied vector.
TV and both defects use exact rational finite sums and maxima.

`KernelCheck`, `SupportCheck`, `QuotientCheck` and `Reconstruction` check normalization, finite
coverage, nonempty closed CORE, prototype coverage/first-occurrence ordering,
complete action coverage, positive raw weights, empty-or-normalized action rows,
and P/C/U comparison equations. `Accept` additionally checks nonuniformity,
retention, TV and the two defect targets. `accept_sound` and
`checked_probability_fixed_unique` derive universal uniqueness through the
committed verifier, about this **constructed operator**.

`ObjecthoodCells.lean` decodes nine typed views: rows, positions, hazards,
policy, prototypes, raw audit parameters, and the three published comparison
tables. Missing inputs reject before computation. Its generic decoder/gate/
acceptance locality and `accepted_unique` are proved. Views retain actual
shared cell identity. No distribution, operator, class function or uniqueness
flag is a decoder parameter.

| Arguments | Classification |
|---|---|
| Types/equality instances | structural interface/evidence |
| schema and nine typed views | raw domains/reference and binding instructions |
| assignment; policy/prototypes/parameters/comparison tables | raw data |
| gate/acceptance and equality proofs | evidence on computed raw checks |
| classes/fibers, P/C/U, operators, candidate, TV/defect | defined objects |

| Field family | Constraint / guard |
|---|---|
| all consumed views | `missing_input`, `missing_rejected`, for every cell |
| P/C/U comparison tables | `changed_P_rejected`, `changed_C_rejected`, `changed_U_rejected` |
| prototypes/predictive classes | quotient coverage/order; `missing_class_rejected` |
| probability scale | normalized raw P and all raw action rows; `zero_scale_rejected` |
| action alphabet/raw support | `SupportCheck`; `omitted_action_rejected`, `zero_weight_rejected` |
| enumeration/trace/perturbation/staging | `KernelCheck` and constructed E plus the committed verifier checks; `operator_congruence` |
| CORE | nonempty, included and P-closed; `empty_core_rejected`, `leaking_core_rejected` |
| candidate/nonuniformity | verified RHS; `uniform_candidate_rejected` |
| retention, TV, zero/perturbed defect targets | recomputed comparisons; `bad_retention_rejected`, `bad_TV_rejected`, `bad_zero_defect_rejected`, `bad_defect_rejected` |

These are **(b) additions**, not changes to old C1/2/3 statements. This is still
an extraction seam, not completion of generic C1: exact POS-04 canonical and
**arbitrary-family** decoder/reconstruction/audit equivalences and control
transfers remain. In particular the rational U fiber formula must be linked
honestly to the legacy scaled integer formula, and the actual CORE/staging
object must be linked to T1's audit. This seam does not claim a new concrete
nonempty C1 instance, automatic stochasticity of the full constructed operator,
or complete per-field sensitivity coverage of the enclosing C1 layer.

C4/C5/C7 and temporal/C8 remain. No run-to-factor lift or new finite-context
premise was introduced. §7.4 remains a stop gate. No status/inventory change.

Continuation checks:

- Final `cd lean && lake build`: **exit 0, 361 jobs**. C1 operator 1.6 s,
  C1 cells 1.8 s, POS-04 profiles about 16 s. No new warnings.
- `/tmp/g6d2-cont2-axioms.lean`: **83/83** theorem probes clean; the union
  is a subset of the standard three.
- Four-module forbidden-construct scan: no matches. `git diff --check`: clean.
- Final `scripts/validate_lean.sh`: **exit 0, PASS**; no issues or untrusted
  axioms, zero placeholders, zero high-confidence vacuity findings, 29
  nongating heuristic leads. Receipt:
  `lean/.validate-logs/run-20261001T115026-242487Z/report.json`.
  The additional lead is the intentionally constant `uniform` comparison vector;
  `uniform_candidate_rejected` checks that it cannot supply acceptance.
- Frozen science/model files, vendor, registry and inventory are unchanged.
