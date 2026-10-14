# G6d-2 continuation 3: C1 decoder/operator/trace boundary

## Proved

This boundary adds five `Targets/GenericHandoff/POS04Objecthood*` modules.
The polymorphic `ObjecthoodRules` and `ObjecthoodCells` definitions remain
unchanged. Their carrier, action and outcome types are not fixed to POS-04.
The new modules specialize them; they do not introduce a replacement generic
rule restricted to ten states.

- **Quotient:** on arbitrary `Inputs` satisfying the existing raw
  `T1Anchors` and `TablesReconstructed` equations, the computed predictive
  partition equals imported M pairwise. The fiber sizes are consequently one
  or two. Thus rational uniform-fiber U agrees with the legacy scaled-integer
  U: the two-element-fiber fact is **derived**, not added as a premise.
  `rational_reconstruction` proves P/C/U reconstruction, including raw
  prototype order; `imported_CU` identifies their computed product.
- **Operators:** `E_matrix` and `Ezero_matrix` identify the generic computed
  operators with the exact T1 operators for every such input. The assigned
  corollary `assigned_operators` quantifies over arbitrary partial assignments
  whose actual assigned C1 gate holds. No positive table substitutes for a
  changed raw row.
- **Decoder:** `decoder_eq`, `gate_decode_iff`, and `accept_decode_iff` hold for
  **every partial assignment**, on both tags. The nine-view decoder returns
  `none` before any legacy decoder default can support acceptance when any
  consumed cell is absent. `scope_membership` identifies its scope exactly.
- **Trace:** `operation_reindex`, `reduction_reindex`, `normalized_reindex`,
  `candidate_reindex`, and `check_reindex` transport the complete normalized
  system and every raw row operation along the index bijection.
  `assigned_trace_check` transfers T1's checked reduction;
  `assigned_probability_fixed_unique` quantifies over **all** probability
  distributions, not a finite sample of displayed candidates.
  `assigned_candidate`, `assigned_nonuniform`, `assigned_core_mass`,
  `assigned_TV`, `assigned_eps_defect`, and `assigned_zero_defect` establish
  the generic readouts: the T1 candidate, nonuniformity, 77/80, 3/80,
  78795/524288 and 1/8. The rational defect formulas are kernel-computed after
  symbolic operator equality, rather than assuming a defect verdict.
- **Instance:** `canonical_raw_gate`, `canonical_raw_accept`, and
  `canonical_accept` instantiate the complete generic C1 evaluator on both
  POS-04 tags. `canonical_equivalence` links this instance to assigned C1.
- **Controls:** `control_outcomes` transfers the actual assignment mutations:
  C1-TABLE and C3-PROFILE accept source C1 and reject target C1; C2-SPLIT
  accepts C1 on both tags. Target rejection is through the changed canonical
  raw P row. C3's predictive partition is not claimed to change.

## Arguments and guards

| Argument | Classification |
|---|---|
| partial assignment and tag | raw data / namespace selection |
| typed bindings and raw specialization | defined from existing primitive cells and POS-04 schema |
| `T1Anchors`, `TablesReconstructed` | evidence of explicit raw protocol/table equations |
| index/state bijection and enumerations | checked structural data |
| T1 row operations | existing raw algebraic certificate, checked against the computed normalized system |
| P, classes, fibers, C/U/CU, perturbation, E, candidate and audit quantities | defined objects, never supplied |

| Field/readout | Check or link | Guard |
|---|---|---|
| nine consumed views (rows, positions, hazards, policy, prototypes, audit, published P/C/U) | `decoder_eq`, `scope_membership` | `missing_rejected`, for every consumed cell |
| canonical raw rows / policy | `P_readout`, `imported_P`, `P_matrix` | `table_control_target_rejected`, `profile_control_target_rejected`; generic `changed_P_rejected` |
| computed predictive partition and prototype order | `predictive_partition`, `C_readout`, `rational_reconstruction` | generic `missing_class_rejected`, `changed_C_rejected` |
| uniform fibers / U | `fiber_size`, `uniform_fiber_scaled`, `U_readout` | generic `changed_U_rejected` |
| scale, core, action coverage and positive weights | generic kernel/support checks, instantiated in `canonical_raw_gate` | generic `zero_scale_rejected`, `empty_core_rejected`, `leaking_core_rejected`, `omitted_action_rejected`, `zero_weight_rejected` |
| epsilon, tau and retention protocol | raw `T1Anchors`; `perturbed_matrix`, `E_matrix`, `Ezero_matrix` | missing audit cell; generic audit rejection lemmas |
| row operations and candidate | `check_reindex`, `assigned_trace_check` | existing verifier's normalized-system residual/identity checks; no uniqueness flag |
| nonuniformity, retention, TV and both defects | `assigned_*` audit theorems | generic uniform/retention/TV/defect rejection theorems |

The guard table reuses the committed generic guards. It does not claim a new
isolated sensitivity theorem for every POS-04 binding projection.

## Not yet proved / next boundary

**Full acceptance equivalence with legacy assigned C1 for arbitrary partial
assignments remains open.** The exact arbitrary-assignment decoder equivalences
above are not that theorem: their RHS is the decoded *generic* gate/acceptance.
The generic rule permits arbitrary raw audit protocols and comparison tables;
the POS-04 specialization must additionally check its published protocol and
prove the two directions between its kernel/quotient/support checks and the
legacy raw checks. These obligations must not be inferred from canonical truth.

C4/C5/C7 extraction and temporal/C8 extraction are untouched in this boundary.
The run-to-factor lift has not been claimed. The §7.4 stop rule remains binding:
any extra finite-context premise beyond G0/G6 must be reported before proceeding.
No registry, inventory, frozen model, or status changes occur here.

## Statement changes and checks

All new definitions/theorems are **(b) mathematical additions** for the generic
TTH-06 development. Existing declaration statements are unchanged; no (a)
renames and no row narrowing.

`cd lean && lake build`: green (366 jobs). Targeted builds: quotient ~8 s,
operator ~66 s, decoder ~96 s, trace ~18 s, instance ~9 s. No new-module warnings;
the full build replays existing CSTTT/vendor warnings.

`scripts/validate_lean.sh`: exit 0. The 77 new theorem axiom probes
use only `propext`, `Quot.sound`, and `Classical.choice` (or fewer).
The new-source forbidden-construct scan and `git diff --check` are clean.
Frozen `cst-tt/`, vendor files, and the inventory are unchanged.
