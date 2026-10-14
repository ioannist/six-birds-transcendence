# CST-TT-01 Exact Negative Kernel

**Phase:** CST-TT-01  
**Status:** frozen exact finite countermodels; no positive Temporal-FIACH witness attempted

## Result

The phase lands fifteen deterministic finite countermodels, covering all fourteen required execution-plan boundaries plus the already-frozen branchwise/recombination boundary `TTN-14`.

| ID | Boundary | TTN | Toy | Minimal size | Candidates | Status |
|---|---|---|---|---|---|---|
| CM-01 | Endpoint snapshot equality without temporal lineage | TTN-01 | TTM-02 | 2,0 | 16 | checked finite countermodel |
| CM-02 | Detached exact temporal copy | TTN-01 | TTM-02 | 2,2,1,0 | 192 | checked finite countermodel |
| CM-03 | Holonomy without endogenous arrow | TTN-03 | TTM-16 | 3 | 41 | checked finite countermodel |
| CM-04 | Externally scheduled temporal shadow | TTN-06 | TTM-04 | 2 | 746 | checked finite countermodel |
| CM-05 | Stable tick phase without genuine progress | TTN-07 | TTM-14 | 1,1 | 10 | checked finite countermodel |
| CM-06 | Current-equal but predictively different routes | TTN-04 | TTM-17 | 2,1 | 98 | checked finite countermodel |
| CM-07 | Nonzero clock-translation holonomy | TTN-05 | TTM-05 | 1,2 | 20 | checked finite countermodel |
| CM-08 | Local clause success without a global package witness | TTN-08 | TTM-11 | 2,1,2 | 34 | checked finite countermodel |
| CM-09 | Public/report-perfect collision with hidden mismatch | TTN-02 | TTM-12 | 2,1 | 98 | checked finite countermodel |
| CM-10 | Small scalar residual hiding a failed hard gate | TTN-10 | TTM-13 | 10,1 | 2046 | checked finite countermodel |
| CM-11 | Exact symmetric fork without an invariant unique selector | TTN-11 | TTM-07 | 2 | 33 | checked finite countermodel |
| CM-12 | Temporal gap followed by an equivalent resumed stream | TTN-09 | TTM-08 | 3 | 30 | checked finite countermodel |
| CM-13 | Finite successful trace without indefinite liveness | TTN-12 | TTM-10 | 3,1 | 15 | checked finite countermodel |
| CM-14 | Same-carrier re-encoding control | TTN-13 | TTM-15 | 1,2 | 18 | checked finite countermodel |
| CM-15 | Branchwise preservation without recombination preservation | TTN-14 | TFM-04 | 2,2 | 260 | checked finite countermodel |

## Consequences for the later constructive target

The bank freezes the following separations before any positive witness is tuned:

- endpoint or temporal-signature equality is not a strict episode relation;
- exact copying, target package success, and target autonomy can coexist with strict-corridor failure;
- route holonomy is not an endogenous arrow;
- externally scheduled motion is not post-withdrawal temporal autonomy;
- stable tick phase is not genuine progress;
- current equality can hide predictive route residue;
- nonzero clock-translation holonomy blocks one global canonical `now`;
- local clause validity does not guarantee global package gluing;
- public/report equality does not identify hidden package or predictive facts;
- scalar averages cannot override a failed hard gate;
- exact fork symmetry does not select one invariant branch;
- a resumed equivalent stream can remain separated by a temporal gap;
- finite success does not establish unbounded liveness;
- same-carrier re-encoding is not cross-carrier transport;
- branch marginals do not determine recombination structure.

The detached-copy witness directly checks kill criterion `K-FIACH-04`: under the frozen definitions it **fails** the strict overlap corridor, so the criterion is not triggered in this phase.

## Countermodels

### CM-01 — Endpoint snapshot equality without temporal lineage

**Boundary:** Endpoint/signature equality is insufficient for the strict episode relation.

**Exact witness:** `{"carrier_count": 2, "endpoint_equal": true, "operational_dependency_present": false, "source_target_distinct": true, "strict_temporal_lineage": false, "temporal_signature_equal": true}`

**Premises checked**

- `distinct_carriers`: `true`
- `endpoint_snapshot_equal`: `true`
- `temporal_signature_equal`: `true`

**Failed stronger conclusion**

- `strict_temporal_lineage_absent`: `true`

**Minimality:** size `[2, 0]` under `(carrier_count, operational_link_count)`. The deterministic search evaluated 16 candidates inside `carrier_count<=2; all three Boolean endpoint/link flags`; 8 were strictly smaller and none qualified. One carrier cannot instantiate a distinct source/target pair; two carriers suffice.

**Lean surface:** `CSTTT.Countermodels.cm01_endpointSnapshotEqualityWithoutLineage`. The explicit proof source is present; compilation is reported separately.
### CM-02 — Detached exact temporal copy

**Boundary:** Exact endpoint, package-like, and autonomy-like success do not imply a strict overlap corridor.

**Exact witness:** `{"carrier_count": 2, "copy_edges": 1, "exact_temporal_copy": true, "mixed_stage_count": 0, "source_and_target_endpoints_declared": true, "source_derived": true, "source_target_distinct": true, "stage_count": 2, "strict_overlap_corridor": false, "support_pattern": ["source", "target"], "target_package_pass": true, "target_post_copy_autonomous": true}`

**Premises checked**

- `distinct_carriers`: `true`
- `exact_temporal_endpoint_match`: `true`
- `source_and_target_endpoints_declared`: `true`
- `source_derived_copy`: `true`
- `target_autonomous_after_copy`: `true`
- `target_package_pass`: `true`

**Failed stronger conclusion**

- `strict_overlap_corridor_absent`: `true`

**Minimality:** size `[2, 2, 1, 0]` under `(carrier_count, stage_count, copy_edge_count, mixed_stage_count)`. The deterministic search evaluated 192 candidates inside `carrier_count<=2; stage_count<=3; one copy edge; one possible mixed stage; all endpoint flags`; 144 were strictly smaller and none qualified. Distinct transport needs two carriers; source derivation needs one copy edge; a detached model has zero mixed stages.

**Lean surface:** `CSTTT.Countermodels.cm02_detachedExactTemporalCopy`. The explicit proof source is present; compilation is reported separately.
### CM-03 — Holonomy without endogenous arrow

**Boundary:** Noncommuting reversible route updates do not supply an endogenous record arrow.

**Exact witness:** `{"endogenous_arrow": false, "nonzero_holonomy": true, "record_update": "constant", "route_a": [0, 2, 1], "route_b": [1, 0, 2], "routes_reversible": true, "state_count": 3, "witness_states": [0, 1, 2]}`

**Premises checked**

- `nonzero_route_holonomy`: `true`
- `route_updates_reversible`: `true`

**Failed stronger conclusion**

- `endogenous_arrow_absent`: `true`

**Minimality:** size `[3]` under `(state_count)`. The deterministic search evaluated 41 candidates inside `all ordered permutation pairs on 1..3 states`; 5 were strictly smaller and none qualified. Permutation groups on one and two points are abelian; three points are the first possible noncommuting case.

**Lean surface:** `CSTTT.Countermodels.cm03_holonomyWithoutArrow`. The explicit proof source is present; compilation is reported separately.
### CM-04 — Externally scheduled temporal shadow

**Boundary:** Runtime temporal progress maintained by an essential scheduler collapses after withdrawal.

**Exact witness:** `{"after_scheduler_withdrawal": [0, 1], "post_withdrawal_autonomous": false, "post_withdrawal_progress": false, "runtime_temporal_match": true, "state_count": 2, "support_is_essential": true, "supported_progress_states": [0, 1], "with_external_scheduler": [1, 0]}`

**Premises checked**

- `external_support_is_essential`: `true`
- `runtime_match_while_supported`: `true`

**Failed stronger conclusion**

- `autonomy_fails`: `true`
- `post_withdrawal_progress_fails`: `true`

**Minimality:** size `[2]` under `(state_count)`. The deterministic search evaluated 746 candidates inside `all deterministic supported/withdrawn transition tables on 1..3 states`; 1 were strictly smaller and none qualified. One state cannot exhibit nontrivial progress; two states suffice for supported motion and withdrawn stasis.

**Lean surface:** `CSTTT.Countermodels.cm04_externalSchedulerShadow`. The explicit proof source is present; compilation is reported separately.
### CM-05 — Stable tick phase without genuine progress

**Boundary:** Tick viability and phase stability do not imply temporal progress.

**Exact witness:** `{"genuine_progress": false, "phase": [0], "phase_count": 1, "phase_stable": true, "state_count": 1, "tick_viable": true, "transition": [0]}`

**Premises checked**

- `phase_stable`: `true`
- `tick_viable`: `true`

**Failed stronger conclusion**

- `genuine_progress_absent`: `true`

**Minimality:** size `[1, 1]` under `(state_count, phase_count)`. The deterministic search evaluated 10 candidates inside `all transition tables on <=2 states and <=2 phases`; 0 were strictly smaller and none qualified. A one-state, one-phase self-loop is the smallest stable system and already lacks progress.

**Lean surface:** `CSTTT.Countermodels.cm05_stableTickWithoutProgress`. The explicit proof source is present; compilation is reported separately.
### CM-06 — Current-equal but predictively different routes

**Boundary:** A present quotient can collide while a continuation probe separates routes; route memory repairs the collision.

**Exact witness:** `{"continuation_probe_output": [0, 1], "current_equal_predictive_mismatch": true, "current_observation": [0, 0], "current_symbol_count": 1, "flat": false, "hidden_state_count": 2, "memory_repair_separates_witness": true, "memory_retained_in_unaugmented_state": false, "route_memory": [0, 1], "witness_pairs": [[0, 1]]}`

**Premises checked**

- `current_classes_collide`: `true`

**Failed stronger conclusion**

- `predictive_equality_fails`: `true`
- `unaugmented_state_has_neither_memory_nor_flatness`: `true`

**Minimality:** size `[2, 1]` under `(hidden_state_count, current_symbol_count)`. The deterministic search evaluated 98 candidates inside `all current-observation and binary continuation-output maps on <=3 hidden states and <=2 public symbols`; 6 were strictly smaller and none qualified. At least two hidden states are required for a collision with different futures; one current symbol suffices.

**Lean surface:** `CSTTT.Countermodels.cm06_currentEqualPredictivelyDifferent`. The explicit proof source is present; compilation is reported separately.
### CM-07 — Nonzero clock-translation holonomy

**Boundary:** A nonzero cycle translation obstructs one route-independent global now.

**Exact witness:** `{"clock_modulus": 2, "global_time_potential_exists": false, "local_now_identity_route": 0, "local_now_loop_route": 1, "loop_source": 0, "loop_target": 0, "loop_translation": 1, "node_count": 1, "nonzero_translation_holonomy": true, "same_boundary_routes": true}`

**Premises checked**

- `nonzero_translation_holonomy`: `true`
- `same_route_boundary`: `true`

**Failed stronger conclusion**

- `global_time_potential_absent`: `true`
- `route_independent_now_absent`: `true`

**Minimality:** size `[1, 2]` under `(node_count, clock_modulus)`. The deterministic search evaluated 20 candidates inside `one or two nodes; cyclic clocks of modulus 1..4; all loop translations`; 1 were strictly smaller and none qualified. Modulus one has no nonzero translation; one node with a modulus-two loop is the smallest obstruction.

**Lean surface:** `CSTTT.Countermodels.cm07_noCanonicalGlobalNow`. The explicit proof source is present; compilation is reported separately.
### CM-08 — Local clause success without a global package witness

**Boundary:** Individually accepted local witnesses can disagree on a shared coordinate.

**Exact witness:** `{"all_local_clauses_accept": true, "clause_count": 2, "coordinate_count": 1, "global_package_witness_exists": false, "local_assignments_on_shared_coordinate": [0, 1], "overlap_compatible": false, "shared_coordinate": 0, "value_count": 2}`

**Premises checked**

- `every_local_clause_accepts`: `true`

**Failed stronger conclusion**

- `global_witness_absent`: `true`
- `overlap_compatibility_fails`: `true`

**Minimality:** size `[2, 1, 2]` under `(clause_count, coordinate_count, value_count)`. The deterministic search evaluated 34 candidates inside `1..3 clauses, 1..2 coordinates, 1..2 values, all shared-coordinate assignments`; 7 were strictly smaller and none qualified. One clause always glues; two clauses and two values are the first possible overlap disagreement.

**Lean surface:** `CSTTT.Countermodels.cm08_localGlobalObstruction`. The explicit proof source is present; compilation is reported separately.
### CM-09 — Public/report-perfect collision with hidden mismatch

**Boundary:** The same finite public report can be emitted by states with different hidden structural facts.

**Exact witness:** `{"hidden_structural_fact": [0, 1], "public_collision_hidden_mismatch": true, "public_observation": [0, 0], "public_symbol_count": 1, "state_count": 2, "witness_pairs": [[0, 1]]}`

**Premises checked**

- `public_or_report_collision`: `true`

**Failed stronger conclusion**

- `hidden_structural_identifiability_fails`: `true`

**Minimality:** size `[2, 1]` under `(state_count, public_symbol_count)`. The deterministic search evaluated 98 candidates inside `all observation maps and hidden Boolean facts on <=3 states and <=2 public symbols`; 6 were strictly smaller and none qualified. Two internal states are necessary for a collision with opposite hidden facts; one public symbol suffices.

**Lean surface:** `CSTTT.Countermodels.cm09_publicShadowCollision`. The explicit proof source is present; compilation is reported separately.
### CM-10 — Small scalar residual hiding a failed hard gate

**Boundary:** A mean binary defect at or below one tenth can coexist with a nonnegotiable failed gate.

**Exact witness:** `{"component_count": 10, "defect_sum": 1, "defect_vector": [0, 0, 0, 0, 0, 0, 0, 0, 0, 1], "every_hard_gate_passes": false, "failed_gate_indices": [9], "small_aggregate_residual": true, "small_residual_test": "10*1 <= 10", "threshold_denominator": 10, "threshold_numerator": 1}`

**Premises checked**

- `aggregate_residual_at_most_one_tenth`: `true`

**Failed stronger conclusion**

- `at_least_one_hard_gate_fails`: `true`

**Minimality:** size `[10, 1]` under `(component_count, failed_gate_count)`. The deterministic search evaluated 2046 candidates inside `all binary defect vectors of length 1..10`; 1023 were strictly smaller and none qualified. At a fixed one-tenth threshold, one failed binary gate needs at least ten components: 1/n <= 1/10 first holds at n=10.

**Lean surface:** `CSTTT.Countermodels.cm10_scalarResidualHardGateFailure`. The explicit proof source is present; compilation is reported separately.
### CM-11 — Exact symmetric fork without an invariant unique selector

**Boundary:** A fixed-point-free target-swap symmetry supports relation-valued branches but no invariant singleton choice.

**Exact witness:** `{"fixed_points": [], "invariant_singleton_selector_exists": false, "swap": [1, 0], "swap_is_involution": true, "symmetric_valid_fork": true, "target_count": 2, "valid_targets": [0, 1]}`

**Premises checked**

- `exact_fixed_point_free_symmetry`: `true`

**Failed stronger conclusion**

- `no_symmetry_invariant_unique_selector`: `true`

**Minimality:** size `[2]` under `(target_count)`. The deterministic search evaluated 33 candidates inside `all permutations on 1..4 targets`; 1 were strictly smaller and none qualified. A fixed-point-free symmetry needs at least two targets; the two-cycle is minimal.

**Lean surface:** `CSTTT.Countermodels.cm11_symmetryNoUniqueSelector`. The explicit proof source is present; compilation is reported separately.
### CM-12 — Temporal gap followed by an equivalent resumed stream

**Boundary:** Equivalent realized endpoints do not satisfy the strict no-gap temporal corridor when an internal stage is unrealized.

**Exact witness:** `{"endpoint_temporal_signatures_equal": true, "internal_temporal_gap": true, "stage_count": 3, "strict_no_gap_corridor": false, "temporal_realized_by_stage": [1, 0, 1]}`

**Premises checked**

- `equivalent_realized_endpoints`: `true`
- `explicit_internal_gap`: `true`

**Failed stronger conclusion**

- `strict_no_gap_corridor_absent`: `true`

**Minimality:** size `[3]` under `(stage_count)`. The deterministic search evaluated 30 candidates inside `all temporal-realization bit traces of length 1..4`; 6 were strictly smaller and none qualified. A source endpoint, an internal gap, and a target endpoint require at least three stages.

**Lean surface:** `CSTTT.Countermodels.cm12_gapResume`. The explicit proof source is present; compilation is reported separately.
### CM-13 — Finite successful trace without indefinite liveness

**Boundary:** A deterministic system can satisfy a nontrivial finite live prefix and still inevitably exhaust its budget.

**Exact witness:** `{"claimed_finite_horizon": 1, "eventual_failure_reached": true, "finite_horizon_success": true, "live_predicate": "budget>0", "maximum_budget": 2, "state_count": 3, "trace": [2, 1, 0, 0], "unbounded_liveness": false}`

**Premises checked**

- `nontrivial_finite_trace_succeeds`: `true`

**Failed stronger conclusion**

- `unbounded_liveness_fails`: `true`

**Minimality:** size `[3, 1]` under `(state_count, claimed_horizon)`. The deterministic search evaluated 15 candidates inside `countdown budgets 0..4 and horizons 1..3`; 6 were strictly smaller and none qualified. A one-transition live prefix followed by failure requires budgets 2->1->0, hence three states.

**Lean surface:** `CSTTT.Countermodels.cm13_finiteTraceNotUnbounded`. The explicit proof source is present; compilation is reported separately.
### CM-14 — Same-carrier re-encoding control

**Boundary:** A nonidentity representation map on one fixed carrier is not a distinct-carrier transport instance.

**Exact witness:** `{"carrier_count": 1, "distinct_carrier_transport": false, "nontrivial_reencoding": true, "reencoding_map": [1, 0], "representation_count": 2, "same_carrier": true}`

**Premises checked**

- `nontrivial_representation_change`: `true`
- `single_fixed_carrier`: `true`

**Failed stronger conclusion**

- `cross_carrier_typing_fails`: `true`

**Minimality:** size `[1, 2]` under `(carrier_count, representation_count)`. The deterministic search evaluated 18 candidates inside `one or two carriers; one to three representations; all representation permutations`; 1 were strictly smaller and none qualified. A nonidentity re-encoding needs two representations, while the negative control fixes one carrier.

**Lean surface:** `CSTTT.Countermodels.cm14_sameCarrierReencoding`. The explicit proof source is present; compilation is reported separately.
### CM-15 — Branchwise preservation without recombination preservation

**Boundary:** Two joint relations can have identical branch marginals while differing in their recombination structure.

**Exact witness:** `{"alphabet_size": 2, "every_branch_marginal_preserved": true, "joint_recombination_preserved": false, "source_marginals": [[0, 1], [0, 1]], "source_relation": [[0, 0], [1, 1]], "target_marginals": [[0, 1], [0, 1]], "target_relation": [[0, 1], [1, 0]]}`

**Premises checked**

- `both_branch_marginals_preserved`: `true`

**Failed stronger conclusion**

- `joint_recombination_differs`: `true`

**Minimality:** size `[2, 2]` under `(alphabet_size, maximum_joint_support_size)`. The deterministic search evaluated 260 candidates inside `all pairs of binary relations over alphabets of size 1..2`; 29 were strictly smaller and none qualified. A one-symbol alphabet or singleton support is determined by its marginals; two binary support points are minimal.

**Lean surface:** `CSTTT.Countermodels.cm15_branchwiseRecombinationFailure`. The explicit proof source is present; compilation is reported separately.


## Claim ceiling

Every result is an exact finite structural boundary. None establishes or refutes consciousness, phenomenal feeling, personal survival, numerical identity, A1, A2-P, certificate soundness, or empirical recognition.
