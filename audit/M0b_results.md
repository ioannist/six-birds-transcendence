# FIACH-POS-02 preregistration evaluation

Computed from the frozen model with exact rational arithmetic. No stored verdict or status field is used as an outcome.

Declaration SHA-256: `27b4605224bd0040db97434c2570fa59716859d343736341c7d894b685bca97f`

Counts: **32 CONFIRMED, 2 CONFIRMED-NARROW, 1 CONFIRMED-CONFOUNDED, 4 FAILED, 1 INVALID-CONTROL, 0 UNDETERMINED**. Clean confirmed ablations: **20**.

C6 and C3 use stable finite-state partitions: equality of action-indexed outputs and successor classes at the fixed point implies equality for every finite disturbance word by induction. No word-length cutoff is used. C1 uses exact `Fraction` Gaussian elimination for the perturbed stationary law; C8 uses a greatest-fixed-point deletion of unsafe states.

| Prediction | Outcome | Deciding computation |
|---|---|---|
| `C1` | **FAILED** | pass=False; core_mass=2/3; threshold=3/4; well_formed=True |
| `C2` | **CONFIRMED** | pass=True; defect_count=18 |
| `C3` | **CONFIRMED** | pass=True; terminal_class_count=5; q_class_count=5 |
| `C4` | **CONFIRMED** | pass=True |
| `C5` | **CONFIRMED** | pass=True |
| `C6` | **CONFIRMED** | pass=True; future_counterexample=None |
| `C7` | **CONFIRMED** | pass=True; strict_refinement=True; recombination_class_count=2; well_formed=True |
| `C8` | **CONFIRMED** | pass=True; maximal_viable_size=6 |
| `TTH-03 bridge` | **CONFIRMED** | pass=True |
| `Route status` | **CONFIRMED** | pass=True; computed_status=route-indexed |
| `Corridor` | **CONFIRMED** | pass=True |
| `TTH-02 package at arrivals` | **FAILED** | pass=False |
| `TTH-05 preservation` | **FAILED** | pass=False |
| `TTH-04 composition` | **CONFIRMED** | pass=False |
| `TTH-06` | **FAILED** | pass=False; endpoint_link=True |
| `T17-I` | **CONFIRMED** | pass=False |
| `NEG-C6-CODE` | **CONFIRMED** | future_counterexample=['T-A0a', 'T-B0'] |
| `NEG-C6-HEALTH` | **CONFIRMED** | future_counterexample=['T-A1safe', 'T-A1warning'] |
| `NEG-C7-NO-JOINT-OBSERVABLE` | **CONFIRMED** | strict_refinement=False; R_classes=1; K_classes=1; local_well_formed=True |
| `NEG-C7-UNCOUPLED` | **INVALID-CONTROL** | strict_refinement=False; R_classes=1; K_classes=1; local_well_formed=False |
| `NEG-PKG-ENDPOINT` | **CONFIRMED-NARROW** | {"baseline_package_pass": false, "local_assignment_issues": ["C1 local assignment", "C1 global predicate"], "state": "T-A0a"} |
| `NEG-PKG-LATER` | **CONFIRMED-NARROW** | {"baseline_package_pass": false, "local_assignment_issues": ["C1 local assignment", "C1 global predicate"], "state": "T-A1safe"} |
| `NEG-C8-UNDERFUND` | **CONFIRMED** | pass=False; maximal_viable_size=0 |
| `NEG-BRIDGE-REP` | **CONFIRMED** | pass=False |
| `NEG-BRIDGE-EDGE` | **CONFIRMED** | pass=False |
| `NEG-ROUTE-ERASE` | **CONFIRMED** | pass=False; computed_status=unresolved |
| `NEG-CORRIDOR-DETACHED` | **CONFIRMED** | pass=False |
| `NEG-CORRIDOR-GAP` | **CONFIRMED** | pass=False |
| `NEG-TTH06-LINK` | **CONFIRMED** | endpoint_link=False |
| `NEG-C6-ORDER` | **CONFIRMED** | {"violations": [["T-A0a", "nominal", "nonpositive delta"], ["T-A0a", "nominal", "unfolded order"]]} |
| `NEG-C6-SUCCESSOR` | **CONFIRMED** | {"violations": [["T-B1safe", "hit", "missing response"]]} |
| `NEG-C6-TICK` | **CONFIRMED** | {"violations": [["T-A0a", "nominal", "tick phase"]]} |
| `NEG-C6-ARROW` | **CONFIRMED** | {"violations": [["T-A0a", "hit", "arrow owner"]]} |
| `NEG-C7-PRESERVATION` | **CONFIRMED-CONFOUNDED** | local_well_formed=False |
| `NEG-C1-CLOSURE` | **CONFIRMED** | closure_changed=True |
| `NEG-C2-SPLIT` | **CONFIRMED** | pass=False; defect_count=0 |
| `NEG-C3-PROFILE` | **CONFIRMED** | pass=False; terminal_class_count=6; q_class_count=5 |
| `NEG-C4-EXPOSE` | **CONFIRMED** | pass=False |
| `NEG-C5-SCHEDULE` | **CONFIRMED** | {"computed_credit": "other", "expected_change": "other", "products": {"other": [1, 0], "self": [0, 0]}, "protocol": "T-genuine"} |
| `NEG-C5-INTERNALIZED` | **CONFIRMED** | {"computed_credit": "ambiguous", "expected_change": "ambiguous", "products": {"other": [1, 0], "self": [1, 0]}, "protocol": "T-internal |

## Failures and undetermined results

### C1: FAILED

Computed evidence: `{"closure": {"all": {"extensive": true, "fixed_sets": 6, "idempotent": true, "max_defect": 1, "monotone": true, "sum_defect": "12"}, "nominal": {"extensive": true, "fixed_sets": 10, "idempotent": true, "max_defect": 1, "monotone": true, "sum_defect": "8"}}, "core_mass": "2/3", "stationary": {"T-A0a": "31/96", "T-A0b": "1/96", "T-A1safe": "1/6", "T-A1warning": "1/6", "T-B0": "1/6", "T-B1safe": "1/6"}, "threshold": "3/4"}`.

The exact perturbed stationary CORE mass is 2/3, below the preregistered 3/4 retention threshold. Closure laws pass, but this C1 surrogate fails its own retention subcheck; full P05 C1 was never claimed.

### TTH-02 package at arrivals: FAILED

Computed evidence: `{"assignment_issues": {"T-A0a": ["C1 global predicate"], "T-B0": ["C1 global predicate"]}, "pass": false}`.

Both arrival packages have valid local coordinate references, but their C1 global predicate fails. Therefore even the declared surrogate target package is not assembled at either arrival; TTH-02 cannot be promoted.

### TTH-05 preservation: FAILED

Computed evidence: `{"assignment_issues": {"T-A0a": ["C1 global predicate"], "T-A0b": ["C1 global predicate"], "T-A1safe": ["C1 global predicate"], "T-A1warning": ["C1 global predicate"], "T-B0": ["C1 global predicate"], "T-B1safe": ["C1 global predicate"]}, "pass": false}`.

All six state-indexed assignments inherit the failed C1 global predicate. The model does not establish preservation of a valid surrogate package along target runs.

### TTH-06: FAILED

Computed evidence: `{"endpoint_link": true, "pass": false, "recognition_value": "notAddressed", "source_package_issues": {"S-A0a": ["C1 global predicate"], "S-B0": ["C1 global predicate"]}, "staged_map": {"c7_transport": {"distribution_failures": [], "pass": true, "quotient_failures": [], "well_formed_issues": []}, "coordinate_failures": [], "pass": true}}`.

The distinct-carrier, endpoint, staged-map, route, corridor, bridge, C7, C8, and recognition checks do not repair the failed source/target C1 package lane. The predicted surrogate handoff is not established; full Temporal-FIACH remains beyond the declared ceiling.

## Qualified and invalid controls

`NEG-C7-UNCOUPLED` is **INVALID-CONTROL**: the quotient distinction collapses, but its unchanged crossed reassembly row disagrees with the new raw coupling. It cannot establish a negative on a well-formed uncoupled system.

`NEG-PKG-ENDPOINT` is **CONFIRMED-NARROW**: deleting `T-A0a` C1 `object_token` creates a local assignment failure, while the baseline arrival package already fails global C1 retention. It shows local deletion detection, not loss of a valid assembled package.

`NEG-PKG-LATER` is **CONFIRMED-NARROW**: deleting `T-A1safe` C1 `object_token` creates a local assignment failure, while baseline package preservation already fails global C1 retention. It shows local deletion detection, not loss of a valid preserved package.

`NEG-C7-PRESERVATION` is **CONFIRMED-CONFOUNDED**: joint-observable transport fails as predicted, but the mutated target assemblage also disagrees with its unchanged crossed reassembly row. The control detects a transport failure but does not isolate transport on a locally well-formed target.

## Mutation well-formedness, separate from target verdicts

| Mutation | Local well-formedness result | Target predicate result |
|---|---|---|
| `NEG-C6-CODE` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-C6-HEALTH` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-C7-NO-JOINT-OBSERVABLE` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-C7-UNCOUPLED` | C7: T-bound-crossed: reassembly coupling crossed disagrees with raw edges ((0, 0), (1, 1)); C1 Markov: well formed | INVALID-CONTROL |
| `NEG-PKG-ENDPOINT` | C7: well formed; C1 Markov: well formed | CONFIRMED-NARROW |
| `NEG-PKG-LATER` | C7: well formed; C1 Markov: well formed | CONFIRMED-NARROW |
| `NEG-C8-UNDERFUND` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-BRIDGE-REP` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-BRIDGE-EDGE` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-ROUTE-ERASE` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-CORRIDOR-DETACHED` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-CORRIDOR-GAP` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-TTH06-LINK` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-C6-ORDER` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-C6-SUCCESSOR` | C7: well formed; C1 Markov: missing row | CONFIRMED |
| `NEG-C6-TICK` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-C6-ARROW` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-C7-PRESERVATION` | C7: T-bound-crossed: reassembly coupling crossed disagrees with raw edges ((0, 0), (1, 1)); C1 Markov: well formed | CONFIRMED-CONFOUNDED |
| `NEG-C1-CLOSURE` | C7: well formed; C1 Markov: missing row | CONFIRMED |
| `NEG-C2-SPLIT` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-C3-PROFILE` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-C4-EXPOSE` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-C5-SCHEDULE` | C7: well formed; C1 Markov: well formed | CONFIRMED |
| `NEG-C5-INTERNALIZED` | C7: well formed; C1 Markov: well formed | CONFIRMED |

Qualified and invalid controls above are excluded from clean confirmations and clean ablations.


## Ambiguity log

- C1 CORE retention: use the unique stationary law of the epsilon-perturbed six-state Markov chain; compare its CORE mass with 3/4. The declaration does not specify a start distribution or an alternative retention statistic.
- C1 defect: symmetric-difference cardinality is an integer (equivalently an exact rational denominator 1), with no pass threshold; missing transitions make the separate Markov audit ill-formed.
- C3 continuation: compare the full finite-state output-equivalence fixed point, including present raw temporal values and action deltas, with computed q; no finite-word cutoff is used.
- C7 local consistency: require each reassembly row's actual coupling edges to equal its named admissible coupling map. This is the natural inverse-law reading of decomposition/reassembly; the declaration does not spell out the equation.
- C8 viability: require a safe response for every declared disturbance, as the spec says 'for each state and both disturbances'; this is a greatest fixed point, not a choice of one favorable action.
- Route current projection: exit_stage comes from the common corridor exit event; health/public/phase come from the arrival state. No stored declared_route_status is consulted.
- C6 tick phase: the declaration says every controller action toggles phase modulo two; the positive order_delta may be one or two and is not the tick increment. Check successor phase = current phase + 1 mod 2.
- Bridge frontier reachability: seed with states produced by reachable declared prehistory edges as well as source package arrivals, then close under source dynamics. This includes the distinct right-arrival history A0b.
- C4 declared continuation: test each one-step disturbance named in observation_interfaces.continuations and require an explicit differing output; the full future quotient alone is insufficient for this clause.

## Claim ceiling

Confirmed entries establish only the named exact finite computations on this declared toy. Any failed clause or lane blocks even the predicted surrogate handoff. No full P05 C-package, T17-I instance, full Temporal-FIACH theorem, or Lean-kernel certificate follows from this Python evaluation.
