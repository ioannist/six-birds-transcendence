# FIACH-POS-03 preregistration evaluation

Computed from the committed declaration using exact rationals and finite fixed points. Stored prediction and status text was not used as a verdict.

Declaration SHA-256: `3e11f665fc139d7f56d357cb0cb1bb6538444c92f2e6dd3367dbccc2c42bf4b1`

## Headline

Outcomes: **35 CONFIRMED**, **2 CONFIRMED-NARROW**, **0 CONFIRMED-CONFOUNDED**, **4 FAILED**, **0 INVALID-CONTROL**, **0 UNDETERMINED**. Clean confirmed ablations: **23**.

C3 and C6 all-word claims use stable finite-state partitions, not a bounded horizon. `E₂` fixed spaces and defects use exact rational matrix operations.

## Prediction outcomes

| Prediction | Outcome | Deciding computation |
|---|---|---|
| `C1` | **FAILED** | CORE=T-A0a,T-A1safe,T-A1warning,T-B0,T-B1safe; Pε=95/96; E₂ε=5/6; E₂ε nonuniform=False; pass=False |
| `C2` | **CONFIRMED** | pass=True |
| `C3` | **CONFIRMED** | pass=True |
| `C4` | **CONFIRMED** | pass=True |
| `C5` | **CONFIRMED** | pass=True |
| `C6` | **CONFIRMED** | pass=True; future_sufficient=True |
| `C7` | **CONFIRMED** | pass=True; strict_refinement=True |
| `C8` | **CONFIRMED** | pass=True; maximal_viable_size=6 |
| `TTH-03 bridge` | **CONFIRMED** | pass=True |
| `Route status` | **CONFIRMED** | pass=True; computed_status=route-indexed |
| `Corridor` | **CONFIRMED** | pass=True |
| `TTH-02 package at arrivals` | **FAILED** | pass=False |
| `TTH-05 preservation` | **FAILED** | pass=False |
| `TTH-04 composition` | **CONFIRMED** | pass=False |
| `TTH-06` | **FAILED** | pass=False; endpoint_link=True |
| `T17-I` | **CONFIRMED** | pass=False |
| `NEG-C6-CODE` | **CONFIRMED** | {"future_counterexample": ["T-A0a", "T-B0"], "partition_rounds": 2} |
| `NEG-C6-HEALTH` | **CONFIRMED** | {"future_counterexample": ["T-A1safe", "T-A1warning"], "partition_rounds": 1} |
| `NEG-C7-NO-JOINT-OBSERVABLE` | **CONFIRMED** | strict_refinement=False; recombination_classes=1; local_well_formed=True |
| `NEG-C7-UNCOUPLED` | **CONFIRMED** | strict_refinement=False; recombination_classes=1; local_well_formed=True |
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
| `NEG-C7-PRESERVATION` | **CONFIRMED** | local_well_formed=True; observable_transport_failures=2; other_staged_issues=0 |
| `NEG-C1-CLOSURE` | **CONFIRMED** | {"closure_changed": true, "markov_well_formed": false, "missing_rows": [["T-A0a", "nominal"]]} |
| `NEG-C2-SPLIT` | **CONFIRMED** | pass=False |
| `NEG-C3-PROFILE` | **CONFIRMED** | pass=False |
| `NEG-C4-EXPOSE` | **CONFIRMED** | pass=False |
| `NEG-C5-SCHEDULE` | **CONFIRMED** | {"computed_credit": "other", "expected_change": "other", "products": {"other": [1, 0], "self": [0, 0]}, "protocol": "T-genuine"} |
| `NEG-C5-INTERNALIZED` | **CONFIRMED** | {"computed_credit": "ambiguous", "expected_change": "ambiguous", "products": {"other": [1, 0], "self": [1, 0]}, "protocol": "T-internalized"} |
| `NEG-C1-UNMAINTAINED-RECURRENCE` | **CONFIRMED** | CORE=T-A0a,T-A1safe,T-A1warning; Pε=21/32; E₂ε=1/2 |

## Exact C1 audit

T1 supports a recurrent/transient audit and `P² C U`, but does **not** prescribe this route-anchored union selector. Anchors on both route components can admit essentially all maintained recurrent states; passing `3/4` retention chiefly limits transient leakage and has limited object-selection force.

| Carrier | Computed CORE | Pε stationary mass | E₂ε fixed mass | Threshold | E₂ε unique | E₂ε nonuniform | δ(E₂⁰) | δ(E₂ε) |
|---|---|---:|---:|---:|---|---|---:|---:|
| source | `S-A0a, S-A1safe, S-A1warning, S-B0, S-B1safe` | `95/96` | `5/6` | `3/4` | True | False | `0` | `11625/131072` |

**source fixed distributions and components:** `{"E2_epsilon_fixed": {"S-A0a": "1/6", "S-A0b": "1/6", "S-A1safe": "1/6", "S-A1warning": "1/6", "S-B0": "1/6", "S-B1safe": "1/6"}, "E2_epsilon_fixed_space": {"affine_dimension": 0, "basis": [], "inconsistent": false, "particular": ["1/6", "1/6", "1/6", "1/6", "1/6", "1/6"], "simplex_constraint": "particular + sum(parameter_i * basis_i) >= 0 componentwise", "unique": true}, "E2_zero_fixed_space": {"affine_dimension": 3, "basis": [["-1", "-1", "1", "1", "0", "0"], ["-1/2", "-1/2", "0", "0", "1", "0"], ["-1/2", "-1/2", "0", "0", "0", "1"]], "inconsistent": false, "particular": ["1/2", "1/2", "0", "0", "0", "0"], "simplex_constraint": "particular + sum(parameter_i * basis_i) >= 0 componentwise", "unique": false}, "P_epsilon_stationary": {"S-A0a": "31/96", "S-A0b": "1/96", "S-A1safe": "1/6", "S-A1warning": "1/6", "S-B0": "1/6", "S-B1safe": "1/6"}, "components": [{"anchor_intersection": ["S-A0a"], "bottom_and_maintained": true, "reasons": [], "selected": true, "states": ["S-A0a", "S-A1safe", "S-A1warning"]}, {"anchor_intersection": [], "bottom_and_maintained": false, "reasons": ["outgoing support", "S-A0b/nominal: escapes component", "S-A0b/hit: escapes component"], "selected": false, "states": ["S-A0b"]}, {"anchor_intersection": ["S-B0"], "bottom_and_maintained": true, "reasons": [], "selected": true, "states": ["S-B0", "S-B1safe"]}]}`.

| target | `T-A0a, T-A1safe, T-A1warning, T-B0, T-B1safe` | `95/96` | `5/6` | `3/4` | True | False | `0` | `11625/131072` |

**target fixed distributions and components:** `{"E2_epsilon_fixed": {"T-A0a": "1/6", "T-A0b": "1/6", "T-A1safe": "1/6", "T-A1warning": "1/6", "T-B0": "1/6", "T-B1safe": "1/6"}, "E2_epsilon_fixed_space": {"affine_dimension": 0, "basis": [], "inconsistent": false, "particular": ["1/6", "1/6", "1/6", "1/6", "1/6", "1/6"], "simplex_constraint": "particular + sum(parameter_i * basis_i) >= 0 componentwise", "unique": true}, "E2_zero_fixed_space": {"affine_dimension": 3, "basis": [["-1", "-1", "1", "1", "0", "0"], ["-1/2", "-1/2", "0", "0", "1", "0"], ["-1/2", "-1/2", "0", "0", "0", "1"]], "inconsistent": false, "particular": ["1/2", "1/2", "0", "0", "0", "0"], "simplex_constraint": "particular + sum(parameter_i * basis_i) >= 0 componentwise", "unique": false}, "P_epsilon_stationary": {"T-A0a": "31/96", "T-A0b": "1/96", "T-A1safe": "1/6", "T-A1warning": "1/6", "T-B0": "1/6", "T-B1safe": "1/6"}, "components": [{"anchor_intersection": ["T-A0a"], "bottom_and_maintained": true, "reasons": [], "selected": true, "states": ["T-A0a", "T-A1safe", "T-A1warning"]}, {"anchor_intersection": [], "bottom_and_maintained": false, "reasons": ["outgoing support", "T-A0b/nominal: escapes component", "T-A0b/hit: escapes component"], "selected": false, "states": ["T-A0b"]}, {"anchor_intersection": ["T-B0"], "bottom_and_maintained": true, "reasons": [], "selected": true, "states": ["T-B0", "T-B1safe"]}]}`.

**Maintenance negative:** `{"E2_epsilon_core_mass": "1/2", "E2_epsilon_retained": false, "P_epsilon_core_mass": "21/32", "P_epsilon_retained": false, "components": [{"anchor_intersection": ["T-A0a"], "bottom_and_maintained": true, "reasons": [], "selected": true, "states": ["T-A0a", "T-A1safe", "T-A1warning"]}, {"anchor_intersection": [], "bottom_and_maintained": false, "reasons": ["outgoing support", "T-A0b/nominal: escapes component", "T-A0b/hit: escapes component"], "selected": false, "states": ["T-A0b"]}, {"anchor_intersection": ["T-B0"], "bottom_and_maintained": false, "reasons": ["T-B0/hit: external action or provenance owner"], "selected": false, "states": ["T-B0", "T-B1safe"]}], "core_state_ids": ["T-A0a", "T-A1safe", "T-A1warning"], "threshold": "3/4"}`.

This is a clean ablation of the **two retention subchecks**: both pass on the baseline and fail after the declared raw owner mutation. Baseline C1 already fails nonuniformity, so this negative does not demonstrate loss of a valid C1 package. The owner mutation also affects other clauses; those side effects are listed below.

## Failed, qualified, or undetermined predictions

### C1: FAILED

Computed evidence: `{"E2_epsilon_core_mass": "5/6", "E2_epsilon_nonuniform": false, "P_epsilon_core_mass": "95/96", "core_state_ids": ["T-A0a", "T-A1safe", "T-A1warning", "T-B0", "T-B1safe"]}`.

On each carrier, raw `P` has column sums `2` and `0` at the merged `A0a/A0b` q-class (and `1` at each other state). The computed `C U` averages that class, making `E₂^(1/16) = Pε² C U` doubly stochastic; every entry is strictly positive (the minimum is `31/1536`). Thus an attracting fixed distribution **does** exist and is unique, but it is uniform (`1/6` on each of six states). The pre-registered requirement for a **nonuniform** attracting distribution fails. Both retention checks pass (`95/96` and `5/6`), so changing CORE or its threshold cannot repair this failure. Even the declared C1 surrogate is not established.

### TTH-02 package at arrivals: FAILED

Computed evidence: `{"assignment_issues": {"T-A0a": ["C1 global predicate"], "T-B0": ["C1 global predicate"]}, "pass": false}`.

The arrival assignments pass their local references, but the target C1 global predicate fails because `E₂` is uniform. No valid surrogate target package is assembled, and full P05 package assembly remains outside the ceiling.

### TTH-05 preservation: FAILED

Computed evidence: `{"assignment_issues": {"T-A0a": ["C1 global predicate"], "T-A0b": ["C1 global predicate"], "T-A1safe": ["C1 global predicate"], "T-A1warning": ["C1 global predicate"], "T-B0": ["C1 global predicate"], "T-B1safe": ["C1 global predicate"]}, "pass": false}`.

Every target state has an assignment, but each inherits the failed C1 global predicate. The model does not establish state-indexed surrogate package preservation.

### TTH-06: FAILED

Computed evidence: `{"endpoint_link": true, "pass": false, "recognition_value": "notAddressed", "source_package_issues": {"S-A0a": ["C1 global predicate"], "S-B0": ["C1 global predicate"]}, "staged_map": {"c7_transport": {"distribution_failures": [], "pass": true, "quotient_failures": [], "well_formed_issues": []}, "coordinate_failures": [], "pass": true}}`.

Source and target C1 both fail nonuniformity, so the source-package and target-package lanes fail despite the other confirmed links. Even the surrogate handoff is not established.

### NEG-PKG-ENDPOINT: CONFIRMED-NARROW

Computed evidence: `{"baseline_package_pass": false, "local_assignment_issues": ["C1 local assignment", "C1 global predicate"], "state": "T-A0a"}`.

The preregistered outcome did not occur or the control has a narrower meaning; retain this result and do not revise POS-03.

### NEG-PKG-LATER: CONFIRMED-NARROW

Computed evidence: `{"baseline_package_pass": false, "local_assignment_issues": ["C1 local assignment", "C1 global predicate"], "state": "T-A1safe"}`.

The preregistered outcome did not occur or the control has a narrower meaning; retain this result and do not revise POS-03.

## Mutation well-formedness and side effects

| Mutation | Source C7 | Target C7 | Target C1 Markov | Other staged issues | Changed clauses/obligations |
|---|---|---|---|---|---|
| `NEG-C6-CODE` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C2": false, "C3": false, "C6": false}}, "changed_obligation_passes": {"Route status": false, "TTH-03 bridge": false}}` |
| `NEG-C6-HEALTH` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C3": false, "C6": false}}, "changed_obligation_passes": {"Route status": false}}` |
| `NEG-C7-NO-JOINT-OBSERVABLE` | True | True | True | 0 | `{"changed_clause_passes": {"source": {"C7": false}, "target": {"C7": false}}, "changed_obligation_passes": {}}` |
| `NEG-C7-UNCOUPLED` | True | True | True | 0 | `{"changed_clause_passes": {"source": {"C7": false}, "target": {"C7": false}}, "changed_obligation_passes": {}}` |
| `NEG-PKG-ENDPOINT` | True | True | True | 1 | `{"changed_clause_passes": {"source": {}, "target": {}}, "changed_obligation_passes": {}}` |
| `NEG-PKG-LATER` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {}}, "changed_obligation_passes": {}}` |
| `NEG-C8-UNDERFUND` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C6": false, "C8": false}}, "changed_obligation_passes": {}}` |
| `NEG-BRIDGE-REP` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {}}, "changed_obligation_passes": {"TTH-03 bridge": false}}` |
| `NEG-BRIDGE-EDGE` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {}}, "changed_obligation_passes": {"TTH-03 bridge": false}}` |
| `NEG-ROUTE-ERASE` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C2": false, "C3": false, "C6": false}}, "changed_obligation_passes": {"Route status": false, "TTH-03 bridge": false}}` |
| `NEG-CORRIDOR-DETACHED` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {}}, "changed_obligation_passes": {"Corridor": false, "Route status": false}}` |
| `NEG-CORRIDOR-GAP` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {}}, "changed_obligation_passes": {"Corridor": false}}` |
| `NEG-TTH06-LINK` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {}}, "changed_obligation_passes": {}}` |
| `NEG-C6-ORDER` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C3": false, "C6": false}}, "changed_obligation_passes": {}}` |
| `NEG-C6-SUCCESSOR` | True | True | False | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C6": false, "C8": false}}, "changed_obligation_passes": {}}` |
| `NEG-C6-TICK` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C3": false, "C6": false}}, "changed_obligation_passes": {"TTH-03 bridge": false}}` |
| `NEG-C6-ARROW` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C6": false, "C8": false}}, "changed_obligation_passes": {}}` |
| `NEG-C7-PRESERVATION` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {}}, "changed_obligation_passes": {}}` |
| `NEG-C1-CLOSURE` | True | True | False | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C3": false, "C6": false, "C8": false}}, "changed_obligation_passes": {"TTH-03 bridge": false}}` |
| `NEG-C2-SPLIT` | True | True | True | 2 | `{"changed_clause_passes": {"source": {}, "target": {"C2": false, "C4": false}}, "changed_obligation_passes": {"Route status": false}}` |
| `NEG-C3-PROFILE` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C1": true, "C3": false, "C6": false}}, "changed_obligation_passes": {"TTH-03 bridge": false}}` |
| `NEG-C4-EXPOSE` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C4": false}}, "changed_obligation_passes": {}}` |
| `NEG-C5-SCHEDULE` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C5": false, "C6": false}}, "changed_obligation_passes": {}}` |
| `NEG-C5-INTERNALIZED` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C5": false}}, "changed_obligation_passes": {}}` |
| `NEG-C1-UNMAINTAINED-RECURRENCE` | True | True | True | 0 | `{"changed_clause_passes": {"source": {}, "target": {"C6": false, "C8": false}}, "changed_obligation_passes": {}}` |

## Ambiguity log

- CORE maintenance: funded means a positive successor budget satisfying the raw ledger equation, with carrier-owned action, generator protocol, and required/regeneration resources. This applies the declared C8-style maintenance language to each bottom component.
- CORE selector: anchors are the source_arrivals.source_state and target_arrivals strings. Bottom SCCs use only positive edges of the unperturbed nominal/hit matrix; missing Markov rows make C1 ill-formed before retention is interpreted.
- T1-style C and U: C is the state-to-computed-q-class indicator and U is uniform on each realized q fiber; E₂=P²CU. At epsilon zero, report the exact affine fixed space with componentwise nonnegativity constraints rather than assuming uniqueness.
- C7 uncoupled: the crossed protocol remains admissible, but its reassembly row is deleted, so local consistency checks retained, realized reassembly rows only. Both assemblages remain in the refinement domain.
- C7 preservation: require both carriers locally well formed and no other staged/quotient failure before calling an observable-transport negative isolated.
- C1 defect: symmetric-difference cardinality is an integer (equivalently an exact rational denominator 1), with no pass threshold; missing transitions make the separate Markov audit ill-formed.
- C3 continuation: compare the full finite-state output-equivalence fixed point, including present raw temporal values and action deltas, with computed q; no finite-word cutoff is used.
- C7 local consistency: require each reassembly row's actual coupling edges to equal its named admissible coupling map. This is the natural inverse-law reading of decomposition/reassembly; the declaration does not spell out the equation.
- C8 viability: require a safe response for every declared disturbance, as the spec says 'for each state and both disturbances'; this is a greatest fixed point, not a choice of one favorable action.
- Route current projection: exit_stage comes from the common corridor exit event; health/public/phase come from the arrival state. No stored declared_route_status is consulted.
- C6 tick phase: the declaration says every controller action toggles phase modulo two; the positive order_delta may be one or two and is not the tick increment. Check successor phase = current phase + 1 mod 2.
- Bridge frontier reachability: seed with states produced by reachable declared prehistory edges as well as source package arrivals, then close under source dynamics. This includes the distinct right-arrival history A0b.
- C4 declared continuation: test each one-step disturbance named in observation_interfaces.continuations and require an explicit differing output; the full future quotient alone is insufficient for this clause.

## POS-02 versus POS-03

POS-02 retains its enumerated CORE and original C1 stationary test. POS-03 uses the declared recurrent, maintained, route-anchored CORE and adds the exact `E₂` audit. POS-02 regression output was compared byte-for-byte with the committed `M0b_results.json`; see the reproduce commands below.

| Model | Target CORE | Pε CORE mass | E₂ε CORE mass | Surrogate package at arrivals | Surrogate handoff |
|---|---|---:|---:|---|---|
| POS-02 | old enumerated | `2/3` | not declared | failed | failed |
| POS-03 | `T-A0a, T-A1safe, T-A1warning, T-B0, T-B1safe` | `95/96` | `5/6` | False | False |

The C7 uncoupled control changes from `INVALID-CONTROL` in POS-02 to a locally well-formed `CONFIRMED` negative in POS-03. The C7 preservation control changes from `CONFIRMED-CONFOUNDED` to an isolated `CONFIRMED` observable-transport negative. Both package-deletion controls remain `CONFIRMED-NARROW`, because C1 still fails.

## Claim ceiling

These are exact Python finite computations for the declared surrogate clauses and handoff obligations. A confirmed result supports only that declared finite ceiling. It does not supply a full P05 integrated package, T17-I, or Lean-kernel Temporal-FIACH proof.

## Reproduce

`python3 scripts/evaluate_fiach_pos02.py audit/proposed_models/FIACH-POS-03.model.json --json-out audit/M1b_results.json --md-out audit/M1b_results.md`

`python3 scripts/evaluate_fiach_pos02.py audit/proposed_models/FIACH-POS-02.model.json --json-out /tmp/POS02-regression.json --md-out /tmp/POS02-regression.md && cmp /tmp/POS02-regression.json audit/M0b_results.json`
