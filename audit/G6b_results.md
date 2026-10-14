# G6b — TTH-06 lane controls, F and O

Exact standard-library computation on the frozen G6a declaration. F is primary full preservation of the declared graded package; O is supplementary C8 operational autonomy (N3). C4–C7 remain surrogates; the disturbance domain is only nominal. No physical or P05/T17-I claim.

## Counts and satisfiability

| Version | CONFIRMED | CONFIRMED-NARROW | CONFIRMED-CONFOUNDED | FAILED | INVALID-CONTROL | UNDETERMINED | Clean isolations |
|---|---|---|---|---|---|---|---|
| F | 13 | 0 | 0 | 0 | 0 | 0 | 2 |
| O | 12 | 0 | 0 | 0 | 0 | 0 | 3 |

Primary counts: twelve individual lane predictions per version, plus the separately disclosed AF→P prediction for F. Secondary predictions are listed and counted separately below. Expected P/AF joint rejection is not an F isolation or confounding. Qualified negative statuses are excluded from clean counts.

F positive satisfiability: **True**. AF→P: **CONFIRMED**.

For arbitrary raw m: AF requires a nonempty entry set E ⊆ SF and packageInside. Choose e in E. PackageAt(m,e) includes P(m), hence P(m). This is a direct logical implication under the fixed definitions, not a finite-family inference or a Lean proof.

## All primary predictions

| Version | Case | Lane | Predicted | Computed | Outcome |
|---|---|---|---|---|---|
| F | Baseline | P | True | True | CONFIRMED |
| F | Baseline | L | True | True | CONFIRMED |
| F | Baseline | AF | True | True | CONFIRMED |
| F | G6-PACKAGE-ONLY | P | False | False | CONFIRMED |
| F | G6-PACKAGE-ONLY | L | True | True | CONFIRMED |
| F | G6-PACKAGE-ONLY | AF | False | False | CONFIRMED |
| F | G6-LINEAGE-ONLY | P | True | True | CONFIRMED |
| F | G6-LINEAGE-ONLY | L | False | False | CONFIRMED |
| F | G6-LINEAGE-ONLY | AF | True | True | CONFIRMED |
| F | G6-WITHDRAWAL-ONLY | P | True | True | CONFIRMED |
| F | G6-WITHDRAWAL-ONLY | L | True | True | CONFIRMED |
| F | G6-WITHDRAWAL-ONLY | AF | False | False | CONFIRMED |
| O | Baseline | P | True | True | CONFIRMED |
| O | Baseline | L | True | True | CONFIRMED |
| O | Baseline | AO | True | True | CONFIRMED |
| O | G6-PACKAGE-ONLY | P | False | False | CONFIRMED |
| O | G6-PACKAGE-ONLY | L | True | True | CONFIRMED |
| O | G6-PACKAGE-ONLY | AO | True | True | CONFIRMED |
| O | G6-LINEAGE-ONLY | P | True | True | CONFIRMED |
| O | G6-LINEAGE-ONLY | L | False | False | CONFIRMED |
| O | G6-LINEAGE-ONLY | AO | True | True | CONFIRMED |
| O | G6-WITHDRAWAL-ONLY | P | True | True | CONFIRMED |
| O | G6-WITHDRAWAL-ONLY | L | True | True | CONFIRMED |
| O | G6-WITHDRAWAL-ONLY | AO | False | False | CONFIRMED |

## Isolation vectors

| Version | Control | Computed (P,L,A) | Interpretation | Status | Clean isolation |
|---|---|---|---|---|
| F | Baseline | (True, True, True) | positive satisfiability | CONFIRMED | False |
| F | G6-PACKAGE-ONLY | (False, True, False) | dependence consequence, not isolation | CONFIRMED | False |
| F | G6-LINEAGE-ONLY | (True, False, True) | isolation | CONFIRMED | True |
| F | G6-WITHDRAWAL-ONLY | (True, True, False) | isolation | CONFIRMED | True |
| O | Baseline | (True, True, True) | positive satisfiability | CONFIRMED | False |
| O | G6-PACKAGE-ONLY | (False, True, True) | isolation | CONFIRMED | True |
| O | G6-LINEAGE-ONLY | (True, False, True) | isolation | CONFIRMED | True |
| O | G6-WITHDRAWAL-ONLY | (True, True, False) | isolation | CONFIRMED | True |

## Secondary predictions

Counts: {'CONFIRMED': 13}.

| Prediction | Versions | Outcome | Computed witness |
|---|---|---|---|
| all-wellformed | F,O | CONFIRMED | `{"Baseline": {"issues": [], "missing_cells": [], "pass": true}, "G6-LINEAGE-ONLY": {"issues": [], "missing_cells": [], "pass": true}, "G6-PACKAGE-ONLY": {"issues": [], "missing_cells": ["publishedC"], "pass": true}, "G6-WITHDRAWAL-ONLY": {"issues": [], "missing_cells": [], "pass": true}}` |
| declared-disturbance-and-response-quantifier | F,O | CONFIRMED | `For every invariant state, each raw route context and nominal disturbance, search all actions and test full support.` |
| baseline-greatest-K-F | F | CONFIRMED | `{"entries": [{"budget": "1/1", "counter": 1, "factor": "p2w1", "probability": "1/1", "register": [["p1w0", "p2w1", "p1w0"], ["mix_1", "mix_2", "exit"]], "ticks": 1}, {"budget": "1/1", "counter": 1, "factor": "p2w1", "probability": "1/1", "register": [["p1w1", "p5w0", "p1w0"], ["mix_1", "mix_2", "exit"]], "ticks": 1}], "greatest": ["p0w0", "p0w1", "p1w0", "p1w1", "p2w1", "p3w0", "p3w1", "p4w0", "p4w1", "p5w0"], "responses": {"p0w0": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p0w1": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p1w0": {"route_a": {"nominal": ["cw"]}, "route_b": {"nominal": ["cw"]}}, "p1w1": {"route_a": {"nominal": ["ccw"]}, "route_b": {"nominal": ["ccw"]}}, "p2w1": {"route_a": {"nominal": ["stay"]}, "route_b": {"nominal": ["stay"]}}, "p3w0": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p3w1": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p4w0": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p4w1": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p5w0": {"route_a": {"nominal": ["stay"]}, "route_b": {"nominal": ["stay"]}}}}` |
| baseline-greatest-K-O | O | CONFIRMED | `{"entries": [{"budget": "1/1", "counter": 1, "factor": "p2w1", "probability": "1/1", "register": [["p1w0", "p2w1", "p1w0"], ["mix_1", "mix_2", "exit"]], "ticks": 1}, {"budget": "1/1", "counter": 1, "factor": "p2w1", "probability": "1/1", "register": [["p1w1", "p5w0", "p1w0"], ["mix_1", "mix_2", "exit"]], "ticks": 1}], "greatest": ["p0w0", "p0w1", "p1w0", "p1w1", "p2w1", "p3w0", "p3w1", "p4w0", "p4w1", "p5w0"], "responses": {"p0w0": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p0w1": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p1w0": {"route_a": {"nominal": ["cw"]}, "route_b": {"nominal": ["cw"]}}, "p1w1": {"route_a": {"nominal": ["ccw"]}, "route_b": {"nominal": ["ccw"]}}, "p2w1": {"route_a": {"nominal": ["stay"]}, "route_b": {"nominal": ["stay"]}}, "p3w0": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p3w1": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p4w0": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p4w1": {"route_a": {"nominal": ["stay", "cw", "ccw"]}, "route_b": {"nominal": ["stay", "cw", "ccw"]}}, "p5w0": {"route_a": {"nominal": ["stay"]}, "route_b": {"nominal": ["stay"]}}}}` |
| baseline-packageInside-every-state | F | CONFIRMED | `{"p0w0": true, "p0w1": true, "p1w0": true, "p1w1": true, "p2w1": true, "p3w0": true, "p3w1": true, "p4w0": true, "p4w1": true, "p5w0": true}` |
| baseline-canonical-response-witness | F,O | CONFIRMED | `{"p0w0": "stay", "p0w1": "stay", "p1w0": "cw", "p1w1": "ccw", "p2w1": "stay", "p3w0": "stay", "p3w1": "stay", "p4w0": "stay", "p4w1": "stay", "p5w0": "stay"}` |
| package-deletion-full-consequence | F | CONFIRMED | `{"SF": [], "map_total": false}` |
| package-deletion-operational-unchanged | O | CONFIRMED | `{"C2_C8": {"source": {"C2": true, "C3": true, "C4": true, "C5": true, "C6": true, "C7": true, "C8": true}, "target": {"C2": true, "C3": true, "C4": true, "C5": true, "C6": true, "C7": true, "C8": true}}, "SO": ["p0w0", "p0w1", "p1w0", "p1w1", "p2w1", "p3w0", "p3w1", "p4w0", "p4w1", "p5w0"]}` |
| lineage-only-raw-cell-and-audit | F,O | CONFIRMED | `{"changed_cells": ["eventTable"], "vertices": [["source_live", "source", 0], ["mix_1-source", "source", 1], ["mix_1-target", "target", 1], ["mix_2-target", "target", 2], ["exit-target", "target", 3]]}` |
| lineage-all-clause-and-route-side-effects | F,O | CONFIRMED | `{"clauses": {"source": {"C1": true, "C2": true, "C3": true, "C4": true, "C5": true, "C6": true, "C7": true, "C8": true}, "target": {"C1": true, "C2": true, "C3": true, "C4": true, "C5": true, "C6": true, "C7": true, "C8": true}}, "route": true}` |
| withdrawal-arrival-and-lineage-unchanged | F,O | CONFIRMED | `{"same_assignment": true}` |
| withdrawal-full-collapse | F | CONFIRMED | `{"SF": [], "withdrawn_C6_C8": {"C6": false, "C8": false}}` |
| withdrawal-operational-collapse | O | CONFIRMED | `{"budget": "1/1", "cost": "1/1", "next_budget": "0/1", "recharge": "0/1"}` |

## Computed invariants, packageInside, responses and entry

### Baseline

Well-formedness: {'pass': True, 'issues': [], 'missing_cells': []}.

**F:** greatest set `['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0']`; pruning `[['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0']]`; exact effective ledger `{'budget': '1/1', 'cost': '1/1', 'recharge': '1/1', 'next_budget': '1/1'}`.
Gates: `{'complete': True, 'withdrawal': True, 'nominal_domain': True, 'action_domain': True, 'nonempty_contexts': True, 'resource_closure': True, 'unit_positive_conserved_ledger': True, 'P_unchanged': True, 'nonempty_invariant': True, 'arrival_execution': True, 'endpoint_inside': True, 'total_responses': True, 'run_advancement': True, 'greatest_fixed_point': True, 'packageInside': True}`.
Responses (state → raw route context → nominal → admissible target-owned actions): `{'p0w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p0w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p1w0': {'route_a': {'nominal': ['cw']}, 'route_b': {'nominal': ['cw']}}, 'p1w1': {'route_a': {'nominal': ['ccw']}, 'route_b': {'nominal': ['ccw']}}, 'p2w1': {'route_a': {'nominal': ['stay']}, 'route_b': {'nominal': ['stay']}}, 'p3w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p3w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p4w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p4w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p5w0': {'route_a': {'nominal': ['stay']}, 'route_b': {'nominal': ['stay']}}}`.

packageInside state checks: `{'p0w0': True, 'p0w1': True, 'p1w0': True, 'p1w1': True, 'p2w1': True, 'p3w0': True, 'p3w1': True, 'p4w0': True, 'p4w1': True, 'p5w0': True}`.

**O:** greatest set `['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0']`; pruning `[['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0']]`; exact effective ledger `{'budget': '1/1', 'cost': '1/1', 'recharge': '1/1', 'next_budget': '1/1'}`.
Gates: `{'complete': True, 'withdrawal': True, 'nominal_domain': True, 'action_domain': True, 'nonempty_contexts': True, 'resource_closure': True, 'unit_positive_conserved_ledger': True, 'P_unchanged': True, 'nonempty_invariant': True, 'arrival_execution': True, 'endpoint_inside': True, 'total_responses': True, 'run_advancement': True, 'greatest_fixed_point': True}`.
Responses (state → raw route context → nominal → admissible target-owned actions): `{'p0w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p0w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p1w0': {'route_a': {'nominal': ['cw']}, 'route_b': {'nominal': ['cw']}}, 'p1w1': {'route_a': {'nominal': ['ccw']}, 'route_b': {'nominal': ['ccw']}}, 'p2w1': {'route_a': {'nominal': ['stay']}, 'route_b': {'nominal': ['stay']}}, 'p3w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p3w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p4w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p4w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p5w0': {'route_a': {'nominal': ['stay']}, 'route_b': {'nominal': ['stay']}}}`.

Both route entries after the actual canonical target step: `[{'factor': 'p2w1', 'probability': '1/1', 'register': [['p1w0', 'p2w1', 'p1w0'], ['mix_1', 'mix_2', 'exit']], 'counter': 1, 'ticks': 1, 'budget': '1/1'}, {'factor': 'p2w1', 'probability': '1/1', 'register': [['p1w1', 'p5w0', 'p1w0'], ['mix_1', 'mix_2', 'exit']], 'counter': 1, 'ticks': 1, 'budget': '1/1'}]`.

Atomic audit gates: `{'distinct_carriers': True, 'no_realized_gap': True, 'entry_exit_support': True, 'audited_mixed_support': True, 'audit_reachability': True, 'nonredundant_interventions': True, 'strict_path_updates': True, 'computed_route_status': True}`.
Bridge laws: `{'coverage': True, 'strict_edge': True, 'different_pasts': True, 'source_representatives': True, 'target_representatives': True, 'coordinate_map': True, 'successor_weights': True, 'order_progress': True, 'tick': True, 'record': True, 'route': True, 'maintenance': True, 'owner': True, 'full_future': True, 'raw_M_link': True, 'snapshot_codecs': True, 'snapshot_domain': True, 'snapshot_coordinate_map': True, 'codec_roundtrips': True, 'all_eight_snapshot_fields_transport': True}`.

### G6-PACKAGE-ONLY

Well-formedness: {'pass': True, 'issues': [], 'missing_cells': ['publishedC']}.

**F:** greatest set `[]`; pruning `[['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0'], []]`; exact effective ledger `{'budget': '1/1', 'cost': '1/1', 'recharge': '1/1', 'next_budget': '1/1'}`.
Gates: `{'complete': True, 'withdrawal': True, 'nominal_domain': True, 'action_domain': True, 'nonempty_contexts': True, 'resource_closure': True, 'unit_positive_conserved_ledger': True, 'P_unchanged': True, 'nonempty_invariant': False, 'arrival_execution': True, 'endpoint_inside': False, 'total_responses': False, 'run_advancement': True, 'greatest_fixed_point': True, 'packageInside': True}`.
Responses (state → raw route context → nominal → admissible target-owned actions): `{}`.

packageInside state checks: `{'p0w0': False, 'p0w1': False, 'p1w0': False, 'p1w1': False, 'p2w1': False, 'p3w0': False, 'p3w1': False, 'p4w0': False, 'p4w1': False, 'p5w0': False}`.

**O:** greatest set `['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0']`; pruning `[['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0']]`; exact effective ledger `{'budget': '1/1', 'cost': '1/1', 'recharge': '1/1', 'next_budget': '1/1'}`.
Gates: `{'complete': True, 'withdrawal': True, 'nominal_domain': True, 'action_domain': True, 'nonempty_contexts': True, 'resource_closure': True, 'unit_positive_conserved_ledger': True, 'P_unchanged': True, 'nonempty_invariant': True, 'arrival_execution': True, 'endpoint_inside': True, 'total_responses': True, 'run_advancement': True, 'greatest_fixed_point': True}`.
Responses (state → raw route context → nominal → admissible target-owned actions): `{'p0w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p0w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p1w0': {'route_a': {'nominal': ['cw']}, 'route_b': {'nominal': ['cw']}}, 'p1w1': {'route_a': {'nominal': ['ccw']}, 'route_b': {'nominal': ['ccw']}}, 'p2w1': {'route_a': {'nominal': ['stay']}, 'route_b': {'nominal': ['stay']}}, 'p3w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p3w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p4w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p4w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p5w0': {'route_a': {'nominal': ['stay']}, 'route_b': {'nominal': ['stay']}}}`.

Both route entries after the actual canonical target step: `[{'factor': 'p2w1', 'probability': '1/1', 'register': [['p1w0', 'p2w1', 'p1w0'], ['mix_1', 'mix_2', 'exit']], 'counter': 1, 'ticks': 1, 'budget': '1/1'}, {'factor': 'p2w1', 'probability': '1/1', 'register': [['p1w1', 'p5w0', 'p1w0'], ['mix_1', 'mix_2', 'exit']], 'counter': 1, 'ticks': 1, 'budget': '1/1'}]`.

Atomic audit gates: `{'distinct_carriers': True, 'no_realized_gap': True, 'entry_exit_support': True, 'audited_mixed_support': True, 'audit_reachability': True, 'nonredundant_interventions': True, 'strict_path_updates': True, 'computed_route_status': True}`.
Bridge laws: `{'coverage': True, 'strict_edge': True, 'different_pasts': True, 'source_representatives': True, 'target_representatives': True, 'coordinate_map': True, 'successor_weights': True, 'order_progress': True, 'tick': True, 'record': True, 'route': True, 'maintenance': True, 'owner': True, 'full_future': True, 'raw_M_link': True, 'snapshot_codecs': True, 'snapshot_domain': True, 'snapshot_coordinate_map': True, 'codec_roundtrips': True, 'all_eight_snapshot_fields_transport': True}`.

### G6-LINEAGE-ONLY

Well-formedness: {'pass': True, 'issues': [], 'missing_cells': []}.

**F:** greatest set `['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0']`; pruning `[['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0']]`; exact effective ledger `{'budget': '1/1', 'cost': '1/1', 'recharge': '1/1', 'next_budget': '1/1'}`.
Gates: `{'complete': True, 'withdrawal': True, 'nominal_domain': True, 'action_domain': True, 'nonempty_contexts': True, 'resource_closure': True, 'unit_positive_conserved_ledger': True, 'P_unchanged': True, 'nonempty_invariant': True, 'arrival_execution': True, 'endpoint_inside': True, 'total_responses': True, 'run_advancement': True, 'greatest_fixed_point': True, 'packageInside': True}`.
Responses (state → raw route context → nominal → admissible target-owned actions): `{'p0w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p0w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p1w0': {'route_a': {'nominal': ['cw']}, 'route_b': {'nominal': ['cw']}}, 'p1w1': {'route_a': {'nominal': ['ccw']}, 'route_b': {'nominal': ['ccw']}}, 'p2w1': {'route_a': {'nominal': ['stay']}, 'route_b': {'nominal': ['stay']}}, 'p3w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p3w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p4w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p4w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p5w0': {'route_a': {'nominal': ['stay']}, 'route_b': {'nominal': ['stay']}}}`.

packageInside state checks: `{'p0w0': True, 'p0w1': True, 'p1w0': True, 'p1w1': True, 'p2w1': True, 'p3w0': True, 'p3w1': True, 'p4w0': True, 'p4w1': True, 'p5w0': True}`.

**O:** greatest set `['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0']`; pruning `[['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0']]`; exact effective ledger `{'budget': '1/1', 'cost': '1/1', 'recharge': '1/1', 'next_budget': '1/1'}`.
Gates: `{'complete': True, 'withdrawal': True, 'nominal_domain': True, 'action_domain': True, 'nonempty_contexts': True, 'resource_closure': True, 'unit_positive_conserved_ledger': True, 'P_unchanged': True, 'nonempty_invariant': True, 'arrival_execution': True, 'endpoint_inside': True, 'total_responses': True, 'run_advancement': True, 'greatest_fixed_point': True}`.
Responses (state → raw route context → nominal → admissible target-owned actions): `{'p0w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p0w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p1w0': {'route_a': {'nominal': ['cw']}, 'route_b': {'nominal': ['cw']}}, 'p1w1': {'route_a': {'nominal': ['ccw']}, 'route_b': {'nominal': ['ccw']}}, 'p2w1': {'route_a': {'nominal': ['stay']}, 'route_b': {'nominal': ['stay']}}, 'p3w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p3w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p4w0': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p4w1': {'route_a': {'nominal': ['stay', 'cw', 'ccw']}, 'route_b': {'nominal': ['stay', 'cw', 'ccw']}}, 'p5w0': {'route_a': {'nominal': ['stay']}, 'route_b': {'nominal': ['stay']}}}`.

Both route entries after the actual canonical target step: `[{'factor': 'p2w1', 'probability': '1/1', 'register': [['p1w0', 'p2w1', 'p1w0'], ['mix_1', 'mix_2', 'exit']], 'counter': 1, 'ticks': 1, 'budget': '1/1'}, {'factor': 'p2w1', 'probability': '1/1', 'register': [['p1w1', 'p5w0', 'p1w0'], ['mix_1', 'mix_2', 'exit']], 'counter': 1, 'ticks': 1, 'budget': '1/1'}]`.

Atomic audit gates: `{'distinct_carriers': True, 'no_realized_gap': True, 'entry_exit_support': True, 'audited_mixed_support': False, 'audit_reachability': False, 'nonredundant_interventions': False, 'strict_path_updates': True, 'computed_route_status': True}`.
Bridge laws: `{'coverage': True, 'strict_edge': True, 'different_pasts': True, 'source_representatives': True, 'target_representatives': True, 'coordinate_map': True, 'successor_weights': True, 'order_progress': True, 'tick': True, 'record': True, 'route': True, 'maintenance': True, 'owner': True, 'full_future': True, 'raw_M_link': True, 'snapshot_codecs': True, 'snapshot_domain': True, 'snapshot_coordinate_map': True, 'codec_roundtrips': True, 'all_eight_snapshot_fields_transport': True}`.

### G6-WITHDRAWAL-ONLY

Well-formedness: {'pass': True, 'issues': [], 'missing_cells': []}.

**F:** greatest set `[]`; pruning `[['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0'], []]`; exact effective ledger `{'budget': '1/1', 'cost': '1/1', 'recharge': '0/1', 'next_budget': '0/1'}`.
Gates: `{'complete': True, 'withdrawal': True, 'nominal_domain': True, 'action_domain': True, 'nonempty_contexts': True, 'resource_closure': False, 'unit_positive_conserved_ledger': False, 'P_unchanged': True, 'nonempty_invariant': False, 'arrival_execution': True, 'endpoint_inside': False, 'total_responses': False, 'run_advancement': False, 'greatest_fixed_point': True, 'packageInside': True}`.
Responses (state → raw route context → nominal → admissible target-owned actions): `{}`.

packageInside state checks: `{'p0w0': False, 'p0w1': False, 'p1w0': False, 'p1w1': False, 'p2w1': False, 'p3w0': False, 'p3w1': False, 'p4w0': False, 'p4w1': False, 'p5w0': False}`.

**O:** greatest set `[]`; pruning `[['p0w0', 'p0w1', 'p1w0', 'p1w1', 'p2w1', 'p3w0', 'p3w1', 'p4w0', 'p4w1', 'p5w0'], []]`; exact effective ledger `{'budget': '1/1', 'cost': '1/1', 'recharge': '0/1', 'next_budget': '0/1'}`.
Gates: `{'complete': True, 'withdrawal': True, 'nominal_domain': True, 'action_domain': True, 'nonempty_contexts': True, 'resource_closure': False, 'unit_positive_conserved_ledger': False, 'P_unchanged': True, 'nonempty_invariant': False, 'arrival_execution': True, 'endpoint_inside': False, 'total_responses': False, 'run_advancement': False, 'greatest_fixed_point': True}`.
Responses (state → raw route context → nominal → admissible target-owned actions): `{}`.

Both route entries after the actual canonical target step: `[{'factor': 'p2w1', 'probability': '1/1', 'register': [['p1w0', 'p2w1', 'p1w0'], ['mix_1', 'mix_2', 'exit']], 'counter': 1, 'ticks': 1, 'budget': '1/1'}, {'factor': 'p2w1', 'probability': '1/1', 'register': [['p1w1', 'p5w0', 'p1w0'], ['mix_1', 'mix_2', 'exit']], 'counter': 1, 'ticks': 1, 'budget': '1/1'}]`.

Atomic audit gates: `{'distinct_carriers': True, 'no_realized_gap': True, 'entry_exit_support': True, 'audited_mixed_support': True, 'audit_reachability': True, 'nonredundant_interventions': True, 'strict_path_updates': True, 'computed_route_status': True}`.
Bridge laws: `{'coverage': True, 'strict_edge': True, 'different_pasts': True, 'source_representatives': True, 'target_representatives': True, 'coordinate_map': True, 'successor_weights': True, 'order_progress': True, 'tick': True, 'record': True, 'route': True, 'maintenance': True, 'owner': True, 'full_future': True, 'raw_M_link': True, 'snapshot_codecs': True, 'snapshot_domain': True, 'snapshot_coordinate_map': True, 'codec_roundtrips': True, 'all_eight_snapshot_fields_transport': True}`.

## Declared check coverage

| Check | Implementing function line | Conditions checked |
|---|---|---|
| P | `scripts/evaluate_tth06_lanes.py:391` | total typed map, value preservation, star cover/dependencies, edge compatibility, completeness, restrictions, coordinate views |
| P.C1-C8 | `scripts/evaluate_tth06_lanes.py:201` | assignment-scope completeness, row validity, reconstructed C1 audit, C2/C3 raw M and profiles, C4/C5/C7 surrogate checks, C6 and C8 |
| P.C6.trace | `scripts/evaluate_tth06_lanes.py:310` | strict events on realized supported paths, unit ticks, funding, writer and owner |
| P.C6.future | `scripts/evaluate_tth06_lanes.py:325` | defined raw-class probabilities/updater, full eight-component observation, finite one-step bisimulation and exact abstract closure with symbolic unbounded count |
| L.atomic | `scripts/evaluate_tth06_lanes.py:487` | actual event support expansion, realized stages, fixed audit vertices, reachability and both intervention projections, strict readout updates |
| L.bridge | `scripts/evaluate_tth06_lanes.py:487` | nonempty supported frontier and strict edge; different pasts; representative descent; raw successor, order/tick/progress/record/route/maintenance/owner equations; all four G1c snapshot pairs (afterFirst and endpoint on both routes), eight exact finite-image codecs and occurrence-wise coordinate-map checks |
| L.endpoint | `scripts/evaluate_tth06_lanes.py:487` | typed source/target terminal and last realized target exit event, receiver activation, raw class map |
| L.route | `scripts/evaluate_tth06_lanes.py:442` | nonempty raw tuple comparison domain, shared endpoint, activated realized funded step, resulting register and interpreted raw future-readout rule/owner |
| AF/AO.entry | `scripts/evaluate_tth06_lanes.py:423` | arrival activation, complete realized strict supported route; only the executed funded row yields entries |
| L.readout | `scripts/evaluate_tth06_lanes.py:410` | declared first/last phase selector and target ownership, applied to resulting register |
| AF/AO.response | `scripts/evaluate_tth06_lanes.py:616` | EVERY invariant state/route context/nominal disturbance, EXIST owned action, EVERY positive successor inside; exact positive conserved ledger and advancement |
| AF.packageInside | `scripts/evaluate_tth06_lanes.py:616` | BW withdrawn resources, recomputed assigned package, all state-view references, run laws; package-filtered greatest fixed point |
| AO.viability | `scripts/evaluate_tth06_lanes.py:616` | same withdrawn inputs, operational C8 greatest set without P/C1-C7 acceptance |
| AF/AO.greatest | `scripts/evaluate_tth06_lanes.py:377` | descending fixed point and independent all-subset containment check; support monotonicity argument |
| AF/AO.support | `scripts/evaluate_tth06_lanes.py:372` | nonempty exact stochastic row, scaled-integral positive mass and ALL successors inside |
| AF/AO.run | `scripts/evaluate_tth06_lanes.py:600` | positive conserved unit budget, writer, tick, owner; defined affine readouts and persistent register |
| wellformed | `scripts/evaluate_tth06_lanes.py:666` | raw syntax/references/stochastic rows, permitted typed absence distinct from package completeness |

## Failures, qualifications and scientific meaning

No failed, narrow, confounded, invalid or undetermined prediction.

F package deletion is expected dependence, not isolation: missing shared publishedC rejects source/target C1 completeness and map totality. It deletes evidence, not T1 dynamics. Withdrawal leaves the arrival package and pre-exit lineage fixed; continuing conserved positive funding fails, even though one prepaid action may be possible.

## Fixed-point and unbounded-word arguments

Descending pruning from K stabilizes because K is finite. Retention is monotone: adding allowed states cannot remove a support-safe response. State package validity and resource/ledger conditions do not depend on S. Every viable subset is retained through each iteration; the stabilized set is a fixed point and the greatest viable set. The evaluator additionally checks containment of all 1024 subsets, independently of the chosen number of prune rounds.

Full future sufficiency is a finite one-step weighted bisimulation on actual predictive classes, including exit classes and assigned tick increments. Code equality fixes the unbounded counter, tick phase, raw register, funding and owner. The defined observer and affine updater preserve this equality; induction gives equality of full eight-component word laws for every finite word, on all run states (hence the closure). No bounded horizon is used. Record and budget advancement follow the positive unit ledger and available writer; every supported response has all its successors in the invariant.

The source/target raw coordinate receiver and the designed route readout retain their pre-registration near-automatic disclosure. This evaluation does not upgrade those surrogates.

## Corrected declared-domain and phase checks

All four frozen G1c snapshot pairs are checked: route_a/route_b at afterFirst (occurrence 1, mix_1) and endpoint (occurrence 2, mix_2). Intermediate receiver-map coherence is required, in addition to all eight snapshot codec/transport equations; no terminal-only snapshot restriction remains.

Phase-2 entries exist only for an activated, realized, supported arrival route and an available actual funded target step. Arrival activation is independently gated in both AF and AO. A hypothetical receiver output without activation contributes no entries. Route readouts interpret the declared raw first/last selector and owner on the resulting register; unknown selectors are rejected.

## Ambiguity log

- **A1** StateViewsResolve/RunReadoutLawsAt are prose, not a new table. Use Substrate.viewScope: all ten state views share the clause cells. Resolve all 160 original coordinates; run readouts are the assigned C6 affine definitions, checked with positive unit ledger/writers across the unbounded closure. No state-varying verdict table is invented.
- **A2** The G4 positive adapter used positive-only atomicPosAvailable and fixed stage support. Recompute availability from assigned trace/funding/route data; expand vertices by actual event support. Keep the mix_2 audit selectors fixed. Source/target stage support follows the declared single-leg stage-position rule; missing audited event vertices reject.
- **A3** Run counters are unbounded; factor fixed points use K. Nominal responses have identity environment effects, and are safe across every raw positive outcome. An affine-update/bisimulation argument covers all counts and words; there is no horizon cutoff.
- **A4** Phase-2 entry requires arrival receiver activation and each complete realized strict route path, supported source history, funded target row and writer availability. Only that executed canonical target policy row contributes successors. Without activation or realization there are no entries; both autonomy versions explicitly gate on this prerequisite independently of withdrawal. Both routes and every resulting entry are checked, with no reset to the pre-probe factor.
- **A5** The F package is BW, with only target recharge availability changed. Arrival receiver/event/route facts remain historical evidence. Withdrawal removes current response dependencies, not the recorded acquisition history; C7 is not reactivated after withdrawal.
- **A6** AF→P is structurally implied by the declared PackageAt conjunction, nonempty entry and packageInside. The report gives this mathematical argument and checks every family member; it does not present Python sampling as a kernel proof of the universal theorem.
- **A7** Greatest sets are unordered subsets. Compute descending pruning to a fixed point and independently enumerate all 1024 subsets for containment; response monotonicity follows because only support containment depends on S.

## Gate-sensitivity self-test

Separate self-test status: **PASS**. These are group sensitivity probes, not exhaustive isolation of all obligations. Self-test failure never suppresses prediction reporting.

| Check | In-memory perturbation | Outcome |
|---|---|---|
| P.totality | remove shared publishedC cell | CAUGHT |
| P.C1 | change a canonical source row probability from 1/2 to 1/4 and its partner to 3/4 | CAUGHT |
| P.C2 | source lower readout becomes state_label (maps to target) | CAUGHT |
| P.C3 | source lower readout becomes state_label (maps to target) | CAUGHT |
| P.C4 | add canonical_M to shared current channels | CAUGHT |
| P.C5 | remove all source clockwise generator edges | CAUGHT |
| P.C6 | remove mix_1 from realized stage list | CAUGHT |
| P.C7 | remove source-present activation | CAUGHT |
| P.C8 | source recharge unavailable (maps to target) | CAUGHT |
| L.realization | un-realize mix_1 | CAUGHT |
| L.audit | delete mix_2 source support only | CAUGHT |
| L.strict_step | set mix_1 strict_step false | CAUGHT |
| L.full_future | set source p0w0/stay tick to 2; p0w1 stays 1 | CAUGHT |
| L.record | disable target route_a writer | CAUGHT |
| L.representatives | replace second representative history with first raw history | CAUGHT |
| L.route | erase raw register write | CAUGHT |
| L.activation | source absent at receiver | CAUGHT |
| L.owner | target resource owned by source | CAUGHT |
| L.snapshot_afterFirst | constant-position receiver keeps terminal p1 but corrupts both intermediate snapshot maps | CAUGHT |
| L.declared_route_readout | change the declared future readout from first history phase to last | CAUGHT |
| L.declared_route_owner | make the declared route readout source-owned | CAUGHT |
| AF.arrival_activation | source_present false before arrival; independently require no entry and failed autonomy | CAUGHT |
| AF.arrival_realization | un-realize mix_1 before phase-2 execution; require no entries | CAUGHT |
| AF.retention | retain no essential recharge resource | CAUGHT |
| AF.source_withdrawal | source remains present after withdrawal | CAUGHT |
| AF.role_withdrawal | external scheduler not removed | CAUGHT |
| AF.disturbance | empty disturbance domain | CAUGHT |
| AF.ledger | zero budget, cost and recharge | CAUGHT |
| AF.record | disable source route_a writer (maps to target) | CAUGHT |
| AF.tick | set source p0w0/stay tick to zero (maps to target) | CAUGHT |
| AF.owner | source resource owned by target (maps to wrong target owner) | CAUGHT |
| AF.missing_dependency | delete shared routeTable cell | CAUGHT |
| AO.arrival_activation | source_present false before arrival; independently require no entry and failed autonomy | CAUGHT |
| AO.arrival_realization | un-realize mix_1 before phase-2 execution; require no entries | CAUGHT |
| AO.retention | retain no essential recharge resource | CAUGHT |
| AO.source_withdrawal | source remains present after withdrawal | CAUGHT |
| AO.role_withdrawal | external scheduler not removed | CAUGHT |
| AO.disturbance | empty disturbance domain | CAUGHT |
| AO.ledger | zero budget, cost and recharge | CAUGHT |
| AO.record | disable source route_a writer (maps to target) | CAUGHT |
| AO.tick | set source p0w0/stay tick to zero (maps to target) | CAUGHT |
| AO.owner | source resource owned by target (maps to wrong target owner) | CAUGHT |
| AO.missing_dependency | delete shared routeTable cell | CAUGHT |
| AF.packageInside | remove shared publishedC cell | CAUGHT |
| AF/AO.full_support_safety | candidate invariant contains p1w0 but not p1w1; p2w1/stay has positive mass to both | CAUGHT |
| reporting.selftest_failure | self-test raises while outcomes remain available | CAUGHT |

Corrected-check witnesses:

- **L.snapshot_afterFirst**: `{'lineage': False, 'snapshot_domain': [{'route': 'route_a', 'position': 'afterFirst', 'occurrence': 1, 'event': 'mix_1'}, {'route': 'route_a', 'position': 'endpoint', 'occurrence': 2, 'event': 'mix_2'}, {'route': 'route_b', 'position': 'afterFirst', 'occurrence': 1, 'event': 'mix_1'}, {'route': 'route_b', 'position': 'endpoint', 'occurrence': 2, 'event': 'mix_2'}], 'coordinate_checks': [False, True, False, True]}`.
- **L.declared_route_readout**: `{'lineage': False, 'readout_spec': {'rule': 'phase of last source WheelState in retained raw route tuple after one funded target step', 'owner': 'target'}, 'readouts': [0, 0]}`.
- **L.declared_route_owner**: `{'lineage': False, 'readout_spec': {'rule': 'phase of first source WheelState in retained raw route tuple after one funded target step', 'owner': 'source'}, 'readouts': [None, None]}`.
- **AF.arrival_activation**: `{'autonomy': False, 'arrival_execution': False, 'entry_states': []}`.
- **AF.arrival_realization**: `{'autonomy': False, 'arrival_execution': False, 'entry_states': []}`.
- **AO.arrival_activation**: `{'autonomy': False, 'arrival_execution': False, 'entry_states': []}`.
- **AO.arrival_realization**: `{'autonomy': False, 'arrival_execution': False, 'entry_states': []}`.

## Reproduce

```bash
python3 -B scripts/evaluate_tth06_lanes.py audit/proposed_models/TTH06-LANES.model.json
python3 -B scripts/selftest_evaluate_tth06_lanes.py
python3 -B scripts/evaluate_tth06_lanes.py audit/proposed_models/TTH06-LANES.model.json --check-repeat
```

The repeat guard reruns the entire evaluation and self-test and compares JSON and Markdown bytes. No timestamp or process-dependent ordering is emitted. Frozen declarations and POS-04 files are read only.

## Supported ceiling

F primary: full preservation of the declared graded package (C4–C7 surrogates), with total target-owned nominal-environment responses and proof-structural lane evidence; AF implies P. O supplementary: narrower operational C8 viability (N3) with predicted logical lane independence. Neither claims P05/T17-I or physical continuation.

When confirmed, F supports satisfiability of graded packageInside and nominal-environment target-owned, probability-one-safe controlled responses, with separate package/lineage derivations and disclosed AF→P dependence. O supplies the three logical independence witnesses only for the narrower operational predicates. These are exact Python results pending G6c kernel proofs; no registry status is changed.
