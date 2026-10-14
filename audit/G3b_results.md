# G3b — exact route-license evaluation

## Outcome summary

**CONFIRMED: 20**, **CONFIRMED-NARROW: 0**, **CONFIRMED-CONFOUNDED: 0**, **FAILED: 0**, **INVALID-CONTROL: 0**, **UNDETERMINED: 0**

Clean ablations: **0**. There were no pre-registered mutations; sensitivity probes are separate evaluator tests.

All arithmetic is exact integer bit/group arithmetic. There are no probabilities, floats, or stored verdicts. All rewrite/completion reachability is saturated to a finite fixed point, not bounded by a word horizon.

| Prediction | Predicted | Computed | Outcome |
|---|---|---|---|
| N-DOMAIN | PASS | PASS | CONFIRMED |
| N-NORM | FAIL | FAIL | CONFIRMED |
| N-FLAT | FAIL | FAIL | CONFIRMED |
| N-CONF | FAIL | FAIL | CONFIRMED |
| N-EQUAL | PASS | PASS | CONFIRMED |
| N-DIFFERENT | PASS | PASS | CONFIRMED |
| N-LOOP | PASS | PASS | CONFIRMED |
| N-GLOBAL | FAIL | FAIL | CONFIRMED |
| N-CONVERSE | PASS | PASS | CONFIRMED |
| P0-NORM | PASS | PASS | CONFIRMED |
| P0-FLAT | PASS | PASS | CONFIRMED |
| P0-CONF | PASS | PASS | CONFIRMED |
| P0-EQUAL | PASS | PASS | CONFIRMED |
| P1-NORM | PASS | PASS | CONFIRMED |
| P1-FLAT | PASS | PASS | CONFIRMED |
| P1-CONF | PASS | PASS | CONFIRMED |
| P1-EQUAL | PASS | PASS | CONFIRMED |
| P-NONCONST | PASS | PASS | CONFIRMED |
| P-FUNCTION | PASS | PASS | CONFIRMED |
| P-CLOCK | PASS | PASS | CONFIRMED |

## Computed witnesses and counterexample scope

### TTH09-NECESSITY-01

Well-formedness: `{'pass': True, 'issues': []}`.

Executed functions on `[0,1]`: `{'r0': [0, 1], 'r1': [0, 1], 'r2': [1, 0]}`.

Endpoints: `{'r0': 0, 'r1': 0, 'r2': 1}`; clock translations: `{'r0': 0, 'r1': 0, 'r2': 1}`.

- `D`: DomainCheck `True`; licenses `{'normalization': False, 'flatness': False, 'confluence': False}`.
- Rewrite terminal sets: `{'r0': ['r0'], 'r1': ['r1'], 'r2': ['r2']}`; completion terminal sets: `{'r0': ['r0'], 'r1': ['r1'], 'r2': ['r2']}`.
- Critical-pair holonomy: `{'r0/r1': 0, 'r0/r2': 1, 'r1/r2': 1}`; completed-pair holonomy: `{}`.
- Failed license gates: `{'normalization': ['shared_unique_normal_form'], 'flatness': ['completion_covers', 'completion_connected', 'completion_shared_unique_normal_form'], 'confluence': ['all_pairs_joinable']}`.

### TTH09-LICENSE-01

Well-formedness: `{'pass': True, 'issues': []}`.

Executed functions on `[0,1]`: `{'a0': [0, 1], 'a1': [1, 0], 'n0': [0, 1], 'n1': [1, 0]}`.

Endpoints: `{'a0': 0, 'a1': 1, 'n0': 0, 'n1': 1}`; clock translations: `{'a0': 0, 'a1': 1, 'n0': 0, 'n1': 1}`.

- `D0`: DomainCheck `True`; licenses `{'normalization': True, 'flatness': True, 'confluence': True}`.
- Rewrite terminal sets: `{'a0': ['n0'], 'n0': ['n0']}`; completion terminal sets: `{'a0': ['n0'], 'n0': ['n0']}`.
- Critical-pair holonomy: `{'a0/n0': 0}`; completed-pair holonomy: `{'a0/n0': 0}`.
- Failed license gates: `{'normalization': [], 'flatness': [], 'confluence': []}`.

- `D1`: DomainCheck `True`; licenses `{'normalization': True, 'flatness': True, 'confluence': True}`.
- Rewrite terminal sets: `{'a1': ['n1'], 'n1': ['n1']}`; completion terminal sets: `{'a1': ['n1'], 'n1': ['n1']}`.
- Critical-pair holonomy: `{'a1/n1': 0}`; completed-pair holonomy: `{'a1/n1': 0}`.
- Failed license gates: `{'normalization': [], 'flatness': [], 'confluence': []}`.

**The necessity control stands**: DomainCheck passes, r0/r1 execute to the same bit, and all three adopted licenses fail on the fixed whole domain D.

This is a counterexample to literal necessity of these licenses on the predeclared comparison domain. It does not assert license failure on every smaller domain or under every alternative license definition. Flatness here is the stronger adopted G3a license, including completion-rank and unique-normal-form conditions beyond G0. The necessity control already fails the G0 covering-completion/connectivity requirements, not only those added conditions.

## Failures and declaration errors

No failed or undetermined predictions. No frozen declaration error was found.

## Ambiguity log

- Critical pairs are filtered by boundary using either side, then BOTH sides must belong to the domain and share its boundary. A malformed cross-boundary pair cannot disappear merely because its other side has the wrong boundary.
- Completion records with a side on the domain boundary are all checked, including duplicates. An extra invalid completion cannot be ignored after a valid one is found.
- Flatness condition 6 ranges over completed critical pairs. With no completions its zero-holonomy subcheck is vacuously true; the nonempty covering-completion and connectivity gates still reject. Holonomy of ALL declared critical pairs is reported separately, including the necessity model toggle comparison.
- Unique/shared normal form means singleton terminal-reachability sets for every route, with the same singleton across the fixed domain. Completion reductions omit identity edges, as prescribed; reflexive one-vertex completion paths are valid.
- Raw event action/clock coherence checks every available event in the model, following the spec global quantifier, not just events appearing in one comparison.
- License evaluation stays on each predeclared same-boundary domain. Positive nonconstancy across boundaries is tested separately and is not a cross-boundary license.

## Gate-sensitivity self-test

Self-test status: **PASS**. 34/34 sensitivity probes caught; all license gates covered; both reporting-method guards passed.

Self-test status is independent of prediction outcomes. An unavailable baseline or failed test does not suppress computed outcomes.

Each probe mutates a fresh in-memory positive-model copy. These are **group-sensitivity probes**, not exhaustive isolation of every conjunct: some coordinated consequences break more than one gate. Each named subcheck and its enclosing license must fail. Frozen files are never edited.

| Gate | Raw perturbation | Well-formed | Result |
|---|---|---|---|
| domain.multiple_routes | D0 keeps only a0 | True | CAUGHT |
| domain.no_duplicates | append repeated a0 to D0 | True | CAUGHT |
| domain.admissible | make e_a0 unavailable | True | CAUGHT |
| domain.boundary_members | change a0 boundary to b1 | True | CAUGHT |
| domain.rewrite_closed | add raw rewrite a0 → a1 outside D0 | True | CAUGHT |
| domain.multiple_routes | give a0 the identical raw event path as n0 | True | CAUGHT |
| domain.no_duplicates | give a0 the identical raw event path as n0 despite different IDs | True | CAUGHT |
| flatness.critical_members_distinct | give a0 the identical raw event path as n0 | True | CAUGHT |
| normalization.domain | make e_a0 unavailable | True | CAUGHT |
| flatness.domain | make e_a0 unavailable | True | CAUGHT |
| confluence.domain | make e_a0 unavailable | True | CAUGHT |
| normalization.rewrite_boundary | add cross-domain raw rewrite a0 → a1 | True | CAUGHT |
| normalization.rank_decreases | cap a0 rank at zero | True | CAUGHT |
| normalization.rewrite_actions | change e_a0 action to toggle | True | CAUGHT |
| normalization.shared_unique_normal_form | delete a0 → n0 rewrite | True | CAUGHT |
| confluence.rewrite_boundary | add cross-domain raw rewrite a0 → a1 | True | CAUGHT |
| confluence.rewrite_actions | change e_a0 action to toggle | True | CAUGHT |
| confluence.all_pairs_joinable | delete a0 → n0 rewrite | True | CAUGHT |
| flatness.event_clock_coherence | change e_a0 clock increment to 1 | True | CAUGHT |
| flatness.critical_nonempty | delete the D0 critical pair | True | CAUGHT |
| flatness.critical_members_distinct | replace D0 pair by a0/a0 | True | CAUGHT |
| flatness.critical_covers | replace D0 pair by a0/a0, leaving n0 uncovered | True | CAUGHT |
| flatness.completion_covers | delete D0 completion | True | CAUGHT |
| flatness.completion_members | change D0 completion join to n1 outside D0 | True | CAUGHT |
| flatness.completion_path_ends | replace left completion path by [n0] | True | CAUGHT |
| flatness.completion_path_steps | insert unsupported n0 → a0 into left completion path | True | CAUGHT |
| flatness.completion_path_actions | change e_a0 action to toggle | True | CAUGHT |
| flatness.completion_connected | delete D0 completion edge, disconnecting the pair | True | CAUGHT |
| flatness.completion_rank_decreases | cap a0 rank at zero | True | CAUGHT |
| flatness.completion_shared_unique_normal_form | delete D0 completion, leaving two terminal Q forms | True | CAUGHT |
| flatness.zero_completed_holonomy | change e_a0 clock increment to 1 | True | CAUGHT |
| domain.admissible | change e_a0 exit to entry, breaking declared endpoint support | True | CAUGHT |
| flatness.critical_members_distinct | change critical pair to a0/a1; do not silently filter it out | True | CAUGHT |
| flatness.completion_path_ends | append a second malformed completion for the existing valid pair | True | CAUGHT |

## Supported ceiling and reproduction

Confirmed positive-license outcomes provide nonconstant finite raw-execution instances of the three adopted sufficient mechanisms. Same-boundary routes agree; nonconstancy across boundaries and bit inputs is checked separately. These are exact Python finite checks, **not Lean kernel proofs**; G3c must prove the generic sufficient-license results and bridge these models. No registry status changes.

```bash
python3 -B scripts/evaluate_tth09_routes.py audit/proposed_models/TTH09-ROUTES.model.json
python3 -B scripts/selftest_evaluate_tth09_routes.py
python3 -B scripts/evaluate_tth09_routes.py audit/proposed_models/TTH09-ROUTES.model.json --json-out /tmp/g3b-rerun.json --md-out /tmp/g3b-rerun.md
cmp audit/G3b_results.json /tmp/g3b-rerun.json
cmp audit/G3b_results.md /tmp/g3b-rerun.md
```

The recorded rerun passed byte-for-byte comparisons for both outputs; no timestamps enter either artifact.
