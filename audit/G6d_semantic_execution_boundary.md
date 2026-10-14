# G6d semantic execution boundary

**Historical execution seam; continued in `G6d_complete_lineage.md`.**
TTH-06 remains conditional. This note records the execution adapter before
whole-lineage aggregation. The continuation completes the strengthened family
aggregate and F/O assembly and annotates the 09 evidence surface with the
counterexample. The final polymorphic `RawHandoff` binding remains open. Frozen
models/results and existing declarations are unchanged.

All new definitions/theorems are **(b) additions for TTH-06**. There are no (a)
changes and no narrowing of the row. The weaker legacy readout is retained.

## Proved

- `ExactFutureReindex.sufficient_iff`: semantic future sufficiency is equivalent
  under a state-surjective, action-surjective reindexing with injective
  observation encoding and checked code/weight/successor equations. Both
  directions retain **all states and all finite words**. This is an internal
  adapter engine; its future parameters are not fields of a raw handoff.
- `ExecutionFrontier.SemanticReadout`: actual realized supported audits with
  terminal history coverage, defined full-interface future sufficiency,
  closure-wide update/readout laws and subprobability rows. It requires the
  semantic word law, not a selected one-step bisimulation verifier.
- `ExecutionBridge.SemanticReadout`: both frames' own semantic obligations,
  plus raw history/initializer equations and weights, successors and all eight
  observation fields on the **whole computed source closure**.
- `semantic_soundness` proves **gate ⇒ semantic readout**. No converse is
  assumed. `semantic_frozen_transport` constructs/compares every frozen snapshot
  field with the actual dynamics' full-future facts attached;
  `semantic_representative_independence` derives the predictive image agreement.
- `POS04SemanticExecution.full_future_iff` is a biconditional to the actual
  `Run6` future, without a C6-acceptance hypothesis or a closure-only narrowing.
  `closure_iff` is a bijective interpreter/actual-run correspondence on the
  entire computed closure, including zero-weight outcomes in the deliberately
  conservative closure definition. Actual supported branches are included.
- `temporal_ready_iff`, `source_ready_iff`, `target_ready_iff` give the exact
  consumed-input domains. Missing inputs cannot be accepted through defaults.
- `transport_laws_iff` identifies the generic bridge laws with independently
  stated raw `Run6` word, initializer, weight, successor and observation
  equations. `semantic_bridge_iff` combines these into an exact adapter for
  **arbitrary partial assignments**. The two semantic frame predicates retain
  their own future/closure/realization obligations.
- Canonical nonemptiness is proved by `positive` and `canonical_transport`.
  Direct semantic guards reject missing inputs, capped progress, uniform
  weights and an identity updater. The cap agrees at the audited counters 1/2
  but fails the independent progression recipe on a supported next step.

These results complete the **execution** part of the bridge. They do not claim
that record-event, finite-factor, carrier/endpoint and retained-route interfaces
have already been aggregated into the whole named lineage readout. Correct
carrier ownership and the corridor/receiver endpoint links remain obligations
of that aggregate, beyond merely transporting an owner observation field.

## Finding: the old named readout is not the complete execution readout

The sensitivity rule is: at `p2w1`'s **noncanonical** `cw` action, relabel lethal
`p2w0` to lethal `p5w1`, keeping every existing numerator. The original source
cell is edited, and the declared stage makes it the target cell. No probability
is tuned or newly invented. Canonical policy rows and acquisition histories
remain unchanged (`unchanged_policy_rows`, `staged_source_unchanged`).

`POS04LineageFutureBoundary` proves:

```lean
legacy_gate_accepts : LineageLane proposal
legacy_named_readout_accepts : ComputedFIACH.StrictTemporalLineage proposal
no_complete_execution_readout :
  ¬ ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw
    (image proposal.assignment)
```

The mismatch occurs **at an audited snapshot**:
`after_first_is_audit_snapshot` identifies it with route A, occurrence 1;
`first_step_probability` is exactly 1. For the subsequent `cw` query, the
`p2w0` branch has target weight **0** and source weight **1**
(`actual_branch_difference`). `no_semantic_transport` uses that checked raw
equation directly, not the failure of a sufficient test.

The reason is visible in
`Targets/ComputedFIACH/AssignmentBridge.lean:194`: `FiniteActionMap` compares
only destinations of type `KState`. Both lethal outcomes are outside K and
have the same hazard Boolean. Its finite M readout therefore misses their
different actual full-future observations. The old frozen results expose
snapshot agreement and each model's own sufficiency, which do not imply the
whole-closure cross-model branch equations.

`legacy_readout_does_not_imply_complete_bridge` formally refutes the attempted
universal implication. Consequently the requested complete semantic adapter
cannot identify the old named predicate with this stronger execution readout.
Per Eddy's guidance, the enclosing **independent complete lineage readout must
carry these substantive dynamics laws**; unused interface declarations must not
be inserted to force equivalence with the old gate. This is a missing semantic
obligation, not a failure of POS-04's canonical instance and not a failure of the canonical positive. The 09 evidence ceiling now explicitly
records the legacy omission; its status remains conditional.

## Argument classification

| Argument | Classification | Constraint |
|---|---|---|
| Component `raw`, schemas, audit, raw maps, recipes | Bridge-owned raw instructions/data | Existing interpreted programs; no future/observer/closure candidate fields |
| Assignment | Shared immutable raw cells | Exact source/target readiness; consumed missing inputs reject |
| Readiness, supported audit, normalization and transport-law proofs | Evidence on raw data | Actual decoded row/update/observation equations |
| Futures, code, observers, roots, closure, snapshots and finite images | Defined objects | Constructed by the interpreters from the assignment |
| Reindex state/action/observation maps | Internal representation adapters | Surjectivity/injectivity and exact interpreter equations, proved per instance |
| `SemanticReadout` evidence | Derived semantic conclusion | Gate soundness; never a raw certificate field |

## Readout coverage

| Field/obligation | Semantic law | Guard |
|---|---|---|
| Every source/target input | Exact `*_ready_iff`; interpreted reads | `missing_source_input_no_readout`, `missing_target_input_no_readout` |
| Histories/audit/realization/activation | Supported `AuditCheck`, terminal coverage, own `PathsAvailable` | `missing_atomic_no_readout`; generic `semantic_unavailable_receiver_guard` |
| Weights | `TransportLaws` on actual whole closure; row normalization | `semantic_weight_mismatch_rejected`, `uniform_no_semantic_readout`, `no_semantic_transport` |
| Successors | Actual updater equation on whole closure | `semantic_successor_mismatch_rejected`, `stationary_no_semantic_readout` |
| Predictive, order, tick phase, progress, record, residue, maintenance, owner | Full observation equation and each frame's independent raw update recipes | `semantic_field_mismatch_rejected`; own-frame `semantic_field_guard` parameterized over all nine readouts |
| Writer | Own raw writer recipe in the closure-wide gate | `semantic_field_guard .writer` |
| Supported advancement/record funding | Positive recipes against actual weights/updater | `semantic_nonadvancing_guard`; `capped_progress_no_semantic_readout` tests the exact progress recipe |
| Full word law | Defined complete observer/code/rows/updater, all-state semantic predicate | `full_future_iff`; no state/word quantifier dropped |
| Frozen components/representatives | Actual supported snapshot fold and whole-closure observation map | `semantic_frozen_transport`, `semantic_representative_independence`; field guards above |

## Checks and remaining work

- Full build: exit 0, 465 jobs; new modules have no warnings. Existing vendor
  and `TemporalFactorRules` warnings remain.
- All **45** new public theorems resolve through `/tmp/g6d_semantic_axioms.lean`;
  only `propext`, `Quot.sound`, and `Classical.choice` occur. The final boundary
  module builds in 20s; the semantic adapter in 5.1s (Lake receipts).
- Existing extended TTH-06 transcription passes, with eight planted drifts
  caught. No frozen model or result is regenerated.
- Validator exits 0: 39 rows / 210 declarations, zero placeholders and
  high-confidence vacuity findings, 36 unchanged heuristic leads. The row
  remains conditional and the inventory is unchanged.
- `git diff --check` and the forbidden-construct scan are clean. CST-TT-08,
  frozen G6 artifacts and `paper/` are untouched.

Next: aggregate the corridor, complete semantic bridge, factor/record laws,
typed carrier/receiver endpoints and full `Indexed`/`Retained` route readout;
prove its independent exact family adapter. Then bind all interpretations into
`RawHandoff`, derive F/O soundness and named control vectors, extend transcription
for the aggregate, and apply the registry promotion gate. The legacy named
readout must remain distinguishable from the stronger complete readout.
