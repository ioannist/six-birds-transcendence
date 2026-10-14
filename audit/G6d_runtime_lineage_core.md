# G6d: polymorphic runtime lineage core

## Proved boundary; TTH-06 is still conditional

`RuntimeLineage` aggregates the committed polymorphic execution, factor,
record, corridor, bridge and route interpreters. It is generic over cell/value
families, register families, states, action tables, events, histories and routes.
The source and receiver are raw instruction frames. Two **defined**
`ExecutionLink`s check their probabilities and actual updates against one
runtime, on all contexts and all positive branches. The exhaustive POS-04
ambient enumeration discharges support coverage; neither exit is forgotten.

This is **not yet the complete generic `RawHandoff`**. The name `CoreReadout`
is deliberate. Its exact POS-04 adapter retains the independently computed
`TypedAcquisitionEndpointPass` as an explicit enclosing obligation:

```lean
(RuntimeLineage.CoreReadout (raw (protocol m)) (image m.assignment) ∧
 TypedAcquisitionEndpointPass m) ↔
 POS04CompleteLineage.StrictTemporalLineage m
```

`POS04RuntimeLineage.complete_iff` proves this for **every partial assignment**;
`whole_iff` proves the same equivalence to `POS04SharedRuntimeLineage`. There is
no converse from the weaker legacy lineage gate. No field was dropped from the
complete family readout and no frozen statement was narrowed.

## Theorems and semantic return

- `RuntimeLineage.soundness`: component `Pass` implies the independently
  defined `CoreReadout`; corridor witnesses and full-word futures are derived
  from their own certifiers.
- `factor_words`: decoded finite-factor transport equations imply equality
  of every finite action-word probe. Its factor types and action types may differ.
- `frozen_transport`: all eight frozen signature components transport on the
  audited finite snapshot images, with full-interface future words unbounded.
- `route_status`: status is `.routeIndexed` only from the full nonempty
  `Indexed`/`Retained` comparison, including distinct raw paths, a shared
  endpoint and retention across **every** actual branch.
- `source_positive_branch`: every positive raw branch commutes with the
  runtime embedding. Membership is derived from checked support coverage.
- `record_soundness`: the stronger raw event/clock/writer audit derives the
  decoded arrow readout. The readout itself is arrow preservation, not a
  projection of a stored record-arrow verdict.
- `POS04RuntimeLineage.positive_pass` and `positive_core`: a nonvacuous instance.
  The inherited actual bridge has a real strict edge and different-past histories.
- `core_iff`, `record_iff`, `factor_iff`, `complete_iff`: exact decoder and semantic
  adapters, including arbitrary missing inputs; none is just canonical truth.
- `O_control_vectors`, `F_control_vectors`, `operational_named_separation`,
  `relabel_vector`: direct named-readout results, transported by biconditional.
  Negatives are not inferred by contraposing a sufficient gate.

The source and target program, corridor, executed-seed and bridge projections
are identified by `source_link_eq`, `target_link_eq`, `corridor_eq`,
`executed_eq` and `bridge_eq`. `shared_from_route` derives all-context links
from the actual consumed route inputs for arbitrary assignments; it does not
conjoin fixed positive adapters.

| Control | P | complete L (core **plus endpoint**) | F | O |
|---|---:|---:|---:|---:|
| Positive | T | T | T | T |
| Package deletion | F | T | F | T |
| Lineage deletion | T | F | T | T |
| Withdrawal deletion | T | T | F | F |
| Relabeling | T | F | T | T |

`relabel_no_core` also rejects the core itself by the independently checked
actual-execution readout. `missing_atomic_no_core` rejects the semantic core
without assuming readiness together with a missing cell.

## Argument classification

These are every argument of `soundness`: all interface types and their
`DecidableEq` instances, `raw`, `a`, and `h`.

| Argument / contained field | Classification | Interpretation |
|---|---|---|
| Cell/value and three register type families; factor, resource, state, action, outcome, predictive, residue, maintenance, endpoint, stage, event, history and route types; equality instances | Raw interface data | No POS-04 type is fixed in `RuntimeLineage`; equality instances only decide raw checks |
| `raw.schema` | Raw finite lists, carrier ids and clock | Source/target schema equations in `SharedExecution`; corridor/route domain checks |
| `raw.runtime` | Raw execution/resource/acquisition instructions | Owns the runtime rows and updater, resource residue and account-derived route owner |
| `raw.source`, `raw.target` | Raw instruction frames (initializers, history/receiver recipes, readout/update instructions, audit selectors) | Actual probability/updater links plus each frame's semantic realization, full future and whole-closure readout laws |
| `sourceEmbedding`, `targetEmbedding`, `translation`, `maps` | Raw typed coordinate instructions/maps | Complete-before-interpretation; actual all-context execution links and whole-source-closure bridge equations |
| `names`, `seeds`, `predictiveCoordinate`, `historyCoordinate`, `routeCoordinate` | Raw coordinate instructions | Constructed corridor and actual executed-seed equations |
| `factor` | Raw typed schemas, equality instances, table/map decoders | Decoded factor equations and derived all-word probe |
| `recordSchema`, `record` | Raw event/clock/writer instructions and enumerations | Option decoding then actual computed arrow preservation |
| `route` | Raw provenance, future-probe and endpoint instructions | Full shared-runtime `Indexed`/`Retained` comparison |
| `a` | Raw immutable partial assignment | One assignment for every component; missing consumed inputs reject |
| `h : Pass raw a` | Evidence on raw checks | No supplied dynamics, observation, closure, verdict or readout |
| Bridge, corridor, seeds, factor classes/words, arrows, route results/status, two execution links, snapshots, future models and closures | Defined objects | No additional theorem argument |

This table does not silently certify cross-component equations absent from this
core: extraction of the typed endpoint and final package/runtime ownership and
coordinate coherence at the public `RawHandoff` boundary remains mandatory.
Raw instruction views are not permission to substitute independent conclusions.

## Field and readout coverage

| Field / readout | Checked law | Guard / exact instance |
|---|---|---|
| Shared stage/carrier interfaces | `SharedExecution` source/target schema equality | `schema_mismatch_no_readout` |
| Disturbance/action/outcome domains, positive-support coverage | Defined source/target `ExecutionLink.Laws`, both raw rows | `source_link_no_readout`, `target_link_no_readout`; inherited omission regression; exhaustive POS-04 `ambient_coverage` |
| Actual probabilities and successors | All-context link equations; closure-wide bridge equations | Inherited uniform/identity update guards; `source_positive_branch`; `relabel_no_core` |
| Atomic events, realization, histories and receiver availability | Corridor construction and independently required source/receiver semantic execution | `missing_atomic_no_readout`, concrete `missing_atomic_no_core`; inherited unavailable-receiver guard |
| Audit, initializers and source seed coordinates | `SeedReadout`, actual four-snapshot folds; terminal-history audit coverage | Inherited `seed_mismatch_guard` / missing-coordinate guard; `executed_eq` |
| Typed factor domains, coordinate, class, policy, probabilities, tick, maintenance, owner and class injectivity | `FactorTransport.Equations` on decoded data | `missing_factor_no_readout`; existing factor per-field mismatch guards; `factor_iff` |
| Record events, clock and writers | Decoded `RecordReadout`; stronger optional `RecordComponent.Check` | `missing_record_no_readout`; existing clock/writer/event/realization guards apply to the stronger certifier; `record_iff` |
| Predictive, event order, tick, progress, writer, record, residue, maintenance and owner on run closure | Independent source AND target semantic readout laws; actual bridge observation law | Inherited `RegisterFuture` field guards and `ExecutionBridge.semantic_field_mismatch_rejected`; `frozen_transport` |
| Route provenance, defined future probe, actual shared endpoint and every retained branch | Full `Indexed` and `Retained`, not merely `ExecutedMemory` | `constant_residue_no_readout`, `empty_route_domain_no_readout`; inherited probe/path/endpoint guards |
| Derived route status | Full retained readout only | `route_status`; inherited never-flat theorem |
| Typed receiver/corridor endpoint obligation | **Still the separately computed POS-04 rule** | Kept explicitly in `whole_iff` / `complete_iff`; generic extraction is unfinished |

A row referring to an inherited stronger certifier does not claim its failure
negates the weaker semantic readout. The new direct semantic guards above have
no simultaneous acceptance premise. Full generic ownership/coordinate coherence
between the factor/record views and the shared execution remains part of the
public interface binding, not an unstated consequence of using one assignment.

## Remaining promotion gates

1. Extract the typed endpoint raw rule generically, and bind factor/record and
   run coordinate/ownership interpretations to the public raw component interface
   by checked equations. This core currently collects their interpreters and
   proves their program links, not the finished public semantic binding.
2. Assemble the polymorphic `RawHandoff` with the closed package dispatcher,
   arbitrary typed stage/checked cover and the historical F/O runtime. Explicitly
   tie lineage's actual acquisition runtime to autonomy's target runtime under
   its receiver/reset and resource conditions. The lanes deliberately use
   different acquisition semantics: funded actual source execution for lineage,
   historical raw source support plus reset/funded target execution for autonomy.
3. Final F/O soundness, generic AF ⇒ P, the exact POS-04 instance and named O
   separation over that **generic** interface; then the final transcription and
   registry gate. Existing generic package/game/AF⇒P/TTH-05 theorems are reusable,
   but their mere existence is not this assembly.

The future implementation retains selected-response `StrictSparse` sensitivity,
positive-support coverage and the hybrid constructor's sound-but-incomplete
scope. No finite-context irrelevance assumption is introduced here. TTH-06's
conditional status and exact statement remain unchanged. No new failed exact
claim was found; no adjudication or model revision is proposed.

## Changes and checks

All new mathematical statements/definitions are **(b), TTH-06**: a polymorphic
core and exact POS-04 specialization. No (a) porting changes, no changes to old
declarations, no narrowed row text. The CSV only adds accurately scoped evidence
and updates its remaining gap list; inventory is regenerated from that surface.
The checker adds Lean-evaluated core source/receiver rows and full ordered raw
execution domains against the frozen model, with four in-memory drift probes.
It does not export proof-only full-word propositions as stored Boolean verdicts,
and does not claim a final generic assembly.

Fresh check receipts are appended after validation below. Work is uncommitted;
`paper/`, CST-TT-08, model declarations and frozen evaluation results are untouched.

### Fresh verification and self-review

- `cd lean && lake build`: exit 0, **514 jobs**, 6.12 s incremental default
  build. The adapter module build was 2.7 s. No new module warnings; older
  replayed linter warnings remain.
- `scripts/validate_lean.sh`: exit 0, inventory match; 39 rows, 226 declaration
  entries / 225 unique, 217 theorem-kind, 8 statement-only, 1 other definition.
  No untrusted axioms, placeholders or high-confidence vacuity findings;
  45 preexisting nongating heuristic leads, with no new leads in this seam.
- `python3 -B scripts/check_tth06_transcription.py`: exit 0; **26** planted
  drift checks caught (four new core-instance checks). A second run's output is
  byte-identical. Its core export compares actual Lean instruction evaluations,
  not a Python reconstruction against itself or proof-only Boolean labels.
- `/tmp/g6d_runtime_lineage_axioms.lean` through `lake env lean`: all **35**
  new theorem names resolve; every axiom set is contained in the standard three.
- Forbidden-token source scan and `git diff --check`: clean. The five frozen
  CST-TT-08 status surfaces were explicitly compared byte-for-byte with HEAD.
  No changes to `paper/`, frozen models or evaluation results.

Self-review: this soundness theorem is a conditional composition of real
interpreters, not final TTH-06 fidelity. `RecordReadout` can have no source
arrows; that is why nonempty arrows are only claimed by the stronger record
certifier, and why the independent full run-advancement and actual bridge
obligations are retained. Neither the decoded arrow implication nor using one
assignment proves the missing cross-component ownership/coordinate equations.
No claim of complete generic lineage, final RawHandoff, or promotion is made
without those remaining checks and the typed endpoint. The concrete whole
adapter retains them in the committed POS-04 semantics.

Ignored logs: `lean/.validate-logs/g6d-runtime-lineage-*`. Validator JSON:
`lean/.validate-logs/run-20261009T095200-948659Z/report.json`.
