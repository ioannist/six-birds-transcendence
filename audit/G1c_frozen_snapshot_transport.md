# G1c — exact frozen transport, CR4 readout-law repair

TTH-03 was first reset to `conditional`. After the generic construction, POS-04 instance and closure guard compiled, it was re-promoted to `proved` at **structural transport on the declared audited frontier only; future words unbounded**. Its exact statement is unchanged. CST-TT-08 and the POS-04 declaration are unchanged. C6 retains its surrogate grade.

## Domain and finite images

The theory describes descent “on the declared reachable quotient image” (`cst-tt/docs/HETEROGENEOUS_TEMPORAL_TRANSPORT.md:27`). The generic theorem covers every reachable history in the declared bridge frontier and every audited snapshot; `SnapshotAuditCheck` requires a terminal snapshot for every declared history. POS-04 uses its two actual route histories, repA and repB, at occurrences one and two, giving four realized history/event/route contexts. The older four-history witness remains intact. No claim about unlisted histories is made.

`SnapshotImage frontier readout` is the exact subtype of actual values in `frontier.map readout`. The attached list gives its `FiniteEnum`, and decoding returns the raw value. The codec identity and no-loss theorems hold for all eight fields. No counter is capped to obtain a finite alphabet. Unbounded counters remain in the run state; later future observations need not belong to this snapshot alphabet. Tick phase alone uses the declared modulus two.

## The structural fix

The three supplied derived objects discovered by review—candidate dynamics, a proposed reference, and candidate observations—have all been removed from the construction's signature. It additionally removes separately supplied audit objects, run embeddings, aggregate codes, displays, decoders and clocks. One raw bridge determines the entire construction.

- `bridgeRunDynamics b`: outcomes are `b.runOutcomes`; weights are raw integer numerators divided by the bridge denominator; successors are `b.runUpdate`.
- `bridgeRunObservation b`: predictive coordinate, actual event counter, raw ticks modulo the bridge period, raw progress, raw record count checked against availability and the raw writer, route residue, maintenance and owner.
- `bridgeRunCode b`: fixed extraction of predictive/order/phase/residue/maintenance/owner from that observation. Progress and record remain in the observation, and their predictability is checked by bisimulation.
- `bridgeFutureModel b`: exactly those defined outcomes, weights, successors, observation and code.
- `bridgeSnapshotAudit b`, source/target run constructors, future roots and closure: defined from the bridge's raw finite audit selectors and typed constructors.
- `frozenBridgeSource/Target`, codecs and typed clock: defined exact finite snapshot images and typed maps, not constructor arguments.

`BridgeRunCoherence` ties full-run core masses to the factor action tables, covers positive outcomes, checks counter and factor tick updates, and checks successor class membership. Ambient exits and maintenance update rules are additional bridge-owned raw data. `SnapshotRunCheck` checks actual factor occurrence, availability, event count and ticks. `BridgeSnapshotReadoutCheck` checks all eight root readouts and injectivity of the predictive coordinate maps. No root-only equation purports to certify a separately supplied future observer: away from roots the observer is still the very same **defined** function of bridge-owned run data.

`BridgeFutureBisim` checks equal one-step observations, weights and successor codes for the defined model. `bridge_defined_future_sufficient` then proves all-word sufficiency by induction. The main result's `actualFuture` field quantifies over the computed closure and every finite word/trace. The bisimulation proof actually establishes sufficiency on all run states, which is stronger. Closure includes even zero-weight enumerated outcomes and is never computed from a proposal.

## Every argument of the generic result

The following audit includes implicit type parameters, proof arguments and the index in the result. The theorem has no supplied derived object.

| Argument | Classification | Meaning / gate |
|---|---|---|
| `H S T E R SC TC RR M : Type` | Raw carrier/component types | Histories, factors, events, routes, predictive classes, residues and maintenance. |
| `b : RawBridge H S T E R SC TC RR M` | Bridge-owned raw data | Declared frontiers, histories, coordinate maps, factor rows, support, ticks, order, progress, record, route and ownership tables. |
| Associated run types, component equality dictionaries and outcome enumeration inside `b` | Bridge-owned raw data | Raw typing and finite outcome domain; no supplied aggregate future model or observation dictionary. |
| Run numerator/denominator, updater, factor/outcome/action projections inside `b` | Bridge-owned raw data | Actual full-run row and update laws; checked by `BridgeRunCoherence`. |
| Individual run predictive/progress/writer/residue/maintenance/owner readouts and predictive maps inside `b` | Bridge-owned raw data | Raw coordinate projections; aggregate observation and code are fixed definitions. POS-04 globally links them to the frozen raw C6 readouts. |
| Component update recipes and writer/availability tables inside `b` | Bridge-owned raw rule data | Independent numerical/table prescriptions, checked by `BridgeRunReadoutLaws` throughout closure; never propositions or an aggregate supplied observer. |
| Audit selectors, period and typed run constructors inside `b` | Bridge-owned raw data | Raw contexts and carrier constructors; coverage/incidence, embedding and readout checks bind their use. |
| `ha : BridgeAdmissible b` | Evidence checking bridge-owned raw data | Coverage, representatives, nonempty reachable frontier and strict edge. |
| `hl : BridgePrimitiveLaws b` | Evidence checking bridge-owned raw data | Raw coordinate, successor, order/tick/progress, record, route, maintenance and ownership equations. |
| `hd : SnapshotAuditCheck b (bridgeSnapshotAudit b)` | Evidence checking bridge-owned raw data | Nonempty finite audit, positive period, actual occurrences/routes/events and endpoint coverage. |
| `hbc : BridgeRunCoherence b` | Evidence checking bridge-owned raw data | Core pushforward/action-row equality, counter/tick updates and class projections. |
| `hrun : SnapshotRunCheck b` | Evidence checking bridge-owned raw data | Actual, enabled source/target embeddings and occurrence/tick equations. |
| `hread : BridgeSnapshotReadoutCheck b` | Evidence checking bridge-owned raw data | Eight-field snapshot equality and injective coordinate lifts. |
| `hupdates : BridgeRunReadoutLaws b` | Evidence checking bridge-owned raw data | Root identity plus every readout equation throughout the unbounded computed closure; see the complete field table below. |
| `hb : BridgeFutureBisim b` | Evidence checking defined functions of raw data | One-step equations, not an assumed sufficiency conclusion; induction derives the latter. |
| `i : Audited b.auditFrontier` in the conclusion/result | Raw audit index with membership evidence | Selects an actual declared snapshot; not a supplied signature. |

All derived objects—reference dynamics, future model, observer, code, roots, closure, snapshot audit, embeddings, finite image types, codecs, frozen signatures, typed clock and all-word law—are **defined**. Their checked proofs may be arguments; their functions are not supplied.

### Exact main signature

```lean
theorem bundledHeterogeneousTemporalTransport_frozen
    (b : RawBridge H S T E R SC TC RR M) (ha : BridgeAdmissible b)
    (hl : BridgePrimitiveLaws b) (hd : SnapshotAuditCheck b (bridgeSnapshotAudit b))
    (hbc : BridgeRunCoherence b) (hrun : SnapshotRunCheck b)
    (hread : BridgeSnapshotReadoutCheck b) (hupdates : BridgeRunReadoutLaws b)
    (hb : BridgeFutureBisim b) :
    RepresentativeIndependent (Reachable b) (SourceHistoryClass b) (TargetHistoryClass b) ∧
    StrictRecordArrowPreserved b ∧ RouteStatusPreserved b ∧
    (∀ h, Reachable b h → StrictSuccessorPreserved b h ∧ StrictOrderTickProgressAt b h) ∧
    (∀ i : Audited b.auditFrontier, FrozenBridgeSnapshotResult b ha hl hd i)
```

The readout supplies representative independence, strict record transport, executed route status, strict successor/order/tick/progress and the constructed frozen structures. `FrozenBridgeSnapshotResult` includes actual eight-field agreement and typed transport equality, eight-field codec identities, observation/code links, raw coherence and all-word sufficiency. Source and target `PredictiveNow.futureSufficient` are the defined full-interface sufficiency proposition, not stored flags.

## Proposal corollaries and the three attacks

The legacy candidate-parametric `SnapshotImages` lemmas remain algebraic codec schemas, explicitly labelled as such. They are not evidence about a bridge execution, and no snapshot-link/display/decoder object enters the current certificate. Old POS-04 snapshot tests are retained as diagnostics.

`BridgeFutureProposalCheck` requires the proposal's outcomes to equal the bridge's and requires code, observation, weight and successor equality on **every state of the bridge-computed closure**. `FrozenBridgeProposalResult` additionally contains the canonical result. It cannot replace the defined model. `bridge_proposal_future_eq_defined` proves trace-law equality by unbounded-word induction; the sufficiency corollary uses that equality. The former `*_frozen_result_fails` names now reject proposal results, rather than pretending the canonical bridge result is false.

Generic weight/successor mismatch guards reject any discrepancy at any closure state. POS-04 retains the uniform and identity attacks, and the joint uniform/stationary attack, as rejected proposals. Their snapshot-only tests still pass, documenting precisely why those tests alone were insufficient.

For Eddy's CR3 attack, `cappedOrderProposal b` is expressible only as a diagnostic proposal. `capped_order_proposal_fails` rejects it whenever a closure state has raw order greater than two. On POS-04:

- `pos04_capped_order_roots_unchanged`: all eight tagged root embeddings retain equal observations.
- `pos04_after_endpoint_supported`: the source route-A endpoint's `.cw/.m3` probability is **one**, and its successor's raw order is **three**.
- `pos04_after_endpoint_in_closure`: that successor belongs to the actual unbounded closure.
- `pos04_capped_order_proposal_fails` and `pos04_capped_order_frozen_result_fails`: the observation equality and proposal certificate fail; the proposed order is two while the defined order is three.

The canonical certificate cannot accept the proposal at all, because it has no observer/model argument.

## POS-04 dynamics and observation link

`pos04_snapshot_bridge_action_row_link` ties factor rows to `actionRow`, with the canonical factor linked to `taggedPNum`. The future row is the exact M-pushforward `classMass/4`, including ambient exits. `pos04_snapshot_bridge_reference_eq` identifies its raw updater and row with the bridge-owned computation. The updater advances unbounded counters, applies raw tick rules, selects the quotient representative, preserves residue and tag, and computes maintenance from the raw ledger. This is the declared quotient successor, not microstate identity.

`pos04_bridge_observation_eq_c6` and `pos04_bridge_code_eq_c6` hold for **every run state**, not just the finite audit. They identify all eight fields and the complete code with original C6, using the injective carrier-id translation. `pos04_defined_future_bisim` reuses the existing positive bisimulation through these global conversions and exact row/successor equations. Maintenance, route and owner are included. Funding/budget preservation on the closure is unchanged: funded budget one, cost one, recharge one; no variable-budget semantics are invented.

## Statement changes and self-review

| Change | Classification |
|---|---|
| Raw full-run and audit coordinate/constructor fields; eight-component observation and fixed code built from them | **(b), TTH-03**: supplies missing raw content; no model verdict field. |
| Defined reference, observer/code, audit, embeddings, clock, exact finite signatures and closure; generic result signatures remove candidate parameters | **(b), TTH-03**: structural strengthening and construction, not a rename. |
| Raw coherence/readout/embedding and defined-model bisimulation premises; full-interface unbounded-word proof | **(b), TTH-03**: checked premises rather than projecting a future-law proof. |
| Proposal equality of all five components on closure; equality/sufficiency corollaries and generic/concrete guards | **(b), TTH-03**: strengthened candidate diagnostics. |
| Existing `*_frozen_result_fails` names now conclude rejection of `FrozenBridgeProposalResult`; canonical theorem/instance names retain updated signatures | **(b), TTH-03**: disclose the mathematical signature change; no registry rename. |
| Move POS-04 raw snapshot selectors into `RawRunDynamics` | No statement change: same declarations and values, dependency repair. |
| 09 re-promotion and inventory wiring | Only TTH-03; exact text unchanged and explicit frontier/unbounded-word ceiling. |

Self-review traces raw tables → coherence → defined run observation/dynamics → one-step equations → word induction → exact snapshot codecs → frozen field transport. No supplied derived object remains in that path. Raw bridge laws are hypotheses of the generic conditional theorem and POS-04 proves them; they are not stored desired conclusions. Future-law sufficiency is derived. There is no physical, T17-I or full P05 claim and no C6 surrogate upgrade. Recognition is not addressed. Extending the audited domain or changing the raw observation interface requires a new checked instance.

## CR4: complete readout coverage

CR3 left individual readouts free of update equations. In particular a capped `runProgress` passed bisimulation; that was a BLOCKING defect. TTH-03 was first reset to `conditional`. The mandatory `BridgeRunReadoutLaws` gate now checks initial identity and component equations throughout `BridgeFutureClosure b`, and is a field of the complete `FrozenBridgeSnapshotResult`. Both the bundled constructor and the frozen-signature constructor require it.

Raw bridge data now declares numerical/table update recipes: `runSourceFactorUpdate`, `runTargetFactorUpdate`, `runPredictiveUpdate`, `runTickAdvance`, `runProgressAdvance`, `runWriterRule`, `runResidueUpdate`, `runMaintenanceUpdate`, `runOwnerUpdate`, and `runEnabledRule`. These are functions on raw coordinates, not propositions or proof fields. POS-04 fills them with its class-representative/tag map, raw tick increments, unit event/progress advance, writer table, retained route tuple, one-token ledger equation, identity ownership and funded availability. The new `runRecord` readout is **checked**, both now and after every update, against those independent writer/availability rules and the uncapped counter. No observation proposal enters the result.

The sources for these recipes are the accepted G0 TTH-03 coordinate laws and the frozen `M3_model_spec.md:22,30-33,40-44`; the implementation is the existing `C6.lean:200-207` full observation and `RawRunDynamics.lean:31-40` updater. POS-04's post-exit register is **retained**, not appended on each future step. All enumerated simulator steps advance the attempt/event counter and progress by one. Only steps of positive raw mass are asserted to have positive tick and progress increments. Unsupported exit steps may have zero tick advance. No realized progress at a zero-mass exit is claimed.

### Readout coverage table

`U` below means `BridgeReadoutUpdateAt`; `R` means root identity checked by `SnapshotRunCheck` and `BridgeSnapshotReadoutCheck`. Both are mandatory in `BridgeRunReadoutLaws`, throughout the computed closure for `U` and on every declared root for `R`. The generic `bridge_readout_field_update_guard` is indexed by the exhaustive `RunReadoutField` enum. `bridge_readout_initial_observation_guard` projects any root component and rejects a wrong value; preservation alone would allow an incorrect constant owner, residue or maintenance label.

| Run readout | Declared and checked law | Gate | Concrete guard theorem (`CSTTT.POS04.` prefix) |
|---|---|---|---|
| Predictive `runPredictive` | After update, equals raw predictive value of the outcome representative at the retained tag; at every closure state with a factor projection, its current value equals that factor’s injected raw class; roots agree. | U.predictive, U.sourcePredictive, U.targetPredictive + R | `pos04_predictive_readout_guard` (constant exit2 rejected) |
| Event order/counter `runCounter` | Counter after every enumerated update equals counter + 1; root equals audited occurrence. | U.counter + R | `pos04_counter_readout_guard` (cap at 2 rejected) |
| Ticks `runTicks` | Raw accumulated ticks plus raw state/action tick increment; positive on positive-mass steps; roots equal actual prefix sums. | U.ticks, U.supportedAdvances + R | `pos04_ticks_readout_guard` (cap at 2 rejected) |
| Tick phase (derived) | `(ticks + increment) mod period`; positive period from audit check. No independent phase observer is supplied. | Derived from U.ticks + audit period + R | `pos04_tickPhase_readout_guard` (capping its raw tick input rejected) |
| Progress `runProgress` | Raw progress plus declared advance; positive advance on positive-mass steps; roots equal bridge progress. POS-04 advance is 1. | U.progress, U.supportedAdvances + R | `pos04_progress_readout_guard` (Eddy's min(eventCount,2) rejected at supported 2→3 step) |
| Writer `runRecordWriter` | Both current and next writer equal raw writer table evaluated on the current/updated residue and owner. | U.writerNow, U.writerNext | `pos04_writer_readout_guard` (constant false rejected) |
| Record `runRecord` | Current count is uncapped counter if raw availability and writer permit, otherwise zero; next count uses updated ledger/residue/owner and counter + 1. Root equals actual raw event record. | U.recordNow, U.recordNext + R | `pos04_record_readout_guard` (constant zero rejected) |
| Residue `runResidue` | Update follows declared route-register operation. POS-04 retains the existing raw tuple; initial tuple equals the actual audited route. | U.residue + R | `pos04_residue_readout_guard` (constant empty tuple rejected) |
| Maintenance `runMaintenance` | Update follows raw ledger rule: funded AND budget-after > 0; roots equal actual funded carrier maintenance. | U.maintenance + R | `pos04_maintenance_readout_guard` (constant false rejected) |
| Owner `runOwner` | Explicit preservation (`runOwnerUpdate owner = owner`), updated readout equals that rule; current factor owner equals corresponding source/target carrier owner; roots agree. | U.ownerPreserved, U.owner, U.sourceOwner, U.targetOwner + R | `pos04_owner_readout_guard` (constant source owner rejected on target) |
| Availability `runEnabled` | Current and next availability equal raw maintenance/owner resource rule; both roots enabled. | U.enabledNow, U.enabledNext + R | `pos04_enabled_readout_guard` (constant false rejected) |
| Source factor `runSourceFactor` | Next projection equals outcome representative on source tag, otherwise none; root is the audited state. | U.sourceFactor + R; existing core-class coherence also retained | `pos04_sourceFactor_readout_guard` (constant none rejected) |
| Target factor `runTargetFactor` | Next projection equals outcome representative on target tag, otherwise none; root is the typed image state. | U.targetFactor + R; existing core-class coherence also retained | `pos04_targetFactor_readout_guard` (constant none rejected) |

There is no missing run readout. Static type dictionaries, outcome enumerations, denominator, tick period and audit selectors are metadata/table parameters, not evolving readouts. They retain their coverage, positivity and coherence gates. Source/target class/owner/tick tables are finite factor primitives; run projection, predictive update, owner anchoring and factor tick coherence link them to the run. POS-04's budget is a constant ledger parameter, not another counter in `C6State`; its exact equation and closure funding are already proved by `pos04_snapshot_future_closure_ledger`.

`pos04_bridge_readout_updates` proves every U equation for **all run states/actions/outcomes**, stronger than closure-only checking. `pos04_snapshot_readout_laws` supplies U and both R checks to the generic construction. `pos04_every_readout_corruption_fails` exhaustively dispatches all 13 enum cases. `pos04_corrupt_readout_no_frozen_result` propagates failure to the complete result, for arbitrary admissibility/law/audit proofs if they exist. Each control changes only the selected raw readout; tick phase is derived, so its control changes only its raw ticks. Recipes, updater, action rows, audit data and all other raw readouts stay fixed. These are gate-sensitivity probes, not newly declared science models or a claim that every conjunct fails in isolation.

### CR4 statement changes

All are **(b), TTH-03**: new raw record readout and independent component update recipes; `BridgeReadoutUpdateAt`, the exhaustive readout dispatch and generic guards; closure-wide `BridgeRunReadoutLaws`; an extra gate field/premise in the frozen result and constructors; POS-04 global update proof/adapter and 13 corruption guards. The earlier mathematical changes remain as listed above. No porting rename or other row change. The exact statement and frontier ceiling are unchanged.

### CR4 self-review

The new gate is mandatory in the full result, rather than a sibling diagnostic. Growth follows raw positive increments on supported steps; bisimulation is used only for predictability. Incorrect invariant constants are rejected by root identity or current raw-rule equations. All enumerated future successors are checked, without a horizon or snapshot cap. The required ownership rule is preservation, not an unconstrained owner update. Guards check each readout under a fixed law/data bundle. Every positive equation is inhabited by POS-04. C4–C7 remain surrogates; no domain expansion or new physical claim is made.

## Reproduction and validation

`cd lean && lake build`; then `python3 -B scripts/validate_lean.py --write-inventory` and `scripts/validate_lean.sh` from the repository root.

- Final `cd lean && lake build`: exit 0, 300 jobs. Raw bridge 4.6 s; frozen generic bridge 2.4 s; POS-04 raw adapter 9.8 s; full-future adapter 3.8 s; snapshot adapter 3.8 s; readout guards 2.5 s. Only existing replayed warnings.
- Inventory regenerated: 39 rows, 174 declaration entries. Final validator exit 0: 165 theorem-kind entries, eight statement-only definitions and one other definition. Every name resolves; inventory matches.
- Zero untrusted axioms, placeholders or gating vacuity findings. Nine unchanged heuristic leads. Report: `lean/.validate-logs/run-20260930T113903-891635Z/report.json`.
- Fresh `/tmp` axiom probes on generic construction, field law/guards, POS-04 global laws, positive instance and exhaustive corruption/no-result theorems show only standard axioms (or fewer).
- `git diff --check` clean. Seven frozen 08/POS-04 registry/handoff/declaration files byte-identical to HEAD. The only changed 09 row is TTH-03. No commits.

CR4 files: `RawBridge.lean`, `FrozenSnapshotBridge.lean`, POS-04 `GenericTransport.lean`, `FutureDynamics.lean`, `FrozenSnapshots.lean`, new `ReadoutGuards.lean`, its `CSTTT.lean` import, 09 CSV, inventory and this report. Earlier G1c files remain in the uncommitted diff.

Additional named (b) definitions: `RunReadoutField`, `RunReadoutValue`, `runReadout`, `expectedNextReadout`, `bridgeRootRun`, `bridgeRootExpectedObservation` and `pos04ReadoutCorruption`. Current source/target predictive readout equations tie every projected factor state to its raw class; ownership preservation is explicit. Generic and concrete guard names and laws are enumerated in the coverage table. Frozen result and constructor signatures now require the readout-law gate. No (a) rename or other row change.
