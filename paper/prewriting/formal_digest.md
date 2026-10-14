# Formal definition digest for the paper (Lean 4, `lean/CSTTT`)

Read-only digest. All paths are relative to `lean/`. Line numbers are from the working tree on 2026-10-13 (branch `build/paper`). I read every cited definition in source. I built nothing and ran no `#check`; all claims come from reading the source.

Conventions used below:
- "Assignment C V" means a partial assignment `(k : C) → Option (V k)` of typed cells. "Complete xs a" means every cell in `xs` has a value.
- "gate" means the checkable hypothesis (`HandoffPass_*`, `*Pass`, `*Check`). "readout" means the semantic predicate concluded.
- The verdict in (f) is mine and is meant to be candid.

All 11 items are covered. The deepest unfolding is in items 1, 2, 4, 6, 8 and 9, as requested. Items 3, 5, 7, 10 and 11 are complete but less deeply unfolded.

---

## 1. TTH-06: generic Temporal-FIACH soundness (F and O), and the POS-04 instance

### (a) Names and locations
| Declaration | File:line |
|---|---|
| `CSTTT.TargetTheory.GenericHandoff.FinalHandoff.temporalFIACHCertificateSoundness_generic_F` | `CSTTT/Targets/GenericHandoff/FinalHandoff.lean:54` |
| `...FinalHandoff.temporalFIACHCertificateSoundness_generic_O` | `FinalHandoff.lean:59` |
| `...FinalHandoff.full_autonomy_implies_package` | `FinalHandoff.lean:71` |
| `...FinalHandoff.HandoffPass_F` / `HandoffPass_O` | `FinalHandoff.lean:46` / `:50` |
| `...FinalHandoff.IntegratedTargetRealization` | `FinalHandoff.lean:25` |
| `...FinalHandoff.StrictTemporalLineage` | `FinalHandoff.lean:39` |
| `...FinalHandoff.PostWithdrawalFullAutonomy` / `...OperationalAutonomy` | `FinalHandoff.lean:28` / `:30` |
| `...FinalHandoff.ScopeCheck` | `FinalHandoff.lean:42` |
| model type `FinalHandoff.Raw` | `FinalHandoff.lean:12-17` |

Note: there are four same-named families in the tree: `OwningHandoff` (in `RawHandoff.lean`), `FinalHandoff`, `HistoricalPackageRuntime` and `ComputedFIACH`. The ledger cites `FinalHandoff`.

### (b) Lean statements
```lean
-- FinalHandoff.lean:54
theorem temporalFIACHCertificateSoundness_generic_F (m : Model) (a : Assignment SC SourceValue)
    (h : HandoffPass_F m a) :
    IntegratedTargetRealization m a ∧ StrictTemporalLineage m a ∧ PostWithdrawalFullAutonomy m a
-- :59  same with HandoffPass_O and PostWithdrawalOperationalAutonomy
-- :71
theorem full_autonomy_implies_package (m : Model) (a : Assignment SC SourceValue)
    (h : PostWithdrawalFullAutonomy m a) : IntegratedTargetRealization m a
```
Here `Model` is `FinalHandoff.Raw SC Cell SourceValue Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint`. All 22 type parameters are arbitrary, with `DecidableEq` on Cell, S, O, Route, Stage, Id, Owner, Resource, P and Q. No finiteness assumption appears on any type.

### (c) Definitions, unfolded

**Model layers.** `FinalHandoff.Raw` (`FinalHandoff.lean:12`) has three fields:
- `base : OwningHandoff.RawHandoff ...` (`RawHandoff.lean:22-42`): source clause package, dispatched target package, frames, runtime schema and runtime, embeddings, snapshot maps, route instructions, historical execution and bindings, and run-cell programs.
- `nominal : NominalHandoff.Instructions` (`NominalHandoff.lean:12`): ledger, `canonicalP`, required resources and a source-presence view.
- `receiver : ReceiverGate.Instructions base`: a receiver-content recipe and an erase map.

The target assignment is computed: `OwningHandoff.target m a = HistoricalPackageRuntime.target ... = DispatchedPackage.global m.package a`. That is the gluing of the stage-mapped local assignments (`HistoricalPackageRuntime.lean:33`, `PackageEngine.lean:12`).

**Gate F** (`FinalHandoff.lean:46`):
`HandoffPass_F m a := NominalHandoff.HandoffPass_F m.base m.nominal a ∧ ReceiverGate.Subcheck ... ∧ ScopeCheck m a`.
- `NominalHandoff.HandoffPass_F` (`NominalHandoff.lean:107`) is `Laws ∧ Pass ∧ OwningHandoff.HandoffPass_F`.
  - `Laws` (`:42`) is a set of raw recipe equations: the C8 dispatcher rule equals the fixed C8 rule, and the resource runtime's `sourcePresent` and `required` instructions agree with the nominal recipe.
  - `Pass` (`:49`) means the withdrawal metadata decodes and `NominalProtocol.Pass` holds (`NominalProtocol.lean:170`). That is a finite Boolean protocol check on decoded rows, policy, ticks, ledger, routes and writers.
- `OwningHandoff.HandoffPass_F` (`RawHandoff.lean:158`) is `SourcePackagePass ∧ Coherence ∧ DispatchedPackage.Valid ∧ RuntimeLineage.CompletePass ∧ FullSubcheck`.
  - `SourcePackagePass` (`:153`): the source assignment satisfies all eight source clause rules.
  - `Coherence` (`:127`): injective owner map, carrier and schema checks, the C6 rule is the temporal decoder, presentation coherence, and target-execution coherence.
  - `DispatchedPackage.Valid` (`DispatchedPackage.lean:24`): cover check, scope check, total stage, reference stage, value preservation, source coverage, every clause rule accepting its mapped local assignment (`LocalChecks`), and edge compatibility of the mapped locals.
  - `CompletePass` (`RuntimeLineage.lean:243`): `Pass ∧ AcquisitionEndpoint.Readout`.
  - `FullSubcheck` (`RawHandoff.lean:144`): `∃ ha hr, Nonempty (SparseFullCertificate ...)`, an invariant certificate (see below).
- `ReceiverGate.Subcheck` (`ReceiverGate.lean:42`): receiver-content laws plus intervention control laws, with endpoint active.
- `ScopeCheck` (`FinalHandoff.lean:42`): `retainedRouteStatus ... = .routeIndexed ∧ recognitionStatusOf m = .notAddressed`. The second conjunct is constant (`RawHandoff.lean:156`: `recognitionStatusOf _ := .notAddressed`).

**Gate O** (`:50`) is identical except that it uses `OperationalSubcheck` (an operational certificate) in place of `FullSubcheck`.

**Readout P: `IntegratedTargetRealization`** (`FinalHandoff.lean:25` → `RawHandoff.lean:134` → `HistoricalPackageRuntime.lean:49`):
```lean
(∀ c k, k ∈ m.package.cover.scopes c → target m a k = mappedLocal ... c k) ∧
(∀ k, (target m a k).isSome = true) ∧ m.package.clauses.accept (target m a)
```
The computed global target assignment restricts to every stage-mapped local and is total. It satisfies all eight dispatcher clause rules: `Package.accept p a := ∀ k, (p.rule k).accept a` (`ClauseDispatcher.lean:171`). The clause rules C1–C8 are fixed algorithms; I did not unfold them.

**Readout L: `StrictTemporalLineage`** (`FinalHandoff.lean:39` → `RawHandoff.lean:137` → `RuntimeLineage.lean:240`):
`CoreReadout raw (target m a) ∧ AcquisitionEndpoint.Readout raw.endpoint (target m a)`, where `CoreReadout` (`RuntimeLineage.lean:138`) has seven conjuncts:
1. `CorridorReadout` (`:123`): for every route `r`, the computed acquisition legs `ls` satisfy `StrictCorridorWitness ls` (TTH-04's object; see item 3).
2. `SeedReadout` (`:126`): seed coherence of the executed corridor.
3. `FactorReadout` (`:45`): decoded factor-transport equations.
4. `RecordReadout` (`:133`): every source record arrow transports to a target arrow.
5. `RetainedRouteReadout`: route status `routeIndexed`.
6. `ExecutionBridge.SemanticReadout` (`SemanticExecutionBridge.lean:108`): both carriers' execution frontiers satisfy `SemanticReadout` (`SemanticExecutionBridge.lean:17`). This includes `FullFutureSufficient`: equal predictive codes imply equal probabilities of every finite observation trace under every action word (`Transport/FullFuture.lean:38`). It also includes the bridge `Laws` (`ExecutionBridge.lean:48`): the translation commutes with initial states, row weights, successors and observations on the whole source closure.
7. `SharedExecution` (`:115`): both frames' schemas equal the runtime schema, and the execution links pass.

**Readout AF: `PostWithdrawalFullAutonomy`** (`FinalHandoff.lean:28`) is `NominalHandoff.FullAutonomy` (`NominalHandoff.lean:54`):
`Pass m r (target m a) ∧ OwningHandoff.PostWithdrawalFullAutonomy m a`.
The second conjunct is `HistoricalPackageRuntime.SparseFullAutonomy (autonomy m) a` (`RawHandoff.lean:139`, `HistoricalSparseRuntime.lean:31`):
`∃ ha hr, StrictSparseGame.Readout rows update Entries Withdrawal PackageAt ResourceClosed Legal StepLaw`.
`StrictSparseGame.Readout` (`StrictSparseGame.lean:20`) is `StrategyGame.GameReadout` with `legal` strengthened by `StrictSparse` (every listed weight of the selected row is positive, `:13`). `GameReadout` (`StrategyGame.lean:52`) is:
```lean
withdrawal ∧ (∃ r, entries r) ∧ ∃ strategy, ∀ entry, entries entry → ∀ r past,
  Play rows update strategy entry (r :: past) →
  package r ∧ resourceClosed r ∧ ∀ d, responseLegal r d (strategy (r::past) d) ∧
    Normalized rows r d (strategy (r::past) d) ∧
    ∀ o, PositiveSupport rows r d (strategy (r::past) d) o → transitionLaw r d (strategy ...) o
```
`Play` (`:37`) is the inductive set of histories generated by the strategy, following every positive-support outcome. `Normalized` (`:29`) means nonnegative weights summing to 1 with some positive entry. The instantiation is:
- `entries = HistoricalAcquisition.Entry` (`HistoricalAcquisition.lean:153`): registers reached by one positive-support response step after a genuine arrival.
- `withdrawal = DomainCheck ∧ WithdrawalCheck` (`ResourceRuntime.lean:109,117`): all six roles removed, removed and retained resources disjoint.
- `package = PackageAt` (`HistoricalPackageRuntime.lean:66`): `IntegratedTargetRealization ∧ Inside ∧ clauses.accept (runAssignment r)`.
- `resourceClosed = ResourceClosed` (`ResourceRuntime.lean:130`): required resources target-owned, retained and with positive balance; removed accounts not retained; source absent; writer present.
- `Legal` (`:141`): the charge is target-owned, uses only retained resources and is affordable.
- `StepLaw` (`:154`): the next state is resource-closed, balances update exactly, and order, ticks, progress and record all strictly advance.

**Readout AO: `PostWithdrawalOperationalAutonomy`** (`FinalHandoff.lean:30`) is `Pass ∧ SparseOperationalAutonomy` (`HistoricalSparseRuntime.lean:60`). It is the same game with `package := ResourceRuntime.Inside` (the factor register is in the declared factor list) instead of `PackageAt`. AO therefore does not require P at each run.

Skipped: the internals of the eight clause algorithms, `AcquisitionEndpoint.Readout`, `ReceiverContent.Laws`, the `NominalProtocol.check` fields (`NominalProtocol.lean:~100-125`), and the register interpreter.

### (d) Plain-English statement
For every handoff model `m` built from the raw interface (`OwningHandoff.RawHandoff` together with nominal-protocol and receiver recipes) over arbitrary types, and every partial source assignment `a`, the following holds. If the F gate passes, then three things hold for the target assignment computed from `a`:
- it is a total, cover-consistent gluing that satisfies all eight clause rules;
- the complete runtime lineage readout holds (strict corridor witness for every route, all-word future sufficiency on both carriers, bridge transport laws, and the typed endpoint rule);
- the nominal protocol passes and there is a causal strategy under which every generated play from every genuine post-withdrawal entry stays package-valid, resource-closed, legal, strictly sparse and normalized, with every positive-support successor obeying the step law.

The O version has the same hypotheses and conclusions, except that the last item requires only membership in the declared factor domain, not the package, along plays. Separately, `full_autonomy_implies_package` says that the F autonomy readout alone implies `IntegratedTargetRealization`.

### (e) What it does NOT say
- It does not say the three F readouts are independent. AF implies P (`full_autonomy_implies_package`, `FinalHandoff.lean:71`, via `StrategyGame.game_entry_package`, `StrategyGame.lean:166`). The registry wording "none of the three is inferred from either of the others" is true only proof-structurally (the P conjunct is not derived from AF). It is false as a logical-independence claim for F. The ledger's TTH-06-GEN wording discloses this correctly.
- It does not give a converse: a valid target need not have a passing gate. For the autonomy subcheck there is an iff (`OwningHandoff.full_subcheck_iff`, `RawHandoff.lean:240`; certificates are semantically complete). There is no such iff for the package or lineage gates.
- Robustness is under nominal disturbances only. Plays quantify over the disturbances of the raw execution and over positive-support outcomes of the selected action. Nothing is said about unselected actions, perturbations of the rows, or resource shocks.
- `StrictSparse` is a representation-sensitive syntactic condition on listed weights, not a stochastic property.
- The receiver readout and `ScopeCheck` are in the gate but not in the theorem's conclusion. They are concluded separately by `receiver_soundness_F/O` (`FinalHandoff.lean:64,67`). `recognitionStatusOf` is a constant.
- The public signature has no `Fintype` hypotheses, but the gate imposes finiteness internally: `ResourceRuntime.DomainCheck` requires finite lists covering every disturbance, action, outcome, factor and resource. Unbounded run contexts remain permitted. (Corrected after Eddy's W2b review.)
- It does not say any instance exists. That is `POS04FinalHandoff.positive_F/O`, below.

### (f) Substantive or definitional?
**The top-level theorem is definitional plumbing.** `FinalHandoff` soundness is `NominalHandoff.soundness_F m.base m.nominal a h.1` (`FinalHandoff.lean:57`): it projects the first gate conjunct and discards the receiver and scope checks. `NominalHandoff.soundness_F` (`NominalHandoff.lean:112`) is a tuple rearrangement whose protocol conjunct of AF is copied from the gate (`h.2.1`). `OwningHandoff.temporalFIACHCertificateSoundness_generic_F` (`RawHandoff.lean:188`) pairs three lemmas applied to three gate conjuncts. The mathematical content is in those three lemmas:
1. Package: `OwningHandoff.package_soundness` → `DispatchedPackage.constructs` (`DispatchedPackage.lean:36`) → `PackageEngine.constructs` (`PackageEngine.lean:28`). This is genuine but short. `glued_restricts` (`Substrate.lean:250`) propagates edge equality along running-intersection paths (`PackageTheory.localEqualityAlongScopedReach`, `Package/FiniteGluing.lean:49`), and each clause's locality transfers local acceptance to the global assignment.
2. Lineage: `RuntimeLineage.complete_soundness` (`RuntimeLineage.lean:246`) → `RuntimeLineage.soundness` (`:152`). Five of the seven `CoreReadout` conjuncts are copied verbatim from `Pass` (Seed, Factor, Record, RetainedRoute, SharedExecution), and the endpoint readout is copied too. Two conjuncts carry content:
   - `AcquisitionCorridor.constructs` (`AcquisitionCorridor.lean:151`), which calls TTH-04 (item 3, itself shallow);
   - `ExecutionBridge.semantic_soundness` → `ExecutionFrontier.semantic_soundness`, which uses `FutureLumping.all_words` (`FutureLumping.lean:27`): one-step code-respecting fiber masses imply all-word trace equality, by induction. **This is the most substantive mathematical step in the lineage lane.**
3. Autonomy: `HistoricalPackageRuntime.sparse_full_soundness` → `StrictSparseGame.soundness` → `StrategyGame.invariant_game_soundness` (`StrategyGame.lean:149`). This is genuine. It builds a causal strategy from an invariant certificate by choice (`selected`, `causalStrategy`, `:100-128`) and proves by induction on `Play` that every generated history stays inside the invariant (`every_play_inside`, `:130`). This is the standard controlled-invariance argument.

`full_autonomy_implies_package` is a one-line projection: the game at a genuine entry yields `PackageAt`, whose first conjunct is `IntegratedTargetRealization`. It holds because P is built into the definition of F's `package` predicate.

### POS-04 instance: `positive_F`, `positive_O`
- `POS04FinalHandoff.positive_F : FinalHandoff.HandoffPass_F (raw (protocol baseline)) baseline.assignment` (`POS04FinalHandoff.lean:66`).
- `positive_O`: same with `HandoffPass_O` (`:71`).
- `baseline` (`Targets/ComputedFIACH/Models.lean:13`) is `⟨canonical, [.targetRecharge], removedRoles, false⟩`: the canonical POS-04 assignment with the target recharge retained, the declared roles removed, and source presence false after withdrawal.

Together with the generic theorems, these show that this one concrete finite two-carrier model (one carrier-changing leg) passes both gates, so all three readouts hold there.

The proof goes through `full_gate_iff_nominal` (`:42`). On POS-04 models the receiver subcheck and `ScopeCheck` follow from the package and lineage gates (`POS04ReceiverGate.checked_of_package_lineage`, `POS04ReceiverGate.lean:33`). The `OwningHandoff`-level pass is `POS04RawHandoff.positive_F` (`POS04RawHandoff.lean:195`), which assembles kernel-checked finite facts.

### "Logical independence" of the O version
The proving declaration is `CSTTT.TargetTheory.GenericHandoff.POS04FinalHandoff.temporalFIACH_three_lane_separation` (`POS04FinalHandoff.lean:111`):
```lean
(∃ m : Model, ∃ a, ¬ P m a ∧ L m a ∧ AO m a) ∧
(∃ m : Model, ∃ a,  P m a ∧ ¬ L m a ∧ AO m a) ∧
(∃ m : Model, ∃ a,  P m a ∧ L m a ∧ ¬ AO m a)
```
`P`, `L` and `AO` are the `FinalHandoff` readouts, and `Model` is `FinalHandoff.Raw` specialized to POS-04 types (`:13`). The witnesses are three raw edits of `baseline` (`Models.lean:14-19`):
- `packageDeletion`: cell `publishedC := none`;
- `lineageDeletion`: event `mix2` loses source support;
- `withdrawalDeletion`: retained resources set to `[]`.

The facts come from `O_control_vectors` (`:79`).

Meaning: each readout can fail while the other two hold, so none follows from the conjunction of the other two. This is not full independence of all eight truth patterns; for example, a model with ¬P ∧ ¬L ∧ AO is not exhibited.

The F analogue, `F_control_vectors` (`:95`), shows that package deletion kills both P and AF. That is consistent with AF ⇒ P, so there is no F separation theorem.

Lower-level duplicates of this result:
- `POS04RawHandoff.temporalFIACH_three_lane_separation` (`POS04RawHandoff.lean:184`), at the `OwningHandoff` level;
- `ComputedFIACH.operational_readouts_logically_independent` (`Targets/ComputedFIACH/Assembly.lean:205`), on the fixed finite POS-04 lane model;
- `operational_lanes_logically_independent` (`:131`), on its Boolean checks.

---

## 2. TTH-07: `native_full_temporal_composition` and `FullHandoffCertificate`

### (a) Locations
- `CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationReturn.native_full_temporal_composition`, `Targets/GenericHandoff/NativeComposition/PublicationReturn.lean:197`.
- `CSTTT.TargetTheory.FullHandoffCertificate`, `Targets/Composition.lean:21`.
- `FullHandoffData` `:7`, `FullHandoffCompatible` `:31`, `composeFullHandoffData` `:46`, `fullTemporalHandoffComposition` `:62`.

### (b) Statements
```lean
-- PublicationReturn.lean:197
theorem native_full_temporal_composition (h : Factor) :
    Nonempty (FullHandoffCertificate (composeFullHandoffData
      (summary NativePackageBundle.canonical canonical_ready true h)
      (summary NativePackageBundle.canonical canonical_ready false h)))

-- Composition.lean:62 (generic)
theorem fullTemporalHandoffComposition {left right : FullHandoffData Package Signature}
    (leftCert : FullHandoffCertificate left) (rightCert : FullHandoffCertificate right)
    (interface : FullHandoffCompatible left right) (endpointsDistinct : left.source ≠ right.target) :
    Nonempty (FullHandoffCertificate (composeFullHandoffData left right))
```
Here `Factor = Bool × Bool × Bool` (`NativeComposition/Factor.lean:9`), the 8-state factor, and `Owner = Bool` indexes the hop (`true` is the first hop, `false` the second).

### (c) Definitions
- `FullHandoffData` (`Composition.lean:7`) is a record with: `source target : CarrierId`; `sourcePackage targetPackage : Package`; `entry exit : Signature`; `routeStatus`; `targetOwner`; and **`realized lineage autonomous : Prop`**.
- **`FullHandoffCertificate d`** (`:21`) is a structure of five proofs: `d.source ≠ d.target`, `d.targetOwner = d.target`, `d.realized`, `d.lineage`, `d.autonomous`. It is not a gate. It is the conjunction of the conclusions, applied to whatever propositions the summary record carries.
- `FullHandoffCompatible left right` (`:31`):
  `left.target = right.source ∧ left.targetPackage = right.sourcePackage ∧ left.exit = right.entry ∧ left.targetOwner = right.source ∧ (both flat ∨ neither unresolved)`.
- `composeFullHandoffData` (`:46`): source from left, target from right, entry from left, exit from right; `realized := left.realized ∧ right.realized`; `lineage := left.lineage ∧ right.lineage`; `autonomous := right.autonomous`.
- The concrete summary `PublicationReturn.summary b hb cell h` (`PublicationReturn.lean:110`) fills the Prop fields with defined predicates:
  - `realized := Realized b hb cell h` (`:100`): both closed native packages accept, receiver content is faithful, the receiver square holds, and the actual first entry exists and is an entry whose packed register equals the target root.
  - `lineage := Lineage b hb cell h` (`:105`): `FullFutureComposition.Laws` (`FullFutureComposition.lean:12`; translation commutes with observation, weight and next on the source closure, image injective) ∧ the computed leg passes `AtomicLegPass` ∧ `RawTransportLane`.
  - `autonomous := ControllerWins b hb cell safeController` (`PublicationComposition.lean:64`): the `GameReadout` shape of item 1 with a fixed explicit controller.
  - `entry` and `exit` are the computed `Signature` (run, whole future model, root, corridor stage), `:13-29`.
  - `targetOwner` is the owner observed at the target root.
  - Carriers are 17, 55 and 101.

### (d) Plain-English statement
For each of the 8 factor values `h`, the composite of the two concrete hop summaries of the canonical native two-hop model (carrier 17 → 55 → 101) satisfies:
- distinct endpoints (17 ≠ 101);
- the final target owns itself;
- both hops are realized;
- both hops satisfy their lineage readout (one-step full-future transport laws, a passing atomic leg, raw credit and joint transport);
- the final hop's explicit controller wins its post-withdrawal game.

### (e) What it does NOT say
- It is not a generic composition theorem; it is one concrete instance. The generic `fullTemporalHandoffComposition` **does not use its `interface` hypothesis**: the proof term (`Composition.lean:70-76`) never mentions it. So the generic "compose when interfaces agree" theorem proves nothing that depends on agreement.
- The composite `lineage` is just the conjunction of the two hops' lineage propositions. No composite whole-chain future or corridor law is concluded here. Such a law exists separately as `computed_temporal_composition` (`PublicationReturn.lean:85`; `future_composition`, `corridor_composition`).
- The composite `autonomous` is only the last hop's autonomy.
- Interface agreement on this instance is proved separately (`actual_interface`, `:186`; `whole_signature_middle`, `:136`) but is not a conjunct of the conclusion.
- Its scope is a single designed model: unit disturbances, aliased roles, receiver ignoring history (per the ledger).

### (f) Substantive or definitional?
The generic composition theorem is definitional: the composite certificate's fields are pairs and projections of the input certificates. The instance's content lives in:
- `actual_certificate` (`:181`): `actual_realized` (`:166`), `actual_lineage` (`:172`), `canonical_controller`, and `actual_target_owner` (`:154`);
- `whole_signature_middle` (`:136`);
- upstream kernel computations in `PublicationFuture`, `PublicationCorridor` and `PublicationReplay`.

Those are computed facts about one model, not general mathematics.

---

## 3. TTH-04: `strictTemporalCorridorComposition_generic`

### (a) Location
`CSTTT.CorridorTheory.AtomicChain.strictTemporalCorridorComposition_generic`, `Corridor/AtomicChain.lean:376`.

### (b) Statement
```lean
theorem strictTemporalCorridorComposition_generic (legs : List FiniteAtomicLeg)
    (h : CorridorPass legs) : StrictCorridorWitness legs
```

### (c) Definitions
- `FiniteAtomicLeg` (`:66`): concrete data. It has source and target carrier codes (`Nat`), a list of `RawStage` (support list, a `realized` flag, and a `Frontier` of eight fields: predictive, order, tick, progress, record, residue, maintenance, owner; `:11-26`), events, dependencies, per-step `ReadoutUpdate` recipes, projections and audit event ids.
- `AtomicLegCheck l : Bool` (`:174`) is the conjunction of:
  - source ≠ target and at least 3 stages;
  - the entry support is exactly {source} and the exit support exactly {target}, with matching owners;
  - every stage is realized, with nonempty support and owner in support;
  - some stage contains both carriers (mixed support);
  - events have unique ids, valid stages and owners;
  - all dependencies point forward in stage (`dependencyCheck`, `:88`);
  - `readoutCheck` (`:124`): there is one update per adjacent stage pair, and `readoutStep` (`:103`) holds. That step check requires predictive += advance; order, tick, progress and record each += a strictly positive advance; residue appended by a nonempty list; nonempty maintenance; and owner in support;
  - `interventionCheck` (`:165`): additive projection nonredundancy or mixed-support removal, plus `auditCheck` (`:93`);
  - `routeStatusOf l = .routeIndexed` (`:147`).
- `AdjacentFrontierCheck a b` (`:192`): `a.target = b.source ∧ exit a = entry b` (the whole stage, hence the full frontier) plus redundant residue and owner equalities.
- `chainCheck` (`:197`): every leg passes `AtomicLegCheck` and consecutive legs pass `AdjacentFrontierCheck`.
- `CorridorPass legs` (`:257`): `legs ≠ [] ∧ chainCheck legs = true ∧ first source ≠ last target`.
- `StrictCorridorWitness legs` (`:268`) has five fields:
  1. `pass : CorridorPass legs`;
  2. `derivation : ChainDerivation legs` (an inductive single/prepend derivation, `:252`);
  3. every leg passes `readoutCheck`;
  4. every stage in `chainStages` is realized;
  5. every readout edge strictly increases order, tick, progress and record.

### (d) Plain-English statement
For every nonempty finite list of atomic legs that individually pass the Boolean atomic check, that agree exactly at each join (same intermediate carrier, identical boundary stage including its whole eight-field frontier, residue and owner), and whose first source differs from the last target, the following holds. The chain admits an inductive derivation, every leg's per-step readout recipes hold, every stage of the concatenated stage list is realized, and every step edge strictly increases order, tick, progress and record.

### (e) What it does NOT say
- It does not compose arbitrary corridors. The hypothesis already contains every per-leg and per-join check; the witness repackages them.
- It makes no claim about route flatness (only route-indexed status), physical time, or continuity beyond these Boolean checks.
- The statement is on concrete `Nat` and `String` data, not abstract carriers.

### (f) Substantive or definitional?
Close to definitional. Each witness field is extracted from `chainCheck` by list induction (`chain_derivation`, `chain_each_pass`, `chain_realized`, `:279-334`). The only arithmetic is `readout_step_strict` (`:116`): a positive increment implies a strict inequality, by `omega`. The genuine instance content (the 17 → 55 → 101 COR-POS-02 chain) lives in kernel `decide` proofs elsewhere.

---

## 4. TTH-01: `acyclicLocalWitnessGluing`; TTN-08: cyclic obstruction

### 4a. TTH-01

**(a)** `CSTTT.PackageTheory.acyclicLocalWitnessGluing`, `Package/FiniteGluing.lean:104`. It is a `noncomputable def` producing a structure.

**(b)**
```lean
noncomputable def acyclicLocalWitnessGluing {Index Coord Value : Type}
    (tree : RootedJoinTree Index Coord) (localAssignment : Index → Coord → Value)
    (accepted hardGate : Index → Prop)
    (edgeCompatible : ∀ i j c, tree.adjacent i j → tree.scope i c → tree.scope j c →
        localAssignment i c = localAssignment j c)
    (allAccepted : ∀ i, accepted i) (allHardGates : ∀ i, hardGate i) :
    IntegratedPackageWitness tree localAssignment accepted hardGate
```

**(c)**
- `RootedJoinTree` (`:23`) has fields:
  - `root` and `parent : Index → Option Index`, with the root having no parent and every nonroot having a parent;
  - `rank`, with the parent's rank strictly smaller;
  - `scope : Index → Coord → Prop`;
  - `covers : ∀ c, ∃ i, scope i c`;
  - `runningIntersection`: any two indices whose scopes contain `c` are joined by a `ScopedReach` path, that is, a path in the undirected parent graph through indices whose scopes all contain `c` (`ScopedReach`, `:7`).
- `adjacent i j := parent i = some j ∨ parent j = some i` (`:43`).
- `IntegratedPackageWitness` (`:91`): `global : Coord → Value`, a restriction property, `∀ i, accepted i`, and `∀ i, hardGate i`.
- `gluedAssignment` (`:66`) picks, by choice, one covering index per coordinate.

**(d)** For arbitrary index, coordinate and value types, and any rooted parent presentation whose scopes cover every coordinate and satisfy the path form of running intersection, the following holds. A family of local assignments that agree on shared coordinates along every parent edge determines a global assignment that restricts to every local assignment on its scope. The witness also records the supplied acceptance and hard-gate premises unchanged.

**(e)**
- It does not conclude global acceptance; acceptance and hard gates are passed through.
- **Finiteness is absent from the statement**: `Index` and `Coord` are arbitrary types and no finiteness hypothesis appears. **Rootedness and rank decrease are hypotheses that the proof does not use.** The proof (`gluedAssignmentAgrees`, `:73`) uses only `covers`, `runningIntersection` and edge compatibility. (Corrected after the W2b review.)
- It does not say the glued assignment is unique (it is, on covered coordinates, but that is not stated).

**(f)** Substantive but elementary: equality propagates along a path by induction (`localEqualityAlongScopedReach`, `:49`). Acceptance fields are definitional pass-through, as the inventory notes.

### 4b. TTN-08

**(a)** The ledger name `CSTTT.POS04.Assigned.ActualCyclePrototype.actual_pos04_cyclic_obstruction` is in file `POS04/Assigned/CyclicObstruction.lean:95` (namespace `ActualCyclePrototype`, `:4`). There is one declaration with two descriptions.

**(b)**
```lean
theorem actual_pos04_cyclic_obstruction :
    AssignedPackagePass canonical .target ∧
    (∀ clause, clauseAccept (actualLocal clause) .target clause) ∧
    (∀ clause, clauseGate (actualLocal clause) .target clause) ∧
    (∀ left right, adjacent left right → ∀ cell, cell ∈ clauseScope .target left →
        cell ∈ clauseScope .target right → actualLocal left cell = actualLocal right cell) ∧
    (∀ left right, Cell.rows .target ∈ clauseScope .target left ∧ Cell.rows .target ∈ clauseScope .target right) ∧
    ¬ ∃ global : Assignment, GlobalRestriction global
```

**(c)**
- `adjacent` (`:41`): the 8-cycle C1–C2–…–C8–C1 via `rank` mod 8.
- `shifted` (`:8`): the canonical assignment with the `positions` table replaced by `publicPosition s + 1`.
- `base c := if c = .c6 then shifted else canonical` (`:43`).
- `actualLocal c := decode (clauseScope .target c) (base c)` (`:45`): the restriction to the clause's actual read scope.
- `clauseScope` (`POS04/Assigned/Substrate.lean:104`): `positions` is in C1, C2, C3, C4 and C6 (via `commonScope`, `:102`), but not in C5, C7 or C8.
- `GlobalRestriction g` (`:83`): `∀ clause cell, cell ∈ scope clause → g cell = actualLocal clause cell`.

**(d)** On the declared POS-04 target domain, the canonical assignment passes the package. The eight local assignments (seven canonical restrictions, plus C6 restricted from a position-shifted table that C6 still accepts) are each accepted and gated by their own clause. They agree on every shared cell along every edge of the 8-cycle, and every pair shares the `rows` cell. Yet no global assignment restricts to all eight.

**(e)**
- The obstruction is not a holonomy around the cycle. C6 is the only shifted local. It shares `positions` with C1–C4, but neither of its cycle neighbours (C5, C7) reads `positions` (`no_adjacent_c6_positions`, `:60`). The scope of `positions` is disconnected on the cycle (`positions_no_scoped_path`, `:119`), so running intersection fails. The cycle shape is incidental; a path graph with the same scopes would fail the same way.
- The ledger's TTN-08 wording ("two pieces that are not adjacent ... read a common cell and disagree on it"; running intersection is what excludes it) is accurate. A "cyclic obstruction" title should not suggest topological content.
- Not every local is a restriction of one assignment; that is by design.

**(f)** The proof is short. Disagreement at one coordinate (`p0w0`: 0 vs 1, `no_actual_global_restriction`, `:85-91`) rules out any global assignment. The local acceptance of `shifted` by C6 is kernel `decide` (`:9-31`).

---

## 5. TTH-05: `postWithdrawalFiniteHorizonInvariance` and `ExactAutonomyCertificate`

**(a)** `CSTTT.AutonomyTheory.postWithdrawalFiniteHorizonInvariance`, `Autonomy/FiniteAutonomy.lean:87`. `ExactAutonomyCertificate` is at `:19`; `ExactAutonomyData` at `:6`.

**(b)**
```lean
theorem postWithdrawalFiniteHorizonInvariance {d : ExactAutonomyData}
    (cert : ExactAutonomyCertificate d) (word : List d.sys.Disturbance) :
    ∃ y, ControlledRun d d.endpoint word y ∧ d.sys.packageValid y
```

**(c)**
- `ControlledSystem` (`Autonomy/System.lean:5`) has:
  - a carrier with a finite enumeration of states, plus finite enumerations of disturbances and actions;
  - **`step : State → Disturbance → Action → State → Prop` (a relation)**;
  - `packageValid`, `actionOwner` and `maintenanceResources`.
- `WithdrawalSpec` (`System.lean:15`): removed and retained resource lists that are disjoint, and six Prop flags (`sourceRemoved`, and so on).
- `ExactAutonomyData` (`:6`): system, endpoint, withdrawal, `inside` region, `resourceOwner`, and `antiStall` and `budgetSolvent` relations. It also carries two Prop flags: boundary and disturbance class fixed before evaluation.
- `ExactAutonomyCertificate` (`:19`) has fields proving:
  - the six withdrawal flags and the two "fixed before evaluation" flags;
  - `endpointInside`;
  - `packageInside` (inside ⇒ packageValid);
  - `resourceClosed` (maintenance resources at inside states are retained);
  - retained resources are target-owned;
  - `response`: ∀ x inside, ∀ disturbance, **∃ action, ∃ x'**, with a target-owned action, `step x d action x'`, x' inside, anti-stall and budget-solvent.
- `ControlledRun` (`:49`): an inductive run along a disturbance word whose every step has these properties.

**(d)** Given an exact autonomy certificate, for every finite disturbance word there exists a run from the endpoint answering the word with target-owned, anti-stalling, budget-solvent steps that stay inside the invariant region, and the final state satisfies the package predicate.

**(e)**
- Existence is angelic: since `step` is a relation and the certificate supplies *some* successor `x'`, the theorem does not cover all nondeterministic successors. For deterministic `step` this is moot. Contrast item 1, where every positive-support outcome is covered.
- It covers finite horizon only, not an infinite run (see TTS-04).
- Withdrawal, ownership and "fixed before evaluation" are Prop flags supplied in the data, not computed.
- Finiteness of states is present in the type but unused.
- The theorem itself is not about POS-04; the POS-04 instance is via `positive_each_entry_*` (supplemental).

**(f)** Elementary, but not mere projection: induction on the word (`finiteHorizonRunExists`, `:67`) followed by `packageInside`. This is a standard viability-kernel argument.

---

## 6. TTH-08: `native_relation_valued_temporal_fission`; TTN-11

### 6a. TTH-08

**(a)** `CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission.native_relation_valued_temporal_fission`, `Targets/GenericHandoff/NativeComposition/FissionRelation.lean:96`.

**(b)**
```lean
theorem native_relation_valued_temporal_fission :
    fork.related fork.source fork.left ∧ fork.related fork.source fork.right ∧
    (∀ target, fork.valid target ↔ target = fork.left ∨ target = fork.right) ∧
    (∀ target, fork.valid (fork.swap target) ↔ fork.valid target) ∧
    (∀ target, fork.swap (fork.swap target) = target) ∧ ¬ InvariantSingleton canonicalRaw
```

**(c)**
- `fork` (`:80`) is the data source ⟨17⟩, left ⟨201⟩, right ⟨202⟩, `related := Continuation canonicalRaw`, `valid := ValidTarget canonicalRaw`, `swap := swapOwner`.
- `ValidTarget r t` (`:11`): `∃ hr branch, Readout r ∧ t = ⟨branchTarget branch⟩ ∧ ∀ h, Nonempty (FullHandoffCertificate (summary r hr branch h))`. Here `branchTarget false = 201` and `true = 202` (`FissionNames.lean:24`), and `FullHandoffCertificate` is as in item 2.
- `Continuation r s t := s = ⟨17⟩ ∧ ValidTarget r t` (`:15`).
- `swapOwner x := ⟨transpose 201 202 x.code⟩` (`FissionNames.lean:66`): it swaps carrier codes 201 and 202 and fixes all others.
- `canonicalRaw := ⟨fun _ => NativePackageBundle.initial, fun _ => false⟩` (`FissionReadout.lean:17`): both branches receive the same initial bundle, so the fork is symmetric by construction.
- **Invariant singleton selector, exactly as in Lean** (`FissionRelation.lean:57`):
  ```lean
  def InvariantSingleton (r : Raw) : Prop :=
    ∃ selected, Continuation r ⟨17⟩ selected ∧ swapOwner selected = selected
  ```
  That is: some continuer of source 17 is a fixed point of the target swap. The function form is `no_equivariant_selector` (`:73`). There is no `select : Raw → CarrierId` such that `select canonicalRaw` is a continuer and `select (exchange r) = swapOwner (select r)` for all `r`. Here `exchange` swaps the two branches' raw inputs (`:68`), and `exchange canonicalRaw = canonicalRaw` holds by `rfl` (`:72`).

**(d)** In the canonical symmetric native fork, source 17 continues to both 201 and 202. The valid targets are exactly 201 and 202, each carrying a full handoff certificate (realized, lineage and controller autonomy) for every factor value. The target swap preserves validity and is an involution. No continuer is fixed by the swap.

**(e)**
- The result is about one model, not a general theorem about all symmetric forks.
- "No invariant selector" means only that no continuer is a fixed point of `swapOwner`. Since the continuers are exactly {201, 202} and the swap exchanges them, this is immediate. It does not exclude non-equivariant selections; `constant_choice_is_valid` (`:107`) shows that choosing 201 is a valid continuation.
- It says nothing about identity (see TTF-07).
- The symmetry is built in (both branches receive identical inputs).

**(f)** The fission conclusions are short logic over `valid_target_iff` (`:17`). The content is in `computed_full_fork` (`FissionReturn.lean:85`) and `canonical_readout` (`FissionReadout.lean:143`): the kernel-checked fact that both branches carry full handoff certificates. The selector obstruction is two lines (`:59-66`).

### 6b. TTN-11

**(a)** `CSTTT.RealControls.ttn11_exists` (`Countermodels/RealControls.lean:612`) and `ttn11_no_invariant_unique_selector` (`:594`).

**(b)**
```lean
theorem ttn11_no_invariant_unique_selector :
    (∀ t : ForkTarget, forkRelated .p1w0 t → forkValid t → forkValid (forkSwap t)) ∧
    ¬ ∃ selected : ForkTarget, forkRelated .p1w0 selected ∧ forkValid selected ∧ forkSwap selected = selected

theorem ttn11_exists :
    ∃ d : TemporalFissionData KState ForkTarget, TemporalFissionCertificate d ∧
      forkCarrierId false ≠ forkCarrierId true ∧
      (∀ t, d.related d.source t → d.valid t → d.valid (d.swap t)) ∧
      ¬ ∃ selected, d.related d.source selected ∧ d.valid selected ∧ d.swap selected = selected
```

**(c)**
- `ForkTarget := {branch : Bool, endpoint : KState}` (`:360`).
- `forkSwap t := {t with branch := !t.branch}` (`:562`).
- `forkRelated` (`:551`): a receiver output equality plus membership in the two fork edges.
- `forkValid` (`:554`): `ForkPackagePass` (`:521`), `ForkAutonomyPass` (`:504`), membership in the greatest viable set, corridor and bridge pass, carrier distinctness, and endpoint `p1w0`.
- `TemporalFissionCertificate` (`Corridor/Fission.lean:15`): distinct targets, both related, both valid, and the swap exchanges them.
- **Invariant selector here:** an element `selected` related to the source, valid, and with `forkSwap selected = selected`. "Unique" does not appear in the Lean statement.

**(d)** There is a symmetric two-target fork on the POS-04 finite model, with distinct target carriers, in which the swap maps valid continuers to valid continuers and no valid continuer is swap-fixed.

**(e)** **The ¬∃ clause does not depend on validity** (the checked fork itself is nonempty; corrected after W2b review). `forkSwap` flips a Boolean and has no fixed points at all (proof: `cases selected.branch <;> simp [forkSwap] at hb`, `:608-610`). It would hold for any relation and validity predicate. The content is in the certificate (`ttn11_symmetric_fork_certificate`, `:570`): both branches pass the package and autonomy checks.

**(f)** The selector part is trivial. The certificate part is a finite computed check.

---

## 7. TTF-07: `actual_branch_identity_return` and `IdentityUnderdetermined`

**(a)** `CSTTT.FallbackTheory.StructuralAdjudication.actual_branch_identity_return`, `Fallback/StructuralAdjudication.lean:106`. `IdentityUnderdetermined` is at `:81`.

**(b)**
```lean
theorem actual_branch_identity_return (affected : Owner) (leftNames rightNames : Owner → CarrierId)
    (history : Factor) (length : Nat) :
    ∃ commands finished state,
      SafeCommands commands ∧ commands.length = length+1 ∧
      extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
        (withdrawnReady affected) history commands = some finished ∧
      finished.read (5+length) = some state ∧ finished.read (6+length) = some state ∧
      PostWithdrawalQualifiedPrototype.qualifiedPackageAt (withdrawnCurrent affected) false state ∧
      NativeAcquiredWithdrawalPrototype.ContinuationLaw affected false state ∧
      IdentityUnderdetermined (fun source endpoint => ancestryDecision leftNames rightNames
        (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
        (withdrawnReady affected) history commands source endpoint = some true)
        0 (5+length) (6+length)
```

**(c)**
- `IdentityUnderdetermined anc s l r` (`:81`):
  ```lean
  l ≠ r ∧ ∃ i j : Nat → Nat → Prop, Compatible anc s i ∧ Compatible anc s j ∧ i ≠ j ∧
    i s l ∧ ¬ i s r ∧ j s r ∧ ¬ j s l ∧
    ¬ (∀ q, Compatible anc s q → q s l) ∧ ¬ (∀ q, Compatible anc s q → q s r)
  ```
- `Compatible anc s q` (`Fallback/IdentityUnderdetermination.lean:14`): `q` is an equivalence relation on node numbers; every non-source node identical to `s` is an `anc`-descendant of `s`; and at most one non-source node is identical to `s`.
- The witnesses are `NumericalIdentity s chosen` (`:12`): x ~ y iff `code x = code y`, with `code s = chosen` and `code n = n` otherwise. This identifies `s` with exactly `chosen`.
- `ancestryDecision` (`Fallback/NativeReceiptExecution.lean:260`) is computed from an actual run of the native world and command ledger. Its result is `some true` iff `source` is the world's source, the seed holds, and `target` is the entry or reachable via the ledger's path bit.

**(d)** For each affected owner, both name maps, each factor value and each length `n`, there is a safe command list of length n+1 whose execution from the canonical withdrawn world succeeds. In the finished world, nodes 5+n and 6+n hold the same state, which satisfies the qualified package and the continuation law. Relative to the computed ancestry relation, the source node 0 has two distinct compatible identity relations, one identifying it with 5+n and the other with 6+n, and no compatible relation is forced to pick either.

**(e)**
- It does not say ancestry implies non-identity, or that identity is undefined. It says that ancestry with two descendants does not determine which (if any) is identical to the source among relations satisfying `Compatible`.
- The identity notion is constrained to equivalence relations with at most one non-source partner of the source. "Unique proper continuer" is built into `Compatible`.
- The original arbitrary-identity schema is refuted separately (`original_identity_schema_rejected`, `:126`).

**(f)** The underdetermination is a pure logical lemma: given anc s l, anc s r and three distinct nodes, the two `NumericalIdentity` relations work (`branching_identity_underdetermined`, `:88`; `two_identity_extensions`, `IdentityUnderdetermination.lean:36`). The execution content (both branches reachable by ancestry, equal states, package and law) comes from `canonical_arbitrary_length_fission` (`Fallback/SafeNativeContinuation.lean:383`).

---

## 8. TTF-05: `original_integrated_temporal_iaps` and `all_actual_outputs_three_lanes`

**(a)**
- `CSTTT.FullNative02.IAPS.original_integrated_temporal_iaps`, `FullNative02/IAPS.lean:76`.
- `CSTTT.FullNative02.IAPS.all_actual_outputs_three_lanes`, `:93`.
- `CSTTT.Prospects.IntegratedTemporalIAPS`, `Prospects/Statements.lean:217`.

**(b)**
```lean
-- Statements.lean:217
def IntegratedTemporalIAPS (Cert : Type) (valid ancestry packageRealized autonomous : Cert → Prop) : Prop :=
  ∀ c, valid c → ancestry c ∧ packageRealized c ∧ autonomous c
-- IAPS.lean:76
theorem original_integrated_temporal_iaps :
    Prospects.IntegratedTemporalIAPS Request Valid Ancestry PackageRealized Autonomous
-- IAPS.lean:93
theorem all_actual_outputs_three_lanes (e : Settlement × Rat)
    (member : e ∈ fusionRows renewable branchesWorld mainRequest) (ready w : World)
    (acquired : outputWarmup e.1.world = some ready) (continuation : Retained 3 ready w) :
    Predictive w 3 ∧ Package.Whole w 3 ∧ Autonomy.Realized 3 w
```

**(c)**
- `Request` (`IAPS.lean:10`): `child (right : Bool) (continuation : List State)` or `output (meetingState : State) (continuation)`. The owner is 1 or 2 for a child and 3 for an output (`:14`).
- `execute` (`:20`) runs the chosen continuation from `branchesWorld` (children) or from a selected fusion world after `outputWarmup` (outputs).
- `Valid r := (execute r).isSome = true` (`:26`).
- **The three lane predicates** (`:27-29`) are all of the form `∀ w, execute r = some w → X w (owner r)`:
  - `Ancestry` uses `Predictive w o` (`FullNative02/PredictiveAncestry.lean:123`):
    - `SourceOwned w o` (`:9`): the owner's access is enabled, and `ancestry w (.birth 0) r.version` holds, where `ancestry` is the transitive closure of the interpreter's ledger edges (`FullNative02/Ancestry.lean:27`); it is least by `ancestry_least`, `:35`;
    - the source world 0 has 6 receipts;
    - for every enabled resident, the native weighted-future law equals the temporal frame's law for every word and trace.
  - `PackageRealized` uses `Package.Whole w o` (`FullNative02/WholePackage.lean:100`): `∃ r key, access w o = some (r, .canonical32, key) ∧ Certificate w o r key`, a structure of C1…C8 component predicates (`:90`); not unfolded further.
  - `Autonomous` uses `Autonomy.Realized o w` (`FullNative02/Autonomy.lean:107`):
    - `Withdrawn w` (source resident absent, no acquisition, empty slots, no external or source custody; `Withdrawal.lean:10`);
    - a quoted viable endpoint;
    - an `AutonomyCertificate` (the old `Autonomy/System.lean:38` shape) whose Prop fields `antiStall`, `budgetSolventOnInvariant` and `targetOwnsMaintenance` are instantiated by defined predicates and proved, plus six withdrawal flags;
    - a two-way simulation between the finite viability rows and the native rows under `FactorLift.lift`, with every lifted world satisfying `Package.Whole`.
- `Retained o start w` (`FullNative02/RetainedHistory.lean:10`): reachable from `start` by the owner's native steps or by any other owner's steps.

**(d)**
- `original_integrated_temporal_iaps`: for every request of the declared protocol, if it executes successfully, the resulting world satisfies, for the request's owner, predictive ancestry from source birth 0, the whole computed eight-condition package, and package-preserving target autonomy after withdrawal.
- `all_actual_outputs_three_lanes`: for every actual fusion row, every successful warm-up of its output, and every world retained from that warm-up (by owner-3 native steps interleaved with other owners' steps), owner 3 satisfies the same three properties.

**(e)**
- **The `valid` hypothesis is not used.** Each lane predicate is already conditional on `execute r = some w`, so the conclusion holds for every request, vacuously for failing ones. The proof begins `intro request _` (`:78`). Nonvacuity comes separately from `both_child_requests_valid` (`:83`) and `acquired_output_request_valid` (`:86`).
- "Ancestry" here is reachability in the ledger graph plus a future-law equality. It is not strict live overlap.
- "Least" is a property of the `ancestry` closure (`Ancestry.lean:35`), not a conjunct of `Predictive`.
- It does not say that a freshly fused output, before warm-up, has the package; the output case requires `outputWarmup`.
- It is a single designed model.

**(f)** The IAPS wrapper is definitional (it projects from `successful_request_three_lanes`, `:40`). The content is in:
- `retained_acceptance`, `retained_source_owned` and `retained_withdrawal`: invariance of acceptance, ownership and withdrawal under `Retained` steps;
- `predictive_from_same_execution` (`PredictiveAncestry.lean:132`);
- `whole_package_from_installed_execution` (`WholePackage.lean:104`);
- `actual_package_preserving_target_autonomy` (`Autonomy.lean:120`);
- kernel computations on the concrete worlds.

---

## 9. TTN-01, TTN-09, TTN-13, TTN-02

### TTN-01: `CSTTT.RealControls.ttn01_exists` (`Countermodels/RealControls.lean:76`)

**(b)**
```lean
theorem ttn01_exists :
    ∃ copy : TaggedState → TaggedState, ∃ stages : List FiniteTemporalStage,
      copy (.source,.p1w0) = (.target,.p1w0) ∧
      rawM .source .p1w0 = rawM (copy (.source,.p1w0)).1 (copy (.source,.p1w0)).2 ∧
      PackagePass .funded .target ∧ TargetAutonomy .funded c8WithdrawnReceiver ∧
      ¬ HasMixedSupport (tagCarrierId .source) (tagCarrierId .target) stages
```

**(c)**
- `rawM tag s := (publicPosition s, rawContinuation tag s)` (`POS04/C2C3.lean:15`): the predictive M readout (position plus lethal-hazard pattern of each action row).
- `PackagePass v tag` (`POS04/Assembly.lean:224`): C1–C8 POS-04 clause passes (C4 and C7 are surrogates).
- `TargetAutonomy v r` (`POS04/Bridge.lean:219`): source absent, the C8 receiver pass holds, and the greatest viable set is nonempty.
- `HasMixedSupport s t stages` (`Corridor/FiniteTemporalCorridor.lean:25`): some stage's support contains both carriers.

**(d)** There is a map sending the source's `p1w0` to the target's `p1w0` with equal predictive readout, together with a stage list containing no stage with both carriers in support. Independently, the funded target passes the POS-04 package and target autonomy.

**(e)** **As stated, `ttn01_exists` is nearly vacuous on the "no corridor" side.** `stages` is existentially chosen and unrelated to the other conjuncts; `stages = []` would satisfy it. The package and autonomy conjuncts do not mention `copy` or `stages`. The meaningful "no strict overlap corridor" content is in:
- `ttn01_no_atomic_corridor` (`:64`): any `AtomicTemporalCorridorData` with these carriers and `stages = detachedStages` has no certificate;
- `ttn01_detached_copy` (`:53`), which also records `NoRealizedGap`.

Even the former is a field projection: `AtomicTemporalCorridorCertificate` has a `mixedSupport` field (`FiniteTemporalCorridor.lean:65,94`). Cite those declarations, not only `ttn01_exists`, if the paper says "the detached reconstruction has no strict corridor".

**(f)** Definitional plus small `decide`/`simp` facts.

### TTN-09: `CSTTT.POS04.ttn09_gap_resume` (`POS04/Countermodels.lean:91`)

**(b)**
```lean
theorem ttn09_gap_resume :
    ∃ v : CorridorVariant,
      Stage.sourceLive ∈ corridorRealized v ∧ Stage.targetExit ∈ corridorRealized v ∧
      Stage.mix1 ∉ corridorRealized v ∧ corridorStrict v = true ∧
      (sourceHistory .repA).getLast? = some .p1w0 ∧ routeTargetEndpoint .a = some .p1w0 ∧
      routeTargetEndpoint .a = routeTargetEndpoint .b ∧ rawM .source .p1w0 = rawM .target .p1w0 ∧
      corridorNoGap v = false ∧ ¬ CorridorPass v
```

**(c)**
- `corridorRealized .gap` drops `mix1` from the realized stages (`POS04/Corridor.lean:13`).
- `corridorNoGap` (`:36`): the realized stages equal the declared stages, and every event's endpoints are realized.
- `corridorStrict` (`:41`): every event is atomic, strict and stage-adjacent.
- `CorridorPass v` (`:79`): mixed count ≥ 2, no gap, strict, paths compose, nonredundant, and exit-event support conditions.

**(d)** In the POS-04 corridor variant with stage `mix1` unrealized, the source-live and target-exit stages remain realized and the events remain strict. The two routes' computed endpoints agree, and source and target `p1w0` have equal predictive readout. The no-gap check fails and the corridor does not pass.

**(e)**
- "Resumed stream" is not formalized; no positive "resumption" predicate exists.
- The endpoint-equivalence conjuncts do not depend on `v`. They are constant facts about the baseline routes.
- No receiver output through the gap is claimed, consistent with the ledger.

**(f)** Kernel `decide` on finite data, plus `neg_corridor_gap_fails`. It is a computed countermodel, not a theorem with general content.

### TTN-13: `CSTTT.POS04.ttn13_same_carrier_boundary` (`POS04/Countermodels.lean:141`)

**(b)** This is a conjunction of three facts:
1. `sameCarrierReencode .p0w0 ≠ .p0w0`;
2. `∀ s, sameCarrierReencode (sameCarrierReencode s) = s`;
3. for all certificate types and predicates, `¬ ∃ cert : TemporalFIACHCertificate ..., cert.source = tagCarrierId .target ∧ cert.target = tagCarrierId .target`.

**(c)**
- `sameCarrierReencode` (`:109`) swaps `p0w0` and `p0w1` and fixes all other states.
- `TemporalFIACHCertificate` (`Targets/TemporalFIACH.lean:17`) has a field `distinct : source ≠ target` (`:28`).

**(d)** A nonidentity involutive re-encoding of the POS-04 target states exists. Separately, no Temporal-FIACH certificate, of any component types, can have its source and target both equal to the target carrier.

**(e)** The two halves are not connected in Lean. The re-encoding is never fed into any certificate or transport predicate. The theorem says nothing about re-encodings failing any semantic transport test; it only records that the certificate type requires distinct carrier ids.

**(f)** Definitional: part 3 is projection of the `distinct` field (`no_same_carrier_fiach`, `:123`); parts 1 and 2 are `decide` and `rfl`.

### TTN-02: `CSTTT.POS04.ttn02_public_shadow` (`POS04/Countermodels.lean:28`)

**(b)**
```lean
theorem ttn02_public_shadow :
    ∃ a b : PointedFactor, a.tag = .target ∧ b.tag = .target ∧
      pointedPublic a = pointedPublic b ∧ pointedHidden a ≠ pointedHidden b ∧
      C4Collision .positive .target
```

**(c)**
- `PointedFactor := {tag, present : KState}` (`:19`).
- `pointedPublic x := c4Current .positive x.tag x.present` (`:23`), where `c4Current v tag s` (`POS04/C4C5.lean:26`) is the list of declared C4 channel readings at `s`.
- `pointedHidden x := rawM x.tag x.present`.
- `C4Collision` (`C4C5.lean:35`): the C4 current readings agree on `hiddenPair` while `rawM` differs.

**(d)** On the POS-04 target, the states `p1w0` and `p1w1` give identical readings on every declared C4 public channel but different predictive M readouts. The fixed hidden pair also exhibits a C4 collision.

**(e)** The interface is the C4 surrogate channel list only. Nothing is claimed about all possible observations or about a consciousness predicate (the file comment says so explicitly, `:25`).

**(f)** Kernel `decide` on finite data.

---

## 10. TTH-09 (route licenses), TTN-04, TTN-05

### TTH-09: `CSTTT.RouteLicenses.flatness_sufficient` (`Transport/RouteLicenses.lean:203`), `normalization_sufficient` (`:153`), `confluence_sufficient` (`:164`)

**(b)** Each has the form, with license `X ∈ {NormalizationLicense, FlatLicense, ConfluenceLicense}`:
```lean
theorem X_sufficient (m : RawSystem R E B V S) (d : Domain R B) (h : XLicense m d)
    (r s : R) (hr : r ∈ d.routes) (hs : s ∈ d.routes) : endpoint m r = endpoint m s
```

**(c)**
- `endpoint m r` (`:47`) executes the route's event word by event actions from its boundary's initial state.
- `DomainCheck` (`:62`): at least two routes with distinct paths, no duplicate paths, every route admissible (events available, vertex path from boundary entry to exit), every route on the domain boundary, and closed under rewrites.
- `NormalizationLicense` (`:88`): domain, rewrites preserve boundary and action (`RewriteActions`, `:86`), rank decreases, and `SharedNormal` (a unique terminal route reachable from every route, `:79`).
- `ConfluenceLicense` (`:94`): domain, boundary, actions, and pairwise joinability.
- `FlatLicense` (`:122`) has 14 fields:
  - event action equals the forward clock, and the clock is invertible;
  - nonempty critical pairs that cover all routes, each completed by valid completion rows;
  - connectivity of routes under completion moves;
  - rank decrease and a shared normal form for reductions;
  - completion action equations;
  - `zero`: the clock holonomy around each completion row is the identity.

**(d)** If the declared raw route system and comparison domain carry a normalization, confluence or flat license, then any two routes in the domain have equal executed endpoints.

**(e)**
- It gives sufficiency only; no converse is stated.
- Several license fields are unused by the proofs:
  - normalization does not use `decreasing` or the boundary-preservation field;
  - flatness uses `connected`, `pairs`, `valid`, `zero`, `clockActions`, `clockInverse` and admissibility, but not `nonempty`, `covers`, `completed`, `decreasing`, `normal` or `actions`;
  - `DomainCheck.distinct`, `noDuplicates` and `closed` are unused everywhere.

  These fields enforce nonvacuity and faithfulness to the spec, not logical necessity.
- Endpoints are equal states of type `S`; nothing is said about intermediate frontiers.

**(f)** Genuine but elementary: induction on reachability along rewrite or move paths (`reach_execution`, `:145`), plus clock-word inversion for flatness (`completed_execution`, `:192`).

### TTN-04: `CSTTT.RouteTheory.noCurrentOnlyPredictor` (`Transport/RouteDiscipline.lean:16`)

**(b)**
```lean
theorem noCurrentOnlyPredictor (current : Route → Current) (future : Route → Future) (r₁ r₂ : Route)
    (hsame : current r₁ = current r₂) (hdifferent : future r₁ ≠ future r₂) :
    ¬ ∃ predictor : Current → Future, predictor (current r₁) = future r₁ ∧ predictor (current r₂) = future r₂
```

**(d)** If two routes have equal current codes and different futures, no function of the current code returns both futures.

**(e)** This half says nothing about the repairs. "Licensed repairs are route memory or flatness" is `memoryOrFlatness` (`:53`). That lemma says: if (current, residue) is future-sufficient, then either current is already future-sufficient (`FlatAt`, `:35`) or residue separates every current-equal, future-distinct pair (`MemoryRepairs`, `:42`). Note that "flatness" there is the trivial `FlatAt`, not the TTH-09 `FlatLicense`. The POS-04 instance is `ttn04_current_collision_memory` (`POS04/Countermodels.lean:58`).

**(f)** Trivial: function congruence.

### TTN-05: `CSTTT.RealControls.ttn05_exists` (`Countermodels/RealControls.lean:203`)

**(b)**
```lean
theorem ttn05_exists : ∃ m : ClockLoopControl,
    m.translation 0 ≠ (0 : Fin 2) ∧ ¬ CanonicalGlobalNow clockBoundary (loopNow m)
```

**(c)**
- `ClockLoopControl := {translation : Fin 2 → Fin 2}` (`:196`).
- `loopNow m .identity = 0` and `loopNow m .loop = m.translation 0` (`:199`).
- `clockBoundary _ = (0 : Fin 1)` (`:180`).
- `CanonicalGlobalNow b ℓ := ∃ g, ∀ r, g (b r) = ℓ r` (`RouteDiscipline.lean:71`).

**(d)** There is a translation of Z/2 phases that moves phase 0, such that the two-path (identity, loop) local-now assignment does not factor through the one-point boundary.

**(e)** "Holonomy" here is just `translation 0 ≠ 0`; no group structure or loop composition is used. The result says nothing about routes with genuinely different boundaries.

**(f)** Trivial: `noCanonicalGlobalNowOfTranslationHolonomy` (`RouteDiscipline.lean:79`) is function congruence.

---

## 11. TTD-02: `actual_modes_incomparable`; TTS-04: `all_supported_streams_infinite_laws`

### TTD-02: `CSTTT.TargetTheory.RawDirectSuccessorReturn.actual_modes_incomparable` (`Targets/RawDirectSuccessorReturn.lean:193`)

**(b)**
```lean
theorem actual_modes_incomparable :
    CSTTT.StrengtheningTheory.EvidenceModesIncomparable OverlapMode DirectMode
```

**(c)**
- `EvidenceModesIncomparable ov dir := (∃ m, ov m ∧ ¬ dir m) ∧ (∃ m, dir m ∧ ¬ ov m)` (`Strengthening/ContinuityClass.lean:35`).
- `ControlModel` (`Corridor/RawDirectSuccessor.lean:390`): an episode `FiniteAtomicLeg`, an input assignment, a dependency-kind map and a data graph.
- `OverlapMode m := AtomicLegPass m.episode` (`:412`; item 3's atomic check).
- `DirectMode m` (`:410`): the episode projects to a raw direct system (`directProjection`, `:396`), and `ImmediateDirect` holds. That means there is exactly one incoming edge, its decoded capsule is present with an unused token, and `Geometry` holds (`:186`): distinct carriers, a live temporal edge, source-only and target-only supports, payload equal to the source frontier, the target frontier being the advanced payload, `readoutStep`, and target stage = source stage + 1.

**(d)** Within the shared raw control-model domain, there is a model whose episode passes the strict overlap check but is not a direct successor, and a model that is a direct successor but fails the overlap check.

**(e)** **Incomparability understates the formal result.** `overlap_not_direct` (`Corridor/RawDirectSeparation.lean:38`) proves the two modes are disjoint on every `ControlModel`: overlap requires the source and target audit events at the same stage, direct requires adjacent stages. The paper could state "disjoint and both nonempty". The "both embed in a generalized path relation" part is `actual_generalized_broader_than_overlap` (`:198`). It proves that overlap ⊆ generalized and that the direct witness is generalized, not that every direct model is generalized; that is `direct_embedding` for each direct model.

**(f)** Kernel `decide` witnesses plus a short stage-arithmetic disjointness lemma.

### TTS-04: `CSTTT.AutonomyTheory.RawRechargingPolicy.all_supported_streams_infinite_laws` (`Autonomy/RawRechargingPolicy.lean:345`)

**(b)**
```lean
theorem all_supported_streams_infinite_laws (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (total : TotalComputedPolicy m a h) (stream : Nat → D) (outcomes : Nat → O)
    (supported : SupportedOutcomes m a h stream outcomes) (n : Nat) :
    let x := outcomeTrajectory m a h stream outcomes n
    let y := outcomeTrajectory m a h stream outcomes (n+1)
    x.factor ∈ greatest m a h ∧ PackageAt m a x.factor ∧ StepOf m a h x (stream n) y ∧
      x.progress < y.progress ∧ x.record < y.record ∧ reserve m a h ≤ x.balance ∧ 0 ≤ x.balance
```
It assumes `[DecidableEq X]`.

**(c)**
- `Raw` (`:28`) has:
  - finite enumerations of states `X`, disturbances `D` and outcomes `O`, and a target carrier;
  - a clause package and per-cell programs computing an assignment from a factor state;
  - a response table view `X → D → Response` (one action, owner, weighted rows, and branch data per outcome: destination, progress and record increments, debit and credit);
  - initial-state views.
- `EventState` (`:9`): factor, progress : Nat, record : Nat, balance : Rat (unbounded registers).
- `PackageAt m a x := m.clauses.accept (factorAssignment m a x)` (`:111`).
- `Retains S x` (`:159`): `PackageAt x`, and for every disturbance the table response is target-owned and normalized, and every positive-weight branch has destination in S, positive progress and record increments, `0 ≤ debit ≤ credit`.
- `greatest` (`:188`): the greatest fixed point of pruning by `Retains` over the finite state list (`ViableSet.greatest`).
- `reserve` (`:147`): the maximum debit over all (x, d, o).
- `TotalComputedPolicy` (`:241`): the initial factor is in `greatest` and the initial balance is ≥ `reserve`.
- `outcomeTrajectory` (`:304`) is driven by the given disturbance and outcome streams.
- `SupportedOutcomes` (`:311`): each chosen outcome has positive weight in the row of the trajectory's current state.
- `StepOf` (`:251`): the actual step relation with target owner, positive increments and an affordable debit.

**(d)** For a raw policy whose initial state lies in the computed greatest viable set with balance at least the maximal debit, consider any disturbance stream and any outcome stream that is positively supported at every step. Then at every time `n` the run stays in the greatest viable set, satisfies the full declared package, takes a lawful target-owned step, strictly increases progress and record, and keeps its balance at least the reserve, and in particular nonnegative.

**(e)**
- **Solvency is near-built-in**: `Retains` requires `debit ≤ credit` on every positive branch, so the balance never decreases (`ledger_monotone`, `:196`). "Replenished" means exactly this per-branch condition.
- The policy is the fixed response table; no strategy choice exists. `greatest` is the greatest set for that policy, not over all strategies.
- `total` is a hypothesis; nonvacuity needs an instance.
- "No finite full-state system can carry such a run" is a different declaration (`FiniteProgress.no_infinite_strict_finite_state_run`).
- The result is model-relative. It does not say anything physical.

**(f)** Moderately substantive. Induction on n uses the greatest-fixed-point property of the finite pruning (`greatest_retains`, `:191`, via `ViableSet.greatest_viable`) and the per-branch ledger monotonicity. Each step is easy, but this is a real invariance proof over infinite streams.

---

## Cross-cutting cautions for the paper
1. **Kinds of certificate.**
   - **Summary certificates** are structures of proofs of already-stated propositions: `FullHandoffCertificate`, `TemporalFissionCertificate`, `AtomicTemporalCorridorCertificate`, `TemporalFIACHCertificate`. Theorems concluding the summary from such a certificate are projections.
   - **Invariant certificates** supply invariant and response obligations, from which run conclusions follow by induction: `ExactAutonomyCertificate`, and the game `InvariantCertificate`. They are not stored conclusions.

   The mathematical content sits in the instance lemmas, or in three generic lemmas: `FutureLumping.all_words`, `StrategyGame.invariant_game_soundness` and `PackageEngine.constructs` (with `glued_restricts`, plus clause locality). (Corrected after the W2b review.)
2. **Unused hypotheses to avoid stating as necessary:**
   - TTH-01: rootedness and rank, which are hypotheses that go unused (finiteness is not assumed at all);
   - TTH-07 (generic): `interface`;
   - TTF-05: `valid`;
   - TTH-09: several license fields;
   - TTN-01 (`ttn01_exists`): the existential `stages`.
3. **Elementary structural exclusions.**
   - TTN-11's "no invariant selector" does not depend on validity: `forkSwap` has no fixed points. The checked fork is nonempty and both branches pass the computed checks.
   - TTN-13's carrier part holds by the `distinct` field.

   (Corrected after the W2b review.)
4. **Name collisions:** `positive_F/O`, `IntegratedTargetRealization`, `StrictTemporalLineage` and `PostWithdrawal*` each exist in four or more namespaces. Always cite the full namespace (`FinalHandoff`, `OwningHandoff`, `HistoricalPackageRuntime`, `ComputedFIACH`).


## Correction note (W2b review, 2026-10-13)
Three kinds of certificate must be kept distinct:
- **Summary certificates** bundle proofs of already-stated propositions (for example `FullHandoffCertificate`).
- **Invariant certificates** supply invariant and response obligations, from which run conclusions follow by induction (for example `ExactAutonomyCertificate`, and the game certificates behind `StrategyGame.invariant_game_soundness`). These are not stored conclusions.
- **Elementary structural exclusions** are results such as the fork swap having no fixed point.

**Completeness.** For the defined StrictSparse game semantics, autonomy is equivalent to the existence of a proof-bearing invariant certificate (`StrategyGame.game_invariant_completeness`; `full_subcheck_iff`). This is a semantic existence theorem, not a search procedure. The finite-factor constructor is sound but potentially incomplete.
