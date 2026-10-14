# G0 — contracts for generic constructive theorems

**Scope and status.** This is a design, not a Lean proof or a registry change. The request says “14 rows” but explicitly enumerates 15 IDs; these are exactly the 15 `conditional` rows in CST-TT-09. All 15 named IDs are treated here. Every proposed replacement below is a **(b) mathematical statement/definition change**, not a porting change. The complete *current* Lean theorem headers (including all registered companion declarations) are reproduced verbatim in Appendix A; each section points to its source and states the unfolded gap. “Exact proposed signature” means the proposed declaration surface; the new raw-data types and computed predicates named there are contractual and must be defined as specified before implementation. No result is promoted merely because a field of a record has the same name as its conclusion.

## Shared implementation rule

All future `Raw*` structures contain **data only**: finite carrier/state/event/route types and enumerations, functions for transitions, support, observations, ownership, resources, maps, and relations. They contain no `Prop` asserting a desired theorem and no stored verdict. A `*Pass` proposition is a definition unfolding to equalities, membership, inequalities, or quantified transition laws *computed from those functions*. A proof of a raw law can be a theorem premise when it is independently checkable and weaker than the intended conclusion. A certificate may package proofs of such laws for reuse, but a theorem whose conclusion is only the same stored fields is a schema lemma and cannot carry a row. For finite POS-04, `decide` checks the premises; generic theorems use induction, equational reasoning, and finite-set arguments. No proposed theorem assumes an unconstrained `packageValid`, `corridorValid`, `autonomyValid`, `related`, `valid`, `antiStall`, or `budgetSolvent` parameter.

The declaration sketches use `FiniteEnum`/`CarrierId`/`TemporalSignature` from CSTTT. `RawPackage`, `RawBridge`, `RawCorridor`, `RawHandoff`, `RawDirect`, `RawDefect`, `RawMargin`, and `RawPolicy` below are *new* data structures, not aliases for existing certificate types. The notation `...Pass` always denotes a `def ... : Prop` calculated from a specified structure. The implementation must prove equivalence to the relevant POS-04 checks rather than silently retype its tables. A POS-04 witness is evidence only at its declared grade: C1–C3 and C8 substantive, C4–C7 surrogates (`POS04/Assembly.lean:221–233`). Thus generic “integrated package” in this design means an **eight-clause structural package at the declared clause grades**, not a full P05 C-package or T17-I. Any stronger reading requires a separate upgrade.

These signatures are **design contracts**, not claims that the new identifiers already elaborate. Before promoting a row, its implementation packet must define each named raw type and computed predicate, prove its displayed theorem with no replacement hypothesis equivalent to the conclusion, and supply the stated finite instance. A mere renaming of an old `Prop` field to `*Pass` does not satisfy this contract. In particular, where this design records no current positive instance, the non-vacuity gate remains open.

## TTH-02 — staged package assembly

**Current statement and gap.** The exact header is in Appendix A (`Package/FiniteGluing.lean:158`). Unfolding `StagedHeterogeneousEvidence` (`:128–156`) shows `separatelyTyped` and `hardGatesNeverAveraged` are free propositions; their proofs are projected. The value-preserving maps are unused. Target acceptance is supplied independently, and the constructed `IntegratedPackageWitness` only glues values.

**Proposed raw contract.** `RawPackage` has a fixed eight-element clause type, scoped coordinate assignments, clause-specific evaluators `localAccept : Clause → (Coord → Value) → Prop` implemented from raw coordinate values, and `hardGate : Clause → (Coord → Value) → Prop` implemented as exact equalities/inequalities. `RawStageMap` has total source/target coordinate and value maps. `StageMapEquations` checks coverage and pointwise transported values on all scoped coordinates. `Locality` means each evaluator/gate depends only on its scope. `TargetLocalChecks` checks each *mapped* target assignment, not an independently supplied target witness. `GlobalPackagePass` checks all eight evaluators/gates on one global assignment. These are definitions over data; source validity, stage equations, locality, and target-local checks are distinct premises.

```lean
theorem stagedHeterogeneousPackageAssembly_generic
    {m : RawPackage} (f : RawStageMap m)
    (hsource : SourcePackagePass m)
    (hmap : StageMapEquations m f)
    (hlocal : ClauseLocality m)
    (htarget : TargetLocalChecks m f)
    (hcompat : EdgeCompatible (mappedLocal m f)) :
    ∃ global : m.TargetCoord → m.TargetValue,
      RestrictsEveryLocal m f global ∧ GlobalPackagePass m global
```

The gluing equality comes from TTH-01; locality transports each target-local clause check to the glued assignment; map equations are used to identify it as the staged image. No lineage/autonomy premise. The generic proof is feasible in core if locality is stated with exact scopes. **Non-vacuity:** `POS04.package_funded_each_tag` (`POS04/Assembly.lean:233`) and `staged_clause_pass` (`:273`) give both ends and map checks; missing bridge: turn POS-04’s 160-coordinate `CoordinatesComplete`, per-clause predicates, and staged equations into `ClauseLocality` and `TargetLocalChecks` for this generic record. **09 text/ceiling:** retain only if “integrated” is explicitly read at declared clause grades. If it means full P05, narrow to: “Typed total value-preserving stage maps, locally checked target clauses and a compatible cover assemble an eight-clause target structural package at its declared clause grades, without lineage or autonomy premises.” **Owner narrowing N1.** Size L; feasible after the locality bridge.

## TTH-03 — bundled heterogeneous temporal transport

**Current and gap.** Appendix A (`Transport/FiniteTemporalTransport.lean:63`): ten arbitrary `Bridge → Prop` parameters are supplied and projected. `TemporalSignatureAgreement` (`:18`) gives component equations but no strict successor/arrow or route law.

**Proposed raw contract.** `RawBridge` contains a nonempty reachable source-history frontier, source/target signatures, total state/history and coordinate maps, source/target transition and record functions, route maps, and ownership maps. `BridgeAdmissible` computes type/coverage, at least one strict reachable edge, and all mapped states’ support. `BridgePrimitiveLaws` checks successor preservation, clock translation equations, strict order/tick/progress/record step inequalities, route-residue equation or a separate route license, maintenance equation, and target-owner equality on the reachable domain. `RepresentativeIndependent` is the existing quantified *computed* relation on reachable histories (`FiniteTemporalTransport.lean:8–15`), with source and pushed target classes computed from raw transitions.

```lean
theorem bundledHeterogeneousTemporalTransport_generic
    {b : RawBridge} (ha : BridgeAdmissible b)
    (hrep : RepresentativeIndependent b.reachable b.sourceClass b.pushedClass)
    (hlaws : BridgePrimitiveLaws b) :
    ∀ h, b.reachable h → TemporalSignatureAgreementAt b h ∧
      StrictSuccessorPreserved b h ∧ StrictRecordArrowPreserved b h ∧
      RouteStatusPreserved b h ∧ TargetOwnedImage b h
```

`BridgePrimitiveLaws` must contain raw map/transition equations, not the four conclusion predicates. **Non-vacuity:** POS-04 `bridge_positive` (`POS04/Bridge.lean:114`) and `rawM_iff_imported_M` (`POS04/C2C3.lean:19`) are concrete candidates with different-past representatives; missing generic bridge lemma is exact alignment of POS-04’s history, event, route, progress, record and owner laws with `BridgePrimitiveLaws`. **09 text/ceiling:** retain at *reachable histories* only if “admissible” explicitly means that declared domain. If the row requires all histories, narrow to “... on the declared nonempty reachable history frontier ...”. **Owner narrowing N2.** Size L; feasible with the raw-law factoring. Future sufficiency cannot follow merely from representative independence; it must be in the raw signature map law.

## TTH-04 — strict corridor composition

**Current and gap.** Appendix A (`Corridor/Composition.lean:61`). `CorridorSummaryData` (`:6–15`) has free proposition flags; `FrontierCompatible` (`:27`) checks only carrier and one signature equality. No actual chain of atomic legs is represented.

**Proposed contract.** `RawCorridor` has a nonempty list of `AtomicLeg` data with realized stages/events, support, intervention readouts, residue, owner, and entry/exit signatures. `AtomicLegPass` computes no gap, mixed support, strict realized event steps, source/target intervention nonredundancy, route readout and owner from those fields. `AdjacentExact` checks the common carrier, temporal frontier, route residue and ownership interface. `CorridorPass` is `every AtomicLegPass ∧ every adjacent AdjacentExact ∧ endpoints distinct`, not a summary flag.

```lean
theorem strictTemporalCorridorComposition_generic
    (left right : RawCorridor)
    (hl : CorridorPass left) (hr : CorridorPass right)
    (hj : AdjacentExact left.lastLeg right.firstLeg)
    (hd : left.source ≠ right.target) :
    CorridorPass (appendCorridor left right)
```

The `appendCorridor` definition concatenates raw leg lists and recomputes all comparisons. **Non-vacuity:** POS-04 has two realized mixed legs and `corridor_positive` (`POS04/Corridor.lean:79–94`); missing bridge is an `AtomicLegPass` equivalence and an `AdjacentExact` proof for its intermediate stage, including route/owner. **09 text/ceiling:** unchanged. (b), L, feasible by list induction. An empty chain is excluded by type/constructor, not by a `True` flag.

## TTH-06 — generic Temporal-FIACH soundness

**Current and gap.** Appendix A (`Targets/FiniteTemporalFIACH.lean:8`). It projects three arbitrary validity fields from `TemporalFIACHCertificate` (`Targets/TemporalFIACH.lean:17–44`); source package, stage preservation and route status are also arbitrary stored fields.

**Proposed contract.** `RawHandoff` holds distinct source/target carrier data, raw source/target packages and staged map, raw corridor, bridge, target controlled system with withdrawal, endpoint links, and raw routes. `HandoffPass` is the conjunction of *computed* `SourcePackagePass`, `StageMapEquations`, `TargetPackagePass`, `CorridorPass`, `BridgePass`, `ContentSensitivity`, `SourceAbsentFails`, `TargetAutonomyPass`, `TypedEndpointLink`, and `routeStatusOf` agreement; recognition is explicitly `.notAddressed`. `IntegratedTargetRealization`, `StrictTemporalLineage`, and `PostWithdrawalAutonomy` are independently defined readouts of respectively the package, corridor/bridge, and controlled invariant, each over the same raw model.

```lean
theorem temporalFIACHCertificateSoundness_generic
    (m : RawHandoff) (h : HandoffPass m) :
    IntegratedTargetRealization m ∧
    StrictTemporalLineage m ∧
    PostWithdrawalAutonomy m
```

`HandoffPass` must be established from raw component theorems; the readout theorem alone is still an elimination rule. The independence claim has a **promotion gate of three same-family controls** with the other two lane predicates still true. POS-04's `NEG-C4-EXPOSE` changes no lineage/autonomy lane in the M3b side-effect record and is a candidate **package-only** failure (`POS04/Assembly.lean:551`); `NEG-CORRIDOR-DETACHED` changes no clause pass and is a candidate **lineage-only** failure (`:481`). Their exact three-lane readouts still need Lean theorems. Neither `NEG-AUTONOMY-WITHDRAW` nor `NEG-C8-UNDERFUND` is an autonomy-only control: M3b records package/stage/bridge side effects, so the third control must be **newly declared before evaluation**, changing only the post-exit withdrawal resource/retention rule while holding endpoint package funding, corridor, bridge and route data fixed. It must prove `IntegratedTargetRealization ∧ StrictTemporalLineage ∧ ¬ PostWithdrawalAutonomy`. All three controls must then be evaluated with the same raw predicates and proved in Lean; `no_fiach_*` alone is insufficient. **Non-vacuity:** `pos04_fiach` and `pos04_fiach_readout` (`POS04/Assembly.lean:344,384`) give the model-relative witness; missing bridge is one `RawHandoff` assembler and equivalence from POS-04 variants to the new generic predicates. **09 text/ceiling:** the current TTH-06 generic row says “certificate entails, as separate fields”; that literal schema remains true, but substantive generic promotion should split as already done for 06b. Suggested new generic text: “A raw-data Temporal-FIACH handoff satisfying independently computed target-package, strict-corridor/bridge, and post-withdrawal controlled-invariant checks entails the three corresponding structural readouts; no lane is inferred from another.” Ceiling “structural finite-model criterion at declared clause grades.” **Owner narrowing N3** if the original is read as full package. (b), L, feasible after G1–G4 and autonomy adapter.

The required separation theorem has this exact target; each control is a raw-model mutation, and none is an arbitrary lane label:

```lean
theorem temporalFIACH_three_lane_separation :
    (∃ m : RawHandoff,
      ¬ IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧
      PostWithdrawalAutonomy m) ∧
    (∃ m : RawHandoff,
      IntegratedTargetRealization m ∧ ¬ StrictTemporalLineage m ∧
      PostWithdrawalAutonomy m) ∧
    (∃ m : RawHandoff,
      IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧
      ¬ PostWithdrawalAutonomy m)
```

## TTH-07 — composition of full handoffs

**Current and gap.** Appendix A (`Targets/Composition.lean:62,79,89`). `FullHandoffCompatible` is unused by the proof, package maps are absent, route status is a label operation, and autonomy is merely inherited from the right.

**Proposed contract.** `RawHandoffMap` has typed package coordinate/value maps and a map from the left target package to the right source package. `HandoffCompatible` computes exact intermediate package equality *under the maps*, carrier/frontier/residue/owner equality, route-readout compatibility, and right-side autonomy availability after the second withdrawal. It also contains four **independently checkable composition laws on raw histories, receivers, and route tables**:

* **Content:** let `D₁` be the reachable source predictive classes delivered by the first receiver at the shared frontier, `f₁` its computed class map, and `f₂` the second receiver's computed class map. Require `∀ x y ∈ D₁, f₂ (f₁ x) = f₂ (f₁ y) → f₁ x = f₁ y`. Equivalently, `f₂` is injective on `f₁(D₁)`. Both receivers must agree with raw class computation on their endpoint states. Then `f₁ x ≠ f₁ y` from the first handoff implies `f₂(f₁ x) ≠ f₂(f₁ y)` for the composite. This is an injectivity **equation on computed maps and a declared domain**, not a stored `ContentSensitivity (composeHandoff a b)` field.
* **Causal activation:** the composite receiver must execute the first receiver and pass its realized intermediate output into the second. Formally, `activateComposite input = activate₂ (output₁ input)` only when `activate₁ input`; otherwise it is `none`, with no preload/fallback branch. Hence `activate₁ sourceAbsent = none` implies `activateComposite sourceAbsent = none`. This is checked by the raw receiver transition and support table, not supplied as an absence verdict.
* **Computed reachability:** for every history in the first bridge's computed reachable domain, every history actually delivered by its raw receiver lies in the second bridge's computed reachable domain. The first bridge's output type and the second bridge's input type agree through the intermediate interface. This is a domain-inclusion theorem over supported history paths and receiver outputs, not a stored `BridgePass` or `reachable=true` label. It lets the second bridge's successor, representative, and signature laws apply to *every* first-stage delivery.
* **Bridge and route readouts:** the two raw bridge maps commute with supported transitions on those reachable histories. Their mapped order, tick, progress, strict record step, maintenance state, and owner equations compose pointwise; the intermediate equations are the same values on both sides. For each compared composite route, concatenate its supported event paths, execute the funded target step, and read the **resulting state's** register/route observable. Require the raw register-write and route-transport equations to identify that readout with the corresponding second-stage readout of the transported first-stage route. The comparison domain is the actual paired routes with shared boundary/endpoint, not a route-status label. This law also preserves route-residue distinctions or the explicit flatness license, so `routeStatusOf` is recomputed from the composite raw routes rather than copied from either handoff.

`composeHandoff` composes the package and receiver maps and concatenates raw corridor legs and event paths; route status is recomputed from composite routes. The shared-frontier equations make the composite receiver well typed; **computed reachability** makes the second bridge laws applicable to every delivered history; representative independence then composes through the two raw class maps. Injectivity establishes composite content sensitivity, and the activation equation establishes composite source-absence failure. `RightAutonomyCompatible` must be the raw equality between the composite target controlled subsystem/withdrawal specification and `b`'s target subsystem/specification, so `hb` supplies its proof by transport. It cannot be a free proposition saying the composite is autonomous. No conclusion conjunct is added as a premise.

In the implementation API, the two new conjuncts of `HandoffCompatible` have the following signatures (with `a.deliveredClass` computed from raw receiver output, and `b.classMap` computed from the second receiver):

```lean
def ReceiverInjectiveOnDelivered (a b : RawHandoff) : Prop :=
  ∀ x y : a.SourceClass,
    x ∈ a.reachableClasses → y ∈ a.reachableClasses →
    b.classMap (a.deliveredClass x) = b.classMap (a.deliveredClass y) →
    a.deliveredClass x = a.deliveredClass y

def CompositeActivationEquation (a b : RawHandoff) : Prop :=
  ∀ input : a.SourceInput,
    (composeHandoff a b).receiver input =
      (a.receiver input).bind b.receiver

def DeliveredHistoriesReachable (a b : RawHandoff) : Prop :=
  ∀ h h', a.bridge.reachable h →
    a.deliverHistory h = some h' → b.bridge.reachable h'

def BridgeRouteReadoutComposition (a b : RawHandoff) : Prop :=
  RawBridgeMapEquations a b ∧
  RawRouteEventPathsCompose a b ∧
  FundedResultingRegisterReadoutEquations a b ∧
  RouteComparisonDomainTransport a b

def HandoffCompatible (a b : RawHandoff) : Prop :=
  PackageMapCompatible a b ∧ AdjacentExact a.corridor.lastLeg b.corridor.firstLeg ∧
  RouteOwnerCompatible a b ∧ ReceiverInjectiveOnDelivered a b ∧
  CompositeActivationEquation a b ∧ DeliveredHistoriesReachable a b ∧
  BridgeRouteReadoutComposition a b ∧ EndpointLinkCompatible a b ∧
  RightAutonomyCompatible a b
```

`RawBridgeMapEquations` means the raw successor square commutes and the component equations just listed hold on every delivered reachable edge; `FundedResultingRegisterReadoutEquations` reads registers **after** executing the funded step; `RouteComparisonDomainTransport` maps every compared pair's raw boundary, exit event, and provenance into the composite comparison domain. It does not assume equality of the two routes' endpoints. None is defined as `BridgePass (composeHandoff a b)` or `RouteMemoryPass (composeHandoff a b)`. `EndpointLinkCompatible` equates the first corridor exit with the second entry and links the composite receiver's raw endpoint event, factor state, phase, and owner to the final corridor exit. The raw receiver must return an `Option` so absent-source activation is `none`, and `Option.bind` has no fallback. `a.SourceClass` and `b`'s input class type must be identified by the intermediate package/interface equality; that typed identification is part of `PackageMapCompatible`. A proof cannot fill `CompositeActivationEquation` by defining a separate composite verdict: it must reduce to the raw two-stage receiver transition.

```lean
theorem fullTemporalHandoffComposition_generic
    (a b : RawHandoff) (ha : HandoffPass a) (hb : HandoffPass b)
    (hc : HandoffCompatible a b)
    (hd : a.source ≠ b.target) :
    HandoffPass (composeHandoff a b)
```

The proof must establish **every** computed `HandoffPass` conjunct. The final two rows spell out the representative and route checks that the POS-04 certificate exposes separately; an implementation may group them inside `BridgePass` and route-status agreement, but may not drop them.

| Composite conjunct | Source of the proof |
|---|---|
| Distinct outer carriers | `hd : a.source ≠ b.target`; composite carrier IDs are definitionally those two IDs. |
| Source package | `ha`'s checked source package; the composite begins on `a.source`. |
| Staged clause preservation | Compose `ha` and `hb`'s raw coordinate/value equations using `PackageMapCompatible`; the shared target/source package and scoped values agree at the middle carrier. |
| Target package | `hb`'s checked target package, transported across the definition of the composite final target. |
| Strict realized corridor | Concatenate `ha` and `hb`'s actual atomic-leg lists; `AdjacentExact` supplies the middle carrier, frontier, residue and owner equalities; list induction retains mixed support, strict steps and no gap. |
| Heterogeneous bridge and representative independence | Compose each raw successor/order/tick/progress/strict-record/maintenance/owner equation from `ha` and `hb` using `RawBridgeMapEquations`. `DeliveredHistoriesReachable` permits applying every second-bridge law and its representative-independence theorem to the first bridge's delivered histories. |
| Content-sensitive transfer | `ha` supplies two distinct delivered classes; `DeliveredHistoriesReachable` puts both inside the second receiver's domain; `ReceiverInjectiveOnDelivered` prevents `b.classMap` from collapsing them. Raw class-map/receiver equations identify them with the composite endpoint classes. |
| Source-absent activation failure | `ha` gives `a.receiver sourceAbsent = none`; `CompositeActivationEquation` reduces the composite receiver to `none.bind b.receiver = none`, with no fallback. |
| Target-only post-withdrawal autonomy | `hb`'s checked controlled invariant and response law; `RightAutonomyCompatible` identifies the composite final controlled subsystem and withdrawal specification with `b`'s raw data. |
| Typed endpoint and ownership link | The two component endpoint links, `AdjacentExact`, `EndpointLinkCompatible`, and `RouteOwnerCompatible` identify the composite entry/exit event, target factor/phase and owner. |
| Route memory, readouts, and computed status | `RawRouteEventPathsCompose` supplies supported composite paths; `FundedResultingRegisterReadoutEquations` transports the **post-step** register reads; `RouteComparisonDomainTransport` supplies actual paired routes and boundary/exit provenance; `RouteOwnerCompatible` supplies owner/writer agreement. Recompute `routeStatusOf` from those reads and the applicable flatness license, never by composing two labels. |
| Recognition status | The structural constructor sets `.notAddressed` by definition; no recognition inference is made. |

The `HandoffCompatible` proof is therefore used in the package-map, corridor, bridge, route, endpoint, owner, content, activation, and autonomy subproofs. **Non-vacuity:** POS-04 has only one source→target handoff (`pos04_fiach`); the old POS-01 composition fixtures are not model-linked to POS-04 predicates. No existing concrete *two-hop* instance; bridge lemma/second model and independently proved intermediate package, delivered-history coverage, route readout transport, receiver injectivity, causal activation, and autonomy are missing. This blocks promotion despite the generic proof plan. **09 text/ceiling:** unchanged: the stronger compatibility laws make the full row conclusion derivable. **Owner N4 remains pending** only for a concrete two-hop witness. (b), L; feasible algebraically but non-vacuity evidence absent.

## TTH-08 — relation-valued symmetric fission

**Current and gap.** Appendix A (`Corridor/Fission.lean:27,35,44`). Both `related` and `valid` are arbitrary, and two nonfixed points do not rule out every invariant selector.

**Proposed contract.** `RawFork` has one source, two distinct branch carrier IDs, raw handoffs for both branches, an involutive branch swap, and a finite continuation set exactly the two branch endpoints. Define `ForkRelated f s t := ∃ branch, HandoffPass (f.branch branch) ∧ endpoint ... = t`; `ForkAutonomous` uses each branch’s computed target-controlled invariant. Define `InvariantSingletonSelector f` as a member of the continuation set fixed by swap; this is the relevant equivariant selector notion, not an unqualified choice function.

```lean
theorem relationValuedTemporalFission_generic
    (f : RawFork) (hl : HandoffPass f.leftHandoff)
    (hr : HandoffPass f.rightHandoff)
    (ha : ForkAutonomous f)
    (hs : ForkSwapLaws f) :
    ForkRelated f f.source f.left ∧
    ForkRelated f f.source f.right ∧
    ¬ InvariantSingletonSelector f
```

**Non-vacuity:** `ttn11_symmetric_fork_certificate`, `fork_package_each_branch`, `fork_autonomy_transport`, and `ttn11_no_invariant_unique_selector` (`Countermodels/RealControls.lean:536,510,570,594`) establish branch-owned packages/autonomy and swap nonselection; missing bridge is actual `HandoffPass` on *both* branches. Therefore this is not yet a nonvacuous **Temporal-FIACH** fork. **09 text/ceiling:** narrow “valid fork” to “two fully checked structural handoffs” if intended, or retain as structural continuation relation with no unique identity claim. Exact proposal: “A two-branch swap-symmetric structural continuation relation with independently checked branch packages and autonomy has two related targets and no swap-invariant singleton selector.” **Owner narrowing N5**; (b), L; generic nonselection proof feasible, full handoff instantiation unavailable.

## TTH-09 — route-independent endpoint licenses

**Current and gap.** Appendix A (`Transport/RouteDiscipline.lean:121`; `Targets/RouteCompletion.lean:45`). Normalization suffices; the flat-status theorem projects a label. There is no flatness-only or confluence endpoint theorem.

**Proposed contract.** `RawRouteSystem` stores supported event paths, a raw step action, a raw route-rewrite relation, a clock-translation table, and a declared same-boundary comparison domain `D`. `AdmissibleRoute` is computed by path support; `endpoint r` is the fold of the raw action table, not a stored route verdict. `D` must contain the compared pair, have at least two distinct routes, and be closed under any rewrite claimed by a license. Define the three licenses by **different primitive mechanisms**:

* `NormalizationLicense m D` supplies a well-founded rank strictly decreasing on every raw rewrite, a normalizer reached by a finite sequence of those rewrites, and a canonical normal form determined only by boundary. Prove *separately from the raw action/rewrite equations* that each rewrite preserves executed endpoint; endpoint equality then follows by the shared normal form. The current `NormalizationCertificate` (`RouteDiscipline.lean:108–116`) is a useful algebraic readout, but its `endpointFactors` cannot simply be copied into the new input.
* `FlatLicense m D` requires a nonempty set of **distinct** same-boundary critical route pairs covering `D`, raw completion squares for every critical pair, path-clock translations around each completed square summing to zero, and connectivity of every same-boundary pair in `D` by a chain of the declared elementary completion moves. That connectivity is a finite graph-reachability check, not an endpoint-equality field. Induction over the chain and raw completion/clock equations gives equal executed endpoints. `r.endpoint = s.endpoint` is neither a field nor enough to construct this license.
* `ConfluenceLicense m D` requires that raw rewrite branches from every same-boundary pair in `D` reach a common descendant, with termination or a finite joinability closure proof and raw action equations showing endpoint preservation along each rewrite. It is not the assertion that original endpoints already agree. Unlike flatness, it needs no zero-clock law.

`RouteLicense m D := NormalizationLicense m D ∨ FlatLicense m D ∨ ConfluenceLicense m D`. The endpoint theorem is then derived by induction over normalization/rewrite paths or over completed critical pairs. None of the licenses contains the desired endpoint equality as an input.

```lean
theorem routeIndependentEndpoint_generic
    (m : RawRouteSystem) (D : List m.Route) (r s : m.Route)
    (ha : AdmissibleRoute m r) (hb : AdmissibleRoute m s)
    (boundary : m.boundary r = m.boundary s)
    (hD : ComparisonDomain m D r s)
    (license : RouteLicense m D) :
    m.endpoint r = m.endpoint s
```

**Necessity countermodel.** Use three distinct admissible one-event routes `r₀,r₁,r₂`, all with the same boundary. Fix the one-bit initial state at `0`; the two distinct event paths `r₀,r₁` apply the identity action, while `r₂` applies the bit-toggle action. Endpoint values are **computed by folding these actions**, giving `0,0,1`. The raw rewrite graph has no edges; the clock translation for the `r₂` path is the same toggle, giving nonzero loop holonomy. Set `D = {r₀,r₁,r₂}` before evaluating it. Thus `endpoint r₀ = endpoint r₁` by raw execution. No boundary-canonical normalization can be reached by rewrites from all three routes (the empty rewrite graph leaves each at its own normal form); global confluence on `D` fails at `r₀,r₂`; flatness fails its covered critical comparison and zero-clock test. The pair `r₀,r₁` therefore has coincident endpoints but **none** of the three defined licenses on the declared comparison domain. This is a finite countermodel sketch to literal necessity, not yet a Lean theorem; it should be predeclared and evaluated before use as evidence. **Non-vacuity:** `diamondCertificate` (`Transport/FiniteExamples.lean:128`) is an existing normalization schema instance but its endpoint is constant; POS-04’s `routeStatusOf` is `.routeIndexed`, not a flat license (`POS04/Assembly.lean:303–320`). Missing raw-execution adapter and a nonconstant positive license instance. **09 text:** the narrowing is **forced**: “Two admissible same-boundary routes have equal temporal endpoints when an explicit nonvacuous flatness, normalization, or confluence certificate licenses their comparison.” **Owner N6.** Ceiling unchanged. (b), M; the finite countermodel and license mechanisms must be formalized.

## TTH-10 — strict record arrow

**Current and gap.** Appendix A (`Transport/RecordArrow.lean:16`): conclusion is definitionally the `StrictlyMonotoneOn` premise. Weak-collapse insufficiency has no witness.

**Proposed contract.** `RawRecordTransport` has source and target record readouts on events, a supported source event-edge relation, a raw event map, a target edge-support table, a numerical record translation `ρ : Nat → Nat`, and a raw increment table `δ : SourceEvent → SourceEvent → Nat`. Define `SourceArrow` and `TargetArrow` by *actual* record strict inequality on supported transitions. `RecordMapStepLaw` checks only that mapped source edges occur in the target edge table and that `targetRecord (mapEvent e) = ρ (sourceRecord e)`. `PositiveRecordIncrement` is the **independently checked raw equation** `ρ (sourceRecord e') = ρ (sourceRecord e) + δ e e'` with `0 < δ e e'` for every supported strict source edge. It mentions neither `TargetArrow` nor an inequality between target records. The target strict inequality follows by substituting the two map equations and the positive increment. An alternative law is a checked strict order embedding for `ρ` over the finite source-record range, again without mentioning `TargetArrow`. A second theorem uses a finite weakly monotone constant translation to show a strict source edge can collapse.

```lean
theorem monotoneRecordDescentTransportsArrow_generic
    (m : RawRecordTransport) (heq : RecordMapStepLaw m)
    (hinc : PositiveRecordIncrement m) :
    ∀ e e', SourceArrow m e e' →
      TargetArrow m (m.mapEvent e) (m.mapEvent e')

theorem weakRecordMonotonicityInsufficient_generic :
    ∃ m : RawRecordTransport,
      WeakRecordMonotone m ∧ HasSourceArrow m ∧ ¬ HasMappedTargetArrow m
```

**Non-vacuity:** POS-04 `bridge_positive` and C6 realized strict event steps (`POS04/Bridge.lean:114`; `POS04/C6.lean:55–65`); TTN-03 `ttn03_exists` (`Countermodels/RealControls.lean:171`) supplies no endogenous arrow. Missing bridge from POS-04 record update/realized edges to the raw `ρ,δ` equations and a positive-increment check; weak-collapse control can use existing record values, but is not yet a named theorem. **09 text/ceiling:** unchanged. (b), M, feasible once the raw increment law is computed rather than restating strict target order.

## TTD-01 — immediate direct successor

**Current and gap.** Appendix A (`Corridor/FiniteDirectSuccessor.lean:50,112`). The event-level conditions are free propositions stored in a certificate; `directSuccessorValidity` omits no storage/replay and no alternative parent.

**Proposed contract.** `RawDirect` has a finite typed event graph, source and target event, parent relation, generator relation, stored payload and its computed temporal signature, archive/storage/replay provenance, route residue, ownership and event order. `ImmediateDirect` is a *definition* checking: exactly one necessary source generator for the target event; edge immediate in the realized graph; full predictive/order/tick/progress/record/route payload preservation; no mediator path, replay token, or alternative parent; target ownership. The theorem extracts the computed obligations from graph equations and a local generation law, not from Boolean verdicts.
Here “necessary” is operational: remove that one source event while holding the target receiver rule fixed, then the generated target event must cease to occur. Uniqueness of a parent edge alone does not establish this counterfactual.

```lean
theorem directSuccessorValidity_generic
    (m : RawDirect) (h : DirectGenerationEquations m)
    (hu : UniqueNecessaryParent m) (hp : CompleteTemporalPayload m)
    (hn : NoMediatorOrReplay m) (ho : RouteOwnerTransfer m) :
    ImmediateDirect m
```

The row’s “valid only when” is a **necessity** claim; to cover it, also prove `ImmediateDirect m → UniqueNecessaryParent m ∧ CompleteTemporalPayload m ∧ NoMediatorOrReplay m ∧ RouteOwnerTransfer m` by unfolding, and keep this distinct from the assembly theorem above. **Non-vacuity:** none of the POS-04 mixed corridor legs is a mediator-free *immediate* direct edge; no Lean `AtomicDirectSuccessorCertificate` instance was found (L3a). Missing finite direct-edge model with a genuinely necessary parent and full payload. **09 text/ceiling:** unchanged as a criterion, but no promotion before nonempty positive witness. (b), L; feasible as a formal criterion, empirically uninstantiated.

## TTD-02 — overlap/direct incomparability

**Current and gap.** Appendix A (`Strengthening/ContinuityClass.lean:43,62`): both separating existential witnesses are premises; `overlap`/`direct` are arbitrary predicates; generalized class is a disjunction of labels rather than a typed path.

**Proposed contract.** Define `OverlapMode m := CorridorPass m.corridor`, `DirectMode m := ImmediateDirect m.direct`, and a sum-indexed `GeneralizedLeg` carrying either raw form. `GeneralizedPathPass` checks every leg with the appropriate computed predicate and adjacent typed frontiers.

```lean
theorem overlapDirectIncomparable_generic :
    (∃ m : ControlModel, OverlapMode m ∧ ¬ DirectMode m) ∧
    (∃ m : ControlModel, DirectMode m ∧ ¬ OverlapMode m) ∧
    (∀ m, OverlapMode m → GeneralizedMode m) ∧
    (∀ m, DirectMode m → GeneralizedMode m)
```

**Non-vacuity:** POS-04 gives a likely overlap-only witness (`corridor_positive`, `POS04/Corridor.lean:90`), but `DirectMode` must first be defined on the *same control-model domain* and proved false. No direct-only witness presently exists. Thus this existential theorem cannot be promoted from current models. **09 text/ceiling:** unchanged only if both witnesses are built; otherwise narrow to the currently proved embedding and mark incomparability conditional, an **owner decision N7**. (b), M/L depending on direct model; generic logic is easy, witness construction is the blocker.

## TTD-03 — direct-successor exclusions

**Current and gap.** Appendix A (`Corridor/FiniteDirectSuccessor.lean:63`): `DetachedOperationalPattern` (`:45`) contains four free fields, omits arbitrary reachability and temporal gap, and the certificate stores their negations.

**Proposed contract.** Define on one raw event graph `DetachedCopy` (target initialized by a copy edge outside the realized event graph), `ArchivalReplay` (the proposed parent is a stored replay event), `StorageMediated` (the proposed immediate edge passes through an intermediate store), and `TemporalGap` (the proposed source/target events have no realized adjacent frontier). Define **`DataReachable m` positively**: there exists a directed path of one or more edges in the raw *data-channel graph* carrying the source payload to a target input. This definition does **not** mention `¬ Generator`, `¬ ImmediateDirect`, or a missing event edge. A direct event may coexist with a separate data-channel path, so `ImmediateDirect m → ¬ DataReachable m` is false and must not be proposed as the row theorem. The correct “arbitrary reachability excluded as a criterion” result is nonimplication, witnessed by a data-only control.

Declare `dataOnlyControl` with two event vertices (`sourceEmit`, `targetRead`), one raw data-channel copy edge carrying the declared payload between them, and **no realized event-generation edge** between those vertices. The data-path witness is the singleton copy edge. A separate finite graph calculation shows the receiver has no generated target event and hence `¬ ImmediateDirect dataOnlyControl`. These are two positive raw checks on different graphs, not `DataReachable := ¬ ImmediateDirect`.

```lean
theorem directSuccessorExcludesDetached_generic
    (m : RawDirect) (h : ImmediateDirect m) :
    ¬ DetachedCopy m ∧ ¬ ArchivalReplay m ∧
    ¬ StorageMediated m ∧ ¬ TemporalGap m

theorem dataOnlyControl_raw :
    DataReachable dataOnlyControl ∧
    NoRealizedGeneration dataOnlyControl

theorem dataReachabilityInsufficient_generic :
    DataReachable dataOnlyControl ∧
    ¬ ImmediateDirect dataOnlyControl
```

`NoRealizedGeneration` is the **computed emptiness of the realized generation-edge list** for this declared two-vertex control. The second theorem uses `ImmediateDirect m → HasRealizedGeneration m`, proved from the raw direct criterion, to turn that positive emptiness calculation into `¬ ImmediateDirect`; it never defines data reachability through a negation.

**Non-vacuity:** TTN-01 detached T1 copy (`Countermodels/RealControls.lean:76`) supplies a negative control for detached copying, but its existing `detachedCopy` function is outside the temporal support graph and must be connected to the new raw data-channel path. `dataOnlyControl` needs a predeclared model, evaluation, then Lean proof; a positive `ImmediateDirect` model remains absent. **09 text/ceiling:** if “excludes arbitrary data reachability” means *reachability alone does not license direct succession*, the text can stay after the nonimplication theorem. If it means a direct edge cannot coexist with any data path, the wording must be narrowed to “... and shows that data reachability alone is insufficient”; **owner N8 pending interpretation**. (b), M; graph checks are feasible, but the missing direct positive witness still gates promotion.

## TTS-01 — generalized structural continuity

**Current and gap.** Appendix A (`Strengthening/ContinuityClass.lean:16,25,62,122`). Embeddings are `Or.inl`/`Or.inr`; paths contain mode labels and arbitrary validity/gap/frontier flags; strict-broader witness is assumed.

**Proposed contract.** `GeneralizedLeg` is a sum of raw overlap and raw direct legs; `LegPass` pattern-matches and computes `AtomicLegPass` or `ImmediateDirect`. `GeneralizedPath` is a nonempty typed list with adjacent exact carrier/frontier/route/owner interfaces. `PathPass` quantifies over every actual leg and adjacent pair. `StrictFIACHLineage` continues to require only overlap `CorridorPass`, never the generalized disjunction.

```lean
theorem generalizedTemporalContinuity_generic
    (a b : GeneralizedPath)
    (ha : PathPass a) (hb : PathPass b)
    (hc : PathCompatible a b) :
    PathPass (appendPath a b) ∧
    (∀ l, AtomicLegPass l → GeneralizedLegPass (.overlap l)) ∧
    (∀ l, ImmediateDirect l → GeneralizedLegPass (.direct l))
```

A separate nonbroadening theorem should state `StrictFIACHLineage m ↔ CorridorPass m.corridor` by definition and show direct-only legs do not enter it. **Non-vacuity:** POS-04 corridor (`POS04/Corridor.lean:90`) gives overlap embedding; no positive direct leg or compatible mixed path exists yet. Missing direct-edge model and mixed-frontier bridge. **09 text/ceiling:** unchanged only when a mixed path is instantiated; otherwise retain conditional. (b), L; generic list proof feasible.

## TTS-02 — exact vector defects

**Current and gap.** Appendix A (`Robustness/DefectVector.lean:24,69,90`). Components use `Nat` defects/tolerances, narrower than rational; equal-scalar opposite verdicts are assumed for an arbitrary profile instead of constructed for `VectorAccepts`.

**Proposed contract.** `RatDefectComponent` contains `hard : Bool`, `defect tolerance : Rat`, nonnegative proofs derived from raw exact residuals, and a component label. `RatVectorAccepts` is pointwise `hard → defect = 0`, `soft → defect ≤ tolerance`; `NoWorseRat` preserves labels/gate types/tolerances and decreases each defect. `scalarSum` is the exact sum of defects. Use the TTN-10 equal-scalar accepted/rejected *control* as an explicit data-level witness, with a declared soft allowance. The scalar witness is not a premise of the theorem.

```lean
theorem exactVectorAcceptance_generic
    (v : List RatDefectComponent) (h : RatVectorAccepts v) :
    (∀ c ∈ v, c.hard = true → c.defect = 0) ∧
    (∀ c ∈ v, c.hard = false → c.defect ≤ c.tolerance)

theorem exactVectorDownward_generic
    {lo hi : List RatDefectComponent}
    (horder : NoWorseRat lo hi) (hhi : RatVectorAccepts hi) :
    RatVectorAccepts lo

theorem scalarDoesNotDetermineExactAcceptance_generic :
    ∃ x y : List RatDefectComponent,
      x ≠ [] ∧ y ≠ [] ∧ scalarSum x = scalarSum y ∧
      RatVectorAccepts x ∧ ¬ RatVectorAccepts y
```

**Non-vacuity:** `ttn10_equal_scalar_different_acceptance` (`Countermodels/RealControls.lean:664`) proves the integer vector control; embed `Nat` in exact `Rat` and show the new `RatVectorAccepts` agrees. The allowance is a comparator design choice, not forced by CM-10 data. **09 text/ceiling:** unchanged. (b), M; feasible with Lean core `Rat` and list induction, or a scaled rational type with verified arithmetic.

## TTS-03 — componentwise temporal margin

**Current and gap.** Appendix A (`Robustness/TemporalMargins.lean:18,45`). One integer margin only yields `minimumIncrement ≤ ...` with no positivity; hard gates are free propositions; five temporal coordinates and every gate are not covered.

**Proposed contract.** `RawMargin` stores five named exact rational baseline increments and radii, an exact perturbation vector, plus a raw hard-gate model using the same package/corridor/autonomy/owner/route predicates as TTH-06. `WithinBox` compares each absolute perturbation to its radius. `PositiveCertifiedMargin` computes `0 < baseline_i - radius_i` for all five. `HardGatesHold` recomputes each discrete gate from the *perturbed* raw model. A separate `GateInvariantUnder` premise must be a raw-data law (e.g. gates depend only on untouched discrete fields), not the conclusion itself.

```lean
theorem boundedTemporalRobustness_generic
    (m : RawMargin) (hbase : PositiveCertifiedMargin m)
    (hbox : WithinBox m) (hg0 : HardGatesHold m.base)
    (hinv : GateInvariantUnder m) :
    FiveAdvancesPositive m.perturbed ∧ HardGatesHold m.perturbed
```

If `GateInvariantUnder` simply says the gates hold after perturbation, the result is projection and must not be promoted. **Non-vacuity:** no existing POS-04 perturbation box across all five coordinates and all hard gates; `C6Trace` has strict event order but no rational margins (`POS04/C6.lean:55`). Missing finite box with positive slacks and a raw gate invariance lemma. **09 text/ceiling:** current “every perturbation inside ...” silently needs a gate-stability domain; exact proposed narrower wording: “Every perturbation in a declared exact five-component box with strictly positive certified slack and unchanged discrete hard-gate inputs preserves the five positive advances and every hard gate.” **Owner narrowing N9.** (b), L; arithmetic feasible, raw perturbation semantics is the risk.

## TTS-04 — model-relative infinite controlled run

**Current and gap.** Appendix A (`Autonomy/UnboundedInvariant.lean:50`). The recursion is real and quantifies every stream, but `antiStall` and `budgetSolvent` in `ExactAutonomyData` (`Autonomy/FiniteAutonomy.lean:6–15`) are arbitrary predicates, not progress/record/budget dynamics.

**Proposed typed contract.** `RawPolicy.State` is the **finite controlled factor**, with a `FiniteEnum` and raw action/transition table. `RawPolicy.RunState` is a separate, generally infinite type carrying a factor projection `factor : RunState → State`, event-indexed `progress : RunState → Nat`, `record : RunState → Nat`, and `balance : RunState → Rat`. A concrete implementation may use `RunState = State × Nat × Nat × Rat`; the factor projection is the first coordinate. `PolicyInside` and the greatest viable subset are predicates on `State` only. `PackageAt m s` means the eight checks on the finite factor state `s`; it does not require the package to encode unbounded counters. `policyAction` reads the finite factor and disturbance; `liftStep` applies the raw factor transition, adds **computed positive** event increments to progress and record, and applies the exact ledger equation to balance. `TotalComputedPolicy` checks for **every** invariant factor state and admitted disturbance that the chosen action is target-owned, its raw row is supported and remains inside, both increments are positive, and the ledger equation preserves the explicit affordability invariant `balance ≥ actionCost` for every run state satisfying it. An initially affordable balance and a declared zero-net-cost or replenishment law are therefore substantive premises, not a stored solvency verdict. The admitted disturbances form the declared `m.Disturbance` type; the theorem covers every stream of that type.

The intended finite-factor projection is explicit in the proposed type, rather than using `State` for both levels:

```lean
structure EventRunState (State : Type) where
  factorState : State
  progressCounter : Nat
  recordCounter : Nat
  balance : Rat

-- RawPolicy.State has a finite enumeration; RawPolicy.RunState is EventRunState RawPolicy.State.
def RawPolicy.factor (m : RawPolicy) (x : m.RunState) : m.State := x.factorState
```

```lean
theorem modelRelativeUnboundedControlledInvariant_generic
    (m : RawPolicy) (h : TotalComputedPolicy m)
    (stream : Nat → m.Disturbance) :
    ∃ run : Nat → m.RunState,
      run 0 = m.initial ∧
      ∀ n, m.factor (run n) ∈ m.greatestViable ∧
        PackageAt m (m.factor (run n)) ∧
        TargetOwnedAction m (m.factor (run n)) (stream n) ∧
        StepOf m (run n) (stream n) (run (n+1)) ∧
        m.progress (run n) < m.progress (run (n+1)) ∧
        m.record (run n) < m.record (run (n+1)) ∧
        0 ≤ m.balance (run (n+1))
```

`RunState` must include unbounded counters/ledger while only its *factor* is finite. Recursion on `n` constructs the run; the `TotalComputedPolicy` raw equations prove each inductive step and give the strongest model-relative all-stream result. A recurrent finite state cannot itself carry a strictly increasing `Nat` progress or record function: by finiteness, an infinite factor trajectory repeats a state, while strict growth along every step would make its value at the later occurrence larger than its earlier value, contradiction. This makes N10's narrowing **forced** if progress/record were intended as state functions. `TotalComputedPolicy` must not merely rename stored `antiStall`/`budgetSolvent` fields. **Non-vacuity:** POS-04 `c8_target_only_after_withdrawal` (`POS04/C8.lean:255`) supplies an exact finite target-owned factor invariant and a one-token recharge rule, but no infinite event-indexed progress/record run exists yet. Missing run-state lifting and a proof that the raw ledger remains solvent for all streams; a finite fixed budget with positive recurring cost and no recharge cannot do this. **09 text/ceiling:** forced narrowing to: “A total target-owned policy on an exact finite controlled factor, with a declared indefinitely solvent event ledger, defines a model-relative infinite event-indexed run preserving the package, ownership, positive event progress and record advance for every admitted disturbance stream.” **Owner N10**; (b), L.

## Dependency-ordered implementation plan

Registry edges used (only edges entering the scoped rows): `TTH-01→TTH-02`; `TTH-03→TTH-04,TTH-10,TTD-01`; `TTN-04→TTH-04,TTH-09`; `TTN-05→TTH-09`; `TTH-02,TTH-04,TTH-05→TTH-06`; `TTH-04,TTN-11→TTH-08`; `TTH-04,TTH-05,TTH-06,TTH-09→TTH-07`; `TTH-04,TTD-01→TTD-02`; `TTD-01,TTN-01→TTD-03`; `TTH-04,TTD-01,TTD-02→TTS-01`; `TTN-10→TTS-02`; `TTH-06,TTS-02→TTS-03`; `TTH-05,TTN-12→TTS-04`. Existing TTH-01/TTH-05 and TTN rows are prerequisites, not re-proved by this plan.

| Packet | Rows and gate | Size |
|---|---|---|
| G1 | TTH-03 raw bridge and nonempty POS-04 adapter; TTH-10 record transport/control | L |
| G2 | TTH-02 source→mapped target local package, locality and gluing; retain declared surrogate ceiling | L |
| G3a — model declaration | Pre-register the three-route necessity control and one nonconstant positive route comparison, with raw action, rewrite, clock and comparison-domain tables. | S |
| G3b — evaluation | Independently evaluate endpoint coincidence, nonexistence of all three licenses on the control, and the positive route-license prediction. | M |
| G3c — Lean bridge | Prove the three generic sufficient-license theorems and the evaluated necessity countermodel. | M |
| G4 | TTH-04 raw atomic corridor chain/adjacent exactness, POS-04 two-leg adapter | L |
| G5 | TTD-01 raw direct-event criterion, including counterfactual necessity. Any new positive control is declared before evaluation; no promotion yet if absent. | L |
| G6a — declaration | Pre-register POS-04-family package-only, lineage-only, and new withdrawal-only controls on one raw model interface. The new withdrawal change touches only the post-exit retention rule. | S |
| G6b — evaluation | Evaluate all three controls with identical predicates; require each selected lane false and the other two true. Report any side effects or failed predictions without tuning. | M |
| G6c — Lean bridge | TTH-06 substantive raw handoff/readout and POS-04 positive instance; prove the three evaluated lane-separation results before promotion. | L |
| G7a — model declaration | Pre-register a second compatible handoff, receiver injectivity and causal activation tables, and a two-branch fork with branch-owned package/autonomy data. No verdict computation. | M |
| G7b — evaluation | Independently evaluate TTH-07 composite content/source-absence and all other interfaces, plus both TTH-08 branch handoffs, swap and autonomy. A failed prediction stays failed. | M |
| G7c — Lean bridge | Prove TTH-07 full `HandoffPass` composition from the explicit laws; prove TTH-08 relation and no invariant singleton selector only to the evaluated grade. | L |
| G8a — model declaration | Pre-register a positive direct edge, a direct-only witness, an overlap-only control on the same domain, and `dataOnlyControl` with one data edge and no realized generation edge. | M |
| G8b — evaluation | Compute TTD-01 criterion, both TTD-02 directions, and TTD-03 positive data reachability plus failure of direct succession, from raw graphs. | M |
| G8c — Lean bridge | Prove TTD-02 incomparability and typed embeddings, and TTD-03 four exclusions plus data-reachability nonimplication; complete TTD-01 non-vacuity. | L |
| G9 | TTS-01 typed mixed-mode path and nonbroadening theorem | L |
| G10 | TTS-02 rational component defects and built equal-scalar control | M |
| G11 | TTS-03 exact box, positive slack, discrete gate invariance | L |
| G12a — model declaration | Pre-register the event-indexed `RunState`, finite-factor projection, positive counter increments, ledger/recharge rule and all-stream policy. State any new non-T1 data explicitly. | M |
| G12b — evaluation | Independently check finite-factor closure, increment positivity and exact ledger solvency for every raw state/disturbance; test a depleted-resource negative without tuning. | M |
| G12c — Lean bridge | Prove TTS-04 event-indexed run by induction from the evaluated laws; exhibit a concrete policy and the finite-state impossibility lemma. | L |

This is a valid topological order of the listed dependencies: G6c follows TTH-02/TTH-04/TTH-05; G7c follows TTH-04/TTH-05/TTH-06/TTH-09 and the existing TTN-11 witness; G8c follows TTH-04/TTD-01 and TTN-01; G9 follows G8c; G11 follows G6c/G10; G12c follows existing TTH-05/TTN-12. Each **new** control is fixed in a declaration packet, evaluated in a separate packet after commitment, and only then bridged in Lean. **Promotion is gated by both** the generic proof and a concrete nonempty instance of its hypotheses. If every row met that bar after owner-approved wording, the 09 successor surface would move from `2 proved / 14 checked finite countermodel / 15 conditional / 8 open` to `17 proved / 14 checked / 0 conditional / 8 open`. That is a projection of a future status surface, not a current result. Several gates above have no model today, so the likely near-term proved count is smaller.

## Owner decisions and falsity findings

| ID | Class | Decision needed |
|---|---|---|
| N1 TTH-02 | **Pending interpretation** | Clarify whether “integrated” means the eight-clause package at declared grades (C4–C7 remain POS-04 surrogates) or full P05; do not promote under the latter reading. |
| N2 TTH-03 | **Pending interpretation/witness** | Specify the admissible reachable-history domain, or supply data for all histories. The current row does not explicitly require all possible histories. |
| N3 TTH-06 | **Pending interpretation/witness** | Split schema readout from substantive raw-data theorem; finite structural ceiling with surrogate clauses requires the three isolated lane controls. |
| N4 TTH-07 | **Pending witness** | Keep the full conclusion using receiver injectivity and causal activation; a concrete second hop remains missing. No narrowing is proposed. |
| N5 TTH-08 | **Pending witness/interpretation** | Decide whether “valid fork” requires two strict handoffs or only branch-owned structural continuation; currently only the latter has partial controls. |
| N6 TTH-09 | **Forced** | Replace literal necessity-sounding “only under” with a sufficient-license claim. The three-route raw countermodel above has coincident endpoints but no license on its declared comparison domain. |
| N7 TTD-02 | **Pending witness** | Retain incomparability conditional until a direct-only witness exists; narrowing to embeddings is an alternative owner choice, not forced by a countermodel. |
| N8 TTD-03 | **Pending interpretation/witness** | “Arbitrary data reachability excluded” should mean reachability alone is insufficient. A direct edge can coexist with a data path, so literal `Direct → ¬ DataReachable` would require forced narrowing; the operational reading awaits a declared control. |
| N9 TTS-03 | **Pending perturbation-domain definition** | Declare whether the exact box leaves discrete hard-gate inputs unchanged. The current box theorem proves only a numeric margin, so neither universal gate preservation nor its negation is established yet. |
| N10 TTS-04 | **Forced** | Lift finite controlled factor to event-indexed run state with a declared indefinitely solvent ledger. Strictly increasing progress/record functions on a recurrent finite state are impossible. |

No owner decision is silently applied to the 09 registry. In particular, a “generic theorem” built by requiring `HandoffPass` and returning its identically named conjuncts would still be a projection. The significant work is the raw-data-to-predicate bridge and nonvacuous instances.

## Appendix A — verbatim current registered Lean theorem headers

Each block is extracted from the current source through the theorem header’s `:= by`; the proof body is omitted. These are the *current* statements, not the proposed ones. Definitions they unfold to are identified in the row sections and the L3a audit.


### TTH-02

**`CSTTT.PackageTheory.stagedHeterogeneousPackageAssembly`** — `lean/CSTTT/Package/FiniteGluing.lean:158`

```lean
theorem stagedHeterogeneousPackageAssembly
    {Index SourceCoord TargetCoord SourceValue TargetValue : Type}
    (targetTree : RootedJoinTree Index TargetCoord)
    (stage :
      StagedHeterogeneousEvidence
        (SourceCoord := SourceCoord)
        (SourceValue := SourceValue)
        (TargetValue := TargetValue)
        targetTree)
    (edgeCompatible :
      ∀ i j : Index, ∀ c : TargetCoord,
        targetTree.adjacent i j →
        targetTree.scope i c → targetTree.scope j c →
        stage.targetLocal i c = stage.targetLocal j c) :
    stage.separatelyTyped ∧ stage.hardGatesNeverAveraged ∧
      Nonempty (IntegratedPackageWitness
        targetTree stage.targetLocal stage.targetAccepted stage.targetHardGate) := by
```


### TTH-03

**`CSTTT.TransportTheory.bundledHeterogeneousTemporalTransport`** — `lean/CSTTT/Transport/FiniteTemporalTransport.lean:63`

```lean
theorem bundledHeterogeneousTemporalTransport
    (Bridge : Type)
    (admissible representativeIndependent predictivePreserved orderPreserved
      tickPhasePreserved tickProgressPreserved recordDescentPreserved
      routeDisciplineSatisfied maintenanceTranslated ownershipInterfaceValid :
      Bridge → Prop)
    (b : Bridge)
    (p : FiniteTemporalTransportProof Bridge admissible representativeIndependent
      predictivePreserved orderPreserved tickPhasePreserved tickProgressPreserved
      recordDescentPreserved routeDisciplineSatisfied maintenanceTranslated
      ownershipInterfaceValid b) :
    representativeIndependent b ∧
    predictivePreserved b ∧
    orderPreserved b ∧
    tickPhasePreserved b ∧
    tickProgressPreserved b ∧
    recordDescentPreserved b ∧
    routeDisciplineSatisfied b ∧
    maintenanceTranslated b ∧
    ownershipInterfaceValid b := by
```


### TTH-04

**`CSTTT.CorridorTheory.strictTemporalCorridorComposition`** — `lean/CSTTT/Corridor/Composition.lean:61`

```lean
theorem strictTemporalCorridorComposition
    {Signature : Type}
    {left right : CorridorSummaryData Signature}
    (leftCert : CorridorSummaryCertificate left)
    (rightCert : CorridorSummaryCertificate right)
    (frontier : FrontierCompatible left right)
    (endpointsDistinct : left.source ≠ right.target) :
    Nonempty (CorridorSummaryCertificate (composeData left right)) := by
```

**`CSTTT.CorridorTheory.atomicTemporalCorridorCertificateSound`** — `lean/CSTTT/Corridor/FiniteTemporalCorridor.lean:75`

```lean
theorem atomicTemporalCorridorCertificateSound
    {d : AtomicTemporalCorridorData}
    (c : AtomicTemporalCorridorCertificate d) :
    d.source ≠ d.target ∧
    NoRealizedGap d.stages ∧
    HasMixedSupport d.source d.target d.stages ∧
    SourceNonredundant d.intervention ∧
    TargetNonredundant d.intervention ∧
    d.localStepsStrict ∧
    d.eventGraphForward ∧
    d.transportAudited ∧
    d.takeoverExact ∧
    d.routeDisciplined := by
```


### TTH-06

**`CSTTT.TargetTheory.temporalFIACHCertificateSoundness`** — `lean/CSTTT/Targets/FiniteTemporalFIACH.lean:8`

```lean
theorem temporalFIACHCertificateSoundness
    {PackageCert CorridorCert AutonomyCert : Type}
    {packageValid : PackageCert → Prop}
    {corridorValid : CorridorCert → Prop}
    {autonomyValid : AutonomyCert → Prop}
    {packageTarget : PackageCert → CarrierId}
    {corridorSource : CorridorCert → CarrierId}
    {corridorTarget : CorridorCert → CarrierId}
    {autonomyTarget : AutonomyCert → CarrierId}
    (cert : TemporalFIACHCertificate PackageCert CorridorCert AutonomyCert
      packageValid corridorValid autonomyValid packageTarget
      corridorSource corridorTarget autonomyTarget) :
    packageValid cert.packageCertificate ∧
    corridorValid cert.corridorCertificate ∧
    autonomyValid cert.autonomyCertificate := by
```


### TTH-07

**`CSTTT.TargetTheory.fullTemporalHandoffComposition`** — `lean/CSTTT/Targets/Composition.lean:62`

```lean
theorem fullTemporalHandoffComposition
    {Package Signature : Type}
    {left right : FullHandoffData Package Signature}
    (leftCert : FullHandoffCertificate left)
    (rightCert : FullHandoffCertificate right)
    (interface : FullHandoffCompatible left right)
    (endpointsDistinct : left.source ≠ right.target) :
    Nonempty (FullHandoffCertificate (composeFullHandoffData left right)) := by
```

**`CSTTT.TargetTheory.composedHandoffPreservesIndependentLanes`** — `lean/CSTTT/Targets/Composition.lean:79`

```lean
theorem composedHandoffPreservesIndependentLanes
    {Package Signature : Type}
    {left right : FullHandoffData Package Signature}
    (cert : FullHandoffCertificate (composeFullHandoffData left right)) :
    (left.realized ∧ right.realized) ∧
    (left.lineage ∧ right.lineage) ∧
    right.autonomous := by
```

**`CSTTT.TargetTheory.routeIndexedComponentPreventsAutomaticFlatness`** — `lean/CSTTT/Targets/Composition.lean:89`

```lean
theorem routeIndexedComponentPreventsAutomaticFlatness
    (left right : RouteStatus)
    (h : left ≠ .flat ∨ right ≠ .flat) :
    composeRouteStatus left right = .routeIndexed := by
```


### TTH-08

**`CSTTT.CorridorTheory.relationValuedTemporalFission`** — `lean/CSTTT/Corridor/Fission.lean:27`

```lean
theorem relationValuedTemporalFission
    {Source Target : Type}
    {d : TemporalFissionData Source Target}
    (cert : TemporalFissionCertificate d) :
    d.related d.source d.left ∧ d.related d.source d.right := by
```

**`CSTTT.CorridorTheory.targetSwapPreservesFissionValidity`** — `lean/CSTTT/Corridor/Fission.lean:35`

```lean
theorem targetSwapPreservesFissionValidity
    {Source Target : Type}
    {d : TemporalFissionData Source Target}
    (cert : TemporalFissionCertificate d) :
    d.valid (d.swap d.left) ∧ d.valid (d.swap d.right) := by
```

**`CSTTT.CorridorTheory.targetSwapSymmetryNonselection`** — `lean/CSTTT/Corridor/Fission.lean:44`

```lean
theorem targetSwapSymmetryNonselection
    {Source Target : Type}
    {d : TemporalFissionData Source Target}
    (cert : TemporalFissionCertificate d) :
    d.swap d.left ≠ d.left ∧ d.swap d.right ≠ d.right := by
```


### TTH-09

**`CSTTT.RouteTheory.routeIndependentEndpointUnderNormalization`** — `lean/CSTTT/Transport/RouteDiscipline.lean:121`

```lean
theorem routeIndependentEndpointUnderNormalization
    {Route Boundary Normal Endpoint : Type}
    (c : NormalizationCertificate Route Boundary Normal Endpoint)
    (r₁ r₂ : Route)
    (hsame : c.boundary r₁ = c.boundary r₂) :
    c.endpoint r₁ = c.endpoint r₂ := by
```

**`CSTTT.TargetTheory.certifiedNormalizationYieldsFlatStatus`** — `lean/CSTTT/Targets/RouteCompletion.lean:45`

```lean
theorem certifiedNormalizationYieldsFlatStatus
    {Package : Type}
    {d : RouteCompletionData Package}
    (cert : RouteCompletionCertificate d)
    (flat : d.flatnessCertified)
    (normal : d.commonNormalForm)
    (clock : d.zeroClockHolonomy) :
    d.outputStatus = .flat := by
```


### TTH-10

**`CSTTT.RecordTheory.monotoneRecordDescentTransportsArrow`** — `lean/CSTTT/Transport/RecordArrow.lean:16`

```lean
theorem monotoneRecordDescentTransportsArrow
    {SourceRecord TargetRecord : Type}
    (sourceLt : SourceRecord → SourceRecord → Prop)
    (targetLt : TargetRecord → TargetRecord → Prop)
    (mapRecord : SourceRecord → TargetRecord)
    (hmono : StrictlyMonotoneOn sourceLt targetLt mapRecord) :
    ∀ a b, sourceLt a b → targetLt (mapRecord a) (mapRecord b) := by
```


### TTD-01

**`CSTTT.DirectSuccessorTheory.directSuccessorValidity`** — `lean/CSTTT/Corridor/FiniteDirectSuccessor.lean:50`

```lean
theorem directSuccessorValidity
    {d : AtomicDirectSuccessorData}
    (c : AtomicDirectSuccessorCertificate d) :
    d.immediateEdge ∧ d.payloadComplete ∧ d.payloadHashBound ∧
    d.edgeNecessary ∧ d.predictiveStep ∧ d.orderStep ∧ d.tickStep ∧
    d.progressStep ∧ d.recordStep ∧ d.routeDisciplined ∧
    d.ownershipTransferred := by
```

**`CSTTT.DirectSuccessorTheory.directSuccessorPathComposition`** — `lean/CSTTT/Corridor/FiniteDirectSuccessor.lean:112`

```lean
theorem directSuccessorPathComposition
    {Signature : Type}
    {left right : DirectSuccessorPathData Signature}
    (leftCert : DirectSuccessorPathCertificate left)
    (rightCert : DirectSuccessorPathCertificate right)
    (frontier : DirectPathCompatible left right)
    (endpointsDistinct : left.source ≠ right.target) :
    Nonempty (DirectSuccessorPathCertificate (composePathData left right)) := by
```


### TTD-02

**`CSTTT.StrengtheningTheory.overlapDirectIncomparable`** — `lean/CSTTT/Strengthening/ContinuityClass.lean:43`

```lean
theorem overlapDirectIncomparable
    {Model : Type}
    {overlap direct : Model → Prop}
    (overlapOnly : ∃ m, overlap m ∧ ¬ direct m)
    (directOnly : ∃ m, direct m ∧ ¬ overlap m) :
    EvidenceModesIncomparable overlap direct := by
```

**`CSTTT.StrengtheningTheory.generalizedStrictlyBroaderThanOverlap`** — `lean/CSTTT/Strengthening/ContinuityClass.lean:62`

```lean
theorem generalizedStrictlyBroaderThanOverlap
    {Model : Type}
    {overlap direct : Model → Prop}
    (directOnly : ∃ m, direct m ∧ ¬ overlap m) :
    StrictlyBroaderThan
      (GeneralizedTemporalContinuity overlap direct)
      overlap := by
```


### TTD-03

**`CSTTT.DirectSuccessorTheory.directSuccessorDetachedCopyExclusion`** — `lean/CSTTT/Corridor/FiniteDirectSuccessor.lean:63`

```lean
theorem directSuccessorDetachedCopyExclusion
    {d : AtomicDirectSuccessorData}
    (c : AtomicDirectSuccessorCertificate d) :
    ¬ DetachedOperationalPattern d := by
```


### TTS-01

**`CSTTT.StrengtheningTheory.overlapEmbedsGeneralized`** — `lean/CSTTT/Strengthening/ContinuityClass.lean:16`

```lean
theorem overlapEmbedsGeneralized
    {Model : Type}
    {overlap direct : Model → Prop}
    {m : Model}
    (h : overlap m) :
    GeneralizedTemporalContinuity overlap direct m := by
```

**`CSTTT.StrengtheningTheory.directEmbedsGeneralized`** — `lean/CSTTT/Strengthening/ContinuityClass.lean:25`

```lean
theorem directEmbedsGeneralized
    {Model : Type}
    {overlap direct : Model → Prop}
    {m : Model}
    (h : direct m) :
    GeneralizedTemporalContinuity overlap direct m := by
```

**`CSTTT.StrengtheningTheory.generalizedStrictlyBroaderThanOverlap`** — `lean/CSTTT/Strengthening/ContinuityClass.lean:62`

```lean
theorem generalizedStrictlyBroaderThanOverlap
    {Model : Type}
    {overlap direct : Model → Prop}
    (directOnly : ∃ m, direct m ∧ ¬ overlap m) :
    StrictlyBroaderThan
      (GeneralizedTemporalContinuity overlap direct)
      overlap := by
```

**`CSTTT.StrengtheningTheory.generalizedPathComposition`** — `lean/CSTTT/Strengthening/ContinuityClass.lean:122`

```lean
theorem generalizedPathComposition
    {Signature : Type}
    {left right : GeneralizedPathData Signature}
    (leftCert : GeneralizedPathCertificate left)
    (rightCert : GeneralizedPathCertificate right)
    (frontier : GeneralizedPathCompatible left right)
    (endpointsDistinct : left.source ≠ right.target) :
    Nonempty (GeneralizedPathCertificate (composeGeneralizedPath left right)) := by
```


### TTS-02

**`CSTTT.DefectTheory.acceptedHardGateIsZero`** — `lean/CSTTT/Robustness/DefectVector.lean:24`

```lean
theorem acceptedHardGateIsZero
    (v : DefectVector)
    (hAccept : VectorAccepts v)
    (c : DefectComponent)
    (hMem : c ∈ v)
    (hHard : c.hard = true) :
    c.defect = 0 := by
```

**`CSTTT.DefectTheory.vectorAcceptanceDownwardClosed`** — `lean/CSTTT/Robustness/DefectVector.lean:69`

```lean
theorem vectorAcceptanceDownwardClosed
    {lower upper : DefectVector}
    (hOrder : NoWorse lower upper)
    (hUpper : VectorAccepts upper) :
    VectorAccepts lower := by
```

**`CSTTT.DefectTheory.scalarSummaryDoesNotDetermineAcceptance`** — `lean/CSTTT/Robustness/DefectVector.lean:90`

```lean
theorem scalarSummaryDoesNotDetermineAcceptance
    {Profile : Type}
    (scalar : Profile → Nat)
    (accepts : Profile → Prop)
    (accepted rejected : Profile)
    (sameScalar : scalar accepted = scalar rejected)
    (hAccepted : accepts accepted)
    (hRejected : ¬ accepts rejected) :
    ∃ x y, scalar x = scalar y ∧ accepts x ∧ ¬ accepts y := by
```


### TTS-03

**`CSTTT.RobustnessTheory.boundedPerturbationPreservesMargin`** — `lean/CSTTT/Robustness/TemporalMargins.lean:18`

```lean
theorem boundedPerturbationPreservesMargin
    (m : TemporalMargin)
    (delta : Int)
    (hDelta : WithinRadius m delta) :
    m.minimumIncrement ≤ m.baseIncrement + delta := by
```

**`CSTTT.RobustnessTheory.failedHardGateCannotBeAveragedAway`** — `lean/CSTTT/Robustness/TemporalMargins.lean:45`

```lean
theorem failedHardGateCannotBeAveragedAway
    (g : HardGateBundle)
    (hFail : ¬ g.integratedPackage) :
    ¬ Nonempty (HardGateCertificate g) := by
```


### TTS-04

**`CSTTT.AutonomyTheory.modelRelativeUnboundedControlledInvariant`** — `lean/CSTTT/Autonomy/UnboundedInvariant.lean:50`

```lean
theorem modelRelativeUnboundedControlledInvariant
    {d : ExactAutonomyData}
    (cert : ExactAutonomyCertificate d)
    (policy : ExactAutonomyPolicy d)
    (disturbance : Nat → d.sys.Disturbance) :
    ∀ n,
      d.sys.packageValid (policyState policy disturbance n) ∧
      d.sys.actionOwner
        (policy.action (policyState policy disturbance n) (disturbance n)) =
        d.sys.carrier.id ∧
      d.sys.step
        (policyState policy disturbance n)
        (disturbance n)
        (policy.action (policyState policy disturbance n) (disturbance n))
        (policyState policy disturbance (n + 1)) ∧
      d.antiStall
        (policyState policy disturbance n)
        (disturbance n)
        (policy.action (policyState policy disturbance n) (disturbance n))
        (policyState policy disturbance (n + 1)) ∧
      d.budgetSolvent
        (policyState policy disturbance n)
        (disturbance n)
        (policy.action (policyState policy disturbance n) (disturbance n))
        (policyState policy disturbance (n + 1)) := by
```

## Appendix B — current CST-TT-09 row sentences and ceilings

This table is mechanically transcribed from `CST-TT-09_THEOREM_STATUS.csv` for the 15 explicit row IDs. Proposed replacements, where needed, appear in the corresponding sections above.

| Row | `exact_statement` | `ceiling_09` |
|---|---|---|
| TTH-02 | Separately typed, total, value-preserving source-to-target clause maps plus an independently valid target gluing certificate assemble one integrated target package without using lineage or autonomy premises. | structural package only |
| TTH-03 | An admissible representative-independent heterogeneous bridge transports every component of the frozen temporal signature: predictive now, order, tick, progress, strict record arrow, route status, maintenance state, and target ownership. | structural transport only |
| TTH-04 | Audited atomic overlap legs compose into a strict carrier-chain temporal corridor when consecutive legs agree exactly on the intermediate carrier, temporal frontier, route residue, and ownership interface. | structural lineage criterion only |
| TTH-06 | A valid Temporal-FIACH certificate entails, as separate fields, integrated target realization, strict temporal lineage, and post-withdrawal autonomy; none of the three is inferred from either of the others. | structural precursor only |
| TTH-07 | Two valid Temporal-FIACH handoffs compose when their package maps factor through the same intermediate package and their corridor, route-memory, ownership, and autonomy interfaces agree. | structural precursor only |
| TTH-08 | A symmetric valid fork is relation-valued: one source may stand in the structural continuation relation to two swap-related autonomous targets, without an invariant singleton selector. | no unique identity conclusion |
| TTH-09 | Two admissible routes with the same boundary have the same temporal endpoint only under an explicit flatness, normalization, or confluence certificate. | route independence only under premises |
| TTH-10 | A record map that preserves every declared strict source-record step preserves the endogenous target arrow; weak monotonicity that collapses strict steps is insufficient. | structural arrow audit only |
| TTD-01 | An immediate direct temporal successor is valid only when one necessary source event generates one target event with complete temporal payload, no storage/replay mediator, no alternative parent, and correct route and ownership transfer. | separate broader criterion |
| TTD-02 | Strict overlap continuity and direct temporal successorship are incomparable: exact witnesses exist for each class outside the other, while both embed in a separately named generalized path relation. | no silent broadening |
| TTD-03 | The frozen direct-successor criterion excludes detached copies, archival replay, storage-mediated reconstruction, temporal gaps, and arbitrary data reachability. | provenance boundary |
| TTS-01 | Strict-overlap and direct-successor legs each embed into a generalized structural-continuity path class, and compatible mixed-mode legs compose there without broadening strict Temporal-FIACH. | broader structural lineage vocabulary only; strict FIACH unchanged |
| TTS-02 | Acceptance under the exact defect semantics is componentwise: every hard-gate defect is zero and every soft defect lies below its own rational tolerance; acceptance is downward closed and not determined by a scalar summary. | finite exact componentwise defect semantics only |
| TTS-03 | Every perturbation inside the declared exact componentwise margin preserves positive predictive, order, tick, progress, and record advances while leaving every hard gate satisfied. | declared exact finite perturbation box only |
| TTS-04 | A total target-owned policy on the exact finite controlled invariant defines a model-relative infinite run that preserves package integrity, progress, record advancement, ownership, and solvency for every admissible disturbance stream. | infinite run inside the exact finite controlled model; no physical persistence theorem |
