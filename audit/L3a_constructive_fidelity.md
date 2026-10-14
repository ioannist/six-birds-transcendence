# L3a constructive statement-fidelity audit

Scope: the 17 conditional rows TTH-01–10, TTD-01–03, and TTS-01–04 in `cst-tt/registries/FINAL_THEOREM_STATUS.csv`. The verdict tests the **registry sentence at its claim ceiling**, not whether a declaration compiles. A stored proof field is a valid conditional premise, but projecting it does not independently establish the mechanism described in the registry. “None” under nonemptiness means no concrete instantiation of the row theorem's premises was found in `lean/CSTTT`; it is not a proof that the premises are inconsistent. All quoted Lean fragments below are from the indicated current source lines. No source or status is changed here.

## TTH-01 — Acyclic local-witness gluing

**Verdict: FAITHFUL (stronger in part).** **Registry text:** “For any finite rooted acyclic running-intersection cover, edge-compatible locally accepted witnesses whose hard gates all pass determine a global assignment restricting to every local witness.” Ceiling: structural package only.

**Lean quotation and unfolding.** `lean/CSTTT/Package/FiniteGluing.lean:104–115` returns `IntegratedPackageWitness tree localAssignment accepted hardGate` from `edgeCompatible`, `allAccepted : ∀ i : Index, accepted i`, and `allHardGates : ∀ i : Index, hardGate i`. The actual constructed field is `global := gluedAssignment tree localAssignment` (`:118`); `gluedAssignment` selects `localAssignment (Classical.choose (tree.covers c)) c` (`:66–70`). The witness requires `restricts : ∀ i, ∀ c, tree.scope i c → global c = localAssignment i c` but merely stores `everyLocalAccepted : ∀ i, accepted i` and `everyHardGatePassed : ∀ i, hardGate i` (`:91–99`). The nontrivial restriction equality follows from `runningIntersection` (`:32–36`) and edge compatibility (`:73–88`).

**Gap:** none at the row's structural-package ceiling: `FiniteGluing.lean:104–122` proves precisely the requested global restriction equality. The gluing argument needs no finiteness premise, so it is stronger on the cover's size. The `accepted` and `hardGate` premises are unused for that equality; their proof fields are carried into the witness, but the row does not claim global clause acceptance. **Nonemptiness:** none; no `RootedJoinTree` with locally accepted assignments is instantiated in Lean. **Registry drift:** none; `:104` names the declaration. **Repair:** none for this row. A recommended follow-up theorem could connect assignment-dependent local acceptance and gates (`lean/CSTTT/Package/Clauses.lean:34–44`) to acceptance of the glued assignment under suitable locality laws. Size **—** for row fidelity.

## TTH-02 — Staged heterogeneous package assembly

**Verdict: PROJECTION.** **Registry text:** “Separately typed, total, value-preserving source-to-target clause maps plus an independently valid target gluing certificate assemble one integrated target package without using lineage or autonomy premises.” Ceiling: structural package only.

**Lean quotation and unfolding.** `lean/CSTTT/Package/FiniteGluing.lean:158–178` concludes `stage.separatelyTyped ∧ stage.hardGatesNeverAveraged ∧ Nonempty (IntegratedPackageWitness targetTree stage.targetLocal stage.targetAccepted stage.targetHardGate)`. `StagedHeterogeneousEvidence` stores `separatelyTypedPass : separatelyTyped` and `hardGatesNeverAveragedPass : hardGatesNeverAveraged` (`:138–141`), plus total map and pointwise equality fields (`:142–152`). The proof projects those two passes and calls `acyclicLocalWitnessGluing` on `stage.targetLocal`, `stage.targetAccepted`, and `stage.targetHardGate` (`:175–178`).

**Gap.** The map fields `mapCoord`, `mapValue`, `everySourceCoordinateMapped`, `everyTargetCoordinateMapped`, and `mappedValuesAgree` are unused in the assembly proof. Target-local assignments, acceptance, and hard gates are independently supplied; no source-to-target map is shown to produce or preserve an accepted target clause. The target witness itself is a generic gluing structure, not an `EightClauseIntegratedPackage` (`lean/CSTTT/Package/TemporalPackage.lean:35–44`). **Nonemptiness:** none; no `StagedHeterogeneousEvidence` instance. **Registry drift:** none; `:158` is exact. **Repair:** split the generic target-gluing result from a new source-to-target assembly theorem that derives target witnesses through the maps and supplies the integrated eight-clause package. Size **L**.

## TTH-03 — Bundled heterogeneous temporal transport

**Verdict: PROJECTION.** **Registry text:** “An admissible representative-independent heterogeneous bridge transports every component of the frozen temporal signature: predictive now, order, tick, progress, strict record arrow, route status, maintenance state, and target ownership.” Ceiling: structural transport only.

**Lean quotation and unfolding.** `lean/CSTTT/Transport/FiniteTemporalTransport.lean:63–82` concludes `representativeIndependent b ∧ predictivePreserved b ∧ orderPreserved b ∧ tickPhasePreserved b ∧ tickProgressPreserved b ∧ recordDescentPreserved b ∧ routeDisciplineSatisfied b ∧ maintenanceTranslated b ∧ ownershipInterfaceValid b`. Every predicate is an arbitrary `Bridge → Prop` argument, and `FiniteTemporalTransportProof` stores each identically named `_ok` proof field (`:43–59`); the proof is field projection (`:83–91`). A concrete signature agreement structure separately equates mapped components (`:18–38`), but this theorem does not use it.

**Gap.** There is no implication from an admissible representative-independent `TemporalBridge` or `ClockTranslation` to component preservation; all component conclusions are already hypotheses inside `p`. In particular `routeDisciplineSatisfied` and `recordDescentPreserved` are unconstrained predicates rather than derived route or strict-arrow laws. **Nonemptiness:** no instance of `FiniteTemporalTransportProof`; `lean/CSTTT/Transport/FiniteExamples.lean:94–107` proves a concrete `TemporalSignatureAgreement` only, and its clock coherence fields are `True` (`:58–70`). **Registry drift:** none; `:63` is exact. **Repair:** strengthen Lean with a bridge-to-agreement theorem over actual source/target signatures. The implementation must define *admissible* substantively: a total, well-typed bridge and clock map on the declared reachable domain, with target ownership and applicable source/target signatures, rather than an arbitrary `Bridge → Prop`. Representative independence must make the pushed predictive class well defined, while separate laws must preserve predictive-now class, route residue and future sufficiency; order relations and strict steps; tick phase, successor and positive progress; strict record steps and the target arrow; route discipline through a specified residue map or a flatness/confluence license; and maintenance-state translation and target ownership. The component equalities of `TemporalSignatureAgreement` (`FiniteTemporalTransport.lean:18–38`) can express part of the conclusion, but do not supply those strict, successor, or route laws. Prove the consequences from these laws and instantiate a nontrivial finite bridge. Strengthening `admissible` and adding these bridge laws are **(b) mathematical changes** for a future implementation packet, not porting repairs. Size **L**.

## TTH-04 — Strict temporal-corridor composition

**Verdict: WEAKER.** **Registry text:** “Audited atomic overlap legs compose into a strict carrier-chain temporal corridor when consecutive legs agree exactly on the intermediate carrier, temporal frontier, route residue, and ownership interface.” Ceiling: structural lineage criterion only.

**Lean quotation and unfolding.** `lean/CSTTT/Corridor/Composition.lean:61–69` gives `Nonempty (CorridorSummaryCertificate (composeData left right))` from two `CorridorSummaryCertificate`s, `frontier : FrontierCompatible left right`, and `endpointsDistinct`. Unfolding gives `FrontierCompatible left right := left.target = right.source ∧ left.exit = right.entry` (`:27–30`) and `composeData` joins arbitrary `atomicLegsValid`, `noRealizedGap`, and `routeDisciplined` propositions by conjunction (`:33–43`). The second registered theorem, `atomicTemporalCorridorCertificateSound` (`lean/CSTTT/Corridor/FiniteTemporalCorridor.lean:75–91`), only projects the fields of one atomic certificate, including `NoRealizedGap` and `HasMixedSupport` (`:20–28`, `:60–72`).

**Gap.** No function turns an `AtomicTemporalCorridorCertificate` into a `CorridorSummaryCertificate`, and the summary contains no list of legs. Route residue and ownership-interface equality are absent from `FrontierCompatible`; the exact intermediate conditions in the row are therefore unproved. **Nonemptiness:** none; no positive atomic or summary corridor certificate is constructed in Lean. **Registry drift:** both `Composition.lean:61` and `FiniteTemporalCorridor.lean:75` match. **Repair:** strengthen Lean with a nonempty chain of actual atomic certificates and explicit adjacent carrier/frontier/route/owner equalities, then derive the summary certificate by chain induction. Size **L**.

## TTH-05 — Post-withdrawal finite-horizon invariance

**Verdict: FAITHFUL.** **Registry text:** “Within the declared finite model, a target-owned response law that keeps every disturbed state inside the controlled invariant yields post-withdrawal finite-horizon package preservation.” Ceiling: model-relative autonomy only.

**Lean quotation and unfolding.** `lean/CSTTT/Autonomy/FiniteAutonomy.lean:87–95` proves `∃ y, ControlledRun d d.endpoint word y ∧ d.sys.packageValid y` for every finite disturbance `word` from `cert : ExactAutonomyCertificate d`. The certificate supplies `endpointInside`, `packageInside`, and a response for every inside state and disturbance with target-owned action, step, next state inside, anti-stall, and solvency (`:19–45`). `ControlledRun` records each such step (`:49–64`); `finiteHorizonRunExists` actually inducts on the word (`:67–83`). `ControlledSystem` carries finite state, disturbance, and action enumerations (`lean/CSTTT/Core/Carrier.lean:13–17`; `lean/CSTTT/Autonomy/System.lean:5–14`).

**Gap:** none at the declared finite-model ceiling. Withdrawal checks are certificate premises (`FiniteAutonomy.lean:20–27`), not independently established physical facts. **Nonemptiness:** none; no `ExactAutonomyCertificate` is instantiated in Lean. **Registry drift:** none; `:87` is exact. **Repair:** none for fidelity. An independently constructed positive certificate is still needed before treating the conditional theorem as an instantiated model. Size **—**.

## TTH-06 — Temporal-FIACH certificate soundness

**Verdict: PROJECTION.** **Registry text:** “A valid Temporal-FIACH certificate entails, as separate fields, integrated target realization, strict temporal lineage, and post-withdrawal autonomy; none of the three is inferred from either of the others.” Ceiling: structural precursor only.

**Lean quotation and unfolding.** `lean/CSTTT/Targets/FiniteTemporalFIACH.lean:8–23` returns `packageValid cert.packageCertificate ∧ corridorValid cert.corridorCertificate ∧ autonomyValid cert.autonomyCertificate` by `⟨cert.packageEvidence, cert.corridorEvidence, cert.autonomyEvidence⟩`. The certificate takes arbitrary validity predicates on arbitrary certificate types, and stores exactly these three proofs (`lean/CSTTT/Targets/TemporalFIACH.lean:17–42`). Endpoint equations are separately stored (`:35–42`), not in the registered conclusion.

**Gap.** The field separation itself matches the registry's second clause. “Soundness” of integrated realization, strict lineage, and withdrawal autonomy is not established: the three `valid` predicates are unconstrained and may be `True`, and none is tied to `EightClauseIntegratedPackage`, an atomic corridor chain, or `ExactAutonomyCertificate`. **Nonemptiness:** none; no `TemporalFIACHCertificate` instance. **Registry drift:** none; `:8` is exact. **Repair:** split the field-projection interface from a substantive soundness row whose typed certificate lanes imply the actual package, corridor, and autonomy predicates; retain the former only at a certificate-interface ceiling. Size **L**.

## TTH-07 — Full temporal handoff composition

**Verdict: WEAKER.** **Registry text:** “Two valid Temporal-FIACH handoffs compose when their package maps factor through the same intermediate package and their corridor, route-memory, ownership, and autonomy interfaces agree.” Ceiling: structural precursor only.

**Lean quotation and unfolding.** `lean/CSTTT/Targets/Composition.lean:62–76` yields `Nonempty (FullHandoffCertificate (composeFullHandoffData left right))` from two certificates, `interface : FullHandoffCompatible left right`, and outer endpoint distinctness. But `composeFullHandoffData` only joins arbitrary `realized` and `lineage` propositions, retains `right.autonomous`, and computes route status (`:46–59`); the proof never uses `interface`. `FullHandoffCompatible` is only intermediate carrier/package/frontier/owner equalities plus a route-status disjunction (`:31–39`). The other two registered theorems project composed lane proofs (`:79–86`) and compute `.routeIndexed` from a nonflat component (`:89–98`).

**Gap.** Interface agreement is not a necessary input to the constructed result; package **maps** do not exist in `FullHandoffData`; no atomic corridor composition, route-memory transfer, or autonomy composition is proved. The arbitrary `realized`/`lineage` fields can stand for unrelated propositions. **Nonemptiness:** none; no `FullHandoffCertificate` instance. **Registry drift:** all three pointers `:62`, `:79`, `:89` match. **Repair:** strengthen Lean with typed two-hop Temporal-FIACH certificates and composable package maps, corridor chain, route residue, owner, and autonomy interfaces, making the compatibility proof necessary for the outer certificate. Size **L**.

## TTH-08 — Relation-valued temporal fission

**Verdict: WEAKER.** **Registry text:** “A symmetric valid fork is relation-valued: one source may stand in the structural continuation relation to two swap-related autonomous targets, without an invariant singleton selector.” Ceiling: no unique identity conclusion.

**Lean quotation and unfolding.** `lean/CSTTT/Corridor/Fission.lean:27–32` returns `d.related d.source d.left ∧ d.related d.source d.right`; `targetSwapPreservesFissionValidity` returns `d.valid (d.swap d.left) ∧ d.valid (d.swap d.right)` (`:35–41`); `targetSwapSymmetryNonselection` returns only `d.swap d.left ≠ d.left ∧ d.swap d.right ≠ d.right` (`:44–53`). `TemporalFissionCertificate` already stores both relation and validity proofs and the two swap equations (`:14–24`).

**Gap.** `related` and `valid` are arbitrary predicates; neither is tied to strict Temporal-FIACH or target autonomy. The last theorem rules out a fixed point at the two chosen targets, but does not quantify over or exclude an invariant singleton selector on the claimed continuation set. **Nonemptiness:** none; no positive fission certificate in Lean. **Registry drift:** all three pointers `:27`, `:35`, `:44` match. **Repair:** strengthen Lean with two actual handoff/autonomy certificates and a formally defined invariant selector on the swap-invariant target set; prove its impossibility under distinctness. Size **L**.

## TTH-09 — Route-independent endpoint under flatness

**Verdict: WEAKER.** **Registry text:** “Two admissible routes with the same boundary have the same temporal endpoint only under an explicit flatness, normalization, or confluence certificate.” Ceiling: route independence only under premises.

**Lean quotation and unfolding.** `lean/CSTTT/Transport/RouteDiscipline.lean:121–135` proves `c.endpoint r₁ = c.endpoint r₂` from `c : NormalizationCertificate ...` and `c.boundary r₁ = c.boundary r₂`. The certificate supplies `normalizeByBoundary : ∀ r, normalize r = canonicalNormal (boundary r)` and `endpointFactors : ∀ r, endpoint r = endpointOfNormal (normalize r)` (`:108–116`). The other registered theorem only returns `d.outputStatus = .flat` from supplied `flatnessCertified`, `commonNormalForm`, and `zeroClockHolonomy` and `cert.outputCorrect` (`lean/CSTTT/Targets/RouteCompletion.lean:17–24`, `:45–53`).

**Gap.** One sufficient **normalization** route is proved for all routes; no admissibility predicate, flatness-only or confluence certificate implies endpoint equality here. The flat-status theorem is a certificate-field projection, not an endpoint theorem. A necessity converse would be false in general: equal endpoints can coincide accidentally without a flatness certificate. **Nonemptiness:** `diamondCertificate` (`lean/CSTTT/Transport/FiniteExamples.lean:128–138`) satisfies normalization and is used at `:140–143`; its endpoint is constant `.joined`, so this instance alone does not test a nontrivial route comparison. **Registry drift:** the two pointers are swapped: normalization is actually `RouteDiscipline.lean:121`; flat status is `RouteCompletion.lean:45`. **Repair:** split the claim into three sufficient licenses: normalization, flatness, and confluence certificates each imply equal endpoints for admissible routes with the same boundary. Retain the existing normalization theorem; specify admissibility and prove the other two implications. If “only under” is meant as a literal converse, revise the row text instead, since that converse fails. **Recommended wording:** “Two admissible routes with the same boundary have equal temporal endpoints when licensed by an explicit normalization, flatness, or confluence certificate.” Size **M**.

## TTH-10 — Monotone record descent transports an arrow

**Verdict: PROJECTION.** **Registry text:** “A record map that preserves every declared strict source-record step preserves the endogenous target arrow; weak monotonicity that collapses strict steps is insufficient.” Ceiling: structural arrow audit only.

**Lean quotation and unfolding.** `lean/CSTTT/Transport/RecordArrow.lean:16–23` takes `hmono : StrictlyMonotoneOn sourceLt targetLt mapRecord` and concludes `∀ a b, sourceLt a b → targetLt (mapRecord a) (mapRecord b)` by `exact hmono`. The definition is literally that same universal implication (`:7–12`).

**Gap.** The positive theorem is a direct restatement of its premise for arbitrary relations; it does not derive an endogenous target arrow from transported records. No theorem or finite counterexample shows weak monotonicity can collapse a strict step. **Nonemptiness:** none; no `StrictlyMonotoneOn` instance with a declared strict source step and target arrow is constructed in Lean. **Registry drift:** none; `:16` is exact. **Repair:** split positive strict-step transport from the weak-monotonicity countermodel; define a genuine target record-arrow predicate and instantiate both on finite records. Size **M**.

## TTD-01 — Direct-successor temporal validity

**Verdict: WEAKER.** **Registry text:** “An immediate direct temporal successor is valid only when one necessary source event generates one target event with complete temporal payload, no storage/replay mediator, no alternative parent, and correct route and ownership transfer.” Ceiling: separate broader criterion.

**Lean quotation and unfolding.** `lean/CSTTT/Corridor/FiniteDirectSuccessor.lean:50–60` concludes `d.immediateEdge ∧ d.payloadComplete ∧ d.payloadHashBound ∧ d.edgeNecessary ∧ d.predictiveStep ∧ d.orderStep ∧ d.tickStep ∧ d.progressStep ∧ d.recordStep ∧ d.routeDisciplined ∧ d.ownershipTransferred`. These are `Prop` fields of `AtomicDirectSuccessorData` (`:7–24`), and every corresponding proof comes from `AtomicDirectSuccessorCertificate` (`:27–43`). The same row also lists `directSuccessorPathComposition`, which concatenates `everyAtomicEdgeValid` and `noRealizedGap` propositions from path certificates (`:75–91`, `:100–125`).

**Gap.** The theorem projects an input certificate; no source/target event, generative edge relation, or complete payload object is modeled. `notStorageMediated`, `notReplayableArchive`, and `noAlternativeTemporalParent` are stored in the certificate but omitted from `directSuccessorValidity`'s conclusion. Path composition is a separate summary statement, not immediate atomic validity. **Nonemptiness:** none; no `AtomicDirectSuccessorCertificate` or path certificate instance in Lean. **Registry drift:** its two pointers are swapped: validity is `:50`, path composition `:112`. **Repair:** strengthen Lean with typed source/target event data and a generative edge, include the negative mediator/parent conditions in validity, and separately prove path composition. Size **L**.

## TTD-02 — Overlap/direct-successor relation

**Verdict: PROJECTION.** **Registry text:** “Strict overlap continuity and direct temporal successorship are incomparable: exact witnesses exist for each class outside the other, while both embed in a separately named generalized path relation.” Ceiling: no silent broadening.

**Lean quotation and unfolding.** `lean/CSTTT/Strengthening/ContinuityClass.lean:43–49` accepts `overlapOnly : ∃ m, overlap m ∧ ¬ direct m` and `directOnly : ∃ m, direct m ∧ ¬ overlap m`, then returns `EvidenceModesIncomparable overlap direct`, defined as the conjunction of exactly those two existentials (`:35–39`). `generalizedStrictlyBroaderThanOverlap` takes `directOnly` again and proves the disjunctive class is strictly broader (`:62–73`), where `GeneralizedTemporalContinuity ... m := overlap m ∨ direct m` (`:9–13`).

**Gap.** No overlap-only or direct-only witness is built; `overlap` and `direct` are arbitrary predicates, not the finite corridor and direct-successor criteria. The listed declarations do not construct the claimed exact witnesses or embed either mode into a certificate-backed generalized *path*. **Nonemptiness:** none; no concrete predicates/witnesses instantiate the theorem in Lean. **Registry drift:** both pointers `:43`, `:62` match. **Repair:** strengthen Lean with concrete finite overlap-only and direct-only models and typed embeddings into the generalized path certificates; retain the generic logical lemma as a helper. Size **M**.

## TTD-03 — Direct-successor detached-copy exclusion

**Verdict: WEAKER.** **Registry text:** “The frozen direct-successor criterion excludes detached copies, archival replay, storage-mediated reconstruction, temporal gaps, and arbitrary data reachability.” Ceiling: provenance boundary.

**Lean quotation and unfolding.** `lean/CSTTT/Corridor/FiniteDirectSuccessor.lean:63–72` proves `¬ DetachedOperationalPattern d` from `c : AtomicDirectSuccessorCertificate d`. The pattern unfolds to `d.storageMediated ∨ d.replayableArchive ∨ ¬ d.edgeNecessary ∨ ¬ d.immediateEdge` (`:45–47`); the certificate stores negations of the first two and proofs of necessity/immediacy (`:27–43`).

**Gap.** The theorem excludes only those four Boolean-like propositions. There is no detached-copy predicate, temporal-gap condition, or arbitrary-data-reachability relation in the pattern; `noAlternativeTemporalParent` is not used. Moreover all exclusions are directly stored in `c`. **Nonemptiness:** none; no positive direct-successor certificate in Lean. **Registry drift:** none; `:63` is exact. **Repair:** strengthen Lean by defining the missing operational patterns using event provenance, time, and reachability, then show an actual direct-successor certificate rules each out. Size **M**.

## TTS-01 — Generalized temporal-continuity path class

**Verdict: WEAKER.** **Registry text:** “Strict-overlap and direct-successor legs each embed into a generalized structural-continuity path class, and compatible mixed-mode legs compose there without broadening strict Temporal-FIACH.” Ceiling: broader structural lineage vocabulary only; strict FIACH unchanged.

**Lean quotation and unfolding.** `lean/CSTTT/Strengthening/ContinuityClass.lean:16–31` embeds arbitrary `overlap m` and `direct m` into `GeneralizedTemporalContinuity overlap direct m`, defined as `overlap m ∨ direct m` (`:9–13`). `generalizedStrictlyBroaderThanOverlap` assumes a `directOnly` witness (`:62–73`). `generalizedPathComposition` returns `Nonempty (GeneralizedPathCertificate (composeGeneralizedPath left right))` from two certificates, `frontier`, and outer distinctness (`:122–139`). The data contains only `modes : List ContinuityLegKind` and arbitrary `everyLegValid`, `noTemporalGap`, `exactFrontiers` propositions (`:82–99`); composition concatenates modes and conjoins flags (`:109–119`).

**Gap.** There is no dependent association between each leg mode and an actual overlap/direct certificate, so “mixed-mode legs” may be labels alone. The strict-broadening result assumes, rather than constructs, a direct-only witness. No formal theorem connects the generalized class to the strict `TemporalFIACH` lineage definition. **Nonemptiness:** none; no positive generalized path certificate in Lean. **Registry drift:** all four pointers are permuted. Actual locations in declaration order are `:16`, `:25`, `:62`, `:122`; registry gives `:122`, `:16`, `:25`, `:62`. **Repair:** strengthen Lean with a typed list of certified legs, per-mode validity, and compatibility at each frontier; prove embeddings and composition and explicitly state that strict FIACH retains its corridor field. Size **L**.

## TTS-02 — Exact vector-valued defect acceptance

**Verdict: WEAKER.** **Registry text:** “Acceptance under the exact defect semantics is componentwise: every hard-gate defect is zero and every soft defect lies below its own rational tolerance; acceptance is downward closed and not determined by a scalar summary.” Ceiling: finite exact componentwise defect semantics only.

**Lean quotation and unfolding.** `lean/CSTTT/Robustness/DefectVector.lean:6–21` defines `defect : Nat`, `tolerance : Nat`, `ComponentAccepts c := if c.hard then c.defect = 0 else c.defect ≤ c.tolerance`, and `VectorAccepts v := ∀ c ∈ v, ComponentAccepts c`. `acceptedHardGateIsZero` extracts hard-gate zero (`:24–33`); `vectorAcceptanceDownwardClosed` uses `NoWorse` with matching gate types and tolerances and smaller defects (`:37–43`, `:69–86`). `scalarSummaryDoesNotDetermineAcceptance` merely repackages supplied `sameScalar`, `hAccepted`, and `hRejected` witnesses for an *arbitrary* `Profile`, scalar, and acceptance predicate (`:90–99`).

**Gap.** `Nat` tolerances are narrower than the claimed rational tolerances. The scalar limitation is not proved for `DefectVector` or a declared scalar summary; the counterexample is an input premise. Empty vectors are accepted definitionally, so a positive acceptance witness must be nonempty to be informative. **Nonemptiness:** none for a nonempty accepted hard/soft defect vector or equal-scalar contrasting pair in Lean. **Registry drift:** all three lines shifted by +2 after L1 imports: actual `:24`, `:69`, `:90`, not `:22`, `:67`, `:88`. **Repair:** strengthen Lean with exact rational defects/tolerances, a named scalar summary, nonempty example vectors with equal summary and opposed verdicts, and the corresponding componentwise theorems. Size **M**.

## TTS-03 — Hard-gate-preserving bounded temporal robustness

**Verdict: WEAKER.** **Registry text:** “Every perturbation inside the declared exact componentwise margin preserves positive predictive, order, tick, progress, and record advances while leaving every hard gate satisfied.” Ceiling: declared exact finite perturbation box only.

**Lean quotation and unfolding.** `lean/CSTTT/Robustness/TemporalMargins.lean:6–15` supplies one signed `TemporalMargin` with `certifiedWorstCase : minimumIncrement + radius ≤ baseIncrement` and `WithinRadius m delta := -m.radius ≤ delta ∧ delta ≤ m.radius`. `boundedPerturbationPreservesMargin` concludes only `m.minimumIncrement ≤ m.baseIncrement + delta` (`:18–25`). `failedHardGateCannotBeAveragedAway` says `¬ g.integratedPackage → ¬ Nonempty (HardGateCertificate g)` (`:45–51`); a gate certificate stores six independent proof fields (`:28–42`). `MarginVectorAccepts` is only a definition of pointwise acceptance for two lists (`:54–61`).

**Gap.** There is no premise `0 < minimumIncrement`, so positive advance is not established. No component-indexed theorem covers predictive, order, tick, progress, and record together; the list predicate is not derived for every box perturbation. Only the integrated-package hard gate is addressed, not preservation of every gate. **Nonemptiness:** none; no concrete margin vector and hard-gate certificate in Lean. **Registry drift:** first pointer `:18` matches; second is stale by one line (`:44` vs actual `:45`). **Repair:** strengthen Lean with five named positive margins, componentwise perturbation bounds, and a hard-gate bundle preserved by construction; prove the vector theorem and instantiate a nonempty finite box. Size **L**.

## TTS-04 — Model-relative unbounded controlled invariant

**Verdict: WEAKER.** **Registry text:** “A total target-owned policy on the exact finite controlled invariant defines a model-relative infinite run that preserves package integrity, progress, record advancement, ownership, and solvency for every admissible disturbance stream.” Ceiling: infinite run inside the exact finite controlled model; no physical persistence theorem.

**Lean quotation and unfolding.** `lean/CSTTT/Autonomy/UnboundedInvariant.lean:27–32` recursively defines `policyState` for every `Nat` and supplied disturbance stream. `modelRelativeUnboundedControlledInvariant` proves for each `n` package validity, target action ownership, step, `d.antiStall`, and `d.budgetSolvent` (`:50–83`) by using `policyStateInside` (`:36–45`), `cert.packageInside`, and the corresponding `ExactAutonomyPolicy` fields (`:7–24`). `ExactAutonomyData` declares `antiStall` and `budgetSolvent` as arbitrary transition predicates (`lean/CSTTT/Autonomy/FiniteAutonomy.lean:6–15`).

**Gap.** The model-relative infinite recursion and universal disturbance quantifier are real. But neither anti-stall nor solvency is connected to numeric progress, record advancement, or resource budgets; they may be arbitrary/constant predicates. The theorem does not assert an explicit state sequence with temporal signatures beyond `policyState`, and no admissibility restriction on streams is modeled (it proves all streams, which is stronger only on that axis). **Nonemptiness:** none; no `ExactAutonomyPolicy` or matching autonomy certificate instance in Lean. **Registry drift:** none; `:50` is exact. **Repair:** strengthen Lean with substantive progress/record/budget fields or transition inequalities in the finite system and a concrete total policy; then prove the same `∀ n` theorem with those fields. Size **L**.

## Summary

| Verdict | Rows | Count |
|---|---|---:|
| FAITHFUL | TTH-01, TTH-05 | 2 |
| STRONGER | — | 0 |
| WEAKER | TTH-04, TTH-07, TTH-08, TTH-09, TTD-01, TTD-03, TTS-01, TTS-02, TTS-03, TTS-04 | 10 |
| PROJECTION | TTH-02, TTH-03, TTH-06, TTH-10, TTD-02 | 5 |
| VACUOUS | — | 0 |
| DIVERGENT | — | 0 |
| MISSING | — | 0 |

No row is marked VACUOUS solely because a caller *could* choose an arbitrary predicate as `True`; that defect is captured as PROJECTION/WEAKER where substantive predicates are unconstrained. No concrete positive certificate instance was located for 16 rows; TTH-09 has only the constant-endpoint diamond instance. These findings keep theorem compilation separate from satisfaction of the registry claims.

### Proposed fix-packet order

The order below is a topological order of the registry's `dependencies` column, not an assertion that every predecessor needs a statement repair. External TTN rows are upstream gates for these packets; their own dependency chain is `TTN-03 → TTN-04 → TTN-05`. Resolve the required external rows `TTN-01`, `TTN-03`, `TTN-04`, `TTN-05`, `TTN-10`, `TTN-11`, and `TTN-12` first, in that chain order where applicable. In particular, TTN-04's route discipline precedes TTH-04 corridor composition and TTN-05 precedes TTH-09.

| Row | Registry prerequisite edges used |
|---|---|
| TTH-01 | none |
| TTH-02 | TTH-01 → TTH-02 |
| TTH-03 | none |
| TTH-04 | TTH-03 → TTH-04; TTN-04 → TTH-04 |
| TTH-05 | TTH-02 → TTH-05 |
| TTH-06 | TTH-02 → TTH-06; TTH-04 → TTH-06; TTH-05 → TTH-06 |
| TTH-07 | TTH-04 → TTH-07; TTH-05 → TTH-07; TTH-06 → TTH-07; TTH-09 → TTH-07 |
| TTH-08 | TTH-04 → TTH-08; TTN-11 → TTH-08 |
| TTH-09 | TTN-04 → TTH-09; TTN-05 → TTH-09 |
| TTH-10 | TTH-03 → TTH-10; TTN-03 → TTH-10 |
| TTD-01 | TTH-03 → TTD-01 |
| TTD-02 | TTH-04 → TTD-02; TTD-01 → TTD-02 |
| TTD-03 | TTD-01 → TTD-03; TTN-01 → TTD-03 |
| TTS-01 | TTH-04 → TTS-01; TTD-01 → TTS-01; TTD-02 → TTS-01 |
| TTS-02 | TTN-10 → TTS-02 |
| TTS-03 | TTH-06 → TTS-03; TTS-02 → TTS-03 |
| TTS-04 | TTH-05 → TTS-04; TTN-12 → TTS-04 |

1. **Roots and package:** TTH-01 (already FAITHFUL; optional acceptance follow-up), TTH-02, TTH-03, TTS-02 (after TTN-10).
2. **First dependents:** TTH-05 (already FAITHFUL; instance check), TTH-04 (after TTN-04), TTH-10 (after TTN-03), TTD-01, TTH-09 (after TTN-04 and TTN-05).
3. **Certificates and relations:** TTD-03 (after TTN-01), TTD-02, TTH-06, TTH-08 (after TTN-11), TTS-04 (after TTN-12).
4. **Composite claims:** TTH-07 (after TTH-09), TTS-01, TTS-03.
