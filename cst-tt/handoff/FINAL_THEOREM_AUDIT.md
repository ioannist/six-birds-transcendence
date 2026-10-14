# Final theorem and boundary audit

This table is the normative CST-TT-08 status surface. The only permitted status values are `proved`, `checked finite countermodel`, `conditional`, `killed`, and `open`.

No row is marked `proved` in this execution because the pinned Lean toolchain was not available. Constructive proof sources are therefore `conditional`; exact negative witnesses remain `checked finite countermodel`.

## Status summary

| Status | Count |
|---|---|
| checked finite countermodel | 12 |
| conditional | 19 |
| open | 8 |

## common

### TTN-01 — Detached-copy insufficiency

**Status:** `checked finite countermodel`  
**Statement:** There exists an exact finite detached reconstruction with endpoint equality, target package realization, and target autonomy but no strict overlap temporal corridor.  
**Dependencies:** `none`  
**Assumptions:** `AS-01;AS-02;AS-18;AS-19`  
**Formal declarations:** `CSTTT.Prospects.DetachedCopyCountermodel;CSTTT.CorridorTheory.noMixedStageExcludesAtomicCorridor`  
**Evidence:** `formal/certificates/corridors/COR-POS-01.certificate.json;formal/certificates/corridors/COR-POS-02-COMPOSED.certificate.json;formal/certificates/corridors/COR-POS-02A.certificate.json;formal/certificates/corridors/COR-POS-02B.certificate.json;formal/certificates/countermodels/CM-01.certificate.json;formal/certificates/countermodels/CM-02.certificate.json`  
**Claim ceiling:** exact finite boundary
### TTN-02 — Public-shadow insufficiency

**Status:** `checked finite countermodel`  
**Statement:** There exist exact finite systems with identical public observations and different hidden consciousness-relevant structural predicates.  
**Dependencies:** `none`  
**Assumptions:** `AS-01`  
**Formal declarations:** `CSTTT.Prospects.PublicShadowCountermodel`  
**Evidence:** `formal/certificates/countermodels/CM-09.certificate.json`  
**Claim ceiling:** finite-interface nonidentifiability
### TTN-03 — Holonomy is not an endogenous arrow

**Status:** `checked finite countermodel`  
**Statement:** There exists an exact finite route system with nontrivial holonomy and no endogenous temporal arrow.  
**Dependencies:** `none`  
**Assumptions:** `AS-01;AS-08;AS-09`  
**Formal declarations:** `CSTTT.Prospects.HolonomyWithoutArrowCountermodel`  
**Evidence:** `formal/certificates/countermodels/CM-03.certificate.json`  
**Claim ceiling:** exact finite boundary
### TTN-04 — Memory-or-flatness boundary

**Status:** `conditional`  
**Statement:** When two histories are current-equal but predictively unequal, a current-only predictor cannot represent both; the licensed repairs are retained route memory or a proof of flatness.  
**Dependencies:** `TTN-03`  
**Assumptions:** `AS-01;AS-04;AS-09;AS-12`  
**Formal declarations:** `CSTTT.RouteTheory.noCurrentOnlyPredictor;CSTTT.RouteTheory.memoryOrFlatness`  
**Evidence:** `formal/certificates/countermodels/CM-06.certificate.json;formal/certificates/route_completion/ROUTE-COMP-FLAT-01.certificate.json;formal/certificates/route_completion/ROUTE-COMP-INDEXED-01.certificate.json;formal/certificates/transport/TR-POS-01.certificate.json`  
**Claim ceiling:** route discipline only
### TTN-05 — No canonical global now under translation holonomy

**Status:** `conditional`  
**Statement:** There exists an exact finite clock-translation loop with nonzero holonomy, so no route-independent global present factors through the shared boundary alone.  
**Dependencies:** `TTN-04`  
**Assumptions:** `AS-01;AS-09;AS-10`  
**Formal declarations:** `CSTTT.RouteTheory.noCanonicalGlobalNowOfTranslationHolonomy`  
**Evidence:** `formal/certificates/countermodels/CM-07.certificate.json;formal/certificates/route_completion/ROUTE-COMP-FLAT-01.certificate.json;formal/certificates/route_completion/ROUTE-COMP-INDEXED-01.certificate.json`  
**Claim ceiling:** route-indexed time only
### TTN-06 — Essential external support defeats autonomy

**Status:** `checked finite countermodel`  
**Statement:** There exists an exact finite target whose runtime behavior is maintained by an essential withdrawn resource and therefore fails post-withdrawal autonomy.  
**Dependencies:** `TTH-05`  
**Assumptions:** `AS-01;AS-20;AS-21;AS-22`  
**Formal declarations:** `CSTTT.AutonomyTheory.removedEssentialResourceExcludesAutonomy`  
**Evidence:** `formal/certificates/autonomy/AUT-POS-01.certificate.json;formal/certificates/countermodels/CM-04.certificate.json`  
**Claim ceiling:** model-relative autonomy boundary
### TTN-07 — Stable tick phase without progress

**Status:** `checked finite countermodel`  
**Statement:** There exists an exact finite clock whose phase is stable while genuine temporal progress is absent.  
**Dependencies:** `none`  
**Assumptions:** `AS-01;AS-06;AS-07`  
**Formal declarations:** `CSTTT.Prospects.StableTickWithoutProgress`  
**Evidence:** `formal/certificates/autonomy/AUT-POS-01.certificate.json;formal/certificates/countermodels/CM-05.certificate.json`  
**Claim ceiling:** temporal closure boundary
### TTN-08 — Local-global package obstruction

**Status:** `checked finite countermodel`  
**Statement:** There exists an exact finite family of locally accepted clause witnesses that admits no coherent global package witness.  
**Dependencies:** `none`  
**Assumptions:** `AS-01;AS-15`  
**Formal declarations:** `CSTTT.Prospects.LocalGlobalObstruction`  
**Evidence:** `formal/certificates/countermodels/CM-08.certificate.json`  
**Claim ceiling:** global package boundary
### TTN-09 — Temporal gap versus resumed stream

**Status:** `checked finite countermodel`  
**Statement:** There exists an exact finite episode with equivalent endpoints and a realized-time gap; it is a resumed stream rather than a strict no-gap corridor.  
**Dependencies:** `TTN-01`  
**Assumptions:** `AS-01;AS-19`  
**Formal declarations:** `CSTTT.Prospects.GapResumeCountermodel;CSTTT.CorridorTheory.realizedGapExcludesAtomicCorridor`  
**Evidence:** `formal/certificates/corridors/COR-POS-01.certificate.json;formal/certificates/corridors/COR-POS-02-COMPOSED.certificate.json;formal/certificates/corridors/COR-POS-02A.certificate.json;formal/certificates/corridors/COR-POS-02B.certificate.json;formal/certificates/countermodels/CM-12.certificate.json`  
**Claim ceiling:** strict no-gap criterion only
### TTN-10 — Scalar residual hides hard-gate failure

**Status:** `checked finite countermodel`  
**Statement:** There exists an exact finite defect profile with a small scalar mean and a failed nonnegotiable hard gate; scalar aggregation does not determine acceptance.  
**Dependencies:** `none`  
**Assumptions:** `AS-01;AS-16`  
**Formal declarations:** `CSTTT.Prospects.ScalarResidualHardGateFailure;CSTTT.DefectTheory.acceptedHardGateIsZero;CSTTT.DefectTheory.scalarSummaryDoesNotDetermineAcceptance`  
**Evidence:** `formal/certificates/countermodels/CM-10.certificate.json;formal/certificates/strengthenings/defects/DEF-EQUAL-SCALAR-01.certificate.json;formal/certificates/strengthenings/defects/DEF-POS-01.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C01.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C02.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C03.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C04.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C05.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C06.certificate.json;formal/certificates/strengthenings/robustness/ROB-POS-01.certificate.json`  
**Claim ceiling:** hard gates cannot be averaged
### TTN-11 — Exact symmetry supplies no invariant unique continuer

**Status:** `checked finite countermodel`  
**Statement:** There exists an exact symmetric two-target fork for which swap symmetry preserves validity and no invariant unique continuer can be selected.  
**Dependencies:** `none`  
**Assumptions:** `AS-01`  
**Formal declarations:** `CSTTT.CorridorTheory.targetSwapSymmetryNonselection`  
**Evidence:** `formal/certificates/countermodels/CM-11.certificate.json;formal/certificates/fission/FISSION-POS-01.certificate.json`  
**Claim ceiling:** no unique identity conclusion
### TTN-12 — Finite success does not imply unbounded liveness

**Status:** `checked finite countermodel`  
**Statement:** For every tested finite horizon there is an exact countdown system that succeeds through that horizon and fails immediately afterward; finite success alone does not imply unbounded liveness.  
**Dependencies:** `none`  
**Assumptions:** `AS-01;AS-20;AS-21;AS-22;AS-34`  
**Formal declarations:** `CSTTT.Prospects.FiniteTraceNotUnboundedLiveness;CSTTT.AutonomyTheory.arbitrarilyLongFinitePrefixStillInsufficient`  
**Evidence:** `formal/certificates/autonomy/AUT-POS-01.certificate.json;formal/certificates/countermodels/CM-13.certificate.json;formal/certificates/strengthenings/unbounded/UNB-POS-01.certificate.json`  
**Claim ceiling:** finite-horizon claim ceiling
### TTN-13 — Same-carrier re-encoding is not cross-carrier transport

**Status:** `checked finite countermodel`  
**Statement:** A nonidentity re-encoding on one fixed carrier does not satisfy the distinct-carrier condition required for cross-carrier transport.  
**Dependencies:** `none`  
**Assumptions:** `AS-01;AS-02`  
**Formal declarations:** `CSTTT.Prospects.SameCarrierReencodingNotCrossCarrier`  
**Evidence:** `formal/certificates/countermodels/CM-14.certificate.json`  
**Claim ceiling:** typing boundary
### TTN-14 — Branchwise preservation need not preserve recombination

**Status:** `checked finite countermodel`  
**Statement:** There exist exact finite joint structures with identical branchwise marginals and different recombination structure; branchwise preservation does not imply integrated binding.  
**Dependencies:** `none`  
**Assumptions:** `AS-01;AS-15;AS-16`  
**Formal declarations:** `CSTTT.PackageTheory.fusionLineageDoesNotImplyIntegratedPackage;CSTTT.PackageTheory.fusionBranchwiseDoesNotRepairRecombination`  
**Evidence:** `formal/certificates/countermodels/CM-15.certificate.json;formal/certificates/fusion/FUSION-BOUNDARY-01.certificate.json`  
**Claim ceiling:** joint-structure boundary

## direct-successor

### TTD-01 — Direct-successor temporal validity

**Status:** `conditional`  
**Statement:** An immediate direct temporal successor is valid only when one necessary source event generates one target event with complete temporal payload, no storage/replay mediator, no alternative parent, and correct route and ownership transfer.  
**Dependencies:** `TTH-03`  
**Assumptions:** `AS-01;AS-02;AS-23`  
**Formal declarations:** `CSTTT.DirectSuccessorTheory.directSuccessorValidity;CSTTT.DirectSuccessorTheory.directSuccessorPathComposition`  
**Evidence:** `formal/certificates/direct_successor/DS-POS-01.certificate.json;formal/certificates/direct_successor/DS-POS-02A.certificate.json;formal/certificates/direct_successor/DS-POS-02B.certificate.json;formal/certificates/strengthenings/direct/DS-POS-03-MIXED-MODE.certificate.json`  
**Claim ceiling:** separate broader criterion
### TTD-02 — Overlap/direct-successor relation

**Status:** `conditional`  
**Statement:** Strict overlap continuity and direct temporal successorship are incomparable: exact witnesses exist for each class outside the other, while both embed in a separately named generalized path relation.  
**Dependencies:** `TTH-04;TTD-01`  
**Assumptions:** `AS-01;AS-18;AS-19;AS-23`  
**Formal declarations:** `CSTTT.StrengtheningTheory.overlapDirectIncomparable;CSTTT.StrengtheningTheory.generalizedStrictlyBroaderThanOverlap`  
**Evidence:** `formal/certificates/strengthenings/continuity/GCP-DIRECT-01.certificate.json;formal/certificates/strengthenings/continuity/GCP-MIXED-01.certificate.json;formal/certificates/strengthenings/continuity/GCP-OVERLAP-01.certificate.json;formal/certificates/strengthenings/continuity/ODR-01.certificate.json;formal/certificates/strengthenings/direct/DS-POS-03-MIXED-MODE.certificate.json`  
**Claim ceiling:** no silent broadening
### TTD-03 — Direct-successor detached-copy exclusion

**Status:** `conditional`  
**Statement:** The frozen direct-successor criterion excludes detached copies, archival replay, storage-mediated reconstruction, temporal gaps, and arbitrary data reachability.  
**Dependencies:** `TTD-01;TTN-01`  
**Assumptions:** `AS-01;AS-02;AS-23`  
**Formal declarations:** `CSTTT.DirectSuccessorTheory.directSuccessorDetachedCopyExclusion`  
**Evidence:** `formal/certificates/direct_successor/DS-POS-01.certificate.json;formal/certificates/direct_successor/DS-POS-02A.certificate.json;formal/certificates/direct_successor/DS-POS-02B.certificate.json`  
**Claim ceiling:** provenance boundary

## fallback

### TTF-01 — Predictive bridge descent

**Status:** `open`  
**Statement:** Open fallback target: prove that a predictive bridge descends through the declared source and target predictive equivalences.  
**Dependencies:** `TTH-03`  
**Assumptions:** `AS-01;AS-04;AS-24`  
**Formal declarations:** `CSTTT.Prospects.PredictiveBridgeDescent`  
**Evidence:** `none`  
**Claim ceiling:** fallback transport only
### TTF-02 — Least operational ancestry

**Status:** `open`  
**Statement:** Open fallback target: construct the least no-ex-nihilo operational ancestry relation generated by admissible provenance seeds.  
**Dependencies:** `TTF-01`  
**Assumptions:** `AS-01;AS-24;AS-25`  
**Formal declarations:** `CSTTT.Prospects.LeastOperationalAncestry`  
**Evidence:** `none`  
**Claim ceiling:** relation-valued successorship only
### TTF-03 — Independent-twin exclusion

**Status:** `open`  
**Statement:** Open fallback target: prove that an independently constructed but structurally equivalent twin is excluded by no-ex-nihilo ancestry.  
**Dependencies:** `TTF-02`  
**Assumptions:** `AS-01;AS-24;AS-25`  
**Formal declarations:** `CSTTT.Prospects.IndependentTwinExclusion`  
**Evidence:** `none`  
**Claim ceiling:** no-ex-nihilo boundary
### TTF-04 — Fallback fission, fusion, and empty targets

**Status:** `open`  
**Statement:** Open fallback target: characterize relation-valued fission, guarded fusion, and empty targets under least operational ancestry.  
**Dependencies:** `TTF-02;TTN-14`  
**Assumptions:** `AS-01;AS-24;AS-25`  
**Formal declarations:** `CSTTT.Prospects.FallbackFissionFusionEmpty`  
**Evidence:** `none`  
**Claim ceiling:** relation-valued only
### TTF-05 — Integrated Temporal-IAPS certificate

**Status:** `open`  
**Statement:** Open fallback target: combine predictive ancestry, integrated target package realization, and autonomy into a Temporal-IAPS certificate.  
**Dependencies:** `TTH-02;TTH-05;TTF-02`  
**Assumptions:** `AS-01;AS-14;AS-20;AS-24;AS-25`  
**Formal declarations:** `CSTTT.Prospects.IntegratedTemporalIAPS`  
**Evidence:** `none`  
**Claim ceiling:** structural successorship only
### TTF-06 — Destructive reconstruction versus independent twin

**Status:** `open`  
**Statement:** Open fallback target: separate source-derived destructive reconstruction from an independently constructed structural twin.  
**Dependencies:** `TTF-02;TTF-03`  
**Assumptions:** `AS-01;AS-24;AS-25`  
**Formal declarations:** `CSTTT.Prospects.DestructiveReconstructionTwinSeparation`  
**Evidence:** `none`  
**Claim ceiling:** structural successorship only
### TTF-07 — Ancestry supplies no unique numerical identity

**Status:** `open`  
**Statement:** Open fallback target: show that ancestry alone supplies no unique numerical-identity verdict under symmetric branching.  
**Dependencies:** `TTF-04;TTN-11`  
**Assumptions:** `AS-01;AS-24;AS-25`  
**Formal declarations:** `CSTTT.Prospects.AncestryNoUniqueIdentity`  
**Evidence:** `none`  
**Claim ceiling:** identity remains separately assumed
### TTF-08 — Predictive ancestry is package-insufficient

**Status:** `open`  
**Statement:** Open fallback target: show that predictive ancestry is insufficient for integrated target package realization.  
**Dependencies:** `TTF-02;TTN-08`  
**Assumptions:** `AS-01;AS-15;AS-24;AS-25`  
**Formal declarations:** `CSTTT.Prospects.PredictiveAncestryPackageInsufficient`  
**Evidence:** `none`  
**Claim ceiling:** independent package audit required

## primary

### TTH-01 — Acyclic local-witness gluing

**Status:** `conditional`  
**Statement:** For any finite rooted acyclic running-intersection cover, edge-compatible locally accepted witnesses whose hard gates all pass determine a global assignment restricting to every local witness.  
**Dependencies:** `none`  
**Assumptions:** `AS-01;AS-15;AS-16`  
**Formal declarations:** `CSTTT.PackageTheory.acyclicLocalWitnessGluing`  
**Evidence:** `formal/certificates/composition/packages/PKG-POS-05-COMP-SOURCE.certificate.json;formal/certificates/composition/packages/PKG-POS-06-COMP-MIDDLE.certificate.json;formal/certificates/composition/packages/PKG-POS-07-COMP-TARGET.certificate.json;formal/certificates/composition/staged/STG-COMP-A.certificate.json;formal/certificates/composition/staged/STG-COMP-B.certificate.json;formal/certificates/composition/staged/STG-COMP-OUTER.certificate.json;formal/certificates/fission/packages/PKG-FIS-LEFT.certificate.json;formal/certificates/fission/packages/PKG-FIS-RIGHT.certificate.json;formal/certificates/fission/packages/PKG-FIS-SOURCE.certificate.json;formal/certificates/fission/staged/STG-FIS-LEFT.certificate.json;formal/certificates/fission/staged/STG-FIS-RIGHT.certificate.json;formal/certificates/fusion/packages/PKG-FUS-CONTROL-VALID.certificate.json;formal/certificates/fusion/packages/PKG-FUS-NEG-01.certificate.json;formal/certificates/packages/PKG-POS-01-TARGET.certificate.json;formal/certificates/packages/PKG-POS-02-SOURCE.certificate.json;formal/certificates/packages/PKG-POS-03-FIACH-SOURCE.certificate.json;formal/certificates/packages/PKG-POS-04-FIACH-TARGET.certificate.json;formal/certificates/packages/STG-POS-01.certificate.json;formal/certificates/packages/STG-POS-02-FIACH.certificate.json`  
**Claim ceiling:** structural package only
### TTH-02 — Staged heterogeneous package assembly

**Status:** `conditional`  
**Statement:** Separately typed, total, value-preserving source-to-target clause maps plus an independently valid target gluing certificate assemble one integrated target package without using lineage or autonomy premises.  
**Dependencies:** `TTH-01`  
**Assumptions:** `AS-01;AS-14;AS-15;AS-16;AS-17`  
**Formal declarations:** `CSTTT.PackageTheory.stagedHeterogeneousPackageAssembly`  
**Evidence:** `formal/certificates/composition/fiach/FIACH-COMP-A.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-B.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-OUTER.certificate.json;formal/certificates/composition/packages/PKG-POS-05-COMP-SOURCE.certificate.json;formal/certificates/composition/packages/PKG-POS-06-COMP-MIDDLE.certificate.json;formal/certificates/composition/packages/PKG-POS-07-COMP-TARGET.certificate.json;formal/certificates/composition/staged/STG-COMP-A.certificate.json;formal/certificates/composition/staged/STG-COMP-B.certificate.json;formal/certificates/composition/staged/STG-COMP-OUTER.certificate.json;formal/certificates/fiach/FIACH-POS-01.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-LEFT.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-RIGHT.certificate.json;formal/certificates/fission/packages/PKG-FIS-LEFT.certificate.json;formal/certificates/fission/packages/PKG-FIS-RIGHT.certificate.json;formal/certificates/fission/packages/PKG-FIS-SOURCE.certificate.json;formal/certificates/fission/staged/STG-FIS-LEFT.certificate.json;formal/certificates/fission/staged/STG-FIS-RIGHT.certificate.json;formal/certificates/fusion/packages/PKG-FUS-CONTROL-VALID.certificate.json;formal/certificates/fusion/packages/PKG-FUS-NEG-01.certificate.json;formal/certificates/packages/PKG-POS-03-FIACH-SOURCE.certificate.json;formal/certificates/packages/PKG-POS-04-FIACH-TARGET.certificate.json;formal/certificates/packages/STG-POS-01.certificate.json;formal/certificates/packages/STG-POS-02-FIACH.certificate.json`  
**Claim ceiling:** structural package only
### TTH-03 — Bundled heterogeneous temporal transport

**Status:** `conditional`  
**Statement:** An admissible representative-independent heterogeneous bridge transports every component of the frozen temporal signature: predictive now, order, tick, progress, strict record arrow, route status, maintenance state, and target ownership.  
**Dependencies:** `none`  
**Assumptions:** `AS-01;AS-02;AS-04;AS-05;AS-06;AS-07;AS-08;AS-09;AS-10;AS-11`  
**Formal declarations:** `CSTTT.TransportTheory.bundledHeterogeneousTemporalTransport`  
**Evidence:** `formal/certificates/transport/TR-POS-01.certificate.json;formal/certificates/transport/TR-POS-02-FLAT.certificate.json`  
**Claim ceiling:** structural transport only
### TTH-04 — Strict temporal-corridor composition

**Status:** `conditional`  
**Statement:** Audited atomic overlap legs compose into a strict carrier-chain temporal corridor when consecutive legs agree exactly on the intermediate carrier, temporal frontier, route residue, and ownership interface.  
**Dependencies:** `TTH-03;TTN-04`  
**Assumptions:** `AS-01;AS-02;AS-18;AS-19`  
**Formal declarations:** `CSTTT.CorridorTheory.strictTemporalCorridorComposition;CSTTT.CorridorTheory.atomicTemporalCorridorCertificateSound`  
**Evidence:** `formal/certificates/composition/corridors/COR-POS-03-FULL-COMPOSITE.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-A.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-B.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-OUTER.certificate.json;formal/certificates/corridors/COR-POS-01.certificate.json;formal/certificates/corridors/COR-POS-02-COMPOSED.certificate.json;formal/certificates/corridors/COR-POS-02A.certificate.json;formal/certificates/corridors/COR-POS-02B.certificate.json;formal/certificates/fiach/FIACH-POS-01.certificate.json;formal/certificates/fission/corridors/COR-FIS-LEFT.certificate.json;formal/certificates/fission/corridors/COR-FIS-RIGHT.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-LEFT.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-RIGHT.certificate.json;formal/certificates/fusion/corridors/COR-FUS-LEFT.certificate.json;formal/certificates/fusion/corridors/COR-FUS-RIGHT.certificate.json`  
**Claim ceiling:** structural lineage criterion only
### TTH-05 — Post-withdrawal finite-horizon invariance

**Status:** `conditional`  
**Statement:** Within the declared finite model, a target-owned response law that keeps every disturbed state inside the controlled invariant yields post-withdrawal finite-horizon package preservation.  
**Dependencies:** `TTH-02`  
**Assumptions:** `AS-01;AS-17;AS-20;AS-21;AS-22`  
**Formal declarations:** `CSTTT.AutonomyTheory.postWithdrawalFiniteHorizonInvariance`  
**Evidence:** `formal/certificates/autonomy/AUT-POS-01.certificate.json;formal/certificates/composition/autonomy/AUT-COMP-A.certificate.json;formal/certificates/composition/autonomy/AUT-COMP-B.certificate.json;formal/certificates/composition/autonomy/AUT-COMP-OUTER.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-A.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-B.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-OUTER.certificate.json;formal/certificates/fiach/FIACH-POS-01.certificate.json;formal/certificates/fission/autonomy/AUT-FIS-LEFT.certificate.json;formal/certificates/fission/autonomy/AUT-FIS-RIGHT.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-LEFT.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-RIGHT.certificate.json`  
**Claim ceiling:** model-relative autonomy only
### TTH-06 — Temporal-FIACH certificate soundness

**Status:** `conditional`  
**Statement:** A valid Temporal-FIACH certificate entails, as separate fields, integrated target realization, strict temporal lineage, and post-withdrawal autonomy; none of the three is inferred from either of the others.  
**Dependencies:** `TTH-02;TTH-04;TTH-05`  
**Assumptions:** `AS-01;AS-02;AS-03;AS-14;AS-18;AS-19;AS-20;AS-21;AS-22`  
**Formal declarations:** `CSTTT.TargetTheory.temporalFIACHCertificateSoundness`  
**Evidence:** `formal/certificates/composition/fiach/FIACH-COMP-A.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-B.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-OUTER.certificate.json;formal/certificates/fiach/FIACH-POS-01.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-LEFT.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-RIGHT.certificate.json`  
**Claim ceiling:** structural precursor only
### TTH-07 — Full temporal handoff composition

**Status:** `conditional`  
**Statement:** Two valid Temporal-FIACH handoffs compose when their package maps factor through the same intermediate package and their corridor, route-memory, ownership, and autonomy interfaces agree.  
**Dependencies:** `TTH-04;TTH-05;TTH-06;TTH-09`  
**Assumptions:** `AS-01;AS-14;AS-15;AS-18;AS-19;AS-20;AS-22`  
**Formal declarations:** `CSTTT.TargetTheory.fullTemporalHandoffComposition;CSTTT.TargetTheory.composedHandoffPreservesIndependentLanes;CSTTT.TargetTheory.routeIndexedComponentPreventsAutomaticFlatness`  
**Evidence:** `formal/certificates/composition/FIACH-COMP-01.certificate.json;formal/certificates/composition/autonomy/AUT-COMP-A.certificate.json;formal/certificates/composition/autonomy/AUT-COMP-B.certificate.json;formal/certificates/composition/autonomy/AUT-COMP-OUTER.certificate.json;formal/certificates/composition/corridors/COR-POS-03-FULL-COMPOSITE.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-A.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-B.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-OUTER.certificate.json;formal/certificates/composition/staged/STG-COMP-A.certificate.json;formal/certificates/composition/staged/STG-COMP-B.certificate.json;formal/certificates/composition/staged/STG-COMP-OUTER.certificate.json;formal/certificates/fission/autonomy/AUT-FIS-LEFT.certificate.json;formal/certificates/fission/autonomy/AUT-FIS-RIGHT.certificate.json;formal/certificates/fission/corridors/COR-FIS-LEFT.certificate.json;formal/certificates/fission/corridors/COR-FIS-RIGHT.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-LEFT.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-RIGHT.certificate.json;formal/certificates/fission/staged/STG-FIS-LEFT.certificate.json;formal/certificates/fission/staged/STG-FIS-RIGHT.certificate.json;formal/certificates/fusion/corridors/COR-FUS-LEFT.certificate.json;formal/certificates/fusion/corridors/COR-FUS-RIGHT.certificate.json`  
**Claim ceiling:** structural precursor only
### TTH-08 — Relation-valued temporal fission

**Status:** `conditional`  
**Statement:** A symmetric valid fork is relation-valued: one source may stand in the structural continuation relation to two swap-related autonomous targets, without an invariant singleton selector.  
**Dependencies:** `TTH-04;TTN-11`  
**Assumptions:** `AS-01;AS-18;AS-19`  
**Formal declarations:** `CSTTT.CorridorTheory.relationValuedTemporalFission;CSTTT.CorridorTheory.targetSwapPreservesFissionValidity;CSTTT.CorridorTheory.targetSwapSymmetryNonselection`  
**Evidence:** `formal/certificates/composition/corridors/COR-POS-03-FULL-COMPOSITE.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-A.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-B.certificate.json;formal/certificates/composition/fiach/FIACH-COMP-OUTER.certificate.json;formal/certificates/fission/FISSION-POS-01.certificate.json;formal/certificates/fission/corridors/COR-FIS-LEFT.certificate.json;formal/certificates/fission/corridors/COR-FIS-RIGHT.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-LEFT.certificate.json;formal/certificates/fission/fiach/FIACH-FIS-RIGHT.certificate.json;formal/certificates/fusion/corridors/COR-FUS-LEFT.certificate.json;formal/certificates/fusion/corridors/COR-FUS-RIGHT.certificate.json`  
**Claim ceiling:** no unique identity conclusion
### TTH-09 — Route-independent endpoint under flatness

**Status:** `conditional`  
**Statement:** Two admissible routes with the same boundary have the same temporal endpoint only under an explicit flatness, normalization, or confluence certificate.  
**Dependencies:** `TTN-04;TTN-05`  
**Assumptions:** `AS-01;AS-09;AS-10;AS-12`  
**Formal declarations:** `CSTTT.RouteTheory.routeIndependentEndpointUnderNormalization;CSTTT.TargetTheory.certifiedNormalizationYieldsFlatStatus`  
**Evidence:** `formal/certificates/route_completion/ROUTE-COMP-FLAT-01.certificate.json;formal/certificates/route_completion/ROUTE-COMP-INDEXED-01.certificate.json;formal/certificates/transport/TR-POS-02-FLAT.certificate.json`  
**Claim ceiling:** route independence only under premises
### TTH-10 — Monotone record descent transports an arrow

**Status:** `conditional`  
**Statement:** A record map that preserves every declared strict source-record step preserves the endogenous target arrow; weak monotonicity that collapses strict steps is insufficient.  
**Dependencies:** `TTH-03;TTN-03`  
**Assumptions:** `AS-01;AS-08`  
**Formal declarations:** `CSTTT.RecordTheory.monotoneRecordDescentTransportsArrow`  
**Evidence:** `formal/certificates/transport/TR-POS-01.certificate.json;formal/certificates/transport/TR-POS-02-FLAT.certificate.json`  
**Claim ceiling:** structural arrow audit only

## primary-strengthening

### TTS-01 — Generalized temporal-continuity path class

**Status:** `conditional`  
**Statement:** Strict-overlap and direct-successor legs each embed into a generalized structural-continuity path class, and compatible mixed-mode legs compose there without broadening strict Temporal-FIACH.  
**Dependencies:** `TTH-04;TTD-01;TTD-02`  
**Assumptions:** `AS-01;AS-18;AS-19;AS-23`  
**Formal declarations:** `CSTTT.StrengtheningTheory.overlapEmbedsGeneralized;CSTTT.StrengtheningTheory.directEmbedsGeneralized;CSTTT.StrengtheningTheory.generalizedStrictlyBroaderThanOverlap;CSTTT.StrengtheningTheory.generalizedPathComposition`  
**Evidence:** `formal/certificates/strengthenings/continuity/GCP-DIRECT-01.certificate.json;formal/certificates/strengthenings/continuity/GCP-MIXED-01.certificate.json;formal/certificates/strengthenings/continuity/GCP-OVERLAP-01.certificate.json;formal/certificates/strengthenings/continuity/ODR-01.certificate.json;formal/certificates/strengthenings/direct/DS-POS-03-MIXED-MODE.certificate.json`  
**Claim ceiling:** broader structural lineage vocabulary only; strict FIACH unchanged
### TTS-02 — Exact vector-valued defect acceptance

**Status:** `conditional`  
**Statement:** Acceptance under the exact defect semantics is componentwise: every hard-gate defect is zero and every soft defect lies below its own rational tolerance; acceptance is downward closed and not determined by a scalar summary.  
**Dependencies:** `TTN-10`  
**Assumptions:** `AS-01;AS-16`  
**Formal declarations:** `CSTTT.DefectTheory.acceptedHardGateIsZero;CSTTT.DefectTheory.vectorAcceptanceDownwardClosed;CSTTT.DefectTheory.scalarSummaryDoesNotDetermineAcceptance`  
**Evidence:** `formal/certificates/strengthenings/defects/DEF-EQUAL-SCALAR-01.certificate.json;formal/certificates/strengthenings/defects/DEF-POS-01.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C01.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C02.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C03.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C04.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C05.certificate.json;formal/certificates/strengthenings/defects/controls/DEF-C06.certificate.json`  
**Claim ceiling:** finite exact componentwise defect semantics only
### TTS-03 — Hard-gate-preserving bounded temporal robustness

**Status:** `conditional`  
**Statement:** Every perturbation inside the declared exact componentwise margin preserves positive predictive, order, tick, progress, and record advances while leaving every hard gate satisfied.  
**Dependencies:** `TTH-06;TTS-02`  
**Assumptions:** `AS-01;AS-16;AS-33`  
**Formal declarations:** `CSTTT.RobustnessTheory.boundedPerturbationPreservesMargin;CSTTT.RobustnessTheory.failedHardGateCannotBeAveragedAway`  
**Evidence:** `formal/certificates/strengthenings/robustness/ROB-POS-01.certificate.json`  
**Claim ceiling:** declared exact finite perturbation box only
### TTS-04 — Model-relative unbounded controlled invariant

**Status:** `conditional`  
**Statement:** A total target-owned policy on the exact finite controlled invariant defines a model-relative infinite run that preserves package integrity, progress, record advancement, ownership, and solvency for every admissible disturbance stream.  
**Dependencies:** `TTH-05;TTN-12`  
**Assumptions:** `AS-01;AS-20;AS-21;AS-22;AS-34`  
**Formal declarations:** `CSTTT.AutonomyTheory.modelRelativeUnboundedControlledInvariant`  
**Evidence:** `formal/certificates/strengthenings/unbounded/UNB-POS-01.certificate.json`  
**Claim ceiling:** infinite run inside the exact finite controlled model; no physical persistence theorem
