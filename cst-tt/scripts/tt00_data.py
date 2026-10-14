"""Frozen CST-TT-00 registries.

The data in this module are normative for the scaffold. Later phases may append
status and evidence fields, but must not silently rewrite identifiers or claim
ceilings.
"""

PHASE = "CST-TT-00"
PROJECT = "CST-TT"
LEAN_TOOLCHAIN = "leanprover/lean4:v4.28.0"
PYTHON_VERSION = "3.13.5"
BASE_COMMIT = "4a48d7ee212cde2404be06f01df0a28aa3ad12fc"
BASE_TAG = "CST-EXP-06-v1"

CLAIM_LANES = [
    dict(lane_id="S-T", name="structural transport", question="What separately typed temporal or package object is preserved across carriers?", inherits_from="none", claim_ceiling="structural"),
    dict(lane_id="S-R", name="structural realization", question="Does the target instantiate one coherent declared package?", inherits_from="none", claim_ceiling="structural"),
    dict(lane_id="S-L", name="structural lineage", question="Does the episode satisfy the frozen overlap or fallback ancestry relation?", inherits_from="none", claim_ceiling="structural relation"),
    dict(lane_id="A", name="post-withdrawal autonomy", question="Does the target maintain the package after named support is removed?", inherits_from="none", claim_ceiling="model-relative autonomy"),
    dict(lane_id="R", name="recognition", question="What observations license applying a structural predicate to a real system?", inherits_from="none", claim_ceiling="empirical bridge only"),
    dict(lane_id="O", name="ontology", question="What follows only with A1, A2-P, certificate soundness, or identity premises?", inherits_from="none", claim_ceiling="separately assumed"),
    dict(lane_id="M", name="methodology", question="What was checked, generated, enumerated, or compiled?", inherits_from="none", claim_ceiling="method only"),
]

DEFINITIONS = [
    ("D-001","CarrierId","CSTTT/Core/Carrier.lean","pre-verdict carrier individuation","M",""),
    ("D-002","Carrier","CSTTT/Core/Carrier.lean","separately typed finite state carrier","M","D-001"),
    ("D-003","CarrierPair","CSTTT/Core/Carrier.lean","source/target pair with prior distinctness","M","D-002"),
    ("D-004","Stage","CSTTT/Core/Episode.lean","finite ordered handoff stage","M",""),
    ("D-005","Event","CSTTT/Core/Episode.lean","carrier-owned staged event","M","D-001;D-004"),
    ("D-006","Dependency","CSTTT/Core/Episode.lean","strictly forward operational dependency","M","D-005"),
    ("D-007","Episode","CSTTT/Core/Episode.lean","operational graph and active support; no lineage field","M","D-003;D-006"),
    ("D-008","TemporalAlphabet","CSTTT/Temporal/Signature.lean","finite alphabets for predictive now, order, tick, progress, record, route, maintenance","S-T","D-002"),
    ("D-009","PredictiveNow","CSTTT/Temporal/Signature.lean","predictive class plus route residue and future-sufficiency obligation","S-T","D-008"),
    ("D-010","TemporalSignature","CSTTT/Temporal/Signature.lean","frozen transported temporal object","S-T","D-009"),
    ("D-011","TemporalClosureSpec","CSTTT/Temporal/Closure.lean","carrier-local order, tick, progress, record, and maintenance semantics","S-R","D-002;D-010"),
    ("D-012","TemporalClosureWitness","CSTTT/Temporal/Closure.lean","state-level temporal realization evidence","S-R","D-011"),
    ("D-013","ClockTranslation","CSTTT/Temporal/Clock.lean","separately typed source/target temporal vocabulary maps","S-T","D-008"),
    ("D-014","RouteComparison","CSTTT/Temporal/Clock.lean","current, predictive, route, and translation comparison","S-T","D-013"),
    ("D-015","ClauseId","CSTTT/Package/Clauses.lean","eight C-shaped structural proxy indices","S-R",""),
    ("D-016","ClauseSpec","CSTTT/Package/Clauses.lean","independent clause scope, acceptance relation, gate, and resources","S-R","D-015"),
    ("D-017","ClauseWitness","CSTTT/Package/Clauses.lean","one local clause assignment and gate evidence","S-R","D-016"),
    ("D-018","ClauseBundle","CSTTT/Package/Clauses.lean","exactly eight independent witness slots","S-R","D-017"),
    ("D-019","JoinTree","CSTTT/Package/Gluing.lean","running-intersection and acyclicity premises","S-R","D-015"),
    ("D-020","IntegratedPackageCertificate","CSTTT/Package/Gluing.lean","global package, hard gates, C6 substance, and target ownership","S-R","D-012;D-018;D-019"),
    ("D-021","StagedClausePreservationEvidence","CSTTT/Package/Gluing.lean","stagewise typed clause preservation independent of lineage","S-T;S-R","D-016"),
    ("D-022","TemporalBridge","CSTTT/Transport/TemporalBridge.lean","componentwise heterogeneous temporal bridge without lineage verdict","S-T","D-013"),
    ("D-023","TemporalTransportCertificate","CSTTT/Transport/TemporalBridge.lean","source/target temporal witnesses plus bundled bridge","S-T","D-012;D-022"),
    ("D-024","RouteHolonomyAudit","CSTTT/Transport/TemporalBridge.lean","two-route endpoint/current/predictive/residue audit","S-T","D-014"),
    ("D-025","FlatnessCertificate","CSTTT/Transport/TemporalBridge.lean","critical-pair joining, trivial residue, and zero translation holonomy","S-T","D-024"),
    ("D-026","CounterfactualAudit","CSTTT/Corridor/TemporalCorridor.lean","source and target nonredundancy at a mixed stage","S-L","D-007;D-010"),
    ("D-027","TemporalCorridorData","CSTTT/Corridor/TemporalCorridor.lean","episode-local realization, transport, frontier, and route data","S-L","D-007;D-026"),
    ("D-028","TemporalCorridorCertificate","CSTTT/Corridor/TemporalCorridor.lean","strict overlap/no-gap/mixed/nonredundant corridor","S-L","D-027"),
    ("D-029","DirectSuccessorCertificate","CSTTT/Corridor/DirectSuccessor.lean","provisional event-to-event class, separately named from overlap","S-L","D-006;D-023"),
    ("D-030","ControlledSystem","CSTTT/Autonomy/System.lean","target dynamics, disturbances, actions, package predicate, and ownership","A","D-002"),
    ("D-031","WithdrawalSpec","CSTTT/Autonomy/System.lean","named removed and retained dependencies","A","D-001"),
    ("D-032","ControlledInvariantCertificate","CSTTT/Autonomy/System.lean","target-owned one-step invariant response certificate","A","D-030"),
    ("D-033","AutonomyCertificate","CSTTT/Autonomy/System.lean","withdrawal, invariant, anti-stall, budget, and ownership","A","D-031;D-032"),
    ("D-034","ClaimLane","CSTTT/Targets/TemporalFIACH.lean","seven non-inheriting claim lanes","M",""),
    ("D-035","TemporalFIACHCertificate","CSTTT/Targets/TemporalFIACH.lean","aggregate of separately validated package, corridor, and autonomy certificates","S-R;S-L;A","D-020;D-028;D-033"),
    ("D-036","TemporalFIACH","CSTTT/Targets/TemporalFIACH.lean","certificate-existence relation; not identity","S-L","D-035"),
    ("D-037","OperationalSeed","CSTTT/Fallback/Ancestry.lean","fallback provenance edges without successor vocabulary","S-L","D-006"),
    ("D-038","AncestryClosure","CSTTT/Fallback/Ancestry.lean","monotone no-ex-nihilo closure interface","S-L","D-037"),
    ("D-039","IAPSCertificate","CSTTT/Fallback/Ancestry.lean","fallback ancestry plus independent package and autonomy","S-R;S-L;A","D-020;D-033;D-038"),
]
DEFINITION_ROWS = [dict(definition_id=i,name=n,module=m,purpose=p,claim_lanes=l,dependencies=d,status="frozen-scaffold") for i,n,m,p,l,d in DEFINITIONS]

THEOREMS = [
    ("TTH-01","Acyclic local-witness gluing","primary","constructive","CST-TT-02","S-R","","CSTTT.Prospects.AcyclicLocalWitnessGluing","TTM-11","structural package only"),
    ("TTH-02","Staged heterogeneous package assembly","primary","constructive","CST-TT-02","S-T;S-R","TTH-01","CSTTT.Prospects.StagedPackageAssembly","TTM-01;TTM-11","structural package only"),
    ("TTH-03","Bundled heterogeneous temporal transport","primary","constructive","CST-TT-03","S-T","","CSTTT.Prospects.BundledTemporalTransport","TTM-05;TTM-17","structural transport only"),
    ("TTH-04","Strict temporal-corridor composition","primary","constructive","CST-TT-04","S-L","TTH-03;TTN-04","CSTTT.Prospects.TemporalCorridorComposition","TTM-01;TTM-05;TTM-06","structural lineage criterion only"),
    ("TTH-05","Post-withdrawal finite-horizon invariance","primary","constructive","CST-TT-05","A","","CSTTT.Prospects.PostWithdrawalFiniteHorizonInvariance","TTM-01;TTM-04;TTM-09;TTM-10","model-relative autonomy only"),
    ("TTH-06","Temporal-FIACH certificate soundness","primary","constructive","CST-TT-05","S-R;S-L;A","TTH-02;TTH-04;TTH-05","CSTTT.Prospects.TemporalFIACHCertificateSoundness","TTM-01;TTM-02;TTM-04;TTM-11","structural precursor only"),
    ("TTH-07","Full temporal handoff composition","primary","constructive","CST-TT-06","S-R;S-L;A","TTH-04;TTH-05;TTH-06;TTH-09","CSTTT.Prospects.FullHandoffComposition","TTM-01;TTM-05;TTM-06","structural precursor only"),
    ("TTH-08","Relation-valued temporal fission","primary","boundary","CST-TT-06","S-L","TTH-04;TTN-11","CSTTT.Prospects.RelationValuedTemporalFission","TTM-07","no unique identity conclusion"),
    ("TTH-09","Route-independent endpoint under flatness","primary","constructive","CST-TT-03","S-T","TTN-04;TTN-05","CSTTT.Prospects.RouteIndependentEndpointUnderFlatness","TTM-05;TTM-06","route independence only under premises"),
    ("TTH-10","Monotone record descent transports an arrow","primary","constructive","CST-TT-03","S-T","TTH-03;TTN-03","CSTTT.Prospects.MonotoneRecordDescentTransportsArrow","TTM-01;TTM-16","structural arrow audit only"),
    ("TTN-01","Detached-copy insufficiency","common","no-go","CST-TT-01","S-L","","CSTTT.Prospects.DetachedCopyCountermodel","TTM-02","exact finite boundary"),
    ("TTN-02","Public-shadow insufficiency","common","no-go","CST-TT-01","S-R;S-L;R","","CSTTT.Prospects.PublicShadowCountermodel","TTM-12","finite-interface nonidentifiability"),
    ("TTN-03","Holonomy is not an endogenous arrow","common","no-go","CST-TT-01","S-T;S-R","","CSTTT.Prospects.HolonomyWithoutArrowCountermodel","TTM-16","exact finite boundary"),
    ("TTN-04","Memory-or-flatness boundary","common","boundary","CST-TT-03","S-T","TTN-03","CSTTT.Prospects.MemoryOrFlatness","TTM-05;TTM-17","route discipline only"),
    ("TTN-05","No canonical global now under translation holonomy","common","no-go","CST-TT-03","S-T","TTN-04","CSTTT.Prospects.NoCanonicalGlobalNow","TTM-05","route-indexed time only"),
    ("TTN-06","Essential external support defeats autonomy","common","no-go","CST-TT-05","A","","CSTTT.Prospects.ExternalSupportAutonomyFailure","TTM-04","model-relative autonomy boundary"),
    ("TTN-07","Stable tick phase without progress","common","no-go","CST-TT-01","S-R","","CSTTT.Prospects.StableTickWithoutProgress","TTM-14","temporal closure boundary"),
    ("TTN-08","Local-global package obstruction","common","no-go","CST-TT-01","S-R","","CSTTT.Prospects.LocalGlobalObstruction","TTM-11","global package boundary"),
    ("TTN-09","Temporal gap versus resumed stream","common","no-go","CST-TT-01","S-L","TTN-01","CSTTT.Prospects.GapResumeCountermodel","TTM-08","strict no-gap criterion only"),
    ("TTN-10","Scalar residual hides hard-gate failure","common","no-go","CST-TT-01","S-R;A","","CSTTT.Prospects.ScalarResidualHardGateFailure","TTM-13","hard gates cannot be averaged"),
    ("TTN-11","Exact symmetry supplies no invariant unique continuer","common","no-go","CST-TT-01","S-L;O","","CSTTT.Prospects.SymmetryNoUniqueContinuer","TTM-07;TFM-03","no unique identity conclusion"),
    ("TTN-12","Finite success does not imply unbounded liveness","common","boundary","CST-TT-01","A","","CSTTT.Prospects.FiniteTraceNotUnboundedLiveness","TTM-10","finite-horizon claim ceiling"),
    ("TTN-13","Same-carrier re-encoding is not cross-carrier transport","common","definition-boundary","CST-TT-01","S-T","","CSTTT.Prospects.SameCarrierReencodingNotCrossCarrier","TTM-15","typing boundary"),
    ("TTN-14","Branchwise preservation need not preserve recombination","common","no-go","CST-TT-01","S-R;S-L","","CSTTT.Prospects.BranchwiseRecombinationFailure","TFM-04","joint-structure boundary"),
    ("TTD-01","Direct-successor temporal validity","direct-successor","constructive","CST-TT-04","S-L","TTH-03","CSTTT.Prospects.DirectSuccessorValidity","TTM-03","separate broader criterion"),
    ("TTD-02","Overlap/direct-successor relation","direct-successor","boundary","CST-TT-07A","S-L","TTH-04;TTD-01","CSTTT.Prospects.OverlapDirectSuccessorRelation","TTM-01;TTM-03;TTM-08","no silent broadening"),
    ("TTD-03","Direct-successor detached-copy exclusion","direct-successor","no-go","CST-TT-04","S-L","TTD-01;TTN-01","CSTTT.Prospects.DirectSuccessorDetachedCopyExclusion","TTM-02;TTM-03","provenance boundary"),
    ("TTF-01","Predictive bridge descent","fallback","fallback","CST-TT-07B","S-T","TTH-03","CSTTT.Prospects.PredictiveBridgeDescent","TFM-01;TFM-02","fallback transport only"),
    ("TTF-02","Least operational ancestry","fallback","fallback","CST-TT-07B","S-L","TTF-01","CSTTT.Prospects.LeastOperationalAncestry","TFM-01;TFM-02;TFM-03","relation-valued successorship only"),
    ("TTF-03","Independent-twin exclusion","fallback","no-go","CST-TT-07B","S-L","TTF-02","CSTTT.Prospects.IndependentTwinExclusion","TFM-02","no-ex-nihilo boundary"),
    ("TTF-04","Fallback fission, fusion, and empty targets","fallback","fallback","CST-TT-07B","S-L","TTF-02;TTN-14","CSTTT.Prospects.FallbackFissionFusionEmpty","TFM-03;TFM-04","relation-valued only"),
    ("TTF-05","Integrated Temporal-IAPS certificate","fallback","fallback","CST-TT-07B","S-R;S-L;A","TTH-02;TTH-05;TTF-02","CSTTT.Prospects.IntegratedTemporalIAPS","TFM-01;TFM-02","structural successorship only"),
    ("TTF-06","Destructive reconstruction versus independent twin","fallback","boundary","CST-TT-07B","S-L","TTF-02;TTF-03","CSTTT.Prospects.DestructiveReconstructionTwinSeparation","TFM-01;TFM-02","structural successorship only"),
    ("TTF-07","Ancestry supplies no unique numerical identity","fallback","no-go","CST-TT-07B","S-L;O","TTF-04;TTN-11","CSTTT.Prospects.AncestryNoUniqueIdentity","TFM-03","identity remains separately assumed"),
    ("TTF-08","Predictive ancestry is package-insufficient","fallback","no-go","CST-TT-07B","S-R;S-L","TTF-02;TTN-08","CSTTT.Prospects.PredictiveAncestryPackageInsufficient","TFM-04","independent package audit required"),
]
LEGACY_PROVENANCE = {
    "TTH-01": "PTH-01", "TTH-02": "PTH-02", "TTH-04": "PTH-03",
    "TTH-05": "PTH-04", "TTH-06": "PTH-05", "TTH-07": "PTH-06",
    "TTH-08": "PTH-07", "TTH-09": "PTH-11", "TTN-01": "PTH-08",
    "TTN-02": "PTH-12", "TTN-04": "PTH-11", "TTN-06": "PTH-09",
    "TTN-08": "PTH-10", "TTN-11": "PTH-07", "TTN-14": "PTH-10",
    "TTF-01": "FTH-01", "TTF-02": "FTH-02", "TTF-03": "FTH-03",
    "TTF-04": "FTH-04", "TTF-05": "FTH-05", "TTF-06": "FTH-06",
    "TTF-07": "FTH-07", "TTF-08": "FTH-08",
}

THEOREM_ROWS = [
    dict(
        theorem_id=i, name=n, family=f, kind=k, phase=p, status="open-scaffold",
        claim_lanes=l, dependencies=d, lean_statement=s, toy_dependencies=t,
        claim_ceiling=c, legacy_provenance_ids=LEGACY_PROVENANCE.get(i, ""),
    )
    for i,n,f,k,p,l,d,s,t,c in THEOREMS
]

TEMPORAL_AMENDMENTS = [
    ("PTH-01", "Acyclic local-witness gluing", "TTH-01", "retained-and-temporally-strengthened", "C6 must contain order, viable progressing tick, endogenous record/arrow, route-aware predictive now, maintenance, and owner fields."),
    ("PTH-02", "Staged heterogeneous package preservation", "TTH-02", "retained-and-temporally-strengthened", "Staged assembly keeps temporal substance and ownership independently audited; it does not import lineage."),
    ("PTH-03", "Live corridor composition", "TTH-04", "retyped", "The generic live corridor becomes strict temporal-corridor composition over a pre-frozen TemporalSignature and explicit route discipline."),
    ("PTH-04", "Post-withdrawal controlled invariance", "TTH-05", "retained", "Withdrawal now explicitly removes source, bridge, migration controller, decoder, scheduler, and undeclared repair support."),
    ("PTH-05", "FIACH certificate soundness", "TTH-06", "retyped", "The aggregate returns S-R, S-L, A, and route status separately and has a structural-precursor claim ceiling."),
    ("PTH-06", "FIACH composition", "TTH-07", "retyped", "Composition must preserve temporal frontiers, route memory or flatness, and maintenance ownership interfaces."),
    ("PTH-07", "Relation-valued fission", "TTH-08;TTN-11", "split", "The positive branch relation and the symmetry-based no-unique-selector boundary are separated."),
    ("PTH-08", "Detached-copy separation", "TTN-01", "retained-and-sharpened", "Endpoint/package/autonomy equality is held fixed while the strict temporal corridor fails."),
    ("PTH-09", "External-support autonomy failure", "TTN-06", "retained-and-sharpened", "External scheduling and decoding are named withdrawal targets rather than generic support."),
    ("PTH-10", "Local/global package obstruction", "TTN-08;TTN-14", "split", "Global gluing failure and branchwise-versus-recombination failure are represented as distinct boundaries."),
    ("PTH-11", "Route-memory composition boundary", "TTN-04;TTH-09", "split", "Memory-or-flatness is the negative boundary; explicit flatness/confluence purchases route-independent endpoints."),
    ("PTH-12", "Public-shadow insufficiency", "TTN-02", "retained-and-temporally-strengthened", "The hidden mismatch may be predictive-now, route residue, temporal ownership, or another package field."),
    ("FTH-01", "Predictive quotient and bridge descent", "TTF-01", "retained-for-conditional-fallback", "Predictive descent is separately typed and remains dormant until a documented FIACH kill."),
    ("FTH-02", "Least operational ancestry relation", "TTF-02", "retained-for-conditional-fallback", "The seed is operational, monotone, and no-ex-nihilo; no successor-equivalent vocabulary is permitted."),
    ("FTH-03", "Independent-twin exclusion", "TTF-03", "retained-for-conditional-fallback", "Structural equivalence alone cannot add a disconnected target to ancestry."),
    ("FTH-04", "Fission, fusion, and empty targets", "TTF-04", "retained-for-conditional-fallback", "Relation-valued outcomes are preserved while recombination/package audits remain separate."),
    ("FTH-05", "IAPS integrated target theorem", "TTF-05", "retyped-for-temporal-fallback", "Temporal-IAPS combines ancestry, integrated temporal package, and autonomy without asserting uninterrupted temporal continuity."),
    ("FTH-06", "Destructive-reconstruction/twin separation", "TTF-06", "retained-for-conditional-fallback", "Source-derived reconstruction and an isomorphic disconnected twin receive different ancestry verdicts."),
    ("FTH-07", "No unique identity from ancestry", "TTF-07", "retained-for-conditional-fallback", "Branching ancestry supplies no unique numerical identity or survival conclusion."),
    ("FTH-08", "Predictive ancestry is package-insufficient", "TTF-08", "retained-for-conditional-fallback", "Ancestry cannot substitute for independent target package realization."),
]
TEMPORAL_AMENDMENT_ROWS = [
    dict(
        legacy_id=legacy_id, legacy_title=legacy_title, temporal_ids=temporal_ids,
        disposition=disposition, temporal_amendment=amendment,
        source_file="synthesis/FROZEN_THEOREM_FAMILY.csv", status="frozen-provenance-map",
    )
    for legacy_id, legacy_title, temporal_ids, disposition, amendment in TEMPORAL_AMENDMENTS
]

TOYS = [
    ("TTM-01","live temporal handoff","primary-positive","CST-TT-05","source-only; mixed; target-only; withdrawal","TTH-02;TTH-04;TTH-05;TTH-06","no witness implemented in phase 00"),
    ("TTM-02","detached exact temporal copy","negative","CST-TT-01","endpoint-equivalent autonomous target without mixed corridor","TTN-01",""),
    ("TTM-03","direct-successor temporal handoff","discriminator","CST-TT-04","last source event directly generates first target event","TTD-01;TTD-03","separate from strict overlap"),
    ("TTM-04","external scheduler or decoder shadow","negative","CST-TT-01","runtime match collapses after withdrawal","TTN-06",""),
    ("TTM-05","replacement-order holonomy","route","CST-TT-03","same boundary; different route residue or clock translation","TTN-04;TTN-05",""),
    ("TTM-06","confluent completion","positive-control","CST-TT-03","critical pairs join and route residue becomes irrelevant","TTH-09",""),
    ("TTM-07","temporal fission","branch","CST-TT-06","symmetric valid fork","TTH-08;TTN-11",""),
    ("TTM-08","gap and resume","negative","CST-TT-01","equivalent resumed stream after explicit temporal gap","TTN-09",""),
    ("TTM-09","anti-stall target","autonomy-control","CST-TT-05","stable state rejected unless tick progress remains possible","TTH-05;TTN-07",""),
    ("TTM-10","long-run budget failure","boundary","CST-TT-05","finite successful prefix followed by insolvency","TTN-12",""),
    ("TTM-11","local/global package obstruction","negative","CST-TT-01","all local clause checks pass; no global witness","TTN-08",""),
    ("TTM-12","public-shadow collision","negative","CST-TT-01","same reports; different hidden predictive/package fact","TTN-02",""),
    ("TTM-13","scalar hard-gate failure","negative","CST-TT-01","small aggregate residual; one failed nonnegotiable gate","TTN-10",""),
    ("TTM-14","stable tick without progress","negative","CST-TT-01","constant phase or stopped clock passes persistence only","TTN-07",""),
    ("TTM-15","same-carrier re-encoding","typing-control","CST-TT-01","representation change on one carrier","TTN-13",""),
    ("TTM-16","holonomy without arrow","negative","CST-TT-01","noncommuting route loop with reversible lifted dynamics","TTN-03",""),
    ("TTM-17","current-equal predictive-route mismatch","negative","CST-TT-01","present-equivalent histories diverge under continuation probes","TTN-04",""),
    ("TFM-01","source-derived destructive successor","fallback-positive","CST-TT-07B","source-record-target operational provenance with gap","TTF-02;TTF-05;TTF-06","only after FIACH kill"),
    ("TFM-02","independent structural twin","fallback-negative","CST-TT-07B","isomorphic target with no source-reachable path","TTF-03;TTF-06",""),
    ("TFM-03","source-derived symmetric duplication","fallback-branch","CST-TT-07B","two qualifying source-derived targets","TTF-04;TTF-07",""),
    ("TFM-04","fusion with recombination conflict","fallback-negative","CST-TT-07B","ancestry can exist while joint package gluing fails","TTF-04;TTF-08;TTN-14",""),
]
TOY_ROWS = [dict(toy_id=i,name=n,role=r,phase=p,minimal_shape=s,discriminates=d,status="specified-not-implemented",notes=notes) for i,n,r,p,s,d,notes in TOYS]

SCHEMAS = [
    ("CS-01","temporal_signature.schema.json","Temporal signature","S-T;S-R","examples/scaffold/temporal_signature.scaffold.json"),
    ("CS-02","package_certificate.schema.json","Integrated package","S-R","examples/scaffold/package_certificate.scaffold.json"),
    ("CS-03","temporal_corridor.schema.json","Strict overlap temporal corridor","S-L","examples/scaffold/temporal_corridor.scaffold.json"),
    ("CS-04","direct_successor.schema.json","Direct successor","S-L","examples/scaffold/direct_successor.scaffold.json"),
    ("CS-05","autonomy_certificate.schema.json","Post-withdrawal autonomy","A","examples/scaffold/autonomy_certificate.scaffold.json"),
    ("CS-06","temporal_fiach_certificate.schema.json","Temporal-FIACH aggregate","S-R;S-L;A","examples/scaffold/temporal_fiach_certificate.scaffold.json"),
    ("CS-07","ancestry_certificate.schema.json","Fallback ancestry interface","S-L","examples/scaffold/ancestry_certificate.scaffold.json"),
    ("CS-08","countermodel_certificate.schema.json","Finite countermodel","M","examples/scaffold/countermodel_certificate.scaffold.json"),
]
SCHEMA_ROWS = [dict(schema_id=i,file=f,name=n,claim_lanes=l,scaffold_example=e,status="frozen-scaffold") for i,f,n,l,e in SCHEMAS]

ASSUMPTIONS = [
    ("AS-01","FINITE-EXACT","structural","All theorem-core carriers, alphabets, episodes, and certificate data are finite and exact.","all","No statement about unbounded physical systems."),
    ("AS-02","H-DISTINCT","structural","Source and target carrier identities are fixed and distinct before evaluation.","FIACH;IAPS","Does not say the target is another person."),
    ("AS-03","H-SOURCE-PKG","structural","The source package premise is independently supplied.","FIACH;IAPS","Does not establish source consciousness."),
    ("AS-04","H-PREDICTIVE-SUFF","structural","The predictive-now vocabulary is sufficient for the declared finite continuation probes.","transport","Probe-relative only."),
    ("AS-05","H-ORDER","structural","A carrier-local successor/order relation is declared.","temporal closure","Order alone is not time or consciousness."),
    ("AS-06","H-TICK","structural","A viable repeatable tick carrier is declared.","temporal closure","Tick stability alone is insufficient."),
    ("AS-07","H-PROGRESS","structural","The tick carrier admits genuine progress.","temporal closure","No phenomenal conclusion."),
    ("AS-08","H-ARROW","structural","An endogenous auditable record/arrow relation is declared.","temporal closure","Holonomy is not substituted for this premise."),
    ("AS-09","H-MAINTENANCE","structural","Temporal maintenance resources and ownership are declared.","temporal closure;autonomy","Model-relative ownership only."),
    ("AS-10","H-BRIDGE-ADM","structural","Cross-carrier component maps satisfy the declared admissibility interface.","transport","Not supplied by A2-P."),
    ("AS-11","H-REP-INDEP","structural","Transport is independent of arbitrary representatives at the declared quotient.","transport","Quotient-relative only."),
    ("AS-12","H-ROUTE-MEMORY","structural","Predictively relevant route residue is retained when route systems are nonflat.","transport;corridor","Can be discharged by AS-13."),
    ("AS-13","H-FLATNESS","optional-structural","Critical pairs join and translation holonomy vanishes for the declared route class.","route-independent strengthening","Not assumed by default."),
    ("AS-14","H-CLOCK-REL","structural","Source-local and target-local order/tick coordinates have an explicit typed relation.","transport;corridor","No canonical global now is presumed."),
    ("AS-15","H-GLOBAL-GLUE","structural","Local clause witnesses satisfy a declared acyclic/running-intersection gluing premise.","package","Cannot be inferred from local validity alone."),
    ("AS-16","H-HARD-GATES","structural","Nonnegotiable clause and viability gates are separately declared.","package;autonomy","Not replaceable by a scalar average."),
    ("AS-17","H-PACKAGE-OWNERSHIP","structural","Essential final package resources lie inside the target boundary.","package","Does not imply autonomy."),
    ("AS-18","H-NONREDUNDANCY","structural","Source and target contributions are tested by predeclared counterfactual interventions.","strict corridor","Must not mention the final verdict."),
    ("AS-19","H-NO-GAP","structural","Every strict-corridor stage realizes the temporal package.","strict corridor","Direct-successor is separately typed."),
    ("AS-20","H-WITHDRAWAL","structural","The source, bridge, controller, decoder, scheduler, and undeclared repair are named and removed.","autonomy","Environment retained by the model remains explicit."),
    ("AS-21","H-DISTURBANCE","structural","A finite admissible disturbance class is fixed before evaluation.","autonomy","Autonomy is relative to this class."),
    ("AS-22","H-INVARIANT","structural","A target-owned controlled invariant region is supplied or computed.","autonomy","Finite model only."),
    ("AS-23","H-DIRECT-PROVENANCE","optional-structural","The last source event operationally generates the first target event with typed temporal preservation.","direct successor","Does not imply strict overlap."),
    ("AS-24","H-ANCESTRY-SEED","fallback-structural","Fallback seed edges are operational and contain no successor-equivalent vocabulary.","IAPS","Only after documented FIACH kill."),
    ("AS-25","H-NO-EX-NIHILO","fallback-structural","Fallback closure cannot admit disconnected twins solely by similarity.","IAPS","Does not select one branch."),
    ("AS-26","H-FELT-TIME","interpretive","The felt aspect requires autonomous layer-realized temporal closure.","ontology/recognition","Explicit hypothesis; not an SBT theorem."),
    ("AS-27","H-CONT-TIME","interpretive","Uninterrupted felt continuity requires episode-indexed continuation of realized temporal closure.","ontology/recognition","Structural antecedent can be studied; felt conclusion remains assumed."),
    ("AS-28","A1","ontological","The consciousness paper's objecthood/realization postulate is accepted.","ontology","No structural theorem proves it."),
    ("AS-29","A2-P","ontological","Substrate indifference is accepted in the intended philosophical sense.","ontology","Does not create transport, lineage, or recognition data."),
    ("AS-30","H-CERT-SOUND","recognition/ontology","The finite structural certificate is sound for the intended consciousness-relevant property.","recognition;ontology","Open bridge."),
    ("AS-31","H-RECOGNITION","empirical","Measurements correctly identify the structural predicates in a real system.","recognition","Not part of theorem/toy core."),
    ("AS-32","H-PERSONAL-IDENTITY","ontological","The selected structural relation is sufficient for personal identity or survival.","ontology","Not assumed in any structural result."),
]
ASSUMPTION_ROWS = [dict(assumption_id=i,name=n,tier=t,statement=s,used_by=u,nonclaim=nc,status="frozen") for i,n,t,s,u,nc in ASSUMPTIONS]

KILL_CRITERIA = [
    ("K-FIACH-01","FIACH","Primitive temporal, package, corridor, or autonomy definitions contain verdict-equivalent vocabulary.","kill and redesign definitions","CST-TT-00 onward"),
    ("K-FIACH-02","FIACH","No noncircular mixed-source/target nonredundancy predicate survives bounded counterexample search.","authorize CST-TT-07B after documentation","CST-TT-04"),
    ("K-FIACH-03","FIACH","Strict temporal corridors fail composition under every scientifically acceptable frontier rule.","authorize CST-TT-07B after documentation","CST-TT-04"),
    ("K-FIACH-04","FIACH","A detached endpoint-equivalent copy satisfies the strict corridor under the frozen definitions.","kill the corridor definition","CST-TT-01/CST-TT-04"),
    ("K-FIACH-05","FIACH","No exact finite positive witness satisfies independent package, corridor, and autonomy gates.","downgrade to no-go or fallback","CST-TT-05"),
    ("K-PKG-01","package","Clause satisfaction or C6 is defined by successful handoff, ancestry, or final verdict.","kill and redesign package layer","CST-TT-02"),
    ("K-PKG-02","package","Local witnesses cannot be glued without adding post hoc target-specific clauses.","retain local/global no-go only","CST-TT-02"),
    ("K-AUTO-01","autonomy","Target maintenance requires a resource declared removed at withdrawal.","autonomy fails","CST-TT-05"),
    ("K-AUTO-02","autonomy","The only invariant region is stalled or violates a hard gate.","autonomy fails","CST-TT-05"),
    ("K-DIRECT-01","direct-successor","Operational provenance reduces to endpoint equality or arbitrary data reachability.","reject direct-successor strengthening","CST-TT-04/CST-TT-07A"),
    ("K-IAPS-01","IAPS","Fallback seed contains ancestry/successor-equivalent vocabulary or every data edge qualifies.","kill fallback construction","CST-TT-07B"),
    ("K-IAPS-02","IAPS","A disconnected independent twin enters the least relation.","kill fallback construction","CST-TT-07B"),
    ("K-IAPS-03","IAPS","Repeated closure universalizes ancestry or admits stale/adversarial records without typed guards.","kill fallback construction","CST-TT-07B"),
    ("K-ONTO-01","all","A structural result is reported as consciousness, felt continuity, survival, or numerical identity without explicit extra assumptions.","block release and correct claim","all phases"),
]
KILL_ROWS = [dict(kill_id=i,target=t,trigger=tr,action=a,decision_phase=p,status="armed") for i,t,tr,a,p in KILL_CRITERIA]

DEPENDENCY_EDGES = [
    ("D-008","D-010","temporal alphabet types the signature"),
    ("D-010","D-011","signature is evaluated by closure semantics"),
    ("D-011","D-012","closure witness instantiates closure semantics"),
    ("D-012","D-020","C6 temporal substance enters package certificate"),
    ("D-016","D-020","independent clauses enter package certificate"),
    ("D-019","D-020","gluing premise enters package certificate"),
    ("D-013","D-022","clock translation enters bridge"),
    ("D-022","D-023","bridge enters transport certificate"),
    ("D-007","D-027","operational episode enters corridor data"),
    ("D-010","D-027","frozen signature precedes corridor data"),
    ("D-026","D-028","counterfactual audit enters corridor certificate"),
    ("D-023","D-029","transport enters direct-successor certificate"),
    ("D-030","D-032","controlled system enters invariant certificate"),
    ("D-031","D-033","withdrawal enters autonomy certificate"),
    ("D-032","D-033","invariant enters autonomy certificate"),
    ("D-020","D-035","package certificate enters aggregate"),
    ("D-028","D-035","strict corridor certificate enters aggregate"),
    ("D-033","D-035","autonomy certificate enters aggregate"),
    ("D-037","D-038","operational seed enters fallback closure"),
    ("D-038","D-039","fallback closure enters IAPS certificate"),
    ("TTH-01","TTH-02","gluing precedes package assembly"),
    ("TTH-03","TTH-04","transport precedes corridor composition"),
    ("TTH-02","TTH-06","package theorem enters aggregate theorem"),
    ("TTH-04","TTH-06","corridor theorem enters aggregate theorem"),
    ("TTH-05","TTH-06","autonomy theorem enters aggregate theorem"),
    ("TTH-06","TTH-07","aggregate theorem precedes full composition"),
    ("TTN-04","TTH-09","memory/flatness boundary precedes route-independent strengthening"),
    ("TTF-02","TTF-05","fallback ancestry enters integrated fallback"),
]
DEPENDENCY_ROWS = [dict(source=s,target=t,reason=r,status="frozen") for s,t,r in DEPENDENCY_EDGES]
