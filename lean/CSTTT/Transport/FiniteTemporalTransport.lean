import CSTTT.Transport.TemporalBridge

namespace CSTTT.TransportTheory

/-- Representative independence is checked only on the declared reachable image.
It says that two raw source representatives in one predictive class have one
well-defined target predictive image. -/
def RepresentativeIndependent
    {SourceRep SourceClass TargetClass : Type}
    (reachable : SourceRep → Prop)
    (sourceClass : SourceRep → SourceClass)
    (pushedTargetClass : SourceRep → TargetClass) : Prop :=
  ∀ x y, reachable x → reachable y → sourceClass x = sourceClass y →
    pushedTargetClass x = pushedTargetClass y

/-- Exact componentwise agreement between separately typed temporal signatures.
This statement contains no operational-episode or later-layer verdict field. -/
structure TemporalSignatureAgreement
    {src dst : TemporalAlphabet}
    (clock : ClockTranslation src dst)
    (targetOwner : CarrierId)
    (source : TemporalSignature src)
    (target : TemporalSignature dst) : Prop where
  predictiveClass :
    clock.mapPredictive source.predictiveNow.predictiveClass =
      target.predictiveNow.predictiveClass
  routeResidue :
    clock.mapRoute source.predictiveNow.routeResidue =
      target.predictiveNow.routeResidue
  futureSufficiency :
    source.predictiveNow.futureSufficient = target.predictiveNow.futureSufficient
  orderState : clock.mapOrder source.orderState = target.orderState
  tickPhase : clock.mapTick source.tickPhase = target.tickPhase
  progressState : clock.mapProgress source.progressState = target.progressState
  arrowRecord : clock.mapRecord source.arrowRecord = target.arrowRecord
  maintenanceState :
    clock.mapMaintenance source.maintenanceState = target.maintenanceState
  targetOwnership : target.owner = targetOwner

/-- Proof-bearing component bundle for heterogeneous temporal transport.
The predicates are supplied independently; the record contains no later-layer
verdict field. -/
structure FiniteTemporalTransportProof
    (Bridge : Type)
    (admissible representativeIndependent predictivePreserved orderPreserved
      tickPhasePreserved tickProgressPreserved recordDescentPreserved
      routeDisciplineSatisfied maintenanceTranslated ownershipInterfaceValid :
      Bridge → Prop)
    (b : Bridge) where
  admissible_ok : admissible b
  representativeIndependent_ok : representativeIndependent b
  predictivePreserved_ok : predictivePreserved b
  orderPreserved_ok : orderPreserved b
  tickPhasePreserved_ok : tickPhasePreserved b
  tickProgressPreserved_ok : tickProgressPreserved b
  recordDescentPreserved_ok : recordDescentPreserved b
  routeDisciplineSatisfied_ok : routeDisciplineSatisfied b
  maintenanceTranslated_ok : maintenanceTranslated b
  ownershipInterfaceValid_ok : ownershipInterfaceValid b

/-- TTH-03. A proof-bearing certificate exposes every frozen temporal component
as a separate conjunct. This is structural transport only. -/
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
  exact ⟨p.representativeIndependent_ok,
    p.predictivePreserved_ok,
    p.orderPreserved_ok,
    p.tickPhasePreserved_ok,
    p.tickProgressPreserved_ok,
    p.recordDescentPreserved_ok,
    p.routeDisciplineSatisfied_ok,
    p.maintenanceTranslated_ok,
    p.ownershipInterfaceValid_ok⟩

/-- Componentwise transport remains independent of an operational episode. -/
theorem transportProof_has_no_episode_premise
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
    admissible b := by
  exact p.admissible_ok

end CSTTT.TransportTheory
