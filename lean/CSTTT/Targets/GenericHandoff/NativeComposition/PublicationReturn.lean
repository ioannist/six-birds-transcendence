import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationComposition
import CSTTT.Targets.Composition

/-! Return to the frozen structural composition interface. The summaries are
computed from the raw publication readout, including the ENTIRE future model,
physical run, root and executed corridor stage. Their predicates are defined
component semantics, rather than independently supplied summary flags. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationReturn
open RegisterInterpreter PublicationReplay PublicationComposition CSTTT.TransportTheory
open CSTTT.CorridorTheory.AtomicChain
local instance : DecidableEq PublicationFuture.Observation := instDecidableEqTemporalSnapshotReadout

structure Signature where
  run : Option ModeExecution.Registers
  future : FullFutureModel Frame.Registers (Unit × Bool) Factor
    (TemporalRunCode Frame.Predictive Frame.Residue Bool) PublicationFuture.Observation
  root : Frame.Registers
  corridor : Option RawStage

noncomputable def leg (b : Assignment Owner NativePackageBundle.Value) (cell : Owner) (h : Factor) : Option FiniteAtomicLeg :=
  (PublicationCorridor.chain (native b) h).bind (fun legs => if cell then legs.head? else legs.getLast?)
noncomputable def entrySignature (b : Assignment Owner NativePackageBundle.Value) (hb : PublicationComposition.Ready b)
    (cell : Owner) (h : Factor) : Signature :=
  ⟨some (AcquisitionExecution.initial (raw cell) (native b) (hb.acquisition cell) h),
    sourceFuture b hb cell,sourceRoot b hb cell h,(leg b cell h).map entry⟩
noncomputable def exitSignature (b : Assignment Owner NativePackageBundle.Value) (hb : PublicationComposition.Ready b)
    (cell : Owner) (h : Factor) : Signature :=
  ⟨SupportedAcquisitionSequence.firstEntry (raw cell) (native b) (hb.acquisition cell) h h,
    targetFuture b hb cell,targetRoot b hb cell h,(leg b cell h).map exit⟩

theorem whole_signature_middle_of_lanes (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) (executed : ExecutionLane b hb) (futures : FutureLane b hb)
    (corridor : CorridorLane b) (h : Factor) : exitSignature b hb true h=entrySignature b hb false h := by
  obtain ⟨seed,left,right,hm,hs,hl,hr,_,_,hj,_⟩ := corridor h
  have chain : PublicationCorridor.chain (native b) h=some [left,right] := by
    simp [PublicationCorridor.chain,hm,hs,hl,hr]
  have leftLeg : leg b true h=some left := by simp [leg,chain]
  have rightLeg : leg b false h=some right := by simp [leg,chain]
  obtain ⟨middle,final,he,hi,_⟩ := executed.2 h
  have physical := he.trans (congrArg some hi)
  have stage : exit left=entry right := by
    simp only [AdjacentFrontierCheck,decide_eq_true_eq] at hj
    exact hj.2.1
  unfold exitSignature entrySignature
  rw [physical,futures.2.2.1,futures.2.2.2.1 h,leftLeg,rightLeg]
  simp only [Option.map_some,stage]

def status (s : ComputedRouteStatus) : RouteStatus :=
  match s with | .routeIndexed => .routeIndexed | .unavailable => .unresolved
noncomputable def routeStatus (b : Assignment Owner NativePackageBundle.Value) (cell : Owner) (h : Factor) : RouteStatus :=
  match leg b cell h with | some l => status (routeStatusOf l) | none => .unresolved

theorem exposed_publication (a : Assignment Owner NativePackageBundle.Value) (cell : Owner)
    (p : NativePackageBundle.Bundle × NativePackageBundle.Bundle) (hp : PublicationMaps.exposure a cell=some p) :
    p.1=NativePackageBundle.publishBundle p.2 := by
  rw [PublicationMaps.exposure_equation] at hp
  cases cell
  all_goals cases ha : a false with
  | none => simp [NativePackageBundle.staged,NativePackageBundle.image,swapOwner,ha] at hp
  | some q =>
    simp [NativePackageBundle.staged,NativePackageBundle.image,swapOwner,ha] at hp
    subst p
    rfl

def RawTransportLane (b : Assignment Owner NativePackageBundle.Value) : Prop :=
  ∀ cell p, b cell=some p →
    p.1=NativePackageBundle.publishBundle p.2 ∧
    ProtocolCreditRules.Transport (NativeCreditCells.data p.2).tables (NativeCreditCells.data p.1).tables
      NativeCreditCells.protocols id id NativePackagePrimitives.translateOwner ∧
    JointHistoryTransport.Transport NativeJointCells.schema NativeJointCells.schema
      (NativeJointCells.data p.2) (NativeJointCells.data p.1) NativeJointCells.historyImage
theorem exposed_raw_transport (a : Assignment Owner NativePackageBundle.Value) :
    RawTransportLane (PublicationMaps.exposure a) := by
  intro cell p hp
  have he := exposed_publication a cell p hp
  refine ⟨he,?_,?_⟩
  · rw [he]; exact PublicationMaps.raw_credit_transport p.2
  · rw [he]; exact PublicationMaps.raw_joint_transport p.2

/-- Every interpreted parent and seam is checked on the actual staged map
output. The outer future and corridor are derived, and final control is the
same explicit function already used for the second target's genuine entries.
Raw credit transport includes housing; joint transport includes entire branch
histories, coupling and distributions. No outer readout is a premise. -/
theorem computed_temporal_composition (a : Assignment Owner NativePackageBundle.Value)
    (h : PublicationComposition.Readout (PublicationMaps.exposure a)) :
    ∃ hb : PublicationComposition.Ready (PublicationMaps.exposure a),
      ExecutionLane (PublicationMaps.exposure a) hb ∧
      FullFutureComposition.Laws (sourceFuture (PublicationMaps.exposure a) hb true)
        (targetFuture (PublicationMaps.exposure a) hb false) (SourceClosure (PublicationMaps.exposure a) hb true)
        (translate (PublicationMaps.exposure a) hb false ∘ translate (PublicationMaps.exposure a) hb true)
        (PublicationFuture.image false ∘ PublicationFuture.image true) ∧
      (∀ factor, PublicationCorridor.Readout (native (PublicationMaps.exposure a)) factor) ∧
      (∀ cell, ControllerWins (PublicationMaps.exposure a) hb cell PublicationResources.safeController) ∧
      (∀ cell copy, (NativeClosedPackage.package cell copy).accept (PublicationMaps.exposure a)) ∧
      RawTransportLane (PublicationMaps.exposure a) := by
  obtain ⟨hb,hp,_,he,hf,hc,hw⟩ := h
  exact ⟨hb,he,future_composition _ hb hf,corridor_composition _ hc,hw,hp,exposed_raw_transport a⟩

def Realized (b : Assignment Owner NativePackageBundle.Value) (hb : PublicationComposition.Ready b) (cell : Owner) (h : Factor) : Prop :=
  (NativeClosedPackage.package cell true).accept b ∧ (NativeClosedPackage.package cell false).accept b ∧
  PublicationReceiver.ContentFaithful cell (native b) ∧ ReceiverSquare b hb cell h ∧
  ∃ x, SupportedAcquisitionSequence.firstEntry (raw cell) (native b) (hb.acquisition cell) h h=some x ∧
    entries b hb cell x ∧ Frame.pack ((x ()).1)=targetRoot b hb cell h
def Lineage (b : Assignment Owner NativePackageBundle.Value) (hb : PublicationComposition.Ready b) (cell : Owner) (h : Factor) : Prop :=
  FullFutureComposition.Laws (sourceFuture b hb cell) (targetFuture b hb cell)
    (SourceClosure b hb cell) (translate b hb cell) (PublicationFuture.image cell) ∧
  (∃ l, leg b cell h=some l ∧ AtomicLegPass l) ∧ RawTransportLane b

noncomputable def summary (b : Assignment Owner NativePackageBundle.Value) (hb : PublicationComposition.Ready b)
    (cell : Owner) (h : Factor) : FullHandoffData (Option NativePackageBundle.Bundle) Signature where
  source := (schema cell).source
  target := (schema cell).target
  sourcePackage := (b cell).map (NativePackageBundle.select true)
  targetPackage := (b cell).map (NativePackageBundle.select false)
  entry := entrySignature b hb cell h
  exit := exitSignature b hb cell h
  routeStatus := routeStatus b cell h
  targetOwner := ((targetFuture b hb cell).observe (targetRoot b hb cell h)).owner
  realized := Realized b hb cell h
  lineage := Lineage b hb cell h
  autonomous := ControllerWins b hb cell PublicationResources.safeController

theorem actual_leg (cell : Owner) (h : Factor) :
    leg NativePackageBundle.canonical cell h=some (if cell then PublicationCorridor.left h else PublicationCorridor.right h) := by
  unfold leg
  change (PublicationCorridor.chain PublicationResources.assignment h).bind _=_
  rw [PublicationCorridor.actual_chain]
  cases cell <;> rfl
theorem actual_status (cell : Owner) (h : Factor) : routeStatus NativePackageBundle.canonical cell h=.routeIndexed := by
  rw [routeStatus,actual_leg]
  cases cell
  · exact congrArg status (PublicationCorridor.computed_route_status h).2
  · exact congrArg status (PublicationCorridor.computed_route_status h).1

theorem whole_signature_middle (h : Factor) :
    exitSignature NativePackageBundle.canonical canonical_ready true h=
      entrySignature NativePackageBundle.canonical canonical_ready false h := by
  unfold exitSignature entrySignature
  have hr : SupportedAcquisitionSequence.firstEntry (raw true) (native NativePackageBundle.canonical)
      (canonical_ready.acquisition true) h h=some (AcquisitionExecution.initial (raw false)
        (native NativePackageBundle.canonical) (canonical_ready.acquisition false) h) := PublicationReplay.actual_boundary h
  rw [hr]
  have hf : targetFuture NativePackageBundle.canonical canonical_ready true=
      sourceFuture NativePackageBundle.canonical canonical_ready false := PublicationFuture.middle_future
  have hx : targetRoot NativePackageBundle.canonical canonical_ready true h=
      sourceRoot NativePackageBundle.canonical canonical_ready false h := PublicationFuture.middle_root h
  rw [hf,hx,actual_leg,actual_leg]
  simp only [ite_true,Bool.false_eq_true,ite_false,Option.map_some]
  have hj := PublicationCorridor.full_frontier_seam h
  simp only [AdjacentFrontierCheck,decide_eq_true_eq] at hj
  rw [hj.2.1]

theorem actual_target_owner (cell : Owner) (h : Factor) :
    ((targetFuture NativePackageBundle.canonical canonical_ready cell).observe
      (targetRoot NativePackageBundle.canonical canonical_ready cell h)).owner=(schema cell).target := by
  change ((PublicationFuture.targetFuture cell).observe (PublicationFuture.targetRoot cell h)).owner = _
  change (RegisterFuture.observation (PublicationFuture.target cell) NativePackageBundle.canonical
    (PublicationFuture.frameReady cell false) (PublicationFuture.targetRoot cell h)).owner=_
  rw [PublicationFuture.observation_equation]
  simp only [PublicationFuture.targetRoot,PublicationReplay.interpreted_translation,PublicationFuture.source_root,
    PublicationReplay.shifted,Frame.pack,TemporalRuntimeCoherence.observationImage,TemporalFactorRules.observe,
    PublicationFuture.selected_owner,Bool.false_eq_true,ite_false]
  cases cell <;> rfl

theorem actual_realized (cell : Owner) (h : Factor) : Realized NativePackageBundle.canonical canonical_ready cell h := by
  refine ⟨NativeClosedPackage.actual_package cell true,NativeClosedPackage.actual_package cell false,
    PublicationReceiver.actual_content_faithful cell,(canonical_execution.1 cell h),
    ModeExecution.pack (PublicationFuture.targetRoot cell h (),cell),
    PublicationFuture.root_is_actual_entry cell h,PublicationFuture.semantic_root_entry cell h,?_⟩
  rfl
theorem actual_lineage (cell : Owner) (h : Factor) : Lineage NativePackageBundle.canonical canonical_ready cell h := by
  refine ⟨canonical_future.1 cell,⟨if cell then PublicationCorridor.left h else PublicationCorridor.right h,
    actual_leg cell h,?_⟩,?_⟩
  · cases cell
    · exact PublicationCorridor.second_leg_pass h
    · exact PublicationCorridor.first_leg_pass h
  · rw [← PublicationMaps.canonical_exposure]
    exact exposed_raw_transport NativePackageBundle.initial

theorem actual_certificate (cell : Owner) (h : Factor) :
    FullHandoffCertificate (summary NativePackageBundle.canonical canonical_ready cell h) := by
  refine ⟨?_,actual_target_owner cell h,actual_realized cell h,actual_lineage cell h,canonical_controller cell⟩
  change (schema cell).source≠(schema cell).target
  cases cell <;> decide +kernel
theorem actual_interface (h : Factor) :
    FullHandoffCompatible (summary NativePackageBundle.canonical canonical_ready true h)
      (summary NativePackageBundle.canonical canonical_ready false h) := by
  refine ⟨rfl,PublicationFuture.middle_bundle,whole_signature_middle h,actual_target_owner true h,Or.inr ?_⟩
  constructor
  all_goals change routeStatus NativePackageBundle.canonical _ h≠.unresolved
  all_goals rw [actual_status]; decide +kernel

/-- The frozen certificate layer is populated by the actual two-hop raw
construction. The middle signature retains both whole future and physical/event
interfaces; final autonomy uses the unchanged explicit controller. -/
theorem native_full_temporal_composition (h : Factor) :
    Nonempty (FullHandoffCertificate (composeFullHandoffData
      (summary NativePackageBundle.canonical canonical_ready true h)
      (summary NativePackageBundle.canonical canonical_ready false h))) := by
  apply fullTemporalHandoffComposition (actual_certificate true h) (actual_certificate false h) (actual_interface h)
  change (⟨17⟩ : CarrierId)≠⟨101⟩
  decide +kernel

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationReturn
