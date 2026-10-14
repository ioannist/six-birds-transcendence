import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationMaps
import CSTTT.Targets.GenericHandoff.FullFutureComposition

/-! A shared-assignment return for the repaired two-hop construction. Every
model, root, translation, game and corridor below is interpreted from the same
bundle assignment. Readiness stores proofs of consumed dependencies only.
The original literal-history and static-presence parents remain unchanged. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationComposition
open RegisterInterpreter CSTTT.TransportTheory PublicationReplay
local instance : DecidableEq PublicationFuture.Observation := instDecidableEqTemporalSnapshotReadout

abbrev native (b : Assignment Owner NativePackageBundle.Value) := NativePackageBundle.nativeInputs b
structure Ready (b : Assignment Owner NativePackageBundle.Value) : Prop where
  acquisition : ∀ cell, AcquisitionExecution.Ready (raw cell) (native b)
  resources : ∀ cell, ResourceRuntime.Ready (PublicationResources.runtime cell) (native b)
  future : ∀ cell copy, RegisterFuture.RawReady (PublicationFuture.frame cell copy) b
  translation : ∀ cell, RegisterSubstitution.Ready (PublicationReplay.translation cell) b

theorem ready_iff (b : Assignment Owner NativePackageBundle.Value) : Ready b ↔ ∀ cell, (b cell).isSome=true := by
  constructor
  · intro hb cell
    exact (NativePackageFuture.ready_iff cell true _ _ b).mp (hb.future cell true)
  · intro present
    have hn : ∀ cell, (native b cell).isSome=true := by
      intro cell
      cases he : b cell with
      | none => have hp := present cell; simp [he] at hp
      | some p => simp [native,NativePackageBundle.nativeInputs,he]
    refine ⟨?_,?_,?_,?_⟩
    · intro cell; exact ModeExecution.acquisition_ready _ _ _ _ _ (hn cell)
    · intro cell; exact (PublicationResources.ready_iff cell _).mpr (hn cell)
    · intro cell copy; exact (NativePackageFuture.ready_iff cell copy _ _ b).mpr (present cell)
    · intro cell; exact (PublicationReplay.translation_ready_iff cell b).mpr (present cell)

noncomputable def sourceFuture (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) (cell : Owner) :=
  RegisterFuture.future (PublicationFuture.source cell) b (hb.future cell true)
noncomputable def targetFuture (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) (cell : Owner) :=
  RegisterFuture.future (PublicationFuture.target cell) b (hb.future cell false)
noncomputable def sourceRoot (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) (cell : Owner) (h : Factor) :=
  Frame.pack ((AcquisitionExecution.initial (raw cell) (native b) (hb.acquisition cell) h ()).1)
noncomputable def translate (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) (cell : Owner) (x : Frame.Registers) :=
  RegisterSubstitution.translate (PublicationReplay.translation cell) b (hb.translation cell) x ()
noncomputable def targetRoot (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) (cell : Owner) (h : Factor) :=
  translate b hb cell (sourceRoot b hb cell h)
abbrev SourceClosure (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) (cell : Owner) :=
  RegisterFuture.Closure (PublicationFuture.source cell) b (hb.future cell true) (factors.map (sourceRoot b hb cell))
abbrev TargetClosure (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) (cell : Owner) :=
  RegisterFuture.Closure (PublicationFuture.target cell) b (hb.future cell false) (factors.map (targetRoot b hb cell))

def FutureLane (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) : Prop :=
  (∀ cell, FullFutureComposition.Laws (sourceFuture b hb cell) (targetFuture b hb cell)
    (SourceClosure b hb cell) (translate b hb cell) (PublicationFuture.image cell)) ∧
  (∀ cell copy, FullFutureSufficient (RegisterFuture.future (PublicationFuture.frame cell copy) b (hb.future cell copy))) ∧
  targetFuture b hb true=sourceFuture b hb false ∧
  (∀ h, targetRoot b hb true h=sourceRoot b hb false h) ∧
  (∀ x, SourceClosure b hb true x → SourceClosure b hb false (translate b hb true x))

def packageAt (b : Assignment Owner NativePackageBundle.Value) (cell : Owner) (x : ModeExecution.Registers) : Prop :=
  (NativeClosedPackage.package cell false).accept b ∧
    ResourceRuntime.Inside (PublicationResources.cfg cell) (PublicationResources.runtime cell) (native b) x ∧
    PublicationNominal.PassAt cell (native b) x
def entries (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) (cell : Owner) :=
  AcquisitionExecution.Entry (schema cell) (raw cell) (native b) (hb.acquisition cell)
def ControllerWins (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) (cell : Owner)
    (controller : StrategyGame.Strategy ModeExecution.Registers Unit Bool) : Prop :=
  (ResourceRuntime.DomainCheck (PublicationResources.cfg cell) (PublicationResources.runtime cell) ∧
    ResourceRuntime.WithdrawalCheck (PublicationResources.cfg cell) (PublicationResources.runtime cell) (native b)) ∧
  (∃ x, entries b hb cell x) ∧
  ∀ entry, entries b hb cell entry → ∀ x past,
    StrategyGame.Play (ResourceRuntime.rows (PublicationResources.runtime cell) (native b))
      (ResourceRuntime.update (PublicationResources.runtime cell) (native b) (hb.resources cell))
      controller entry (x::past) →
    packageAt b cell x ∧ ResourceRuntime.ResourceClosed (PublicationResources.cfg cell)
      (PublicationResources.runtime cell) (native b) x ∧
    ∀ d, ResourceRuntime.Legal (PublicationResources.cfg cell) (PublicationResources.runtime cell)
      (native b) x d (controller (x::past) d) ∧
      StrategyGame.Normalized (ResourceRuntime.rows (PublicationResources.runtime cell) (native b)) x d (controller (x::past) d) ∧
      ∀ o, StrategyGame.PositiveSupport (ResourceRuntime.rows (PublicationResources.runtime cell) (native b))
        x d (controller (x::past) d) o → ResourceRuntime.StepLaw (PublicationResources.cfg cell)
          (PublicationResources.runtime cell) (native b) (hb.resources cell) x d (controller (x::past) d) o

def receiverInput (x : ModeExecution.Registers) (h : Factor) : PublicationReceiver.Input :=
  ⟨(x ()).1.factor,(x ()).1.counter,(x ()).1.ticks,(x ()).1.residue.1,(x ()).1.residue.2,h,h⟩
def ReceiverSquare (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) (cell : Owner) (h : Factor) : Prop :=
  ∃ terminal, EpisodeExecution.sourceTerminal (raw cell) (native b) (hb.acquisition cell) h=some terminal ∧
    PublicationReceiver.receive cell (native b) (receiverInput terminal h)=
      some (AcquisitionExecution.receive (raw cell) (native b) (hb.acquisition cell) terminal h h ())
def ExecutionLane (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) : Prop :=
  (∀ cell h, ReceiverSquare b hb cell h) ∧
  ∀ h, ∃ middle final,
    SupportedAcquisitionSequence.firstEntry (raw true) (native b) (hb.acquisition true) h h=some middle ∧
    middle=AcquisitionExecution.initial (raw false) (native b) (hb.acquisition false) h ∧
    SupportedAcquisitionSequence.nextEntry (raw true) (raw false) PublicationSequence.boundary (native b)
      (hb.acquisition true) (hb.acquisition false) (PublicationSequence.boundary_ready (native b)) h h h h=some final ∧
    entries b hb true middle ∧ entries b hb false final ∧
    Frame.pack ((middle ()).1)=targetRoot b hb true h ∧ Frame.pack ((final ()).1)=targetRoot b hb false h

def CorridorLane (b : Assignment Owner NativePackageBundle.Value) : Prop :=
  ∀ h, ∃ seed left right,
    PublicationCorridor.middle (native b) h=some true ∧
    PublicationCorridor.initialSeed (native b) h=some seed ∧
    PublicationCorridor.episode true (native b) h seed=some left ∧
    PublicationCorridor.episode false (native b) h (CSTTT.CorridorTheory.AtomicChain.exit left).frontier.residue=some right ∧
    CSTTT.CorridorTheory.AtomicChain.AtomicLegPass left ∧ CSTTT.CorridorTheory.AtomicChain.AtomicLegPass right ∧
    CSTTT.CorridorTheory.AtomicChain.AdjacentFrontierCheck left right=true ∧ left.source≠right.target

theorem corridor_composition (b : Assignment Owner NativePackageBundle.Value) (hc : CorridorLane b) (h : Factor) :
    PublicationCorridor.Readout (native b) h := by
  obtain ⟨seed,left,right,hm,hs,hl,hr,hpl,hpr,hj,hd⟩ := hc h
  refine ⟨[left,right],?_,?_⟩
  · simp [PublicationCorridor.chain,hm,hs,hl,hr]
  · apply CSTTT.CorridorTheory.AtomicChain.strictTemporalCorridorComposition_generic
    refine ⟨by simp,?_,?_⟩
    · simpa only [CSTTT.CorridorTheory.AtomicChain.chainCheck,Bool.and_eq_true] using ⟨⟨hpl,hj⟩,hpr⟩
    · simpa only [List.head?_cons,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.getD_some,
        Option.map_some,ne_eq,Option.some.injEq] using hd

/-- Full structural lane checks on interpreted objects, with an explicit
controller shared by intermediate and final targets. No derived verdict is a
primitive field. The C4--C7 grades are those of NativeClosedPackage. -/
def Readout (b : Assignment Owner NativePackageBundle.Value) : Prop :=
  ∃ hb : Ready b,
    (∀ cell copy, (NativeClosedPackage.package cell copy).accept b) ∧
    (∀ cell, PublicationReceiver.ContentFaithful cell (native b)) ∧
    ExecutionLane b hb ∧ FutureLane b hb ∧
    CorridorLane b ∧
    ∀ cell, ControllerWins b hb cell PublicationResources.safeController

theorem controller_game (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b) (cell : Owner)
    (controller : StrategyGame.Strategy ModeExecution.Registers Unit Bool)
    (hw : ControllerWins b hb cell controller) :
    StrategyGame.GameReadout (ResourceRuntime.rows (PublicationResources.runtime cell) (native b))
      (ResourceRuntime.update (PublicationResources.runtime cell) (native b) (hb.resources cell))
      (entries b hb cell)
      (ResourceRuntime.DomainCheck (PublicationResources.cfg cell) (PublicationResources.runtime cell) ∧
        ResourceRuntime.WithdrawalCheck (PublicationResources.cfg cell) (PublicationResources.runtime cell) (native b))
      (packageAt b cell) (ResourceRuntime.ResourceClosed (PublicationResources.cfg cell) (PublicationResources.runtime cell) (native b))
      (ResourceRuntime.Legal (PublicationResources.cfg cell) (PublicationResources.runtime cell) (native b))
      (ResourceRuntime.StepLaw (PublicationResources.cfg cell) (PublicationResources.runtime cell) (native b) (hb.resources cell)) :=
  ⟨hw.1,hw.2.1,controller,hw.2.2⟩

theorem future_composition (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b)
    (hf : FutureLane b hb) :
    FullFutureComposition.Laws (sourceFuture b hb true) (targetFuture b hb false) (SourceClosure b hb true)
      (translate b hb false ∘ translate b hb true) (PublicationFuture.image false ∘ PublicationFuture.image true) := by
  apply FullFutureComposition.compose (sourceFuture b hb true) (targetFuture b hb true) (targetFuture b hb false)
    (SourceClosure b hb true) (SourceClosure b hb false)
  · exact hf.1 true
  · rw [hf.2.2.1]; exact hf.1 false
  · exact hf.2.2.2.2

theorem all_word_composition (b : Assignment Owner NativePackageBundle.Value) (hb : Ready b)
    (hf : FutureLane b hb) (x : Frame.Registers) (hx : SourceClosure b hb true x)
    (word : List (Unit × Bool)) (trace : List PublicationFuture.Observation) :
    fullFuture (targetFuture b hb false) (translate b hb false (translate b hb true x)) word
      (trace.map (PublicationFuture.image false ∘ PublicationFuture.image true))=
      fullFuture (sourceFuture b hb true) x word trace :=
  FullFutureComposition.all_words _ _ _ _ _ (future_composition b hb hf) x hx word trace

theorem missing_readout (b : Assignment Owner NativePackageBundle.Value) (cell : Owner) (hm : b cell=none) :
    ¬ Readout b := by
  rintro ⟨_,_,hr,_⟩
  exact PublicationReceiver.missing_not_faithful cell (native b) (by simp [native,NativePackageBundle.nativeInputs,hm]) (hr cell)

def cutReceiver (cell : Owner) (b : Assignment Owner NativePackageBundle.Value) : Assignment Owner NativePackageBundle.Value :=
  fun o => if o=cell then (b o).map (fun p =>
    ({p.1 with native := {p.1.native with receiver := {p.1.native.receiver with sourcePresent := false}}},p.2)) else b o
theorem cut_receiver_native (cell : Owner) (b : Assignment Owner NativePackageBundle.Value) :
    native (cutReceiver cell b)=PublicationReceiver.cutAt cell (native b) := by
  funext o
  by_cases he : o=cell
  · subst o
    simp [native,cutReceiver,NativePackageBundle.nativeInputs,PublicationReceiver.cutAt,Option.map_map,
      Function.comp_def,PublicationReceiver.cutSource]
  · simp [native,cutReceiver,NativePackageBundle.nativeInputs,PublicationReceiver.cutAt,he]
theorem cut_receiver_copied_source (cell o : Owner) (b : Assignment Owner NativePackageBundle.Value) :
    (cutReceiver cell b o).map Prod.snd=(b o).map Prod.snd := by
  by_cases he : o=cell
  · simp [cutReceiver,he,Option.map_map,Function.comp_def]
  · simp [cutReceiver,he]
theorem cut_receiver_no_readout (cell : Owner) (b : Assignment Owner NativePackageBundle.Value) :
    ¬ Readout (cutReceiver cell b) := by
  rintro ⟨_,_,hr,_⟩
  have hc := hr cell
  rw [cut_receiver_native] at hc
  exact PublicationReceiver.cut_at_not_faithful cell (native b) hc

theorem failed_corridor_no_readout (b : Assignment Owner NativePackageBundle.Value) (h : Factor)
    (hn : ¬ PublicationCorridor.Readout (native b) h) : ¬ Readout b := by
  rintro ⟨_,_,_,_,_,hc,_⟩
  exact hn (corridor_composition b hc h)

theorem exposed_missing (a : Assignment Owner NativePackageBundle.Value) (hm : a false=none) :
    ¬ Readout (PublicationMaps.exposure a) := by
  apply missing_readout _ true
  rw [PublicationMaps.exposure_equation]
  simp [NativePackageBundle.staged,NativePackageBundle.image,swapOwner,hm]

theorem canonical_ready : Ready NativePackageBundle.canonical :=
  ⟨PublicationReplay.ready,PublicationResources.ready,PublicationFuture.frameReady,PublicationReplay.mapReady⟩
theorem canonical_future : FutureLane NativePackageBundle.canonical canonical_ready := by
  refine ⟨?_,PublicationFuture.independently_sufficient,PublicationFuture.middle_future,PublicationFuture.middle_root,?_⟩
  · intro cell
    refine ⟨rfl,PublicationFuture.image_injective cell,?_,PublicationFuture.future_observation cell,
      (fun x _ => PublicationFuture.future_weight cell x),
      (fun x _ => PublicationFuture.future_next cell x)⟩
    intro x hx a o ho
    exact PublicationFuture.future_closure_next cell x hx a o
  · intro x hx
    exact PublicationFuture.middle_closure _ (PublicationFuture.translated_closure true x hx)

theorem canonical_controller (cell : Owner) :
    ControllerWins NativePackageBundle.canonical canonical_ready cell PublicationResources.safeController := by
  refine ⟨⟨PublicationResources.domain cell,PublicationResources.withdrawal_check cell⟩,
    PublicationResources.entries_nonempty cell,?_⟩
  intro entry he x past hp
  have hx := PublicationResources.every_safe_play_inside cell entry he _ hp x past rfl
  have hpackage := PublicationResources.package_inside cell x hx
  refine ⟨⟨hpackage.1,hpackage.2,PublicationNominal.every_safe_play_pass cell entry he x past hp⟩,?_,?_⟩
  · obtain ⟨h,time,rfl⟩ := hx
    exact PublicationResources.target_resource_closed cell h time
  · intro d; cases d
    obtain ⟨h,time,rfl⟩ := hx
    refine ⟨PublicationResources.target_legal cell h time,PublicationResources.target_normalized cell h time,?_⟩
    intro o ho
    have he := (PublicationResources.target_positive_unique cell h o time).mp ho
    subst o
    exact PublicationResources.target_step_law cell h time

theorem canonical_execution : ExecutionLane NativePackageBundle.canonical canonical_ready := by
  constructor
  · intro cell h
    refine ⟨PublicationPhysical.terminalRun cell h,PublicationPhysical.source_terminal cell h,?_⟩
    have hi : receiverInput (PublicationPhysical.terminalRun cell h) h=PublicationReceiver.terminalInput cell h := rfl
    rw [hi]
    exact PublicationReceiver.actual_receiver_square cell h
  · intro h
    refine ⟨PublicationPhysical.entryRun true h,PublicationPhysical.entryRun false h,
      PublicationPhysical.actual_entry true h,PublicationSequence.physical_middle h,
      PublicationSequence.next_entry h,?_,PublicationSequence.next_semantic_entry h,?_,?_⟩
    · exact PublicationExecution.first_semantic_entry (PublicationReplay.ready true) h
    · have hx := Option.some.inj ((PublicationPhysical.actual_entry true h).symm.trans
        (PublicationFuture.root_is_actual_entry true h))
      exact congrArg (fun y : ModeExecution.Registers => Frame.pack ((y ()).1)) hx
    · have hx := Option.some.inj ((PublicationPhysical.actual_entry false h).symm.trans
        (PublicationFuture.root_is_actual_entry false h))
      exact congrArg (fun y : ModeExecution.Registers => Frame.pack ((y ()).1)) hx

theorem canonical_corridor : CorridorLane NativePackageBundle.canonical := by
  intro h
  refine ⟨PublicationCorridor.seed h,PublicationCorridor.left h,PublicationCorridor.right h,
    PublicationCorridor.actual_middle h,PublicationCorridor.actual_seed h,?_,?_,
    PublicationCorridor.first_leg_pass h,PublicationCorridor.second_leg_pass h,
    PublicationCorridor.full_frontier_seam h,?_⟩
  · exact PublicationCorridor.actual_episode true h _
  · exact PublicationCorridor.actual_episode false h _
  · change (17 : Nat)≠101; decide +kernel

theorem canonical_readout : Readout NativePackageBundle.canonical :=
  ⟨canonical_ready,NativeClosedPackage.actual_package,PublicationReceiver.actual_content_faithful,
    canonical_execution,canonical_future,canonical_corridor,canonical_controller⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationComposition
