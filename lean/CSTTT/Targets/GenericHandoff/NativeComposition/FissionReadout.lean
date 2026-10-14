import CSTTT.Targets.GenericHandoff.NativeComposition.FissionAutonomy

/-! A fork consumes two branch-indexed primitive placements. Each branch runs
the actual publication map. Cutting its current receiver preserves its whole
copied source, but rejects the actual readout. No certificate or verdict is a
primitive input. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
open RegisterInterpreter PublicationReplay CSTTT.TransportTheory
open CSTTT.CorridorTheory.AtomicChain

structure Raw where
  initial : Bool → Assignment Owner NativePackageBundle.Value
  cutCurrentSource : Bool → Bool
def assignment (r : Raw) (branch : Bool) : Assignment Owner NativePackageBundle.Value :=
  if r.cutCurrentSource branch then PublicationComposition.cutReceiver true (PublicationMaps.exposure (r.initial branch))
  else PublicationMaps.exposure (r.initial branch)
def canonicalRaw : Raw := ⟨fun _ => NativePackageBundle.initial,fun _ => false⟩
theorem canonical_assignment (branch : Bool) : assignment canonicalRaw branch=NativePackageBundle.canonical :=
  PublicationMaps.canonical_exposure

def Ready (r : Raw) : Prop := ∀ branch, PublicationComposition.Ready (assignment r branch)
theorem assignment_presence (r : Raw) (branch cell : Bool) :
    (assignment r branch cell).isSome=(r.initial branch false).isSome := by
  rw [assignment,PublicationMaps.exposure_equation]
  cases hc : r.cutCurrentSource branch <;> cases cell
  all_goals cases hi : r.initial branch false <;>
    simp [PublicationComposition.cutReceiver,NativePackageBundle.staged,NativePackageBundle.image,NativeComposition.swapOwner,hi]
theorem ready_iff (r : Raw) : Ready r ↔ ∀ branch, (r.initial branch false).isSome=true := by
  constructor
  · intro hr branch
    have h := (PublicationComposition.ready_iff _).mp (hr branch) true
    rwa [assignment_presence] at h
  · intro hr branch
    apply (PublicationComposition.ready_iff _).mpr
    intro cell
    rw [assignment_presence]
    exact hr branch

def consumed (r : Raw) : Bool := (r.initial false false).isSome && (r.initial true false).isSome
def decoded (r : Raw) : Option (Bool → Assignment Owner NativePackageBundle.Value) :=
  if consumed r then some (assignment r) else none
theorem consumed_iff (r : Raw) : consumed r=true ↔ Ready r := by
  rw [ready_iff]
  simp only [consumed,Bool.and_eq_true]
  constructor
  · intro h branch
    cases branch
    · exact h.1
    · exact h.2
  · intro h; exact ⟨h false,h true⟩
theorem decoded_iff (r : Raw) : decoded r=some (assignment r) ↔ Ready r := by
  rw [←consumed_iff]
  cases h : consumed r <;> simp [decoded,h]
theorem canonical_ready : Ready canonicalRaw := by
  intro branch
  rw [canonical_assignment]
  exact PublicationComposition.canonical_ready

structure PlacedBundle where
  bundle : NativePackageBundle.Bundle
  names : Owner → CarrierId
def sourcePackage (b : Assignment Owner NativePackageBundle.Value) : Option PlacedBundle :=
  (b true).map (fun p => ⟨p.2,names true⟩)
def targetPackage (branch : Bool) (b : Assignment Owner NativePackageBundle.Value) : Option PlacedBundle :=
  (b true).map (fun p => ⟨p.1,branchNames branch⟩)

def OwnerControl (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) : Prop :=
  ∀ entry, PublicationComposition.entries b hb true entry → ∀ x past,
    StrategyGame.Play (ResourceRuntime.rows (PublicationResources.runtime true) (PublicationComposition.native b))
      (ResourceRuntime.update (PublicationResources.runtime true) (PublicationComposition.native b) (hb.resources true))
      PublicationResources.safeController entry (x::past) →
    (resourceOwnerExpr branch).eval (PublicationComposition.native b) x ()=some (⟨branchTarget branch⟩ : CarrierId) ∧
    (PublicationResources.runtime true).sourcePresent.eval (PublicationComposition.native b) x ()=some false

def LegLane (branch : Bool) (b : Assignment Owner NativePackageBundle.Value) : Prop :=
  ∀ h, ∃ l, PublicationReturn.leg b true h=some l ∧ AtomicLegPass (renameLeg branch l) ∧
    l.source=17 ∧ l.target=55

structure BranchChecks (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) : Prop where
  parent : PublicationComposition.Readout b
  sourceOwner : ∀ x, ((PublicationComposition.sourceFuture b hb true).observe x).owner=(⟨17⟩ : CarrierId)
  targetOwner : ∀ h, ((targetFuture branch b hb).observe (PublicationComposition.targetRoot b hb true h)).owner=
    (⟨branchTarget branch⟩ : CarrierId)
  leg : LegLane branch b
  owners : OwnerControl branch b hb
  autonomy : NamedControllerWins branch b hb

def Readout (r : Raw) : Prop :=
  ∃ hr : Ready r,
    (∀ branch, BranchChecks branch (assignment r branch) (hr branch)) ∧
    sourcePackage (assignment r false)=sourcePackage (assignment r true) ∧
    ∀ h, PublicationReturn.entrySignature (assignment r false) (hr false) true h=
      PublicationReturn.entrySignature (assignment r true) (hr true) true h

theorem current_source_required (r : Raw) (branch : Bool) (h : Readout r) : r.cutCurrentSource branch=false := by
  obtain ⟨hr,hc,_⟩ := h
  have hp := (hc branch).parent
  cases he : r.cutCurrentSource branch
  · rfl
  · have ha : assignment r branch=PublicationComposition.cutReceiver true (PublicationMaps.exposure (r.initial branch)) := by
      simp [assignment,he]
    rw [ha] at hp
    exact False.elim (PublicationComposition.cut_receiver_no_readout _ _ hp)
theorem cut_current_no_readout (r : Raw) (branch : Bool) (h : r.cutCurrentSource branch=true) : ¬Readout r := by
  intro hr
  have hf := current_source_required r branch hr
  rw [h] at hf
  contradiction
theorem whole_copied_source_preserved (r : Raw) (branch cell : Bool) :
    (assignment r branch cell).map Prod.snd=(PublicationMaps.exposure (r.initial branch) cell).map Prod.snd := by
  unfold assignment
  cases hc : r.cutCurrentSource branch
  · rfl
  · exact PublicationComposition.cut_receiver_copied_source true cell _
theorem missing_no_readout (r : Raw) (branch : Bool) (hm : r.initial branch false=none) : ¬Readout r := by
  rintro ⟨hr,_⟩
  have hp := (ready_iff r).mp hr branch
  simp [hm] at hp

theorem canonical_renamed_leg (branch : Bool) (h : Factor) :
    AtomicLegPass (renameLeg branch (PublicationCorridor.left h)) := by
  cases branch
  all_goals unfold AtomicLegPass
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> decide +kernel
theorem canonical_owner_control (branch : Bool) :
    OwnerControl branch NativePackageBundle.canonical PublicationComposition.canonical_ready := by
  intro entry he x past hp
  exact every_safe_play_owner branch entry he x past hp
theorem canonical_branch_checks (branch : Bool) :
    BranchChecks branch NativePackageBundle.canonical PublicationComposition.canonical_ready := by
  refine ⟨PublicationComposition.canonical_readout,?_,?_,?_,canonical_owner_control branch,
    canonical_named_controller branch⟩
  · intro x
    change (RegisterFuture.observation (PublicationFuture.source true) NativePackageBundle.canonical
      (PublicationFuture.frameReady true true) x).owner=_
    rw [PublicationFuture.observation_equation]
    rfl
  · intro h; exact canonical_target_owner branch _
  · intro h
    exact ⟨PublicationCorridor.left h,PublicationReturn.actual_leg true h,canonical_renamed_leg branch h,rfl,rfl⟩
theorem canonical_readout : Readout canonicalRaw := by
  refine ⟨canonical_ready,?_,?_,?_⟩
  · intro branch
    simpa only [canonical_assignment] using canonical_branch_checks branch
  · rw [canonical_assignment,canonical_assignment]
  · intro h
    simp only [canonical_assignment]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
