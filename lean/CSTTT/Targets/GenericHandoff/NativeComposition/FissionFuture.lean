import CSTTT.Targets.GenericHandoff.NativeComposition.FissionNames

/-! Full futures are computed by mapping the actual raw owner expression.
The entire source model remains shared. The target sufficiency theorem and
all-word returns do not restrict the horizon or discard zero-weight outcomes. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
open RegisterInterpreter PublicationReplay CSTTT.TransportTheory
local instance : DecidableEq PublicationFuture.Observation := instDecidableEqTemporalSnapshotReadout

theorem rename_owner_injective (branch : Bool) : Function.Injective (renameOwner branch) := by
  intro x y h
  simpa only [rename_owner_involution] using congrArg (renameOwner branch) h

abbrev targetRaw (branch : Bool) :=
  OwnerRelabel.renamedRaw (renameOwner branch) (PublicationFuture.target true)
noncomputable def targetFuture (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) := RegisterFuture.future (targetRaw branch) b (hb.future true false)

theorem target_ready_iff (branch : Bool) (b : Assignment Owner NativePackageBundle.Value) :
    RegisterFuture.RawReady (targetRaw branch) b ↔ (b true).isSome=true :=
  (OwnerRelabel.ready_iff _ _ b).trans (NativePackageFuture.ready_iff true false _ _ b)

theorem target_observation (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) (x : Frame.Registers) :
    (targetFuture branch b hb).observe x=
      renameObservation branch ((PublicationComposition.targetFuture b hb true).observe x) :=
  OwnerRelabel.observation_equation (renameOwner branch) (PublicationFuture.target true) b (hb.future true false) x

theorem target_weight (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) (x : Frame.Registers) (a : Unit × Bool) (o : Factor) :
    (targetFuture branch b hb).weight x a o=(PublicationComposition.targetFuture b hb true).weight x a o := rfl
theorem target_next (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) (x : Frame.Registers) (a : Unit × Bool) (o : Factor) :
    (targetFuture branch b hb).next x a o=(PublicationComposition.targetFuture b hb true).next x a o := rfl

theorem target_laws (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) (parent : PublicationComposition.FutureLane b hb) :
    FullFutureComposition.Laws (PublicationComposition.sourceFuture b hb true) (targetFuture branch b hb)
      (PublicationComposition.SourceClosure b hb true) (PublicationComposition.translate b hb true)
      (renameObservation branch ∘ PublicationFuture.image true) :=
  OwnerRelabel.transport_laws _ _ _ _ _ _ _ _ (rename_owner_injective branch) (parent.1 true)

theorem target_independently_sufficient (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) (parent : PublicationComposition.FutureLane b hb) :
    FullFutureSufficient (targetFuture branch b hb) :=
  OwnerRelabel.independently_sufficient _ _ (rename_owner_injective branch)
    (rename_owner_involution branch) _ _ _ (parent.2.1 true false)

theorem all_words (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) (parent : PublicationComposition.FutureLane b hb)
    (x : Frame.Registers) (hx : PublicationComposition.SourceClosure b hb true x)
    (word : List (Unit × Bool)) (trace : List PublicationFuture.Observation) :
    fullFuture (targetFuture branch b hb) (PublicationComposition.translate b hb true x) word
      (trace.map (renameObservation branch ∘ PublicationFuture.image true))=
      fullFuture (PublicationComposition.sourceFuture b hb true) x word trace :=
  FullFutureComposition.all_words _ _ _ _ _ (target_laws branch b hb parent) x hx word trace

theorem canonical_target_owner (branch : Bool) (x : Frame.Registers) :
    ((targetFuture branch NativePackageBundle.canonical PublicationComposition.canonical_ready).observe x).owner=
      (⟨branchTarget branch⟩ : CarrierId) := by
  rw [target_observation]
  change renameOwner branch (RegisterFuture.observation (PublicationFuture.target true)
    NativePackageBundle.canonical (PublicationFuture.frameReady true false) x).owner=_
  rw [PublicationFuture.observation_equation]
  cases branch <;> rfl

theorem canonical_swap_observation (branch : Bool) (x : Frame.Registers) :
    (targetFuture (!branch) NativePackageBundle.canonical PublicationComposition.canonical_ready).observe x=
      swapObservation ((targetFuture branch NativePackageBundle.canonical PublicationComposition.canonical_ready).observe x) := by
  rw [target_observation,target_observation]
  change renameObservation (!branch) (RegisterFuture.observation (PublicationFuture.target true)
    NativePackageBundle.canonical (PublicationFuture.frameReady true false) x)=
      swapObservation (renameObservation branch (RegisterFuture.observation (PublicationFuture.target true)
        NativePackageBundle.canonical (PublicationFuture.frameReady true false) x))
  rw [PublicationFuture.observation_equation]
  cases branch <;> rfl

theorem canonical_swap_laws (branch : Bool) :
    FullFutureComposition.Laws (targetFuture branch NativePackageBundle.canonical PublicationComposition.canonical_ready)
      (targetFuture (!branch) NativePackageBundle.canonical PublicationComposition.canonical_ready)
      (fun _ => True) id swapObservation := by
  refine ⟨rfl,swap_observation_injective,(by intros; trivial),?_,?_,?_⟩
  · intro x _; exact canonical_swap_observation branch x
  · intro x _ a o; rfl
  · intro x _ a o; rfl

theorem canonical_swap_all_words (branch : Bool) (x : Frame.Registers) (word : List (Unit × Bool))
    (trace : List PublicationFuture.Observation) :
    fullFuture (targetFuture (!branch) NativePackageBundle.canonical PublicationComposition.canonical_ready) x word
      (trace.map swapObservation)=
      fullFuture (targetFuture branch NativePackageBundle.canonical PublicationComposition.canonical_ready) x word trace :=
  FullFutureComposition.all_words _ _ _ _ _ (canonical_swap_laws branch) x trivial word trace

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
