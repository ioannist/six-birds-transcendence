import CSTTT.Targets.GenericHandoff.NativeComposition.FissionReturn
import CSTTT.Corridor.FissionClosure

/-! The continuation relation is derived from whole executed certificates.
The exact entire continuation set is the two certified targets. The primitive
fork is fixed by branch exchange, and the named whole futures are exchanged by
the target involution. Selection without an invariance demand remains possible. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
open RegisterInterpreter PublicationReplay CSTTT.TransportTheory CSTTT.CorridorTheory

def ValidTarget (r : Raw) (target : CarrierId) : Prop :=
  ∃ hr : Ready r, ∃ branch : Bool,
    Readout r ∧ target=(⟨branchTarget branch⟩ : CarrierId) ∧
      ∀ h, Nonempty (FullHandoffCertificate (summary r hr branch h))
def Continuation (r : Raw) (source target : CarrierId) : Prop := source=(⟨17⟩ : CarrierId) ∧ ValidTarget r target

theorem valid_target_iff (r : Raw) (target : CarrierId) :
    ValidTarget r target ↔ Readout r ∧ (target=(⟨201⟩ : CarrierId) ∨ target=(⟨202⟩ : CarrierId)) := by
  constructor
  · rintro ⟨_,branch,hr,ht,_⟩
    cases branch
    · exact ⟨hr,Or.inl ht⟩
    · exact ⟨hr,Or.inr ht⟩
  · rintro ⟨h,ht⟩
    obtain ⟨hr,hc,_⟩ := computed_full_fork r h
    rcases ht with rfl | rfl
    · exact ⟨hr,false,h,rfl,hc false⟩
    · exact ⟨hr,true,h,rfl,hc true⟩
theorem continuation_iff (r : Raw) (source target : CarrierId) :
    Continuation r source target ↔ source=(⟨17⟩ : CarrierId) ∧ Readout r ∧
      (target=(⟨201⟩ : CarrierId) ∨ target=(⟨202⟩ : CarrierId)) := by
  simp only [Continuation,valid_target_iff]

theorem swap_left : swapOwner (⟨201⟩ : CarrierId)=(⟨202⟩ : CarrierId) := rfl
theorem swap_right : swapOwner (⟨202⟩ : CarrierId)=(⟨201⟩ : CarrierId) := rfl
theorem target_swap_preserves_validity (r : Raw) (target : CarrierId) :
    ValidTarget r (swapOwner target) ↔ ValidTarget r target := by
  constructor
  · intro h
    obtain ⟨hr,ht⟩ := (valid_target_iff r _).mp h
    apply (valid_target_iff r _).mpr
    refine ⟨hr,?_⟩
    rcases ht with ht | ht
    · exact Or.inr (by simpa only [swap_owner_involution,swap_left] using congrArg swapOwner ht)
    · exact Or.inl (by simpa only [swap_owner_involution,swap_right] using congrArg swapOwner ht)
  · intro h
    obtain ⟨hr,ht⟩ := (valid_target_iff r _).mp h
    apply (valid_target_iff r _).mpr
    refine ⟨hr,?_⟩
    rcases ht with rfl | rfl
    · exact Or.inr swap_left
    · exact Or.inl swap_right
theorem target_swap_preserves_continuation (r : Raw) (source target : CarrierId) :
    Continuation r source (swapOwner target) ↔ Continuation r source target := by
  simp only [Continuation,target_swap_preserves_validity]

def InvariantSingleton (r : Raw) : Prop :=
  ∃ selected, Continuation r (⟨17⟩ : CarrierId) selected ∧ swapOwner selected=selected
theorem no_invariant_singleton (r : Raw) : ¬InvariantSingleton r := by
  rintro ⟨selected,hc,hfixed⟩
  obtain ⟨_,_,ht⟩ := (continuation_iff r _ _).mp hc
  rcases ht with rfl | rfl
  · have hn : (⟨202⟩ : CarrierId)≠⟨201⟩ := by decide +kernel
    exact hn hfixed
  · have hn : (⟨201⟩ : CarrierId)≠⟨202⟩ := by decide +kernel
    exact hn hfixed

def exchange (r : Raw) : Raw := ⟨fun branch => r.initial (!branch),fun branch => r.cutCurrentSource (!branch)⟩
theorem exchange_involution (r : Raw) : exchange (exchange r)=r := by
  cases r
  simp only [exchange,Bool.not_not]
theorem canonical_primitive_symmetry : exchange canonicalRaw=canonicalRaw := rfl
theorem no_equivariant_selector (select : Raw → CarrierId)
    (valid : Continuation canonicalRaw (⟨17⟩ : CarrierId) (select canonicalRaw))
    (equivariant : ∀ r, select (exchange r)=swapOwner (select r)) : False := by
  have he := equivariant canonicalRaw
  rw [canonical_primitive_symmetry] at he
  exact no_invariant_singleton canonicalRaw ⟨select canonicalRaw,valid,he.symm⟩

def fork : TemporalFissionData CarrierId CarrierId where
  source := ⟨17⟩
  left := ⟨201⟩
  right := ⟨202⟩
  related := Continuation canonicalRaw
  valid := ValidTarget canonicalRaw
  swap := swapOwner
theorem native_fission_certificate : TemporalFissionCertificate fork := by
  have left : ValidTarget canonicalRaw (⟨201⟩ : CarrierId) :=
    (valid_target_iff _ _).mpr ⟨canonical_readout,Or.inl rfl⟩
  have right : ValidTarget canonicalRaw (⟨202⟩ : CarrierId) :=
    (valid_target_iff _ _).mpr ⟨canonical_readout,Or.inr rfl⟩
  exact ⟨by decide +kernel,⟨rfl,left⟩,⟨rfl,right⟩,left,right,swap_left,swap_right⟩

/-- Frozen TTH-08 return: two actual autonomous full handoffs, exact whole
continuation set, whole-source sharing and an invariant-selector obstruction. -/
theorem native_relation_valued_temporal_fission :
    fork.related fork.source fork.left ∧ fork.related fork.source fork.right ∧
    (∀ target, fork.valid target ↔ target=fork.left ∨ target=fork.right) ∧
    (∀ target, fork.valid (fork.swap target) ↔ fork.valid target) ∧
    (∀ target, fork.swap (fork.swap target)=target) ∧ ¬InvariantSingleton canonicalRaw := by
  refine ⟨native_fission_certificate.leftRelated,native_fission_certificate.rightRelated,?_,
    target_swap_preserves_validity canonicalRaw,swap_owner_involution,no_invariant_singleton canonicalRaw⟩
  intro target
  simpa only [fork,true_and] using
    (valid_target_iff canonicalRaw target).trans (and_iff_right canonical_readout)

theorem constant_choice_is_valid : Continuation canonicalRaw (⟨17⟩ : CarrierId) (⟨201⟩ : CarrierId) :=
  native_fission_certificate.leftRelated
theorem constant_choice_is_not_invariant : swapOwner (⟨201⟩ : CarrierId)≠⟨201⟩ := by decide +kernel
theorem outside_target_is_not_a_continuation (target : CarrierId)
    (h201 : target≠⟨201⟩) (h202 : target≠⟨202⟩) : ¬Continuation canonicalRaw (⟨17⟩ : CarrierId) target := by
  intro h
  exact ((continuation_iff _ _ _).mp h).2.2.elim h201 h202

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
