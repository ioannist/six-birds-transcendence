import CSTTT.Corridor.Fission

namespace CSTTT.CorridorTheory.FissionClosure
open CSTTT.CorridorTheory

def oldFork : TemporalFissionData Unit (Fin 3) where
  source := ()
  left := 0
  right := 1
  related := fun _ _ => True
  valid := fun _ => True
  swap := fun x => if x=0 then 1 else if x=1 then 0 else x

theorem old_fork_certificate : TemporalFissionCertificate oldFork :=
  ⟨by decide, trivial, trivial, trivial, trivial, by decide, by decide⟩

theorem old_certificate_allows_an_invariant_continuer :
    ∃ selected : Fin 3, oldFork.related oldFork.source selected ∧ oldFork.valid selected ∧
      oldFork.swap selected=selected := ⟨2,trivial,trivial,by decide⟩

def PairRelated {S T : Type} (d : TemporalFissionData S T) (s : S) (t : T) : Prop :=
  s=d.source ∧ (t=d.left ∨ t=d.right) ∧ d.related s t ∧ d.valid t
def InvariantSelector {S T : Type} (d : TemporalFissionData S T) : Prop :=
  ∃ selected, PairRelated d d.source selected ∧ d.swap selected=selected

theorem pair_relation_exact {S T : Type} (d : TemporalFissionData S T)
    (h : TemporalFissionCertificate d) (t : T) :
    PairRelated d d.source t ↔ t=d.left ∨ t=d.right := by
  constructor
  · intro ht; exact ht.2.1
  · intro ht
    rcases ht with rfl | rfl
    · exact ⟨rfl,Or.inl rfl,h.leftRelated,h.leftValid⟩
    · exact ⟨rfl,Or.inr rfl,h.rightRelated,h.rightValid⟩

theorem pair_selector_impossible {S T : Type} (d : TemporalFissionData S T)
    (h : TemporalFissionCertificate d) : ¬InvariantSelector d := by
  rintro ⟨selected,ht,hfixed⟩
  rcases (pair_relation_exact d h selected).mp ht with rfl | rfl
  · exact h.targetsDistinct (h.swapLeft.symm.trans hfixed).symm
  · exact h.targetsDistinct (h.swapRight.symm.trans hfixed)

theorem pair_swap_preserves_relation {S T : Type} (d : TemporalFissionData S T)
    (h : TemporalFissionCertificate d) (t : T) :
    PairRelated d d.source t → PairRelated d d.source (d.swap t) := by
  intro ht
  rcases (pair_relation_exact d h t).mp ht with rfl | rfl
  · rw [h.swapLeft]; exact (pair_relation_exact d h d.right).mpr (Or.inr rfl)
  · rw [h.swapRight]; exact (pair_relation_exact d h d.left).mpr (Or.inl rfl)

theorem pair_swap_equivalence {S T : Type} (d : TemporalFissionData S T)
    (h : TemporalFissionCertificate d) (involution : ∀ t, d.swap (d.swap t)=t) (t : T) :
    PairRelated d d.source (d.swap t) ↔ PairRelated d d.source t := by
  constructor
  · intro ht
    simpa only [involution] using pair_swap_preserves_relation d h (d.swap t) ht
  · exact pair_swap_preserves_relation d h t

end CSTTT.CorridorTheory.FissionClosure
