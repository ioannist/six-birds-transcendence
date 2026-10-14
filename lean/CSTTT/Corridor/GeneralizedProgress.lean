import CSTTT.Corridor.RawDirectSuccessor
namespace CSTTT.CorridorTheory.GeneralizedProgress
open CSTTT.CorridorTheory.AtomicChain CSTTT.CorridorTheory.RawDirectSuccessor

def Strict (a b : Frontier) : Prop :=
  a.order<b.order ∧ a.tick<b.tick ∧ a.progress<b.progress ∧ a.record<b.record

theorem strict_trans {a b c : Frontier} (ab : Strict a b) (bc : Strict b c) : Strict a c := by
  rcases ab with ⟨_,_,_,_⟩
  rcases bc with ⟨_,_,_,_⟩
  constructor
  · omega
  constructor
  · omega
  constructor <;> omega

theorem readout_endpoints (stages : List RawStage) (updates : List ReadoutUpdate)
    (length : updates.length+1=stages.length) (nonempty : updates≠[])
    (checked : ((stages.zip (stages.drop 1)).zip updates).all
      (fun pair => readoutStep pair.1.1 pair.1.2 pair.2)=true) :
    Strict (stages.headD default).frontier (stages.getLastD default).frontier := by
  induction updates generalizing stages with
  | nil => contradiction
  | cons update rest ih =>
    cases stages with
    | nil => simp at length
    | cons first tail =>
      cases tail with
      | nil => simp at length
      | cons second after =>
        simp only [List.drop_succ_cons,List.drop_zero,List.zip_cons_cons,List.all_cons,
          Bool.and_eq_true] at checked
        have firstStep : Strict first.frontier second.frontier :=
          readout_step_strict first second update checked.1
        cases rest with
        | nil =>
          have empty : after=[] := by simpa using length
          subst after
          simpa using firstStep
        | cons next others =>
          have hl : (next::others).length+1=(second::after).length := by
            simp only [List.length_cons] at length ⊢
            omega
          have lastStep := ih (second::after) hl (by simp) checked.2
          simpa using strict_trans firstStep lastStep

theorem overlap_strict (episode : FiniteAtomicLeg) (h : AtomicLegPass episode) :
    Strict (entry episode).frontier (exit episode).frontier := by
  simp only [AtomicLegPass,AtomicLegCheck,Bool.and_eq_true] at h
  have geometry := h.1.1.1.1.1.1.1.1.1
  have readout := h.1.1.2
  simp only [readoutCheck,Bool.and_eq_true,decide_eq_true_eq] at readout
  simp only [decide_eq_true_eq] at geometry
  apply readout_endpoints episode.stages episode.updates readout.1 _ readout.2
  intro empty
  rw [empty] at readout
  have length := readout.1
  have size := geometry.2.1
  simp at length
  omega

theorem every_leg_strict (leg : GeneralizedLeg) (h : legCheck leg=true) :
    Strict (legEntry leg).2 (legExit leg).2 := by
  cases leg with
  | overlap episode => exact overlap_strict episode h
  | direct raw boundary input => exact direct_strict_temporal_steps raw boundary input h

theorem path_strict {a b : Signature} (path : GeneralizedPath a b) : Strict a.2 b.2 := by
  induction path with
  | one leg checked => exact every_leg_strict leg checked
  | append left right hl hr => exact strict_trans hl hr

theorem no_closed_path (a : Signature) : ¬ Nonempty (GeneralizedPath a a) := by
  rintro ⟨path⟩
  have h := (path_strict path).2.2.1
  omega

end CSTTT.CorridorTheory.GeneralizedProgress
