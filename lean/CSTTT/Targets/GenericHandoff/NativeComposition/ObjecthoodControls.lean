import CSTTT.Targets.GenericHandoff.NativeComposition.ObjecthoodPublication

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeObjecthoodCells
open RegisterInterpreter ModeExecution

def eraseP (s : Supplement) : Supplement := {s with publishedP := fun _ _ => 0}
def eraseCurrentP (a : Assignment Cell Value) : Assignment Cell Value
  | .inl o => a (.inl o)
  | .inr o => (a (.inr o)).map (fun p => (eraseP p.1,p.2))

theorem erased_native_unchanged (a : Assignment Cell Value) :
    nativeInputs (eraseCurrentP a)=nativeInputs a := rfl
theorem erased_copied_source_unchanged (a : Assignment Cell Value) (o : Owner) :
    (eraseCurrentP a (.inr o)).map (selectSupplement true)=
      (a (.inr o)).map (selectSupplement true) := by
  simp only [eraseCurrentP,Option.map_map]
  rfl

theorem erased_source_decode_unchanged (a : Assignment Cell Value) (o : Owner) :
    ObjecthoodCells.decoded clauseSchema.toSchema (bindings o true) (eraseCurrentP a)=
      ObjecthoodCells.decoded clauseSchema.toSchema (bindings o true) a := by
  rw [decoded,decoded]
  cases hn : a (.inl o) <;> cases hs : a (.inr o) <;>
    simp [eraseCurrentP,hn,hs,selectSupplement]

theorem erased_source_accept_iff (a : Assignment Cell Value) (o : Owner) :
    ObjecthoodProtocol.Accept clauseSchema.toSchema reference (bindings o true) (eraseCurrentP a) ↔
      ObjecthoodProtocol.Accept clauseSchema.toSchema reference (bindings o true) a := by
  simp only [ObjecthoodProtocol.Accept,erased_source_decode_unchanged]

theorem data_round (n : Nat) (s : Supplement) : data (roundInput n) s=data (canonicalInput false) s := by
  induction n with
  | zero => rfl
  | succ n ih => exact (data_publish (roundInput n) s).trans ih

/-- This refutes the actual C1 acceptance, by reconstruction of the actual
probe row, rather than solely disagreeing with a sufficient reference check. -/
theorem erased_actual_raw_rejected (n : Nat) :
    ¬ ObjecthoodRules.Accept (data (roundInput n) (eraseP supplement)) := by
  intro h
  have he := h.1.2.2.1.1 (false,false,false) (false,false,false)
  rw [data_round] at he
  have hp : ObjecthoodRules.P (data (canonicalInput false) (eraseP supplement))
      (false,false,false) (false,false,false)=1 := by decide +kernel
  rw [hp] at he
  change (1:Rat)=0 at he
  have hn : (1:Rat)≠0 := by decide +kernel
  exact hn he

theorem erased_target_actual_accept_rejected (a : Assignment Cell Value) (o : Owner) (n : Nat)
    (hp : a (.inl o)=some (episodePair n))
    (hs : a (.inr o)=some (supplement,supplement)) :
    ¬ ObjecthoodCells.Accept clauseSchema.toSchema (bindings o false) (eraseCurrentP a) := by
  rw [acceptance_iff]
  intro h
  obtain ⟨p,s,hp',hs',ha⟩ := h
  change a (.inl o)=some p at hp'
  have ep := Option.some.inj (hp.symm.trans hp')
  have es : s=(eraseP supplement,supplement) := by
    simpa [eraseCurrentP,hs] using hs'.symm
  subst p
  subst s
  exact erased_actual_raw_rejected (n+1) ha

theorem erased_final_c1_rejected :
    ¬ ObjecthoodProtocol.Accept clauseSchema.toSchema reference (bindings false false)
      (eraseCurrentP (staged initialCanonical)) := by
  rintro ⟨d,hd,ha,_⟩
  exact erased_target_actual_accept_rejected (staged initialCanonical) false 1
    (congrFun canonical_native_exposure false) (canonical_supplement_exposure false) ⟨d,hd,ha⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeObjecthoodCells
