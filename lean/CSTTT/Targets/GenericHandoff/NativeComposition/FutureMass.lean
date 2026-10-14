import CSTTT.Targets.GenericHandoff.NativeComposition.ObjecthoodProbe
import CSTTT.Targets.GenericHandoff.NativeComposition.ExposureRepair

namespace CSTTT.TargetTheory.GenericHandoff.NativeObservedFutureRulesPrototype
set_option autoImplicit false
variable {S A : Type}

-- A raw weighted transition law, with observation after each actual action.
def mass (rows : S → A → List (S × Nat)) (observe : S → Nat) : S → List A → List Nat → Nat
  | _,[],[] => 1
  | _,[],_::_ => 0
  | _,_::_,[] => 0
  | state,action::rest,obs::observations =>
    (rows state action).foldr (fun edge acc =>
      (if observe edge.1=obs then edge.2*mass rows observe edge.1 rest observations else 0)+acc) 0

theorem weighted_fold_constant (row : List (S × Nat)) (k : Nat) :
    row.foldr (fun edge acc => edge.2*k+acc) 0=(row.map Prod.snd).sum*k := by
  induction row with
  | nil => simp
  | cons edge rest ih =>
    simp only [List.foldr_cons,List.map_cons,List.sum_cons,ih,Nat.add_mul]

theorem foldr_no_emissions (row : List (S × Nat)) :
    row.foldr (fun _ acc => acc) 0=0 := by
  induction row with
  | nil => rfl
  | cons edge rest ih => exact ih

theorem constant_observation_exact (rows : S → A → List (S × Nat)) (observe : S → Nat)
    (scale constant : Nat) (rowTotal : ∀ s a,((rows s a).map Prod.snd).sum=scale)
    (observed : ∀ s,observe s=constant) (state : S) (word : List A) (outputs : List Nat) :
    mass rows observe state word outputs=
      if outputs=List.replicate word.length constant then scale^word.length else 0 := by
  induction word generalizing state outputs with
  | nil => cases outputs <;> simp [mass]
  | cons action rest ih =>
    cases outputs with
    | nil => simp [mass]
    | cons obs tail =>
      simp only [mass,observed,ih]
      by_cases first : constant=obs
      · subst obs
        simp only [ite_true,weighted_fold_constant,rowTotal]
        by_cases same : tail=List.replicate rest.length constant
        · simp [same,List.replicate_succ,Nat.pow_succ,Nat.mul_comm]
        · simp [same,List.replicate_succ]
      · simp [first,List.replicate_succ,Ne.symm first,foldr_no_emissions]

theorem constant_observation_all_initial (rows : S → A → List (S × Nat)) (observe : S → Nat)
    (scale constant : Nat) (rowTotal : ∀ s a,((rows s a).map Prod.snd).sum=scale)
    (observed : ∀ s,observe s=constant) (s t : S) (word : List A) (outputs : List Nat) :
    mass rows observe s word outputs=mass rows observe t word outputs := by
  rw [constant_observation_exact rows observe scale constant rowTotal observed,
    constant_observation_exact rows observe scale constant rowTotal observed]

end CSTTT.TargetTheory.GenericHandoff.NativeObservedFutureRulesPrototype
