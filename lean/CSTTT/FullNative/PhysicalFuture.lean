import CSTTT.FullNative.PhysicalProfile

namespace CSTTT.FullNative
set_option autoImplicit false
set_option maxHeartbeats 8000000

structure Shape where
  outside : Bool
  u : Bool
  v : Bool
  phase : Bool
  deriving DecidableEq, Repr

def eraseReplica (s : State) : Shape := ⟨s.outside,s.u,s.v,s.phase⟩
def representative (q : Shape) : State := ⟨q.outside,q.u,q.v,false,q.phase⟩

theorem erase_representative (q : Shape) : eraseReplica (representative q) = q := by
  cases q; rfl

theorem projected_rows (s : State) (a : Bool) :
    (rationalRows model s a).map (fun e => (eraseReplica e.1,e.2)) =
      WeightedFuture.projectedRows (rationalRows model) eraseReplica representative (eraseReplica s) a := by
  cases a <;> rfl

theorem public_projection (s : State) :
    publicLens s = publicLens (representative (eraseReplica s)) := rfl

theorem classes_shape_exact (s t : State) :
    classes model s = classes model t ↔ eraseReplica s = eraseReplica t := by
  rw [first_profile_equation]
  cases s with
  | mk p u v r phase =>
    cases t with
    | mk q x y j clock =>
      cases p <;> cases u <;> cases v <;> cases phase <;>
        cases q <;> cases x <;> cases y <;> cases clock <;>
        simp only [classFormula,kernelCode,eraseReplica] <;> decide +kernel

theorem public_all_words (s t : State) (same : classes model s = classes model t)
    (word : List Bool) (trace : List Nat) :
    WeightedFuture.law (rationalRows model) publicLens s word trace =
      WeightedFuture.law (rationalRows model) publicLens t word trace := by
  change WeightedFuture.law (rationalRows model)
      (fun s => publicLens (representative (eraseReplica s))) s word trace =
    WeightedFuture.law (rationalRows model)
      (fun s => publicLens (representative (eraseReplica s))) t word trace
  exact WeightedFuture.equal_projection_all_words (rationalRows model)
    (fun q => publicLens (representative q)) eraseReplica representative
    projected_rows s t ((classes_shape_exact s t).mp same) word trace

def probe (s : State) : State := ⟨true,s.u,s.v,s.replica,!s.phase⟩

theorem probe_row (s : State) : rationalRows model s true = [(probe s,1)] := by
  simp [rationalRows,model,rows,probe]
  decide +kernel

theorem probe_law (s : State) (a b : Nat) :
    WeightedFuture.law (rationalRows model) publicLens s [true] [a,b] =
      if a = publicLens s ∧ b = publicLens (probe s) then 1 else 0 := by
  simp only [WeightedFuture.law,probe_row,List.foldr_cons,List.foldr_nil]
  by_cases h : a = publicLens s
  · simp [h,Rat.add_zero]
  · simp [h]

theorem current_probe_shape_exact (s t : State) :
    publicLens s = publicLens t ∧ publicLens (probe s) = publicLens (probe t) ↔
      eraseReplica s = eraseReplica t := by
  cases s with
  | mk p u v r phase =>
    cases t with
    | mk q x y j clock =>
      cases p <;> cases u <;> cases v <;> cases phase <;>
        cases q <;> cases x <;> cases y <;> cases clock <;>
        simp only [publicLens,kernelCode,probe,eraseReplica] <;> decide +kernel

theorem full_public_future_exact (s t : State) :
    (∀ word trace, WeightedFuture.law (rationalRows model) publicLens s word trace =
      WeightedFuture.law (rationalRows model) publicLens t word trace) ↔
      classes model s = classes model t := by
  constructor
  · intro h
    have witness := h [true] [publicLens s,publicLens (probe s)]
    rw [probe_law,probe_law] at witness
    have hp : publicLens s = publicLens t ∧ publicLens (probe s) = publicLens (probe t) := by
      by_cases yes : publicLens s = publicLens t ∧ publicLens (probe s) = publicLens (probe t)
      · exact yes
      · simp [yes] at witness
    exact (classes_shape_exact s t).mpr ((current_probe_shape_exact s t).mp hp)
  · intro same
    exact public_all_words s t same

end CSTTT.FullNative
