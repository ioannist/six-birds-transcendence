import CSTTT.Targets.GenericHandoff.POS04ObjecthoodOperator

/-! The checked T1 trace is transported along the actual index bijection;
this is symbolic preservation of the entire normalized system, not a fresh
numerical test of a displayed stationary vector. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodTrace
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open FixedPointVerifier POS04ObjecthoodQuotient POS04ObjecthoodOperator

def liftSystem (sys : System I) : System KState :=
  ⟨fun s t => sys.matrix (index s) (index t),fun s => sys.rhs (index s)⟩
def liftMatrix (e : Matrix I) : Matrix KState := fun s t => e (index s) (index t)

theorem index_eq (s : KState) (i : I) : s = stateAt i ↔ index s = i := by
  constructor
  · intro h; rw [h,index_stateAt]
  · intro h; rw [← stateAt_index s,h]

theorem index_injective (s t : KState) : index s = index t ↔ s = t := by
  constructor
  · intro h; exact (stateAt_index s).symm.trans ((congrArg stateAt h).trans (stateAt_index t))
  · intro h; rw [h]

theorem operation_reindex (op : RowOperation I) (sys : System I) :
    applyOperation (stateOperation op) (liftSystem sys) = liftSystem (applyOperation op sys) := by
  cases op <;>
    simp only [stateOperation,applyOperation,liftSystem,System.mk.injEq] <;>
    constructor
  all_goals
    funext s
    try funext t
    simp only [index_eq,index_stateAt]
  all_goals grind

theorem reduction_reindex (ops : List (RowOperation I)) (sys : System I) :
    reduce (ops.map stateOperation) (liftSystem sys) = liftSystem (reduce ops sys) := by
  induction ops generalizing sys with
  | nil => rfl
  | cons op ops ih =>
    change reduce (ops.map stateOperation) (applyOperation (stateOperation op) (liftSystem sys)) = _
    rw [operation_reindex,ih]
    rfl

theorem normalized_reindex (e : Matrix I) (anchor : I) :
    normalized (liftMatrix e) (stateAt anchor) = liftSystem (normalized e anchor) := by
  simp only [normalized,liftMatrix,liftSystem,System.mk.injEq]
  constructor
  · funext s t
    simp only [identity,index_eq,index_injective]
  · funext s
    simp only [index_eq]

theorem candidate_reindex (e : Matrix I) (anchor : I) (ops : List (RowOperation I)) :
    candidate (liftMatrix e) (stateAt anchor) (ops.map stateOperation) =
      fun s => candidate e anchor ops (index s) := by
  unfold candidate
  rw [normalized_reindex,reduction_reindex]
  rfl

theorem assigned_candidate (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.pi (raw d) = fun s => CSTTT.Objecthood.T1Audit.pi (index s) := by
  unfold ObjecthoodRules.pi
  rw [E_matrix d ha hr]
  change candidate (liftMatrix FixedPointT1.matrix) (stateAt 0)
    (FixedPointT1.operations.map stateOperation) = _
  rw [candidate_reindex,FixedPointT1.candidate_eq_pi]


theorem sum_reindex (f : I → Rat) :
    (kernel.map fun s => f (index s)).sum = ((List.finRange 10).map f).sum := by
  rw [show (kernel.map fun s => f (index s)) = (kernel.map index).map f by rw [List.map_map]; rfl]
  rw [show kernel.map index = List.finRange 10 by decide]

theorem mass_reindex (x : I → Rat) :
    mass kernel (fun s => x (index s)) = mass (List.finRange 10) x := sum_reindex x

theorem dot_reindex (a x : I → Rat) :
    dot kernel (fun s => a (index s)) (fun s => x (index s)) = dot (List.finRange 10) a x :=
  sum_reindex (fun i => a i * x i)

theorem check_reindex (e : Matrix I) (anchor : I) (ops : List (RowOperation I))
    (h : check (List.finRange 10) e anchor ops = true) :
    check kernel (liftMatrix e) (stateAt anchor) (ops.map stateOperation) = true := by
  simp only [check,checkCore,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h ⊢
  have hr := reduction_reindex ops (normalized e anchor)
  rw [← normalized_reindex] at hr
  have hc := candidate_reindex e anchor ops
  refine ⟨by decide,⟨⟨⟨?_,?_⟩,?_⟩,?_⟩⟩
  · intro s hs t ht
    have he := h.2.1.1.1 (index s) (by simp) (index t) (by simp)
    have hm := congrArg (fun sys : System KState => sys.matrix s t) hr
    dsimp only at hm
    rw [hm]
    simpa only [liftSystem,identity,index_injective] using he
  · intro s hs
    rw [hc]
    exact h.2.1.1.2 (index s) (by simp)
  · rw [hc,mass_reindex]
    exact h.2.1.2
  · intro s hs
    rw [hc]
    change dot kernel (fun t => e (index t) (index s))
      (fun t => candidate e anchor ops (index t)) = _
    rw [dot_reindex (fun i => e i (index s)) (candidate e anchor ops)]
    exact h.2.2 (index s) (by simp)

theorem assigned_trace_check (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    check kernel (ObjecthoodRules.E (raw d)) (raw d).anchor (raw d).operations = true := by
  rw [E_matrix d ha hr]
  change check kernel (liftMatrix FixedPointT1.matrix) (stateAt 0)
    (FixedPointT1.operations.map stateOperation) = true
  exact check_reindex _ _ _ FixedPointT1.checked

theorem assigned_probability_fixed_unique (d : Inputs)
    (ha : T1Anchors d) (hr : TablesReconstructed d) :
    Probability kernel (ObjecthoodRules.pi (raw d)) ∧
    Fixed kernel (ObjecthoodRules.E (raw d)) (ObjecthoodRules.pi (raw d)) ∧
    (∀ x, Probability kernel x → Fixed kernel (ObjecthoodRules.E (raw d)) x →
      x = ObjecthoodRules.pi (raw d)) :=
  check_sound kernel (by intro s; cases s <;> decide)
    _ _ _ (assigned_trace_check d ha hr)

theorem assigned_nonuniform (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.pi (raw d) ≠ ObjecthoodRules.uniform (raw d) := by
  rw [assigned_candidate d ha hr]
  intro h
  have h0 := congrFun h .p0w0
  have hn : CSTTT.Objecthood.T1Audit.pi (index KState.p0w0) ≠
      ObjecthoodRules.uniform (raw d) .p0w0 := by
    change CSTTT.Objecthood.T1Audit.pi 0 ≠ (1 / 10 : Rat)
    decide +kernel
  exact hn h0

theorem assigned_core_mass (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.coreMass (raw d) = 77/80 := by
  unfold ObjecthoodRules.coreMass
  rw [assigned_candidate d ha hr]
  change (core.map fun s => CSTTT.Objecthood.T1Audit.pi (index s)).sum = _
  decide +kernel

theorem assigned_TV (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.TV (raw d) = 3/80 := by
  unfold ObjecthoodRules.TV
  rw [assigned_candidate d ha hr]
  change ((kernel.map fun s => ObjecthoodRules.absRat
    (CSTTT.Objecthood.T1Audit.pi (index s) -
      (if s ∈ core then 1 / (core.length : Rat) else 0))).sum) / 2 = _
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem eps_defect_link :
    ((kernel.map fun s =>
      ((kernel.map fun t => ObjecthoodRules.absRat
        (ObjecthoodRules.product kernel (lift E2eps) (lift E2eps) s t -
          lift E2eps s t)).sum) / 2).foldl max 0) = 78795/524288 := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem zero_defect_link :
    ((kernel.map fun s =>
      ((kernel.map fun t => ObjecthoodRules.absRat
        (ObjecthoodRules.product kernel (lift E2zero) (lift E2zero) s t -
          lift E2zero s t)).sum) / 2).foldl max 0) = 1/8 := by
  decide +kernel

theorem assigned_eps_defect (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.defect (raw d) (ObjecthoodRules.E (raw d)) = 78795/524288 := by
  rw [E_matrix d ha hr]
  exact eps_defect_link

theorem assigned_zero_defect (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.defect (raw d) (ObjecthoodRules.Ezero (raw d)) = 1/8 := by
  rw [Ezero_matrix d ha hr]
  exact zero_defect_link

end CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodTrace
