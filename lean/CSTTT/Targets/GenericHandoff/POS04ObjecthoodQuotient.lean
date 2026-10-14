import CSTTT.Targets.GenericHandoff.ObjecthoodCells
import CSTTT.Targets.GenericHandoff.POS04ProfileRules
import CSTTT.Targets.GenericHandoff.FixedPointAssignedT1

/-! G6d-2a family bridge: the actual assigned C table forces the computed
predictive partition and hence the uniform-fiber denominator. These lemmas
quantify over arbitrary inputs satisfying the raw reconstruction checks, not
just the canonical assignment or a finite menu of intervention labels. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodQuotient
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

theorem rawC_anchor (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (i : I) (k : J) : rawC d i k = cIndicator i k := by
  rcases hr with ⟨hidx,_,_,_,_,_,hc,_,_⟩
  simp only [List.all_eq_true,beq_iff_eq] at hc
  have h := hc i (by rw [hidx]; simp) k (by simp)
  simpa [ha.2.2.1] using h

theorem predictive_column_iff (d : Inputs) (hr : TablesReconstructed d) (s t : KState) :
    predictive d s = predictive d t ↔ ∀ k : J, rawC d (index s) k = rawC d (index t) k := by
  constructor
  · intro h k
    simp only [rawC,stateAt_index]
    rw [h]
  · intro h
    rcases hr with ⟨_,hlen,_,_,hcov,_,_,_,_⟩
    simp only [List.all_eq_true,decide_eq_true_eq] at hcov
    have hs : s ∈ kernel := by cases s <;> decide
    obtain ⟨n,hn,hv⟩ := List.getElem_of_mem (hcov s hs)
    let k : J := ⟨n,by simpa [classOrder,hlen] using hn⟩
    have hd : (classOrder d).getD k.val (0,[]) = predictive d s := by
      simp [List.getD,List.getElem?_eq_getElem hn,hv,k]
    have hcs : rawC d (index s) k = 1 := by
      simp only [rawC,stateAt_index]
      rw [hd]
      simp
    have hct : rawC d (index t) k = 1 := (h k).symm.trans hcs
    simp only [rawC,stateAt_index,hd] at hct
    by_cases he : predictive d t = predictive d s
    · exact he.symm
    · simp [he] at hct

theorem imported_columns_iff (s t : KState) :
    (∀ k : J, cIndicator (index s) k = cIndicator (index t) k) ↔
      mClass (index s) = mClass (index t) := by
  cases s <;> cases t <;> decide

theorem predictive_partition (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (s t : KState) :
    predictive d s = predictive d t ↔ mClass (index s) = mClass (index t) := by
  rw [predictive_column_iff d hr]
  simp only [rawC_anchor d ha hr]
  exact imported_columns_iff s t

theorem fiber_size (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) (s : KState) :
    fiberSize d s = classSize (index s) := by
  have he : (kernel.filter fun t => predictive d s == predictive d t) =
      (kernel.filter fun t => mClass (index s) == mClass (index t)) := by
    apply List.filter_congr
    intro t ht
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact predictive_partition d ha hr s t
  unfold fiberSize
  rw [he]
  cases s <;> decide

theorem fiber_small (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) (s : KState) :
    fiberSize d s = 1 ∨ fiberSize d s = 2 := by
  rw [fiber_size d ha hr]
  exact m_fibers_nonempty_and_small (index s)

/-- The rational uniform prototype equals the legacy scaled integer formula
because reconstruction *derives* fibers of size one or two. This is not an
extra hypothesis on arbitrary assignment values. -/
theorem uniform_fiber_scaled (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (s : KState) : (1 : Rat) / fiberSize d s = ((2 / fiberSize d s : Nat) : Rat) / 2 := by
  rcases fiber_small d ha hr s with h | h <;> rw [h] <;> decide +kernel


def stateOperation : FixedPointVerifier.RowOperation I → FixedPointVerifier.RowOperation KState
  | .swap i j => .swap (stateAt i) (stateAt j)
  | .scale i q => .scale (stateAt i) q
  | .add i j q => .add (stateAt i) (stateAt j) q

/-- Raw assigned inputs, with only fixed T1 protocol metadata supplied by the
specialization. Every numerical operator continues to use the assigned tables. -/
def raw (d : Inputs) : ObjecthoodRules.Raw KState Action Ambient :=
  ⟨{ POS04ProfileRules.raw d with revealLabel := false },d.policy,d.prototypes,
   4,d.audit.tau,d.audit.epsilon,core,.p0w0,FixedPointT1.operations.map stateOperation,
   (fun s t => (d.publishedP (index s) (index t) : Rat) / 4),
   (fun s k => if h : k < 7 then (d.publishedC (index s) ⟨k,h⟩ : Rat) else 0),
   (fun k s => if h : k < 7 then (d.publishedU ⟨k,h⟩ (index s) : Rat) / 2 else 0),
   d.audit.retention,3/80,1/8,78795/524288⟩

theorem class_readout (d : Inputs) : ObjecthoodRules.classOf (raw d) = predictive d := rfl

theorem generic_fiber_length (d : Inputs) (s : KState) :
    (ObjecthoodRules.fiber (raw d) s).length = fiberSize d s := by
  change (kernel.filter fun t => decide (predictive d t = predictive d s)).length = _
  unfold fiberSize
  congr 1
  apply List.filter_congr
  intro t ht
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq,beq_iff_eq]
  exact eq_comm

theorem rowWeight_sum (row : List (Ambient × Nat)) (t : KState) :
    rowWeight row t = (row.map fun e => if e.1 = .inK t then e.2 else 0).sum := by
  have fold (xs : List (Ambient × Nat)) (n : Nat) :
      xs.foldl (fun total e => total + e.2) n = n + (xs.map Prod.snd).sum := by
    induction xs generalizing n with
    | nil => simp
    | cons e xs ih => simp only [List.foldl_cons,List.map_cons,List.sum_cons]; rw [ih]; omega
  unfold rowWeight
  rw [fold]
  simp only [Nat.zero_add]
  induction row with
  | nil => rfl
  | cons e row ih =>
    by_cases he : e.1 = .inK t
    · simp [he,ih]
    · simp [he,ih]

theorem P_readout (d : Inputs) (s t : KState) :
    ObjecthoodRules.P (raw d) s t = (rowWeight (d.rows s (d.policy s)) t : Rat) / 4 := by
  unfold ObjecthoodRules.P
  change ((d.rows s (d.policy s)).map fun e =>
    if POS04ProfileRules.schema.destination e.1 = some t then (e.2 : Rat) else 0).sum / 4 = _
  rw [rowWeight_sum]
  congr 1
  induction d.rows s (d.policy s) with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons,Rat.natCast_add]
    rw [ih]
    congr 1
    cases e.1 <;> simp [POS04ProfileRules.schema]
    split <;> rfl

/-- Rational C agrees with the assigned indicator, before any imported table
is substituted. The prototype length is the declared raw shape check. -/
theorem C_readout (d : Inputs) (hlen : d.prototypes.length = 7) (s : KState) (k : J) :
    ObjecthoodRules.C (raw d) s k.val = (rawC d (index s) k : Rat) := by
  have hn : k.val < d.prototypes.length := by rw [hlen]; exact k.isLt
  have hd : (classOrder d).getD k.val (0,[]) = predictive d d.prototypes[k.val] := by
    simp [classOrder,List.getD,hn]
  unfold ObjecthoodRules.C
  rw [show (raw d).prototypes = d.prototypes from rfl]
  rw [class_readout,List.getElem?_eq_getElem hn]
  simp only [rawC,stateAt_index,hd]
  split <;> simp_all

theorem U_readout (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (k : J) (s : KState) : ObjecthoodRules.U (raw d) k.val s = (rawU d k (index s) : Rat) / 2 := by
  have hn : k.val < d.prototypes.length := by rw [hr.2.1]; exact k.isLt
  have hd : (classOrder d).getD k.val (0,[]) = predictive d d.prototypes[k.val] := by
    simp [classOrder,List.getD,hn]
  unfold ObjecthoodRules.U
  rw [show (raw d).prototypes = d.prototypes from rfl]
  rw [class_readout]
  rw [List.getElem?_eq_getElem hn]
  simp only [rawU,stateAt_index,hd]
  by_cases he : predictive d s = predictive d d.prototypes[k.val]
  · simp only [he,if_true,generic_fiber_length]
    have hf : fiberSize d d.prototypes[k.val] = fiberSize d s := by
      unfold fiberSize
      rw [he]
    rw [hf]
    exact uniform_fiber_scaled d ha hr s
  · simp only [he,if_false]
    decide +kernel


theorem rational_reconstruction (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.Reconstruction (raw d) := by
  have hfull := hr
  rcases hr with ⟨hidx,hlen,hcol,hnd,hcov,hp,hc,hu,hprod⟩
  simp only [List.all_eq_true,beq_iff_eq] at hc hu
  refine ⟨?_,?_,?_⟩
  · intro s t
    rw [P_readout,hp]
    rfl
  · intro s k
    have hk : k.val < 7 := by simpa only [raw,hlen] using k.isLt
    let j : J := ⟨k.val,hk⟩
    have hread := C_readout d hlen s j
    have he := hc (index s) (by rw [hidx]; simp) j (by simp)
    change ObjecthoodRules.C (raw d) s k.val = _
    rw [hread,he]
    simp only [raw,hk,dif_pos]
    rfl
  · intro k s
    have hk : k.val < 7 := by simpa only [raw,hlen] using k.isLt
    let j : J := ⟨k.val,hk⟩
    have hread := U_readout d ha hfull j s
    have he := hu j (by simp) (index s) (by rw [hidx]; simp)
    change ObjecthoodRules.U (raw d) k.val s = _
    rw [hread,he]
    simp only [raw,hk,dif_pos]
    rfl

theorem imported_P (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (s t : KState) : ObjecthoodRules.P (raw d) s t = entry P (index s) (index t) := by
  rw [P_readout,hr.2.2.2.2.2.1 s t,ha.2.1]
  rfl

theorem imported_C (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (s : KState) (k : J) : ObjecthoodRules.C (raw d) s k.val = (cIndicator (index s) k : Rat) := by
  rw [C_readout d hr.2.1,rawC_anchor d ha hr]

theorem imported_U (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (k : J) (s : KState) : ObjecthoodRules.U (raw d) k.val s = (uPrototypeNum k (index s) : Rat) / 2 := by
  have hu := hr.2.2.2.2.2.2.2.1
  simp only [List.all_eq_true,beq_iff_eq] at hu
  rw [U_readout d ha hr,hu k (by simp) (index s) (by rw [hr.1]; simp),ha.2.2.2]

theorem imported_C_nat (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (s : KState) (k : Nat) (hk : k < 7) :
    ObjecthoodRules.C (raw d) s k = (cIndicator (index s) ⟨k,hk⟩ : Rat) :=
  imported_C d ha hr s ⟨k,hk⟩
theorem imported_U_nat (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (k : Nat) (hk : k < 7) (s : KState) :
    ObjecthoodRules.U (raw d) k s = (uPrototypeNum ⟨k,hk⟩ (index s) : Rat) / 2 :=
  imported_U d ha hr ⟨k,hk⟩ s

theorem imported_CU (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (s t : KState) : ObjecthoodRules.CU (raw d) s t = entry CU (index s) (index t) := by
  unfold ObjecthoodRules.CU
  rw [show (raw d).prototypes.length = 7 from hr.2.1]
  change (ObjecthoodRules.C (raw d) s 0 * ObjecthoodRules.U (raw d) 0 t +
    (ObjecthoodRules.C (raw d) s 1 * ObjecthoodRules.U (raw d) 1 t +
    (ObjecthoodRules.C (raw d) s 2 * ObjecthoodRules.U (raw d) 2 t +
    (ObjecthoodRules.C (raw d) s 3 * ObjecthoodRules.U (raw d) 3 t +
    (ObjecthoodRules.C (raw d) s 4 * ObjecthoodRules.U (raw d) 4 t +
    (ObjecthoodRules.C (raw d) s 5 * ObjecthoodRules.U (raw d) 5 t +
    (ObjecthoodRules.C (raw d) s 6 * ObjecthoodRules.U (raw d) 6 t + 0))))))) = _
  rw [imported_C_nat d ha hr s 0 (by decide),imported_U_nat d ha hr 0 (by decide) t,
    imported_C_nat d ha hr s 1 (by decide),imported_U_nat d ha hr 1 (by decide) t,
    imported_C_nat d ha hr s 2 (by decide),imported_U_nat d ha hr 2 (by decide) t,
    imported_C_nat d ha hr s 3 (by decide),imported_U_nat d ha hr 3 (by decide) t,
    imported_C_nat d ha hr s 4 (by decide),imported_U_nat d ha hr 4 (by decide) t,
    imported_C_nat d ha hr s 5 (by decide),imported_U_nat d ha hr 5 (by decide) t,
    imported_C_nat d ha hr s 6 (by decide),imported_U_nat d ha hr 6 (by decide) t]
  cases s <;> cases t <;> decide +kernel

end CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodQuotient
