import CSTTT.Targets.GenericHandoff.POS04ObjecthoodQuotient

/-! Generic rational operator / T1 scaled-matrix bridge. The arbitrary-family
inputs are retained through the P/C/U reconstruction lemmas; only afterwards
are the exact T1 tables used. These are representation equations, not new
candidate-only fixed-point tests. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodOperator
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open POS04ObjecthoodQuotient

def lift (a : ScaledMatrix) : FixedPointVerifier.Matrix KState :=
  fun s t => entry a (index s) (index t)

theorem identity_product (a : FixedPointVerifier.Matrix KState) :
    ObjecthoodRules.product kernel FixedPointVerifier.identity a = a := by
  funext s t
  have h := FixedPointVerifier.dot_indicator kernel (by decide) s (fun k => a k t)
  have hs : s ∈ kernel := by cases s <;> decide
  simpa only [ObjecthoodRules.product,FixedPointVerifier.dot,hs,if_true] using h

theorem P_matrix (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.P (raw d) = lift P := by
  funext s t
  exact imported_P d ha hr s t

theorem CU_matrix (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.CU (raw d) = lift CU := by
  funext s t
  exact imported_CU d ha hr s t

theorem perturbed_matrix (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.perturbed (raw d) = lift Peps := by
  funext s t
  unfold ObjecthoodRules.perturbed
  rw [imported_P d ha hr s t]
  have he : (raw d).epsilon = 1/16 := by rw [show (raw d).epsilon = d.audit.epsilon from rfl,ha.1]; rfl
  rw [he]
  change (1 - (1/16 : Rat)) * entry P (index s) (index t) + (1/16 : Rat) / 10 = _
  rw [show lift Peps s t = entry Peps (index s) (index t) from rfl,
    peps_is_t1_mixture]
  grind

/- Exact representation conversions on the published T1 tables, checked
without storing any replacement rational matrix. -/
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem peps_product : ObjecthoodRules.product kernel (lift Peps) (lift Peps) = lift Peps2 := by
  funext s t
  cases s <;> cases t <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem peps2_cu_product : ObjecthoodRules.product kernel (lift Peps2) (lift CU) = lift E2eps := by
  funext s t
  cases s <;> cases t <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem p_product : ObjecthoodRules.product kernel (lift P) (lift P) = lift P2 := by
  funext s t
  cases s <;> cases t <;> decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem p2_cu_product : ObjecthoodRules.product kernel (lift P2) (lift CU) = lift E2zero := by
  funext s t
  cases s <;> cases t <;> decide +kernel

theorem E_matrix (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.E (raw d) = lift E2eps := by
  have ht : (raw d).tau = 2 := by rw [show (raw d).tau = d.audit.tau from rfl,ha.1]; rfl
  unfold ObjecthoodRules.E
  rw [ht,CU_matrix d ha hr,perturbed_matrix d ha hr]
  change ObjecthoodRules.product kernel (ObjecthoodRules.power kernel (lift Peps) 2) (lift CU) = _
  simp only [ObjecthoodRules.power]
  rw [identity_product,peps_product,peps2_cu_product]

theorem Ezero_matrix (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.Ezero (raw d) = lift E2zero := by
  have ht : (raw d).tau = 2 := by rw [show (raw d).tau = d.audit.tau from rfl,ha.1]; rfl
  unfold ObjecthoodRules.Ezero
  rw [ht,CU_matrix d ha hr,P_matrix d ha hr]
  change ObjecthoodRules.product kernel (ObjecthoodRules.power kernel (lift P) 2) (lift CU) = _
  simp only [ObjecthoodRules.power]
  rw [identity_product,p_product,p2_cu_product]

/-- Actual assignment family: both operator equations, conditional only on the
existing completeness/raw reconstruction gate, with no default-filled bypass. -/
theorem assigned_operators (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (h : C1Gate a tag) :
    ObjecthoodRules.E (raw (clauseInputs a tag .c1)) = lift E2eps ∧
    ObjecthoodRules.Ezero (raw (clauseInputs a tag .c1)) = lift E2zero :=
  ⟨E_matrix _ h.2.1 h.2.2,Ezero_matrix _ h.2.1 h.2.2⟩

theorem canonical_operators (tag : Tag) :
    ObjecthoodRules.E (raw (clauseInputs canonical tag .c1)) = lift E2eps ∧
    ObjecthoodRules.Ezero (raw (clauseInputs canonical tag .c1)) = lift E2zero :=
  assigned_operators canonical tag (canonical_c123 tag).1.1


theorem table_control_target_rejected :
    ¬ ObjecthoodRules.Gate (raw (clauseInputs (negC1Table canonical) .target .c1)) := by
  apply ObjecthoodRules.changed_P_rejected _ .p2w1 .p1w0
  decide +kernel

theorem profile_control_target_rejected :
    ¬ ObjecthoodRules.Gate (raw (clauseInputs (negC3Profile canonical) .target .c1)) := by
  apply ObjecthoodRules.changed_P_rejected _ .p1w0 .p2w1
  decide +kernel

theorem table_control_source_unchanged :
    raw (clauseInputs (negC1Table canonical) .source .c1) =
      raw (clauseInputs canonical .source .c1) := rfl

theorem profile_control_source_unchanged :
    raw (clauseInputs (negC3Profile canonical) .source .c1) =
      raw (clauseInputs canonical .source .c1) := rfl

theorem lower_control_unchanged (tag : Tag) :
    raw (clauseInputs (negC2Split canonical) tag .c1) =
      raw (clauseInputs canonical tag .c1) := by cases tag <;> rfl

end CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodOperator
