import CSTTT.Targets.GenericHandoff.POS04ObjecthoodOperator

/-! POS-04 typed C1 bindings. Exact partial-assignment decoding is independent
of acceptance. The published protocol constants come from T1Audit/Data and
FixedPointT1, never from a stored uniqueness or acceptance verdict. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodCells
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open POS04ObjecthoodQuotient

def bindings (tag : Tag) : ObjecthoodCells.Bindings Cell Value KState Action Ambient :=
  ⟨⟨.rows tag,id⟩,⟨.positions,id⟩,⟨.hazards,id⟩,⟨.policy,id⟩,⟨.prototypes,id⟩,
   ⟨.audit,fun p => ⟨4,p.tau,p.epsilon,core,.p0w0,
     FixedPointT1.operations.map stateOperation,p.retention,3/80,1/8,78795/524288⟩⟩,
   ⟨.publishedP,fun p s t => (p (index s) (index t) : Rat) / 4⟩,
   ⟨.publishedC,fun c s k => if h : k < 7 then (c (index s) ⟨k,h⟩ : Rat) else 0⟩,
   ⟨.publishedU,fun u k s => if h : k < 7 then (u ⟨k,h⟩ (index s) : Rat) / 2 else 0⟩⟩

theorem scope_membership (tag : Tag) (k : Cell) :
    k ∈ (bindings tag).scope ↔ k ∈ clauseScope tag .c1 := by
  simp [bindings,ObjecthoodCells.Bindings.scope,clauseScope,commonScope]
  grind

/-- Missing inputs fail before the generic decoder can reconstruct an object,
for every consumed cell, on any partial assignment. -/
theorem missing_rejected (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c1) :
    ¬ ObjecthoodCells.Gate POS04ProfileRules.schema (bindings tag)
        (CSTTT.POS04.Assigned.put a k none) ∧
    ¬ ObjecthoodCells.Accept POS04ProfileRules.schema (bindings tag)
        (CSTTT.POS04.Assigned.put a k none) := by
  apply ObjecthoodCells.missing_rejected _ _ _ k
  · exact (scope_membership tag k).mpr hk
  · simp

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
open Classical in
theorem decoder_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ObjecthoodCells.decoded POS04ProfileRules.schema (bindings tag) a =
      if CSTTT.POS04.Assigned.Complete (clauseScope tag .c1) a then
        some (raw (inputs a tag)) else none := by
  cases hr : a (.rows tag) <;> cases hp : a .positions <;>
    cases hh : a .hazards <;> cases hpol : a .policy <;>
    cases hproto : a .prototypes <;> cases ha : a .audit <;>
    cases hP : a .publishedP <;> cases hC : a .publishedC <;> cases hU : a .publishedU <;>
    simp [ObjecthoodCells.decoded,bindings,CellView.read,raw,POS04ProfileRules.raw,
      inputs,hr,hp,hh,hpol,hproto,ha,hP,hC,hU,
      CSTTT.POS04.Assigned.Complete,clauseScope,commonScope]

theorem raw_scoped (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    raw (inputs a tag) = raw (clauseInputs a tag .c1) := by cases tag <;> rfl

theorem decoded_complete (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c1) a) :
    ObjecthoodCells.decoded POS04ProfileRules.schema (bindings tag) a =
      some (raw (clauseInputs a tag .c1)) := by
  rw [decoder_eq,if_pos h,raw_scoped]

theorem decoded_canonical (tag : Tag) :
    ObjecthoodCells.decoded POS04ProfileRules.schema (bindings tag) canonical =
      some (raw (clauseInputs canonical tag .c1)) :=
  decoded_complete _ _ (canonical_c123 tag).1.1.1.1


theorem gate_decode_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ObjecthoodCells.Gate POS04ProfileRules.schema (bindings tag) a ↔
      CSTTT.POS04.Assigned.Complete (clauseScope tag .c1) a ∧
        ObjecthoodRules.Gate (raw (clauseInputs a tag .c1)) := by
  unfold ObjecthoodCells.Gate
  rw [decoder_eq,raw_scoped]
  by_cases h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c1) a <;> simp [h]

theorem accept_decode_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ObjecthoodCells.Accept POS04ProfileRules.schema (bindings tag) a ↔
      CSTTT.POS04.Assigned.Complete (clauseScope tag .c1) a ∧
        ObjecthoodRules.Accept (raw (clauseInputs a tag .c1)) := by
  unfold ObjecthoodCells.Accept
  rw [decoder_eq,raw_scoped]
  by_cases h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c1) a <;> simp [h]

theorem table_control_rejected :
    ¬ ObjecthoodCells.Gate POS04ProfileRules.schema (bindings .target) (negC1Table canonical) := by
  intro h
  exact POS04ObjecthoodOperator.table_control_target_rejected ((gate_decode_iff _ _).mp h).2

theorem profile_control_rejected :
    ¬ ObjecthoodCells.Gate POS04ProfileRules.schema (bindings .target) (negC3Profile canonical) := by
  intro h
  exact POS04ObjecthoodOperator.profile_control_target_rejected ((gate_decode_iff _ _).mp h).2

end CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodCells
