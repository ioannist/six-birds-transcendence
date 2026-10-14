import CSTTT.Targets.GenericHandoff.POS04ObjecthoodCells
import CSTTT.Targets.GenericHandoff.POS04ObjecthoodTrace

/-! Concrete C1 instantiation of the polymorphic rational rules. Numerical
closure checks cover the raw kernel/quotient/support only; the fixed-distribution
check and its all-distribution uniqueness conclusion use the transported trace.
This does not yet claim arbitrary-partial-assignment acceptance equivalence. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodInstance
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open POS04ObjecthoodQuotient POS04ObjecthoodCells POS04ObjecthoodTrace

private instance (p : KState → Prop) [DecidablePred p] : Decidable (∀ s, p s) :=
  decidable_of_iff (∀ i : I, p (stateAt i)) ⟨
    fun h s => by simpa only [stateAt_index] using h (index s),
    fun h i => h (stateAt i)⟩

private instance (p : Action → Prop) [DecidablePred p] : Decidable (∀ a, p a) :=
  decidable_of_iff (p .stay ∧ p .cw ∧ p .ccw) ⟨
    fun h a => by cases a; exact h.1; exact h.2.1; exact h.2.2,
    fun h => ⟨h _,h _,h _⟩⟩

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem canonical_raw_gate (tag : Tag) :
    ObjecthoodRules.Gate (raw (clauseInputs canonical tag .c1)) := by
  have hg := (canonical_c123 tag).1.1
  refine ⟨?_,?_,?_,?_,assigned_trace_check _ hg.2.1 hg.2.2⟩
  · unfold ObjecthoodRules.KernelCheck
    cases tag <;> decide +kernel
  · unfold ObjecthoodRules.QuotientCheck
    cases tag <;> decide +kernel
  · exact rational_reconstruction _ hg.2.1 hg.2.2
  · unfold ObjecthoodRules.SupportCheck
    cases tag <;> decide +kernel

theorem canonical_raw_accept (tag : Tag) :
    ObjecthoodRules.Accept (raw (clauseInputs canonical tag .c1)) := by
  have hg := (canonical_c123 tag).1.1
  refine ⟨canonical_raw_gate tag,assigned_nonuniform _ hg.2.1 hg.2.2,?_,
    assigned_TV _ hg.2.1 hg.2.2,assigned_zero_defect _ hg.2.1 hg.2.2,
    assigned_eps_defect _ hg.2.1 hg.2.2⟩
  rw [assigned_core_mass _ hg.2.1 hg.2.2]
  change (77/80 : Rat) ≥ 3/4
  decide +kernel

theorem canonical_accept (tag : Tag) :
    ObjecthoodCells.Accept POS04ProfileRules.schema (bindings tag) canonical :=
  (accept_decode_iff _ _).mpr ⟨(canonical_c123 tag).1.1.1.1,canonical_raw_accept tag⟩

theorem canonical_equivalence (tag : Tag) :
    ObjecthoodCells.Accept POS04ProfileRules.schema (bindings tag) canonical ↔
      C1Accept canonical tag :=
  ⟨fun _ => (canonical_c123 tag).1,fun _ => canonical_accept tag⟩

theorem table_control_target_not_accepted :
    ¬ ObjecthoodCells.Accept POS04ProfileRules.schema (bindings .target)
      (negC1Table canonical) := by
  intro h
  exact POS04ObjecthoodOperator.table_control_target_rejected
    ((accept_decode_iff _ _).mp h).2.1

theorem profile_control_target_not_accepted :
    ¬ ObjecthoodCells.Accept POS04ProfileRules.schema (bindings .target)
      (negC3Profile canonical) := by
  intro h
  exact POS04ObjecthoodOperator.profile_control_target_rejected
    ((accept_decode_iff _ _).mp h).2.1

theorem table_control_source_accepted :
    ObjecthoodCells.Accept POS04ProfileRules.schema (bindings .source)
      (negC1Table canonical) := by
  apply (accept_decode_iff _ _).mpr
  constructor
  · exact (neg_c1_table_outcomes .source).1.1.1.1
  · rw [POS04ObjecthoodOperator.table_control_source_unchanged]
    exact canonical_raw_accept .source

theorem profile_control_source_accepted :
    ObjecthoodCells.Accept POS04ProfileRules.schema (bindings .source)
      (negC3Profile canonical) := by
  apply (accept_decode_iff _ _).mpr
  constructor
  · exact (neg_c3_profile_outcomes .source).1.1.1.1
  · rw [POS04ObjecthoodOperator.profile_control_source_unchanged]
    exact canonical_raw_accept .source

theorem lower_control_accepted (tag : Tag) :
    ObjecthoodCells.Accept POS04ProfileRules.schema (bindings tag)
      (negC2Split canonical) := by
  apply (accept_decode_iff _ _).mpr
  constructor
  · exact (neg_c2_split_outcomes tag).1.1.1.1
  · rw [POS04ObjecthoodOperator.lower_control_unchanged]
    exact canonical_raw_accept tag

/-- Per-tag C1 outcomes: the target table/profile mutations fail through P;
the source and both lower-readout controls remain accepted. -/
theorem control_outcomes :
    ObjecthoodCells.Accept POS04ProfileRules.schema (bindings .source) (negC1Table canonical) ∧
    ¬ ObjecthoodCells.Accept POS04ProfileRules.schema (bindings .target) (negC1Table canonical) ∧
    ObjecthoodCells.Accept POS04ProfileRules.schema (bindings .source) (negC3Profile canonical) ∧
    ¬ ObjecthoodCells.Accept POS04ProfileRules.schema (bindings .target) (negC3Profile canonical) ∧
    (∀ tag, ObjecthoodCells.Accept POS04ProfileRules.schema (bindings tag) (negC2Split canonical)) :=
  ⟨table_control_source_accepted,table_control_target_not_accepted,
    profile_control_source_accepted,profile_control_target_not_accepted,lower_control_accepted⟩

end CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodInstance
