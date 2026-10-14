import CSTTT.Targets.GenericHandoff.ClauseDispatcher
import CSTTT.Targets.GenericHandoff.POS04ObjecthoodReference
import CSTTT.Targets.GenericHandoff.POS04Exposure
import CSTTT.Targets.GenericHandoff.POS04ProtocolCredit
import CSTTT.Targets.GenericHandoff.POS04Joint
import CSTTT.Targets.GenericHandoff.POS04OperationalViability
import CSTTT.Targets.GenericHandoff.POS04TemporalFactor

/-! Concrete POS-04 instance of the closed raw dispatcher. This proves
nonemptiness of its hypotheses without a flag. Arbitrary-partial C3/C6 and
actual-runtime equivalences remain separate completion gates for promotion. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04Dispatcher
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit ClauseDispatcher

def package (t : Tag) : Package Cell Value where
  rule
  | .c1 => .c1 inferInstance POS04ProfileRules.schema POS04ObjecthoodReference.reference (POS04ObjecthoodCells.bindings t)
  | .c2 => .c2 inferInstance inferInstance POS04ProfileRules.clauseSchema (POS04ProfileRules.clauseBindings t)
  | .c3 => .c3 inferInstance inferInstance POS04ProfileRules.clauseSchema (POS04ProfileRules.clauseBindings t)
  | .c4 => .c4 inferInstance inferInstance POS04Exposure.schema (POS04Exposure.bindings t)
  | .c5 => .c5 inferInstance inferInstance inferInstance inferInstance (POS04ProtocolCredit.schema t) (POS04ProtocolCredit.bindings t)
  | .c6 => .c6 inferInstance inferInstance inferInstance inferInstance inferInstance (POS04TemporalFactor.schema t) (POS04TemporalFactor.bindings t)
  | .c7 => .c7 inferInstance inferInstance inferInstance inferInstance inferInstance POS04Joint.schema (POS04Joint.bindings t)
  | .c8 => .c8 inferInstance inferInstance inferInstance (POS04OperationalViability.schema t) ambientStates (POS04OperationalViability.bindings t)

set_option maxRecDepth 8192 in
theorem canonical_accept (t : Tag) : (package t).accept canonical := by
  intro c
  cases c with
  | c1 => exact POS04ObjecthoodReference.canonical_accept t
  | c2 => exact (POS04ProfileRules.generic_c2_iff _ _).mpr (canonical_c123 t).2.1
  | c3 =>
    refine ⟨(POS04ProfileRules.generic_c3_iff _ _).mpr (canonical_c123 t).2.2,?_,?_,?_⟩
    · exact POS04ProfileRules.raw (clauseInputs canonical t .c3)
    · exact (clauseInputs canonical t .c3).publishedM
    · have he := POS04ProfileRules.clause_decode_eq canonical t .c3 (Or.inr rfl)
      rw [if_pos (canonical_complete _),POS04ProfileRules.raw_scoped _ _ .c3 (Or.inr rfl),
        POS04ProfileRules.labels_scoped _ _ .c3 (Or.inr rfl)] at he
      exact ⟨he,POS04ProfileRules.canonical_genuine_stabilization t⟩
  | c4 => exact POS04Exposure.canonical_accept t
  | c5 => exact POS04ProtocolCredit.canonical_accept t
  | c6 => exact POS04TemporalFactor.canonical_assigned t
  | c7 => exact POS04Joint.canonical_accept t
  | c8 =>
    change OperationalCells.Accept (POS04OperationalViability.schema t) ambientStates (POS04OperationalViability.bindings t) canonical
    refine ⟨POS04OperationalViability.raw (clause8 canonical t),?_,?_,?_⟩
    · rw [POS04OperationalViability.decoded_eq]
      have hc : CSTTT.TargetTheory.GenericHandoff.Complete (clauseScope t .c8) canonical := by intro k hk; rfl
      rw [if_pos hc,POS04OperationalViability.raw_scoped]
    · obtain ⟨d,hd,ha⟩ := (POS04OperationalViability.canonical_accept t).2
      have he : OperationalViability.decoded (POS04OperationalViability.bindings t) canonical =
          some (POS04OperationalViability.raw (clause8 canonical t)) := by
        rw [POS04OperationalViability.decoded_eq]
        have hc : CSTTT.TargetTheory.GenericHandoff.Complete (clauseScope t .c8) canonical := by intro k hk; rfl
        rw [if_pos hc,POS04OperationalViability.raw_scoped]
      have hx := Option.some.inj (hd.symm.trans he)
      subst d
      exact ha
    · constructor
      · intro o; cases o with
        | inK s => cases s <;> decide
        | p2w0 => decide
        | p5w1 => decide
      · intro s hs a ha
        cases t <;> cases s <;> cases a <;> decide +kernel

theorem deleted_C (t : Tag) :
    ¬ (package t).accept (CSTTT.POS04.Assigned.put canonical .publishedC none) := by
  apply Package.missing_rejected (package t) _ .c1 .publishedC
  · simp [package,Rule.scope,POS04ObjecthoodCells.bindings,ObjecthoodCells.Bindings.scope]
  · simp

end CSTTT.TargetTheory.GenericHandoff.POS04Dispatcher
