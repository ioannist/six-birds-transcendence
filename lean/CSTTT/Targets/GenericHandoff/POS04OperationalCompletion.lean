import CSTTT.Targets.GenericHandoff.POS04ObjecthoodProtocol
import CSTTT.Targets.GenericHandoff.OperationalCells
import CSTTT.Targets.GenericHandoff.POS04OperationalViability
namespace CSTTT.TargetTheory.GenericHandoff.POS04OperationalViability
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

theorem row_rule_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    OperationalCells.RowsValid (schema t) ambientStates (raw (clause8 a t)) ↔
      RowsValid (clauseInputs a t .c8) := by
  have ho : ∀ o : Ambient, o ∈ ambientStates := by
    intro o; cases o with
    | inK s => cases s <;> decide
    | p2w0 => decide
    | p5w1 => decide
  simp only [OperationalCells.RowsValid,ho,and_true,RowsValid,List.all_eq_true,
    Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq]
  constructor
  · intro h s hs act ha
    have hv := h.2 s hs act ha
    rcases hv with ⟨hp,hn⟩ | ⟨hp,hn⟩
    · exact ⟨hp,Or.inl (by rw [POS04ObjecthoodProtocol.sum_weights]; exact hn)⟩
    · exact ⟨hp,Or.inr (by rw [POS04ObjecthoodProtocol.sum_weights]; exact hn)⟩
  · intro h
    refine ⟨by intro _; trivial,?_⟩
    intro s hs act ha
    obtain ⟨hp,hn⟩ := h s hs act ha
    rw [POS04ObjecthoodProtocol.sum_weights] at hn
    rcases hn with hn | hn
    · exact Or.inl ⟨hp,hn⟩
    · exact Or.inr ⟨hp,hn⟩
theorem dispatcher_c8_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    OperationalCells.Accept (schema t) ambientStates (bindings t) a ↔ C8Accept a t := by
  rw [← generic_c8_iff]
  unfold OperationalCells.Accept AssignedAccept OperationalViability.AssignedAccept
  rw [decoded_eq,raw_scoped]
  by_cases hc : Complete (clauseScope t .c8) a
  · simp only [if_pos hc,Option.some.injEq]
    constructor
    · rintro ⟨d,rfl,ha,hr⟩
      exact ⟨(row_rule_iff a t).mp hr,_,rfl,ha⟩
    · rintro ⟨hr,d,rfl,ha⟩
      exact ⟨_,rfl,ha,(row_rule_iff a t).mpr hr⟩
  · simp [hc]
end CSTTT.TargetTheory.GenericHandoff.POS04OperationalViability
