import CSTTT.POS04.Assigned.PackageInstance
import CSTTT.POS04.Assigned.C6ActualFutureEquivalence

namespace CSTTT.POS04.Assigned.ActualCyclePrototype
open CSTTT.Objecthood.T1Audit
set_option autoImplicit false
-- Frozen primitive intervention, before any evaluation. No verdict fields.
def shifted : Assignment := put canonical .positions (some (fun state => publicPosition state+1))
theorem shifted_c6_gate : C6Gate shifted .target := by
  unfold C6Gate
  refine ⟨⟨?_,?_⟩,⟨⟨rfl,?_⟩,?_⟩,?_,?_,rfl,?_⟩
  · intro cell member
    cases cell <;> simp [shifted,put,canonical]
  · unfold RowsValid
    decide +kernel
  · intro s t
    cases s <;> cases t <;> decide +kernel
  · intro s t
    cases s <;> cases t <;> decide +kernel
  · unfold Trace6
    decide +kernel
  · unfold LedgerConservation6
    decide +kernel
  · unfold UnitFunding6
    decide +kernel
theorem shifted_c6_bisim : FiniteBisim6 (runInputs6 shifted .target) := by
  unfold FiniteBisim6
  decide +kernel
theorem shifted_c6_coarser : Coarser6 shifted .target := by
  unfold Coarser6
  decide +kernel
theorem shifted_c6_accepts : C6Accept shifted .target :=
  ⟨shifted_c6_gate,shifted_c6_bisim,shifted_c6_coarser⟩
-- All-word sufficiency survives on the actual ambient-outcome interpreter.
theorem shifted_actual_future : CSTTT.TransportTheory.FullFutureSufficient (actualFuture6 shifted .target) :=
  accepted_actual_all_words6 shifted_c6_accepts

def rank : Clause → Nat
  | .c1 => 0 | .c2 => 1 | .c3 => 2 | .c4 => 3
  | .c5 => 4 | .c6 => 5 | .c7 => 6 | .c8 => 7
def adjacent (left right : Clause) : Prop :=
  (rank left+1)%8=rank right ∨ (rank right+1)%8=rank left
def base (clause : Clause) : Assignment := if clause=.c6 then shifted else canonical
-- EXACT actual decoder-dependency scopes: no newly invented diagonal cell.
def actualLocal (clause : Clause) : Assignment := decode (clauseScope .target clause) (base clause)
theorem local_reads (clause : Clause) (cell : Cell) (member : cell∈clauseScope .target clause) :
    actualLocal clause cell=base clause cell := by simp [actualLocal,decode,member]
theorem local_outside (clause : Clause) (cell : Cell) (absent : cell∉clauseScope .target clause) :
    actualLocal clause cell=none := by simp [actualLocal,decode,absent]

theorem all_actual_local_accepts (clause : Clause) : clauseAccept (actualLocal clause) .target clause := by
  apply (clause_accept_locality .target clause (fun cell member => local_reads clause cell member)).mpr
  by_cases isSix : clause=.c6
  · subst clause
    exact shifted_c6_accepts
  · simpa [base,isSix] using canonical_assigned_package .target clause
theorem all_actual_local_gates (clause : Clause) : clauseGate (actualLocal clause) .target clause :=
  clause_accept_implies_gate clause (all_actual_local_accepts clause)

theorem no_adjacent_c6_positions (left right : Clause) (edge : adjacent left right)
    (leftRead : Cell.positions∈clauseScope .target left) (rightRead : Cell.positions∈clauseScope .target right) :
    left≠.c6 ∧ right≠.c6 := by
  cases left <;> cases right <;> simp_all [adjacent,rank,clauseScope,commonScope]
theorem base_other_cell (clause : Clause) (cell : Cell) (other : cell≠.positions) : base clause cell=canonical cell := by
  by_cases isSix : clause=.c6
  · simp [base,isSix,shifted,put,other]
  · simp [base,isSix]
theorem actual_cycle_edge_compatible (left right : Clause) (edge : adjacent left right)
    (cell : Cell) (leftRead : cell∈clauseScope .target left) (rightRead : cell∈clauseScope .target right) :
    actualLocal left cell=actualLocal right cell := by
  rw [local_reads left cell leftRead,local_reads right cell rightRead]
  by_cases isPosition : cell=.positions
  · subst cell
    have nonSix := no_adjacent_c6_positions left right edge leftRead rightRead
    simp [base,nonSix.1,nonSix.2]
  · rw [base_other_cell left cell isPosition,base_other_cell right cell isPosition]

-- Every cycle edge has actual shared raw rows, not an empty overlap.
theorem every_edge_has_actual_rows (left right : Clause) :
    Cell.rows .target∈clauseScope .target left ∧ Cell.rows .target∈clauseScope .target right := by
  cases left <;> cases right <;> decide +kernel

def GlobalRestriction (global : Assignment) : Prop :=
  ∀ clause cell,cell∈clauseScope .target clause → global cell=actualLocal clause cell
theorem no_actual_global_restriction : ¬∃ global : Assignment,GlobalRestriction global := by
  rintro ⟨global,restricts⟩
  have first := restricts .c1 .positions (by decide +kernel)
  have sixth := restricts .c6 .positions (by decide +kernel)
  have equal := congrArg (fun position : Option (KState → Nat) => position.map (fun f => f .p0w0)) (first.symm.trans sixth)
  change (some 0 : Option Nat)=some 1 at equal
  contradiction

-- This is POS04's own assignment-sensitive C1–C8 acceptance, not pass side
-- conditions conjoined to an invented assignment-equality ClauseSpec.
theorem actual_pos04_cyclic_obstruction :
    AssignedPackagePass canonical .target ∧
    (∀ clause,clauseAccept (actualLocal clause) .target clause) ∧
    (∀ clause,clauseGate (actualLocal clause) .target clause) ∧
    (∀ left right,adjacent left right → ∀ cell,cell∈clauseScope .target left → cell∈clauseScope .target right →
      actualLocal left cell=actualLocal right cell) ∧
    (∀ left right,Cell.rows .target∈clauseScope .target left ∧ Cell.rows .target∈clauseScope .target right) ∧
    ¬∃ global : Assignment,GlobalRestriction global :=
  ⟨canonical_assigned_package .target,all_actual_local_accepts,all_actual_local_gates,
    actual_cycle_edge_compatible,every_edge_has_actual_rows,no_actual_global_restriction⟩

-- Full actual future sufficiency holds on the very local used in the cycle.
theorem actual_local_c6_future :
    CSTTT.TransportTheory.FullFutureSufficient (actualFuture6 (actualLocal .c6) .target) :=
  accepted_actual_all_words6 (all_actual_local_accepts .c6)

theorem positions_disagree : actualLocal .c1 .positions ≠ actualLocal .c6 .positions := by
  intro equal
  have atZero := congrArg (fun position : Option (KState → Nat) => position.map (fun f => f .p0w0)) equal
  change (some 0 : Option Nat)=some 1 at atZero
  contradiction

-- The actual raw coordinate cannot propagate along the declared cycle.
-- Sigma encoding is only for the existing homogeneous gluing lemma.
theorem positions_no_scoped_path :
    ¬CSTTT.PackageTheory.ScopedReach adjacent (fun clause cell => cell∈clauseScope .target clause)
      Cell.positions Clause.c1 Clause.c6 := by
  intro path
  let values : Clause → Cell → Sigma (fun cell => Option (Value cell)) :=
    fun clause cell => ⟨cell,actualLocal clause cell⟩
  have compatible : ∀ left right cell, adjacent left right →
      cell∈clauseScope .target left → cell∈clauseScope .target right →
      values left cell=values right cell := by
    intro left right cell edge leftRead rightRead
    exact congrArg (Sigma.mk cell) (actual_cycle_edge_compatible left right edge cell leftRead rightRead)
  have equal := CSTTT.PackageTheory.localEqualityAlongScopedReach compatible path
  exact positions_disagree (eq_of_heq (Sigma.mk.inj equal).2)

-- The underlying graph really is one connected eight-clause cycle.
def successor : Clause → Clause
  | .c1 => .c2 | .c2 => .c3 | .c3 => .c4 | .c4 => .c5
  | .c5 => .c6 | .c6 => .c7 | .c7 => .c8 | .c8 => .c1
theorem successor_edge (clause : Clause) : adjacent clause (successor clause) := by
  cases clause <;> simp [adjacent,rank,successor]
theorem rank_injective : Function.Injective rank := by
  intro left right equal
  cases left <;> cases right <;> simp_all [rank]
theorem cycle_edges_exact (left right : Clause) :
    adjacent left right ↔ successor left=right ∨ successor right=left := by
  cases left <;> cases right <;> simp [adjacent,rank,successor]

theorem unscoped_reach_extend {first middle last : Clause}
    (path : CSTTT.PackageTheory.ScopedReach adjacent (fun (_ : Clause) (_ : Unit) => True) () first middle)
    (edge : adjacent middle last) :
    CSTTT.PackageTheory.ScopedReach adjacent (fun (_ : Clause) (_ : Unit) => True) () first last := by
  induction path with
  | refl middle present => exact .step trivial trivial edge (.refl last trivial)
  | step pi pj earlier tail ih => exact .step pi pj earlier (ih edge)

theorem cycle_connected (clause : Clause) :
    CSTTT.PackageTheory.ScopedReach adjacent (fun (_ : Clause) (_ : Unit) => True) () Clause.c1 clause := by
  have h1 : CSTTT.PackageTheory.ScopedReach adjacent (fun (_ : Clause) (_ : Unit) => True) () Clause.c1 Clause.c1 :=
    .refl Clause.c1 trivial
  have h2 := unscoped_reach_extend h1 (successor_edge .c1)
  have h3 := unscoped_reach_extend h2 (successor_edge .c2)
  have h4 := unscoped_reach_extend h3 (successor_edge .c3)
  have h5 := unscoped_reach_extend h4 (successor_edge .c4)
  have h6 := unscoped_reach_extend h5 (successor_edge .c5)
  have h7 := unscoped_reach_extend h6 (successor_edge .c6)
  have h8 := unscoped_reach_extend h7 (successor_edge .c7)
  cases clause <;> assumption

-- Reject the actual integrated witness, even if it is also required to pass
-- the global package. This is not a failed sufficient gluing criterion.
theorem no_actual_integrated_package :
    ¬∃ global : Assignment,GlobalRestriction global ∧ AssignedPackagePass global .target := by
  rintro ⟨global,restriction,_⟩
  exact no_actual_global_restriction ⟨global,restriction⟩

-- Universally quantify partial inputs before taking the declared scopes.
-- No missing cell is filled to obtain this exact acceptance equivalence.
theorem every_partial_localization_iff (assignment : Assignment) (clause : Clause) :
    clauseAccept (decode (clauseScope .target clause) assignment) .target clause ↔
      clauseAccept assignment .target clause := by
  apply clause_accept_locality .target clause
  intro cell member
  simp [decode,member]

-- Baseline repair: return C6's raw position to the common canonical table.
theorem unshifted_actual_family_glues :
    ∃ global : Assignment,AssignedPackagePass global .target ∧
      ∀ clause cell,cell∈clauseScope .target clause →
        global cell=decode (clauseScope .target clause) canonical cell := by
  refine ⟨canonical,canonical_assigned_package .target,?_⟩
  intro clause cell member
  simp [decode,member]

theorem accepted_complete {assignment : Assignment} (clause : Clause)
    (accepted : clauseAccept assignment .target clause) : Complete (clauseScope .target clause) assignment := by
  cases clause with
  | c1 => exact accepted.1.1.1
  | c2 => exact accepted.1.1.1
  | c3 => exact accepted.1.1.1
  | c4 => exact accepted.1.1.1
  | c5 => exact accepted.1.1
  | c6 => exact accepted.1.1.1
  | c7 => exact accepted.1.1.1
  | c8 => exact accepted.1.1

-- Direct rejection of the actual acceptance predicate, for EVERY partial input.
theorem missing_consumed_rejects (assignment : Assignment) (clause : Clause) (cell : Cell)
    (member : cell∈clauseScope .target clause) (missing : assignment cell=none) :
    ¬clauseAccept assignment .target clause := by
  intro accepted
  have present := accepted_complete clause accepted cell member
  rw [missing] at present
  contradiction

end CSTTT.POS04.Assigned.ActualCyclePrototype
