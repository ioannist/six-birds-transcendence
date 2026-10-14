import CSTTT.POS04.Assigned.Adapters

/-! G2a sensitivity guards. Single-cell corruptions are method-level probes,
not newly registered scientific models. Whole-table cells retain exact types;
the declared model's row interventions are separately proved in Adapters. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit

/-- Every missing required cell rejects its clause; totalization cannot bypass
this gate. This is quantified over all assignments, not only canonical data. -/
theorem c1_missing_rejected (a : Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c1) : ¬ C1Accept (put a k none) tag := by
  intro h
  exact missing_cell_rejected _ a k hk h.1.1.1

theorem c2_missing_rejected (a : Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c2) : ¬ C2Accept (put a k none) tag := by
  intro h
  exact missing_cell_rejected _ a k hk h.1.1.1

theorem c3_missing_rejected (a : Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c3) : ¬ C3Accept (put a k none) tag := by
  intro h
  exact missing_cell_rejected _ a k hk h.1.1.1

/-- Deleting any required scoped read fails at decoding as well as the gate. -/
theorem scope_deletion_rejected (tag : Tag) (c : Clause) (k : Cell)
    (hk : k ∈ clauseScope tag c) :
    ¬ Complete (clauseScope tag c) (decode ((clauseScope tag c).filter fun j => decide (j ≠ k)) canonical) := by
  intro hc
  have hnone : decode ((clauseScope tag c).filter fun j => decide (j ≠ k)) canonical k = none := by
    apply decoder_outside
    simp
  have h := hc k hk
  rw [hnone] at h
  contradiction

/-- Whole-table field probes have no verdict field and change just one cell. -/
def noRows (a : Assignment) (tag : Tag) :=
  put a (.rows tag) (some (fun _ _ => []))
def flatPositions (a : Assignment) := put a .positions (some (fun _ => 0))
def noHazards (a : Assignment) := put a .hazards (some (fun _ => false))
def stayPolicy (a : Assignment) := put a .policy (some (fun _ => .stay))
def repeatedPrototypes (a : Assignment) :=
  put a .prototypes (some (List.replicate 7 .p0w0))
def zeroP (a : Assignment) := put a .publishedP (some (fun _ _ => 0))
def zeroC (a : Assignment) := put a .publishedC (some (fun _ _ => 0))
def zeroU (a : Assignment) := put a .publishedU (some (fun _ _ => 0))
def flatM (a : Assignment) := put a .publishedM (some (fun _ => 0))
def wrongTau (a : Assignment) := put a .audit (some ⟨1,c1Epsilon,c1RetentionThreshold⟩)

theorem c1_rows_guard (tag : Tag) : ¬ C1Accept (noRows canonical tag) tag := by
  intro h
  have he := h.1.2.2.2.2.2.2.2.1 .p1w0 .p2w1
  cases tag <;> change (0 : Nat) = 4 at he <;> contradiction

theorem c1_policy_guard (tag : Tag) : ¬ C1Accept (stayPolicy canonical) tag := by
  intro h
  have he := h.1.2.2.2.2.2.2.2.1 .p1w0 .p2w1
  cases tag <;> change (0 : Nat) = 4 at he <;> contradiction

theorem c1_positions_guard (tag : Tag) : ¬ C1Accept (flatPositions canonical) tag := by
  intro h
  have hn : ¬ (classOrder (clauseInputs (flatPositions canonical) tag .c1)).Nodup := by
    cases tag <;> decide
  exact hn h.1.2.2.2.2.2.1

theorem c1_hazards_guard (tag : Tag) : ¬ C1Accept (noHazards canonical) tag := by
  intro h
  have hn : ¬ (classOrder (clauseInputs (noHazards canonical) tag .c1)).Nodup := by
    cases tag <;> decide
  exact hn h.1.2.2.2.2.2.1

theorem c1_prototypes_guard (tag : Tag) : ¬ C1Accept (repeatedPrototypes canonical) tag := by
  intro h
  have hn : ¬ (classOrder (clauseInputs (repeatedPrototypes canonical) tag .c1)).Nodup := by
    cases tag <;> decide
  exact hn h.1.2.2.2.2.2.1

theorem c1_P_guard (tag : Tag) : ¬ C1Accept (zeroP canonical) tag := by
  intro h
  have he := congrFun (congrFun h.1.2.1.2.1 0) 2
  cases tag <;> change (0 : Nat) = 2 at he <;> contradiction

theorem c1_C_guard (tag : Tag) : ¬ C1Accept (zeroC canonical) tag := by
  intro h
  have he := congrFun (congrFun h.1.2.1.2.2.1 0) 0
  cases tag <;> change (0 : Nat) = 1 at he <;> contradiction

theorem c1_U_guard (tag : Tag) : ¬ C1Accept (zeroU canonical) tag := by
  intro h
  have he := congrFun (congrFun h.1.2.1.2.2.2 0) 0
  cases tag <;> change (0 : Nat) = 1 at he <;> contradiction

theorem c1_tau_guard (tag : Tag) : ¬ C1Accept (wrongTau canonical) tag := by
  intro h
  have he := congrArg AuditParameters.tau h.1.2.1.1
  cases tag <;> change (1 : Nat) = 2 at he <;> contradiction

def wrongEpsilon (a : Assignment) := put a .audit (some ⟨c1Tau,0,c1RetentionThreshold⟩)
def wrongRetention (a : Assignment) := put a .audit (some ⟨c1Tau,c1Epsilon,0⟩)

theorem c1_epsilon_guard (tag : Tag) : ¬ C1Accept (wrongEpsilon canonical) tag := by
  intro h
  have he := congrArg AuditParameters.epsilon h.1.2.1.1
  have hn : (0 : Rat) ≠ 1/16 := by grind
  cases tag <;> exact hn he

theorem c1_retention_guard (tag : Tag) : ¬ C1Accept (wrongRetention canonical) tag := by
  intro h
  have he := congrArg AuditParameters.retention h.1.2.1.1
  have hn : (0 : Rat) ≠ 3/4 := by grind
  cases tag <;> exact hn he

theorem c2_rows_guard (tag : Tag) : ¬ C2Accept (noRows canonical tag) tag := by
  intro h
  have hr : predictive (clauseInputs (noRows canonical tag) tag .c2) .p1w0 =
      predictive (clauseInputs (noRows canonical tag) tag .c2) .p1w1 := by
    cases tag <;> decide
  have he := (h.1.2.2 .p1w0 .p1w1).mp hr
  cases tag <;> change (1 : Nat) = 2 at he <;> contradiction

theorem c2_positions_guard (tag : Tag) : ¬ C2Accept (flatPositions canonical) tag := by
  intro h
  have hr : predictive (clauseInputs (flatPositions canonical) tag .c2) .p0w0 =
      predictive (clauseInputs (flatPositions canonical) tag .c2) .p3w0 := by
    cases tag <;> decide
  have he := (h.1.2.2 .p0w0 .p3w0).mp hr
  cases tag <;> change (0 : Nat) = 4 at he <;> contradiction

theorem c2_hazards_guard (tag : Tag) : ¬ C2Accept (noHazards canonical) tag := by
  intro h
  have hr : predictive (clauseInputs (noHazards canonical) tag .c2) .p1w0 =
      predictive (clauseInputs (noHazards canonical) tag .c2) .p1w1 := by
    cases tag <;> decide
  have he := (h.1.2.2 .p1w0 .p1w1).mp hr
  cases tag <;> change (1 : Nat) = 2 at he <;> contradiction

theorem c2_M_guard (tag : Tag) : ¬ C2Accept (flatM canonical) tag := by
  intro h
  have he := congrFun h.1.2.1 .p1w0
  cases tag <;> change (0 : Nat) = 1 at he <;> contradiction

theorem c3_rows_guard (tag : Tag) : ¬ C3Accept (noRows canonical tag) tag := by
  intro h
  have hr : predictive (clauseInputs (noRows canonical tag) tag .c3) .p1w0 =
      predictive (clauseInputs (noRows canonical tag) tag .c3) .p1w1 := by
    cases tag <;> decide
  have he := (h.1.2.2 .p1w0 .p1w1).mp hr
  cases tag <;> change (1 : Nat) = 2 at he <;> contradiction

theorem c3_positions_guard (tag : Tag) : ¬ C3Accept (flatPositions canonical) tag := by
  intro h
  have hr : predictive (clauseInputs (flatPositions canonical) tag .c3) .p0w0 =
      predictive (clauseInputs (flatPositions canonical) tag .c3) .p3w0 := by
    cases tag <;> decide
  have he := (h.1.2.2 .p0w0 .p3w0).mp hr
  cases tag <;> change (0 : Nat) = 4 at he <;> contradiction

theorem c3_hazards_guard (tag : Tag) : ¬ C3Accept (noHazards canonical) tag := by
  intro h
  have hr : predictive (clauseInputs (noHazards canonical) tag .c3) .p1w0 =
      predictive (clauseInputs (noHazards canonical) tag .c3) .p1w1 := by
    cases tag <;> decide
  have he := (h.1.2.2 .p1w0 .p1w1).mp hr
  cases tag <;> change (1 : Nat) = 2 at he <;> contradiction

theorem c3_M_guard (tag : Tag) : ¬ C3Accept (flatM canonical) tag := by
  intro h
  have he := congrFun h.1.2.1 .p1w0
  cases tag <;> change (0 : Nat) = 1 at he <;> contradiction

theorem c2_lower_guard (tag : Tag) :
    ¬ C2Accept (put canonical (.lower tag) (some .stateLabel)) tag := by
  intro h
  have hn : lower (clauseInputs (put canonical (.lower tag) (some .stateLabel)) tag .c2) .p1w0 ≠
      lower (clauseInputs (put canonical (.lower tag) (some .stateLabel)) tag .c2) .p1w1 := by
    cases tag <;> decide
  exact hn h.2.1

theorem c3_lower_guard (tag : Tag) :
    ¬ C3Accept (put canonical (.lower tag) (some .stateLabel)) tag := by
  intro h
  have hn : classCount (seed (clauseInputs
      (put canonical (.lower tag) (some .stateLabel)) tag .c3)) ≠ 6 := by
    cases tag <;> decide
  exact hn h.2.1

/-- Same typed row, invalid mass (three fourths rather than one). This tests
input validity itself, independently of the later clause-specific rule. -/
def malformedRows (a : Assignment) (tag : Tag) :=
  editRow a tag .p0w0 .cw [(.inK .p1w0,3)]

theorem malformed_rows_gates_reject (tag : Tag) :
    ¬ C1Gate (malformedRows canonical tag) tag ∧
    ¬ C2Gate (malformedRows canonical tag) tag ∧
    ¬ C3Gate (malformedRows canonical tag) tag := by
  have h1 : ¬ RowsValid (clauseInputs (malformedRows canonical tag) tag .c1) := by
    unfold RowsValid
    cases tag <;> decide
  have h2 : ¬ RowsValid (clauseInputs (malformedRows canonical tag) tag .c2) := by
    unfold RowsValid
    cases tag <;> decide
  have h3 : ¬ RowsValid (clauseInputs (malformedRows canonical tag) tag .c3) := by
    unfold RowsValid
    cases tag <;> decide
  exact ⟨fun h => h1 h.1.2,fun h => h2 h.1.2,fun h => h3 h.1.2⟩

end CSTTT.POS04.Assigned

