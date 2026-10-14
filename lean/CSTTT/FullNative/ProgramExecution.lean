import CSTTT.FullNative.BranchBinding

/-! Derived all-word and actual-execution obligations for frozen FULL-NATIVE-01. -/
namespace CSTTT.FullNative.Binding
set_option autoImplicit false
set_option maxHeartbeats 8000000

def ProgramSector (d : Model) (x : PhysicalExecution.Execution) : Prop :=
  x.resident.installed=some d ∧
  x.accounts.allocation x.resident.token=some (.localGenerator x.resident.owner) ∧
  x.accounts.charge x.resident.token=true

theorem program_sector_preserved (d : Model) (x : PhysicalExecution.Execution)
    (h : ProgramSector d x) (a : Bool) (s : State) (n : Nat) :
    ProgramSector d (PhysicalExecution.advance AccountExecution.renewable x a s n) :=
  ⟨h.1,h.2.1,AccountExecution.renewable_charge x.accounts x.resident.token⟩

theorem program_rows (d : Model) (x : PhysicalExecution.Execution) (h : ProgramSector d x) (a : Bool) :
    PhysicalExecution.rawRows AccountExecution.renewable x a=
      (d.rows x.resident.current a).map fun e =>
        (PhysicalExecution.advance AccountExecution.renewable x a e.1 e.2,e.2) := by
  have enabled : AccountExecution.enabled x.accounts x.resident.owner x.resident.token=true := by
    simp [AccountExecution.enabled,h.2.1,h.2.2]
  simp [PhysicalExecution.rawRows,h.1,enabled]

theorem actual_program_law (d : Model) (observe : State → Nat) (x : PhysicalExecution.Execution)
    (h : ProgramSector d x) (word : List Bool) (outputs : List Nat) :
    emittedLaw (PhysicalExecution.normalizedRows AccountExecution.renewable)
      (fun x => observe x.resident.current) x word outputs=
    emittedLaw (rationalRows d) observe x.resident.current word outputs := by
  induction word generalizing x outputs with
  | nil => cases outputs <;> rfl
  | cons a rest ih =>
    cases outputs with
    | nil => rfl
    | cons o os =>
      simp only [emittedLaw,PhysicalExecution.normalizedRows,program_rows d x h a,
        rationalRows,List.foldr_map]
      congr 1
      funext e acc
      exact congrArg (fun z => (if observe e.1=o then (e.2:Rat)/16*z else 0)+acc)
        (ih (PhysicalExecution.advance AccountExecution.renewable x a e.1 e.2)
          (program_sector_preserved d x h a e.1 e.2) os)

theorem actual_emitted_law (observe : State → Nat) (x : PhysicalExecution.Execution)
    (h : PhysicalExecution.sector x) (word : List Bool) (outputs : List Nat) :
    emittedLaw (PhysicalExecution.normalizedRows AccountExecution.renewable)
      (fun x => observe x.resident.current) x word outputs=
    emittedLaw (rationalRows model) observe x.resident.current word outputs := by
  induction word generalizing x outputs with
  | nil => cases outputs <;> rfl
  | cons a rest ih =>
    cases outputs with
    | nil => rfl
    | cons o os =>
      simp only [emittedLaw,PhysicalExecution.normalizedRows,
        PhysicalExecution.sector_rows x h a,rationalRows,model,List.foldr_map]
      congr 1
      funext e acc
      exact congrArg (fun z => (if observe e.1=o then (e.2:Rat)/16*z else 0)+acc)
        (ih (PhysicalExecution.advance AccountExecution.renewable x a e.1 e.2)
          (PhysicalExecution.sector_preserved x h a e.1 e.2) os)

end CSTTT.FullNative.Binding
