import CSTTT.FullNative.OriginalPackage
import CSTTT.Prospects.Statements

/-! G28 TTN-14: all-word branch preservation with actual joint-law failure.
The flattened installed program is the G17/G22/G23 preregistered null control,
not a new process or a supplied coupling. Raw world/account/packet execution
generates both sets of receipts. The G27 C7 body itself rejects the flat case. -/
namespace CSTTT.FullNative.RecombinationBoundary
open AccountExecution PhysicalExecution SnapshotExecution SharedPackage OriginalPackage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def branchLaw (right : Bool) (x : Execution) (word : List Bool) (outputs : List Nat) : Rat :=
  Binding.emittedLaw (normalizedRows renewable) (fun e => Binding.branch right e.resident.current) x word outputs
def jointLaw (x : Execution) (word : List Bool) (outputs : List Nat) : Rat :=
  Binding.emittedLaw (normalizedRows renewable) (fun e => Binding.joint e.resident.current) x word outputs
def BranchEqual (x y : Execution) : Prop := ∀ right word outputs,
  branchLaw right x word outputs=branchLaw right y word outputs
def JointEqual (x y : Execution) : Prop := ∀ word outputs, jointLaw x word outputs=jointLaw y word outputs

/-- The strict C7 distinction is measured on actual supported successors,
including their actual issued weights/receipts, not just formal split states. -/
def StrictBinding (x : Execution) : Prop := ∃ y z n m,
  (y,n)∈rawRows renewable x false ∧ (z,m)∈rawRows renewable x false ∧ 0<n ∧ 0<m ∧
  BranchEqual y z ∧ ¬JointEqual y z

def canonical : Raw := sourceRaw
def canonicalExecution : Execution := TemporalTransport.sourceAtCopy
def flattened : Raw := ⟨Credit.flatCycleWorld,0⟩
theorem flat_carrier_present : (flattened.world.carriers 0).isSome=true := by decide +kernel
def flatExecution : Execution := ⟨flattened.world.accounts,
  (flattened.world.carriers 0).get flat_carrier_present⟩
theorem canonical_read : execution canonical=some canonicalExecution := source_read
theorem flattened_read : execution flattened=some flatExecution := by rfl
theorem flat_program_sector : Binding.ProgramSector (flatten model) flatExecution := ⟨rfl,rfl,rfl⟩

theorem actual_branches_preserved : BranchEqual canonicalExecution flatExecution := by
  intro right word outputs
  unfold branchLaw
  rw [Binding.actual_emitted_law (Binding.branch right) canonicalExecution actual_ready.1.1,
    Binding.actual_program_law (flatten model) (Binding.branch right) flatExecution flat_program_sector,
    Binding.flatten_preserves_branches,Binding.branch_all_wordsR,Binding.branch_all_wordsR]

theorem actual_joint_countertrace : jointLaw canonicalExecution [false] [0]=1/8 ∧
    jointLaw flatExecution [false] [0]=1/4 := by
  constructor
  · rw [jointLaw,Binding.actual_emitted_law Binding.joint canonicalExecution actual_ready.1.1]
    decide +kernel
  · rw [jointLaw,Binding.actual_program_law (flatten model) Binding.joint flatExecution flat_program_sector]
    decide +kernel

theorem actual_joint_not_preserved : ¬JointEqual canonicalExecution flatExecution := by
  intro equal
  have bad := equal [false] [0]
  rw [actual_joint_countertrace.1,actual_joint_countertrace.2] at bad
  exact (by decide +kernel : (1/8:Rat)≠1/4) bad

theorem ready_strict_binding (x : Execution) (h : Ready x) : StrictBinding x := by
  have c7 := (computed_certificate x h).c7
  refine ⟨Binding.splitExecution x false,Binding.splitExecution x true,
    weight x.resident.current false false,weight x.resident.current false true,
    Binding.actual_split_supported x h.1 false,Binding.actual_split_supported x h.1 true,
    (Binding.split_supported x.resident.current false).2,
    (Binding.split_supported x.resident.current true).2,c7.2.1,?_⟩
  intro equal
  exact c7.2.2.1 (equal [false] [0])

theorem admitted_c7_is_actual (p : Raw) (accepted : Accept p) :
    ∃ x, execution p=some x ∧ C7 x ∧ StrictBinding x := by
  obtain ⟨x,read,ready,cert⟩ := accepted
  exact ⟨x,read,cert.c7,ready_strict_binding x ready⟩

theorem flat_joint_uniform (x y : Execution)
    (hx : Binding.ProgramSector (flatten model) x) (hy : Binding.ProgramSector (flatten model) y) :
    JointEqual x y := by
  intro word outputs
  rw [jointLaw,jointLaw,Binding.actual_program_law _ _ _ hx,Binding.actual_program_law _ _ _ hy]
  exact Binding.flattening_destroys_joint_gap _ _ word outputs

theorem program_successor (d : Model) (x y : Execution) (h : Binding.ProgramSector d x)
    (a : Bool) (n : Nat) (edge : (y,n)∈rawRows renewable x a) : Binding.ProgramSector d y := by
  rw [Binding.program_rows d x h a] at edge
  obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
  have equal : y=advance renewable x a e.1 e.2 := (congrArg Prod.fst eq).symm
  rw [equal]
  exact Binding.program_sector_preserved d x h a e.1 e.2

theorem flat_actual_strict_binding_rejected : ¬StrictBinding flatExecution := by
  rintro ⟨y,z,n,m,left,right,_,_,_,gap⟩
  exact gap (flat_joint_uniform y z
    (program_successor _ _ _ flat_program_sector false n left)
    (program_successor _ _ _ flat_program_sector false m right))

theorem flat_actual_g27_c7_rejected : ¬C7 flatExecution := by
  intro h
  have left := Binding.program_sector_preserved (flatten model) flatExecution flat_program_sector
    false (Binding.splitState flatExecution.resident.current false) (weight flatExecution.resident.current false false)
  have right := Binding.program_sector_preserved (flatten model) flatExecution flat_program_sector
    false (Binding.splitState flatExecution.resident.current true) (weight flatExecution.resident.current false true)
  exact h.2.2.1 (flat_joint_uniform _ _ left right [false] [0])

theorem flat_program_differs : flatten model≠model := by
  intro equal
  have rows := congrArg (fun d : Model => d.rows FullInterface.rootState false) equal
  exact (by decide +kernel : (flatten model).rows FullInterface.rootState false≠
    model.rows FullInterface.rootState false) rows

theorem flat_ready_rejected : ¬Ready flatExecution := by
  intro h
  have equal : some (flatten model)=some model := h.1.1
  exact flat_program_differs (Option.some.inj equal)

theorem flattened_package_rejected : ¬Accept flattened ∧ ∀ c, ¬clause flattened c :=
  raw_gate_rejected _ _ flattened_read flat_ready_rejected

def BranchTransport (pair : Raw × Raw) : Prop := ∃ x y,
  execution pair.1=some x ∧ execution pair.2=some y ∧ BranchEqual x y
def JointTransport (pair : Raw × Raw) : Prop := ∃ x y,
  execution pair.1=some x ∧ execution pair.2=some y ∧ JointEqual x y

/-- Original generic TTN-14 predicate with the actual installed-program laws.
All complete ordered emitted branch words survive; joint recombination does not. -/
theorem full_ttn14 : CSTTT.Prospects.BranchwiseRecombinationFailure (Raw × Raw)
    BranchTransport JointTransport := by
  refine ⟨(canonical,flattened),⟨_,_,canonical_read,flattened_read,actual_branches_preserved⟩,?_⟩
  rintro ⟨x,y,left,right,equal⟩
  have hx := Option.some.inj (canonical_read.symm.trans left)
  have hy := Option.some.inj (flattened_read.symm.trans right)
  subst x
  subst y
  exact actual_joint_not_preserved equal

theorem full_ttn14_with_actual_readouts :
    Accept canonical ∧ C7 canonicalExecution ∧ StrictBinding canonicalExecution ∧
    BranchEqual canonicalExecution flatExecution ∧ ¬JointEqual canonicalExecution flatExecution ∧
    ¬StrictBinding flatExecution ∧ ¬C7 flatExecution ∧ ¬Accept flattened :=
  ⟨source_and_both_targets.1,(computed_certificate _ actual_ready.1).c7,
    ready_strict_binding _ actual_ready.1,actual_branches_preserved,actual_joint_not_preserved,
    flat_actual_strict_binding_rejected,flat_actual_g27_c7_rejected,flattened_package_rejected.1⟩

end CSTTT.FullNative.RecombinationBoundary
