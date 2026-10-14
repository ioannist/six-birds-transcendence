import CSTTT.Targets.GenericHandoff.ExecutionBridgeComposition
import CSTTT.Targets.GenericHandoff.POS04ExecutionBridge

/-! Predeclared typed-register instruction fixture and inhabited executed
bridge specialization. The identity continuation is not a physical new hop. -/
namespace CSTTT.TargetTheory.GenericHandoff.RegisterCompositionModels
open RegisterInterpreter RegisterSubstitution
abbrev CellValue (_ : Bool) := Nat
abbrev MiddleValue : Bool → Type | false => Nat | true => Bool
def multiplier : Nat := 2
def sourceValue : Nat := 5
def first : (r : Bool) → Expr Bool CellValue Unit (fun _ => Nat) Unit (MiddleValue r)
  | false => .map (fun p => p.1 + p.2) (.pair (.register ()) (.cell false))
  | true => .map (fun n => decide (n > 0)) (.cell true)
def second : Unit → Expr Bool CellValue Bool MiddleValue Unit Nat :=
  fun _ => .map (fun n => n * multiplier) (.register false)
def eager : Expr Bool CellValue Bool MiddleValue Unit Nat :=
  .choose (.literal true) (.register false) (.map (fun b => if b then 99 else 0) (.register true))
def output (a : Assignment Bool CellValue) : Option Nat :=
  (program first second ()).eval a (fun _ => sourceValue) ()
def eagerOutput (a : Assignment Bool CellValue) : Option Nat :=
  (substitute first eager).eval a (fun _ => sourceValue) ()
def positive : Assignment Bool CellValue | false => some 3 | true => some 1
def consumedCut : Assignment Bool CellValue | false => none | true => some 1
def unusedCut : Assignment Bool CellValue | false => some 3 | true => none
def changed : Assignment Bool CellValue | false => some 4 | true => some 1

theorem output_equation (a : Assignment Bool CellValue) :
    output a = (a false).map (fun n => (sourceValue + n) * multiplier) := by
  simp [output,program,substitute,first,second,Expr.eval]
  cases a false <;> rfl

theorem ready_iff (a : Assignment Bool CellValue) :
    Ready (program first second) a ↔ a false ≠ none := by
  simp only [Ready,Complete,program,substitute,first,second,Expr.dependencies,List.mem_append,
    List.mem_singleton,List.not_mem_nil,false_or]
  cases h : a false <;> simp [h]

theorem consumed_missing : output consumedCut = none := by rw [output_equation]; rfl
theorem unused_missing : output unusedCut = some 16 := by rw [output_equation]; rfl
theorem unused_prefix_not_ready : ¬ Ready first unusedCut := by
  intro h
  have hc := h true true (by simp [first,Expr.dependencies])
  simp [unusedCut] at hc
theorem unused_composite_ready : Ready (program first second) unusedCut :=
  (ready_iff unusedCut).mpr (by decide +kernel)
theorem eager_missing : eagerOutput unusedCut = none := by
  exact missing_consumed_register first eager unusedCut true true
    (by simp [eager,reads]) (by simp [first,Expr.dependencies]) rfl _ ()
theorem positive_readout : output positive = some 16 := by rw [output_equation]; rfl
theorem changed_readout : output changed = some 18 := by rw [output_equation]; rfl
theorem instruction_effect : output positive ≠ output changed := by
  rw [positive_readout,changed_readout]; decide +kernel

def continuation := ExecutionBridge.identityRaw POS04ReceiverFrontier.raw
def bridge := ExecutionBridgeComposition.compose POS04ExecutionBridge.raw continuation
theorem bridge_positive : ExecutionBridge.Valid bridge CSTTT.POS04.Assigned.canonical :=
  ExecutionBridgeComposition.valid POS04ExecutionBridge.raw continuation rfl _
    POS04ExecutionBridge.positive
    ((ExecutionBridge.identity_valid_iff POS04ReceiverFrontier.raw _).mpr POS04ReceiverFrontier.positive)

theorem bridge_initial_translation
    (h : ExecutionBridge.TranslationReady bridge CSTTT.POS04.Assigned.canonical)
    (x : Registers POS04RegisterDynamics.Register POS04RegisterDynamics.RegisterValue) :
    ExecutionBridge.translate bridge CSTTT.POS04.Assigned.canonical h x = x := by
  funext r
  exact Option.some.inj ((ExecutionBridge.translate_equation bridge _ h x r).symm)

theorem middle_closure
    (hs : ExecutionFrontier.Ready POS04ExecutionBridge.raw.source CSTTT.POS04.Assigned.canonical)
    (ht : ExecutionFrontier.Ready POS04ExecutionBridge.raw.target CSTTT.POS04.Assigned.canonical)
    (x : Registers POS04RegisterDynamics.Register POS04RegisterDynamics.RegisterValue)
    (hx : ExecutionFrontier.Closure POS04ExecutionBridge.raw.source CSTTT.POS04.Assigned.canonical hs x) :
    ExecutionFrontier.Closure POS04ExecutionBridge.raw.target CSTTT.POS04.Assigned.canonical ht x := by
  have hc := ExecutionBridgeComposition.closure_transport POS04ExecutionBridge.raw _
    hs ht (POS04ExecutionBridge.translation_ready _) (POS04ExecutionBridge.canonical_laws hs ht)
    POS04ExecutionFrontier.canonical_domain.1 POS04ExecutionFrontier.canonical_domain.2 x hx
  rw [POS04ExecutionBridge.translate_eq] at hc
  exact hc

end CSTTT.TargetTheory.GenericHandoff.RegisterCompositionModels
