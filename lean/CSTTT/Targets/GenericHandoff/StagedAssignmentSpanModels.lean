import CSTTT.Targets.GenericHandoff.StagedAssignmentSpan
import CSTTT.Targets.GenericHandoff.StageCompositionModels
import CSTTT.Targets.GenericHandoff.POS04DispatchedComposition
import CSTTT.Targets.GenericHandoff.POS04ExecutionBridge

/-! Actual numerical assignment span and native executed-bridge specialization.
The native stages are the existing package exchange, not a new physical hop. -/
namespace CSTTT.TargetTheory.GenericHandoff.StagedAssignmentSpanModels
open RegisterInterpreter CellReindex
open StageCompositionModels
def span (a : Assignment Unit (fun _ => Nat)) :=
  StagedAssignmentSpan.span add multiply first second cover cover a
abbrev NumericValue := StagedAssignmentSpan.JointValue (fun _ : Unit => Nat) (fun _ : Unit => Nat)
def readBoth : Expr (Sum Unit Unit) NumericValue Empty RegisterInitialization.NoValue Unit Nat :=
  .map (fun p => p.1 + p.2) (.pair (.cell (.inl ())) (.cell (.inr ())))
def sameContext : Expr (Sum Unit Unit) NumericValue Empty RegisterInitialization.NoValue Unit Nat :=
  .map (fun p => p.1 + p.2) (.pair (.cell (.inl ())) (.cell (.inl ())))
def output (a : Assignment Unit (fun _ => Nat)) :=
  readBoth.eval (span a) RegisterInitialization.noRegisters ()
def shortcut (a : Assignment Unit (fun _ => Nat)) :=
  sameContext.eval (span a) RegisterInitialization.noRegisters ()
def positive : Assignment Unit (fun _ => Nat) := fun _ => some positiveValue
def limit : Nat := 3
def rejectAbove : TranslationLanguage Unit Unit (fun _ => Nat) (fun _ => Nat) where
  Instruction _ _ := Nat
  execute n value := if value ≤ limit then some (value+n) else none
def partialFirst : Stage (Index := Unit) rejectAbove := fun _ _ => some ⟨(),increment⟩
def rejectedValue : Nat := 4
def rejectedSource : Assignment Unit (fun _ => Nat) := fun _ => some rejectedValue
def partialSpan (a : Assignment Unit (fun _ => Nat)) :=
  StagedAssignmentSpan.span rejectAbove multiply partialFirst second cover cover a
def partialOutput (a : Assignment Unit (fun _ => Nat)) :=
  readBoth.eval (partialSpan a) RegisterInitialization.noRegisters ()
def rightCutSpan (a : Assignment Unit (fun _ => Nat)) :=
  StagedAssignmentSpan.span add multiply first absentRight cover cover a
def rightCutOutput (a : Assignment Unit (fun _ => Nat)) :=
  readBoth.eval (rightCutSpan a) RegisterInitialization.noRegisters ()

theorem middle_cell (a : Assignment Unit (fun _ => Nat)) :
    span a (.inl ()) = (a ()).map (fun n => n+increment) := by
  cases h : a () <;> simp [span,StagedAssignmentSpan.span,StagedAssignmentSpan.join,
    PackageEngine.global,glued,firstCover,mappedLocal,first,cover,scopes,add,h]
theorem final_cell (a : Assignment Unit (fun _ => Nat)) :
    span a (.inr ()) = (a ()).map (fun n => (n+increment)*multiplier) := by
  change PackageEngine.global multiply (PackageEngine.global add a first cover) second cover () = _
  rw [← GlobalStageComposition.global_equation add multiply first second cover a cover]
  cases h : a () <;> simp [PackageEngine.global,glued,firstCover,mappedLocal,cover,scopes,
    GlobalStageComposition.stage,GlobalStageComposition.selectedArrow,StageComposition.language,first,second,add,multiply,h]
theorem output_equation (a : Assignment Unit (fun _ => Nat)) :
    output a = (a ()).map (fun n => (n+increment)+(n+increment)*multiplier) := by
  simp only [output,readBoth,Expr.eval,middle_cell,final_cell]
  cases a () <;> rfl
theorem shortcut_equation (a : Assignment Unit (fun _ => Nat)) :
    shortcut a = (a ()).map (fun n => (n+increment)+(n+increment)) := by
  simp only [shortcut,sameContext,Expr.eval,middle_cell]
  cases a () <;> rfl
theorem source_missing (a : Assignment Unit (fun _ => Nat)) (h : a () = none) : output a = none := by
  rw [output_equation,h]; rfl
theorem positive_readout : output positive = some 12 := by rw [output_equation]; rfl
theorem same_context_readout : shortcut positive = some 8 := by rw [shortcut_equation]; rfl
theorem same_context_not_equivalent :
    ¬ ∀ a : Assignment Unit (fun _ => Nat), output a = shortcut a := by
  intro h
  have he := h positive
  rw [positive_readout,same_context_readout] at he
  contradiction
theorem right_cut (a : Assignment Unit (fun _ => Nat)) : rightCutOutput a = none := by
  simp [rightCutOutput,readBoth,Expr.eval,rightCutSpan,StagedAssignmentSpan.span,
    StagedAssignmentSpan.join,PackageEngine.global,glued,firstCover,mappedLocal,
    absentRight,cover,scopes]
theorem partial_first_rejects : partialOutput rejectedSource = none := by
  decide +kernel
theorem rejected_source_present : (rejectedSource ()).isSome = true := rfl
theorem partial_positive : partialOutput positive = some 12 := by decide +kernel

open CSTTT.POS04 CSTTT.POS04.Assigned
open CSTTT.TargetTheory.ComputedFIACH
def nativeSpan (a : CSTTT.POS04.Assigned.Assignment) :=
  StagedAssignmentSpan.span POS04DispatchedStage.raw.language POS04DispatchedStage.raw.language
    POS04DispatchedStage.raw.stage POS04DispatchedStage.raw.stage
    POS04DispatchedStage.raw.cover POS04DispatchedStage.raw.cover a
def nativeBridge := BridgeCellReindex.raw (TC := Sum Cell Cell)
  (TV := StagedAssignmentSpan.JointValue Value Value)
  Sum.inr (fun _ x => x) POS04ExecutionBridge.raw

theorem native_final_pullback (a : CSTTT.POS04.Assigned.Assignment) :
    pullback Sum.inr (fun _ x => x) (nativeSpan a) = a := by
  dsimp only [nativeSpan]
  rw [StagedAssignmentSpan.final_equation]
  exact (DispatchedComposition.target_equation POS04DispatchedStage.raw POS04DispatchedStage.raw a).symm.trans
    (POS04DispatchedComposition.target_equation a)
theorem native_middle_pullback (a : CSTTT.POS04.Assigned.Assignment) :
    pullback Sum.inl (fun _ x => x) (nativeSpan a) = image a := by
  dsimp only [nativeSpan]
  rw [StagedAssignmentSpan.middle_equation]
  exact POS04DispatchedStage.global_eq_image a
theorem native_valid_iff (a : CSTTT.POS04.Assigned.Assignment) :
    ExecutionBridge.Valid nativeBridge (nativeSpan a) ↔ ExecutionBridge.Valid POS04ExecutionBridge.raw a := by
  dsimp only [nativeBridge]
  rw [BridgeCellReindex.valid_iff,native_final_pullback]
theorem native_semantic_iff (a : CSTTT.POS04.Assigned.Assignment) :
    ExecutionBridge.SemanticReadout nativeBridge (nativeSpan a) ↔
      ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw a := by
  dsimp only [nativeBridge]
  rw [BridgeCellReindex.semantic_iff,native_final_pullback]
theorem native_positive : ExecutionBridge.Valid nativeBridge (nativeSpan canonical) :=
  (native_valid_iff canonical).mpr POS04ExecutionBridge.positive
theorem native_semantic_positive : ExecutionBridge.SemanticReadout nativeBridge (nativeSpan canonical) :=
  ExecutionBridge.semantic_soundness _ _ native_positive
theorem native_deleted_atomic_no_readout (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ ExecutionBridge.SemanticReadout nativeBridge (nativeSpan (Assigned.put a .eventTable none)) := by
  rw [native_semantic_iff]
  apply ExecutionBridge.missing_atomic_no_semantic_readout
  simp [POS04ExecutionBridge.raw,POS04ExecutionFrontier.raw,POS04ExecutionFrontier.acquisition,
    POS04ExecutionFrontier.eventView,CellView.read]

end CSTTT.TargetTheory.GenericHandoff.StagedAssignmentSpanModels
