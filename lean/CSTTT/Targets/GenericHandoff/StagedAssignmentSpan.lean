import CSTTT.Targets.GenericHandoff.BridgeCellReindex
import CSTTT.Targets.GenericHandoff.GlobalStageComposition

/-! A common primitive namespace built from two ACTUAL stage globals. The
middle/final assignments are computed, never supplied. Reindexed raw bridge
programs read their own branch and preserve exact partial semantics. -/
namespace CSTTT.TargetTheory.GenericHandoff.StagedAssignmentSpan
open RegisterInterpreter CellReindex
variable {SC MC TC LI RI R Env X : Type} {SV : SC → Type} {MV : MC → Type} {TV : TC → Type} {RV : R → Type}
abbrev JointValue (MV : MC → Type) (TV : TC → Type) : Sum MC TC → Type
  | .inl k => MV k
  | .inr k => TV k

def join (a : Assignment MC MV) (b : Assignment TC TV) : Assignment (Sum MC TC) (JointValue MV TV)
  | .inl k => a k
  | .inr k => b k

theorem left_pullback (a : Assignment MC MV) (b : Assignment TC TV) :
    pullback Sum.inl (fun _ x => x) (join a b) = a := by
  funext k
  simp [pullback,join]
theorem right_pullback (a : Assignment MC MV) (b : Assignment TC TV) :
    pullback Sum.inr (fun _ x => x) (join a b) = b := by
  funext k
  simp [pullback,join]

variable [DecidableEq MC] [DecidableEq TC]
def span (left : TranslationLanguage SC MC SV MV) (right : TranslationLanguage MC TC MV TV)
    (first : Stage (Index := LI) left) (second : Stage (Index := RI) right)
    (middleCover : RawCover LI MC) (targetCover : RawCover RI TC) (a : Assignment SC SV) :
    Assignment (Sum MC TC) (JointValue MV TV) :=
  join (PackageEngine.global left a first middleCover)
    (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover)

variable (left : TranslationLanguage SC MC SV MV) (right : TranslationLanguage MC TC MV TV)
    (first : Stage (Index := LI) left) (second : Stage (Index := RI) right)
    (middleCover : RawCover LI MC) (targetCover : RawCover RI TC)

theorem middle_equation (a : Assignment SC SV) :
    pullback Sum.inl (fun _ x => x) (span left right first second middleCover targetCover a) =
      PackageEngine.global left a first middleCover := left_pullback _ _
theorem final_equation (a : Assignment SC SV) :
    pullback Sum.inr (fun _ x => x) (span left right first second middleCover targetCover a) =
      PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover := right_pullback _ _

theorem composed_target (a : Assignment SC SV) :
    pullback Sum.inr (fun _ x => x) (span left right first second middleCover targetCover a) =
      PackageEngine.global (StageComposition.language left right) a
        (GlobalStageComposition.stage left right first second middleCover) targetCover :=
  (final_equation left right first second middleCover targetCover a).trans
    (GlobalStageComposition.global_equation left right first second middleCover a targetCover).symm

theorem middle_expression (a : Assignment SC SV) (e : Expr MC MV R RV Env X) (run : Registers R RV) (env : Env) :
    (expression Sum.inl (fun _ x => x) e).eval (span left right first second middleCover targetCover a) run env =
      e.eval (PackageEngine.global left a first middleCover) run env := by
  rw [evaluation,middle_equation]
theorem final_expression (a : Assignment SC SV) (e : Expr TC TV R RV Env X) (run : Registers R RV) (env : Env) :
    (expression Sum.inr (fun _ x => x) e).eval (span left right first second middleCover targetCover a) run env =
      e.eval (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover) run env := by
  rw [evaluation,final_equation]

variable {S T D A O P Q Residue Maintenance Stage Id History RouteId : Type}
    {SRV : S → Type} {TRV : T → Type}
variable [DecidableEq O] [DecidableEq Stage] [DecidableEq P] [DecidableEq Q]
    [DecidableEq Residue] [DecidableEq Maintenance]

theorem middle_bridge_valid_iff
    (r : ExecutionBridge.Raw MC MV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment SC SV) :
    ExecutionBridge.Valid (BridgeCellReindex.raw Sum.inl (fun _ x => x) r)
      (span left right first second middleCover targetCover a) ↔
      ExecutionBridge.Valid r (PackageEngine.global left a first middleCover) := by
  rw [BridgeCellReindex.valid_iff,middle_equation]
theorem final_bridge_valid_iff
    (r : ExecutionBridge.Raw TC TV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment SC SV) :
    ExecutionBridge.Valid (BridgeCellReindex.raw Sum.inr (fun _ x => x) r)
      (span left right first second middleCover targetCover a) ↔
      ExecutionBridge.Valid r
        (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover) := by
  rw [BridgeCellReindex.valid_iff,final_equation]
theorem middle_bridge_semantic_iff
    (r : ExecutionBridge.Raw MC MV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment SC SV) :
    ExecutionBridge.SemanticReadout (BridgeCellReindex.raw Sum.inl (fun _ x => x) r)
      (span left right first second middleCover targetCover a) ↔
      ExecutionBridge.SemanticReadout r (PackageEngine.global left a first middleCover) := by
  rw [BridgeCellReindex.semantic_iff,middle_equation]
theorem final_bridge_semantic_iff
    (r : ExecutionBridge.Raw TC TV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment SC SV) :
    ExecutionBridge.SemanticReadout (BridgeCellReindex.raw Sum.inr (fun _ x => x) r)
      (span left right first second middleCover targetCover a) ↔
      ExecutionBridge.SemanticReadout r
        (PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover) := by
  rw [BridgeCellReindex.semantic_iff,final_equation]

end CSTTT.TargetTheory.GenericHandoff.StagedAssignmentSpan
