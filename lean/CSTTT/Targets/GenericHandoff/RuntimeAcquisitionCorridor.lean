import CSTTT.Targets.GenericHandoff.AcquisitionCorridor
import CSTTT.Targets.GenericHandoff.RuntimeExecutionFrontier

/-! The G4 and executed G1c projections read the SAME runtime acquisition
bindings, assignment and execution. Seed instructions are raw coordinate
instructions; their snapshot coherence belongs to the enclosing bridge gate.
-/
namespace CSTTT.TargetTheory.GenericHandoff.RuntimeComponents

variable {Cell R D A O P Factor Resource Residue Stage Id History RouteId : Type}
  {Value : Cell → Type} {RV : R → Type}

def corridor (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (names : AcquisitionCorridor.Names Id)
    (seeds : StaticView Cell Value (AcquisitionCorridor.Seeds History)) :
    AcquisitionCorridor.Raw Cell Value R RV D A O Stage Id History RouteId :=
  ⟨acquisition raw,acquisitionSchema cfg,names,seeds⟩

theorem corridor_frontier_acquisition (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (names : AcquisitionCorridor.Names Id) (seeds : StaticView Cell Value (AcquisitionCorridor.Seeds History))
    (audit : List (History × Nat)) (auditRoute : History × Nat → RouteId) :
    (corridor cfg raw names seeds).acquisition = (frontier cfg raw audit auditRoute).acquisition := rfl

theorem corridor_resource_rows (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (names : AcquisitionCorridor.Names Id) (seeds : StaticView Cell Value (AcquisitionCorridor.Seeds History))
    (a : Assignment Cell Value) (x : RegisterInterpreter.Registers R RV) (d : D) (act : A) :
    AcquisitionExecution.rows (corridor cfg raw names seeds).acquisition a x d act =
      ResourceRuntime.rows (resources raw) a x d act := rfl

end CSTTT.TargetTheory.GenericHandoff.RuntimeComponents
