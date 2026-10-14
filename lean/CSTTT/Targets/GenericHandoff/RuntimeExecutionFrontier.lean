import CSTTT.Targets.GenericHandoff.ExecutionFrontier
import CSTTT.Targets.GenericHandoff.RuntimeComponents

/-! Defined acquisition/future audit of the shared runtime component. The
only extra data are raw finite audit selectors. All execution, observation,
code, probability, updater and closure objects are projections of that same
runtime; none can be substituted at this boundary. -/
namespace CSTTT.TargetTheory.GenericHandoff.RuntimeComponents
open RegisterInterpreter
variable {Cell R D A O P Factor Resource Residue Stage Id History RouteId : Type}
    {Value : Cell → Type} {RV : R → Type}

def frontier (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (audit : List (History × Nat)) (auditRoute : History × Nat → RouteId) :
    ExecutionFrontier.Raw Cell Value R RV D A O P Residue (List ResourceRuntime.Account) Stage Id History RouteId :=
  ⟨acquisition raw,(temporal cfg raw).readouts,raw.readoutRecipes,cfg.tickPeriod,audit,
    acquisitionSchema cfg,auditRoute⟩

theorem frontier_temporal (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (audit : List (History × Nat)) (route : History × Nat → RouteId) :
    ExecutionFrontier.temporal (frontier cfg raw audit route) = temporal cfg raw := rfl

theorem frontier_ready_iff (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (audit : List (History × Nat)) (route : History × Nat → RouteId) (a : Assignment Cell Value) :
    ExecutionFrontier.Ready (frontier cfg raw audit route) a ↔
      AcquisitionExecution.Ready (acquisition raw) a ∧ RegisterFuture.RawReady (temporal cfg raw) a := Iff.rfl

theorem frontier_rows (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (audit : List (History × Nat)) (route : History × Nat → RouteId) (a : Assignment Cell Value)
    (h : ExecutionFrontier.Ready (frontier cfg raw audit route) a)
    (x : Registers R RV) (d : D) (act : A) :
    RegisterFuture.row (ExecutionFrontier.temporal (frontier cfg raw audit route)) a h.2 x (d,act) =
      ResourceRuntime.rows (resources raw) a x d act := by
  exact ExecutionFrontier.rows_shared _ a h x d act

theorem frontier_update (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (audit : List (History × Nat)) (route : History × Nat → RouteId) (a : Assignment Cell Value)
    (h : ExecutionFrontier.Ready (frontier cfg raw audit route) a)
    (hr : ResourceRuntime.Ready (resources raw) a) (x : Registers R RV) (d : D) (act : A) (o : O) :
    RegisterFuture.next (ExecutionFrontier.temporal (frontier cfg raw audit route)) a h.2 x (d,act) o =
      ResourceRuntime.update (resources raw) a hr x d act o := rfl
end CSTTT.TargetTheory.GenericHandoff.RuntimeComponents
