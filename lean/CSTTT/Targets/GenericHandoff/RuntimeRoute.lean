import CSTTT.Targets.GenericHandoff.RuntimeExecutionFrontier
import CSTTT.Targets.GenericHandoff.RouteComponent

/-! Shared-runtime route binding for TTH-06. Acquisition, register, owner,
rows and updater are projections of one raw runtime. The only additional raw
instructions describe provenance encoding, the declared future probe and the
endpoint coordinate. No result table or route status is supplied.

The readout is the FULL Indexed/Retained comparison: distinct raw paths, a
shared arrival endpoint, and preservation on EVERY actual response branch.
This component does not by itself certify the G1c execution bridge. -/
namespace CSTTT.TargetTheory.GenericHandoff.RuntimeComponents
open RegisterInterpreter

structure RouteInstructions (Cell : Type) (Value : Cell → Type) (R : Type)
    (RV : R → Type) (D A O Id History Residue Endpoint : Type) where
  provenance : StaticView Cell Value (History → List (D × A × O) → List Id → Residue)
  probe : Expr Cell Value R RV Unit (Option Nat)
  endpoint : Expr Cell Value R RV Unit Endpoint

variable {Cell R D A O P Factor Resource Residue Endpoint Stage Id History RouteId : Type}
    {Value : Cell → Type} {RV : R → Type}

def route (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint) :
    RouteComponent.Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint where
  acquisition := acquisition raw
  provenance := instructions.provenance
  register := raw.resource.residue
  readout := instructions.probe
  owner := (temporal cfg raw).readouts.owner
  endpoint := instructions.endpoint

theorem route_rows_shared (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value) (x : Registers R RV) (d : D) (act : A) :
    AcquisitionExecution.rows (route cfg raw instructions).acquisition a x d act =
      ResourceRuntime.rows (resources raw) a x d act := rfl

theorem route_update_shared (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value)
    (ha : AcquisitionExecution.Ready (route cfg raw instructions).acquisition a)
    (hr : ResourceRuntime.Ready (resources raw) a)
    (x : Registers R RV) (d : D) (act : A) (o : O) :
    AcquisitionExecution.update (route cfg raw instructions).acquisition a ha x d act o =
      ResourceRuntime.update (resources raw) a hr x d act o := rfl

theorem route_owner_from_resources (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value) (x : Registers R RV)
    (h : ResourceRuntime.ResourceClosed (resourceSchema cfg) (resources raw) a x) :
    (route cfg raw instructions).owner.eval a x () = some cfg.target :=
  resource_owner_link cfg raw a x h

variable [DecidableEq Stage]

/-- Semantic readout, not the weaker ExecutedMemory witness. -/
def RetainedRouteReadout (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value) : Prop :=
  ∃ h : RouteComponent.Ready (route cfg raw instructions) a,
    RouteComponent.Indexed (acquisitionSchema cfg) (route cfg raw instructions) a h.1

noncomputable def retainedRouteStatus (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value) : CSTTT.RouteStatus :=
  RouteComponent.statusOf (acquisitionSchema cfg) (route cfg raw instructions) a

theorem retained_route_status_iff (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value) : retainedRouteStatus cfg raw instructions a = .routeIndexed ↔
      RetainedRouteReadout cfg raw instructions a :=
  RouteComponent.status_indexed_iff _ _ _

theorem retained_route_never_flat (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value) : retainedRouteStatus cfg raw instructions a ≠ .flat :=
  RouteComponent.never_flat _ _ _

/-- An actual route result uses the SAME resource updater and positive
support. This does not replace historical-support entries in the autonomy
lane with acquisition history or acquisition resources. -/
theorem retained_result_shared (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value)
    (ha : AcquisitionExecution.Ready (acquisition raw) a)
    (hr : ResourceRuntime.Ready (resources raw) a) (rid : RouteId) (entry : Registers R RV)
    (he : RouteComponent.Result (acquisitionSchema cfg) (route cfg raw instructions) a ha rid entry) :
    ∃ arrived d act o, AcquisitionExecution.Arrival (acquisitionSchema cfg) (acquisition raw) a ha rid arrived ∧
      StrategyGame.PositiveSupport (ResourceRuntime.rows (resources raw) a) arrived d act o ∧
      entry = ResourceRuntime.update (resources raw) a hr arrived d act o :=
  RouteComponent.result_actual_update _ _ _ _ _ _ he

/-- Explicitly retain the entire comparison, not only one favorable pair of
post-exit samples. Both Retained obligations cover every response branch. -/
theorem retained_route_comparison (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value) (h : RetainedRouteReadout cfg raw instructions a) :
    ∃ ready : RouteComponent.Ready (route cfg raw instructions) a,
      ∃ r s, r ∈ cfg.routes ∧ s ∈ cfg.routes ∧ r ≠ s ∧
        RouteComponent.pathIdentity (route cfg raw instructions) a r ≠
          RouteComponent.pathIdentity (route cfg raw instructions) a s ∧
        ∃ rr sr nr ns endpoint, rr ≠ sr ∧ nr ≠ ns ∧
          RouteComponent.Retained (acquisitionSchema cfg) (route cfg raw instructions) a ready.1 r rr nr endpoint ∧
          RouteComponent.Retained (acquisitionSchema cfg) (route cfg raw instructions) a ready.1 s sr ns endpoint := h

theorem missing_route_input_rejected (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ (acquisition raw).dependencies) (hm : a k = none) :
    ¬ RetainedRouteReadout cfg raw instructions a :=
  RouteComponent.missing_acquisition_rejected _ _ _ k hk hm

theorem constant_register_no_retained_routes (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value) (c : Residue)
    (bad : ∀ x, raw.resource.residue.eval a x () = some c) :
    ¬ RetainedRouteReadout cfg raw instructions a :=
  RouteComponent.constant_register_rejected _ _ _ c bad

theorem empty_domain_no_retained_routes (cfg : Schema Factor Resource Stage Id History RouteId)
    (raw : Raw Cell Value R RV D A O P Factor Resource Residue Stage Id History RouteId)
    (instructions : RouteInstructions Cell Value R RV D A O Id History Residue Endpoint)
    (a : Assignment Cell Value) (bad : cfg.routes = []) :
    ¬ RetainedRouteReadout cfg raw instructions a :=
  RouteComponent.empty_comparison_rejected _ _ _ bad

end CSTTT.TargetTheory.GenericHandoff.RuntimeComponents

namespace CSTTT.TargetTheory.GenericHandoff.RouteComponent
open RegisterInterpreter
variable {Cell R D A O Stage Id History RouteId Residue Endpoint : Type}
    {Value : Cell → Type} {RV : R → Type} [DecidableEq Stage]

/-- An internal adapter lemma for a raw owner instruction. The two executions
are definitionally identical; the equation must hold on EVERY run, after the
required inputs have been checked. It cannot replace a missing input guard. -/
theorem retained_owner_congr
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (owner : Expr Cell Value R RV Unit CarrierId)
    (cfg : Config Stage Id History RouteId) (a : Assignment Cell Value)
    (h : AcquisitionExecution.Ready raw.acquisition a)
    (equation : ∀ x, owner.eval a x () = raw.owner.eval a x ())
    (r : RouteId) (residue : Residue) (probe : Nat) (endpoint : Endpoint) :
    Retained cfg {raw with owner := owner} a h r residue probe endpoint ↔
      Retained cfg raw a h r residue probe endpoint := by
  unfold Retained
  simp only [equation]
  rfl

theorem indexed_owner_congr
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (owner : Expr Cell Value R RV Unit CarrierId)
    (cfg : Config Stage Id History RouteId) (a : Assignment Cell Value)
    (h : AcquisitionExecution.Ready raw.acquisition a)
    (equation : ∀ x, owner.eval a x () = raw.owner.eval a x ()) :
    Indexed cfg {raw with owner := owner} a h ↔ Indexed cfg raw a h := by
  unfold Indexed
  simp only [retained_owner_congr raw owner cfg a h equation]
  rfl

theorem pass_owner_congr
    (raw : Raw Cell Value R RV D A O Stage Id History RouteId Residue Endpoint)
    (owner : Expr Cell Value R RV Unit CarrierId)
    (cfg : Config Stage Id History RouteId) (a : Assignment Cell Value)
    (readiness : Ready {raw with owner := owner} a ↔ Ready raw a)
    (equation : Ready raw a → ∀ x, owner.eval a x () = raw.owner.eval a x ()) :
    Pass cfg {raw with owner := owner} a ↔ Pass cfg raw a := by
  constructor
  · rintro ⟨h,hi⟩
    have hr := readiness.mp h
    exact ⟨hr,(indexed_owner_congr raw owner cfg a h.1 (equation hr)).mp hi⟩
  · rintro ⟨h,hi⟩
    exact ⟨readiness.mpr h,(indexed_owner_congr raw owner cfg a h.1 (equation h)).mpr hi⟩

end CSTTT.TargetTheory.GenericHandoff.RouteComponent
