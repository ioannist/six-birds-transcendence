import CSTTT.Targets.GenericHandoff.RuntimeRoute
import CSTTT.Targets.GenericHandoff.POS04RouteReadout
import CSTTT.Targets.GenericHandoff.POS04ResourceRuntime

/-! Exact arbitrary-partial POS-04 instance of shared-runtime route memory.
The owner is reconstructed from the actual required recharge account, not a
separate carrier label. All consumed ledger/resource/event/history cells must
be present. This adapter retains Indexed AND Retained, including raw path
identity, shared endpoint and every actual post-reception support branch.
The first-phase probe is still the declared designed readout, not independent
evidence. No change to the frozen model or to the family semantics. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RuntimeRoute
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RegisterDynamics POS04RouteExecution POS04ResourceRuntime
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def instructions : RuntimeComponents.RouteInstructions Cell Value Unit FrameValue
    LaneDisturbance Action Ambient EventId RouteId (List KState × List EventId) (Tag × Ambient) :=
  ⟨routeRaw.provenance,routeRaw.readout,routeRaw.endpoint⟩

def raw (p : Protocol) := RuntimeComponents.route cfg (runtime p) instructions

theorem raw_eq (p : Protocol) : raw p =
    {routeRaw with owner := (RuntimeComponents.temporal cfg (runtime p)).readouts.owner} := rfl

theorem ready_iff (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    RouteComponent.Ready (raw p) a ↔ Complete dependencies a := by
  constructor
  · intro h
    apply (ready_route_iff a).mp
    refine ⟨h.1,?_⟩
    intro k hk
    simp [RouteComponent.scope,routeRaw,provenance,StaticView.dependencies,Expr.dependencies] at hk
    rcases hk with hk | hk | hk
    all_goals subst k
    all_goals apply h.2
    all_goals simp [raw,RuntimeComponents.route,RuntimeComponents.temporal,
      runtime,bindings,accounts,RouteComponent.scope,instructions,routeRaw,provenance,
      StaticView.dependencies,Expr.dependencies]
  · intro hc
    refine ⟨ready a hc,?_⟩
    intro k hk
    apply hc k
    simp [raw,RuntimeComponents.route,RuntimeComponents.temporal,
      runtime,bindings,accounts,RouteComponent.scope,instructions,routeRaw,provenance,
      StaticView.dependencies,Expr.dependencies] at hk
    simp only [dependencies,List.mem_cons,List.not_mem_nil,or_false]
    grind

/-- Exact owner equation on ALL run contexts, not just the two sample results.
Presence, rather than a decoder default, supplies the ledger and owner. -/
theorem owner_equation (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete dependencies a) (x : Registers Unit FrameValue) :
    (raw p).owner.eval a x () = routeRaw.owner.eval a x () := by
  have hr := cell_value (hc (.resources .target) (by simp [dependencies]))
  have hl := cell_value (hc .maintenance (by simp [dependencies]))
  simp only [raw,RuntimeComponents.route,RuntimeComponents.temporal,runtime,bindings,
    accounts,Expr.eval,routeRaw]
  rw [hr,hl]
  rfl

theorem pass_iff (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    RuntimeComponents.RetainedRouteReadout cfg (runtime p) instructions a ↔ RoutePass a := by
  change RouteComponent.Pass _ (raw p) a ↔ RoutePass a
  rw [raw_eq]
  apply RouteComponent.pass_owner_congr
  · exact (ready_iff p a).trans (ready_route_iff a).symm
  · intro h x
    exact owner_equation p a ((ready_route_iff a).mp h) x

/-- Exact semantic readout adapter for EVERY partial assignment. -/
theorem semantic_iff (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    RuntimeComponents.RetainedRouteReadout cfg (runtime p) instructions a ↔
      Complete dependencies a ∧ POS04RouteReadout.RouteReadout a :=
  (pass_iff p a).trans (POS04RouteReadout.route_readout_partial_iff a)

theorem status_iff (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    RuntimeComponents.retainedRouteStatus cfg (runtime p) instructions a = .routeIndexed ↔
      Complete dependencies a ∧ POS04RouteReadout.RouteReadout a :=
  (RuntimeComponents.retained_route_status_iff _ _ _ _).trans (semantic_iff p a)

theorem positive (p : Protocol) :
    RuntimeComponents.RetainedRouteReadout cfg (runtime p) instructions canonical :=
  (pass_iff p canonical).mpr POS04RouteExecution.positive

/-- A swapped raw history domain remains a valid comparison: [1,0] is not
rejected in favor of baseline [0,1]. The gate requires definedness/distinction. -/
theorem reversed (p : Protocol) :
    RuntimeComponents.RetainedRouteReadout cfg (runtime p) instructions POS04RouteReadout.reversed :=
  (pass_iff p _).mpr POS04RouteReadout.reversed_pass

theorem wrong_account_owner (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment)
    (resource : ResourceData) (hi : a (.resources .target) = some resource)
    (bad : resource.owner = .source) :
    ¬ RuntimeComponents.RetainedRouteReadout cfg (runtime p) instructions a :=
  fun h => POS04RouteExecution.wrong_owner_rejected a resource hi bad ((pass_iff p a).mp h)

theorem missing_atomic (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ RuntimeComponents.RetainedRouteReadout cfg (runtime p) instructions
      (Assigned.put a .eventTable none) :=
  fun h => POS04RouteExecution.missing_atomic_rejected a ((pass_iff p _).mp h)

theorem missing_source_rows (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ RuntimeComponents.RetainedRouteReadout cfg (runtime p) instructions
      (Assigned.put a (.rows .source) none) :=
  fun h => POS04RouteExecution.missing_source_rows_rejected a ((pass_iff p _).mp h)

theorem missing_target_rows (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ RuntimeComponents.RetainedRouteReadout cfg (runtime p) instructions
      (Assigned.put a (.rows .target) none) :=
  fun h => POS04RouteExecution.missing_target_rows_rejected a ((pass_iff p _).mp h)

/-- The account-derived owner consumes the ledger even though the pure old
owner display did not; acquisition already requires it, so no new gate is added. -/
theorem missing_ledger (p : Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ RuntimeComponents.RetainedRouteReadout cfg (runtime p) instructions
      (Assigned.put a .maintenance none) := by
  intro h
  have hc := (semantic_iff p _).mp h |>.1
  have hm := hc .maintenance (by simp [dependencies])
  simp [Assigned.put] at hm

end CSTTT.TargetTheory.GenericHandoff.POS04RuntimeRoute
