import CSTTT.Targets.GenericHandoff.TemporalFactorCells
import CSTTT.Targets.GenericHandoff.POS04ProfileRules
import CSTTT.POS04.Assigned.C6Adapters

/-! POS-04 finite C6 data adapter. The concrete acceptance and actual-runtime
word/lift equivalences remain completion gates. All tables here are reused
assigned primitives or typed projections of them, never cached verdicts. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04TemporalFactor
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

def eventMap (e : CSTTT.POS04.Event) : TemporalFactorRules.Event CSTTT.POS04.Stage EventId :=
  ⟨e.id,e.fromStage,e.toStage,e.atomic,e.strictStep⟩
def routeMap (r : CSTTT.POS04.Route) : TemporalFactorRules.Route RouteId HistoryId EventId :=
  ⟨r.id,r.sourceHistory,r.eventPath⟩
def observableMap : FutureObservable → TemporalFactorRules.Observable
  | .predictiveNow => .predictive
  | .eventOrder => .order
  | .tickPhase => .tick
  | .cumulativeProgress => .progress
  | .endogenousRecordCount => .record
  | .routeResidue => .route
  | .maintenanceState => .maintenance
  | .owner => .owner

def schema (t : Tag) : TemporalFactorRules.Schema KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag :=
  ⟨POS04ProfileRules.clauseSchema,t,historyIds,routeIds,stages,eventIds,1,1,
    ⟨ledger.initialBudget,ledger.actionCost,ledger.rechargePerAction⟩,(.inK .p0w0,.inK .p0w1)⟩

def raw (d : RunInputs6) (t : Tag) : TemporalFactorRules.Raw KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag :=
  ⟨d.base.base.rows,d.base.base.positions,d.base.base.hazards,d.base.base.policy,d.base.base.publishedM,
    (fun s u => d.base.base.publishedP (index s) (index u)),d.ticks,
    ⟨d.resource.owner,d.resource.rechargeAvailable⟩,
    ⟨d.ledger.initialBudget,d.ledger.actionCost,d.ledger.rechargePerAction⟩,
    d.interface.map observableMap,d.base.histories,d.base.events.map eventMap,d.base.realized,
    d.base.receiver.funded,d.base.routes.map routeMap,d.base.writers t⟩

def bindings (t : Tag) : TemporalFactorCells.Bindings Cell Value KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag :=
  ⟨⟨.rows t,id⟩,⟨.positions,id⟩,⟨.hazards,id⟩,⟨.policy,id⟩,⟨.publishedM,id⟩,
    ⟨.publishedP,fun p s u => p (index s) (index u)⟩,⟨.ticks t,id⟩,
    ⟨.resources t,fun r => ⟨r.owner,r.rechargeAvailable⟩⟩,
    ⟨.maintenance,fun l => ⟨l.initialBudget,l.actionCost,l.rechargePerAction⟩⟩,
    ⟨.interface,fun i => i.map observableMap⟩,⟨.histories,id⟩,
    ⟨.eventTable,fun es => es.map eventMap⟩,⟨.realized,id⟩,⟨.receiverInput,fun r => r.funded⟩,
    ⟨.routeTable,fun rs => rs.map routeMap⟩,⟨.writers,fun w => w t⟩⟩

theorem scope_membership (t : Tag) (k : Cell) :
    k ∈ (bindings t).scope ↔ k ∈ clauseScope t .c6 := by
  simp only [bindings,TemporalFactorCells.Bindings.scope,clauseScope,commonScope,List.mem_cons,List.mem_append,List.not_mem_nil,or_false]
  grind

theorem missing_rejected (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (k : Cell)
    (hk : k ∈ clauseScope t .c6) :
    ¬ TemporalFactorCells.Accept (schema t) (bindings t) (CSTTT.POS04.Assigned.put a k none) :=
  TemporalFactorCells.missing_rejected _ _ _ k ((scope_membership t k).mpr hk) (by simp)

theorem decoded_canonical (t : Tag) :
    TemporalFactorCells.decoded (bindings t) canonical = some (raw (runInputs6 canonical t) t) := by
  cases t <;> rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem canonical_accept (t : Tag) : TemporalFactorRules.Accept (schema t) (raw (runInputs6 canonical t) t) := by
  refine ⟨POS04ProfileRules.domain_checked,?_,?_,?_,?_,?_,?_,?_,?_⟩
  all_goals cases t
  all_goals try simp only [TemporalFactorRules.Reference,TemporalFactorRules.Trace,TemporalFactorRules.Funding,
      TemporalFactorRules.FiniteBisim,TemporalFactorRules.Coarser,ProfileRules.RowsValid,ProfileRules.Linked,
      ProfileRules.SamePartition,funext_iff]
  all_goals first
    | decide +kernel
    | (constructor
       · constructor
         · intro s; cases s <;> rfl
         · intro s u; cases s <;> cases u <;> decide +kernel
       · intro s u; cases s <;> cases u <;> decide +kernel)

theorem canonical_assigned (t : Tag) : TemporalFactorCells.Accept (schema t) (bindings t) canonical :=
  ⟨_,decoded_canonical t,canonical_accept t⟩

end CSTTT.TargetTheory.GenericHandoff.POS04TemporalFactor
