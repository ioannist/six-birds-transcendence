import CSTTT.Targets.GenericHandoff.POS04HistoricalAcquisition

/-! TTH-06: duplicate-ID regression requested by Eddy.
One raw event-table edit disables source support on the original records and
appends the original mix1 record. This is a diagnostic, not a new positive model.
Frozen event6 still resolves first records for the strict path. Frozen active7
scans all non-exit records and activates using the appended mixed record.
No unique-ID assumption or receiver/funding change is introduced. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalDuplicateEvents
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter POS04RegisterDynamics
open POS04HistoricalAcquisition
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def changedEvents : List CSTTT.POS04.Event :=
  events.map (fun e => {e with sourceSupport := false}) ++ [eventOf .mix1]
def assignment : CSTTT.POS04.Assigned.Assignment :=
  Assigned.put canonical .eventTable (some changedEvents)
def diagnostic : RawLaneModel :=
  {baseline with assignment := assignment}

theorem staged_assignment : image diagnostic.assignment = assignment := by
  change image (mapCell canonical .eventTable
    (fun es => es.map (fun e => {e with sourceSupport := false}) ++ [eventOf .mix1])) = assignment
  rw [image_map_events,image_canonical]
  rfl

theorem ready : HistoricalAcquisition.Ready raw assignment := by
  apply POS04HistoricalAcquisition.ready
  intro k _
  cases k
  all_goals try (rename_i t; cases t)
  all_goals rfl

def pathEvents (id : EventId) : Option (AcquisitionExecution.Event CSTTT.POS04.Stage) :=
  some (eventProjection {eventOf id with sourceSupport := false})

theorem first_event_is_not_mixed :
    (raw.events.read assignment).map (fun f => (f .mix1).map AcquisitionExecution.Event.sourceSupport) =
      some (some false) := rfl

theorem activation_is_mixed :
    HistoricalAcquisition.Activated (POS04ExecutionFrontier.receiverView.project receiver)
      (activationRecords changedEvents) realizedStages := by
  refine ⟨rfl,rfl,rfl,fun _ => ⟨eventProjection (eventOf .mix1),?_,by decide,by decide,rfl,rfl,rfl⟩⟩
  apply List.mem_map.mpr
  refine ⟨eventOf .mix1,List.mem_filter.mpr ⟨?_,rfl⟩,rfl⟩
  exact List.mem_append_right _ (by simp)

theorem duplicate_path (rid : RouteId) :
    HistoricalAcquisition.PathCheck POS04ExecutionFrontier.schema pathEvents realizedStages (routeOf rid).eventPath := by
  let e := fun id => eventProjection {eventOf id with sourceSupport := false}
  refine ⟨.mix1,[.mix2,.exit],by cases rid <;> rfl,⟨e .mix1,rfl,rfl⟩,?_,?_,.exit,e .exit,
    by cases rid <;> rfl,rfl,rfl,rfl,rfl⟩
  · intro id _
    refine ⟨?_,e id,rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
    all_goals cases id <;> decide +kernel
  · intro pair hp
    rcases pair with ⟨i,j⟩
    refine ⟨e i,e j,rfl,rfl,?_⟩
    cases rid <;> cases i <;> cases j <;>
      simp_all [routeOf,routes,e,eventProjection,eventOf,events,stages]

theorem duplicate_arrival (rid : RouteId) :
    HistoricalAcquisition.Arrival POS04ExecutionFrontier.schema raw assignment ready rid
      (encode (POS04RouteExecution.arrivalFor rid)) := by
  obtain ⟨hist,sr,sp,coord,tr,tp,rs,es,ss,recv,first,rest,
    hh,hs,hsp,hcoord,ht,htp,hr,he,hreal,hrecv,hrid,hhid,hlist,hss,hts,hpath,hact,hreset⟩ :=
      canonical_arrival rid
  refine ⟨hist,sr,sp,coord,tr,tp,rs,pathEvents,ss,recv,first,rest,
    hh,hs,hsp,hcoord,ht,htp,hr,?_,hreal,hrecv,hrid,hhid,hlist,hss,hts,?_,?_,?_⟩
  · change some _ = some pathEvents
    apply congrArg some
    funext id; cases id <;> rfl
  · have er : rs = POS04ExecutionFrontier.routeView.project routes := Option.some.inj hr.symm
    have ess : ss = realizedStages := Option.some.inj hreal.symm
    rw [er,ess]
    cases rid
    · exact duplicate_path .a
    · exact duplicate_path .b
  · have er : recv = POS04ExecutionFrontier.receiverView.project receiver := Option.some.inj hrecv.symm
    have ess : ss = realizedStages := Option.some.inj hreal.symm
    rw [er,ess]
    exact ⟨activationRecords changedEvents,rfl,activation_is_mixed⟩
  · have eqreset (input : HistoricalAcquisition.ReceiverInput KState RouteId EventId RouteId) :
        HistoricalAcquisition.reset raw assignment ready input =
          HistoricalAcquisition.reset raw canonical canonical_ready input := by
      rw [reset_computed assignment ready input receiver rfl,
        reset_computed canonical canonical_ready input receiver rfl]
    rw [eqreset]
    exact hreset

theorem duplicate_entry (rid : RouteId) :
    HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw assignment ready
      (encode (POS04RouteExecution.resultFor rid)) := by
  apply actual_supported_branch_entry assignment ready rid _ (duplicate_arrival rid)
    (fun r => ⟨r,[.mix1,.mix2,.exit]⟩) (by
      change some (POS04ExecutionFrontier.routeView.project routes) = _
      apply congrArg some; funext r; cases r <;> rfl) (.nominal,.cw)
    (by cases rid <;> rfl)
  · simp only [StrategyGame.Normalized,StrategyGame.PositiveSupport,actual_row assignment ready]
    refine ⟨?_,?_,Ambient.inK .p2w1,1,?_,by decide⟩
    all_goals cases rid <;> decide +kernel
  · refine ⟨1,?_,by decide⟩
    cases rid <;> decide +kernel


/-- Raw strict-step=true cannot license a skipped POS-04 stage. This checks
the newly bound clock rule, not a sibling clause/corridor rejection. -/
theorem skipped_stage_projection_rejected :
    (eventProjection {eventOf .mix1 with toStage := .targetExit}).strictStep = false := rfl

theorem skipped_stage_path_rejected (realized : List CSTTT.POS04.Stage) :
    ¬ HistoricalAcquisition.PathCheck POS04ExecutionFrontier.schema
      (fun id => if id = .mix1 then
        some (eventProjection {eventOf .mix1 with toStage := .targetExit}) else pathEvents id)
      realized [.mix1] := by
  exact HistoricalAcquisition.nonstrict_event_rejected POS04ExecutionFrontier.schema
    (fun id : EventId => if id = .mix1 then
      some (eventProjection {eventOf .mix1 with toStage := .targetExit}) else pathEvents id)
    realized [EventId.mix1] EventId.mix1
    (by simp) (eventProjection {eventOf .mix1 with toStage := .targetExit})
    (by simp) skipped_stage_projection_rejected

theorem legacy_ao_accepts : AO diagnostic := by
  change operationalAutonomyCheck diagnostic = true
  decide +kernel

theorem historical_operational_accepts : POS04HistoricalAutonomy.OperationalAutonomy diagnostic :=
  (POS04HistoricalAutonomy.operational_game_iff_ao diagnostic).mpr legacy_ao_accepts

/-- Both the frozen operational game and the new polymorphic acquisition
accept the diagnostic. Whole polymorphic game equivalence remains a later gate. -/
theorem duplicate_regression : AO diagnostic ∧
    POS04HistoricalAutonomy.OperationalAutonomy diagnostic ∧
    ∃ h : HistoricalAcquisition.Ready raw (image diagnostic.assignment),
      ∃ r, HistoricalAcquisition.Entry POS04ExecutionFrontier.schema raw
        (image diagnostic.assignment) h r := by
  refine ⟨legacy_ao_accepts,historical_operational_accepts,?_⟩
  rw [staged_assignment]
  exact ⟨ready,_,duplicate_entry .a⟩

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalDuplicateEvents
