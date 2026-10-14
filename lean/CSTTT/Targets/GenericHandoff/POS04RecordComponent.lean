import CSTTT.Targets.GenericHandoff.RecordComponent
import CSTTT.Targets.GenericHandoff.POS04FactorTransport

/-! POS-04 record extraction, from shared event/realization/writer cells.
The event clock is the declared stage ordinal (G6_lane_spec.md:104–145).
The fixed ordinal is a schema rule, not a stored record-arrow verdict. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RecordComponent
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter

def eventMap (e : CSTTT.POS04.Event) : AcquisitionExecution.Event CSTTT.POS04.Stage :=
  ⟨e.fromStage,e.toStage,e.sourceSupport,e.targetSupport,e.strictStep,e.atomic,1⟩

def cfg : RecordComponent.Schema EventId RouteId := ⟨eventIds,routeIds⟩

def view : StaticView Cell Value (RecordComponent.Data CSTTT.POS04.Stage EventId RouteId) :=
  ⟨.map (fun p : List CSTTT.POS04.Event × (List CSTTT.POS04.Stage × (Tag → RouteId → Bool)) =>
    { events := fun i => (p.1.find? fun e => decide (e.id = i)).map eventMap
      realized := p.2.1
      sourceWriter := p.2.2 .source
      targetWriter := p.2.2 .target
      clock := stages.idxOf })
    (.pair (.cell Cell.eventTable) (.pair (.cell Cell.realized) (.cell Cell.writers)))⟩

def data (a : CSTTT.POS04.Assigned.Assignment) : RecordComponent.Data CSTTT.POS04.Stage EventId RouteId :=
  { events := fun i => ((runInputs6 a .target).base.events.find? fun e => decide (e.id = i)).map eventMap
    realized := (runInputs6 a .target).base.realized
    sourceWriter := (runInputs6 a .source).base.writers .source
    targetWriter := (runInputs6 a .target).base.writers .target
    clock := stages.idxOf }

theorem dependencies : view.dependencies = [.eventTable,.realized,.writers] := rfl

theorem read_equation (a : CSTTT.POS04.Assigned.Assignment)
    (h : Complete view.dependencies a) : view.read a = some (data a) := by
  have h1 := POS04RegisterDynamics.cell_value (h .eventTable (by simp [dependencies]))
  have h2 := POS04RegisterDynamics.cell_value (h .realized (by simp [dependencies]))
  have h3 := POS04RegisterDynamics.cell_value (h .writers (by simp [dependencies]))
  simp only [StaticView.read,view,Expr.eval]
  rw [h1,h2,h3]
  rfl

theorem missing_rejected (a : CSTTT.POS04.Assigned.Assignment) (k : Cell)
    (hk : k ∈ view.dependencies) (hm : a k = none) : ¬ RecordComponent.Pass cfg view a :=
  RecordComponent.missing_rejected cfg view a k hk hm

private theorem lookup (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (i : EventId) :
    (data a).events i = (event6 (runInputs6 a t) i).map eventMap := by
  cases t <;> rfl

private theorem strict_equation (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (e : CSTTT.POS04.Event) :
    RecordComponent.strict (data a) (eventMap e) = strictEvent6 (runInputs6 a t) e := by
  cases t <;>
    simp [RecordComponent.strict,data,eventMap,strictEvent6,Bool.and_assoc,runInputs6,extraInputs,inputs,Assigned.decode,clauseScope,commonScope]

theorem edges_equation (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    RecordComponent.edges cfg (data a) (decide (t = .source)) = assignedRecordEdges a t := by
  unfold RecordComponent.edges assignedRecordEdges
  apply congrArg (fun f => eventIds.flatMap f)
  funext i
  apply congrArg (fun f => eventIds.filterMap f)
  funext j
  rw [lookup a t i,lookup a t j]
  cases hi : event6 (runInputs6 a t) i <;> cases hj : event6 (runInputs6 a t) j
  all_goals simp only [Option.map_none,Option.map_some]
  all_goals try rfl
  rename_i e f
  rw [strict_equation a t e,strict_equation a t f]
  cases t <;> rfl

theorem rank_equation (a : CSTTT.POS04.Assigned.Assignment) (i : EventId) :
    RecordComponent.rank (data a) i = assignedRecordRank a i := by
  unfold RecordComponent.rank assignedRecordRank
  rw [lookup a .target i]
  cases hi : event6 (runInputs6 a .target) i <;> rfl

/-- The whole computed record object equals the existing assignment-owned
bridge field, for every partial assignment. Defaults are not a Pass witness:
the read-equation above requires completeness before this object is usable. -/
theorem transport_equation (a : CSTTT.POS04.Assigned.Assignment) :
    RecordComponent.transport cfg (data a) = assignedRecordTransport a := by
  unfold RecordComponent.transport assignedRecordTransport
  rw [show RecordComponent.edges cfg (data a) true = assignedRecordEdges a .source from edges_equation a .source,
      show RecordComponent.edges cfg (data a) false = assignedRecordEdges a .target from edges_equation a .target]
  have hr : RecordComponent.rank (data a) = assignedRecordRank a := funext (rank_equation a)
  rw [hr]

theorem positive_check : RecordComponent.Check cfg (data canonical) := by
  unfold RecordComponent.Check
  decide +kernel

theorem positive : RecordComponent.Pass cfg view canonical :=
  ⟨_,read_equation canonical (canonical_complete _),positive_check⟩

theorem positive_arrow : ∃ i j, CSTTT.RecordTheory.SourceArrow
    (RecordComponent.transport cfg (data canonical)) i j :=
  RecordComponent.nonempty_arrow cfg (data canonical) positive_check

theorem no_writer_guard : ¬ RecordComponent.Check cfg
    {(data canonical) with targetWriter := fun _ => false} :=
  RecordComponent.writer_rejected cfg _ .a (by decide) (Or.inr rfl)

theorem zero_clock_guard : ¬ RecordComponent.Check cfg
    {(data canonical) with clock := fun _ => 0} :=
  RecordComponent.zero_clock_rejected cfg _ .mix1 (by decide) (eventMap (events[0]!)) rfl rfl

/-- Decoder equivalence in BOTH directions, not just canonical truth. -/
theorem pass_iff (a : CSTTT.POS04.Assigned.Assignment) :
    RecordComponent.Pass cfg view a ↔ Complete view.dependencies a ∧ RecordComponent.Check cfg (data a) := by
  constructor
  · rintro ⟨d,hd,hc⟩
    have hp : Complete view.dependencies a := by
      intro k hk
      cases hm : a k with
      | some v => rfl
      | none =>
        rw [view.missing a k hk hm] at hd
        contradiction
    rw [read_equation a hp] at hd
    cases Option.some.inj hd
    exact ⟨hp,hc⟩
  · rintro ⟨hp,hc⟩
    exact ⟨_,read_equation a hp,hc⟩

theorem arrow_equivalences (m : RawLaneModel) (i j : EventId) :
    (CSTTT.RecordTheory.SourceArrow (RecordComponent.transport cfg (data (image m.assignment))) i j ↔
      CSTTT.RecordTheory.SourceArrow (assignmentRawBridge m).record i j) ∧
    (CSTTT.RecordTheory.TargetArrow (RecordComponent.transport cfg (data (image m.assignment))) i j ↔
      CSTTT.RecordTheory.TargetArrow (assignmentRawBridge m).record i j) := by
  rw [transport_equation]
  exact ⟨Iff.rfl,Iff.rfl⟩

/-- Raw support deletion and event-table erasure, leaving every other
primitive unchanged. These controls are computed, not boolean verdicts. -/
theorem source_support_erasure_guard : ¬ RecordComponent.Check cfg
    {(data canonical) with events := fun i => ((data canonical).events i).map (fun e => {e with sourceSupport := false})} := by
  unfold RecordComponent.Check
  decide +kernel

theorem target_support_erasure_guard : ¬ RecordComponent.Check cfg
    {(data canonical) with events := fun i => ((data canonical).events i).map (fun e => {e with targetSupport := false})} := by
  unfold RecordComponent.Check
  decide +kernel

theorem event_erasure_guard : ¬ RecordComponent.Check cfg
    {(data canonical) with events := fun _ => none} := by
  unfold RecordComponent.Check
  decide +kernel

theorem realization_erasure_guard : ¬ RecordComponent.Check cfg
    {(data canonical) with realized := []} := by
  apply RecordComponent.unrealized_rejected cfg _ .mix1 (by decide) (eventMap (eventOf .mix1)) rfl
  simp

end CSTTT.TargetTheory.GenericHandoff.POS04RecordComponent
