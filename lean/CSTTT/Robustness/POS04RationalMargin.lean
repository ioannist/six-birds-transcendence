import CSTTT.Robustness.PartialEventReadout
import CSTTT.Targets.GenericHandoff.POS04FinalCorrespondence

/-! Class (b): the declared operational rational-register successor and frozen-control kernel returns. Original Nat observers and gate inputs remain under erasure. -/
namespace CSTTT.RobustnessTheory.POS04RationalMargin
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.GenericHandoff CSTTT.TargetTheory.ComputedFIACH
open CSTTT.RobustnessTheory ExactFiveMargins RegisterInterpreter RegisterInitialization
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000
-- Class (b): the previously declared released base model.
def model := POS04FinalHandoff.raw (POS04ResourceRuntime.protocol baseline)
-- Class (b): all rational corrections, from an actual optional primitive.
def input (delta : Vector) : RawRationalMargin.Input Cell Value := ⟨canonical,some delta⟩
-- Class (b): actual complete readiness, independently of the numeric readout.
theorem ready (delta : Vector) : RawRationalMargin.EventReady model (input delta) := by
  refine ⟨?_,by simp [input]⟩
  change ExecutionFrontier.Ready POS04ExecutionFrontier.raw
    (OwningHandoff.target (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline)) canonical)
  rw [POS04RawHandoff.target_eq,image_canonical]
  exact POS04ExecutionFrontier.canonical_ready
-- Class (b): the raw initial observation, derived in the following theorem.
def before : Vector | .predictive => 1 | _ => 0
-- Class (b): the raw final observation, derived in the following theorem.
def after : Vector | .predictive => 3 | _ => 1
-- Class (b): exact full raw five-coordinate read, not a numeric premise.
theorem original_reads (delta : Vector) :
    RawRationalMargin.OriginalReads model (input delta) (ready delta)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1) before after := by
  unfold RawRationalMargin.OriginalReads
  have hi : ExecutionFrontier.initial model.base.frames.sourceFrame
      (OwningHandoff.target model.base (input delta).source) (ready delta).1 RouteId.a =
      POS04RegisterDynamics.encode (acquisitionInitialRun canonical .source .a) := by
    change ExecutionFrontier.initial POS04ExecutionFrontier.raw _ _ .a = _
    change ExecutionFrontier.initial POS04ExecutionFrontier.raw
      (OwningHandoff.target (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline)) canonical) _ .a = _
    have hh : ∀ (a : CSTTT.POS04.Assigned.Assignment), a=canonical →
        ∀ hr : ExecutionFrontier.Ready POS04ExecutionFrontier.raw a,
        ExecutionFrontier.initial POS04ExecutionFrontier.raw a hr .a =
        POS04RegisterDynamics.encode (acquisitionInitialRun canonical .source .a) := by
      intro a ha hr
      subst a
      exact POS04ExecutionFrontier.initial_eq canonical (canonical_complete _) .a
    exact hh _ (by rw [POS04RawHandoff.target_eq,image_canonical]) _
  constructor
  · intro i
    rw [hi]
    change (RawRationalMargin.originalObserver model i).eval
      (OwningHandoff.target (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline)) canonical) _ () = _
    rw [POS04RawHandoff.target_eq,image_canonical]
    cases i <;> rfl
  · intro i
    rw [hi]
    have hu : AcquisitionExecution.update model.base.frames.sourceFrame.acquisition
        (OwningHandoff.target model.base (input delta).source) (ready delta).1.1
        (POS04RegisterDynamics.encode (acquisitionInitialRun canonical .source .a))
        LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=
        POS04RegisterDynamics.encode (actualUpdate6 (runInputs6 canonical .source)
          (acquisitionInitialRun canonical .source .a) Action.cw (Ambient.inK KState.p2w1)) := by
      change AcquisitionExecution.update POS04ExecutionFrontier.acquisition _ _ _ _ _ _ = _
      change AcquisitionExecution.update POS04ExecutionFrontier.acquisition
        (OwningHandoff.target (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline)) canonical) _ _ _ _ _ = _
      have hh : ∀ (a : CSTTT.POS04.Assigned.Assignment), a=canonical →
          ∀ hr : AcquisitionExecution.Ready POS04ExecutionFrontier.acquisition a,
          AcquisitionExecution.update POS04ExecutionFrontier.acquisition a hr
            (POS04RegisterDynamics.encode (acquisitionInitialRun canonical .source .a))
            LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1) =
            POS04RegisterDynamics.encode (actualUpdate6 (runInputs6 canonical .source)
              (acquisitionInitialRun canonical .source .a) Action.cw (Ambient.inK KState.p2w1)) := by
        intro a ha hr
        subst a
        exact POS04ExecutionFrontier.actual_update canonical (canonical_complete _) _ _ _ _
      exact hh _ (by rw [POS04RawHandoff.target_eq,image_canonical]) _
    rw [hu]
    change (RawRationalMargin.originalObserver model i).eval
      (OwningHandoff.target (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline)) canonical) _ () = _
    rw [POS04RawHandoff.target_eq,image_canonical]
    cases i <;> rfl

-- Class (b): signed baseline differences, derived from original_reads.
def advances : Vector | .predictive => 2 | _ => 1
-- Class (b): the previously frozen half-radius closed box.
def radius : Vector := fun _ => (1 : Rat)/2
-- Class (b): exact certified positive slack for all five coordinates.
theorem certified_margin : PositiveCertifiedMargin advances radius := by
  intro i
  cases i <;> decide +kernel
-- Class (b): actual event equality for every rational correction, no box restriction.
theorem actual_advance (delta : Vector) :
    RawRationalMargin.eventAdvance model (input delta) (ready delta)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=
      some (fun i => advances i+delta i) := by
  have h := RawRationalMargin.actual_event_advance model (input delta) (ready delta)
    RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)
    before after delta rfl (original_reads delta).1 (original_reads delta).2
  have he : (fun i => (after i-before i)+delta i)=(fun i => advances i+delta i) := by
    funext i
    have hb : after i-before i=advances i := by cases i <;> decide +kernel
    rw [hb]
  exact h.trans (congrArg some he)
-- Class (b): all corrections inherit the complete original F/O gates.
theorem inherited_gates (delta : Vector) :
    RawRationalMargin.hardGate_F model (input delta) ∧
    RawRationalMargin.hardGate_O model (input delta) :=
  ⟨POS04FinalHandoff.positive_F,POS04FinalHandoff.positive_O⟩
-- Class (b): actual five-coordinate operational robustness on the whole closed box.
theorem all_corrections (delta : Vector) (box : WithinBox radius delta) :
    RawRationalMargin.eventAdvance model (input delta) (ready delta)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=
      some (fun i => advances i+delta i) ∧
    (∀ i, 0<advances i+delta i) ∧
    RawRationalMargin.hardGate_F model (input delta) ∧
    RawRationalMargin.hardGate_O model (input delta) :=
  ⟨actual_advance delta,all_five_positive advances radius delta certified_margin box,
    inherited_gates delta⟩

-- Class (b): actual optional source controls, same frozen declared quarter primitive.
def partialInput (source : CSTTT.POS04.Assigned.Assignment) (delta : Option Vector) :
    RawRationalMargin.Input Cell Value := ⟨source,delta⟩
-- Class (b): the frozen all-quarter correction.
def quarter : Vector := fun _ => (1 : Rat)/4
-- Class (b): actual substituted post-event raw expression, defined for missing inputs.
def partialAfter (source : CSTTT.POS04.Assigned.Assignment) (delta : Option Vector)
    (i : ExactFiveMargins.Coordinate) : Option Rat :=
  (PartialEventReadout.afterExpr (RawRationalMargin.initializer model)
    (RawRationalMargin.program model) (RawRationalMargin.observer model i)).eval
    (RawRationalMargin.target model (partialInput source delta)) noRegisters
    (RouteId.a,LaneDisturbance.nominal,Action.cw,Ambient.inK KState.p2w1)
-- Class (b): absence refutes the actual post-event raw predictive read.
theorem missing_positions_after :
    partialAfter (Assigned.put canonical .positions none) (some quarter) .predictive=none := rfl
-- Class (b): frozen row-absence control does NOT erase the actual projected numeric read.
theorem missing_rows_after :
    partialAfter (Assigned.put canonical (.rows Tag.source) none) (some quarter) .predictive=some ((3 : Rat)+(1 : Rat)/4) := by decide +kernel
-- Class (b): kernel refutation of the original frozen control expectation.
theorem missing_rows_expectation_false :
    ¬ partialAfter (Assigned.put canonical (.rows Tag.source) none) (some quarter) .predictive=none := by
  rw [missing_rows_after]
  intro h
  cases h
-- Class (b): absence refutes the actual post-event raw record read.
theorem missing_writers_after :
    partialAfter (Assigned.put canonical .writers none) (some quarter) .record=none := rfl
-- Class (b): absence refutes the actual post-event raw record read.
theorem missing_maintenance_after :
    partialAfter (Assigned.put canonical .maintenance none) (some quarter) .record=none := rfl
-- Class (b): absent correction refutes every actual extended post-event read.
theorem missing_correction_after (i : ExactFiveMargins.Coordinate) :
    partialAfter canonical none i=none := by cases i <;> rfl

-- Class (b): the original source row is still consumed by the complete source package.
theorem missing_source_rows_gates (delta : Option Vector) :
    ¬ RawRationalMargin.hardGate_F model
      (partialInput (Assigned.put canonical (.rows Tag.source) none) delta) ∧
    ¬ RawRationalMargin.hardGate_O model
      (partialInput (Assigned.put canonical (.rows Tag.source) none) delta) := by
  have h := OwningHandoff.missing_source_primitive_no_pass model.base
    (Assigned.put canonical (.rows Tag.source) none) .c1 (.rows Tag.source)
    (by simp [model,POS04FinalHandoff.raw,POS04RawHandoff.raw,POS04Dispatcher.package,
      ClauseDispatcher.Rule.scope,POS04ObjecthoodCells.bindings,ObjecthoodCells.Bindings.scope])
    (by simp)
  exact ⟨fun gate => h.1 gate.1.2.2,fun gate => h.2 gate.1.2.2⟩

-- Class (b): exact original initializer under the operational register projection.
theorem initial_erased (delta : Vector) :
    RationalRegisters.erase (RawRationalMargin.initialRun model (input delta) (ready delta) RouteId.a)=
      POS04RegisterDynamics.encode (acquisitionInitialRun canonical .source .a) := by
  rw [RawRationalMargin.initial_run_erasure]
  have hh : ∀ (a : CSTTT.POS04.Assigned.Assignment), a=canonical →
      ∀ hr : ExecutionFrontier.Ready POS04ExecutionFrontier.raw a,
      ExecutionFrontier.initial POS04ExecutionFrontier.raw a hr .a =
      POS04RegisterDynamics.encode (acquisitionInitialRun canonical .source .a) := by
    intro a ha hr
    subst a
    exact POS04ExecutionFrontier.initial_eq canonical (canonical_complete _) .a
  exact hh (OwningHandoff.target model.base (input delta).source) (by
    change OwningHandoff.target
      (POS04RawHandoff.raw (POS04ResourceRuntime.protocol baseline)) canonical=canonical
    rw [POS04RawHandoff.target_eq,image_canonical]) (ready delta).1
-- Class (b): the actual initialized optional row for every rational correction.
theorem actual_initial_row (delta : Vector) :
    (RawRationalMargin.row model).eval (RawRationalMargin.target model (input delta))
      (RawRationalMargin.initialRun model (input delta) (ready delta) RouteId.a)
      (LaneDisturbance.nominal,Action.cw)=some [(Ambient.inK KState.p2w1,(1 : Rat))] := by
  rw [RawRationalMargin.row_erasure,initial_erased]
  change (POS04ExecutionFrontier.acquisition.execution.row).eval
    (OwningHandoff.target (POS04RawHandoff.raw _) canonical) _ _ = _
  rw [POS04RawHandoff.target_eq,image_canonical]
  decide +kernel
-- Class (b): non-vacuous actual positive support from the same initialized event.
theorem actual_supported (delta : Vector) :
    RawRationalMargin.Supported model (input delta)
      (RawRationalMargin.initialRun model (input delta) (ready delta) RouteId.a)
      LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1) := by
  refine ⟨_,actual_initial_row delta,(1 : Rat),by simp,?_⟩
  decide +kernel
-- Class (b): actual aggregated positive probability, no supplied support verdict.
theorem actual_weight (delta : Vector) :
    RawRationalMargin.outcomeWeight model (input delta)
      (RawRationalMargin.initialRun model (input delta) (ready delta) RouteId.a)
      LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=some (1 : Rat) := by
  unfold RawRationalMargin.outcomeWeight
  rw [actual_initial_row]
  decide +kernel

-- Class (b): the frozen outside-half-box order correction.
def outside : Vector | .order => -1 | _ => 0
-- Class (b): the frozen radius-one lower-corner correction.
def zeroSlack : Vector := fun _ => -1
-- Class (b): refutes actual all-five positivity of the outside-box event.
theorem outside_actual_not_positive (v : Vector)
    (read : RawRationalMargin.eventAdvance model (input outside) (ready outside)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=some v) :
    ¬ ∀ i, 0<v i := by
  have hv := Option.some.inj ((actual_advance outside).symm.trans read)
  have ho := congrArg (fun f : Vector => f .order) hv
  change advances .order+outside .order=v .order at ho
  have hz : advances .order+outside .order=0 := by decide +kernel
  rw [hz] at ho
  intro hp
  have h := hp .order
  rw [← ho] at h
  exact (by decide : ¬ (0 : Rat)<0) h
-- Class (b): refutes actual all-five positivity at the zero-slack lower corner.
theorem zero_slack_actual_not_positive (v : Vector)
    (read : RawRationalMargin.eventAdvance model (input zeroSlack) (ready zeroSlack)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=some v) :
    ¬ ∀ i, 0<v i := by
  have hv := Option.some.inj ((actual_advance zeroSlack).symm.trans read)
  have ho := congrArg (fun f : Vector => f .record) hv
  change advances .record+zeroSlack .record=v .record at ho
  have hz : advances .record+zeroSlack .record=0 := by decide +kernel
  rw [hz] at ho
  intro hp
  have h := hp .record
  rw [← ho] at h
  exact (by decide : ¬ (0 : Rat)<0) h
-- Class (b): the source/staging dependency expectation fails without tuning the control.
theorem missing_source_rows_readout_some :
    RawRationalMargin.partialEventAdvance model
      (partialInput (Assigned.put canonical (.rows Tag.source) none) (some quarter))
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1) =
      some (fun i => advances i+quarter i) := by
  unfold RawRationalMargin.partialEventAdvance PartialEventReadout.partialAdvance
  have hb : RawRationalMargin.readVector (fun i =>
      (PartialEventReadout.beforeExpr (RawRationalMargin.initializer model)
        (RawRationalMargin.observer model i)).eval
        (RawRationalMargin.target model (partialInput
          (Assigned.put canonical (.rows Tag.source) none) (some quarter))) noRegisters
        (RouteId.a,LaneDisturbance.nominal,Action.cw,Ambient.inK KState.p2w1))=some before := by
    apply RawRationalMargin.read_vector_some
    intro i
    cases i <;> decide +kernel
  have ha : RawRationalMargin.readVector (fun i =>
      (PartialEventReadout.afterExpr (RawRationalMargin.initializer model)
        (RawRationalMargin.program model) (RawRationalMargin.observer model i)).eval
        (RawRationalMargin.target model (partialInput
          (Assigned.put canonical (.rows Tag.source) none) (some quarter))) noRegisters
        (RouteId.a,LaneDisturbance.nominal,Action.cw,Ambient.inK KState.p2w1))=
      some (fun i => after i+quarter i) := by
    apply RawRationalMargin.read_vector_some
    intro i
    cases i <;> decide +kernel
  rw [hb,ha]
  apply congrArg some
  funext i
  cases i <;> decide +kernel
end CSTTT.RobustnessTheory.POS04RationalMargin

namespace CSTTT.RobustnessTheory.POS04RationalMargin
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.GenericHandoff CSTTT.TargetTheory.ComputedFIACH
open CSTTT.RobustnessTheory ExactFiveMargins RegisterInterpreter RegisterInitialization
-- Class (b): one returned event with all five positives, whole gates and real support.
theorem supported_box_event (delta : Vector) (box : WithinBox radius delta) :
    RawRationalMargin.partialEventAdvance model (input delta)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=
      some (fun i => advances i+delta i) ∧
    (∀ i, 0<advances i+delta i) ∧
    RawRationalMargin.hardGate_F model (input delta) ∧
    RawRationalMargin.hardGate_O model (input delta) ∧
    RawRationalMargin.Supported model (input delta)
      (RawRationalMargin.initialRun model (input delta) (ready delta) RouteId.a)
      LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1) ∧
    RawRationalMargin.outcomeWeight model (input delta)
      (RawRationalMargin.initialRun model (input delta) (ready delta) RouteId.a)
      LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=some (1 : Rat) := by
  refine ⟨?_,(all_corrections delta box).2.1,(inherited_gates delta).1,
    (inherited_gates delta).2,actual_supported delta,actual_weight delta⟩
  rw [RawRationalMargin.partial_event_advance_eq model (input delta) (ready delta)]
  exact actual_advance delta
-- Class (b): actual missing positions refute the whole partial event.
theorem missing_positions_vector :
    RawRationalMargin.partialEventAdvance model
      (partialInput (Assigned.put canonical .positions none) (some quarter))
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=none :=
  PartialEventReadout.missing_after_rejects _ _ _ _ _ _ _ _ .predictive missing_positions_after
-- Class (b): actual missing writer refutes the whole partial event.
theorem missing_writers_vector :
    RawRationalMargin.partialEventAdvance model
      (partialInput (Assigned.put canonical .writers none) (some quarter))
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=none :=
  PartialEventReadout.missing_after_rejects _ _ _ _ _ _ _ _ .record missing_writers_after
-- Class (b): actual missing maintenance refutes the whole partial event.
theorem missing_maintenance_vector :
    RawRationalMargin.partialEventAdvance model
      (partialInput (Assigned.put canonical .maintenance none) (some quarter))
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=none :=
  PartialEventReadout.missing_after_rejects _ _ _ _ _ _ _ _ .record missing_maintenance_after
-- Class (b): actual missing correction refutes the whole partial event.
theorem missing_correction_vector :
    RawRationalMargin.partialEventAdvance model (partialInput canonical none)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=none :=
  PartialEventReadout.missing_after_rejects _ _ _ _ _ _ _ _ .order (missing_correction_after .order)
-- Class (b): outside-box control refutes any positive returned partial vector.
theorem outside_no_positive_readout :
    ¬ ∃ v, RawRationalMargin.partialEventAdvance model (input outside)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=some v ∧ ∀ i, 0<v i := by
  rintro ⟨v,hv,hpos⟩
  rw [RawRationalMargin.partial_event_advance_eq model (input outside) (ready outside)] at hv
  exact outside_actual_not_positive v hv hpos
-- Class (b): radius-one lower corner refutes any positive returned partial vector.
theorem zero_slack_no_positive_readout :
    ¬ ∃ v, RawRationalMargin.partialEventAdvance model (input zeroSlack)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=some v ∧ ∀ i, 0<v i := by
  rintro ⟨v,hv,hpos⟩
  rw [RawRationalMargin.partial_event_advance_eq model (input zeroSlack) (ready zeroSlack)] at hv
  exact zero_slack_actual_not_positive v hv hpos
-- Class (b): declared constant receiver uses the same actual old execution frame.
def constantModel := POS04FinalHandoff.constant
-- Class (b): every rational correction preserves the direct receiver failure.
theorem constant_receiver_failure (delta : Option Vector) :
    ¬ FinalHandoff.ReceiverReadout constantModel (partialInput canonical delta).source :=
  POS04FinalHandoff.constant_no_receiver_readout
-- Class (b): every rational correction leaves both complete gates rejected.
theorem constant_gate_failure (delta : Option Vector) :
    ¬ RawRationalMargin.hardGate_F constantModel (partialInput canonical delta) ∧
    ¬ RawRationalMargin.hardGate_O constantModel (partialInput canonical delta) :=
  POS04FinalHandoff.constant_no_handoff
-- Class (b): numeric event is unchanged by the declared receiver primitive change.
theorem constant_partial_event (delta : Option Vector) :
    RawRationalMargin.partialEventAdvance constantModel (partialInput canonical delta)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=
    RawRationalMargin.partialEventAdvance model (partialInput canonical delta)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1) := rfl
-- Class (b): original full gates can hold while missing correction rejects execution.
theorem missing_correction_original_gates :
    RawRationalMargin.hardGate_F model (partialInput canonical none) ∧
    RawRationalMargin.hardGate_O model (partialInput canonical none) :=
  ⟨POS04FinalHandoff.positive_F,POS04FinalHandoff.positive_O⟩
end CSTTT.RobustnessTheory.POS04RationalMargin

namespace CSTTT.RobustnessTheory.POS04RationalMargin
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.GenericHandoff CSTTT.TargetTheory.ComputedFIACH
open CSTTT.RobustnessTheory ExactFiveMargins RegisterInterpreter RegisterInitialization
-- Class (b): kernel witness of positive actual numbers and failed complete gates.
theorem constant_positive_no_gates (delta : Vector) (box : WithinBox radius delta) :
    RawRationalMargin.partialEventAdvance constantModel (input delta)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=
      some (fun i => advances i+delta i) ∧
    (∀ i, 0<advances i+delta i) ∧
    ¬ RawRationalMargin.hardGate_F constantModel (input delta) ∧
    ¬ RawRationalMargin.hardGate_O constantModel (input delta) ∧
    ¬ FinalHandoff.ReceiverReadout constantModel (input delta).source := by
  exact ⟨(constant_partial_event (some delta)).trans (supported_box_event delta box).1,
    (supported_box_event delta box).2.1,(constant_gate_failure (some delta)).1,
    (constant_gate_failure (some delta)).2,constant_receiver_failure (some delta)⟩
-- Class (b): the frozen quarter correction is in the whole closed half-box.
theorem quarter_within_box : WithinBox radius quarter := by
  intro i
  cases i <;> decide +kernel
-- Class (b): actual positivity alone cannot force the full original F gate.
theorem positive_numbers_do_not_force_F :
    ¬ ∀ m : POS04FinalHandoff.Model, ∀ delta : Vector, WithinBox radius delta →
      (∃ v, RawRationalMargin.partialEventAdvance m (input delta)
        RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=some v ∧
        ∀ i, 0<v i) → RawRationalMargin.hardGate_F m (input delta) := by
  intro h
  have w := constant_positive_no_gates quarter quarter_within_box
  exact w.2.2.1 (h constantModel quarter quarter_within_box ⟨_,w.1,w.2.1⟩)
-- Class (b): actual positivity alone cannot force the full original O gate.
theorem positive_numbers_do_not_force_O :
    ¬ ∀ m : POS04FinalHandoff.Model, ∀ delta : Vector, WithinBox radius delta →
      (∃ v, RawRationalMargin.partialEventAdvance m (input delta)
        RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=some v ∧
        ∀ i, 0<v i) → RawRationalMargin.hardGate_O m (input delta) := by
  intro h
  have w := constant_positive_no_gates quarter quarter_within_box
  exact w.2.2.2.1 (h constantModel quarter quarter_within_box ⟨_,w.1,w.2.1⟩)
-- Class (b): every deleted original raw primitive refutes both complete old gates.
theorem missing_primitive_gates (source : CSTTT.POS04.Assigned.Assignment)
    (k : Cell) (delta : Option Vector) :
    ¬ RawRationalMargin.hardGate_F model (partialInput (Assigned.put source k none) delta) ∧
    ¬ RawRationalMargin.hardGate_O model (partialInput (Assigned.put source k none) delta) := by
  have incomplete : ¬ CSTTT.POS04.Assigned.Complete primitiveCells (Assigned.put source k none) := by
    intro hc
    have hk := hc k (primitive_cells_complete k)
    simp [Assigned.put_same] at hk
  have reject : sourcePackageCheck {baseline with assignment := Assigned.put source k none} ≠ true := by
    simp [sourcePackageCheck,incomplete]
  constructor
  · intro gate
    exact reject ((POS04FinalCorrespondence.final_full_iff
      {baseline with assignment := Assigned.put source k none}).mp gate).1.1
  · intro gate
    exact reject ((POS04FinalCorrespondence.final_operational_iff
      {baseline with assignment := Assigned.put source k none}).mp gate).1.1

end CSTTT.RobustnessTheory.POS04RationalMargin

namespace CSTTT.RobustnessTheory.POS04RationalMargin
open CSTTT.POS04 CSTTT.Objecthood.T1Audit CSTTT.TargetTheory.GenericHandoff CSTTT.TargetTheory.ComputedFIACH ExactFiveMargins
-- Class (b): the actual returned quarter event cannot be an original Nat difference.
theorem quarter_event_not_original_nat_difference (a b : Nat) :
    ¬ ∃ v : Vector, RawRationalMargin.partialEventAdvance model (input quarter)
      RouteId.a LaneDisturbance.nominal Action.cw (Ambient.inK KState.p2w1)=some v ∧
      v .order=(b : Rat)-(a : Rat) := by
  rintro ⟨v,read,original⟩
  rw [RawRationalMargin.partial_event_advance_eq model (input quarter) (ready quarter),
    actual_advance quarter] at read
  have he := congrArg (fun f : Vector => f .order) (Option.some.inj read)
  have numeric : advances .order+quarter .order=(5/4 : Rat) := by decide +kernel
  change advances .order+quarter .order=v .order at he
  rw [numeric] at he
  exact RationalRegisters.quarter_not_original_nat_difference a b (original.symm.trans he.symm)
end CSTTT.RobustnessTheory.POS04RationalMargin
