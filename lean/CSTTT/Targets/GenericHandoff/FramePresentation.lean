import CSTTT.Targets.GenericHandoff.PresentationCoherence
import CSTTT.Targets.GenericHandoff.ExecutionFrontier

/-! Raw frame → finite presentation constructor, TTH-06.
The temporal presentation cannot supply a second probability table, updater,
clock period, order/progress/record/writer/owner instruction, or closure. These
are DEFINED from the acquisition frame. Only the typed predictive coordinate
translation and finite primitive projection are raw interface operations.
Their all-context simulation is checked by TemporalRuntimeCoherence.Laws.
This is not an assertion that arbitrary run recipes have finite factors. -/
namespace CSTTT.TargetTheory.GenericHandoff.FramePresentation
open RegisterInterpreter
variable {Cell R S A O H H0 Route Route0 Stage Id Owner D P : Type}
  {Value : Cell → Type} {RV : R → Type}

local notation "Frame" => ExecutionFrontier.Raw Cell Value R RV D A O P (List S × List Id) Bool Stage Id H Route

/-- Typed alphabet translation; all other raw observer instructions are
literally the frame instructions, including writer and absolute ticks. -/
def readouts (f : Frame)
    (predictive : P → TemporalFactorRules.Predictive O) :
    RegisterFuture.Readouts Cell Value R RV (TemporalFactorRules.Predictive O) (List S × List Id) Bool :=
  {f.readouts with predictive := .map predictive f.readouts.predictive}

def runtime (f : Frame)
    (predictive : P → TemporalFactorRules.Predictive O) :
    RegisterFuture.Raw Cell Value R RV D A O (TemporalFactorRules.Predictive O) (List S × List Id) Bool :=
  ⟨f.acquisition.execution.outcomes,f.acquisition.execution.actions,
    f.acquisition.execution.disturbances,f.tickPeriod,f.acquisition.execution.row,
    f.acquisition.execution.program,readouts f predictive⟩

def raw (cfg : TemporalFactorRules.Schema S A O H0 Route0 Stage Id Owner)
    (v : TemporalFactorCells.Bindings Cell Value S A O H0 Route0 Stage Id Owner)
    (f : Frame)
    (predictive : P → TemporalFactorRules.Predictive O)
    (projection : Expr Cell Value R RV Unit (TemporalFactorRules.Run O S Id))
    (owner : Owner → CarrierId) :
    TemporalRuntimeCoherence.Raw Cell Value R RV S A O H0 Route0 Stage Id Owner D :=
  ⟨cfg,v,runtime f predictive,projection,owner⟩

theorem row (f : Frame)
    (predictive : P → TemporalFactorRules.Predictive O) :
    (runtime f predictive).row = f.acquisition.execution.row := rfl

theorem updater (f : Frame)
    (predictive : P → TemporalFactorRules.Predictive O) :
    (runtime f predictive).program = f.acquisition.execution.program := rfl

theorem period (f : Frame)
    (predictive : P → TemporalFactorRules.Predictive O) :
    (runtime f predictive).tickPeriod = f.tickPeriod := rfl

/-- Every evolving observer component is taken from the frame, not a supplied
candidate agreeing only at snapshots. -/
theorem observer (f : Frame)
    (predictive : P → TemporalFactorRules.Predictive O) :
    (runtime f predictive).readouts.order = f.readouts.order ∧
    (runtime f predictive).readouts.ticks = f.readouts.ticks ∧
    (runtime f predictive).readouts.progress = f.readouts.progress ∧
    (runtime f predictive).readouts.writer = f.readouts.writer ∧
    (runtime f predictive).readouts.record = f.readouts.record ∧
    (runtime f predictive).readouts.residue = f.readouts.residue ∧
    (runtime f predictive).readouts.maintenance = f.readouts.maintenance ∧
    (runtime f predictive).readouts.owner = f.readouts.owner :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem predictive (f : Frame)
    (image : P → TemporalFactorRules.Predictive O) (a : Assignment Cell Value) (x : Registers R RV) :
    (runtime f image).readouts.predictive.eval a x () =
      (f.readouts.predictive.eval a x ()).map image := rfl

/-- Owning construction for both presentations. There are no separate
candidate temporal dynamics/observers in this interface. -/
structure Raw (Cell : Type) (Value : Cell → Type) (SR TR : Type)
    (SRV : SR → Type) (TRV : TR → Type)
    (S A O H HF Route Stage Id Owner D P Q : Type) where
  sourceFrame : ExecutionFrontier.Raw Cell Value SR SRV D A O P (List S × List Id) Bool Stage Id H Route
  targetFrame : ExecutionFrontier.Raw Cell Value TR TRV D A O Q (List S × List Id) Bool Stage Id H Route
  sourceSchema : TemporalFactorRules.Schema S A O HF Route Stage Id Owner
  targetSchema : TemporalFactorRules.Schema S A O HF Route Stage Id Owner
  sourceCells : TemporalFactorCells.Bindings Cell Value S A O HF Route Stage Id Owner
  targetCells : TemporalFactorCells.Bindings Cell Value S A O HF Route Stage Id Owner
  sourcePredictive : P → TemporalFactorRules.Predictive O
  targetPredictive : Q → TemporalFactorRules.Predictive O
  sourceProjection : Expr Cell Value SR SRV Unit (TemporalFactorRules.Run O S Id)
  targetProjection : Expr Cell Value TR TRV Unit (TemporalFactorRules.Run O S Id)
  owner : Owner → CarrierId
  events : CellView Cell Value (List (AcquisitionEndpoint.SupportedEvent Stage Id))
  receiver : CellView Cell Value AcquisitionExecution.Receiver
  entry : Stage
  exit : Stage
  exitEvent : Id
  fallback : S
  rowScale : Nat
  transfer : S → S
  clock : Stage → Nat
  factorMaps : StaticView Cell Value (FactorTransport.Maps S S A A Owner)
  record : StaticView Cell Value (RecordComponent.Data Stage Id Route)

variable {SR TR HF Q : Type} {SRV : SR → Type} {TRV : TR → Type}
local notation "Model" => Raw Cell Value SR TR SRV TRV S A O H HF Route Stage Id Owner D P Q

def presentation (m : Model) : PresentationCoherence.Raw Cell Value SR TR SRV TRV S A O HF Route Stage Id Owner D where
  source := raw m.sourceSchema m.sourceCells m.sourceFrame m.sourcePredictive m.sourceProjection m.owner
  target := raw m.targetSchema m.targetCells m.targetFrame m.targetPredictive m.targetProjection m.owner
  events := m.events
  receiver := m.receiver
  entry := m.entry
  exit := m.exit
  exitEvent := m.exitEvent
  fallback := m.fallback
  rowScale := m.rowScale
  transfer := m.transfer
  clock := m.clock
  factorMaps := m.factorMaps
  record := m.record

theorem source_row (m : Model) : (presentation m).source.runtime.row = m.sourceFrame.acquisition.execution.row := rfl
theorem target_row (m : Model) : (presentation m).target.runtime.row = m.targetFrame.acquisition.execution.row := rfl
theorem source_program (m : Model) : (presentation m).source.runtime.program = m.sourceFrame.acquisition.execution.program := rfl
theorem target_program (m : Model) : (presentation m).target.runtime.program = m.targetFrame.acquisition.execution.program := rfl

theorem source_primitives (m : Model) :
    (PresentationCoherence.endpointBindings (presentation m)).source = m.sourceCells := rfl
theorem target_primitives (m : Model) :
    (PresentationCoherence.endpointBindings (presentation m)).target = m.targetCells := rfl

/-- Public stage/clock/owner interface equations. These compare raw schemas;
they do not demand baseline-specific numeric readouts. -/
def SchemaCheck (m : Model) : Prop :=
  m.sourceFrame.schema.clock = m.clock ∧ m.targetFrame.schema.clock = m.clock ∧
  m.sourceFrame.schema.stages = m.sourceSchema.stages ∧
  m.targetFrame.schema.stages = m.targetSchema.stages ∧
  m.sourceFrame.schema.eventIds = m.sourceSchema.events ∧
  m.targetFrame.schema.eventIds = m.targetSchema.events ∧
  m.sourceFrame.schema.routes = m.sourceSchema.routes ∧
  m.targetFrame.schema.routes = m.targetSchema.routes ∧
  m.sourceFrame.schema.entryStage = m.entry ∧ m.targetFrame.schema.entryStage = m.entry ∧
  m.sourceFrame.schema.exitStage = m.exit ∧ m.targetFrame.schema.exitStage = m.exit ∧
  m.sourceFrame.schema.source = m.owner m.sourceSchema.owner ∧
  m.targetFrame.schema.target = m.owner m.targetSchema.owner

def sourceInterface (m : Model) :=
  (m.sourceFrame.schema.clock,m.sourceFrame.schema.stages,m.sourceFrame.schema.eventIds,
    m.sourceFrame.schema.routes,m.sourceFrame.schema.entryStage,m.sourceFrame.schema.exitStage,
    m.sourceFrame.schema.source)
def sourceExpected (m : Model) :=
  (m.clock,m.sourceSchema.stages,m.sourceSchema.events,m.sourceSchema.routes,m.entry,m.exit,
    m.owner m.sourceSchema.owner)
def targetInterface (m : Model) :=
  (m.targetFrame.schema.clock,m.targetFrame.schema.stages,m.targetFrame.schema.eventIds,
    m.targetFrame.schema.routes,m.targetFrame.schema.entryStage,m.targetFrame.schema.exitStage,
    m.targetFrame.schema.target)
def targetExpected (m : Model) :=
  (m.clock,m.targetSchema.stages,m.targetSchema.events,m.targetSchema.routes,m.entry,m.exit,
    m.owner m.targetSchema.owner)

theorem source_interface (m : Model) (h : SchemaCheck m) : sourceInterface m = sourceExpected m := by
  rcases h with ⟨hc,_,hs,_,he,_,hr,_,hi,_,ho,_,hw,_⟩
  simp only [sourceInterface,sourceExpected,hc,hs,he,hr,hi,ho,hw]

theorem target_interface (m : Model) (h : SchemaCheck m) : targetInterface m = targetExpected m := by
  rcases h with ⟨_,hc,_,hs,_,he,_,hr,_,hi,_,ho,_,hw⟩
  simp only [targetInterface,targetExpected,hc,hs,he,hr,hi,ho,hw]

/-- Covers EACH public stage/clock/owner interface field via its selector,
including pointwise clock evaluation. The inequality is a raw equation, not
an assumed failure flag. -/
theorem source_interface_guard {X : Type} (m : Model)
    (field : ((Stage → Nat) × List Stage × List Id × List Route × Stage × Stage × CarrierId) → X)
    (bad : field (sourceInterface m) ≠ field (sourceExpected m)) : ¬ SchemaCheck m :=
  fun h => bad (congrArg field (source_interface m h))

theorem target_interface_guard {X : Type} (m : Model)
    (field : ((Stage → Nat) × List Stage × List Id × List Route × Stage × Stage × CarrierId) → X)
    (bad : field (targetInterface m) ≠ field (targetExpected m)) : ¬ SchemaCheck m :=
  fun h => bad (congrArg field (target_interface m h))

theorem source_clock_guard (m : Model) (s : Stage)
    (bad : m.sourceFrame.schema.clock s ≠ m.clock s) : ¬ SchemaCheck m :=
  fun h => bad (congrFun h.1 s)

theorem target_owner_guard (m : Model)
    (bad : m.targetFrame.schema.target ≠ m.owner m.targetSchema.owner) : ¬ SchemaCheck m :=
  fun h => bad h.2.2.2.2.2.2.2.2.2.2.2.2.2

end CSTTT.TargetTheory.GenericHandoff.FramePresentation
