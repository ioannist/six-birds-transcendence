import CSTTT.Targets.GenericHandoff.NativeComposition.AvailabilityFactor
import CSTTT.Targets.GenericHandoff.NativeComposition.ObjecthoodProbe
import CSTTT.Targets.GenericHandoff.NativeComposition.ExposureScout

/-! C4 at its disclosed collision/connector/exposure surrogate grade, bound
to the same assigned native rows/positions/hazards/classes as C2/C3/C6.
The connector is reconstructed by the declared probe from actual rows.
It is never a supplied supported-path verdict. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ExposureRepair
open RegisterInterpreter

def start : Factor := (false,true,false)
def finish : Factor := (true,true,false)
def schema : ExposureRules.Schema Factor Bool Factor Unit := ExposureScout.schema (start,finish)
def connector (i : Input) : List Factor :=
  start :: (i.temporal.rows start (ObjecthoodProbe.policy i.temporal start)).map Prod.fst
def data (i : Input) : ExposureRules.Raw Factor Bool Factor Unit :=
  ⟨i.temporal.rows,i.temporal.positions,i.temporal.hazards,[.availability],
    ObjecthoodProbe.policy i.temporal,fun _ => connector i,i.temporal.classes⟩
def bindings (cell : Owner) (copy : Bool) : ExposureRules.Bindings Owner MemoryValue Factor Bool Factor Unit :=
  let get := MemoryFrames.selectInput copy
  ⟨⟨cell,fun p => (get p).temporal.rows⟩,⟨cell,fun p => (get p).temporal.positions⟩,
    ⟨cell,fun p => (get p).temporal.hazards⟩,⟨cell,fun _ => [.availability]⟩,
    ⟨cell,fun p => ObjecthoodProbe.policy (get p).temporal⟩,
    ⟨cell,fun p _ => connector (get p)⟩,⟨cell,fun p => (get p).temporal.classes⟩⟩

theorem decoded (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) :
    ExposureRules.decoded (bindings cell copy) a=
      (a cell).map (fun p => data (MemoryFrames.selectInput copy p)) := by
  cases ha : a cell <;> simp [ExposureRules.decoded,bindings,CellView.read,ha,data]
theorem acceptance_iff (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) :
    ExposureRules.AssignedAccept schema (bindings cell copy) a ↔
      ∃ p, a cell=some p ∧ ExposureRules.SurrogateAccept schema (data (MemoryFrames.selectInput copy p)) := by
  simp only [ExposureRules.AssignedAccept,decoded]
  cases a cell <;> simp
theorem missing_rejected (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) (hm : a cell=none) :
    ¬ ExposureRules.AssignedAccept schema (bindings cell copy) a := by
  rw [acceptance_iff]
  simp [hm]

theorem data_publish (i : Input) : data (publish i)=data i := rfl
theorem publication_source_decoded (a : Assignment Owner MemoryValue) (o : Owner) :
    ExposureRules.decoded (bindings (swapOwner o) true) (memoryImage a)=
      ExposureRules.decoded (bindings o false) a := by
  rw [decoded,decoded]
  have h := congrArg (fun z : Option Input => z.map data) (published_source a o)
  simpa [sourceInputs,currentInputs,Option.map_map,MemoryFrames.selectInput] using h
theorem publication_source_accept_iff (a : Assignment Owner MemoryValue) (o : Owner) :
    ExposureRules.AssignedAccept schema (bindings (swapOwner o) true) (memoryImage a) ↔
      ExposureRules.AssignedAccept schema (bindings o false) a := by
  simp only [ExposureRules.AssignedAccept,publication_source_decoded]

theorem actual_connector : connector (AvailabilityFactor.input false)=[start,finish] := rfl
theorem gate : ExposureRules.Gate schema (data (AvailabilityFactor.input false)) := by
  refine ⟨?_,?_,?_,by decide +kernel,by decide +kernel,by decide +kernel⟩
  · exact factor_domain
  · simp only [ProfileRules.RowsValid]; decide +kernel
  · refine ⟨rfl,?_⟩
    intro s t
    rcases s with ⟨p,v,j⟩
    rcases t with ⟨q,w,k⟩
    cases p <;> cases v <;> cases j <;> cases q <;> cases w <;> cases k <;> decide +kernel
theorem collision : ExposureRules.Collision schema (data (AvailabilityFactor.input false)) := by
  unfold ExposureRules.Collision
  decide +kernel
theorem supported_connector : ExposureRules.Connector schema (data (AvailabilityFactor.input false)) := by
  unfold ExposureRules.Connector ExposureRules.Collision
  decide +kernel
theorem exposed : ExposureRules.Exposed schema (data (AvailabilityFactor.input false)) := by
  refine ⟨.availability,by decide +kernel,⟨(false,false,false),start,by decide +kernel⟩,?_⟩
  intro s t hp
  have hv : s.2.1=t.2.1 := (AvailabilityFactor.prediction_iff false s t).mp (congrArg Sum.inl hp) |>.2
  change ((0,clauseSchema.actions.filter (fun a => !(AvailabilityFactor.rows s a).isEmpty)),none)=
    ((0,clauseSchema.actions.filter (fun a => !(AvailabilityFactor.rows t a).isEmpty)),none)
  cases ht : t.2.1 <;> simp [clauseSchema,AvailabilityFactor.rows,hv,ht]
theorem actual_c4_accept : ExposureRules.SurrogateAccept schema (data (AvailabilityFactor.input false)) :=
  ⟨gate,collision,supported_connector,exposed⟩

theorem old_actual_c4_rejected (i : Input)
    (hr : i.temporal.rows=(factorData false).rows)
    (hp : i.temporal.positions=(factorData false).positions)
    (hh : i.temporal.hazards=(factorData false).hazards) :
    ¬ ExposureRules.SurrogateAccept schema (data i) := by
  have h := ExposureScout.actual_c4_rejected (start,finish) [.availability]
    (ObjecthoodProbe.policy i.temporal) (connector i)
  intro ha
  apply h
  -- C4 acceptance uses classes only in Gate; the operational contradiction
  -- in the scout is independent of that reference field.
  have hc : i.temporal.classes=labels := ha.1.2.2.1.1
  simpa [data,ExposureScout.raw,hr,hp,hh,hc] using ha

theorem restored_availability_exposed_rejected (i : Input)
    (hr : i.temporal.rows=(factorData false).rows) : ¬ ExposureRules.Exposed schema (data i) := by
  rintro ⟨c,hc,⟨s,t,hn⟩,_⟩
  have he : c=.availability := by simpa [data] using hc
  subst c
  exact hn (by simp [ExposureRules.channel,data,hr,factorData,schema,ExposureScout.schema,clauseSchema])

def brokenConnectorInput : Input :=
  {AvailabilityFactor.input false with temporal :=
    {AvailabilityFactor.temporal false with rows := fun s a =>
      if s=start ∧ a=true then [] else AvailabilityFactor.rows s a}}
theorem broken_connector_rejected : ¬ ExposureRules.Connector schema (data brokenConnectorInput) := by
  unfold ExposureRules.Connector ExposureRules.Collision
  decide +kernel
theorem broken_actual_c4_rejected : ¬ ExposureRules.SurrogateAccept schema (data brokenConnectorInput) :=
  fun h => broken_connector_rejected h.2.2.1

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ExposureRepair
