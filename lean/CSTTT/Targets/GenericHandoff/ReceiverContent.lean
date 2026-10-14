import CSTTT.Targets.GenericHandoff.RawHandoff

/-! All-input receiver reset square. This is a component of the pending G0
receiver binding, not a final handoff gate or a nominal-protocol replacement.
Frame initialization is raw instruction syntax; received runs/classes are
computed. Activation remains separate from merely initializing a frame. -/
namespace CSTTT.TargetTheory.GenericHandoff.ReceiverContent
open RegisterInterpreter RegisterInitialization
set_option maxRecDepth 16384
set_option maxHeartbeats 600000

variable {SC Cell R SR TR S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint : Type}
  {SourceValue : SC → Type} {Value : Cell → Type} {RV : R → Type} {SRV : SR → Type} {TRV : TR → Type}
local notation "Model" => OwningHandoff.RawHandoff SC Cell SourceValue Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint
local notation "Input" => HistoricalAcquisition.ReceiverInput S H Id Route

/-- Raw typed initialization and coordinate instructions, with no input run,
receiver result, predictive-class map, or activation verdict. -/
structure Instructions (Cell TR S O H Id Route : Type) (Value : Cell → Type) (TRV : TR → Type) where
  resetProgram : InitialProgram Cell Value TR TRV (HistoricalAcquisition.ReceiverInput S H Id Route)
  outcome : S → O

local notation "Recipe" => Instructions Cell TR S O H Id Route Value TRV
variable [DecidableEq S] [DecidableEq O] [DecidableEq Route]
  [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner]

def acquisition (m : Model) := HistoricalPackageRuntime.acquisition (OwningHandoff.autonomy m)

/-- Every input terminal, full past and path is covered. The endpoint data and
factor map must decode from the SAME owning primitives. Frame equality binds
historical reception to actual receiver registers, beyond a class equality.
All five evolving coordinates are checked, including assigned funding. -/
structure Laws (m : Model) (r : Recipe) (a : Assignment Cell Value)
    (hi : RegisterInitialization.Ready r.resetProgram a)
    (hh : HistoricalAcquisition.Ready (acquisition m) a)
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target a)
    (he : ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime m)) a)
    (d : AcquisitionEndpoint.Data S A O HF Route Stage Id Owner)
    (maps : FactorTransport.Maps S S A A Owner) : Prop where
  decoded : AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings a = some d
  factorMap : m.frames.factorMaps.read a = some maps
  stateMap : maps.state = m.frames.transfer
  coordinate : m.historical.targetCoordinate.read a = some m.frames.transfer
  histories : ∀ rid route routes hs,
    TemporalFactorRules.route d.source rid = some route →
    m.historical.routes.read a = some routes → m.historical.histories.read a = some hs →
    hs (routes rid).history = d.source.histories route.history
  paths : ∀ rid route routes, TemporalFactorRules.route d.source rid = some route →
    m.historical.routes.read a = some routes → (routes rid).path = route.eventPath
  endpointHistories : d.target.histories = d.source.histories
  receiver : m.historical.receiver.read a = some d.receiver
  realized : m.historical.realized.read a = some d.target.realized
  activation : ∀ records, m.historical.activationEvents.read a = some records →
    (HistoricalAcquisition.Activated d.receiver records d.target.realized ↔
      AcquisitionEndpoint.active (OwningHandoff.endpoint m).schema d = true)
  outcome : ∀ s, m.frames.targetSchema.base.destination (r.outcome s) = some s
  frame : ∀ input, ExecutionLink.embed (PublicRuntime.historicalLink (OwningHandoff.publicRuntime m)) a he
      (RegisterInitialization.initial r.resetProgram a hi input) =
    HistoricalAcquisition.reset (acquisition m) a hh input
  projection : ∀ input, TemporalRuntimeCoherence.project (OwningHandoff.presentation m).target a ht
      (RegisterInitialization.initial r.resetProgram a hi input) =
    ⟨r.outcome (m.frames.transfer input.1),0,0,(input.2.1,input.2.2.1),d.receiver.funded⟩

noncomputable def receivedRun (m : Model) (r : Recipe) (a : Assignment Cell Value)
    (hi : RegisterInitialization.Ready r.resetProgram a)
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target a)
    (input : Input) :=
  TemporalRuntimeCoherence.project (OwningHandoff.presentation m).target a ht
    (RegisterInitialization.initial r.resetProgram a hi input)

/-- Source absence returns none before an initialized run can be returned.
Reset alone never licenses activation. -/
noncomputable def receive (m : Model) (r : Recipe) (a : Assignment Cell Value)
    (hi : RegisterInitialization.Ready r.resetProgram a)
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target a)
    (input : Input) :
    Option (TemporalFactorRules.Run O S Id) := do
  let d ← AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings a
  if AcquisitionEndpoint.active (OwningHandoff.endpoint m).schema d then
    some (receivedRun m r a hi ht input) else none

/-- Classify the ACTUAL returned factor. Absent/malformed factor decoding
stays absent rather than using a default representative. -/
noncomputable def receivedClass (m : Model) (r : Recipe) (a : Assignment Cell Value)
    (hi : RegisterInitialization.Ready r.resetProgram a)
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target a)
    (input : Input) :
    Option FactorTransport.Predictive := do
  let d ← AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings a
  let run ← receive m r a hi ht input
  let s ← m.frames.targetSchema.base.destination run.factor
  pure (FactorTransport.classOf m.frames.targetSchema (PresentationCoherence.factor d.target) s)

/-- A named semantic readout: actual returned classes distinguish EVERY pair
of source classes. Decoding and a genuine distinct input pair are required,
so absent data and singleton/empty input classes do not pass vacuously. -/
def ContentFaithful (m : Model) (r : Recipe) (a : Assignment Cell Value)
    (hi : RegisterInitialization.Ready r.resetProgram a)
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target a) : Prop :=
  ∃ d, AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings a = some d ∧
    (∃ x y : Input, FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) x.1 ≠
      FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) y.1) ∧
    (∀ input : Input, ∃ cls, receivedClass m r a hi ht input = some cls) ∧
    ∀ x y : Input, FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) x.1 ≠
      FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) y.1 →
      receivedClass m r a hi ht x ≠ receivedClass m r a hi ht y

variable {m : OwningHandoff.RawHandoff SC Cell SourceValue Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint}
  {r : Instructions Cell TR S O H Id Route Value TRV} {a : Assignment Cell Value}
  {hi : RegisterInitialization.Ready r.resetProgram a}
  {hh : HistoricalAcquisition.Ready (acquisition m) a}
  {ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target a}
  {he : ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime m)) a}
  {d : AcquisitionEndpoint.Data S A O HF Route Stage Id Owner}
  {maps : FactorTransport.Maps S S A A Owner}

theorem received_run (laws : Laws m r a hi hh ht he d maps) (input : Input) :
    receivedRun m r a hi ht input =
      ⟨r.outcome (maps.state input.1),0,0,(input.2.1,input.2.2.1),d.receiver.funded⟩ := by
  rw [receivedRun,laws.projection,laws.stateMap]

theorem source_absent
    (decoded : AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings a = some d) (absent : d.receiver.sourcePresent = false) (input : Input) :
    receive m r a hi ht input = none := by
  simp [receive,decoded,AcquisitionEndpoint.active,absent]

theorem source_absent_class
    (decoded : AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings a = some d) (absent : d.receiver.sourcePresent = false) (input : Input) :
    receivedClass m r a hi ht input = none := by
  simp [receivedClass,decoded,source_absent decoded absent input]

theorem active_class (laws : Laws m r a hi hh ht he d maps)
    (active : AcquisitionEndpoint.active (OwningHandoff.endpoint m).schema d = true) (input : Input) :
    receivedClass m r a hi ht input = some
      (FactorTransport.classOf m.frames.targetSchema (PresentationCoherence.factor d.target) (maps.state input.1)) := by
  simp [receivedClass,receive,laws.decoded,active,received_run laws,laws.outcome]

/-- Genuine content dependence for EVERY raw input. Class injectivity comes
from checked factor transport; a distinct source pair is explicit evidence,
not presumed to exist in an arbitrary carrier. -/
theorem distinct_source_classes (laws : Laws m r a hi hh ht he d maps)
    (eqs : FactorTransport.Equations m.frames.sourceSchema m.frames.targetSchema
      (PresentationCoherence.factor d.source) (PresentationCoherence.factor d.target) maps)
    (active : AcquisitionEndpoint.active (OwningHandoff.endpoint m).schema d = true)
    (x y : Input)
    (distinct : FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) x.1 ≠
      FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) y.1) :
    receivedClass m r a hi ht x ≠ receivedClass m r a hi ht y := by
  rw [active_class laws active x,active_class laws active y]
  intro same
  have hp := Option.some.inj same
  rw [eqs.predictive,eqs.predictive] at hp
  exact distinct (eqs.classInjective x.1 y.1 hp)

/-- The actual decoded factor readout supplies the equations on the endpoint
primitives. Neither a second factor table nor a freely supplied class map is
needed by content sensitivity. -/
theorem factor_equations (laws : Laws m r a hi hh ht he d maps)
    (hf : RuntimeLineage.FactorReadout (OwningHandoff.factor m) a) :
    FactorTransport.Equations m.frames.sourceSchema m.frames.targetSchema
      (PresentationCoherence.factor d.source) (PresentationCoherence.factor d.target) maps := by
  obtain ⟨ds,dt,mp,hs,htarget,hm,eqs⟩ := hf
  have fields := PresentationCoherence.endpoint_factor_decoded (OwningHandoff.presentation m) a d laws.decoded
  have es := Option.some.inj (hs.symm.trans fields.1)
  have et := Option.some.inj (htarget.symm.trans fields.2)
  have em := Option.some.inj (hm.symm.trans laws.factorMap)
  subst ds; subst dt; subst mp
  exact eqs

theorem distinct_source_classes_from_factor (laws : Laws m r a hi hh ht he d maps)
    (hf : RuntimeLineage.FactorReadout (OwningHandoff.factor m) a)
    (active : AcquisitionEndpoint.active (OwningHandoff.endpoint m).schema d = true)
    (x y : Input)
    (distinct : FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) x.1 ≠
      FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) y.1) :
    receivedClass m r a hi ht x ≠ receivedClass m r a hi ht y :=
  distinct_source_classes laws (factor_equations laws hf) active x y distinct

theorem content_faithful (laws : Laws m r a hi hh ht he d maps)
    (hf : RuntimeLineage.FactorReadout (OwningHandoff.factor m) a)
    (active : AcquisitionEndpoint.active (OwningHandoff.endpoint m).schema d = true)
    (pair : ∃ x y : Input, FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) x.1 ≠
      FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) y.1) :
    ContentFaithful m r a hi ht :=
  ⟨d,laws.decoded,pair,(fun input => ⟨_,active_class laws active input⟩),
    distinct_source_classes_from_factor laws hf active⟩

theorem source_absent_not_faithful
    (decoded : AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings a = some d)
    (absent : d.receiver.sourcePresent = false) : ¬ ContentFaithful m r a hi ht := by
  rintro ⟨data,hdata,⟨x,y,distinct⟩,_,faithful⟩
  have same := Option.some.inj (hdata.symm.trans decoded)
  subst data
  exact faithful x y distinct ((source_absent_class decoded absent x).trans (source_absent_class decoded absent y).symm)

/-- A mismatch at any reset coordinate rejects the equations. This is a
certificate guard, not a claim that a failed sufficient check refutes a game. -/
theorem reset_coordinate_guard {X : Type}
    (field : TemporalFactorRules.Run O S Id → X) (input : Input)
    (bad : field (receivedRun m r a hi ht input) ≠
      field ⟨r.outcome (maps.state input.1),0,0,(input.2.1,input.2.2.1),d.receiver.funded⟩) :
    ¬ Laws m r a hi hh ht he d maps := fun h => bad (congrArg field (received_run h input))

theorem missing_endpoint
    (missing : AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings a = none) (input : Input) :
    receive m r a hi ht input = none ∧ receivedClass m r a hi ht input = none := by
  simp [receive,receivedClass,missing]

theorem missing_endpoint_cell (k : Cell) (hk : k ∈ (OwningHandoff.endpoint m).bindings.scope)
    (missing : a k = none) (input : Input) :
    receive m r a hi ht input = none ∧ receivedClass m r a hi ht input = none :=
  missing_endpoint (AcquisitionEndpoint.missing_input _ a k hk missing) input

theorem missing_endpoint_not_faithful
    (missing : AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings a = none) :
    ¬ ContentFaithful m r a hi ht := by
  rintro ⟨data,hdata,_⟩
  rw [missing] at hdata
  contradiction

/-- Actual historical arrival produces the same target frame, with the real
terminal, full past and event path. Activation is derived from the historical
record scan through the checked raw decoder equation. No input run is supplied. -/
theorem arrival_frame (laws : Laws m r a hi hh ht he d maps) (rid : Route) (arrived : Registers R RV)
    (ha : HistoricalAcquisition.Arrival (RuntimeComponents.acquisitionSchema m.schema)
      (acquisition m) a hh rid arrived) :
    ∃ histories routes first rest,
      m.historical.histories.read a = some histories ∧ m.historical.routes.read a = some routes ∧
      histories (routes rid).history = first::rest ∧
      let input : Input := ((first::rest).getLastD first,first::rest,(routes rid).path,(routes rid).history,rid)
      arrived = ExecutionLink.embed (PublicRuntime.historicalLink (OwningHandoff.publicRuntime m)) a he
        (RegisterInitialization.initial r.resetProgram a hi input) ∧
      receive m r a hi ht input = some (receivedRun m r a hi ht input) := by
  rcases ha with ⟨histories,sr,sp,coordinate,tr,tp,routes,events,realized,receiver,first,rest,
    hhists,hs,hsp,hcoord,htr,htp,hroutes,hev,hreal,hrecv,hrid,hhid,hlist,hss,hts,hpath,hact,hreset⟩
  have er := Option.some.inj (hrecv.symm.trans laws.receiver)
  have es := Option.some.inj (hreal.symm.trans laws.realized)
  subst receiver; subst realized
  obtain ⟨records,hrecords,act⟩ := hact
  have active := (laws.activation records hrecords).mp act
  refine ⟨histories,routes,first,rest,hhists,hroutes,hlist,?_,?_⟩
  · rw [HistoricalAcquisition.recorded_word_terminal (default := first)] at hreset
    exact hreset.trans (laws.frame _).symm
  · simp [receive,laws.decoded,active]

/-- Endpoint reception and the ACTUAL target-frame factor agree for every
coherent source input; unrelated historical coordinates are not discarded. -/
theorem endpoint_frame (laws : Laws m r a hi hh ht he d maps)
    (active : AcquisitionEndpoint.active (OwningHandoff.endpoint m).schema d = true)
    (history : HF) (input : Input)
    (terminal : (d.source.histories history).getLast? = some input.1) :
    AcquisitionEndpoint.received (OwningHandoff.endpoint m).schema d history = some (maps.state input.1) ∧
    m.frames.targetSchema.base.destination (receivedRun m r a hi ht input).factor = some (maps.state input.1) := by
  constructor
  · simp only [AcquisitionEndpoint.received,active,ite_true,laws.endpointHistories,terminal,Option.map_some]
    exact congrArg some (congrFun laws.stateMap input.1).symm
  · rw [received_run laws]
    exact laws.outcome _

/-- The entire historical→endpoint→actual receiver square, including both
the full source past and event path. The source route is a decoded primitive
reference, not an independently supplied terminal or receiver result. -/
theorem arrival_endpoint_frame (laws : Laws m r a hi hh ht he d maps)
    (rid : Route) (route : TemporalFactorRules.Route Route HF Id)
    (hroute : TemporalFactorRules.route d.source rid = some route) (arrived : Registers R RV)
    (ha : HistoricalAcquisition.Arrival (RuntimeComponents.acquisitionSchema m.schema)
      (acquisition m) a hh rid arrived) :
    ∃ histories routes first rest,
      m.historical.histories.read a = some histories ∧ m.historical.routes.read a = some routes ∧
      histories (routes rid).history = first::rest ∧ d.source.histories route.history = first::rest ∧
      (routes rid).path = route.eventPath ∧
      let input : Input := ((first::rest).getLastD first,first::rest,(routes rid).path,(routes rid).history,rid)
      arrived = ExecutionLink.embed (PublicRuntime.historicalLink (OwningHandoff.publicRuntime m)) a he
        (RegisterInitialization.initial r.resetProgram a hi input) ∧
      receive m r a hi ht input = some (receivedRun m r a hi ht input) ∧
      AcquisitionEndpoint.received (OwningHandoff.endpoint m).schema d route.history = some (maps.state input.1) ∧
      m.frames.targetSchema.base.destination (receivedRun m r a hi ht input).factor = some (maps.state input.1) := by
  obtain ⟨histories,routes,first,rest,hhists,hroutes,hlist,hframe,hreceive⟩ := arrival_frame laws rid arrived ha
  have hist := (laws.histories rid route routes histories hroute hroutes hhists).symm.trans hlist
  have path := laws.paths rid route routes hroute hroutes
  let input : Input := ((first::rest).getLastD first,first::rest,(routes rid).path,(routes rid).history,rid)
  have active : AcquisitionEndpoint.active (OwningHandoff.endpoint m).schema d = true := by
    by_cases h : AcquisitionEndpoint.active (OwningHandoff.endpoint m).schema d = true
    · exact h
    · have empty : receive m r a hi ht input = none := by simp [receive,laws.decoded,h]
      rw [empty] at hreceive
      contradiction
  have terminal : (d.source.histories route.history).getLast? = some input.1 := by
    rw [hist]
    change (first::rest).getLast? = some ((first::rest).getLastD first)
    rw [List.getLastD_eq_getLast?,List.getLast?_eq_some_getLast (by simp)]
    rfl
  exact ⟨histories,routes,first,rest,hhists,hroutes,hlist,hist,path,hframe,hreceive,endpoint_frame laws active _ input terminal⟩

end CSTTT.TargetTheory.GenericHandoff.ReceiverContent
