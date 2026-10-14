import CSTTT.Targets.GenericHandoff.ReceiverIntervention
import CSTTT.Targets.GenericHandoff.DispatchedComposition

/-! Actual receiver sequencing in a common typed coordinate interface. The
second input is constructed from the first returned factor, full past and
path, plus raw namespace maps. This component does not assert that arbitrary
deliveries belong to the next supported acquisition domain or that two
receiver ports form a full temporal handoff. -/
namespace CSTTT.TargetTheory.GenericHandoff.ReceiverSequence
open RegisterInterpreter RegisterInitialization
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

variable {Cell R SR TR S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint : Type}
  {Value : Cell → Type} {RV : R → Type} {SRV : SR → Type} {TRV : TR → Type}
local notation "Model" => OwningHandoff.RawHandoff Cell Cell Value Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint
local notation "Recipe" => ReceiverContent.Instructions Cell TR S O H Id Route Value TRV
local notation "Input" => HistoricalAcquisition.ReceiverInput S H Id Route

structure Delivery (Cell : Type) (Value : Cell → Type) (S A Owner H Id Route : Type) where
  maps : StaticView Cell Value (FactorTransport.Maps S S A A Owner)
  event : Id → Id
  history : H → H
  route : Route → Route

variable [DecidableEq Cell] [DecidableEq S] [DecidableEq O] [DecidableEq Route]
  [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner]

/-- No cached state/class is delivered: decode the ACTUAL first returned
factor, then map its ACTUAL returned past/path. Missing raw maps reject. -/
def deliver (left : Model) (transport : Delivery Cell Value S A Owner H Id Route)
    (a : Assignment Cell Value) (original : Input) (run : TemporalFactorRules.Run O S Id) : Option Input := do
  let maps ← transport.maps.read a
  let terminal ← left.frames.targetSchema.base.destination run.factor
  pure (maps.state terminal,run.residue.1.map maps.state,run.residue.2.map transport.event,
    transport.history original.2.2.2.1,transport.route original.2.2.2.2)

noncomputable def receiveAt (left right : Model) (first second : Recipe)
    (transport : Delivery Cell Value S A Owner H Id Route) (a b : Assignment Cell Value)
    (hi : RegisterInitialization.Ready first.resetProgram a)
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation left).target a)
    (hj : RegisterInitialization.Ready second.resetProgram b)
    (hu : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation right).target b)
    (input : Input) : Option (TemporalFactorRules.Run O S Id) := do
  let actual ← ReceiverContent.receive left first a hi ht input
  let next ← deliver left transport a input actual
  ReceiverContent.receive right second b hj hu next

noncomputable def classAt (left right : Model) (first second : Recipe)
    (transport : Delivery Cell Value S A Owner H Id Route) (a b : Assignment Cell Value)
    (hi : RegisterInitialization.Ready first.resetProgram a)
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation left).target a)
    (hj : RegisterInitialization.Ready second.resetProgram b)
    (hu : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation right).target b)
    (input : Input) : Option FactorTransport.Predictive := do
  let data ← AcquisitionEndpoint.decoded (OwningHandoff.endpoint right).bindings b
  let run ← receiveAt left right first second transport a b hi ht hj hu input
  let terminal ← right.frames.targetSchema.base.destination run.factor
  pure (FactorTransport.classOf right.frames.targetSchema (PresentationCoherence.factor data.target) terminal)

/-- Public pipeline assignments are the two actual stage/cover globals. -/
def leftCells (left : Model) (a : Assignment Cell Value) := OwningHandoff.target left a
def rightCells (left right : Model) (a : Assignment Cell Value) :=
  OwningHandoff.target right (leftCells left a)

noncomputable def receive (left right : Model) (first second : Recipe)
    (transport : Delivery Cell Value S A Owner H Id Route) (a : Assignment Cell Value)
    (hi : RegisterInitialization.Ready first.resetProgram (leftCells left a))
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation left).target (leftCells left a))
    (hj : RegisterInitialization.Ready second.resetProgram (rightCells left right a))
    (hu : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation right).target (rightCells left right a))
    (input : Input) :=
  receiveAt left right first second transport (leftCells left a) (rightCells left right a) hi ht hj hu input

noncomputable def receivedClass (left right : Model) (first second : Recipe)
    (transport : Delivery Cell Value S A Owner H Id Route) (a : Assignment Cell Value)
    (hi : RegisterInitialization.Ready first.resetProgram (leftCells left a))
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation left).target (leftCells left a))
    (hj : RegisterInitialization.Ready second.resetProgram (rightCells left right a))
    (hu : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation right).target (rightCells left right a))
    (input : Input) :=
  classAt left right first second transport (leftCells left a) (rightCells left right a) hi ht hj hu input

variable (left right : OwningHandoff.RawHandoff Cell Cell Value Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint)
    (first second : ReceiverContent.Instructions Cell TR S O H Id Route Value TRV)
    (transport : Delivery Cell Value S A Owner H Id Route) (a b : Assignment Cell Value)
    (hi : RegisterInitialization.Ready first.resetProgram a)
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation left).target a)
    (hj : RegisterInitialization.Ready second.resetProgram b)
    (hu : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation right).target b)

omit [DecidableEq Cell] [DecidableEq S] [DecidableEq O] [DecidableEq Route] [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner] in
theorem missing_maps (input : Input) (run : TemporalFactorRules.Run O S Id)
    (h : transport.maps.read a = none) : deliver left transport a input run = none := by
  simp [deliver,h]

omit [DecidableEq Cell] [DecidableEq S] [DecidableEq O] [DecidableEq Route] [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner] in
theorem undecodable_first_factor (input : Input) (run : TemporalFactorRules.Run O S Id)
    (h : left.frames.targetSchema.base.destination run.factor = none) :
    deliver left transport a input run = none := by
  cases hm : transport.maps.read a <;> simp [deliver,hm,h]

omit [DecidableEq Cell] in
theorem first_none (input : Input) (h : ReceiverContent.receive left first a hi ht input = none) :
    receiveAt left right first second transport a b hi ht hj hu input = none := by
  simp [receiveAt,h]

omit [DecidableEq Cell] in
theorem missing_maps_receive (input : Input) (h : transport.maps.read a = none) :
    receiveAt left right first second transport a b hi ht hj hu input = none := by
  cases hr : ReceiverContent.receive left first a hi ht input <;> simp [receiveAt,hr,deliver,h]

omit [DecidableEq Cell] in
theorem receive_none_class_none (input : Input)
    (h : receiveAt left right first second transport a b hi ht hj hu input = none) :
    classAt left right first second transport a b hi ht hj hu input = none := by
  cases hd : AcquisitionEndpoint.decoded (OwningHandoff.endpoint right).bindings b <;> simp [classAt,hd,h]

omit [DecidableEq Cell] in
theorem missing_right_endpoint (input : Input)
    (h : AcquisitionEndpoint.decoded (OwningHandoff.endpoint right).bindings b = none) :
    classAt left right first second transport a b hi ht hj hu input = none := by simp [classAt,h]

omit [DecidableEq Cell] in
/-- Classification is of the actual second receive, after actual delivery. -/
theorem class_sequence (input : Input) :
    classAt left right first second transport a b hi ht hj hu input =
      (ReceiverContent.receive left first a hi ht input).bind (fun run =>
        (deliver left transport a input run).bind (ReceiverContent.receivedClass right second b hj hu)) := by
  cases hd : AcquisitionEndpoint.decoded (OwningHandoff.endpoint right).bindings b
  all_goals cases hl : ReceiverContent.receive left first a hi ht input
  all_goals try simp [classAt,receiveAt,hd,hl,Option.bind_assoc]
  case none.some actual =>
    cases hm : deliver left transport a input actual <;>
      simp [ReceiverContent.receivedClass,hd]
  case some.some data actual =>
    cases hm : deliver left transport a input actual <;>
      simp [ReceiverContent.receivedClass,hd]

omit [DecidableEq Cell] in
theorem source_absent (input : Input) (data : AcquisitionEndpoint.Data S A O HF Route Stage Id Owner)
    (hd : AcquisitionEndpoint.decoded (OwningHandoff.endpoint left).bindings a = some data)
    (h : data.receiver.sourcePresent = false) :
    receiveAt left right first second transport a b hi ht hj hu input = none ∧
      classAt left right first second transport a b hi ht hj hu input = none := by
  have hn := first_none left right first second transport a b hi ht hj hu input
    (ReceiverContent.source_absent hd h input)
  exact ⟨hn,receive_none_class_none left right first second transport a b hi ht hj hu input hn⟩

/-- Original stage/cover construction binds both receiver assignments. -/
theorem shared_final_target (original : Assignment Cell Value) :
    rightCells left right original =
      DispatchedPackage.global (DispatchedComposition.compose left.package right.package) original :=
  (DispatchedComposition.target_equation left.package right.package original).symm

/-- Evidence concerns actual decoders, reset programs, factor tables and
activation. No desired composite class preservation is a field. -/
def Checked : Prop :=
  ∃ hh : HistoricalAcquisition.Ready (ReceiverContent.acquisition left) a,
    ∃ he : ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime left)) a,
      ∃ hk : HistoricalAcquisition.Ready (ReceiverContent.acquisition right) b,
        ∃ hf : ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime right)) b,
          ∃ dl dr lm rm middle,
            ReceiverContent.Laws left first a hi hh ht he dl lm ∧
            ReceiverContent.Laws right second b hj hk hu hf dr rm ∧
            RuntimeLineage.FactorReadout (OwningHandoff.factor left) a ∧
            RuntimeLineage.FactorReadout (OwningHandoff.factor right) b ∧
            transport.maps.read a = some middle ∧
            FactorTransport.Equations left.frames.targetSchema right.frames.sourceSchema
              (PresentationCoherence.factor dl.target) (PresentationCoherence.factor dr.source) middle ∧
            AcquisitionEndpoint.active (OwningHandoff.endpoint left).schema dl = true ∧
            AcquisitionEndpoint.active (OwningHandoff.endpoint right).schema dr = true ∧
            ∃ x y : Input, FactorTransport.classOf left.frames.sourceSchema (PresentationCoherence.factor dl.source) x.1 ≠
              FactorTransport.classOf left.frames.sourceSchema (PresentationCoherence.factor dl.source) y.1

def ContentFaithful : Prop :=
  ∃ dl, AcquisitionEndpoint.decoded (OwningHandoff.endpoint left).bindings a = some dl ∧
    (∃ x y : Input, FactorTransport.classOf left.frames.sourceSchema (PresentationCoherence.factor dl.source) x.1 ≠
      FactorTransport.classOf left.frames.sourceSchema (PresentationCoherence.factor dl.source) y.1) ∧
    (∀ input : Input, ∃ cls, classAt left right first second transport a b hi ht hj hu input = some cls) ∧
    ∀ x y : Input, FactorTransport.classOf left.frames.sourceSchema (PresentationCoherence.factor dl.source) x.1 ≠
      FactorTransport.classOf left.frames.sourceSchema (PresentationCoherence.factor dl.source) y.1 →
      classAt left right first second transport a b hi ht hj hu x ≠
        classAt left right first second transport a b hi ht hj hu y

omit [DecidableEq Cell] in
theorem none_classes_not_faithful
    (h : ∀ input : Input, classAt left right first second transport a b hi ht hj hu input = none) :
    ¬ ContentFaithful left right first second transport a b hi ht hj hu := by
  rintro ⟨data,decoded,⟨x,y,distinct⟩,total,faithful⟩
  obtain ⟨cls,hcls⟩ := total x
  rw [h x] at hcls
  contradiction

omit [DecidableEq Cell] [DecidableEq S] [DecidableEq O] [DecidableEq Route] [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner] in
theorem deliver_equation (input : Input) (run : TemporalFactorRules.Run O S Id)
    (maps : FactorTransport.Maps S S A A Owner) (terminal : S)
    (hm : transport.maps.read a = some maps)
    (hs : left.frames.targetSchema.base.destination run.factor = some terminal) :
    deliver left transport a input run = some
      (maps.state terminal,run.residue.1.map maps.state,run.residue.2.map transport.event,
        transport.history input.2.2.2.1,transport.route input.2.2.2.2) := by
  simp [deliver,hm,hs]

omit [DecidableEq Cell] in
theorem first_run
    (hh : HistoricalAcquisition.Ready (ReceiverContent.acquisition left) a)
    (he : ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime left)) a)
    (dl : AcquisitionEndpoint.Data S A O HF Route Stage Id Owner)
    (lm : FactorTransport.Maps S S A A Owner)
    (hl : ReceiverContent.Laws left first a hi hh ht he dl lm)
    (hal : AcquisitionEndpoint.active (OwningHandoff.endpoint left).schema dl = true)
    (input : Input) :
    ReceiverContent.receive left first a hi ht input = some
      ⟨first.outcome (lm.state input.1),0,0,(input.2.1,input.2.2.1),dl.receiver.funded⟩ := by
  simpa [ReceiverContent.receive,hl.decoded,hal] using congrArg some (ReceiverContent.received_run hl input)

omit [DecidableEq Cell] in
theorem actual_receive
    (hh : HistoricalAcquisition.Ready (ReceiverContent.acquisition left) a)
    (he : ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime left)) a)
    (hk : HistoricalAcquisition.Ready (ReceiverContent.acquisition right) b)
    (hf : ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime right)) b)
    (dl dr : AcquisitionEndpoint.Data S A O HF Route Stage Id Owner)
    (lm rm middle : FactorTransport.Maps S S A A Owner)
    (hl : ReceiverContent.Laws left first a hi hh ht he dl lm)
    (hr : ReceiverContent.Laws right second b hj hk hu hf dr rm)
    (hm : transport.maps.read a = some middle)
    (hal : AcquisitionEndpoint.active (OwningHandoff.endpoint left).schema dl = true)
    (har : AcquisitionEndpoint.active (OwningHandoff.endpoint right).schema dr = true)
    (input : Input) :
    receiveAt left right first second transport a b hi ht hj hu input = some
      ⟨second.outcome (rm.state (middle.state (lm.state input.1))),0,0,
        (input.2.1.map middle.state,input.2.2.1.map transport.event),dr.receiver.funded⟩ := by
  have hlr := first_run left first a hi ht hh he dl lm hl hal input
  let next : Input := (middle.state (lm.state input.1),input.2.1.map middle.state,
    input.2.2.1.map transport.event,transport.history input.2.2.2.1,transport.route input.2.2.2.2)
  simpa [receiveAt,hlr,deliver,hm,hl.outcome,next] using first_run right second b hj hu hk hf dr rm hr har next

omit [DecidableEq Cell] in
theorem actual_class
    (hh : HistoricalAcquisition.Ready (ReceiverContent.acquisition left) a)
    (he : ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime left)) a)
    (hk : HistoricalAcquisition.Ready (ReceiverContent.acquisition right) b)
    (hf : ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime right)) b)
    (dl dr : AcquisitionEndpoint.Data S A O HF Route Stage Id Owner)
    (lm rm middle : FactorTransport.Maps S S A A Owner)
    (hl : ReceiverContent.Laws left first a hi hh ht he dl lm)
    (hr : ReceiverContent.Laws right second b hj hk hu hf dr rm)
    (hm : transport.maps.read a = some middle)
    (hal : AcquisitionEndpoint.active (OwningHandoff.endpoint left).schema dl = true)
    (har : AcquisitionEndpoint.active (OwningHandoff.endpoint right).schema dr = true)
    (input : Input) :
    classAt left right first second transport a b hi ht hj hu input = some
      (FactorTransport.classOf right.frames.targetSchema (PresentationCoherence.factor dr.target)
        (rm.state (middle.state (lm.state input.1)))) := by
  have hlr : ReceiverContent.receive left first a hi ht input = some
      ⟨first.outcome (lm.state input.1),0,0,(input.2.1,input.2.2.1),dl.receiver.funded⟩ := by
    exact first_run left first a hi ht hh he dl lm hl hal input
  rw [class_sequence,hlr]
  simp only [Option.bind_some,deliver,hm,hl.outcome]
  exact ReceiverContent.active_class hr har _

omit [DecidableEq Cell] in
theorem content_soundness
    (h : Checked left right first second transport a b hi ht hj hu) :
    ContentFaithful left right first second transport a b hi ht hj hu := by
  obtain ⟨hh,he,hk,hf,dl,dr,lm,rm,middle,hl,hr,hfl,hfr,hm,eqm,hal,har,pair⟩ := h
  have eql := ReceiverContent.factor_equations hl hfl
  have eqr := ReceiverContent.factor_equations hr hfr
  have value := actual_class left right first second transport a b hi ht hj hu hh he hk hf dl dr lm rm middle hl hr hm hal har
  refine ⟨dl,hl.decoded,pair,(fun input => ⟨_,value input⟩),?_⟩
  intro x y distinct same
  rw [value x,value y] at same
  have hlast := Option.some.inj same
  rw [eqr.predictive,eqr.predictive] at hlast
  have hmiddle := eqr.classInjective _ _ hlast
  rw [eqm.predictive,eqm.predictive] at hmiddle
  have hfirst := eqm.classInjective _ _ hmiddle
  rw [eql.predictive,eql.predictive] at hfirst
  exact distinct (eql.classInjective _ _ hfirst)

theorem source_erasure
    (erase : Value left.frames.receiver.cell → Value left.frames.receiver.cell)
    (law : ReceiverIntervention.ErasureLaw left.frames.receiver erase)
    (hi' : RegisterInitialization.Ready first.resetProgram (ReceiverIntervention.withoutSource left.frames.receiver erase a))
    (ht' : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation left).target
      (ReceiverIntervention.withoutSource left.frames.receiver erase a)) (input : Input) :
    receiveAt left right first second transport (ReceiverIntervention.withoutSource left.frames.receiver erase a)
      b hi' ht' hj hu input = none ∧
    classAt left right first second transport (ReceiverIntervention.withoutSource left.frames.receiver erase a)
      b hi' ht' hj hu input = none := by
  have hn := first_none left right first second transport _ b hi' ht' hj hu input
    (ReceiverIntervention.no_reception left first erase law a hi' ht' input).1
  exact ⟨hn,receive_none_class_none left right first second transport _ b hi' ht' hj hu input hn⟩

theorem source_erasure_not_faithful
    (erase : Value left.frames.receiver.cell → Value left.frames.receiver.cell)
    (law : ReceiverIntervention.ErasureLaw left.frames.receiver erase)
    (hi' : RegisterInitialization.Ready first.resetProgram (ReceiverIntervention.withoutSource left.frames.receiver erase a))
    (ht' : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation left).target
      (ReceiverIntervention.withoutSource left.frames.receiver erase a)) :
    ¬ ContentFaithful left right first second transport (ReceiverIntervention.withoutSource left.frames.receiver erase a)
      b hi' ht' hj hu := by
  apply none_classes_not_faithful
  intro input
  exact (source_erasure left right first second transport a b hj hu erase law hi' ht' input).2

/-- Public content conclusion quantifies readiness on the constructed globals.
It supplies no independently chosen intermediate or final assignment. -/
def ContentReadout (left right : Model) (first second : Recipe)
    (transport : Delivery Cell Value S A Owner H Id Route) (original : Assignment Cell Value) : Prop :=
  ∃ hi : RegisterInitialization.Ready first.resetProgram (leftCells left original),
    ∃ ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation left).target (leftCells left original),
      ∃ hj : RegisterInitialization.Ready second.resetProgram (rightCells left right original),
        ∃ hu : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation right).target (rightCells left right original),
          ContentFaithful left right first second transport (leftCells left original) (rightCells left right original) hi ht hj hu

end CSTTT.TargetTheory.GenericHandoff.ReceiverSequence
