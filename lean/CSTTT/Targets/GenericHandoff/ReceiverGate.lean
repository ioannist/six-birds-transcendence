import CSTTT.Targets.GenericHandoff.ReceiverIntervention

/-! Owning receiver gate. All raw initializer/intervention syntax is fixed
before testing it. Laws inspect the same decoded endpoint, factor, initialized
actual frame and source-absence rerun. No candidate received class is supplied.
The latent and prepared-run equations are explicit checks, not consequences
claimed for arbitrary hidden receiver-cell fields. -/
namespace CSTTT.TargetTheory.GenericHandoff.ReceiverGate
open RegisterInterpreter RegisterInitialization
variable {SC Cell R SR TR S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint : Type}
  {SourceValue : SC → Type} {Value : Cell → Type} {RV : R → Type} {SRV : SR → Type} {TRV : TR → Type}
local notation "Model" => OwningHandoff.RawHandoff SC Cell SourceValue Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint
local notation "Input" => HistoricalAcquisition.ReceiverInput S H Id Route

structure Instructions (m : Model) where
  receiver : ReceiverContent.Instructions Cell TR S O H Id Route Value TRV
  erase : Value m.frames.receiver.cell → Value m.frames.receiver.cell

variable [DecidableEq Cell] [DecidableEq S] [DecidableEq O] [DecidableEq Route]
  [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner]

def withoutSource (m : Model) (r : Instructions m) (a : Assignment Cell Value) :=
  ReceiverIntervention.withoutSource m.frames.receiver r.erase a

structure ControlLaws (m : Model) (r : Instructions m) (a : Assignment Cell Value) : Prop where
  erasure : ReceiverIntervention.ErasureLaw m.frames.receiver r.erase
  latentSource : TemporalFactorCells.decoded m.frames.sourceCells (withoutSource m r a) =
    TemporalFactorCells.decoded m.frames.sourceCells a
  latentTarget : TemporalFactorCells.decoded m.frames.targetCells (withoutSource m r a) =
    TemporalFactorCells.decoded m.frames.targetCells a
  initialization : ∀ input k, evaluate r.receiver.resetProgram (withoutSource m r a) input k =
    evaluate r.receiver.resetProgram a input k
  targetReady : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target (withoutSource m r a) ↔
    TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target a
  prepared : ∀ (hi : RegisterInitialization.Ready r.receiver.resetProgram a)
    (ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target a)
    (hi' : RegisterInitialization.Ready r.receiver.resetProgram (withoutSource m r a))
    (ht' : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target (withoutSource m r a)) input,
    ReceiverContent.receivedRun m r.receiver (withoutSource m r a) hi' ht' input =
    ReceiverContent.receivedRun m r.receiver a hi ht input

def Subcheck (m : Model) (r : Instructions m) (a : Assignment Cell Value) : Prop :=
  ∃ hi : RegisterInitialization.Ready r.receiver.resetProgram a,
    ∃ hh : HistoricalAcquisition.Ready (ReceiverContent.acquisition m) a,
      ∃ ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target a,
        ∃ he : ExecutionLink.Ready (PublicRuntime.historicalLink (OwningHandoff.publicRuntime m)) a,
          ∃ d maps, ReceiverContent.Laws m r.receiver a hi hh ht he d maps ∧
            ControlLaws m r a ∧ AcquisitionEndpoint.active (OwningHandoff.endpoint m).schema d = true ∧
            ∃ x y : Input, FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) x.1 ≠
              FactorTransport.classOf m.frames.sourceSchema (PresentationCoherence.factor d.source) y.1

/-- Both before/after readouts rerun the identical raw receiver instruction. -/
def Readout (m : Model) (r : Instructions m) (a : Assignment Cell Value) : Prop :=
  ∃ hi : RegisterInitialization.Ready r.receiver.resetProgram a,
    ∃ ht : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target a,
      ReceiverContent.ContentFaithful m r.receiver a hi ht ∧
      ∃ hi' : RegisterInitialization.Ready r.receiver.resetProgram (withoutSource m r a),
        ∃ ht' : TemporalRuntimeCoherence.Ready (OwningHandoff.presentation m).target (withoutSource m r a),
          (∀ input, ReceiverContent.receivedRun m r.receiver (withoutSource m r a) hi' ht' input =
            ReceiverContent.receivedRun m r.receiver a hi ht input) ∧
          (∀ input, ReceiverContent.receive m r.receiver (withoutSource m r a) hi' ht' input = none ∧
            ReceiverContent.receivedClass m r.receiver (withoutSource m r a) hi' ht' input = none) ∧
          ¬ ReceiverContent.ContentFaithful m r.receiver (withoutSource m r a) hi' ht'

omit [DecidableEq Cell] in
theorem active_of_endpoint (m : Model) (a : Assignment Cell Value)
    (d : AcquisitionEndpoint.Data S A O HF Route Stage Id Owner)
    (hd : AcquisitionEndpoint.decoded (OwningHandoff.endpoint m).bindings a = some d)
    (h : AcquisitionEndpoint.Readout (OwningHandoff.endpoint m) a) :
    AcquisitionEndpoint.active (OwningHandoff.endpoint m).schema d = true := by
  obtain ⟨data,decoded,nonempty,allRoutes⟩ := h
  obtain ⟨rid,hrid⟩ := List.exists_mem_of_ne_nil _ nonempty
  obtain ⟨actual,route,state,hactual,_,received,_,_⟩ :=
    AcquisitionEndpoint.receiver_state _ _ a ⟨data,decoded,nonempty,allRoutes⟩ rid hrid
  have equal := Option.some.inj (hd.symm.trans hactual)
  subst actual
  unfold AcquisitionEndpoint.received at received
  split at received
  · assumption
  · contradiction

theorem soundness (m : Model) (r : Instructions m) (a : Assignment Cell Value)
    (hf : RuntimeLineage.FactorReadout (OwningHandoff.factor m) a) (h : Subcheck m r a) : Readout m r a := by
  obtain ⟨hi,hh,ht,he,d,maps,laws,controls,active,pair⟩ := h
  have hi' := (ReceiverIntervention.initial_ready_iff m.frames.receiver r.erase a r.receiver.resetProgram).mpr hi
  have ht' := controls.targetReady.mpr ht
  refine ⟨hi,ht,ReceiverContent.content_faithful laws hf active pair,hi',ht',?_,?_,?_⟩
  · exact controls.prepared hi ht hi' ht'
  · intro input
    exact ReceiverIntervention.no_reception m r.receiver r.erase controls.erasure a hi' ht' input
  · exact ReceiverIntervention.not_faithful m r.receiver r.erase controls.erasure a hi' ht'

theorem missing_endpoint_no_readout (m : Model) (r : Instructions m) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ (OwningHandoff.endpoint m).bindings.scope) (hm : a k = none) : ¬ Readout m r a := by
  rintro ⟨hi,ht,h,_⟩
  exact ReceiverContent.missing_endpoint_not_faithful (AcquisitionEndpoint.missing_input _ a k hk hm) h

end CSTTT.TargetTheory.GenericHandoff.ReceiverGate
