import CSTTT.Targets.GenericHandoff.ReceiverGate
import CSTTT.Targets.GenericHandoff.POS04NominalHandoff

namespace CSTTT.TargetTheory.GenericHandoff.POS04ReceiverGate
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH POS04ResourceRuntime
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def instructions (p : POS04ResourceRuntime.Protocol) : ReceiverGate.Instructions (POS04RawHandoff.raw p) :=
  ⟨POS04ReceiverContent.instructions,POS04ReceiverIntervention.erase⟩

theorem controls (p : POS04ResourceRuntime.Protocol) (a : CSTTT.POS04.Assigned.Assignment) :
    ReceiverGate.ControlLaws (POS04RawHandoff.raw p) (instructions p) a :=
  ⟨POS04ReceiverIntervention.erasure_law,POS04ReceiverIntervention.latent_factor a .source,
    POS04ReceiverIntervention.latent_factor a .target,POS04ReceiverIntervention.evaluation_unchanged a,
    POS04ReceiverIntervention.target_ready_iff p a,
    (fun hi ht hi' ht' input => POS04ReceiverIntervention.prepared_run_unchanged p a hi hi' ht ht' input)⟩

theorem target_pair (a : CSTTT.POS04.Assigned.Assignment) (h : C2Accept a .target) :
    FactorTransport.classOf (POS04TemporalFactor.schema .target) (POS04FactorTransport.data a .target) POS04ReceiverContent.inputA.1 ≠
      FactorTransport.classOf (POS04TemporalFactor.schema .target) (POS04FactorTransport.data a .target) POS04ReceiverContent.inputB.1 := by
  have hm := h.1.2
  have link := hm.2
  rw [hm.1] at link
  have hp : predictive (runInputs6 a .target).base.base = predictive (clauseInputs a .target .c2) := rfl
  rw [POS04FactorTransport.class_equation,POS04FactorTransport.class_equation,hp]
  intro equal
  have classes := (link POS04ReceiverContent.inputA.1 POS04ReceiverContent.inputB.1).mp equal
  change mClass 0 = mClass 2 at classes
  contradiction

theorem checked_of_package_lineage (m : RawLaneModel)
    (hp : DispatchedPackage.Valid (POS04RawHandoff.raw (protocol m)).package m.assignment)
    (hl : OwningHandoff.StrictTemporalLineage (POS04RawHandoff.raw (protocol m)) m.assignment) :
    ReceiverGate.Subcheck (POS04RawHandoff.raw (protocol m)) (instructions (protocol m)) (image m.assignment) := by
  have endpoint := hl.2
  rw [POS04RawHandoff.target_eq] at endpoint
  have hc : Assigned.Complete acquisitionDependencies (image m.assignment) := by
    obtain ⟨d,hd,_⟩ := endpoint
    exact (POS04AcquisitionEndpoint.decoded_complete_iff _).mp ⟨d,hd⟩
  have laws := POS04ReceiverContent.checked_from_inputs (protocol m) (image m.assignment) hc
  refine ⟨_,_,_,_,POS04AcquisitionEndpoint.data (image m.assignment),POS04FactorTransport.maps,laws,
    controls _ _,ReceiverGate.active_of_endpoint _ _ _ laws.decoded endpoint,?_,?_,?_⟩
  · exact POS04ReceiverContent.inputA
  · exact POS04ReceiverContent.inputB
  · have hf : RuntimeLineage.FactorReadout (OwningHandoff.factor (POS04RawHandoff.raw (protocol m))) (image m.assignment) := by
      have fields := hl.1.2.2.1
      rwa [POS04RawHandoff.target_eq] at fields
    have eqs := ReceiverContent.factor_equations laws hf
    have accepted := (DispatchedPackage.constructs _ _ hp).2.2 .c2
    change ((POS04Dispatcher.package .target).rule .c2).accept
      (DispatchedPackage.global POS04DispatchedStage.raw m.assignment) at accepted
    rw [POS04DispatchedStage.global_eq_image] at accepted
    have c2 : C2Accept (image m.assignment) .target :=
      (POS04Dispatcher.clause_accept_iff _ _ .c2).mp accepted
    have distinct := target_pair _ c2
    intro equal
    have targetEqual := (eqs.predictive POS04ReceiverContent.inputA.1).trans
      ((congrArg POS04FactorTransport.maps.predictive equal).trans (eqs.predictive POS04ReceiverContent.inputB.1).symm)
    exact distinct targetEqual

end CSTTT.TargetTheory.GenericHandoff.POS04ReceiverGate
