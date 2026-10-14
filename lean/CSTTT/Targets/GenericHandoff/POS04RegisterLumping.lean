import CSTTT.Targets.GenericHandoff.FutureLumpingTransport
import CSTTT.Targets.GenericHandoff.POS04FutureLumping

/-! Exact one-step runtime binding for arbitrary partial POS-04 assignments.
The generic execution frontier uses the same class-mass law as C6, not the
stronger, potentially rejecting branch-resolving bisimulation. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RegisterFuture
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TransportTheory RegisterInterpreter POS04RegisterDynamics

/-- Temporal readiness is not whole-clause readiness. The committed class-mass
proof does not use its extra completeness argument; derive it directly. -/
theorem actual_one_step (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hf : FiniteBisim6 (runInputs6 a tag)) : FutureLumping.OneStep (actualFuture6 a tag) := by
  intro x y hcode
  have hq := bisim6_all_states a tag hf x y hcode
  refine ⟨hq.1,?_⟩
  intro act
  constructor
  · intro o _
    exact ((actual_quotient_step6 _ tag x act o).1.trans
      (hq.2 act (predictive6 (runInputs6 a tag) o)).2).trans
        (actual_quotient_step6 _ tag y act o).1.symm
  · intro o ho
    change WeightedFibers.mass ambientStates (FutureLumping.NextCode (actualFuture6 a tag) x act)
      (actualWeight6 (runInputs6 a tag) x act) _ =
      WeightedFibers.mass ambientStates (FutureLumping.NextCode (actualFuture6 a tag) x act)
      (actualWeight6 (runInputs6 a tag) y act) _
    rw [POS04FutureLumping.next_code_fiber,POS04FutureLumping.next_code_fiber]
    exact (hq.2 act (predictive6 (runInputs6 a tag) o)).1

theorem one_step (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (hf : FiniteBisim6 (runInputs6 a tag)) :
    FutureLumping.OneStep (Model a tag hc) := by
  apply FutureLumping.transport_one_step (actualFuture6 a tag) (Model a tag hc)
    decodeRun Prod.snd c6CodeToBridge c6ObservationToBridge
    (fun _ _ h => c6_code_to_bridge_injective _ _ h) rfl
  · intro x; simpa only [encode_decode] using code_eq a tag hc (decodeRun x)
  · intro x; simpa only [encode_decode] using observation_eq a tag hc (decodeRun x)
  · intro x da o; simpa only [encode_decode] using weight_eq a tag hc (decodeRun x) da.1 da.2 o
  · intro x da o; simpa only [encode_decode,decode_encode] using
      congrArg decodeRun (next_eq a tag hc (decodeRun x) da.1 da.2 o)
  · exact actual_one_step a tag hf
end CSTTT.TargetTheory.GenericHandoff.POS04RegisterFuture
