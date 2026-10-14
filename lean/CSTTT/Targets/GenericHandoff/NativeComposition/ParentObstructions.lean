import CSTTT.Targets.GenericHandoff.AcquisitionEndpoint
import CSTTT.Targets.GenericHandoff.NativeComposition.NativeControls
import CSTTT.Targets.GenericHandoff.NativeComposition.ClockScout

/-! Direct counterexamples adjudicate the three old-parent requirements that
cannot represent this native episode. The original requirements are preserved. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ParentObstructions
open ModeExecution

theorem physical_clock_not_stage_index : clock 2 2 ≠ stages.idxOf := by
  intro he
  have hz := congrFun he (0 : Stage)
  change 2=0 at hz
  contradiction

theorem source_presence_not_static (value : Option Bool) :
    ¬ ∀ x : ModeExecution.Registers, finalResources.sourcePresent.eval nativeAssignment x ()=value := by
  intro he
  have hs := he (snapshot (false,false,false) 8 6 true)
  have ht := he (snapshot (false,false,false) 8 6 false)
  change some true=value at hs
  change some false=value at ht
  have bad : (some true : Option Bool)=some false := hs.trans ht.symm
  contradiction

def identityEndpoint : AcquisitionEndpoint.Schema Factor Bool Factor History Route Stage Bool Owner :=
  ⟨factorSchema false,factorSchema true,0,2,true,(false,false,false),1,id⟩
def actualEndpointData : AcquisitionEndpoint.Data Factor Bool Factor History Route Stage Bool Owner :=
  ⟨(roundInput 0).temporal,(roundInput 1).temporal,
    [⟨false,0,1,true,true,true,true⟩,⟨true,1,2,true,true,false,true⟩],⟨true,true,true,true⟩⟩

theorem identity_endpoint_rejects_actual_publication (h : Factor) :
    AcquisitionEndpoint.atRoute identityEndpoint actualEndpointData h=false := by
  rcases h with ⟨phase,visible,hidden⟩
  cases phase <;> cases visible <;> cases hidden <;> decide +kernel

theorem fixed_history_replay_unsupported_after_zero_weight_successor :
    ¬ StrategyGame.PositiveSupport (AcquisitionExecution.rows firstAcquisition nativeAssignment)
      (snapshot (false,false,true) 2 1 false) () false (false,false,false) := by
  rw [episode_positive_unique true false 0 1 nativeAssignment 0 rfl]
  simp [snapshot,pack,destination]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ParentObstructions
