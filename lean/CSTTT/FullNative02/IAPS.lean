import CSTTT.FullNative02.ContextTransport
import CSTTT.FullNative02.BlockControls

namespace CSTTT.FullNative02.IAPS
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

inductive Request where
  | child (right : Bool) (continuation : List State)
  | output (meetingState : State) (continuation : List State)
  deriving DecidableEq, Repr
def owner : Request → Nat
  | .child right _ => if right then 2 else 1
  | .output _ _ => 3
def selectedFusion (state : State) : Option World :=
  ((fusionRows renewable branchesWorld mainRequest).find? fun e =>
    decide ((e.1.world.residents 3).map Resident.current=some state)).map fun e => e.1.world
def execute : Request → Option World
  | .child right continuation => runChoices renewable branchesWorld (if right then 2 else 1) continuation
  | .output state continuation => do
    let cold ← selectedFusion state
    let acquired ← outputWarmup cold
    runChoices renewable acquired 3 continuation
def Valid (request : Request) : Prop := (execute request).isSome=true
def Ancestry (request : Request) : Prop := ∀ w,execute request=some w→Predictive w (owner request)
def PackageRealized (request : Request) : Prop := ∀ w,execute request=some w→Package.Whole w (owner request)
def Autonomous (request : Request) : Prop := ∀ w,execute request=some w→Autonomy.Realized (owner request) w

theorem selected_is_actual (state : State) (w : World) (h : selectedFusion state=some w) :
    ∃ e,e∈fusionRows renewable branchesWorld mainRequest ∧ e.1.world=w := by
  cases selected : (fusionRows renewable branchesWorld mainRequest).find? (fun e =>
      decide ((e.1.world.residents 3).map Resident.current=some state)) with
  | none => simp only [selectedFusion,selected,Option.map_none] at h; cases h
  | some e =>
    have world : e.1.world=w := by simpa only [selectedFusion,selected,Option.map_some,Option.some.injEq] using h
    exact ⟨e,List.mem_of_find?_eq_some selected,world⟩

theorem successful_request_three_lanes (request : Request) (w : World) (success : execute request=some w) :
    Predictive w (owner request) ∧ Package.Whole w (owner request) ∧ Autonomy.Realized (owner request) w := by
  have finish (start w : World) (owner : Nat) (continuation : List State)
      (accepted : Package.Accept02 start owner=true) (withdrawn : Withdrawn start)
      (ancestral : SourceOwned start owner) (success : runChoices renewable start owner continuation=some w) :
      Predictive w owner ∧ Package.Whole w owner ∧ Autonomy.Realized owner w := by
    have path := run_choices_retained start w owner continuation success
    have package := retained_acceptance _ _ _ accepted path
    exact ⟨predictive_from_same_execution _ _ (retained_source_owned _ _ _ ancestral path),
      Package.whole_package_from_installed_execution _ _ package,
      Autonomy.actual_package_preserving_target_autonomy _ _ package (retained_withdrawal _ _ _ withdrawn path)⟩
  cases request with
  | child right continuation =>
    cases right
    · exact finish branchesWorld w 1 continuation both_withdrawn_children_accept.1 withdrawn_branches
        both_children_source_owned.1 success
    · exact finish branchesWorld w 2 continuation both_withdrawn_children_accept.2 withdrawn_branches
        both_children_source_owned.2 success
  | output state continuation =>
    cases selected : selectedFusion state with
    | none => simp [execute,selected] at success
    | some cold =>
      obtain ⟨e,member,equal⟩ := selected_is_actual state cold selected
      cases equal
      cases acquired : outputWarmup e.1.world with
      | none => simp [execute,selected,acquired] at success
      | some ready =>
        have readyMember : ready∈(outputWarmup e.1.world).toList := by simp [acquired]
        exact finish ready w 3 continuation
          (every_acquired_output_accepts e member ready readyMember)
          (withdrawn_all_acquired_outputs e member ready readyMember)
          (every_warm_output_source_owned e member ready acquired)
          (by simpa [execute,selected,acquired] using success)

/-- The unchanged original formula. Validity is computed request success,
and each lane is returned from that same execution, not supplied witnesses. -/
theorem original_integrated_temporal_iaps :
    Prospects.IntegratedTemporalIAPS Request Valid Ancestry PackageRealized Autonomous := by
  intro request _
  exact ⟨fun w success => (successful_request_three_lanes request w success).1,
    fun w success => (successful_request_three_lanes request w success).2.1,
    fun w success => (successful_request_three_lanes request w success).2.2⟩

theorem both_child_requests_valid : Valid (.child false []) ∧ Valid (.child true []) := by
  unfold Valid
  decide +kernel
theorem acquired_output_request_valid : Valid (.output ⟨false,false,false,false,true⟩ []) := by
  unfold Valid
  decide +kernel
theorem every_actual_output_has_valid_request :
    ∀ e∈fusionRows renewable branchesWorld mainRequest,
      (e.1.world.residents 3).map (fun r => (execute (.output r.current [])).isSome)=some true := by
  decide +kernel
theorem all_actual_outputs_three_lanes (e : Settlement × Rat)
    (member : e∈fusionRows renewable branchesWorld mainRequest) (ready w : World)
    (acquired : outputWarmup e.1.world=some ready) (continuation : Retained 3 ready w) :
    Predictive w 3 ∧ Package.Whole w 3 ∧ Autonomy.Realized 3 w := by
  have readyMember : ready∈(outputWarmup e.1.world).toList := by simp [acquired]
  have accepted := retained_acceptance 3 ready w
    (every_acquired_output_accepts e member ready readyMember) continuation
  exact ⟨predictive_from_same_execution w 3 (retained_source_owned 3 ready w
      (every_warm_output_source_owned e member ready acquired) continuation),
    Package.whole_package_from_installed_execution w 3 accepted,
    Autonomy.actual_package_preserving_target_autonomy 3 w accepted
      (retained_withdrawal 3 ready w (withdrawn_all_acquired_outputs e member ready readyMember) continuation)⟩
theorem earlier_source_whole_package : Package.Whole sourceWorld 0 :=
  Package.whole_package_from_installed_execution _ _ source_checkpoint_accepts

end CSTTT.FullNative02.IAPS
