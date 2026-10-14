import CSTTT.FullNative02.FailureControls
import CSTTT.FullNative02.SelectorContinuations

namespace CSTTT.FullNative02.SelectorRegression
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

/-- Every operation is selected from the actual installed execution. -/
def firstFusion (w : World) (left right output : Nat) : Option World := do
  let request ← requestFor w left right output false false
  let entry ← (fusionRows renewable w request).head?
  pure entry.1.world

theorem first_fusion_history (w v : World) (left right output : Nat)
    (success : firstFusion w left right output=some v) (history : History renewable 8 .canonical32 w) :
    History renewable 8 .canonical32 v := by
  cases request : requestFor w left right output false false with
  | none => simp [firstFusion,request] at success
  | some q =>
    cases selected : (fusionRows renewable w q).head? with
    | none => simp [firstFusion,request,selected] at success
    | some entry =>
      have equal : entry.1.world=v := by simpa [firstFusion,request,selected] using success
      have supported : entry∈fusionRows renewable w q := by
        cases rows : fusionRows renewable w q with
        | nil => simp [rows] at selected
        | cons head tail =>
          have same : head=entry := by simpa only [rows,List.head?_cons,Option.some.injEq] using selected
          exact List.mem_cons.mpr (.inl same.symm)
      exact equal ▸ History.next history (.fusion supported)

def threeKeyRun : Option World := do
  let first ← firstFusion tokenZeroWorld 0 1 3
  let aligned ← chooseNative renewable first 3 false ⟨false,false,false,false,false⟩
  firstFusion aligned 3 2 4
theorem three_key_parent_supported : threeKeyRun.isSome=true := by decide +kernel
def threeKeyWorld : World := threeKeyRun.get three_key_parent_supported

theorem token_zero_world_history : History renewable 8 .canonical32 tokenZeroWorld := by
  have success : tokenZeroRun=some tokenZeroWorld := (Option.some_get token_zero_run_available).symm
  cases copied : bootstrap sourceWorld 0 1 2 with
  | none => simp [tokenZeroRun,copied] at success
  | some w =>
    cases left : runChoices renewable w 1 sixCycle with
    | none => simp [tokenZeroRun,copied,left] at success
    | some v =>
      exact run_choices_history _ _ _ _ _ _ _ (by simpa [tokenZeroRun,copied,left] using success)
        (run_choices_history _ _ _ _ _ _ _ left (bootstrap_history _ _ _ _ _ _ _ _ copied source_history))

theorem three_key_parent_history : History renewable 8 .canonical32 threeKeyWorld := by
  have success : threeKeyRun=some threeKeyWorld := (Option.some_get three_key_parent_supported).symm
  cases first : firstFusion tokenZeroWorld 0 1 3 with
  | none => simp [threeKeyRun,first] at success
  | some w =>
    cases aligned : chooseNative renewable w 3 false ⟨false,false,false,false,false⟩ with
    | none => simp [threeKeyRun,first,aligned] at success
    | some v =>
      exact first_fusion_history v threeKeyWorld 3 2 4
        (by simpa [threeKeyRun,first,aligned] using success)
        (.next (first_fusion_history _ _ _ _ _ first token_zero_world_history)
          (chosen_native_step _ _ _ _ _ _ aligned))

def acquire (xs ys : List Token) : Option World := do
  let divided ← partition threeKeyWorld 4 5 6 xs ys
  runChoices renewable divided 5 (cycleFrom true)
theorem both_selector_acquisitions_supported :
    (acquire [2,0] [1]).isSome=true ∧ (acquire [0,2] [1]).isSome=true := by decide +kernel
def unsortedWorld : World := (acquire [2,0] [1]).get both_selector_acquisitions_supported.1
def sortedWorld : World := (acquire [0,2] [1]).get both_selector_acquisitions_supported.2

theorem unsorted_selector_world_history : History renewable 8 .canonical32 unsortedWorld := by
  have success : acquire [2,0] [1]=some unsortedWorld := (Option.some_get both_selector_acquisitions_supported.1).symm
  cases divided : partition threeKeyWorld 4 5 6 [2,0] [1] with
  | none => simp [acquire,divided] at success
  | some v =>
    exact run_choices_history _ _ _ _ _ _ _
      (by simpa [acquire,divided] using success) (.next three_key_parent_history (.partition divided))

theorem unsorted_selector_world_accepted :
    keys threeKeyWorld.accounts 4=[0,1,2] ∧
    (access unsortedWorld 5).map (fun data => data.2.2)=some 0 ∧
    Epoch.accept unsortedWorld 5=true ∧ Epoch.accept sortedWorld 5=true := by decide +kernel

theorem selector_permutation_regression :
    Epoch.accept unsortedWorld 5=Epoch.accept sortedWorld 5 :=
  unsorted_selector_world_accepted.2.2.1.trans unsorted_selector_world_accepted.2.2.2.symm

theorem unsorted_selector_whole_package : Package.Whole unsortedWorld 5 :=
  Package.whole_package_from_installed_execution _ _ unsorted_selector_world_accepted.2.2.1

end CSTTT.FullNative02.SelectorRegression
