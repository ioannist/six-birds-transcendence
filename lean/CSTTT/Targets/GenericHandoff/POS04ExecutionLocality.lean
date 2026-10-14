import CSTTT.Targets.GenericHandoff.ExecutionLocality
import CSTTT.Targets.GenericHandoff.POS04SemanticExecution
import CSTTT.Targets.GenericHandoff.POS04RouteReadout

/-! Isolation of the registered C1 deletion. This proves raw instruction
locality, not independence inferred from a failed sufficient gate. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ExecutionLocality
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open RegisterInterpreter POS04RegisterDynamics CSTTT.TargetTheory.ComputedFIACH
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def frame : Tag → ExecutionFrontier.Raw Cell Value Register RegisterValue LaneDisturbance Action Ambient
    CSTTT.POS04.PredictiveNow (List KState × List EventId) Bool CSTTT.POS04.Stage EventId RouteId RouteId
  | .source => POS04ExecutionFrontier.raw
  | .target => POS04ReceiverFrontier.raw

/-- The proof covers EVERY raw read, initializer, updater, receiver and
independent recipe. It is not merely equality of the audit displays. -/
theorem agreement {a b : CSTTT.POS04.Assigned.Assignment}
    (h : ∀ k, k ≠ .publishedC → a k = b k) (t : Tag) :
    ExecutionLocality.Agreement (frame t) a b := by
  have sub : ∀ (xs : List Cell), Cell.publishedC ∉ xs →
      GenericHandoff.Agrees xs a b := by
    intro xs hn k hk
    apply h k
    intro he; subst k; exact hn hk
  refine ⟨⟨?_,?_,?_⟩,?_,?_,?_,?_⟩
  · apply sub; cases t <;> decide +kernel
  · intro r; apply sub; cases t <;> cases r <;> decide +kernel
  · apply sub; cases t <;> decide +kernel
  · apply sub; cases t <;> decide +kernel
  · intro r; apply sub; cases t <;> cases r <;> decide +kernel
  · intro r; apply sub; cases t <;> cases r <;> decide +kernel
  · intro f; apply sub; cases t <;> cases f <;> decide +kernel

theorem semantic_transfer {a b : CSTTT.POS04.Assigned.Assignment}
    (h : ∀ k, k ≠ .publishedC → a k = b k) (t : Tag)
    (hv : ExecutionFrontier.SemanticReadout (frame t) a) :
    ExecutionFrontier.SemanticReadout (frame t) b :=
  ExecutionLocality.semantic_transfer _ (agreement h t) hv

theorem package_control_unchanged (k : Cell) (hk : k ≠ .publishedC) :
    canonical k = image packageDeletion.assignment k := by
  have he : image packageDeletion.assignment k = image canonical k := by
    cases k with
    | rows t => cases t <;> rfl
    | lower t => cases t <;> rfl
    | protocols t => cases t <;> rfl
    | ticks t => cases t <;> rfl
    | joint t => cases t <;> rfl
    | resources t => cases t <;> rfl
    | publishedC => exact False.elim (hk rfl)
    | _ => rfl
  rw [he,image_canonical]

theorem package_control_source : ExecutionFrontier.SemanticReadout
    POS04ExecutionFrontier.raw (image packageDeletion.assignment) :=
  semantic_transfer package_control_unchanged .source POS04SemanticExecution.positive.1

theorem package_control_target : ExecutionFrontier.SemanticReadout
    POS04ReceiverFrontier.raw (image packageDeletion.assignment) :=
  semantic_transfer package_control_unchanged .target POS04SemanticExecution.positive.2.1

theorem inputs_unchanged (t : Tag) :
    runInputs6 (image packageDeletion.assignment) t = runInputs6 canonical t := by
  cases t <;> rfl

theorem initial_unchanged (t : Tag) (r : RouteId) :
    acquisitionInitialRun (image packageDeletion.assignment) t r = acquisitionInitialRun canonical t r := by
  cases t <;> rfl

theorem dynamics_unchanged : POS04SemanticExecution.dynamics (image packageDeletion.assignment) =
    POS04SemanticExecution.dynamics canonical := by
  unfold POS04SemanticExecution.dynamics
  rw [inputs_unchanged]

theorem roots_unchanged : POS04SemanticExecution.roots (image packageDeletion.assignment) =
    POS04SemanticExecution.roots canonical := by
  unfold POS04SemanticExecution.roots
  simp only [initial_unchanged]

theorem closure_unchanged (x : Run6) : POS04SemanticExecution.Closure (image packageDeletion.assignment) x ↔
    POS04SemanticExecution.Closure canonical x := by
  simp only [POS04SemanticExecution.Closure,dynamics_unchanged,roots_unchanged]

theorem package_control_transport : POS04SemanticExecution.TransportLaws (image packageDeletion.assignment) := by
  obtain ⟨hw,hi,hr,hn,ho⟩ := POS04SemanticExecution.canonical_transport
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact hw
  · intro r; rw [initial_unchanged,initial_unchanged]; exact hi r
  · intro x hx act o; rw [inputs_unchanged,inputs_unchanged]
    exact hr x ((closure_unchanged x).mp hx) act o
  · intro x hx act ha o hout; rw [inputs_unchanged,inputs_unchanged]
    exact hn x ((closure_unchanged x).mp hx) act ha o hout
  · intro x hx; rw [inputs_unchanged,inputs_unchanged]
    exact ho x ((closure_unchanged x).mp hx)

theorem package_control_bridge : ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw
    (image packageDeletion.assignment) :=
  (POS04SemanticExecution.semantic_bridge_iff _).mpr
    ⟨package_control_source,package_control_target,package_control_transport⟩

theorem source_fold_unchanged (x : Run6) (word : List (LaneDisturbance × Action × Ambient)) :
    POS04ExecutedCorridor.actualFold (image packageDeletion.assignment) x word =
      POS04ExecutedCorridor.actualFold canonical x word := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    simp only [POS04ExecutedCorridor.actualFold,inputs_unchanged,ih]

theorem route_fold_unchanged (t : Tag) (x : Run6) (word : List StepEnv) :
    POS04RouteExecution.actualFold (image packageDeletion.assignment) t x word =
      POS04RouteExecution.actualFold canonical t x word := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    simp only [POS04RouteExecution.actualFold,inputs_unchanged,ih]

theorem route_support_unchanged (t : Tag) (x : Run6) (word : List StepEnv) :
    POS04RouteExecution.supportedWord (image packageDeletion.assignment) t x word =
      POS04RouteExecution.supportedWord canonical t x word := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    simp only [POS04RouteExecution.supportedWord,inputs_unchanged,ih]

theorem route_arrival_unchanged (r : RouteId) :
    POS04RouteExecution.arrivalRun (image packageDeletion.assignment) r =
      POS04RouteExecution.arrivalRun canonical r := by
  unfold POS04RouteExecution.arrivalRun
  rw [initial_unchanged,show POS04RouteExecution.wordFor (image packageDeletion.assignment) r =
    POS04RouteExecution.wordFor canonical r from rfl,route_fold_unchanged]
  rfl

end CSTTT.TargetTheory.GenericHandoff.POS04ExecutionLocality
