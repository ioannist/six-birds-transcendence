import CSTTT.Targets.GenericHandoff.NativeComposition.CoupledKernel
import CSTTT.Targets.GenericHandoff.ProfileNormalization

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePairedQuotientPrototype
open RegisterInterpreter FixedPointVerifier CoupledNativeKernelPrototype
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

-- The observer is the literal pair of the two existing branch emissions.
theorem outside_paired_future_equal (owner : Owner) (s t : Kernel)
    (word : List Bool) (observations : List Nat) :
    outputMass (input owner) pairedObserve (outside s) word observations =
      outputMass (input owner) pairedObserve (outside t) word observations := by
  induction word generalizing observations with
  | nil => cases observations <;> rfl
  | cons action rest ih =>
    cases observations with
    | nil => rfl
    | cons obs tail =>
      change (if 0=obs then 8*outputMass (input owner) pairedObserve (outside s) rest tail else 0)=
        (if 0=obs then 8*outputMass (input owner) pairedObserve (outside t) rest tail else 0)
      rw [ih tail]

theorem safe_rows_equal (s t : Kernel) (same : diagonalWeight s=diagonalWeight t) :
    rows (embed s) false=rows (embed t) false := by
  simp only [rows,embed,Bool.false_eq_true,ite_false]
  rw [same]

theorem equal_weight_paired_future (owner : Owner) (s t : Kernel)
    (same : diagonalWeight s=diagonalWeight t) : pairedEquivalent (input owner) s t := by
  intro word observations
  cases word with
  | nil => cases observations <;> rfl
  | cons action rest =>
    cases observations with
    | nil => rfl
    | cons obs tail =>
      cases action with
      | false =>
        simp only [outputMass,selected_rows]
        rw [safe_rows_equal s t same]
      | true =>
        change (if 0=obs then 8*outputMass (input owner) pairedObserve (outside s) rest tail else 0)=
          (if 0=obs then 8*outputMass (input owner) pairedObserve (outside t) rest tail else 0)
        rw [outside_paired_future_equal owner s t rest tail]

theorem safe_zero_mass (owner : Owner) (s : Kernel) :
    outputMass (input owner) pairedObserve (embed s) [false] [0]=diagonalWeight s := by
  rcases s with ⟨u,v⟩; cases u <;> cases v <;> decide +kernel +revert

theorem full_paired_future_exact (owner : Owner) (s t : Kernel) :
    pairedEquivalent (input owner) s t ↔ diagonalWeight s=diagonalWeight t := by
  constructor
  · intro equal
    have separating := equal [false] [0]
    simpa only [safe_zero_mass] using separating
  · exact equal_weight_paired_future owner s t

-- Finite weighted emission/successor signatures; outside is a distinct tag,
-- not an exit identity supplied to the observer.
def successorClass (c : Kernel → Nat) (outcome : Factor) : Option Nat :=
  (CoupledNativeKernelPrototype.destination outcome).map c
def blocks (c : Kernel → Nat) : List (Option Nat) :=
  (kernelStates.map fun s => some (c s)).eraseDups ++ [none]
def emittedBlockMass (i : Input) (c : Kernel → Nat) (s : Kernel)
    (action : Bool) (obs : Nat) (block : Option Nat) : Nat :=
  ((i.temporal.rows (embed s) action).map fun edge =>
    if pairedObserve edge.1=obs ∧ successorClass c edge.1=block then edge.2 else 0).sum
def signature (i : Input) (c : Kernel → Nat) (s : Kernel) : Nat × List Nat :=
  (c s,[false,true].flatMap fun action => [0,1,2,3].flatMap fun obs =>
    (blocks c).map fun block => emittedBlockMass i c s action obs block)
def step (i : Input) (c : Kernel → Nat) (s : Kernel) : Nat :=
  ((kernelStates.map (signature i c)).eraseDups).idxOf (signature i c s)
def iterate (i : Input) : Nat → Kernel → Nat
  | 0 => fun _ => 0
  | n+1 => step i (iterate i n)
def classes (i : Input) : Kernel → Nat := iterate i 2
def count (c : Kernel → Nat) : Nat := (kernelStates.map c).eraseDups.length

-- A closed description of the computed answer, never a raw input.
def expectedClass (s : Kernel) : Nat :=
  if s.1 && s.2 then 2 else if s.1 || s.2 then 1 else 0
theorem first_equation (owner : Owner) : iterate (input owner) 1=expectedClass := by
  funext s
  rcases s with ⟨u,v⟩; cases u <;> cases v <;> decide +kernel +revert
theorem step_equation (owner : Owner) : step (input owner) expectedClass=expectedClass := by
  funext s
  rcases s with ⟨u,v⟩; cases u <;> cases v <;> decide +kernel +revert
theorem second_equation (owner : Owner) : classes (input owner)=expectedClass := by
  change step (input owner) (iterate (input owner) 1)=expectedClass
  rw [first_equation,step_equation]
theorem stable_forever (owner : Owner) (n : Nat) :
    iterate (input owner) (1+n)=expectedClass := by
  induction n with
  | zero => exact first_equation owner
  | succ n ih =>
    change step (input owner) (iterate (input owner) (1+n))=expectedClass
    rw [ih,step_equation]
theorem profile_trajectory (owner : Owner) :
    count (iterate (input owner) 0)=1 ∧ count (iterate (input owner) 1)=3 ∧
      count (classes (input owner))=3 := by
  rw [first_equation,second_equation]
  decide +kernel +revert
theorem expected_class_exact (s t : Kernel) :
    expectedClass s=expectedClass t ↔ diagonalWeight s=diagonalWeight t := by
  rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
  cases u <;> cases v <;> cases a <;> cases b <;> decide +kernel
theorem stable_partition_full_paired_future (owner : Owner) (s t : Kernel) :
    classes (input owner) s=classes (input owner) t ↔ pairedEquivalent (input owner) s t := by
  rw [second_equation,expected_class_exact,full_paired_future_exact]
theorem actual_merge_and_exit_separation (owner : Owner) :
    pairedEquivalent (input owner) (false,true) (true,false) ∧
    ¬(∀ word exit,exitMass (input owner) (embed (false,true)) word exit=
      exitMass (input owner) (embed (true,false)) word exit) := by
  constructor
  · apply (full_paired_future_exact owner _ _).mpr; rfl
  · rw [full_exit_future_exact]; decide +kernel
theorem legacy_prediction_does_not_match (owner : Owner) :
    ¬ProfileRules.SamePartition (ProfileRules.predictive (CoupledNativeKernelPrototype.profile (input owner)))
      (classes (input owner)) := by
  intro linked
  have wrong := (linked (false,false) (false,true)).mp (old_prediction_constant owner _ _)
  rw [second_equation] at wrong
  exact (by decide +kernel : expectedClass (false,false)≠expectedClass (false,true)) wrong

-- Sum over DISTINCT computed class labels, so a merged fiber is counted once.
def classLabels (i : Input) : List Nat := (kernelStates.map (classes i)).eraseDups
def fiber (i : Input) (k : Nat) : List Kernel :=
  kernelStates.filter fun s => decide (classes i s=k)
def C (i : Input) (s : Kernel) (k : Nat) : Rat := if classes i s=k then 1 else 0
def U (i : Input) (k : Nat) (s : Kernel) : Rat :=
  if classes i s=k then 1/(fiber i k).length else 0
def CU (i : Input) (s t : Kernel) : Rat :=
  ((classLabels i).map fun k => C i s k*U i k t).sum
theorem fiber_contains_self (i : Input) (s : Kernel) : s∈fiber i (classes i s) := by
  simp only [fiber,List.mem_filter,decide_eq_true_eq]
  exact ⟨kernel_mem s,True.intro⟩
theorem class_label_has_positive_fiber (i : Input) (k : Nat) (present : k∈classLabels i) :
    0<(fiber i k).length := by
  have mapped : k∈kernelStates.map (classes i) := (ProfileRules.dedup_mem _ _).mp present
  rcases List.mem_map.mp mapped with ⟨s,_,rfl⟩
  exact List.length_pos_of_mem (fiber_contains_self i s)
theorem labels_equation (owner : Owner) : classLabels (input owner)=[0,1,2] := by
  unfold classLabels; rw [second_equation]; decide +kernel
theorem middle_fiber (owner : Owner) : fiber (input owner) 1=[(false,true),(true,false)] := by
  unfold fiber; rw [second_equation]; decide +kernel
theorem projection_averages_middle (owner : Owner) :
    CU (input owner) (false,true) (false,true)=1/2 ∧
    CU (input owner) (false,true) (true,false)=1/2 := by
  simp only [CU,labels_equation,C,U,fiber,second_equation]
  decide +kernel
theorem projection_not_identity (owner : Owner) : CU (input owner)≠identity := by
  intro equal
  have wrong := congrFun (congrFun equal (false,true)) (true,false)
  rw [(projection_averages_middle owner).2] at wrong
  exact (by decide +kernel : (1:Rat)/2≠identity (false,true) (true,false)) wrong
theorem projection_idempotent (owner : Owner) :
    ObjecthoodRules.product kernelStates (CU (input owner)) (CU (input owner))=CU (input owner) := by
  funext s t
  simp only [ObjecthoodRules.product,CU,labels_equation,C,U,fiber,second_equation]
  rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
  cases u <;> cases v <;> cases a <;> cases b <;> decide +kernel

theorem projection_probability_rows (owner : Owner) (s : Kernel) :
    Probability kernelStates (CU (input owner) s) := by
  constructor
  · intro t
    simp only [CU,labels_equation,C,U,fiber,second_equation]
    rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
    cases u <;> cases v <;> cases a <;> cases b <;> decide +kernel
  · simp only [FixedPointVerifier.mass,kernelStates,List.map_cons,List.map_nil,
      CU,labels_equation,C,U,fiber,second_equation]
    rcases s with ⟨u,v⟩; cases u <;> cases v <;> decide +kernel

theorem perturbed_projection_retains_matrix (owner : Owner) (perturb : Bool) :
    ObjecthoodRules.product kernelStates (perturbed (input owner) perturb) (CU (input owner))=
      perturbed (input owner) perturb := by
  funext s t
  simp only [ObjecthoodRules.product,CU,labels_equation,C,U,fiber,second_equation]
  rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
  cases u <;> cases v <;> cases a <;> cases b <;> cases perturb
  all_goals decide +kernel +revert

def closure (i : Input) (perturb squared : Bool) : Matrix Kernel :=
  ObjecthoodRules.product kernelStates
    (ObjecthoodRules.power kernelStates (perturbed i perturb) (if squared then 2 else 1)) (CU i)
def candidate (i : Input) (perturb squared : Bool) : Vector Kernel :=
  FixedPointVerifier.candidate (closure i perturb squared) (false,false) (operations perturb squared)
theorem closure_equation (owner : Owner) (perturb squared : Bool) :
    closure (input owner) perturb squared=verifiedMatrix perturb squared := by
  unfold closure
  funext s t
  simp only [ObjecthoodRules.product,CU,labels_equation,C,U,fiber,second_equation]
  rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
  cases u <;> cases v <;> cases a <;> cases b <;> cases perturb <;> cases squared
  all_goals decide +kernel +revert
theorem all_four_verifiers_pass (owner : Owner) (perturb squared : Bool) :
    check kernelStates (closure (input owner) perturb squared) (false,false)
      (operations perturb squared)=true := by
  rw [closure_equation]
  cases perturb <;> cases squared <;> decide +kernel
theorem candidate_equation (owner : Owner) (perturb squared : Bool) :
    candidate (input owner) perturb squared=expected perturb := by
  unfold candidate; rw [closure_equation]
  have verified := CoupledNativeKernelPrototype.candidate_equation owner perturb squared
  unfold CoupledNativeKernelPrototype.candidate at verified
  rw [CoupledNativeKernelPrototype.closure_equation] at verified
  exact verified
theorem all_four_probability_fixed_unique (owner : Owner) (perturb squared : Bool) :
    Probability kernelStates (candidate (input owner) perturb squared) ∧
    Fixed kernelStates (closure (input owner) perturb squared) (candidate (input owner) perturb squared) ∧
    (∀ x,Probability kernelStates x → Fixed kernelStates (closure (input owner) perturb squared) x →
      x=candidate (input owner) perturb squared) :=
  check_sound kernelStates kernel_mem _ _ _ (all_four_verifiers_pass owner perturb squared)
theorem all_four_nonuniform (owner : Owner) (perturb squared : Bool) :
    candidate (input owner) perturb squared≠(fun _ => (1:Rat)/4) := by
  rw [candidate_equation]
  have nonuniform := CoupledNativeKernelPrototype.all_four_nonuniform owner perturb squared
  rw [CoupledNativeKernelPrototype.candidate_equation] at nonuniform
  exact nonuniform

-- Existing intervention, actual recomputation; no new raw model.
theorem flat_step_constant (i : Input) : step (flatten i) (fun _ => 0)=(fun _ => 0) := by
  funext s
  rcases s with ⟨u,v⟩; cases u <;> cases v <;> rfl
theorem flat_iterate_constant (i : Input) (n : Nat) : iterate (flatten i) n=(fun _ => 0) := by
  induction n with
  | zero => rfl
  | succ n ih => change step (flatten i) (iterate (flatten i) n)=(fun _ => 0); rw [ih,flat_step_constant]
theorem flat_classes_constant (i : Input) : classes (flatten i)=(fun _ => 0) :=
  flat_iterate_constant i 2
theorem flat_full_future_exact (i : Input) (s t : Kernel) :
    classes (flatten i) s=classes (flatten i) t ↔ pairedEquivalent (flatten i) s t := by
  rw [flat_classes_constant]
  exact ⟨fun _ => flat_paired_all_future_equal i s t,fun _ => rfl⟩

-- The scientific predicate consumes the computed partition AND actual laws.
def PredictiveRefinement (i : Input) : Prop :=
  count (classes i)>1 ∧ ∀ s t,classes i s=classes i t ↔ pairedEquivalent i s t
noncomputable def quotientBit (i : Input) : Bool := by
  classical
  exact decide (PredictiveRefinement i)
theorem actual_predictive_refinement (owner : Owner) : PredictiveRefinement (input owner) :=
  ⟨by rw [second_equation]; decide +kernel,stable_partition_full_paired_future owner⟩
theorem flat_predictive_refinement_rejected (i : Input) : ¬PredictiveRefinement (flatten i) := by
  intro accepted
  have bad := accepted.1
  rw [flat_classes_constant] at bad
  exact (by decide +kernel : ¬count (fun _ : Kernel => 0)>1) bad
theorem actual_quotient_bit (owner : Owner) : quotientBit (input owner)=true := by
  classical
  exact decide_eq_true (actual_predictive_refinement owner)
theorem flat_quotient_bit (i : Input) : quotientBit (flatten i)=false := by
  classical
  exact decide_eq_false (flat_predictive_refinement_rejected i)
theorem quotient_readout_true_exact (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) :
    readout quotientBit cell copy a=some true ↔
      ∃ pair,a cell=some pair ∧ PredictiveRefinement (MemoryFrames.selectInput copy pair) := by
  classical
  rw [readout_some_exact]
  simp only [quotientBit,decide_eq_true_eq]
theorem quotient_readout_false_exact (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) :
    readout quotientBit cell copy a=some false ↔
      ∃ pair,a cell=some pair ∧ ¬PredictiveRefinement (MemoryFrames.selectInput copy pair) := by
  classical
  rw [readout_some_exact]
  simp only [quotientBit,decide_eq_false_iff_not]
theorem quotient_readout_none_exact (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) :
    readout quotientBit cell copy a=none ↔ a cell=none := readout_none_exact quotientBit cell copy a
theorem concrete_quotient_readouts (owner : Owner) :
    readout quotientBit owner false assignment=some true ∧
    readout quotientBit owner false flatAssignment=some false ∧
    readout quotientBit owner true flatAssignment=some true := by
  simp only [readout,selected,assignment,flatAssignment,Option.map_some,MemoryFrames.selectInput,ite_true]
  exact ⟨congrArg some (actual_quotient_bit owner),congrArg some (flat_quotient_bit (input owner)),
    congrArg some (actual_quotient_bit owner)⟩

-- Same raw Input couples the EXACT paired-future quotient to its C1 operator.
-- This remains a finite native component, not the original eight-clause API.
theorem same_native_quotient_return (owner : Owner) :
    PredictiveRefinement (input owner) ∧ count (classes (input owner))=3 ∧
    CurrentPrivacy (input owner) ∧
    (∃ s t,branchwiseEquivalent (input owner) s t ∧ ¬pairedEquivalent (input owner) s t) ∧
    (∀ perturb squared,Probability kernelStates (candidate (input owner) perturb squared) ∧
      Fixed kernelStates (closure (input owner) perturb squared) (candidate (input owner) perturb squared) ∧
      (∀ x,Probability kernelStates x → Fixed kernelStates (closure (input owner) perturb squared) x →
        x=candidate (input owner) perturb squared)) ∧
    forward (input owner)≠reverse (input owner) ∧
    OperationalViability.Accept (viabilitySchema owner) (viabilityData (input owner)) :=
  ⟨actual_predictive_refinement owner,(profile_trajectory owner).2.2,actual_current_constant owner,
    ⟨_,_,paired_binding_split owner⟩,all_four_probability_fixed_unique owner,
    (actual_cycle_directionality owner).2.2,actual_viability owner⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativePairedQuotientPrototype
