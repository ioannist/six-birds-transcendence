import CSTTT.Targets.GenericHandoff.NativeComposition.PairedPredictiveQuotient
import CSTTT.Targets.GenericHandoff.NativeComposition.MemoryFrames

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOriginalInterfacePrototype
open RegisterInterpreter FixedPointVerifier CoupledNativeKernelPrototype CSTTT.TransportTheory
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
local instance : DecidableEq (TemporalSnapshotReadout Frame.Predictive Frame.Residue Bool) :=
  CSTTT.TransportTheory.instDecidableEqTemporalSnapshotReadout

-- The ORIGINAL frame schema has no external outcome at all.
theorem original_destination_internal (o : Factor) : clauseSchema.destination o=some o := rfl
def phasePrediction (owner : Owner) (phase : Bool) : Frame.Predictive :=
  TemporalFactorRules.prediction (factorSchema owner) (input owner).temporal (phase,false,false)
theorem native_prediction_equation (owner : Owner) (s : Factor) :
    TemporalFactorRules.prediction (factorSchema owner) (input owner).temporal s=
      phasePrediction owner s.1 := by
  rcases s with ⟨p,u,v⟩; cases p <;> cases u <;> cases v <;> rfl
theorem phase_prediction_distinct (owner : Owner) : phasePrediction owner false≠phasePrediction owner true := by
  cases owner <;> decide +kernel
theorem native_prediction_exact (owner : Owner) (s t : Factor) :
    TemporalFactorRules.prediction (factorSchema owner) (input owner).temporal s=
      TemporalFactorRules.prediction (factorSchema owner) (input owner).temporal t ↔ s.1=t.1 := by
  rw [native_prediction_equation,native_prediction_equation]
  rcases s with ⟨p,u,v⟩; rcases t with ⟨q,a,b⟩
  cases p <;> cases q <;> simp [phase_prediction_distinct,Ne.symm (phase_prediction_distinct owner)]
theorem native_class_mass (owner : Owner) (s : Factor) (action : Bool) (c : Frame.Predictive) :
    TemporalFactorRules.mass (factorSchema owner) (input owner).temporal s action c=
      if phasePrediction owner (s.1 || action)=c then 8 else 0 := by
  simp only [TemporalFactorRules.mass,TemporalFactorRules.row,factorSchema,clauseSchema]
  change ((rows s action).filter (fun e => decide
    (TemporalFactorRules.prediction (factorSchema owner) (input owner).temporal e.1=c))).foldl
      (fun n e => n+e.2) 0= _
  simp only [native_prediction_equation]
  rcases s with ⟨p,u,v⟩
  cases p <;> cases u <;> cases v <;> cases action
  all_goals by_cases hi : phasePrediction owner false=c
  all_goals by_cases ho : phasePrediction owner true=c
  all_goals simp [rows,embed,outside,diagonalWeight,hi,ho]
theorem native_finite_bisim (owner : Owner) :
    TemporalFactorRules.FiniteBisim (factorSchema owner) (input owner).temporal := by
  intro s hs t ht action ha hp
  have phase := (native_prediction_exact owner s t).mp hp
  refine ⟨?_,rfl⟩
  intro c hc
  rw [native_class_mass,native_class_mass,phase]

-- Same raw factor future with the original EIGHT-component representation.
-- This intermediary only removes the owner's representation change.
def observedModel (i : Input) (owner : Owner) (names : Owner → CarrierId) :
    FullFutureModel Frame.State Bool Factor (TemporalFactorRules.Code Factor Factor Bool Owner)
      (TemporalSnapshotReadout Frame.Predictive Frame.Residue Bool) :=
  ⟨factors,TemporalFactorRules.code (factorSchema owner) i.temporal 2,
    fun x => TemporalRuntimeCoherence.observationImage names
      (TemporalFactorRules.observe (factorSchema owner) i.temporal 2 x),
    TemporalFactorRules.weight (factorSchema owner) i.temporal,
    TemporalFactorRules.update (factorSchema owner) i.temporal⟩
theorem observed_all_words (owner : Owner) (names : Owner → CarrierId) :
    FullFutureSufficient (observedModel (input owner) owner names) := by
  apply FutureLumping.all_words
  intro x y hc
  have native := TemporalFactorRules.one_step (factorSchema owner) (input owner).temporal 2
    factor_domain (native_finite_bisim owner) x y hc
  exact ⟨congrArg (TemporalRuntimeCoherence.observationImage names) native.1,native.2⟩
def context (s : Factor) (counter ticks : Nat) (residue : Frame.Residue) (funded : Bool) : Frame.State :=
  ⟨s,counter,ticks,residue,funded⟩
theorem same_context_code (owner : Owner) (s t : Kernel) (counter ticks : Nat)
    (residue : Frame.Residue) (funded : Bool) :
    TemporalFactorRules.code (factorSchema owner) (input owner).temporal 2
      (context (embed s) counter ticks residue funded)=
    TemporalFactorRules.code (factorSchema owner) (input owner).temporal 2
      (context (embed t) counter ticks residue funded) := by
  simp only [TemporalFactorRules.code,context,native_prediction_equation,embed]
theorem original_full_future_kernel_equal (owner : Owner) (names : Owner → CarrierId)
    (s t : Kernel) (counter ticks : Nat) (residue : Frame.Residue) (funded : Bool)
    (word : List Bool) (trace : List (TemporalSnapshotReadout Frame.Predictive Frame.Residue Bool)) :
    fullFuture (observedModel (input owner) owner names) (context (embed s) counter ticks residue funded) word trace=
      fullFuture (observedModel (input owner) owner names) (context (embed t) counter ticks residue funded) word trace :=
  observed_all_words owner names _ _ (same_context_code owner s t counter ticks residue funded) word trace
theorem original_full_future_phase_exact (owner : Owner) (names : Owner → CarrierId)
    (s t : Factor) (counter ticks : Nat) (residue : Frame.Residue) (funded : Bool) :
    (∀ word trace,fullFuture (observedModel (input owner) owner names)
      (context s counter ticks residue funded) word trace=
      fullFuture (observedModel (input owner) owner names)
      (context t counter ticks residue funded) word trace) ↔ s.1=t.1 := by
  constructor
  · intro same
    let x := context s counter ticks residue funded
    let y := context t counter ticks residue funded
    let model := observedModel (input owner) owner names
    have test := same [] [model.observe x]
    by_cases observed : model.observe x=model.observe y
    · exact (native_prediction_exact owner s t).mp (congrArg TemporalSnapshotReadout.predictive observed)
    · have different : [model.observe x]≠[model.observe y] := by
        intro equal; exact observed (List.cons.inj equal).1
      change (if [model.observe x]=[model.observe x] then (1:Rat) else 0)=
        (if [model.observe x]=[model.observe y] then 1 else 0) at test
      simp only [ite_true,if_neg different] at test
      exact False.elim ((by decide +kernel : (1:Rat)≠0) test)
  · intro phase word trace
    apply observed_all_words owner names _ _ ?_ word trace
    simp only [observedModel,TemporalFactorRules.code,context,native_prediction_equation,phase]

theorem memory_weight_link (cell source owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : RegisterFuture.RawReady (MemoryFrames.raw cell source owner names) a)
    (p : Input × Input) (hp : a cell=some p) (x : Frame.Registers) (da : Unit × Bool) (o : Factor) :
    RegisterFuture.weight (MemoryFrames.raw cell source owner names) a h x da o=
      (observedModel (MemoryFrames.selectInput source p) owner names).weight (x ()) da.2 o := by
  unfold RegisterFuture.weight
  rw [MemoryFrames.row cell source owner names a h p hp]
  change _ = (((TemporalFactorRules.actualRows (factorSchema owner)
    (MemoryFrames.selectInput source p).temporal (x ()) da.2).filter fun e => decide (e.1=o)).map Prod.snd).sum
  generalize TemporalFactorRules.actualRows (factorSchema owner)
    (MemoryFrames.selectInput source p).temporal (x ()) da.2 = row
  induction row with
  | nil => rfl
  | cons edge rest ih => by_cases same : edge.1=o <;> simp [same,ih,Rat.zero_add]
theorem memory_full_word_law (cell source owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : RegisterFuture.RawReady (MemoryFrames.raw cell source owner names) a)
    (p : Input × Input) (hp : a cell=some p) (x : Frame.Registers) (word : List (Unit × Bool))
    (trace : List (TemporalSnapshotReadout Frame.Predictive Frame.Residue Bool)) :
    fullFuture (RegisterFuture.future (MemoryFrames.raw cell source owner names) a h) x word trace=
      fullFuture (observedModel (MemoryFrames.selectInput source p) owner names) (x ()) (word.map Prod.snd) trace := by
  have transport := FutureReindex.mapped_word_law
    (observedModel (MemoryFrames.selectInput source p) owner names)
    (RegisterFuture.future (MemoryFrames.raw cell source owner names) a h)
    (fun run => run ()) Prod.snd id (fun _ _ he => he) rfl
    (MemoryFrames.observation cell source owner names a h p hp)
    (memory_weight_link cell source owner names a h p hp)
    (fun run da o => by
      change (RegisterFuture.next (MemoryFrames.raw cell source owner names) a h run da o) ()= _
      rw [MemoryFrames.next cell source owner names a h p hp]; rfl)
    x word trace
  simpa only [List.map_id] using transport
theorem actual_original_full_kernel_equal (cell source owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : RegisterFuture.RawReady (MemoryFrames.raw cell source owner names) a)
    (p : Input × Input) (hp : a cell=some p) (selectedNative : MemoryFrames.selectInput source p=input owner)
    (s t : Kernel) (counter ticks : Nat) (residue : Frame.Residue) (funded : Bool)
    (word : List (Unit × Bool)) (trace : List (TemporalSnapshotReadout Frame.Predictive Frame.Residue Bool)) :
    fullFuture (RegisterFuture.future (MemoryFrames.raw cell source owner names) a h)
      (Frame.pack (context (embed s) counter ticks residue funded)) word trace=
    fullFuture (RegisterFuture.future (MemoryFrames.raw cell source owner names) a h)
      (Frame.pack (context (embed t) counter ticks residue funded)) word trace := by
  rw [memory_full_word_law cell source owner names a h p hp,
    memory_full_word_law cell source owner names a h p hp,selectedNative]
  exact original_full_future_kernel_equal owner names s t counter ticks residue funded _ _

-- This is the actual original predictor, not the separate labeled exit profile.
def prediction (i : Input) (s : Kernel) : Frame.Predictive :=
  TemporalFactorRules.prediction (factorSchema i.temporal.resource.owner) i.temporal (embed s)
def classes (i : Input) (s : Kernel) : Nat :=
  (kernelStates.map (prediction i)).eraseDups.idxOf (prediction i s)
theorem classes_constant (owner : Owner) : classes (input owner)=(fun _ => 0) := by
  funext s
  rcases s with ⟨u,v⟩; cases u <;> cases v <;> cases owner <;> decide +kernel
theorem original_partition_full_future_exact (owner : Owner) (names : Owner → CarrierId)
    (s t : Kernel) (counter ticks : Nat) (residue : Frame.Residue) (funded : Bool) :
    classes (input owner) s=classes (input owner) t ↔
      ∀ word trace,fullFuture (observedModel (input owner) owner names)
        (context (embed s) counter ticks residue funded) word trace=
        fullFuture (observedModel (input owner) owner names)
        (context (embed t) counter ticks residue funded) word trace := by
  rw [classes_constant]
  exact ⟨fun _ => original_full_future_kernel_equal owner names s t counter ticks residue funded,fun _ => rfl⟩
def labels (i : Input) : List Nat := (kernelStates.map (classes i)).eraseDups
def fiber (i : Input) (k : Nat) : List Kernel := kernelStates.filter fun s => decide (classes i s=k)
def C (i : Input) (s : Kernel) (k : Nat) : Rat := if classes i s=k then 1 else 0
def U (i : Input) (k : Nat) (s : Kernel) : Rat := if classes i s=k then 1/(fiber i k).length else 0
def CU (i : Input) (s t : Kernel) : Rat := ((labels i).map fun k => C i s k*U i k t).sum
theorem labels_equation (owner : Owner) : labels (input owner)=[0] := by
  unfold labels; rw [classes_constant]; decide +kernel
theorem projection_uniform (owner : Owner) : CU (input owner)=(fun _ _ => (1:Rat)/4) := by
  funext s t
  simp only [CU,labels_equation,C,U,fiber,classes_constant]
  decide +kernel
def closure (i : Input) (perturb squared : Bool) : Matrix Kernel :=
  ObjecthoodRules.product kernelStates
    (ObjecthoodRules.power kernelStates (perturbed i perturb) (if squared then 2 else 1)) (CU i)
def uniform : Vector Kernel := fun _ => 1/(kernelStates.length:Rat)
theorem uniform_equation : uniform=(fun _ => (1:Rat)/4) := rfl
theorem all_four_closures_uniform (owner : Owner) (perturb squared : Bool) :
    closure (input owner) perturb squared=(fun _ _ => (1:Rat)/4) := by
  unfold closure; rw [projection_uniform]
  funext s t
  rcases s with ⟨u,v⟩; rcases t with ⟨a,b⟩
  cases u <;> cases v <;> cases a <;> cases b <;> cases perturb <;> cases squared
  all_goals decide +kernel +revert
theorem uniform_probability : Probability kernelStates uniform := by
  constructor
  · intro s; change 0≤(1:Rat)/4; decide +kernel
  · decide +kernel
theorem uniform_fixed (owner : Owner) (perturb squared : Bool) :
    Fixed kernelStates (closure (input owner) perturb squared) uniform := by
  rw [all_four_closures_uniform]
  intro s
  change dot kernelStates (fun _ => (1:Rat)/4) (fun _ => (1:Rat)/4)=(1:Rat)/4
  decide +kernel
theorem actual_fixed_point_unique_uniform (owner : Owner) (perturb squared : Bool) (x : Vector Kernel)
    (prob : Probability kernelStates x) (fixed : Fixed kernelStates (closure (input owner) perturb squared) x) :
    x=uniform := by
  funext s
  have equation := fixed s
  rw [all_four_closures_uniform] at equation
  have scaled : dot kernelStates (fun _ => (1:Rat)/4) x=(1/4)*mass kernelStates x := by
    have scale := dot_scale kernelStates ((1:Rat)/4) (fun _ => 1) x
    simpa only [dot,mass,Rat.mul_one,Rat.one_mul] using scale
  change dot kernelStates (fun _ => (1:Rat)/4) x=x s at equation
  rw [scaled,prob.2] at equation
  simpa only [uniform_equation,Rat.mul_one] using equation.symm
def NonuniformC1 (i : Input) : Prop :=
  ∃ perturb squared x,Probability kernelStates x ∧ Fixed kernelStates (closure i perturb squared) x ∧ x≠uniform
theorem actual_nonuniform_C1_rejected (owner : Owner) : ¬NonuniformC1 (input owner) := by
  rintro ⟨perturb,squared,x,prob,fixed,nonuniform⟩
  exact nonuniform (actual_fixed_point_unique_uniform owner perturb squared x prob fixed)
noncomputable def nonuniformBit (i : Input) : Bool := by
  classical
  exact decide (NonuniformC1 i)
theorem actual_nonuniform_bit_false (owner : Owner) : nonuniformBit (input owner)=false := by
  classical
  exact decide_eq_false (actual_nonuniform_C1_rejected owner)
theorem nonuniform_readout_true_exact (cell source : Owner) (a : Assignment Owner MemoryValue) :
    readout nonuniformBit cell source a=some true ↔
      ∃ p,a cell=some p ∧ NonuniformC1 (MemoryFrames.selectInput source p) := by
  classical
  rw [readout_some_exact]
  simp only [nonuniformBit,decide_eq_true_eq]
theorem nonuniform_readout_false_exact (cell source : Owner) (a : Assignment Owner MemoryValue) :
    readout nonuniformBit cell source a=some false ↔
      ∃ p,a cell=some p ∧ ¬NonuniformC1 (MemoryFrames.selectInput source p) := by
  classical
  rw [readout_some_exact]
  simp only [nonuniformBit,decide_eq_false_iff_not]
theorem nonuniform_readout_none_exact (cell source : Owner) (a : Assignment Owner MemoryValue) :
    readout nonuniformBit cell source a=none ↔ a cell=none := readout_none_exact nonuniformBit cell source a
theorem concrete_original_readout_false (owner : Owner) (source : Bool) :
    readout nonuniformBit owner source assignment=some false := by
  simp only [readout,selected,assignment,Option.map_some]
  cases source <;> exact congrArg some (actual_nonuniform_bit_false owner)

-- Stronger obstruction at the ORIGINAL ObjecthoodRules.Accept boundary:
-- every possible horizon, perturbation, prototype list, operation list and
-- remaining raw certificate field is retained in this universal negative.
theorem original_objecthood_columns_equal (owner : Owner)
    (d : ObjecthoodRules.Raw Kernel Bool Factor)
    (profileEq : d.profile=CoupledNativeKernelPrototype.profile (input owner)) (s t u : Kernel) :
    ObjecthoodRules.E d s t=ObjecthoodRules.E d s u := by
  have constant (x y : Kernel) : ObjecthoodRules.classOf d x=ObjecthoodRules.classOf d y := by
    simpa only [ObjecthoodRules.classOf,profileEq] using old_prediction_constant owner x y
  have uniformU (k : Nat) (x y : Kernel) : ObjecthoodRules.U d k x=ObjecthoodRules.U d k y := by
    unfold ObjecthoodRules.U
    cases h : d.prototypes[k]? with
    | none => rfl
    | some p => simp only [if_pos (constant x p),if_pos (constant y p)]
  have columns (x y z : Kernel) : ObjecthoodRules.CU d x y=ObjecthoodRules.CU d x z := by
    unfold ObjecthoodRules.CU
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    rw [uniformU k y z]
  unfold ObjecthoodRules.E ObjecthoodRules.product
  apply congrArg List.sum
  apply List.map_congr_left
  intro k hk
  rw [columns k t u]
theorem original_probability_fixed_uniform (owner : Owner)
    (d : ObjecthoodRules.Raw Kernel Bool Factor)
    (profileEq : d.profile=CoupledNativeKernelPrototype.profile (input owner)) (x : Vector Kernel)
    (prob : Probability kernelStates x) (fixed : Fixed kernelStates (ObjecthoodRules.E d) x) : x=uniform := by
  have constant (s : Kernel) : x s=x (false,false) := by
    have equation := fixed s
    have columns : (fun j => ObjecthoodRules.E d j s)=(fun j => ObjecthoodRules.E d j (false,false)) :=
      funext fun j => original_objecthood_columns_equal owner d profileEq j s (false,false)
    rw [columns] at equation
    exact equation.symm.trans (fixed (false,false))
  have norm := prob.2
  simp only [mass,kernelStates,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,constant,Rat.add_zero] at norm
  have center : x (false,false)=(1:Rat)/4 := by grind
  funext s
  exact (constant s).trans center
theorem original_checked_candidate_uniform (owner : Owner)
    (d : ObjecthoodRules.Raw Kernel Bool Factor)
    (profileEq : d.profile=CoupledNativeKernelPrototype.profile (input owner))
    (gate : ObjecthoodRules.Gate d) : ObjecthoodRules.pi d=ObjecthoodRules.uniform d := by
  have checked := ObjecthoodRules.checked_probability_fixed_unique d gate
  have prob : Probability kernelStates (ObjecthoodRules.pi d) := by
    simpa only [profileEq,CoupledNativeKernelPrototype.profile] using checked.1
  have fixed : Fixed kernelStates (ObjecthoodRules.E d) (ObjecthoodRules.pi d) := by
    simpa only [profileEq,CoupledNativeKernelPrototype.profile] using checked.2.1
  have same := original_probability_fixed_uniform owner d profileEq _ prob fixed
  funext s
  change ObjecthoodRules.pi d s=1/(d.profile.states.length:Rat)
  rw [profileEq]
  exact congrFun same s
theorem original_objecthood_accept_rejected (owner : Owner)
    (d : ObjecthoodRules.Raw Kernel Bool Factor)
    (profileEq : d.profile=CoupledNativeKernelPrototype.profile (input owner)) : ¬ObjecthoodRules.Accept d := by
  intro accepted
  exact accepted.2.1 (original_checked_candidate_uniform owner d profileEq accepted.1)
def OriginalC1Possible (i : Input) : Prop :=
  ∃ d : ObjecthoodRules.Raw Kernel Bool Factor,
    d.profile=CoupledNativeKernelPrototype.profile i ∧ ObjecthoodRules.Accept d
theorem original_C1_impossible (owner : Owner) : ¬OriginalC1Possible (input owner) := by
  rintro ⟨d,profileEq,accepted⟩
  exact original_objecthood_accept_rejected owner d profileEq accepted
noncomputable def originalC1Bit (i : Input) : Bool := by
  classical
  exact decide (OriginalC1Possible i)
theorem actual_original_C1_bit_false (owner : Owner) : originalC1Bit (input owner)=false := by
  classical
  exact decide_eq_false (original_C1_impossible owner)
theorem original_C1_true_exact (cell source : Owner) (a : Assignment Owner MemoryValue) :
    readout originalC1Bit cell source a=some true ↔
      ∃ p,a cell=some p ∧ OriginalC1Possible (MemoryFrames.selectInput source p) := by
  classical
  rw [readout_some_exact]
  simp only [originalC1Bit,decide_eq_true_eq]
theorem original_C1_false_exact (cell source : Owner) (a : Assignment Owner MemoryValue) :
    readout originalC1Bit cell source a=some false ↔
      ∃ p,a cell=some p ∧ ¬OriginalC1Possible (MemoryFrames.selectInput source p) := by
  classical
  rw [readout_some_exact]
  simp only [originalC1Bit,decide_eq_false_iff_not]
theorem original_C1_none_exact (cell source : Owner) (a : Assignment Owner MemoryValue) :
    readout originalC1Bit cell source a=none ↔ a cell=none := readout_none_exact originalC1Bit cell source a
theorem concrete_original_C1_false (owner : Owner) (source : Bool) :
    readout originalC1Bit owner source assignment=some false := by
  simp only [readout,selected,assignment,Option.map_some]
  cases source <;> exact congrArg some (actual_original_C1_bit_false owner)

theorem original_row_scale : clauseSchema.rowScale=1 := rfl
theorem original_funded_row_total (owner : Owner) (x : Frame.State) (action : Bool) (funded : x.funded=true) :
    ((TemporalFactorRules.actualRows (factorSchema owner) (input owner).temporal x action).map Prod.snd).sum=8 := by
  simp only [TemporalFactorRules.actualRows,TemporalFactorRules.enabled,funded,input,canonicalInput,
    factorData,Bool.true_and,TemporalFactorRules.row,factorSchema,clauseSchema]
  rcases x with ⟨⟨p,u,v⟩,counter,ticks,residue,paid⟩
  change (((rows (p,u,v) action).map fun e => (e.1,(e.2:Rat)/1)).map Prod.snd).sum=8
  cases p <;> cases u <;> cases v <;> cases action <;> decide +kernel
theorem actual_memory_row_not_probability (cell source owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : RegisterFuture.RawReady (MemoryFrames.raw cell source owner names) a)
    (p : Input × Input) (hp : a cell=some p) (selectedNative : MemoryFrames.selectInput source p=input owner)
    (x : Frame.Registers) (funded : (x ()).funded=true) (da : Unit × Bool) :
    ((RegisterFuture.row (MemoryFrames.raw cell source owner names) a h x da).map Prod.snd).sum≠1 := by
  rw [MemoryFrames.row cell source owner names a h p hp,selectedNative,original_funded_row_total owner (x ()) da.2 funded]
  decide +kernel

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOriginalInterfacePrototype
