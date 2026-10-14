import CSTTT.FullNative.SharedPackage
import CSTTT.Targets.GenericHandoff.NativeComposition.OriginalInterfaceObstruction

/-! G27b: one historical chain realizes source and BOTH target certificates.
The interface is the original prose C1--C8 design contract at the explicitly
preregistered G17 behavioral/history interfaces, with the C1 period-two audit.
The unchanged G15a original dispatcher remains refuted. No new model is used. -/
namespace CSTTT.FullNative.OriginalPackage
open AccountExecution PhysicalExecution SnapshotExecution SharedPackage
open TargetTheory.GenericHandoff FixedPointVerifier
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

local instance : DecidableEq (CSTTT.TransportTheory.TemporalSnapshotReadout
    NativeComposition.Frame.Predictive NativeComposition.Frame.Residue Bool) :=
  CSTTT.TransportTheory.instDecidableEqTemporalSnapshotReadout

def sourceRaw : Raw := ⟨Credit.sourceCycleWorld,0⟩
def targetRaw (right : Bool) : Raw := ⟨Credit.creditedBothWorld,TemporalTransport.branchOwner right⟩
def targetExecution (right : Bool) : Execution :=
  ⟨Credit.creditedBothWorld.accounts,if right then Credit.creditedSecondLocal else Credit.creditedFirstLocal⟩

theorem source_read : execution sourceRaw=some TemporalTransport.sourceAtCopy := by rfl
theorem target_read (right : Bool) : execution (targetRaw right)=some (targetExecution right) := by
  cases right <;> rfl

theorem actual_ready : Ready TemporalTransport.sourceAtCopy ∧
    ∀ right, Ready (targetExecution right) := by
  constructor
  · exact ⟨⟨rfl,rfl,rfl⟩,rfl,by decide +kernel⟩
  · intro right
    cases right <;> exact ⟨⟨rfl,rfl,rfl⟩,rfl,by decide +kernel⟩

theorem source_and_both_targets : Accept sourceRaw ∧ ∀ right, Accept (targetRaw right) :=
  ⟨accept_from_raw sourceRaw _ source_read actual_ready.1,
    fun right => accept_from_raw (targetRaw right) _ (target_read right) (actual_ready.2 right)⟩

theorem all_eight_from_same_raw (c : Clause) :
    clause sourceRaw c ∧ ∀ right, clause (targetRaw right) c :=
  ⟨accepts_all_clauses sourceRaw source_and_both_targets.1 c,
    fun right => accepts_all_clauses (targetRaw right) (source_and_both_targets.2 right) c⟩

def HistoricalChain : Prop :=
    Credit.runCycle initialWorld 0 Credit.sourcePlan=some sourceRaw.world ∧
    Credit.transferFrom sourceRaw.world=some Credit.creditedTransferWorld ∧
    Credit.runCycle Credit.creditedTransferWorld 1 Credit.sourcePlan=some Credit.creditedFirstWorld ∧
    Credit.runCycle Credit.creditedFirstWorld 2 Credit.sourcePlan=some (targetRaw false).world ∧
    Historical sourceRaw.world ∧ Historical (targetRaw false).world ∧
    (targetRaw false).world=(targetRaw true).world ∧
    (targetRaw false).world.carriers 0=none ∧ (targetRaw false).world.bridge=none

theorem single_historical_chain : HistoricalChain :=
  ⟨Credit.source_cycle_success,rfl,rfl,rfl,Credit.source_cycle_historical,
    Credit.credited_both_historical,rfl,Credit.same_history_both_credits.2.2.2.2.2.1,
    Credit.same_history_both_credits.2.2.2.2.2.2⟩

theorem program_and_provenance_coherence (right : Bool) :
    (targetExecution right).resident.installed=TemporalTransport.sourceAtCopy.resident.installed ∧
    (targetExecution right).resident.rootedRoute=([TemporalTransport.anchor.state],[TemporalTransport.anchor.receipt]) ∧
    (frame (TemporalTransport.targetAtCopy right)).context.localRecords=0 ∧
    TemporalTransport.consumedAnchor=some ⟨6,6,20,FullInterface.rootState⟩ ∧
    (TemporalTransport.writtenSnapshot right).map (fun s => s.receipt)=
      TemporalTransport.sourceAtCopy.resident.receipts.head? := by
  cases right <;> refine ⟨rfl,?_⟩ <;> decide +kernel

def Coherence : Prop :=
  Siblings Credit.creditedBothWorld ∧
  (∀ word, ∃ final, JointContinuation Credit.creditedBothWorld word final ∧
    Historical final ∧ Siblings final) ∧
  (∀ a, ((JointFuture.normalizedJointRows Credit.creditedBothWorld a).map Prod.snd).sum=1) ∧
  (∀ word trace, JointFuture.jointLaw TemporalTransport.anchor Credit.creditedBothWorld word trace=
    WeightedFuture.law (normalizedRows renewable)
      (fun x => FullInterface.observe (TemporalTransport.shiftRun TemporalTransport.anchor (frame x)))
      (targetExecution false) (word.map Prod.fst) (trace.map Prod.fst) *
    WeightedFuture.law (normalizedRows renewable)
      (fun x => FullInterface.observe (TemporalTransport.shiftRun TemporalTransport.anchor (frame x)))
      (targetExecution true) (word.map Prod.snd) (trace.map Prod.snd)) ∧
  (∀ right,
    TemporalTransport.shiftRun TemporalTransport.anchor (frame (TemporalTransport.targetAtCopy right))=
      TemporalTransport.rebase (TemporalTransport.targetAtCopy right).resident.owner
        (TemporalTransport.targetAtCopy right).resident.rootedRoute (frame TemporalTransport.sourceAtCopy)) ∧
  (∀ right, (frame (TemporalTransport.targetAtCopy right)).context≠
      (frame TemporalTransport.sourceAtCopy).context)

theorem actual_coherence : Coherence :=
  ⟨Credit.credited_both_siblings,Credit.credited_joint_future,
    JointFuture.normalized_joint_mass _ Credit.credited_both_siblings,JointClaims.credited_joint_factorization,
    fun right => (TemporalTransport.actual_copy_transport right).2.2,
    fun right => (TemporalTransport.copy_contexts_not_identical right).1⟩

def SplitHistories : Prop := ∀ right,
  Historical (mount sourceRaw.world sourceRaw.owner (Binding.splitExecution TemporalTransport.sourceAtCopy right)) ∧
  ∀ target, Historical (mount (targetRaw target).world (targetRaw target).owner
    (Binding.splitExecution (targetExecution target) right))

theorem actual_historical_splits : SplitHistories := by
  intro right
  constructor
  · exact Binding.world_split_historical sourceRaw.world Credit.source_cycle_historical 0
      TemporalTransport.sourceAtCopy.resident rfl rfl actual_ready.1.1 right
  · intro target
    cases target
    · exact Binding.world_split_historical Credit.creditedBothWorld Credit.credited_both_historical 1
        Credit.creditedFirstLocal rfl rfl (actual_ready.2 false).1 right
    · exact Binding.world_split_historical Credit.creditedBothWorld Credit.credited_both_historical 2
        Credit.creditedSecondLocal rfl rfl (actual_ready.2 true).1 right

/-- The single output includes all eight certificates and the shared-data law
bridge. Its constructor is evaluated here; no clause witness is a parameter. -/
structure Assembly : Prop where
  source : Accept sourceRaw
  first : Accept (targetRaw false)
  second : Accept (targetRaw true)
  shared : Coherence
  chain : HistoricalChain
  splitHistories : SplitHistories
  sourceHistory : Historical sourceRaw.world
  targetHistory : Historical (targetRaw false).world
  provenance : ∀ right,
    (targetExecution right).resident.installed=TemporalTransport.sourceAtCopy.resident.installed ∧
    (targetExecution right).resident.rootedRoute=([TemporalTransport.anchor.state],[TemporalTransport.anchor.receipt]) ∧
    (frame (TemporalTransport.targetAtCopy right)).context.localRecords=0 ∧
    TemporalTransport.consumedAnchor=some ⟨6,6,20,FullInterface.rootState⟩ ∧
    (TemporalTransport.writtenSnapshot right).map (fun s => s.receipt)=
      TemporalTransport.sourceAtCopy.resident.receipts.head?

theorem full_original_design_assembly : Assembly :=
  ⟨source_and_both_targets.1,source_and_both_targets.2 false,source_and_both_targets.2 true,
    actual_coherence,single_historical_chain,actual_historical_splits,
    Credit.source_cycle_historical,Credit.credited_both_historical,
    program_and_provenance_coherence⟩

/-- The former stronger C1 gate is deliberately not accepted by this repair. -/
def AllStagingsUnique : Prop := ∀ perturb squared, ∀ p q,
  Probability states p → Probability states q →
  Fixed states (Objecthood.closure perturb squared) p →
  Fixed states (Objecthood.closure perturb squared) q → p=q

theorem old_stronger_c1_gate_rejected : ¬AllStagingsUnique := by
  intro unique
  obtain ⟨p,q,fp,fq,neq⟩ := Objecthood.squared_unperturbed_nonunique
  exact neq (unique false true _ _ p q fp fq)

theorem explicit_period_two_countertrace :
    PositiveMatrix.push states Objecthood.P (Objecthood.phaseLaw false)=Objecthood.phaseLaw true ∧
    PositiveMatrix.push states Objecthood.P (Objecthood.phaseLaw true)=Objecthood.phaseLaw false ∧
    Objecthood.phaseLaw false≠Objecthood.phaseLaw true :=
  ⟨Objecthood.phase_step false,Objecthood.phase_step true,Objecthood.squared_unperturbed_nonunique.2.2.2.2⟩

theorem physical_stationarity_is_not_history_return :
    ClockClosure.Route TemporalTransport.sourceAtCopy [false,false]
      (ClockClosure.secondReturn TemporalTransport.sourceAtCopy) ∧
    (ClockClosure.secondReturn TemporalTransport.sourceAtCopy).resident.current=
      TemporalTransport.sourceAtCopy.resident.current ∧
    (frame (ClockClosure.secondReturn TemporalTransport.sourceAtCopy)).context.order=
      (frame TemporalTransport.sourceAtCopy).context.order+2 ∧
    ClockClosure.secondReturn TemporalTransport.sourceAtCopy≠TemporalTransport.sourceAtCopy :=
  ClockClosure.physical_return_countertrace _ actual_ready.1.1 actual_ready.1.2.1

theorem expanded_current_rejects_privacy (x : Execution) :
    Binding.expandedCurrent (Binding.splitExecution x false).resident.current≠
    Binding.expandedCurrent (Binding.splitExecution x true).resident.current := by
  intro equal
  exact (Binding.split_promotion x.resident.current).2 (congrArg Prod.snd equal)

theorem flattened_binding_rejected (s t : State) (word : List Bool) (outputs : List Nat) :
    Binding.emittedLaw (rationalRows (flatten model)) Binding.joint s word outputs=
    Binding.emittedLaw (rationalRows (flatten model)) Binding.joint t word outputs :=
  Binding.flattening_destroys_joint_gap s t word outputs

theorem observer_timing_boundary (x : Execution) :
    Binding.emittedLaw (normalizedRows renewable) (fun y => Binding.joint y.resident.current) x [] []=1 ∧
    WeightedFuture.law (normalizedRows renewable) (fun y => FullInterface.observe (frame y)) x [] []=0 :=
  ⟨rfl,rfl⟩

open CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOriginalInterfacePrototype
  CSTTT.TargetTheory.GenericHandoff.NativeComposition.CoupledNativeKernelPrototype in
theorem legacy_original_c1_impossible (owner : Bool) : ¬OriginalC1Possible (input owner) :=
  original_C1_impossible owner

open CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOriginalInterfacePrototype
  CSTTT.TargetTheory.GenericHandoff.NativeComposition.CoupledNativeKernelPrototype in
theorem legacy_predictor_merges_all_kernel_states (owner : Bool) :
    CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOriginalInterfacePrototype.classes (input owner)=
      (fun _ => 0) := classes_constant owner

open CSTTT.TargetTheory.GenericHandoff.NativeComposition
  CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOriginalInterfacePrototype
  CSTTT.TargetTheory.GenericHandoff.NativeComposition.CoupledNativeKernelPrototype in
theorem legacy_rows_mass_eight (owner : Bool) (x : Frame.State) (a : Bool) (funded : x.funded=true) :
    ((TemporalFactorRules.actualRows (factorSchema owner) (input owner).temporal x a).map Prod.snd).sum=8 :=
  original_funded_row_total owner x a funded

open CSTTT.TargetTheory.GenericHandoff.NativeComposition
  CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOriginalInterfacePrototype
  CSTTT.TargetTheory.GenericHandoff.NativeComposition.CoupledNativeKernelPrototype
  CSTTT.TransportTheory in
theorem legacy_full_future_merges_kernel (owner : Bool) (names : Bool → CarrierId)
    (s t : Bool × Bool) (counter ticks : Nat) (residue : Frame.Residue) (funded : Bool)
    (word : List Bool) (trace : List (TemporalSnapshotReadout Frame.Predictive Frame.Residue Bool)) :
    fullFuture (observedModel (input owner) owner names) (context (embed s) counter ticks residue funded) word trace=
    fullFuture (observedModel (input owner) owner names) (context (embed t) counter ticks residue funded) word trace :=
  original_full_future_kernel_equal owner names s t counter ticks residue funded word trace

open CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOriginalInterfacePrototype
  CSTTT.TargetTheory.GenericHandoff.NativeComposition.CoupledNativeKernelPrototype in
structure AuditPanel : Prop where
  rejectedStrongerC1 : ¬AllStagingsUnique
  rejectedLegacyC1 : ∀ owner : Bool, ¬OriginalC1Possible (input owner)
  currentExpansion : ∀ x : Execution,
    Binding.expandedCurrent (Binding.splitExecution x false).resident.current≠
      Binding.expandedCurrent (Binding.splitExecution x true).resident.current
  flattenedJoint : ∀ (s t : CSTTT.FullNative.State) word outputs,
    Binding.emittedLaw (rationalRows (flatten model)) Binding.joint s word outputs=
      Binding.emittedLaw (rationalRows (flatten model)) Binding.joint t word outputs
  controls : ControlAudit
  historyBoundary : ∀ xs : List Execution, xs≠[] → (∀ x∈xs, sector x) →
    (∀ x∈xs, ∀ y n, (y,n)∈rawRows renewable x false → y∈xs) → False
  conditionalJoint : JointClaims.conditionedJoint [] [JointClaims.correlatedObservation false]=some (1/10) ∧
    JointClaims.conditionedBranch false [] [(JointClaims.correlatedObservation false).1]=some (1/10) ∧
    JointClaims.conditionedBranch true [] [(JointClaims.correlatedObservation false).2]=some (1/10) ∧
    (1/10:Rat)≠(1/10:Rat)*(1/10:Rat)
  conditionalRepair : ∀ word trace,
    JointClaims.conditionedJoint word trace=JointClaims.conditionedProducts word trace

theorem computed_audit_panel : AuditPanel :=
  ⟨old_stronger_c1_gate_rejected,legacy_original_c1_impossible,expanded_current_rejects_privacy,
    flattened_binding_rejected,control_audit,ClockClosure.no_finite_closed_history_carrier,
    JointClaims.conditioning_factorization_countertrace,JointClaims.conditioned_joint_sum_of_products⟩

structure AuditedAssembly : Prop where
  package : Assembly
  panel : AuditPanel

/-- Honest stronger successor: shared-raw positive assembly together with its
preserved original-interface refutation, period-two rejection and controls. -/
theorem audited_shared_raw_successor : AuditedAssembly :=
  ⟨full_original_design_assembly,computed_audit_panel⟩

end CSTTT.FullNative.OriginalPackage
