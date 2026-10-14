import CSTTT.Fallback.EmptyDecision

namespace CSTTT.FallbackTheory.AllOutcomeEmptyPrototype
open CSTTT.POS04 CSTTT.Objecthood.T1Audit
open CSTTT.TransportTheory CSTTT.FallbackTheory.OperationalTrace
open CSTTT.FallbackTheory.SharedOperationalSeed CSTTT.FallbackTheory.GuardedFusion
open CSTTT.FallbackTheory.EmptyDecisionPrototype
set_option autoImplicit false

-- Frozen primitive recipe: existing raw prefix, genuinely executed branching
-- and differing supported updates, then a fresh merger with disjoint actions.
def native : List (NativeDescendant.Command KState) :=
  [.fission 2 3 4,.advance 3 5 0 .p1w0,.advance 4 7 0 .p1w1]
def forked : Store KState KState := EmptyDecisionPrototype.Example.splitStore
def leftAdvanced : Store KState KState := NativeDescendant.advanced forked 3 5 .p1w0
def evolved : Store KState KState := NativeDescendant.advanced leftAdvanced 4 7 .p1w1
def credits : Credits := [(100,5),(101,7)]
def before : World KState KState := ⟨evolved,credits⟩
def receipts : List (ReceiptAncestry.Receipt KState KState) :=
  [⟨EmptyDecisionPrototype.Example.origin,.fission 2 3 4,forked⟩,
   ⟨forked,.advance 3 5 0 .p1w0,leftAdvanced⟩,
   ⟨leftAdvanced,.advance 4 7 0 .p1w1,evolved⟩]
def proposed : Program KState :=
  ⟨fun left right => if left=.p1w0 ∧ right=.p1w1 then [(.p2w1,4)] else [],4⟩
def command (outcome : KState) : GuardedFusion.Command KState := ⟨5,7,8,1,2,outcome⟩

theorem native_left_step : NativeDescendant.step (pos04RawBridge .positive) forked (.advance 3 5 0 .p1w0)=some leftAdvanced := by
  simp [NativeDescendant.step,forked,EmptyDecisionPrototype.Example.splitStore,
    NativeDescendant.split,EmptyDecisionPrototype.Example.origin,withRawTwin,
    activated,dormant,erased,captured,initial,put,switch,leftAdvanced]
  decide +kernel
theorem native_right_step : NativeDescendant.step (pos04RawBridge .positive) leftAdvanced (.advance 4 7 0 .p1w1)=some evolved := by
  simp [NativeDescendant.step,leftAdvanced,NativeDescendant.advanced,forked,
    EmptyDecisionPrototype.Example.splitStore,NativeDescendant.split,
    EmptyDecisionPrototype.Example.origin,withRawTwin,activated,dormant,erased,
    captured,initial,put,switch,evolved]
  decide +kernel

theorem actual_native_recorded : ReceiptAncestry.actualRecorded (pos04RawBridge .positive)
    EmptyDecisionPrototype.Example.inputs native=some (evolved,receipts) := by
  have forkStep : NativeDescendant.step (pos04RawBridge .positive) EmptyDecisionPrototype.Example.origin
      (.fission 2 3 4)=some forked := EmptyDecisionPrototype.Example.fission_step
  simp only [ReceiptAncestry.actualRecorded,EmptyDecisionPrototype.Example.computed_origin,
    native,ReceiptAncestry.recordedRun,forkStep,Option.bind_some]
  rfl

theorem evolved_parent_reads : before.store.read 5=some (.target KState.p1w0) ∧
    before.store.read 7=some (.target KState.p1w1) ∧ before.store.read 8=none := by
  simp [before,evolved,leftAdvanced,NativeDescendant.advanced,forked,
    EmptyDecisionPrototype.Example.splitStore,NativeDescendant.split,
    EmptyDecisionPrototype.Example.origin,withRawTwin,activated,dormant,erased,captured,initial,put]

theorem both_actual_marginals :
    actionRow .target .p1w0 .cw=[(.inK .p2w1,4)] ∧
    actionRow .target .p1w1 .ccw=[(.inK .p5w0,4)] ∧
    (pos04RawBridge .positive).targetActionStep .p1w0 1 .p2w1=4 ∧
    (pos04RawBridge .positive).targetActionStep .p1w1 2 .p5w0=4 := by
  decide +kernel

theorem no_common_native_outcome (outcome : KState) :
    ¬(0<(pos04RawBridge .positive).targetActionStep .p1w0 1 outcome ∧
      0<(pos04RawBridge .positive).targetActionStep .p1w1 2 outcome) := by
  cases outcome <;> decide +kernel

-- ANY joint program fails, not only a zero weight in our proposed row.
theorem every_program_incompatible (program : Program KState) (outcome : KState) :
    compatible (pos04RawBridge .positive) program (command outcome) .p1w0 .p1w1=false := by
  cases accepted : compatible (pos04RawBridge .positive) program (command outcome) .p1w0 .p1w1 with
  | false => rfl
  | true =>
    have support := (compatible_iff _ _ _ _ _).mp accepted
    exact False.elim (no_common_native_outcome outcome ⟨support.2.1,support.2.2⟩)

theorem structural_available (outcome : KState) :
    structuralGuard proposed before (command outcome) .p1w0 .p1w1=true := by
  change structuralGuard proposed before (command .p0w0) .p1w0 .p1w1=true
  decide +kernel

theorem every_outcome_empty_step (outcome : KState) :
    settle (pos04RawBridge .positive) proposed before (command outcome)=some (before,false) := by
  have actual := settle_exact (pos04RawBridge .positive) proposed before (command outcome)
    .p1w0 .p1w1 evolved_parent_reads.1 evolved_parent_reads.2.1 (structural_available outcome)
  simpa [every_program_incompatible] using actual

theorem actual_every_outcome_settlement (outcome : KState) :
    actualSettlement (pos04RawBridge .positive) EmptyDecisionPrototype.Example.inputs native
      (some proposed) (some credits) (command outcome)=some ((before,receipts),false) := by
  simp only [actualSettlement,actual_native_recorded]
  change (settle (pos04RawBridge .positive) proposed before (command outcome)).bind
    (fun result => some ((result.1,receipts),result.2))=some ((before,receipts),false)
  rw [every_outcome_empty_step]
  rfl

theorem actual_both_branch_ancestry (outcome : KState) :
    settledAncestry (pos04RawBridge .positive) EmptyDecisionPrototype.Example.inputs native
      (some proposed) (some credits) (command outcome) 0 5=some true ∧
    settledAncestry (pos04RawBridge .positive) EmptyDecisionPrototype.Example.inputs native
      (some proposed) (some credits) (command outcome) 0 7=some true := by
  constructor
  all_goals apply (settled_ancestry_true_iff _ _ _ _ _ _ _ _).mpr
  all_goals refine ⟨before,receipts,false,actual_every_outcome_settlement outcome,2,
    EmptyDecisionPrototype.Example.actual_seed,Or.inr (?_)⟩
  · apply Path.extend (y := 3) (Path.one ?_) ?_
    · simp [combinedLedger,receipts,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges,fusionLedger]
    · simp [combinedLedger,receipts,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges,fusionLedger]
  · apply Path.extend (y := 4) (Path.one ?_) ?_
    · simp [combinedLedger,receipts,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges,fusionLedger]
    · simp [combinedLedger,receipts,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges,fusionLedger]

theorem fresh_output_no_seed (source : Nat) :
    ¬Seed (pos04RawBridge .positive) EmptyDecisionPrototype.Example.inputs source 8 := by
  apply disconnected_target_excludes_all _ _ EmptyDecisionPrototype.Example.origin
    EmptyDecisionPrototype.Example.computed_origin 8
  intro predecessor
  simp [EmptyDecisionPrototype.Example.origin,withRawTwin,activated,dormant,erased,captured,initial]

theorem fresh_output_no_ledger_path (source : Nat) : ¬Path (combinedLedger receipts []) source 8 := by
  apply no_incoming_excludes
  intro predecessor
  simp [combinedLedger,receipts,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges,fusionLedger]

theorem actual_every_outcome_ancestry_false (source : Nat) (outcome : KState) :
    settledAncestry (pos04RawBridge .positive) EmptyDecisionPrototype.Example.inputs native
      (some proposed) (some credits) (command outcome) source 8=some false := by
  apply (settled_ancestry_false_iff _ _ _ _ _ _ _ _).mpr
  refine ⟨before,receipts,false,actual_every_outcome_settlement outcome,?_⟩
  rintro ⟨seeded,seed,equal|path⟩
  · subst seeded
    exact fresh_output_no_seed source seed
  · exact fresh_output_no_ledger_path seeded path

theorem every_program_guard_false (program : Program KState) (outcome : KState) :
    guard (pos04RawBridge .positive) program before (command outcome) .p1w0 .p1w1=false := by
  cases accepted : guard (pos04RawBridge .positive) program before (command outcome) .p1w0 .p1w1 with
  | false => rfl
  | true =>
    have incompatible := (original_guard_split _ _ _ _ _ _).mp accepted |>.2
    rw [every_program_incompatible] at incompatible
    cases incompatible

theorem every_program_original_step_rejected (program : Program KState) (outcome : KState) :
    GuardedFusion.step (pos04RawBridge .positive) program before (command outcome)=none := by
  have leftRead : before.store.read (command outcome).left=some (.target KState.p1w0) := evolved_parent_reads.1
  have rightRead : before.store.read (command outcome).right=some (.target KState.p1w1) := evolved_parent_reads.2.1
  simp [GuardedFusion.step,leftRead,rightRead,every_program_guard_false]

theorem actual_native_executed : NativeDescendant.extendActual (pos04RawBridge .positive)
    EmptyDecisionPrototype.Example.inputs native=some evolved := by
  rw [←ReceiptAncestry.actual_recorded_exact,actual_native_recorded]
  rfl

-- ALL partial program/credit assignments reject the original merger directly.
-- Even a different normalized joint program cannot overcome native disjointness.
theorem actual_all_partial_programs_reject (program : Option (Program KState))
    (rawCredits : Option Credits) (outcome : KState) :
    actualRun (pos04RawBridge .positive) EmptyDecisionPrototype.Example.inputs native
      program rawCredits [command outcome]=none := by
  cases program with
  | none => simp [actualRun]
  | some program =>
    cases rawCredits with
    | none => simp [actualRun]
    | some rawCredits =>
      have nativeRun : NativeDescendant.run (pos04RawBridge .positive) EmptyDecisionPrototype.Example.origin native=some evolved := by
        simpa [NativeDescendant.extendActual,EmptyDecisionPrototype.Example.computed_origin] using actual_native_executed
      have zero : GuardedFusion.step (pos04RawBridge .positive) program ⟨evolved,rawCredits⟩ (command outcome)=none := by
        have hl : evolved.read (command outcome).left=some (.target KState.p1w0) := evolved_parent_reads.1
        have hr : evolved.read (command outcome).right=some (.target KState.p1w1) := evolved_parent_reads.2.1
        have rejected : guard (pos04RawBridge .positive) program ⟨evolved,rawCredits⟩ (command outcome) .p1w0 .p1w1=false := by
          cases accepted : guard (pos04RawBridge .positive) program ⟨evolved,rawCredits⟩ (command outcome) .p1w0 .p1w1 with
          | false => rfl
          | true =>
            have incompatible := (original_guard_split _ _ _ _ _ _).mp accepted |>.2
            rw [every_program_incompatible] at incompatible
            cases incompatible
        simp [GuardedFusion.step,hl,hr,rejected]
      simp [actualRun,EmptyDecisionPrototype.Example.computed_origin,nativeRun,GuardedFusion.run,zero]

-- Same actual source ancestry, updated branches and genuinely empty fresh
-- output for EVERY candidate common target state, with no unsupported-row input.
theorem actual_all_outcome_empty_return (outcome : KState) :
    actualSettlement (pos04RawBridge .positive) EmptyDecisionPrototype.Example.inputs native
      (some proposed) (some credits) (command outcome)=some ((before,receipts),false) ∧
    settledAncestry (pos04RawBridge .positive) EmptyDecisionPrototype.Example.inputs native
      (some proposed) (some credits) (command outcome) 0 5=some true ∧
    settledAncestry (pos04RawBridge .positive) EmptyDecisionPrototype.Example.inputs native
      (some proposed) (some credits) (command outcome) 0 7=some true ∧
    before.store.read 8=none ∧
    (∀ source,settledAncestry (pos04RawBridge .positive) EmptyDecisionPrototype.Example.inputs native
      (some proposed) (some credits) (command outcome) source 8=some false) ∧
    ∀ program : Program KState,GuardedFusion.step (pos04RawBridge .positive) program before (command outcome)=none :=
  ⟨actual_every_outcome_settlement outcome,(actual_both_branch_ancestry outcome).1,
    (actual_both_branch_ancestry outcome).2,evolved_parent_reads.2.2,
    fun source => actual_every_outcome_ancestry_false source outcome,
    fun program => every_program_original_step_rejected program outcome⟩

end CSTTT.FallbackTheory.AllOutcomeEmptyPrototype
