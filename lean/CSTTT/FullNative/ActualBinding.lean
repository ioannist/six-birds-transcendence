import CSTTT.FullNative.CurrentExposure

/-! Derived all-word and actual-execution obligations for frozen FULL-NATIVE-01. -/
namespace CSTTT.FullNative.Binding
set_option autoImplicit false
set_option maxHeartbeats 8000000

def splitState (s : State) (right : Bool) : State := ⟨false,false,right,false,!s.phase⟩

def splitExecution (x : PhysicalExecution.Execution) (right : Bool) : PhysicalExecution.Execution :=
  PhysicalExecution.advance AccountExecution.renewable x false (splitState x.resident.current right)
    (weight x.resident.current false right)

theorem split_supported (s : State) (right : Bool) :
    (splitState s right,weight s false right)∈rows s false ∧ 0<weight s false right := by
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases right <;> decide +kernel

theorem actual_split_supported (x : PhysicalExecution.Execution) (h : PhysicalExecution.sector x)
    (right : Bool) : (splitExecution x right,weight x.resident.current false right)∈
      PhysicalExecution.rawRows AccountExecution.renewable x false := by
  rw [PhysicalExecution.sector_rows x h false]
  exact List.mem_map.mpr ⟨(splitState x.resident.current right,weight x.resident.current false right),
    (split_supported x.resident.current right).1,rfl⟩

theorem actual_split_context (x : PhysicalExecution.Execution) (h : PhysicalExecution.sector x) :
    (PhysicalExecution.frame (splitExecution x false)).context=
      (PhysicalExecution.frame (splitExecution x true)).context := by
  simp only [splitExecution,PhysicalExecution.frame_advance x h]
  rfl

theorem split_promotion (s : State) :
    currentPublic (splitState s false)=currentPublic (splitState s true) ∧
    classes model (splitState s false)≠classes model (splitState s true) := by
  constructor
  · rw [inside_public _ rfl,inside_public _ rfl]
  · simp only [first_profile_equation,splitState,classFormula,kernelCode,bit]
    cases h : s.phase <;> decide +kernel

theorem historical_source_split :
    PhysicalExecution.Reachable AccountExecution.renewable (splitExecution PhysicalExecution.source false) ∧
    PhysicalExecution.Reachable AccountExecution.renewable (splitExecution PhysicalExecution.source true) :=
  ⟨PhysicalExecution.Reachable.step (a:=false) (n:=weight PhysicalExecution.source.resident.current false false)
    .initial (actual_split_supported _ PhysicalExecution.source_sector false),
  PhysicalExecution.Reachable.step (a:=false) (n:=weight PhysicalExecution.source.resident.current false true)
    .initial (actual_split_supported _ PhysicalExecution.source_sector true)⟩

theorem split_joint_gap (s : State) :
    emittedLaw (rationalRows model) joint (splitState s false) [false] [0]=1/8 ∧
    emittedLaw (rationalRows model) joint (splitState s true) [false] [0]=3/8 := by
  cases s with
  | mk p u v r phase => dsimp only [splitState]; cases phase <;> decide +kernel

theorem actual_split_sectors (x : PhysicalExecution.Execution) (h : PhysicalExecution.sector x)
    (right : Bool) : PhysicalExecution.sector (splitExecution x right) :=
  PhysicalExecution.sector_preserved x h false _ _

theorem actual_split_current (x : PhysicalExecution.Execution) (h : PhysicalExecution.sector x) :
    actualCurrent (splitExecution x false)=actualCurrent (splitExecution x true) := by
  rw [actual_current_sector _ (actual_split_sectors x h false),
    actual_current_sector _ (actual_split_sectors x h true)]
  exact (split_promotion x.resident.current).1

theorem actual_split_binding (x : PhysicalExecution.Execution) (h : PhysicalExecution.sector x) :
    (∀ right word outputs,
      emittedLaw (PhysicalExecution.normalizedRows AccountExecution.renewable)
        (fun y => branch right y.resident.current) (splitExecution x false) word outputs=
      emittedLaw (PhysicalExecution.normalizedRows AccountExecution.renewable)
        (fun y => branch right y.resident.current) (splitExecution x true) word outputs) ∧
    emittedLaw (PhysicalExecution.normalizedRows AccountExecution.renewable)
      (fun y => joint y.resident.current) (splitExecution x false) [false] [0]≠
    emittedLaw (PhysicalExecution.normalizedRows AccountExecution.renewable)
      (fun y => joint y.resident.current) (splitExecution x true) [false] [0] := by
  constructor
  · intro right word outputs
    rw [actual_emitted_law _ _ (actual_split_sectors x h false),
      actual_emitted_law _ _ (actual_split_sectors x h true),branch_all_wordsR,branch_all_wordsR]
  · rw [actual_emitted_law _ _ (actual_split_sectors x h false),
      actual_emitted_law _ _ (actual_split_sectors x h true)]
    change emittedLaw (rationalRows model) joint (splitState x.resident.current false) [false] [0]≠
      emittedLaw (rationalRows model) joint (splitState x.resident.current true) [false] [0]
    rw [(split_joint_gap x.resident.current).1,(split_joint_gap x.resident.current).2]
    decide +kernel

/-- Non-exposure is checked on genuine supported source histories. -/
theorem no_historical_predictor_factor :
    ¬ ∃ g : Nat × Nat × Nat → Nat, ∀ x,
      PhysicalExecution.Reachable AccountExecution.renewable x → x.resident.current.outside=false →
      classes model x.resident.current=g (actualCurrent x) := by
  rintro ⟨g,h⟩
  have left:=h _ historical_source_split.1 rfl
  have right:=h _ historical_source_split.2 rfl
  rw [actual_split_current _ PhysicalExecution.source_sector] at left
  have eq:=left.trans right.symm
  exact (split_promotion PhysicalExecution.source.resident.current).2 eq

open SnapshotExecution PhysicalExecution AccountExecution

theorem world_split_supported (w : World) (o : Owner) (p : Local)
    (cell : w.carriers o=some p) (owner : p.owner=o) (funded : sector ⟨w.accounts,p⟩)
    (right : Bool) :
    (mount w o (splitExecution ⟨w.accounts,p⟩ right),weight p.current false right)∈
      nativeRows renewable w o false := by
  simp only [nativeRows,cell,owner,if_true]
  exact List.mem_map.mpr ⟨(splitExecution ⟨w.accounts,p⟩ right,weight p.current false right),
    actual_split_supported _ funded right,rfl⟩

theorem world_split_historical (w : World) (history : Historical w) (o : Owner) (p : Local)
    (cell : w.carriers o=some p) (owner : p.owner=o) (funded : sector ⟨w.accounts,p⟩)
    (right : Bool) : Historical (mount w o (splitExecution ⟨w.accounts,p⟩ right)) :=
  Historical.native (o:=o) (a:=false) (n:=weight p.current false right) history
    (world_split_supported w o p cell owner funded right)

theorem both_targets_historical_splits (right : Bool) :
    Historical (mount autonomousSiblings 1
      (splitExecution ⟨autonomousSiblings.accounts,activatedLocal 1⟩ right)) ∧
    Historical (mount autonomousSiblings 2
      (splitExecution ⟨autonomousSiblings.accounts,activatedLocal 2⟩ right)) :=
  ⟨world_split_historical _ actual_snapshot_history 1 _ withdrawn_generators.2.2.1 rfl
      siblings_actual_sectors.1 right,
    world_split_historical _ actual_snapshot_history 2 _ withdrawn_generators.2.2.2.1 rfl
      siblings_actual_sectors.2 right⟩

theorem first_target_binding :
    (∀ right word outputs,
      emittedLaw (normalizedRows renewable) (fun y => branch right y.resident.current)
        (splitExecution ⟨autonomousSiblings.accounts,activatedLocal 1⟩ false) word outputs=
      emittedLaw (normalizedRows renewable) (fun y => branch right y.resident.current)
        (splitExecution ⟨autonomousSiblings.accounts,activatedLocal 1⟩ true) word outputs) ∧
    emittedLaw (normalizedRows renewable) (fun y => joint y.resident.current)
      (splitExecution ⟨autonomousSiblings.accounts,activatedLocal 1⟩ false) [false] [0]≠
    emittedLaw (normalizedRows renewable) (fun y => joint y.resident.current)
      (splitExecution ⟨autonomousSiblings.accounts,activatedLocal 1⟩ true) [false] [0] :=
  actual_split_binding _ siblings_actual_sectors.1

theorem second_target_binding :
    (∀ right word outputs,
      emittedLaw (normalizedRows renewable) (fun y => branch right y.resident.current)
        (splitExecution ⟨autonomousSiblings.accounts,activatedLocal 2⟩ false) word outputs=
      emittedLaw (normalizedRows renewable) (fun y => branch right y.resident.current)
        (splitExecution ⟨autonomousSiblings.accounts,activatedLocal 2⟩ true) word outputs) ∧
    emittedLaw (normalizedRows renewable) (fun y => joint y.resident.current)
      (splitExecution ⟨autonomousSiblings.accounts,activatedLocal 2⟩ false) [false] [0]≠
    emittedLaw (normalizedRows renewable) (fun y => joint y.resident.current)
      (splitExecution ⟨autonomousSiblings.accounts,activatedLocal 2⟩ true) [false] [0] :=
  actual_split_binding _ siblings_actual_sectors.2

end CSTTT.FullNative.Binding
