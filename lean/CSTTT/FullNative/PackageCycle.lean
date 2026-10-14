import CSTTT.FullNative.RecombinationBoundary
import CSTTT.FullNative.PublicShadow
import CSTTT.POS04.Assigned.CyclicObstruction

/-! G28: test the original POS-04 obstruction against G27's actual decoder.
The old partial primitive scopes are preserved; they are not silently reused
as scopes of G27. Every G27 clause reads the same complete decoded execution.
Literal agreement of that read on the original cycle gives a global accepted
raw package. CURRENT-only agreement is insufficient, with actual readout failure.
No raw model, channel, clause field or graph is modified. -/
namespace CSTTT.FullNative.PackageCycle
open AccountExecution PhysicalExecution SnapshotExecution SharedPackage OriginalPackage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def oldClause : Clause → CSTTT.POS04.Clause
  | .c1 => .c1 | .c2 => .c2 | .c3 => .c3 | .c4 => .c4
  | .c5 => .c5 | .c6 => .c6 | .c7 => .c7 | .c8 => .c8
def successor : Clause → Clause
  | .c1 => .c2 | .c2 => .c3 | .c3 => .c4 | .c4 => .c5
  | .c5 => .c6 | .c6 => .c7 | .c7 => .c8 | .c8 => .c1
abbrev adjacent (c d : Clause) : Prop :=
  (CSTTT.POS04.Assigned.ActualCyclePrototype.rank (oldClause c)+1)%8=
    CSTTT.POS04.Assigned.ActualCyclePrototype.rank (oldClause d) ∨
  (CSTTT.POS04.Assigned.ActualCyclePrototype.rank (oldClause d)+1)%8=
    CSTTT.POS04.Assigned.ActualCyclePrototype.rank (oldClause c)
theorem original_graph_exact (c d : Clause) : adjacent c d ↔
    CSTTT.POS04.Assigned.ActualCyclePrototype.adjacent (oldClause c) (oldClause d) := Iff.rfl
theorem original_cycle_edges (c : Clause) : adjacent c (successor c) := by cases c <;> decide +kernel

def LocalAccepted (family : Clause → Raw) : Prop := ∀ c, clause (family c) c
def LiteralCompatible (family : Clause → Raw) : Prop :=
  ∀ c d, adjacent c d → execution (family c)=execution (family d)
def GlobalRestriction (global : Raw) (family : Clause → Raw) : Prop :=
  ∀ c, execution global=execution (family c)

/-- The two actual input cells of G27 are World and resident address. Literal
agreement of both is stronger than the decoded agreement used below. -/
def RawCellCompatible (family : Clause → Raw) : Prop := ∀ c d, adjacent c d →
  (family c).world=(family d).world ∧ (family c).owner=(family d).owner

theorem raw_cells_imply_decoder_agreement (family : Clause → Raw) (h : RawCellCompatible family) :
    LiteralCompatible family := by
  intro c d edge
  obtain ⟨world,owner⟩ := h c d edge
  have equal : family c=family d := by
    cases first : family c with
    | mk w o =>
      cases second : family d with
      | mk v p =>
        simp only [first,second] at world owner
        cases world
        cases owner
        rfl
  exact congrArg execution equal

theorem all_decoders_equal (family : Clause → Raw) (h : LiteralCompatible family) (c : Clause) :
    execution (family .c1)=execution (family c) := by
  have h2 := h .c1 .c2 (original_cycle_edges .c1)
  have h3 := h2.trans (h .c2 .c3 (original_cycle_edges .c2))
  have h4 := h3.trans (h .c3 .c4 (original_cycle_edges .c3))
  have h5 := h4.trans (h .c4 .c5 (original_cycle_edges .c4))
  have h6 := h5.trans (h .c5 .c6 (original_cycle_edges .c5))
  have h7 := h6.trans (h .c6 .c7 (original_cycle_edges .c6))
  have h8 := h7.trans (h .c7 .c8 (original_cycle_edges .c7))
  cases c
  · rfl
  all_goals assumption

/-- Construct the global from an actual member of the family, not free data. -/
theorem upgraded_actual_cycle_glues (family : Clause → Raw) (accepted : LocalAccepted family)
    (compatible : LiteralCompatible family) :
    ∃ global, GlobalRestriction global family ∧ Accept global ∧
      (∀ c, clause global c) ∧
      (Historical (family .c1).world → Historical global.world) := by
  have restricts := all_decoders_equal family compatible
  refine ⟨family .c1,restricts,?_,?_,fun h => h⟩
  · obtain ⟨x,read,ready,_⟩ := accepted .c1
    exact accept_from_raw _ x read ready
  · intro c
    exact (no_independent_clause_inputs _ _ (restricts c) c).mpr (accepted c)

theorem no_upgraded_literal_cycle_obstruction (family : Clause → Raw) :
    ¬(LocalAccepted family ∧ LiteralCompatible family ∧
      ¬∃ global, GlobalRestriction global family ∧ Accept global) := by
  rintro ⟨accepted,compatible,absent⟩
  obtain ⟨global,restricts,accepts,_,_⟩ := upgraded_actual_cycle_glues family accepted compatible
  exact absent ⟨global,restricts,accepts⟩

theorem no_actual_raw_cell_cycle_obstruction (family : Clause → Raw) :
    ¬(LocalAccepted family ∧ RawCellCompatible family ∧
      ¬∃ global, GlobalRestriction global family ∧ Accept global) := by
  rintro ⟨accepted,compatible,absent⟩
  exact no_upgraded_literal_cycle_obstruction family
    ⟨accepted,raw_cells_imply_decoder_agreement family compatible,absent⟩

/-- At literal World/address coherence the selected existing member recovers
the entire Raw of every local, not only a scalar or decoded projection. -/
theorem upgraded_literal_raw_reconstruction (family : Clause → Raw) (accepted : LocalAccepted family)
    (compatible : RawCellCompatible family) :
    ∃ global, (∀ c, global=family c) ∧ Accept global ∧
      (Historical (family .c1).world → Historical global.world) := by
  have equal (c d : Clause) (edge : adjacent c d) : family c=family d := by
    obtain ⟨world,owner⟩ := compatible c d edge
    cases first : family c with
    | mk w o =>
      cases second : family d with
      | mk v p =>
        simp only [first,second] at world owner
        cases world
        cases owner
        rfl
  have h2 := equal .c1 .c2 (original_cycle_edges .c1)
  have h3 := h2.trans (equal .c2 .c3 (original_cycle_edges .c2))
  have h4 := h3.trans (equal .c3 .c4 (original_cycle_edges .c3))
  have h5 := h4.trans (equal .c4 .c5 (original_cycle_edges .c4))
  have h6 := h5.trans (equal .c5 .c6 (original_cycle_edges .c5))
  have h7 := h6.trans (equal .c6 .c7 (original_cycle_edges .c6))
  have h8 := h7.trans (equal .c7 .c8 (original_cycle_edges .c7))
  refine ⟨family .c1,?_,?_,fun h => h⟩
  · intro c
    cases c
    · rfl
    all_goals assumption
  · obtain ⟨x,read,ready,_⟩ := accepted .c1
    exact accept_from_raw _ x read ready

def installedPublic (p : Raw) (s : State) : Option Nat := do
  let x ← execution p
  let program ← x.resident.installed
  pure (program.publicLens s)

theorem actual_c6_installed_public (p : Raw) (accepted : clause p .c6) :
    installedPublic p FullInterface.rootState=some 0 := by
  obtain ⟨x,read,ready,_⟩ := accepted
  simp [installedPublic,read,ready.1.1,model,publicLens,FullInterface.rootState]

def oldC6Position : Option Nat :=
  (CSTTT.POS04.Assigned.ActualCyclePrototype.actualLocal .c6 .positions).map (fun f => f .p0w0)
theorem old_c6_position_one : oldC6Position=some 1 := by rfl

/-- The actual old C6 local accepts, but its shifted numerical public field
cannot be lifted to an admitted G27 installed-program readout at the root. -/
theorem old_position_intervention_has_no_g27_lift :
    ¬∃ p : Raw, clause p .c6 ∧ installedPublic p FullInterface.rootState=oldC6Position := by
  rintro ⟨p,accepted,equal⟩
  rw [actual_c6_installed_public p accepted,old_c6_position_one] at equal
  contradiction

def mixed : Clause → Raw := fun c => if c=.c6 then targetRaw false else sourceRaw
def currentCompatible (family : Clause → Raw) : Prop := ∀ c d, adjacent c d →
  PublicShadow.shadow (family c)=PublicShadow.shadow (family d)
def fullCode (p : Raw) : Option (Nat × FullInterface.Context) :=
  (execution p).map (fun x => FullInterface.code (frame x))

theorem mixed_actual_locals_accept : LocalAccepted mixed := by
  intro c
  by_cases sixth : c=.c6
  · subst c
    simpa only [mixed,if_pos rfl] using accepts_all_clauses _ (source_and_both_targets.2 false) Clause.c6
  · simp only [mixed,sixth,if_false]
    exact accepts_all_clauses _ source_and_both_targets.1 c

theorem actual_current_alias : PublicShadow.shadow sourceRaw=PublicShadow.shadow (targetRaw false) := by
  exact (PublicShadow.shadow_inside sourceRaw TemporalTransport.sourceAtCopy source_read
    actual_ready.1.1 actual_ready.1.2.1).trans
    (PublicShadow.shadow_inside (targetRaw false) (targetExecution false) (target_read false)
      (actual_ready.2 false).1 (actual_ready.2 false).2.1).symm

theorem mixed_current_compatible : currentCompatible mixed := by
  intro c d _
  have common (e : Clause) : PublicShadow.shadow (mixed e)=PublicShadow.shadow sourceRaw := by
    by_cases sixth : e=.c6
    · simpa only [mixed,sixth,if_true] using actual_current_alias.symm
    · simp [mixed,sixth]
  exact (common c).trans (common d).symm

theorem mixed_literal_compatibility_rejected : ¬LiteralCompatible mixed := by
  intro h
  have equal := h .c5 .c6 (original_cycle_edges .c5)
  change execution sourceRaw=execution (targetRaw false) at equal
  rw [source_read,target_read] at equal
  have owner := congrArg (fun z : Option Execution => z.map (fun x => x.resident.owner.val)) equal
  simp only [Option.map_some,PublicShadow.decoded_owner _ _ source_read,
    PublicShadow.decoded_owner _ _ (target_read false)] at owner
  change (some 0 : Option Nat)=some 1 at owner
  contradiction

theorem mixed_actual_full_readouts_conflict :
    ¬∃ global : Raw, fullCode global=fullCode (mixed .c3) ∧ fullCode global=fullCode (mixed .c6) := by
  rintro ⟨global,left,right⟩
  have equal := left.symm.trans right
  change fullCode sourceRaw=fullCode (targetRaw false) at equal
  rw [fullCode,fullCode,source_read,target_read] at equal
  have owner := congrArg (fun z : Option (Nat × FullInterface.Context) => z.map (fun q => q.2.owner.val)) equal
  simp only [Option.map_some,FullInterface.code,frame,
    PublicShadow.decoded_owner _ _ source_read,
    PublicShadow.decoded_owner _ _ (target_read false)] at owner
  change (some 0 : Option Nat)=some 1 at owner
  contradiction

theorem c3_initial_full_future_separates :
    WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (frame x))
      TemporalTransport.sourceAtCopy [] [FullInterface.observe (frame TemporalTransport.sourceAtCopy)]=1 ∧
    WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (frame x))
      (targetExecution false) [] [FullInterface.observe (frame TemporalTransport.sourceAtCopy)]=0 := by
  have different : FullInterface.observe (frame TemporalTransport.sourceAtCopy)≠
      FullInterface.observe (frame (targetExecution false)) := by
    intro same
    have owner := congrArg (TargetTheory.GenericHandoff.TemporalFactorRules.Observation.owner) same
    change TemporalTransport.sourceAtCopy.resident.owner=(targetExecution false).resident.owner at owner
    rw [PublicShadow.decoded_owner _ _ source_read,PublicShadow.decoded_owner _ _ (target_read false)] at owner
    exact (by decide +kernel : sourceRaw.owner≠(targetRaw false).owner) owner
  constructor
  · simp [WeightedFuture.law]
  · simp [WeightedFuture.law,different]

theorem current_only_gluing_countertrace : LocalAccepted mixed ∧ currentCompatible mixed ∧
    ¬LiteralCompatible mixed ∧
    ¬∃ global : Raw, fullCode global=fullCode (mixed .c3) ∧ fullCode global=fullCode (mixed .c6) :=
  ⟨mixed_actual_locals_accept,mixed_current_compatible,mixed_literal_compatibility_rejected,
    mixed_actual_full_readouts_conflict⟩

open CSTTT.POS04.Assigned in
theorem original_actual_obstruction_preserved :
    (∀ c, clauseAccept (ActualCyclePrototype.actualLocal c) .target c) ∧
    (∀ c d, ActualCyclePrototype.adjacent c d → ∀ cell,
      cell∈clauseScope .target c → cell∈clauseScope .target d →
      ActualCyclePrototype.actualLocal c cell=ActualCyclePrototype.actualLocal d cell) ∧
    ¬∃ global : Assignment, ActualCyclePrototype.GlobalRestriction global :=
  ⟨ActualCyclePrototype.all_actual_local_accepts,ActualCyclePrototype.actual_cycle_edge_compatible,
    ActualCyclePrototype.no_actual_global_restriction⟩

end CSTTT.FullNative.PackageCycle
