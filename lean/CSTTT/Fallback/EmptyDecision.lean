import CSTTT.Fallback.GuardedFusion

namespace CSTTT.FallbackTheory.EmptyDecisionPrototype
open CSTTT.TransportTheory
open CSTTT.FallbackTheory.OperationalTrace
open CSTTT.FallbackTheory.SharedOperationalSeed
open CSTTT.FallbackTheory.GuardedFusion
set_option autoImplicit false
variable {H S T E R SC TC RR M : Type} [DecidableEq S] [DecidableEq T]
-- All new declarations are class (b). A successful EMPTY decision is distinct from unavailable execution.
-- A well-formed normalized proposal must still satisfy every structural/token/activity/freshness condition.
def structuralGuard (program : Program T) (world : World S T) (command : GuardedFusion.Command T) (left right : T) : Bool :=
  rowValid program left right && decide (command.left≠command.right) && (world.store.read command.target).isNone &&
    world.store.active command.left && world.store.active command.right && decide ((world.credits.map Prod.fst).Nodup) &&
    world.credits.all (fun entry => housed world.store entry.2) && allocated world.credits command.left && allocated world.credits command.right
-- Only the common supported requested outcome can be fused; incompatibility is read from actual raw rows.
def compatible (b : RawBridge H S T E R SC TC RR M) (program : Program T) (command : GuardedFusion.Command T) (left right : T) : Bool :=
  decide (0<jointWeight program left right command.outcome) &&
    decide (0<b.targetActionStep left command.leftAction command.outcome) &&
    decide (0<b.targetActionStep right command.rightAction command.outcome)
omit [DecidableEq S] [DecidableEq T] in
theorem structural_guard_iff (program : Program T) (world : World S T) (command : GuardedFusion.Command T) (left right : T) :
    structuralGuard program world command left right=true ↔
      rowValid program left right=true ∧ command.left≠command.right ∧ world.store.read command.target=none ∧
      world.store.active command.left=true ∧ world.store.active command.right=true ∧
      (world.credits.map Prod.fst).Nodup ∧ (∀ entry∈world.credits,housed world.store entry.2=true) ∧
      allocated world.credits command.left=true ∧ allocated world.credits command.right=true := by
  simp [structuralGuard,List.all_eq_true,and_assoc]
omit [DecidableEq S] in
theorem compatible_iff (b : RawBridge H S T E R SC TC RR M) (program : Program T) (command : GuardedFusion.Command T) (left right : T) :
    compatible b program command left right=true ↔
      0<jointWeight program left right command.outcome ∧
      0<b.targetActionStep left command.leftAction command.outcome ∧
      0<b.targetActionStep right command.rightAction command.outcome := by
  simp [compatible,and_assoc]
theorem original_guard_split (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : GuardedFusion.Command T) (left right : T) :
    guard b program world command left right=true ↔
      structuralGuard program world command left right=true ∧ compatible b program command left right=true := by
  rw [guard_iff,structural_guard_iff,compatible_iff]
  constructor
  · rintro ⟨row,joint,leftSupport,rightSupport,distinct,fresh,leftActive,rightActive,exclusive,housing,leftAllocation,rightAllocation⟩
    exact ⟨⟨row,distinct,fresh,leftActive,rightActive,exclusive,housing,leftAllocation,rightAllocation⟩,joint,leftSupport,rightSupport⟩
  · rintro ⟨⟨row,distinct,fresh,leftActive,rightActive,exclusive,housing,leftAllocation,rightAllocation⟩,joint,leftSupport,rightSupport⟩
    exact ⟨row,joint,leftSupport,rightSupport,distinct,fresh,leftActive,rightActive,exclusive,housing,leftAllocation,rightAllocation⟩
-- true denotes an accepted merger; false denotes an available, structurally valid empty proposal.
-- Neither missing primitives nor malformed structural proposals produce an empty success.
def settle (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : GuardedFusion.Command T) : Option (World S T × Bool) := do
  let .target left ← world.store.read command.left | none
  let .target right ← world.store.read command.right | none
  if structuralGuard program world command left right then
    if compatible b program command left right then some (merged world command,true) else some (world,false)
  else none
omit [DecidableEq S] in
theorem settle_exact (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : GuardedFusion.Command T) (left right : T)
    (hl : world.store.read command.left=some (.target left)) (hr : world.store.read command.right=some (.target right))
    (structural : structuralGuard program world command left right=true) :
    settle b program world command=some (if compatible b program command left right then (merged world command,true) else (world,false)) := by
  cases hc : compatible b program command left right <;> simp [settle,hl,hr,structural,hc]
theorem settle_return (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world finished : World S T) (command : GuardedFusion.Command T) (kind : Bool)
    (settled : settle b program world command=some (finished,kind)) :
    ∃ left right,world.store.read command.left=some (.target left) ∧ world.store.read command.right=some (.target right) ∧
      structuralGuard program world command left right=true ∧
      ((kind=true ∧ guard b program world command left right=true ∧ finished=merged world command) ∨
        (kind=false ∧ compatible b program command left right=false ∧ finished=world ∧ finished.store.read command.target=none)) := by
  cases hl : world.store.read command.left with
  | none => simp [settle,hl] at settled
  | some content =>
    cases content with
    | source payload => simp [settle,hl] at settled
    | record address time payload => simp [settle,hl] at settled
    | target left =>
      cases hr : world.store.read command.right with
      | none => simp [settle,hl,hr] at settled
      | some content =>
        cases content with
        | source payload => simp [settle,hl,hr] at settled
        | record address time payload => simp [settle,hl,hr] at settled
        | target right =>
          cases hs : structuralGuard program world command left right with
          | false => simp [settle,hl,hr,hs] at settled
          | true =>
            cases hc : compatible b program command left right with
            | false =>
              have equal : (world,false)=(finished,kind) := by simpa [settle,hl,hr,hs,hc] using settled
              cases equal
              exact ⟨left,right,rfl,rfl,hs,Or.inr ⟨rfl,hc,rfl,(structural_guard_iff program world command left right).mp hs |>.2.2.1⟩⟩
            | true =>
              have equal : (merged world command,true)=(finished,kind) := by simpa [settle,hl,hr,hs,hc] using settled
              cases equal
              exact ⟨left,right,rfl,rfl,hs,Or.inl ⟨rfl,(original_guard_split b program world command left right).mpr ⟨hs,hc⟩,rfl⟩⟩
-- An accepted settlement exactly executes the original guarded step; an empty settlement leaves a genuinely absent fresh target.
theorem settled_run (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world finished : World S T) (command : GuardedFusion.Command T) (kind : Bool)
    (settled : settle b program world command=some (finished,kind)) :
    run b program world (if kind then [command] else [])=some finished := by
  obtain ⟨left,right,hl,hr,_,fused|empty⟩ := settle_return b program world finished command kind settled
  · obtain ⟨rfl,accepted,rfl⟩ := fused
    simp [GuardedFusion.run,step_exact b program world command left right hl hr accepted]
  · obtain ⟨rfl,_,rfl,_⟩ := empty
    rfl
-- Only the raw source-checked prefix and actual recorder can construct the initial world and receipts.
def actualSettlement (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T)) (rawCredits : Option Credits)
    (command : GuardedFusion.Command T) : Option ((World S T × List (ReceiptAncestry.Receipt S T)) × Bool) := do
  let program ← rawProgram
  let credits ← rawCredits
  let (store,receipts) ← ReceiptAncestry.actualRecorded b inputs native
  let (finished,kind) ← settle b program ⟨store,credits⟩ command
  some ((finished,receipts),kind)
theorem missing_program_rejects (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (credits : Option Credits) (command : GuardedFusion.Command T) :
    actualSettlement b inputs native none credits command=none := by simp [actualSettlement]
theorem missing_credits_rejects (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T)) (command : GuardedFusion.Command T) :
    actualSettlement b inputs native program none command=none := by cases program <;> simp [actualSettlement]

-- Every optional settlement is characterized by actual typed parents and structural admissibility, on arbitrary partial stores.
omit [DecidableEq S] in
theorem settlement_available_iff (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : GuardedFusion.Command T) :
    (settle b program world command).isSome=true ↔ ∃ left right,
      world.store.read command.left=some (.target left) ∧ world.store.read command.right=some (.target right) ∧
      structuralGuard program world command left right=true := by
  cases hl : world.store.read command.left with
  | none => simp [settle,hl]
  | some content =>
    cases content with
    | source payload => simp [settle,hl]
    | record address time payload => simp [settle,hl]
    | target left =>
      cases hr : world.store.read command.right with
      | none => simp [settle,hl,hr]
      | some content =>
        cases content with
        | source payload => simp [settle,hl,hr]
        | record address time payload => simp [settle,hl,hr]
        | target right =>
          cases hc : compatible b program command left right <;>
            cases hs : structuralGuard program world command left right <;> simp [settle,hl,hr,hc,hs]
-- The EMPTY readout is exact and available; it is never a renamed unavailable execution.
theorem empty_settlement_iff (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world finished : World S T) (command : GuardedFusion.Command T) :
    settle b program world command=some (finished,false) ↔ ∃ left right,
      world.store.read command.left=some (.target left) ∧ world.store.read command.right=some (.target right) ∧
      structuralGuard program world command left right=true ∧ compatible b program command left right=false ∧ finished=world := by
  constructor
  · intro settled
    obtain ⟨left,right,hl,hr,structural,fused|empty⟩ := settle_return b program world finished command false settled
    · simp at fused
    · exact ⟨left,right,hl,hr,structural,empty.2.1,empty.2.2.1⟩
  · rintro ⟨left,right,hl,hr,structural,incompatible,rfl⟩
    simpa only [incompatible,Bool.false_eq_true,ite_false] using settle_exact b program finished command left right hl hr structural
-- Returned native receipts and the actual fusion choice justify the exact selected original execution stream.
theorem actual_settlement_recorded (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T)) (rawCredits : Option Credits)
    (command : GuardedFusion.Command T) (finished : World S T) (receipts : List (ReceiptAncestry.Receipt S T)) (kind : Bool)
    (settled : actualSettlement b inputs native rawProgram rawCredits command=some ((finished,receipts),kind)) :
    actualRecordedFusion b inputs native rawProgram rawCredits (if kind then [command] else [])=some (finished,receipts) := by
  cases hp : rawProgram with
  | none => simp [actualSettlement,hp] at settled
  | some program =>
    cases hc : rawCredits with
    | none => simp [actualSettlement,hp,hc] at settled
    | some credits =>
      cases hn : ReceiptAncestry.actualRecorded b inputs native with
      | none => simp [actualSettlement,hp,hc,hn] at settled
      | some result =>
        obtain ⟨store,nativeReceipts⟩ := result
        cases hs : settle b program ⟨store,credits⟩ command with
        | none => simp [actualSettlement,hp,hc,hn,hs] at settled
        | some value =>
          obtain ⟨finalWorld,tag⟩ := value
          have equal : ((finalWorld,nativeReceipts),tag)=((finished,receipts),kind) := by
            simpa [actualSettlement,hp,hc,hn,hs] using settled
          cases equal
          simp [actualRecordedFusion,hn,settled_run b program ⟨store,credits⟩ finished command kind hs]
-- Scientific ancestry still uses the actual cached predictive Seed and only the actually accepted receipt/merger ledger.
def settledAncestry (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T)) (credits : Option Credits)
    (command : GuardedFusion.Command T) (source target : Nat) : Option Bool :=
  (actualSettlement b inputs native program credits command).map (fun result =>
    finishedAncestry b inputs (if result.2 then [command] else []) result.1 source target)
theorem settled_ancestry_agrees (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T)) (credits : Option Credits)
    (command : GuardedFusion.Command T) (finished : World S T) (receipts : List (ReceiptAncestry.Receipt S T)) (kind : Bool)
    (settled : actualSettlement b inputs native program credits command=some ((finished,receipts),kind)) (source target : Nat) :
    settledAncestry b inputs native program credits command source target=
      actualAncestry b inputs native program credits (if kind then [command] else []) source target := by
  have recorded := actual_settlement_recorded b inputs native program credits command finished receipts kind settled
  simp [settledAncestry,settled,actualAncestry,recorded]
theorem settled_ancestry_none_iff (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T)) (credits : Option Credits)
    (command : GuardedFusion.Command T) (source target : Nat) :
    settledAncestry b inputs native program credits command source target=none ↔
      actualSettlement b inputs native program credits command=none := by
  simp [settledAncestry]
-- A genuine positive quote has the exact same least Seed/accepted-ledger semantics on every partial input.
theorem settled_ancestry_true_iff (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T)) (credits : Option Credits)
    (command : GuardedFusion.Command T) (source target : Nat) :
    settledAncestry b inputs native program credits command source target=some true ↔
      ∃ finished receipts kind,actualSettlement b inputs native program credits command=some ((finished,receipts),kind) ∧
        Provenance b inputs (combinedLedger receipts (if kind then [command] else [])) source target := by
  constructor
  · intro positive
    obtain ⟨⟨⟨finished,receipts⟩,kind⟩,settled,bit⟩ := Option.map_eq_some_iff.mp positive
    have recorded := actual_settlement_recorded b inputs native program credits command finished receipts kind settled
    have actualPositive : actualAncestry b inputs native program credits (if kind then [command] else []) source target=some true := by
      simpa [actualAncestry,recorded] using congrArg some bit
    exact ⟨finished,receipts,kind,settled,(actual_relation_exact b inputs native program credits _ finished receipts recorded source target).mp actualPositive⟩
  · rintro ⟨finished,receipts,kind,settled,provenance⟩
    rw [settled_ancestry_agrees b inputs native program credits command finished receipts kind settled source target]
    exact (actual_relation_exact b inputs native program credits _ finished receipts
      (actual_settlement_recorded b inputs native program credits command finished receipts kind settled) source target).mpr provenance

-- Available false ancestry is the negation of actual least predictive provenance, not a failed sufficient test.
theorem settled_ancestry_false_iff (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T)) (credits : Option Credits)
    (command : GuardedFusion.Command T) (source target : Nat) :
    settledAncestry b inputs native program credits command source target=some false ↔
      ∃ finished receipts kind,actualSettlement b inputs native program credits command=some ((finished,receipts),kind) ∧
        ¬Provenance b inputs (combinedLedger receipts (if kind then [command] else [])) source target := by
  constructor
  · intro negative
    obtain ⟨⟨⟨finished,receipts⟩,kind⟩,settled,bit⟩ := Option.map_eq_some_iff.mp negative
    refine ⟨finished,receipts,kind,settled,?_⟩
    intro provenance
    have positive := (settled_ancestry_true_iff b inputs native program credits command source target).mpr
      ⟨finished,receipts,kind,settled,provenance⟩
    rw [negative] at positive
    cases positive
  · rintro ⟨finished,receipts,kind,settled,absent⟩
    have recorded := actual_settlement_recorded b inputs native program credits command finished receipts kind settled
    cases hb : finishedAncestry b inputs (if kind then [command] else []) (finished,receipts) source target with
    | false => simp [settledAncestry,settled,hb]
    | true =>
      have positive : actualAncestry b inputs native program credits (if kind then [command] else []) source target=some true := by
        simp [actualAncestry,recorded,hb]
      exact False.elim (absent ((actual_relation_exact b inputs native program credits _ finished receipts recorded source target).mp positive))
-- Missing consumed source prefix cannot be relabeled an empty success.
theorem missing_prefix_rejects (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T)) (credits : Option Credits)
    (command : GuardedFusion.Command T) (missing : computedStore inputs=none) :
    actualSettlement b inputs native program credits command=none := by
  cases program <;> cases credits <;> simp [actualSettlement,ReceiptAncestry.actualRecorded,missing]
-- An invalid structural proposal is unavailable regardless of compatibility and never produces an empty world.
omit [DecidableEq S] in
theorem invalid_structural_rejected (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : GuardedFusion.Command T)
    (invalid : ∀ left right,structuralGuard program world command left right=false) : settle b program world command=none := by
  cases settled : settle b program world command with
  | none => rfl
  | some result =>
    have available : (settle b program world command).isSome=true := by rw [settled]; rfl
    obtain ⟨left,right,_,_,structural⟩ := (settlement_available_iff b program world command).mp available
    rw [invalid left right] at structural
    cases structural
-- Duplicate primitive credit IDs refute actual settlement, not just its merger subcase.
omit [DecidableEq S] in
theorem duplicate_credits_rejected (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : GuardedFusion.Command T) (duplicate : ¬(world.credits.map Prod.fst).Nodup) :
    settle b program world command=none := by
  apply invalid_structural_rejected
  intro left right
  simp [structuralGuard,duplicate]

-- The successful result reconstructs its actual optional pre-settlement world and exact raw program, never a caller-supplied world.
theorem actual_settlement_base (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T)) (rawCredits : Option Credits)
    (command : GuardedFusion.Command T) (finished : World S T) (receipts : List (ReceiptAncestry.Receipt S T)) (kind : Bool)
    (settled : actualSettlement b inputs native rawProgram rawCredits command=some ((finished,receipts),kind)) :
    ∃ program before,rawProgram=some program ∧ actualRecordedFusion b inputs native rawProgram rawCredits []=some (before,receipts) ∧
      settle b program before command=some (finished,kind) := by
  cases hp : rawProgram with
  | none => simp [actualSettlement,hp] at settled
  | some program =>
    cases hc : rawCredits with
    | none => simp [actualSettlement,hp,hc] at settled
    | some credits =>
      cases hn : ReceiptAncestry.actualRecorded b inputs native with
      | none => simp [actualSettlement,hp,hc,hn] at settled
      | some result =>
        obtain ⟨store,nativeReceipts⟩ := result
        cases hs : settle b program ⟨store,credits⟩ command with
        | none => simp [actualSettlement,hp,hc,hn,hs] at settled
        | some value =>
          obtain ⟨finalWorld,tag⟩ := value
          have equal : ((finalWorld,nativeReceipts),tag)=((finished,receipts),kind) := by
            simpa [actualSettlement,hp,hc,hn,hs] using settled
          cases equal
          exact ⟨program,⟨store,credits⟩,rfl,by simp [actualRecordedFusion,hn,GuardedFusion.run],hs⟩
-- An actual EMPTY proposal supplies a successful unchanged native world and a genuinely empty requested target read.
theorem actual_empty_return (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T)) (credits : Option Credits)
    (command : GuardedFusion.Command T) (finished : World S T) (receipts : List (ReceiptAncestry.Receipt S T))
    (settled : actualSettlement b inputs native program credits command=some ((finished,receipts),false)) :
    actualRecordedFusion b inputs native program credits []=some (finished,receipts) ∧ finished.store.read command.target=none := by
  obtain ⟨actualProgram,before,_,recorded,settledStep⟩ := actual_settlement_base b inputs native program credits command finished receipts false settled
  obtain ⟨left,right,hl,hr,structural,incompatible,equal⟩ := (empty_settlement_iff b actualProgram before finished command).mp settledStep
  rw [equal]
  exact ⟨recorded,(structural_guard_iff actualProgram before command left right).mp structural |>.2.2.1⟩
-- Both source-relative ancestry premises are preserved; typed target descent is distinct from historical-source ancestry.
theorem actual_rooted_outcome (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T)) (credits : Option Credits)
    (command : GuardedFusion.Command T) (finished : World S T) (receipts : List (ReceiptAncestry.Receipt S T)) (kind : Bool) (source : Nat)
    (settled : actualSettlement b inputs native program credits command=some ((finished,receipts),kind))
    (leftAncestor : settledAncestry b inputs native program credits command source command.left=some true)
    (rightAncestor : settledAncestry b inputs native program credits command source command.right=some true) :
    (settledAncestry b inputs native program credits command source command.left=some true ∧
      settledAncestry b inputs native program credits command source command.right=some true) ∧
    ((kind=true ∧ Path (combinedLedger receipts [command]) command.left command.target ∧
      Path (combinedLedger receipts [command]) command.right command.target ∧
      settledAncestry b inputs native program credits command source command.target=some true) ∨
      (kind=false ∧ finished.store.read command.target=none ∧
        actualRecordedFusion b inputs native program credits []=some (finished,receipts))) := by
  refine ⟨⟨leftAncestor,rightAncestor⟩,?_⟩
  cases kind with
  | false =>
    have empty := actual_empty_return b inputs native program credits command finished receipts settled
    exact Or.inr ⟨rfl,empty.2,empty.1⟩
  | true =>
    have recorded := actual_settlement_recorded b inputs native program credits command finished receipts true settled
    have leftPath : Path (combinedLedger receipts [command]) command.left command.target := .one (by
      apply List.mem_append.mpr
      right
      simp [fusionLedger])
    have rightPath : Path (combinedLedger receipts [command]) command.right command.target := .one (by
      apply List.mem_append.mpr
      right
      simp [fusionLedger])
    have leftActual := leftAncestor
    rw [settled_ancestry_agrees b inputs native program credits command finished receipts true settled source command.left] at leftActual
    have ancestor := (actual_relation_exact b inputs native program credits [command] finished receipts recorded source command.left).mp leftActual
    have root := closed_path (combinedLedger receipts [command]) (Provenance b inputs (combinedLedger receipts [command]))
      (provenance_least b inputs (combinedLedger receipts [command])).2.1 source command.left command.target ancestor leftPath
    have targetQuote := (settled_ancestry_true_iff b inputs native program credits command source command.target).mpr
      ⟨finished,receipts,true,settled,root⟩
    exact Or.inl ⟨rfl,leftPath,rightPath,targetQuote⟩

namespace Example
open CSTTT.POS04 CSTTT.Objecthood.T1Audit CSTTT.FallbackTheory.SourceCheckedTrace
-- This is exactly the already committed joint_zero_requested_outcome recipe. Its original prediction is unchanged.
def inputs : RawInputs KState KState := ⟨0,some .p0w0,some id,3,destructiveWithTwin 0 1 2 6 2 .p1w0⟩
def program : Program KState := ⟨fun left right => if left=.p0w0 ∧ right=.p0w0 then [(.p1w1,4)] else [],4⟩
def command : GuardedFusion.Command KState := ⟨3,4,5,0,0,.p1w0⟩
def origin : Store KState KState := withRawTwin 0 1 2 6 2 id .p0w0 .p1w0
def splitStore : Store KState KState := NativeDescendant.split origin 2 3 4 .p0w0
def before : World KState KState := ⟨splitStore,[(100,3),(101,4)]⟩
def receipts : List (ReceiptAncestry.Receipt KState KState) := [⟨origin,.fission 2 3 4,splitStore⟩]
theorem computed_origin : computedStore inputs=some origin := by
  exact actual_checked_program 0 1 2 6 2 3 id KState.p0w0 KState.p1w0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem fission_step : NativeDescendant.step (pos04RawBridge .positive) origin (.fission 2 3 4)=some splitStore := by
  simp [NativeDescendant.step,origin,withRawTwin,activated,dormant,erased,captured,initial,put,switch,splitStore]
theorem empty_step : settle (pos04RawBridge .positive) program before command=some (before,false) := by
  apply (empty_settlement_iff _ _ _ _ _).mpr
  refine ⟨.p0w0,.p0w0,?_,?_,?_,?_,rfl⟩
  · simp [before,splitStore,NativeDescendant.split,command,put]
  · simp [before,splitStore,NativeDescendant.split,command,put]
  · decide +kernel
  · decide +kernel
theorem actual_empty_settlement : actualSettlement (pos04RawBridge .positive) inputs [.fission 2 3 4]
    (some program) (some [(100,3),(101,4)]) command=some ((before,receipts),false) := by
  simp [actualSettlement,ReceiptAncestry.actualRecorded,computed_origin,ReceiptAncestry.recordedRun,
    fission_step]
  change (settle (pos04RawBridge .positive) program before command).bind (fun result =>
    some ((result.1,receipts),result.2))=some ((before,receipts),false)
  rw [empty_step]
  rfl
theorem actual_seed : Seed (pos04RawBridge .positive) inputs 0 2 := by
  apply (root_seed_exact (pos04RawBridge .positive) inputs 2).mpr
  exact CSTTT.FallbackTheory.OperationalSeed.actual_seed_constructed (pos04RawBridge .positive)
    CSTTT.FallbackTheory.ReleasedPredictiveQuotient.released_map_laws 0 1 2 6 2 3 KState.p0w0 KState.p1w0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem actual_branch_ancestry : settledAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
    (some program) (some [(100,3),(101,4)]) command 0 3=some true ∧
    settledAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
    (some program) (some [(100,3),(101,4)]) command 0 4=some true := by
  constructor
  all_goals apply (settled_ancestry_true_iff _ _ _ _ _ _ _ _).mpr
  all_goals refine ⟨before,receipts,false,actual_empty_settlement,2,actual_seed,Or.inr (.one ?_)⟩
  all_goals simp [combinedLedger,receipts,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges,fusionLedger]
-- The available EMPTY branch keeps both actual scientific ancestral branches and has no target payload at its requested output.
theorem actual_empty_rooted_return :
    settledAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4] (some program) (some [(100,3),(101,4)]) command 0 3=some true ∧
    settledAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4] (some program) (some [(100,3),(101,4)]) command 0 4=some true ∧
    before.store.read 5=none ∧
    actualRecordedFusion (pos04RawBridge .positive) inputs [.fission 2 3 4] (some program) (some [(100,3),(101,4)]) []=some (before,receipts) := by
  have empty := actual_empty_return (pos04RawBridge .positive) inputs [.fission 2 3 4] (some program) (some [(100,3),(101,4)])
    command before receipts actual_empty_settlement
  exact ⟨actual_branch_ancestry.1,actual_branch_ancestry.2,empty.2,empty.1⟩
-- This actual empty output has an available negative scientific readout for EVERY source query.
theorem empty_target_no_seed (source : Nat) : ¬Seed (pos04RawBridge .positive) inputs source 5 := by
  apply disconnected_target_excludes_all _ inputs origin computed_origin 5
  intro predecessor
  simp [origin,withRawTwin,activated,dormant,erased,captured,initial]
theorem empty_target_no_ledger_path (source : Nat) : ¬Path (combinedLedger receipts []) source 5 := by
  apply no_incoming_excludes
  intro predecessor
  simp [combinedLedger,receipts,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges,fusionLedger]
theorem actual_empty_target_ancestry_false (source : Nat) :
    settledAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
      (some program) (some [(100,3),(101,4)]) command source 5=some false := by
  apply (settled_ancestry_false_iff _ _ _ _ _ _ _ _).mpr
  refine ⟨before,receipts,false,actual_empty_settlement,?_⟩
  rintro ⟨seeded,seed,equal|path⟩
  · subst seeded
    exact empty_target_no_seed source seed
  · exact empty_target_no_ledger_path seeded path
theorem original_step_rejected : GuardedFusion.step (pos04RawBridge .positive) program before command=none := by
  apply joint_conflict_rejects _ _ _ _ KState.p0w0 KState.p0w0
  · simp [before,splitStore,NativeDescendant.split,command,put]
  · simp [before,splitStore,NativeDescendant.split,command,put]
  · decide +kernel
theorem original_actual_fusion_rejected : actualRun (pos04RawBridge .positive) inputs [.fission 2 3 4]
    (some program) (some [(100,3),(101,4)]) [command]=none := by
  simp [actualRun,computed_origin,NativeDescendant.run,fission_step]
  change GuardedFusion.run (pos04RawBridge .positive) program before [command]=none
  simp [GuardedFusion.run,original_step_rejected]
theorem original_ancestry_unavailable (source target : Nat) :
    actualAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
      (some program) (some [(100,3),(101,4)]) [command] source target=none := by
  exact (actual_ancestry_none_iff _ _ _ _ _ _ _ _).mpr original_actual_fusion_rejected
end Example
end CSTTT.FallbackTheory.EmptyDecisionPrototype
