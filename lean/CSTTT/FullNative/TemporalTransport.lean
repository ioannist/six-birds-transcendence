import CSTTT.FullNative.DriveClock

namespace CSTTT.FullNative.TemporalTransport
open AccountExecution PhysicalExecution SnapshotExecution
open TargetTheory.GenericHandoff
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

abbrev Observation := TemporalFactorRules.Observation State State Nat Owner

structure Anchor where
  order : Nat
  records : Nat
  receipt : Nat
  state : State
  deriving DecidableEq, Repr

def readAnchor (p : Local) : Option Anchor := p.receipts.head?.map fun r =>
  ⟨p.orderBase+p.receipts.length,p.receipts.length,r.serial,r.after⟩
def consumedAnchor : Option Anchor := (Credit.sourceCycleWorld.carriers 0).bind readAnchor
theorem anchor_available : consumedAnchor.isSome=true := by decide +kernel
def anchor : Anchor := consumedAnchor.get anchor_available

def branchOwner (right : Bool) : Owner := if right then 2 else 1
theorem source_at_copy_present : (Credit.sourceCycleWorld.carriers 0).isSome=true := by decide +kernel
def sourceAtCopy : Execution :=
  ⟨Credit.sourceCycleWorld.accounts,(Credit.sourceCycleWorld.carriers 0).get source_at_copy_present⟩
theorem target_at_copy_present (right : Bool) :
    (Credit.creditedTransferWorld.carriers (branchOwner right)).isSome=true := by
  cases right <;> decide +kernel
def targetAtCopy (right : Bool) : Execution :=
  ⟨Credit.creditedTransferWorld.accounts,
    (Credit.creditedTransferWorld.carriers (branchOwner right)).get (target_at_copy_present right)⟩

/-- Read the literal written slot before either one-time consumer activates. -/
def writtenCopies : Option World := do
  let reserved ← reserveSiblings Credit.sourceCycleWorld
  let first ← writeSnapshot reserved 1
  writeSnapshot first 2
def writtenSnapshot (right : Bool) : Option Snapshot :=
  writtenCopies.bind fun w => w.slots (branchOwner right)

theorem consumed_anchor_provenance (right : Bool) :
    consumedAnchor=some ⟨6,6,20,FullInterface.rootState⟩ ∧
    (sourceAtCopy.resident.receipts.head?).map Receipt.serial=some anchor.receipt ∧
    anchor.order=(frame sourceAtCopy).context.order ∧
    anchor.records=(frame sourceAtCopy).context.localRecords ∧
    anchor.records=anchor.receipt/4+1 ∧
    (writtenSnapshot right).map (fun s => (s.state,s.receipt.serial))=some (anchor.state,anchor.receipt) ∧
    (writtenSnapshot right).map (fun s => s.receipt)=sourceAtCopy.resident.receipts.head? ∧
    (targetAtCopy right).resident.rootedRoute=([anchor.state],[anchor.receipt]) ∧
    (targetAtCopy right).resident.receipts=[] ∧
    (targetAtCopy right).resident.orderBase=0 := by
  cases right <;> decide +kernel

def shiftContext (a : Anchor) (c : FullInterface.Context) : FullInterface.Context :=
  {c with order := a.order+c.order,localRecords := a.records+c.localRecords}
def shiftRun (a : Anchor) (r : FullInterface.Run) : FullInterface.Run :=
  ⟨r.current,shiftContext a r.context⟩
def rebase (owner : Owner) (route : List State × List Nat) (r : FullInterface.Run) : FullInterface.Run :=
  ⟨r.current,{r.context with owner:=owner,rootedRoute:=route}⟩

theorem shift_advance (a : Anchor) (r : FullInterface.Run) (s : State) :
    shiftRun a (FullInterface.advance r s)=FullInterface.advance (shiftRun a r) s := by
  cases r
  simp [shiftRun,shiftContext,FullInterface.advance,FullInterface.advanceContext,Nat.add_assoc]

theorem shift_context_injective (a : Anchor) (c d : FullInterface.Context)
    (same : shiftContext a c=shiftContext a d) : c=d := by
  cases c; cases d
  simp only [shiftContext,FullInterface.Context.mk.injEq] at same
  obtain ⟨order,records,route,charge,owner⟩ := same
  congr <;> first | assumption | omega

theorem shifted_code_exact (a : Anchor) (r s : FullInterface.Run) :
    FullInterface.code (shiftRun a r)=FullInterface.code (shiftRun a s) ↔
      FullInterface.code r=FullInterface.code s := by
  simp only [FullInterface.code,shiftRun,Prod.mk.injEq]
  constructor
  · rintro ⟨physical,context⟩
    exact ⟨physical,shift_context_injective a _ _ context⟩
  · rintro ⟨physical,context⟩
    exact ⟨physical,congrArg (shiftContext a) context⟩

theorem actual_shift_update (a : Anchor) (x : Execution) (h : sector x)
    (act : Bool) (s : State) (n : Nat) :
    shiftRun a (frame (advance renewable x act s n))=
      FullInterface.advance (shiftRun a (frame x)) s := by
  rw [frame_advance x h,shift_advance]

theorem actual_copy_transport (right : Bool) :
    sector sourceAtCopy ∧ sector (targetAtCopy right) ∧
    shiftRun anchor (frame (targetAtCopy right))=
      rebase (targetAtCopy right).resident.owner (targetAtCopy right).resident.rootedRoute (frame sourceAtCopy) := by
  cases right <;> refine ⟨⟨rfl,rfl,rfl⟩,⟨rfl,rfl,rfl⟩,?_⟩ <;> decide +kernel

theorem copy_contexts_not_identical (right : Bool) :
    (frame (targetAtCopy right)).context≠(frame sourceAtCopy).context ∧
    (shiftRun anchor (frame (targetAtCopy right))).context≠(frame sourceAtCopy).context := by
  cases right <;> decide +kernel

/-- Decode the actual retained single source receipt, without reading a live
source after withdrawal. Correctness is proved for the consumed token0 receipt
below, not assumed for arbitrary fabricated serials or arbitrary order bases. -/
def retainedEpoch (c : FullInterface.Context) : Option (Nat × Nat) :=
  match c.rootedRoute with
  | ([_],[serial]) => some (serial/4+1,serial/4+1)
  | _ => none
def retainedShift (r : FullInterface.Run) : Option FullInterface.Run := do
  let e ← retainedEpoch r.context
  pure ⟨r.current,{r.context with order:=e.1+r.context.order,localRecords:=e.2+r.context.localRecords}⟩
theorem retained_copy_transport (right : Bool) :
    retainedEpoch (frame (targetAtCopy right)).context=some (anchor.order,anchor.records) ∧
    retainedShift (frame (targetAtCopy right))=some (shiftRun anchor (frame (targetAtCopy right))) := by
  cases right <;> decide +kernel

theorem actual_frame_law {V : Type} [DecidableEq V] (ob : FullInterface.Run → V)
    (x : Execution) (h : sector x) (word : List Bool) (trace : List V) :
    WeightedFuture.law (normalizedRows renewable) (fun x => ob (frame x)) x word trace=
      WeightedFuture.law FullInterface.rows ob (frame x) word trace := by
  induction word generalizing x trace with
  | nil => rfl
  | cons act rest ih =>
    cases trace with
    | nil => rfl
    | cons v tail =>
      simp only [WeightedFuture.law]
      by_cases hv : v=ob (frame x)
      · simp only [hv,if_true]
        rw [←sector_projection x h act,List.foldr_map]
        simp only [normalizedRows,sector_rows x h act,List.foldr_map]
        congr 1
        funext e acc
        exact congrArg (fun z => (e.2:Rat)/16*z+acc)
          (ih (advance renewable x act e.1 e.2) (sector_preserved x h act e.1 e.2) tail)
      · simp [hv]

theorem shifted_rows (a : Anchor) (r : FullInterface.Run) (act : Bool) :
    (FullInterface.rows r act).map (fun e => (shiftRun a e.1,e.2))=
      FullInterface.rows (shiftRun a r) act := by
  by_cases charged : r.context.charge=true
  · have charge : (shiftRun a r).context.charge=r.context.charge := rfl
    have current : (shiftRun a r).current=r.current := rfl
    simp only [FullInterface.rows,charge,current,charged,if_true]
    simp only [List.map_map,Function.comp_def,shift_advance]
  · have hc : r.context.charge=false := Bool.eq_false_iff.mpr charged
    simp [FullInterface.rows,shiftRun,shiftContext,hc]

theorem shifted_future_law (a : Anchor) (r : FullInterface.Run) (word : List Bool)
    (trace : List Observation) :
    WeightedFuture.law FullInterface.rows (fun r => FullInterface.observe (shiftRun a r)) r word trace=
      WeightedFuture.law FullInterface.rows FullInterface.observe (shiftRun a r) word trace := by
  induction word generalizing r trace with
  | nil => rfl
  | cons act rest ih =>
    cases trace with
    | nil => rfl
    | cons v tail =>
      simp only [WeightedFuture.law]
      by_cases hv : v=FullInterface.observe (shiftRun a r)
      · simp only [hv,if_true]
        rw [←shifted_rows a r act,List.foldr_map]
        congr 1
        funext e acc
        rw [ih]
      · simp [hv]

theorem actual_transported_future (right : Bool) (word : List Bool) (trace : List Observation) :
    WeightedFuture.law (normalizedRows renewable)
      (fun x => FullInterface.observe (shiftRun anchor (frame x))) (targetAtCopy right) word trace=
    WeightedFuture.law FullInterface.rows FullInterface.observe
      (rebase (targetAtCopy right).resident.owner (targetAtCopy right).resident.rootedRoute (frame sourceAtCopy)) word trace := by
  rw [actual_frame_law (fun r => FullInterface.observe (shiftRun anchor r)) _
      (actual_copy_transport right).2.1,shifted_future_law,
    (actual_copy_transport right).2.2]

theorem transported_future_exact (x y : Execution) (hx : sector x) (hy : sector y) :
    (∀ word trace, WeightedFuture.law (normalizedRows renewable)
        (fun x => FullInterface.observe (shiftRun anchor (frame x))) x word trace=
      WeightedFuture.law (normalizedRows renewable)
        (fun x => FullInterface.observe (shiftRun anchor (frame x))) y word trace) ↔
      FullInterface.code (frame x)=FullInterface.code (frame y) := by
  have bridge : (∀ word trace, WeightedFuture.law (normalizedRows renewable)
        (fun x => FullInterface.observe (shiftRun anchor (frame x))) x word trace=
      WeightedFuture.law (normalizedRows renewable)
        (fun x => FullInterface.observe (shiftRun anchor (frame x))) y word trace) ↔
      (∀ word trace, WeightedFuture.law FullInterface.rows FullInterface.observe (shiftRun anchor (frame x)) word trace=
        WeightedFuture.law FullInterface.rows FullInterface.observe (shiftRun anchor (frame y)) word trace) := by
    constructor <;> intro h word trace
    · simpa only [actual_frame_law (fun r => FullInterface.observe (shiftRun anchor r)) x hx,
        actual_frame_law (fun r => FullInterface.observe (shiftRun anchor r)) y hy,shifted_future_law] using h word trace
    · simpa only [actual_frame_law (fun r => FullInterface.observe (shiftRun anchor r)) x hx,
        actual_frame_law (fun r => FullInterface.observe (shiftRun anchor r)) y hy,shifted_future_law] using h word trace
  exact bridge.trans ((FullInterface.full_future_exact _ _).trans (shifted_code_exact anchor _ _))

end CSTTT.FullNative.TemporalTransport
