import CSTTT.FullNative02.ROMObserver
import CSTTT.FullNative.FullInterface

namespace CSTTT.FullNative02.Temporal
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 8000000

structure Residue where
  installed : ROM
  birth : Node
  birthCursor : Nat
  roots : List (Node × Nat)
  deriving DecidableEq, Repr

structure Context where
  order : Nat
  records : Nat
  residue : Residue
  charge : Bool
  owner : Nat
  deriving DecidableEq, Repr

structure Run where
  current : State
  context : Context
  deriving DecidableEq, Repr

structure Observation where
  predictive : Nat
  order : Nat
  tick : Bool
  progress : Nat
  record : Nat
  residue : Residue
  maintenance : Bool
  owner : Nat
  deriving DecidableEq, Repr

def advanceContext (c : Context) : Context := {c with order:=c.order+1,records:=c.records+1}
def advance (r : Run) (s : State) : Run := ⟨s,advanceContext r.context⟩
def rows (r : Run) (action : Bool) : List (Run × Rat) :=
  if r.context.charge then (rationalRows r.context.residue.installed.program r.current action).map fun e => (advance r e.1,e.2)
  else []
def observe (r : Run) : Observation :=
  ⟨classes r.context.residue.installed.program r.current,r.context.order,r.current.phase,r.context.order,
    r.context.records,r.context.residue,r.context.charge,r.context.owner⟩
def code (r : Run) : Nat × Context := (classes r.context.residue.installed.program r.current,r.context)
def project (r : Run) : Shape × Context := (eraseReplica r.current,r.context)
def representative (q : Shape × Context) : Run := ⟨FullNative.representative q.1,q.2⟩

theorem projected_rows (r : Run) (a : Bool) :
    (rows r a).map (fun e => (project e.1,e.2))=
      WeightedFuture.projectedRows rows project representative (project r) a := by
  cases charge : r.context.charge
  · simp [rows,charge,WeightedFuture.projectedRows,project,representative]
  · have projected := congrArg (fun es : List (Shape × Rat) =>
        es.map fun e => ((e.1,advanceContext r.context),e.2)) (rom_projected_rows r.context.residue.installed r.current a)
    simpa [rows,charge,WeightedFuture.projectedRows,project,representative,advance,
      List.map_map,Function.comp_def] using projected

theorem observation_projection : observe=fun r => observe (representative (project r)) := by
  funext r
  simp only [observe,rom_physical_classes]
  rfl

theorem code_projection_exact (r s : Run) : code r=code s ↔ project r=project s := by
  simp only [code,rom_physical_classes,project,Prod.mk.injEq]
  rw [←congrFun first_profile_equation r.current,←congrFun first_profile_equation s.current,classes_shape_exact]

theorem all_words (r s : Run) (same : code r=code s) (word : List Bool)
    (trace : List Observation) :
    WeightedFuture.law rows observe r word trace=WeightedFuture.law rows observe s word trace := by
  rw [observation_projection]
  exact WeightedFuture.equal_projection_all_words rows (fun q => observe (representative q))
    project representative projected_rows r s ((code_projection_exact r s).mp same) word trace

theorem future_exact (r s : Run) :
    (∀ word trace,WeightedFuture.law rows observe r word trace=
      WeightedFuture.law rows observe s word trace) ↔ code r=code s := by
  constructor
  · intro laws
    have witness := laws [] [observe r]
    have eq : observe r=observe s := by
      by_cases eq : observe r=observe s
      · exact eq
      · simp [WeightedFuture.law,eq] at witness
    have predictive := congrArg Observation.predictive eq
    have order := congrArg Observation.order eq
    have records := congrArg Observation.record eq
    have residue := congrArg Observation.residue eq
    have charge := congrArg Observation.maintenance eq
    have owner := congrArg Observation.owner eq
    rcases r with ⟨rs,⟨ro,rn,rr,rc,ra⟩⟩
    rcases s with ⟨ss,⟨so,sn,sr,sc,sa⟩⟩
    simp only [observe] at predictive order records residue charge owner
    simp only [residue] at predictive
    simp [code,Context.mk.injEq,predictive,order,records,residue,charge,owner]
  · exact fun same => all_words r s same

def frameROM (w : World) (r : Resident) (rom : ROM) (key : Token) : Run :=
  ⟨r.current,⟨r.receipts.length,r.receipts.length,
    ⟨rom,r.birth,r.birthCursor,r.roots⟩,w.accounts.charge key,r.owner⟩⟩

/-- Canonical interpretation used only behind an actual canonical access proof.
The raw observer below obtains its ROM from authenticated binding, even when
stored charge is absent, and rejects missing code. -/
abbrev frame (w : World) (r : Resident) (key : Token) : Run := frameROM w r .canonical32 key

def actual (w : World) (owner : Nat) : Option Run :=
  (binding w owner).map fun data => frameROM w data.1 data.2.1 data.2.2

theorem actual_frame (w : World) (owner : Nat) (r : Resident) (rom : ROM) (key : Token)
    (h : binding w owner=some (r,rom,key)) : actual w owner=some (frameROM w r rom key) := by
  simp [actual,h]

theorem frame_append (w : World) (owner : Nat) (r : Resident) (rom : ROM) (key : Token)
    (charge : w.accounts.charge key=true) (action : Bool) (e : State × Nat) :
    frameROM (FullNative02.advance renewable w owner r rom key action e)
      {r with
        current := e.1
        version := .version w.events.length
        receipts := r.receipts++[makeReceipt renewable w owner r rom key action e]} rom key=
    advance (frameROM w r rom key) e.1 := by
  simp [frameROM,FullNative02.advance,transact,put,renewable,AccountExecution.renewable,charge,
    advance,advanceContext]

theorem actual_rom_all_words (w : World) (owner : Nat) (r : Resident) (rom : ROM) (key : Token)
    (h : binding w owner=some (r,rom,key)) (word : List Bool)
    (trace : List (Option Observation)) :
    WeightedFuture.law (fun w a => normalizedNative renewable w owner a)
      (fun w => (actual w owner).map observe) w word trace=
    WeightedFuture.law rows (fun r => some (observe r)) (frameROM w r rom key) word trace := by
  induction word generalizing w r trace with
  | nil => simp [WeightedFuture.law,actual_frame _ _ _ _ _ h]
  | cons a rest ih =>
    cases trace with
    | nil => rfl
    | cons v tail =>
      cases charge : w.accounts.charge key
      case false =>
        have disabled : access w owner=none := by simp [access,h,charge]
        have unfunded : (frameROM w r rom key).context.charge=false := charge
        simp [WeightedFuture.law,actual_frame _ _ _ _ _ h,normalizedNative,nativeRows,disabled,rows,unfunded]
      case true =>
        have enabled : access w owner=some (r,rom,key) := by simp [access,h,charge]
        have frameCharge : (frameROM w r rom key).context.charge=true := charge
        have current : (frameROM w r rom key).current=r.current := rfl
        have installed : (frameROM w r rom key).context.residue.installed=rom := rfl
        simp only [WeightedFuture.law,actual_frame _ _ _ _ _ h,Option.map_some,
          normalizedNative,native_rows_from_access _ _ _ _ _ _ enabled a,rows,frameCharge,
          if_true,current,installed,rationalRows,List.foldr_map]
        by_cases hv : v=some (observe (frameROM w r rom key))
        · simp only [hv,if_true]
          congr 1
          funext e acc
          have after := renewable_access_after w owner r rom key enabled a e
          have next := ih _ _ (access_facts _ _ _ _ _ after).1 tail
          rw [frame_append _ _ _ _ _ charge] at next
          exact congrArg (fun z => (e.2:Rat)/16*z+acc) next
        · simp only [frameROM,charge] at hv ⊢
          simp only [if_neg hv]

theorem actual_all_words (w : World) (owner : Nat) (r : Resident) (key : Token)
    (h : access w owner=some (r,.canonical32,key)) (word : List Bool)
    (trace : List (Option Observation)) :
    WeightedFuture.law (fun w a => normalizedNative renewable w owner a)
      (fun w => (actual w owner).map observe) w word trace=
    WeightedFuture.law rows (fun r => some (observe r)) (frame w r key) word trace :=
  actual_rom_all_words w owner r .canonical32 key (access_facts _ _ _ _ _ h).1 word trace

end CSTTT.FullNative02.Temporal
