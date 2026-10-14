import CSTTT.FullNative.AccountExecution

/-! FULL-NATIVE-01 execution reads an installed local program and an actually
owned, charged token. Each generated receipt records the executed edge, local
hardware issuer and consumed environmental packet. The renewable environment
is an explicit open input, not energy minted by a local primitive. -/
namespace CSTTT.FullNative.PhysicalExecution
open AccountExecution
set_option autoImplicit false

structure Receipt where
  issuer : Actor
  token : Token
  serial : Nat
  before : State
  after : State
  action : Bool
  weight : Nat
  energy : Option Unit
  deriving DecidableEq, Repr

structure Local where
  owner : Owner
  token : Token
  installed : Option Model
  current : State
  receipts : List Receipt
  rootedRoute : List State × List Nat
  orderBase : Nat

structure Execution where
  accounts : Accounts
  resident : Local

def issued (supply : Supply) (x : Execution) (a : Bool) (s : State) (n : Nat) : Receipt :=
  ⟨.localGenerator x.resident.owner,x.resident.token,
    4*x.accounts.portCursor x.resident.token+x.resident.token.val,
    x.resident.current,s,a,n,supply x.resident.token (x.accounts.portCursor x.resident.token)⟩

def advance (supply : Supply) (x : Execution) (a : Bool) (s : State) (n : Nat) : Execution :=
  ⟨transact supply x.accounts x.resident.token,
    {x.resident with
      current := s
      receipts := issued supply x a s n :: x.resident.receipts}⟩

def rawRows (supply : Supply) (x : Execution) (a : Bool) : List (Execution × Nat) :=
  match x.resident.installed with
  | none => []
  | some d => if enabled x.accounts x.resident.owner x.resident.token then
      (d.rows x.resident.current a).map fun e => (advance supply x a e.1 e.2,e.2)
    else []

def normalizedRows (supply : Supply) (x : Execution) (a : Bool) : List (Execution × Rat) :=
  (rawRows supply x a).map fun e => (e.1,(e.2:Rat)/16)

def frame (x : Execution) : FullInterface.Run :=
  ⟨x.resident.current,⟨x.resident.orderBase+x.resident.receipts.length,x.resident.receipts.length,
    x.resident.rootedRoute,x.accounts.charge x.resident.token,x.resident.owner⟩⟩

def source : Execution :=
  ⟨initial,⟨0,0,some model,FullInterface.rootState,[],([],[]),0⟩⟩

def sector (x : Execution) : Prop :=
  x.resident.installed = some model ∧
  x.accounts.allocation x.resident.token = some (.localGenerator x.resident.owner) ∧
  x.accounts.charge x.resident.token = true

theorem source_sector : sector source := by exact ⟨rfl,rfl,rfl⟩

theorem enabled_sector (x : Execution) (h : sector x) :
    enabled x.accounts x.resident.owner x.resident.token = true := by
  simp [enabled,h.2.1,h.2.2]

theorem sector_preserved (x : Execution) (h : sector x) (a : Bool) (s : State) (n : Nat) :
    sector (advance renewable x a s n) := by
  exact ⟨h.1,h.2.1,renewable_charge x.accounts x.resident.token⟩

theorem frame_advance (x : Execution) (h : sector x) (a : Bool) (s : State) (n : Nat) :
    frame (advance renewable x a s n) = FullInterface.advance (frame x) s := by
  simp [frame,advance,FullInterface.advance,FullInterface.advanceContext,
    renewable_charge,h.2.2,Nat.add_assoc]

theorem sector_rows (x : Execution) (h : sector x) (a : Bool) :
    rawRows renewable x a =
      (FullNative.rows x.resident.current a).map fun e =>
        (advance renewable x a e.1 e.2,e.2) := by
  simp [rawRows,h.1,enabled_sector x h,model]

theorem sector_projection (x : Execution) (h : sector x) (a : Bool) :
    (normalizedRows renewable x a).map (fun e => (frame e.1,e.2)) =
      FullInterface.rows (frame x) a := by
  simp only [normalizedRows,sector_rows x h a,List.map_map,Function.comp_def]
  have charged : (frame x).context.charge = true := h.2.2
  simp only [FullInterface.rows,charged,if_true,rationalRows,model,List.map_map,
    Function.comp_def,frame_advance x h]
  rfl

theorem no_program (supply : Supply) (x : Execution) (a : Bool)
    (missing : x.resident.installed = none) : rawRows supply x a = [] := by
  simp [rawRows,missing]

theorem no_charge (supply : Supply) (x : Execution) (a : Bool)
    (empty : x.accounts.charge x.resident.token = false) : rawRows supply x a = [] := by
  cases hp : x.resident.installed <;> simp [rawRows,hp,enabled,empty]

theorem no_owner (supply : Supply) (x : Execution) (a : Bool)
    (unowned : x.accounts.allocation x.resident.token ≠ some (.localGenerator x.resident.owner)) :
    rawRows supply x a = [] := by
  cases hp : x.resident.installed <;> simp [rawRows,hp,enabled,unowned]

theorem receipt_consumption (supply : Supply) (x : Execution) (a : Bool) (s : State) (n : Nat) :
    (advance supply x a s n).resident.receipts.head? = some (issued supply x a s n) ∧
    (issued supply x a s n).issuer = .localGenerator x.resident.owner ∧
    (issued supply x a s n).before = x.resident.current ∧
    (issued supply x a s n).after = s ∧
    (issued supply x a s n).energy = supply x.resident.token (x.accounts.portCursor x.resident.token) ∧
    (advance supply x a s n).accounts.portCursor x.resident.token =
      x.accounts.portCursor x.resident.token+1 ∧
    (advance supply x a s n).accounts.charge x.resident.token =
      (issued supply x a s n).energy.isSome := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,cursor_after supply x.accounts x.resident.token,
    charge_after supply x.accounts x.resident.token⟩

theorem energy_absence_stops_next (x : Execution) (a b : Bool) (s : State) (n : Nat) :
    rawRows absentSupply (advance absentSupply x a s n) b = [] := by
  apply no_charge
  exact missing_energy_depletes x.accounts x.resident.token

theorem actual_full_law (x : Execution) (h : sector x) (word : List Bool)
    (trace : List (TargetTheory.GenericHandoff.TemporalFactorRules.Observation State State Nat (Fin 3))) :
    WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (frame x)) x word trace =
      WeightedFuture.law FullInterface.rows FullInterface.observe (frame x) word trace := by
  induction word generalizing x trace with
  | nil => rfl
  | cons a rest ih =>
    cases trace with
    | nil => rfl
    | cons v tail =>
      simp only [WeightedFuture.law]
      by_cases hv : v = FullInterface.observe (frame x)
      · simp only [hv,if_true]
        rw [← sector_projection x h a,List.foldr_map]
        simp only [normalizedRows,sector_rows x h a,List.foldr_map]
        congr 1
        funext e acc
        exact congrArg (fun z => (e.2:Rat)/16*z+acc)
          (ih (advance renewable x a e.1 e.2) (sector_preserved x h a e.1 e.2) tail)
      · simp [hv]

/-- Supported execution, retaining every generated receipt. This is distinct
from an arbitrary context or a history supplied by an observer. -/
inductive Reachable (supply : Supply) : Execution → Prop where
  | initial : Reachable supply source
  | step {x y : Execution} {a : Bool} {n : Nat} :
      Reachable supply x → (y,n) ∈ rawRows supply x a → Reachable supply y

theorem reachable_sector (x : Execution) (h : Reachable renewable x) : sector x := by
  induction h with
  | initial => exact source_sector
  | @step x y a n reachable edge ih =>
    rw [sector_rows x ih a] at edge
    obtain ⟨e,_,he⟩ := List.mem_map.mp edge
    have hy : advance renewable x a e.1 e.2 = y := congrArg Prod.fst he
    rw [← hy]
    exact sector_preserved x ih a e.1 e.2

theorem enabled_row_mass (x : Execution) (h : sector x) (a : Bool) :
    (rawRows renewable x a).foldr (fun e acc => e.2+acc) 0 = 16 := by
  rw [sector_rows x h a,List.foldr_map]
  simpa [List.sum,List.foldr_map] using (rows_positive_normalized x.resident.current a).2

theorem reachable_receipts_local (x : Execution) (h : Reachable renewable x) :
    ∀ r ∈ x.resident.receipts,
      r.issuer = .localGenerator x.resident.owner ∧
      r.token = x.resident.token ∧ r.energy = some () := by
  induction h with
  | initial => simp [source]
  | @step x y a n reachable edge ih =>
    rw [sector_rows x (reachable_sector x reachable) a] at edge
    obtain ⟨e,_,he⟩ := List.mem_map.mp edge
    have hy : advance renewable x a e.1 e.2 = y := congrArg Prod.fst he
    rw [← hy]
    intro r hr
    simp only [advance,List.mem_cons] at hr
    rcases hr with rfl | hr
    · exact ⟨rfl,rfl,rfl⟩
    · exact ih r hr

theorem reachable_head_ends_current (x : Execution) (h : Reachable renewable x) :
    ∀ r, x.resident.receipts.head? = some r → r.after = x.resident.current := by
  induction h with
  | initial => simp [source]
  | @step x y a n reachable edge ih =>
    rw [sector_rows x (reachable_sector x reachable) a] at edge
    obtain ⟨e,_,he⟩ := List.mem_map.mp edge
    have hy : advance renewable x a e.1 e.2 = y := congrArg Prod.fst he
    rw [← hy]
    intro r hr
    have eq : issued renewable x a e.1 e.2 = r := Option.some.inj hr
    rw [← eq]
    rfl

theorem single_packet_consumed (x : Execution) (a : Bool) (s : State) (n : Nat) :
    (debit x.accounts x.resident.token).charge x.resident.token = false ∧
    (advance renewable x a s n).accounts.charge x.resident.token = true ∧
    (advance renewable x a s n).accounts.portCursor x.resident.token =
      x.accounts.portCursor x.resident.token+1 := by
  exact ⟨debit_empty _ _,renewable_charge _ _,cursor_after _ _ _⟩

def replicaLeft : Execution := advance renewable source false FullInterface.replicaLeft 1
def replicaRight : Execution := advance renewable source false FullInterface.replicaRight 1

theorem actual_reachable_fiber :
    Reachable renewable replicaLeft ∧ Reachable renewable replicaRight ∧
    (frame replicaLeft).context = (frame replicaRight).context ∧
    FullInterface.code (frame replicaLeft) = FullInterface.code (frame replicaRight) ∧
    (replicaLeft.resident.receipts.head?).map Receipt.after ≠
      (replicaRight.resident.receipts.head?).map Receipt.after := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · exact Reachable.step (a := false) (n := 1) .initial (by
      change (replicaLeft,1) ∈ rawRows renewable source false
      rw [sector_rows source source_sector]
      simp [source,FullNative.rows,kernels,bits,
        weight,diagonal,FullInterface.rootState,FullInterface.replicaLeft,replicaLeft])
  · exact Reachable.step (a := false) (n := 1) .initial (by
      change (replicaRight,1) ∈ rawRows renewable source false
      rw [sector_rows source source_sector]
      simp [source,FullNative.rows,kernels,bits,
        weight,diagonal,FullInterface.rootState,FullInterface.replicaRight,replicaRight])
  · rfl
  · simp only [replicaLeft,replicaRight,frame_advance source source_sector,
      FullInterface.code,first_profile_equation]
    rfl
  · decide +kernel

theorem actual_reachable_fiber_full_future (word : List Bool)
    (trace : List (TargetTheory.GenericHandoff.TemporalFactorRules.Observation State State Nat (Fin 3))) :
    WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (frame x)) replicaLeft word trace =
      WeightedFuture.law (normalizedRows renewable) (fun x => FullInterface.observe (frame x)) replicaRight word trace := by
  rw [actual_full_law replicaLeft (reachable_sector _ actual_reachable_fiber.1),
    actual_full_law replicaRight (reachable_sector _ actual_reachable_fiber.2.1)]
  exact FullInterface.all_words _ _ actual_reachable_fiber.2.2.2.1 word trace

end CSTTT.FullNative.PhysicalExecution
