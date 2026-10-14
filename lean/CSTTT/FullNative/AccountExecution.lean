import CSTTT.FullNative.FullInterface

namespace CSTTT.FullNative.AccountExecution
set_option autoImplicit false
abbrev Owner := Fin 3
abbrev Token := Fin 4

inductive Actor where
  | localGenerator : Owner → Actor
  | bridge
  deriving DecidableEq, Repr

structure Accounts where
  allocation : Token → Option Actor
  charge : Token → Bool
  portCursor : Token → Nat

abbrev Supply := Token → Nat → Option Unit
def renewable : Supply := fun _ _ => some ()
def absentSupply : Supply := fun _ _ => none
def put {X : Type} (f : Token → X) (t : Token) (x : X) : Token → X :=
  fun k => if k=t then x else f k

def enabled (a : Accounts) (owner : Owner) (token : Token) : Bool :=
  decide (a.allocation token = some (.localGenerator owner)) && a.charge token

def debit (a : Accounts) (token : Token) : Accounts :=
  {a with charge := put a.charge token false}

def transact (supply : Supply) (a : Accounts) (token : Token) : Accounts :=
  {debit a token with
    charge := put a.charge token ((supply token (a.portCursor token)).isSome)
    portCursor := put a.portCursor token (a.portCursor token+1)}

def initial : Accounts :=
  ⟨(fun t => if t=0 then some (.localGenerator 0) else if t=3 then some .bridge else none),
    (fun _ => true),(fun _ => 0)⟩

def allocateSiblings (a : Accounts) : Option Accounts :=
  if a.allocation 1 = none ∧ a.allocation 2 = none ∧
      a.charge 1 = true ∧ a.charge 2 = true ∧
      (∀ t : Token, a.allocation t ≠ some (.localGenerator 1) ∧
        a.allocation t ≠ some (.localGenerator 2)) then
    some {a with allocation := (put (put a.allocation 1 (some (.localGenerator 1))) 2 (some (.localGenerator 2)))}
  else none

def canonical : Accounts :=
  {initial with allocation := (put (put initial.allocation 1 (some (.localGenerator 1))) 2 (some (.localGenerator 2)))}

theorem initial_allocation : allocateSiblings initial = some canonical := by
  unfold allocateSiblings
  have h : initial.allocation 1 = none ∧ initial.allocation 2 = none ∧
      initial.charge 1 = true ∧ initial.charge 2 = true ∧
      (∀ t : Token, initial.allocation t ≠ some (.localGenerator 1) ∧
        initial.allocation t ≠ some (.localGenerator 2)) := by
    refine ⟨rfl,rfl,rfl,rfl,?_⟩
    intro t
    have ht : t=0 ∨ t=1 ∨ t=2 ∨ t=3 := by
      have hlt := t.isLt
      simp only [Fin.ext_iff]
      omega
    rcases ht with rfl | rfl | rfl | rfl <;> decide +kernel
  rw [if_pos h]
  rfl

theorem charge_after (supply : Supply) (a : Accounts) (t : Token) :
    (transact supply a t).charge t = (supply t (a.portCursor t)).isSome := by
  simp [transact,put]

theorem other_charge (supply : Supply) (a : Accounts) (t k : Token) (different : k≠t) :
    (transact supply a t).charge k = a.charge k := by
  simp [transact,put,different]

theorem cursor_after (supply : Supply) (a : Accounts) (t : Token) :
    (transact supply a t).portCursor t = a.portCursor t+1 := by
  simp [transact,put]

theorem missing_energy_depletes (a : Accounts) (t : Token) :
    (transact absentSupply a t).charge t = false := by
  simp [charge_after,absentSupply]

theorem renewable_charge (a : Accounts) (t : Token) :
    (transact renewable a t).charge t = true := by
  simp [charge_after,renewable]

theorem port_consumption (supply : Supply) (a : Accounts) (t : Token) :
    (transact supply a t).portCursor t > a.portCursor t := by
  rw [cursor_after]
  omega

theorem allocation_unchanged (supply : Supply) (a : Accounts) (t : Token) :
    (transact supply a t).allocation = a.allocation := rfl

theorem transaction_independence (supply : Supply) (a : Accounts)
    (owner : Owner) (t k : Token) (different : t≠k) :
    enabled (transact supply a k) owner t = enabled a owner t := by
  simp [enabled,transact,debit,put,different]

theorem debit_empty (a : Accounts) (t : Token) : (debit a t).charge t = false := by
  simp [debit,put]

theorem other_cursor (supply : Supply) (a : Accounts) (t k : Token) (different : k≠t) :
    (transact supply a t).portCursor k = a.portCursor k := by
  simp [transact,debit,put,different]

theorem independent_transactions (supply : Supply) (a : Accounts) (t k : Token)
    (different : t≠k) :
    transact supply (transact supply a t) k = transact supply (transact supply a k) t := by
  have different' : k≠t := Ne.symm different
  cases a with
  | mk allocation charge cursor =>
    simp only [transact,debit,put]
    congr 1 <;> funext j <;>
      by_cases hjt : j=t <;> by_cases hjk : j=k <;>
      simp_all [put]

theorem siblings_simultaneously_enabled :
    enabled canonical 1 1 = true ∧ enabled canonical 2 2 = true ∧
    canonical.allocation 0 = initial.allocation 0 ∧
    canonical.allocation 3 = initial.allocation 3 := by
  decide +kernel

theorem sibling_ports_independent (supply : Supply) :
    (transact supply canonical 1).charge 2 = true ∧
    (transact supply canonical 1).portCursor 2 = 0 ∧
    enabled (transact supply canonical 1) 2 2 = true := by
  refine ⟨?_,?_,?_⟩
  · rw [other_charge supply canonical 1 2 (by decide)]
    rfl
  · rw [other_cursor supply canonical 1 2 (by decide)]
    rfl
  · rw [transaction_independence supply canonical 2 2 1 (by decide)]
    decide +kernel

theorem allocation_exclusive (a : Accounts) (o p : Owner) (t : Token)
    (ho : a.allocation t = some (.localGenerator o))
    (hp : a.allocation t = some (.localGenerator p)) : o=p := by
  rw [ho] at hp
  exact Actor.localGenerator.inj (Option.some.inj hp)

theorem duplicate_owner_rejected (a : Accounts) (t : Token)
    (occupied : a.allocation t = some (.localGenerator 1)) : allocateSiblings a = none := by
  unfold allocateSiblings
  split
  · rename_i h
    exact False.elim ((h.2.2.2.2 t).1 occupied)
  · rfl

theorem depleted_reserve_rejected (a : Accounts) (depleted : a.charge 1 = false) :
    allocateSiblings a = none := by
  unfold allocateSiblings
  split
  · rename_i h
    rw [depleted] at h
    exact False.elim (Bool.noConfusion h.2.2.1)
  · rfl

end CSTTT.FullNative.AccountExecution
