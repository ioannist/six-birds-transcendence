import CSTTT.Targets.GenericHandoff.Substrate
import CSTTT.Targets.GenericHandoff.ViableSet

/-! Polymorphic operational C8 finite-factor rule. Rows and resources are raw
inputs; the greatest set is defined by ViableSet. This module makes no claim
that unrestricted run recipes have a finite factor. Prices, carrier sizes,
action domains and numerator scales are parameters, not POS-04 constants. -/
namespace CSTTT.TargetTheory.GenericHandoff.OperationalViability

structure Ledger where
  initial : Nat
  cost : Nat
  recharge : Nat
structure Resource (Owner : Type) where
  owner : Owner
  rechargeAvailable : Bool
structure Schema (S A O Owner : Type) where
  states : List S
  actions : List A
  destination : O → Option S
  scale : Nat
  targetOwner : Owner
  ledger : Ledger
  canonicalP : S → S → Nat
structure Raw (S A O Owner : Type) where
  rows : S → A → List (O × Nat)
  policy : S → A
  resource : Resource Owner
  ledger : Ledger

section Rules
variable {S A O Owner : Type} [DecidableEq S] [DecidableEq Owner]
    (cfg : Schema S A O Owner) (d : Raw S A O Owner)

def budgetAfter := d.ledger.initial - d.ledger.cost + d.ledger.recharge
def available : Bool := d.resource.rechargeAvailable &&
  decide (d.ledger.initial ≥ d.ledger.cost) && decide (budgetAfter d > 0) &&
  decide (d.resource.owner = cfg.targetOwner)
def rowClosed (s : S) (a : A) (set : List S) : Bool :=
  let row := d.rows s a
  !row.isEmpty && decide ((row.map Prod.snd).sum = cfg.scale) &&
  row.all (fun e => decide (e.2 > 0) && match cfg.destination e.1 with
    | some t => decide (t ∈ set)
    | none => false)
def retain (set : List S) (s : S) : Bool :=
  available cfg d && cfg.actions.any (fun a => rowClosed cfg d s a set)
def greatest := ViableSet.greatest cfg.states (retain cfg d)
def weight (s t : S) : Nat :=
  ((d.rows s (d.policy s)).map fun e => if cfg.destination e.1 = some t then e.2 else 0).sum

def LedgerCheck : Prop :=
  d.resource.rechargeAvailable = true ∧ d.ledger.initial = cfg.ledger.initial ∧
  d.ledger.cost = cfg.ledger.cost ∧ d.ledger.recharge = cfg.ledger.recharge ∧
  budgetAfter d = d.ledger.initial

def DomainCheck : Prop := cfg.states.Nodup ∧ (∀ s, s ∈ cfg.states) ∧
  cfg.actions.Nodup ∧ (∀ a, a ∈ cfg.actions) ∧ cfg.actions ≠ [] ∧ cfg.scale > 0

def PUnchanged : Prop := ∀ s ∈ cfg.states, ∀ t ∈ cfg.states, weight cfg d s t = cfg.canonicalP s t
/-- Completeness and general row well-formedness are decoder/interface checks;
this operator's rule is the exact operational ledger/closure/P condition. -/
def Accept : Prop := DomainCheck cfg ∧ greatest cfg d ≠ [] ∧ available cfg d = true ∧
  LedgerCheck cfg d ∧ PUnchanged cfg d

omit [DecidableEq Owner] in
theorem row_closed_mono (s : S) (a : A) {U V : List S} (hUV : U ⊆ V)
    (h : rowClosed cfg d s a U = true) : rowClosed cfg d s a V = true := by
  simp only [rowClosed,Bool.and_eq_true,List.all_eq_true] at h ⊢
  refine ⟨h.1,?_⟩
  intro e he
  have hp := h.2 e he
  cases hd : cfg.destination e.1 with
  | none => simp [hd] at hp
  | some t =>
    simp only [hd,decide_eq_true_eq] at hp ⊢
    exact ⟨hp.1,hUV hp.2⟩

theorem retain_monotone : ViableSet.Monotone (retain cfg d) := by
  intro U V hUV s hs
  simp only [retain,Bool.and_eq_true,List.any_eq_true] at hs ⊢
  obtain ⟨a,ha,hr⟩ := hs.2
  exact ⟨hs.1,a,ha,row_closed_mono cfg d s a hUV hr⟩

theorem greatest_viable (covered : ∀ s, s ∈ cfg.states) :
    ViableSet.Viable (retain cfg d) (greatest cfg d) :=
  ViableSet.greatest_viable cfg.states covered _ (retain_monotone cfg d)
theorem greatest_fixed (covered : ∀ s, s ∈ cfg.states) :
    ViableSet.prune (retain cfg d) (greatest cfg d) = greatest cfg d :=
  ViableSet.greatest_fixed cfg.states covered _ (retain_monotone cfg d)
theorem greatest_contains (covered : ∀ s, s ∈ cfg.states) (set : List S)
    (h : ViableSet.Viable (retain cfg d) set) : set ⊆ greatest cfg d :=
  ViableSet.greatest_contains_viable cfg.states covered _ (retain_monotone cfg d) set h

theorem unavailable_empty (covered : ∀ s, s ∈ cfg.states)
    (h : available cfg d = false) : greatest cfg d = [] :=
  ViableSet.no_viable_member_empty cfg.states covered _ (retain_monotone cfg d)
    (by intro set s; simp [retain,h])

def fundedRow (s : S) (a : A) := if available cfg d then d.rows s a else []
omit [DecidableEq S] in
theorem funded_row_unchanged (h : available cfg d = true) (s : S) (a : A) :
    fundedRow cfg d s a = d.rows s a := by simp [fundedRow,h]

theorem no_recharge_rejected (h : d.resource.rechargeAvailable = false) : ¬ Accept cfg d := by
  intro ha
  have hv := ha.2.2.1
  simp [available,h] at hv

theorem wrong_owner_rejected (h : d.resource.owner ≠ cfg.targetOwner) : ¬ Accept cfg d := by
  intro ha
  have hv := ha.2.2.1
  simp [available,h] at hv
end Rules

structure Bindings (Cell : Type) (Value : Cell → Type) (S A O Owner : Type) where
  rows : CellView Cell Value (S → A → List (O × Nat))
  policy : CellView Cell Value (S → A)
  resource : CellView Cell Value (Resource Owner)
  ledger : CellView Cell Value Ledger

section Decoder
variable {Cell S A O Owner : Type} {Value : Cell → Type}
def Bindings.scope (v : Bindings Cell Value S A O Owner) : List Cell :=
  [v.rows.cell,v.policy.cell,v.resource.cell,v.ledger.cell]
def decoded (v : Bindings Cell Value S A O Owner) (a : Assignment Cell Value) : Option (Raw S A O Owner) := do
  let rows ← v.rows.read a
  let policy ← v.policy.read a
  let resource ← v.resource.read a
  let ledger ← v.ledger.read a
  pure ⟨rows,policy,resource,ledger⟩
theorem decoded_locality (v : Bindings Cell Value S A O Owner) {a b : Assignment Cell Value}
    (h : Agrees v.scope a b) : decoded v a = decoded v b := by
  have hr := view_locality v.rows (h _ (by simp [Bindings.scope]))
  have hp := view_locality v.policy (h _ (by simp [Bindings.scope]))
  have hres := view_locality v.resource (h _ (by simp [Bindings.scope]))
  have hl := view_locality v.ledger (h _ (by simp [Bindings.scope]))
  simp only [decoded,hr,hp,hres,hl]
theorem missing_consumed (v : Bindings Cell Value S A O Owner) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) : decoded v a = none := by
  simp only [Bindings.scope,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with h | h | h | h <;> subst k <;> simp [decoded,CellView.read,hm]

variable [DecidableEq S] [DecidableEq Owner]
def AssignedAccept (cfg : Schema S A O Owner) (v : Bindings Cell Value S A O Owner)
    (a : Assignment Cell Value) : Prop := ∃ d, decoded v a = some d ∧ Accept cfg d

theorem acceptance_locality (cfg : Schema S A O Owner) (v : Bindings Cell Value S A O Owner)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : AssignedAccept cfg v a ↔ AssignedAccept cfg v b := by
  unfold AssignedAccept; rw [decoded_locality v h]
theorem missing_rejected (cfg : Schema S A O Owner) (v : Bindings Cell Value S A O Owner)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) :
    ¬ AssignedAccept cfg v a := by
  simp [AssignedAccept,missing_consumed v a k hk hm]
end Decoder
end CSTTT.TargetTheory.GenericHandoff.OperationalViability
