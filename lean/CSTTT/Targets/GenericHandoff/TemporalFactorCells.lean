import CSTTT.Targets.GenericHandoff.TemporalFactorRules

/-! Generic C6 primitive decoder. Every required input is a typed view into
one shared assignment. No absence can use a canonical table, and no computed
future, code, class, closure or acceptance verdict is a binding field. -/
namespace CSTTT.TargetTheory.GenericHandoff.TemporalFactorCells
open TemporalFactorRules

structure Bindings (Cell : Type) (Value : Cell → Type) (S A O H RouteId Stage Id Owner : Type) where
  rows : CellView Cell Value (S → A → List (O × Nat))
  positions : CellView Cell Value (S → Nat)
  hazards : CellView Cell Value (O → Bool)
  policy : CellView Cell Value (S → A)
  classes : CellView Cell Value (S → Nat)
  publishedP : CellView Cell Value (S → S → Nat)
  ticks : CellView Cell Value (S → A → Nat)
  resource : CellView Cell Value (OperationalViability.Resource Owner)
  ledger : CellView Cell Value OperationalViability.Ledger
  interface : CellView Cell Value (List Observable)
  histories : CellView Cell Value (H → List S)
  events : CellView Cell Value (List (Event Stage Id))
  realized : CellView Cell Value (List Stage)
  receiverFunded : CellView Cell Value Bool
  routes : CellView Cell Value (List (Route RouteId H Id))
  writers : CellView Cell Value (RouteId → Bool)

variable {Cell S A O H RouteId Stage Id Owner : Type} {Value : Cell → Type}

def Bindings.scope (v : Bindings Cell Value S A O H RouteId Stage Id Owner) : List Cell :=
  [v.rows.cell,v.positions.cell,v.hazards.cell,v.policy.cell,v.classes.cell,v.publishedP.cell,
   v.ticks.cell,v.resource.cell,v.ledger.cell,v.interface.cell,v.histories.cell,v.events.cell,
   v.realized.cell,v.receiverFunded.cell,v.routes.cell,v.writers.cell]

def decoded (v : Bindings Cell Value S A O H RouteId Stage Id Owner) (a : Assignment Cell Value) :
    Option (Raw S A O H RouteId Stage Id Owner) := do
  let rows ← v.rows.read a
  let positions ← v.positions.read a
  let hazards ← v.hazards.read a
  let policy ← v.policy.read a
  let classes ← v.classes.read a
  let publishedP ← v.publishedP.read a
  let ticks ← v.ticks.read a
  let resource ← v.resource.read a
  let ledger ← v.ledger.read a
  let interface ← v.interface.read a
  let histories ← v.histories.read a
  let events ← v.events.read a
  let realized ← v.realized.read a
  let receiverFunded ← v.receiverFunded.read a
  let routes ← v.routes.read a
  let writers ← v.writers.read a
  pure ⟨rows,positions,hazards,policy,classes,publishedP,ticks,resource,ledger,interface,
    histories,events,realized,receiverFunded,routes,writers⟩

theorem decoder_locality (v : Bindings Cell Value S A O H RouteId Stage Id Owner)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : decoded v a = decoded v b := by
  have h1 := view_locality v.rows (h _ (by simp [Bindings.scope]))
  have h2 := view_locality v.positions (h _ (by simp [Bindings.scope]))
  have h3 := view_locality v.hazards (h _ (by simp [Bindings.scope]))
  have h4 := view_locality v.policy (h _ (by simp [Bindings.scope]))
  have h5 := view_locality v.classes (h _ (by simp [Bindings.scope]))
  have h6 := view_locality v.publishedP (h _ (by simp [Bindings.scope]))
  have h7 := view_locality v.ticks (h _ (by simp [Bindings.scope]))
  have h8 := view_locality v.resource (h _ (by simp [Bindings.scope]))
  have h9 := view_locality v.ledger (h _ (by simp [Bindings.scope]))
  have h10 := view_locality v.interface (h _ (by simp [Bindings.scope]))
  have h11 := view_locality v.histories (h _ (by simp [Bindings.scope]))
  have h12 := view_locality v.events (h _ (by simp [Bindings.scope]))
  have h13 := view_locality v.realized (h _ (by simp [Bindings.scope]))
  have h14 := view_locality v.receiverFunded (h _ (by simp [Bindings.scope]))
  have h15 := view_locality v.routes (h _ (by simp [Bindings.scope]))
  have h16 := view_locality v.writers (h _ (by simp [Bindings.scope]))
  simp only [decoded,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13,h14,h15,h16]

theorem missing_input (v : Bindings Cell Value S A O H RouteId Stage Id Owner) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) : decoded v a = none := by
  simp only [Bindings.scope,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk | hk
  all_goals subst k; simp [decoded,CellView.read,hm]

variable [DecidableEq S] [DecidableEq O] [DecidableEq RouteId] [DecidableEq Stage] [DecidableEq Id]

def Accept (cfg : Schema S A O H RouteId Stage Id Owner)
    (v : Bindings Cell Value S A O H RouteId Stage Id Owner) (a : Assignment Cell Value) : Prop :=
  ∃ d, decoded v a = some d ∧ TemporalFactorRules.Accept cfg d

theorem acceptance_locality (cfg : Schema S A O H RouteId Stage Id Owner)
    (v : Bindings Cell Value S A O H RouteId Stage Id Owner)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : Accept cfg v a ↔ Accept cfg v b := by
  simp only [Accept,decoder_locality v h]

theorem missing_rejected (cfg : Schema S A O H RouteId Stage Id Owner)
    (v : Bindings Cell Value S A O H RouteId Stage Id Owner) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) : ¬ Accept cfg v a := by
  simp [Accept,missing_input v a k hk hm]

end CSTTT.TargetTheory.GenericHandoff.TemporalFactorCells
