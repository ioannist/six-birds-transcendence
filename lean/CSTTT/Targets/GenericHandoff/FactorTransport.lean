import CSTTT.Targets.GenericHandoff.TemporalFactorRules
import CSTTT.Targets.GenericHandoff.StaticView

/-! Raw finite-factor extraction for G6d lineage. Predictive classes, policy
steps, action steps, and word probes are computed from the decoded tables. This
component does not replace the independently checked full run/closure laws.
The source and target factor domains and alphabets are arbitrary. -/
namespace CSTTT.TargetTheory.GenericHandoff.FactorTransport
open TemporalFactorRules

abbrev Predictive := Nat × List (List Bool)

/-- Only factor-consumed primitives. In particular the interface-declaration
list, history table and writer table are NOT decoder dependencies here. -/
structure Data (S A O Owner : Type) where
  rows : S → A → List (O × Nat)
  positions : S → Nat
  hazards : O → Bool
  policy : S → A
  ticks : S → A → Nat
  resource : OperationalViability.Resource Owner
  ledger : OperationalViability.Ledger

structure Maps (S T A B Owner : Type) where
  state : S → T
  action : A → B
  coordinate : Nat → Nat
  predictive : Predictive → Predictive
  maintenance : Bool → Bool
  owner : Owner → Owner

variable {S T A B O N H R Stage Id Owner : Type}
  [DecidableEq S] [DecidableEq T] [DecidableEq Owner]

def classOf (cfg : Schema S A O H R Stage Id Owner)
    (d : Data S A O Owner) : S → Predictive :=
  fun s => (d.positions s,cfg.base.actions.map fun a => (d.rows s a).map fun e => d.hazards e.1)

def actionWeight (cfg : Schema S A O H R Stage Id Owner)
    (d : Data S A O Owner) (s : S) (a : A) (u : S) : Nat :=
  ((d.rows s a).map fun e => if cfg.base.destination e.1 = some u then e.2 else 0).sum

def canonicalWeight (cfg : Schema S A O H R Stage Id Owner) (d : Data S A O Owner)
    (s u : S) : Nat := actionWeight cfg d s (d.policy s) u

def maintained [DecidableEq Owner] (cfg : Schema S A O H R Stage Id Owner)
    (d : Data S A O Owner) : Bool :=
  d.resource.rechargeAvailable && decide (d.ledger.initial ≥ d.ledger.cost) &&
    decide (d.ledger.initial - d.ledger.cost + d.ledger.recharge > 0) && decide (d.resource.owner = cfg.owner)

/-- Every clause is an equation on decoded raw fields. Injectivity is checked
on realized source classes, not assumed on an unbounded class alphabet. -/
structure Equations
    (src : Schema S A O H R Stage Id Owner) (tgt : Schema T B N H R Stage Id Owner)
    (ds : Data S A O Owner) (dt : Data T B N Owner)
    (m : Maps S T A B Owner) : Prop where
  states : tgt.base.states = src.base.states.map m.state
  coordinate : ∀ s, dt.positions (m.state s) = m.coordinate (ds.positions s)
  predictive : ∀ s, classOf tgt dt (m.state s) = m.predictive (classOf src ds s)
  policy : ∀ s, dt.policy (m.state s) = m.action (ds.policy s)
  action : ∀ s a u, actionWeight tgt dt (m.state s) (m.action a) (m.state u) =
    actionWeight src ds s a u
  tick : ∀ s, dt.ticks (m.state s) (dt.policy (m.state s)) = ds.ticks s (ds.policy s)
  maintenance : maintained tgt dt = m.maintenance (maintained src ds)
  owner : dt.resource.owner = m.owner ds.resource.owner
  classInjective : ∀ s u, m.predictive (classOf src ds s) = m.predictive (classOf src ds u) →
    classOf src ds s = classOf src ds u
  scale : tgt.base.rowScale = src.base.rowScale

/-- The finite M-class action-word probe. Full eight-component futures are
proved separately by the actual-support run binding. -/
def word (cfg : Schema S A O H R Stage Id Owner) (d : Data S A O Owner)
    (s : S) : List A → S → Nat
  | [], u => if classOf cfg d s = classOf cfg d u then 1 else 0
  | a :: rest, u => (cfg.base.states.map fun v => actionWeight cfg d s a v * word cfg d v rest u).sum

theorem policy_step (src : Schema S A O H R Stage Id Owner) (tgt : Schema T B N H R Stage Id Owner)
    (ds : Data S A O Owner) (dt : Data T B N Owner)
    (m : Maps S T A B Owner) (h : Equations src tgt ds dt m) (s u : S) :
    canonicalWeight tgt dt (m.state s) (m.state u) = canonicalWeight src ds s u := by
  change actionWeight tgt dt (m.state s) (dt.policy (m.state s)) (m.state u) = _
  rw [h.policy]
  exact h.action s (ds.policy s) u

/-- Actual row probabilities use the schema denominator, checked independently
of the integer-numerator equations. -/
def actionProbability (cfg : Schema S A O H R Stage Id Owner) (d : Data S A O Owner)
    (s : S) (a : A) (u : S) : Rat := (actionWeight cfg d s a u : Rat) / cfg.base.rowScale

theorem probability_transport (src : Schema S A O H R Stage Id Owner)
    (tgt : Schema T B N H R Stage Id Owner) (ds : Data S A O Owner)
    (dt : Data T B N Owner) (m : Maps S T A B Owner) (h : Equations src tgt ds dt m)
    (s u : S) (a : A) : actionProbability tgt dt (m.state s) (m.action a) (m.state u) =
      actionProbability src ds s a u := by
  simp only [actionProbability,h.action,h.scale]

theorem word_transport (src : Schema S A O H R Stage Id Owner) (tgt : Schema T B N H R Stage Id Owner)
    (ds : Data S A O Owner) (dt : Data T B N Owner)
    (m : Maps S T A B Owner) (h : Equations src tgt ds dt m) (w : List A) (s u : S) :
    word tgt dt (m.state s) (w.map m.action) (m.state u) = word src ds s w u := by
  induction w generalizing s with
  | nil =>
    simp only [List.map_nil,word,h.predictive]
    have he : m.predictive (classOf src ds s) = m.predictive (classOf src ds u) ↔
        classOf src ds s = classOf src ds u := ⟨h.classInjective s u,congrArg m.predictive⟩
    simp only [he]
  | cons a rest ih =>
    simp only [List.map_cons,word,h.states,List.map_map,Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro v _
    rw [h.action,ih]

omit [DecidableEq Owner] in
/-- The raw row bisimulation derives representative independence for every
finite action word; it is not an input future function. -/
theorem word_sufficient (cfg : Schema S A O H R Stage Id Owner)
    (d : Data S A O Owner)
    (hb : ∀ s t, classOf cfg d s = classOf cfg d t → ∀ a u,
      actionWeight cfg d s a u = actionWeight cfg d t a u)
    (s t : S) (he : classOf cfg d s = classOf cfg d t) (w : List A) (u : S) :
    word cfg d s w u = word cfg d t w u := by
  cases w with
  | nil => simp only [word,he]
  | cons a rest =>
    simp only [word]
    congr 1
    apply List.map_congr_left
    intro v _
    rw [hb s t he a v]

variable {Cell : Type} {Value : Cell → Type}

/-- Maps are raw typed cell instructions; tables are decoded once from the
shared immutable assignment. All derived objects above use those tables. -/
structure Binding (Cell : Type) (Value : Cell → Type)
    (S T A B O N H R Stage Id Owner : Type) where
  source : StaticView Cell Value (Data S A O Owner)
  target : StaticView Cell Value (Data T B N Owner)
  maps : StaticView Cell Value (Maps S T A B Owner)

def Binding.scope (b : Binding Cell Value S T A B O N H R Stage Id Owner) :=
  b.source.dependencies ++ b.target.dependencies ++ b.maps.dependencies

def Pass (src : Schema S A O H R Stage Id Owner) (tgt : Schema T B N H R Stage Id Owner)
    (b : Binding Cell Value S T A B O N H R Stage Id Owner) (a : Assignment Cell Value) : Prop :=
  ∃ ds dt m, b.source.read a = some ds ∧
    b.target.read a = some dt ∧ b.maps.read a = some m ∧
    Equations src tgt ds dt m

theorem locality (src : Schema S A O H R Stage Id Owner) (tgt : Schema T B N H R Stage Id Owner)
    (b : Binding Cell Value S T A B O N H R Stage Id Owner)
    {a a' : Assignment Cell Value} (h : Agrees b.scope a a') : Pass src tgt b a ↔ Pass src tgt b a' := by
  have hs := b.source.locality (fun k hk => h k (by simp [Binding.scope,hk]))
  have ht := b.target.locality (fun k hk => h k (by simp [Binding.scope,hk]))
  have hm := b.maps.locality (fun k hk => h k (by simp [Binding.scope,hk]))
  simp only [Pass,hs,ht,hm]

theorem missing_rejected (src : Schema S A O H R Stage Id Owner) (tgt : Schema T B N H R Stage Id Owner)
    (b : Binding Cell Value S T A B O N H R Stage Id Owner) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ b.scope) (hm : a k = none) : ¬ Pass src tgt b a := by
  simp only [Binding.scope,List.mem_append] at hk
  rcases hk with (hk | hk) | hk
  · simp [Pass,b.source.missing a k hk hm]
  · simp [Pass,b.target.missing a k hk hm]
  · simp [Pass,b.maps.missing a k hk hm]

/-- A mismatched action row, even at a single realized factor, is rejected. -/
theorem action_mismatch_rejected (src : Schema S A O H R Stage Id Owner)
    (tgt : Schema T B N H R Stage Id Owner) (ds : Data S A O Owner)
    (dt : Data T B N Owner) (m : Maps S T A B Owner)
    (s u : S) (a : A)
    (bad : actionWeight tgt dt (m.state s) (m.action a) (m.state u) ≠ actionWeight src ds s a u) :
    ¬ Equations src tgt ds dt m := fun h => bad (h.action s a u)

/-- Per-field guards consume independently computed mismatches. They require
no simultaneous acceptance hypothesis; a bad field precludes the equations. -/
theorem states_mismatch_rejected (src : Schema S A O H R Stage Id Owner)
    (tgt : Schema T B N H R Stage Id Owner) (ds : Data S A O Owner)
    (dt : Data T B N Owner) (m : Maps S T A B Owner)
    (bad : tgt.base.states ≠ src.base.states.map m.state) : ¬ Equations src tgt ds dt m :=
  fun h => bad h.states

theorem coordinate_mismatch_rejected (src : Schema S A O H R Stage Id Owner)
    (tgt : Schema T B N H R Stage Id Owner) (ds : Data S A O Owner)
    (dt : Data T B N Owner) (m : Maps S T A B Owner) (s : S)
    (bad : dt.positions (m.state s) ≠ m.coordinate (ds.positions s)) : ¬ Equations src tgt ds dt m :=
  fun h => bad (h.coordinate s)

theorem predictive_mismatch_rejected (src : Schema S A O H R Stage Id Owner)
    (tgt : Schema T B N H R Stage Id Owner) (ds : Data S A O Owner)
    (dt : Data T B N Owner) (m : Maps S T A B Owner) (s : S)
    (bad : classOf tgt dt (m.state s) ≠ m.predictive (classOf src ds s)) : ¬ Equations src tgt ds dt m :=
  fun h => bad (h.predictive s)

theorem policy_mismatch_rejected (src : Schema S A O H R Stage Id Owner)
    (tgt : Schema T B N H R Stage Id Owner) (ds : Data S A O Owner)
    (dt : Data T B N Owner) (m : Maps S T A B Owner) (s : S)
    (bad : dt.policy (m.state s) ≠ m.action (ds.policy s)) : ¬ Equations src tgt ds dt m :=
  fun h => bad (h.policy s)

theorem tick_mismatch_rejected (src : Schema S A O H R Stage Id Owner)
    (tgt : Schema T B N H R Stage Id Owner) (ds : Data S A O Owner)
    (dt : Data T B N Owner) (m : Maps S T A B Owner) (s : S)
    (bad : dt.ticks (m.state s) (dt.policy (m.state s)) ≠ ds.ticks s (ds.policy s)) :
    ¬ Equations src tgt ds dt m := fun h => bad (h.tick s)

theorem maintenance_mismatch_rejected (src : Schema S A O H R Stage Id Owner)
    (tgt : Schema T B N H R Stage Id Owner) (ds : Data S A O Owner)
    (dt : Data T B N Owner) (m : Maps S T A B Owner)
    (bad : maintained tgt dt ≠ m.maintenance (maintained src ds)) : ¬ Equations src tgt ds dt m :=
  fun h => bad h.maintenance

theorem owner_mismatch_rejected (src : Schema S A O H R Stage Id Owner)
    (tgt : Schema T B N H R Stage Id Owner) (ds : Data S A O Owner)
    (dt : Data T B N Owner) (m : Maps S T A B Owner)
    (bad : dt.resource.owner ≠ m.owner ds.resource.owner) : ¬ Equations src tgt ds dt m :=
  fun h => bad h.owner

theorem class_collapse_rejected (src : Schema S A O H R Stage Id Owner)
    (tgt : Schema T B N H R Stage Id Owner) (ds : Data S A O Owner)
    (dt : Data T B N Owner) (m : Maps S T A B Owner) (s u : S)
    (he : m.predictive (classOf src ds s) = m.predictive (classOf src ds u))
    (bad : classOf src ds s ≠ classOf src ds u) : ¬ Equations src tgt ds dt m :=
  fun h => bad (h.classInjective s u he)

theorem scale_mismatch_rejected (src : Schema S A O H R Stage Id Owner)
    (tgt : Schema T B N H R Stage Id Owner) (ds : Data S A O Owner)
    (dt : Data T B N Owner) (m : Maps S T A B Owner)
    (bad : tgt.base.rowScale ≠ src.base.rowScale) : ¬ Equations src tgt ds dt m := fun h => bad h.scale

end CSTTT.TargetTheory.GenericHandoff.FactorTransport
