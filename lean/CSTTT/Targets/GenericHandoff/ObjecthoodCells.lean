import CSTTT.Targets.GenericHandoff.ObjecthoodRules

/-! Typed C1 primitive decoding. All required inputs are Option reads; a
missing input prevents reconstruction before any numerical rule is applied.
No distribution, quotient, closure operator or uniqueness verdict is supplied.
-/
namespace CSTTT.TargetTheory.GenericHandoff.ObjecthoodCells

structure Parameters (S : Type) where
  rowScale : Nat
  tau : Nat
  epsilon : Rat
  core : List S
  anchor : S
  operations : List (FixedPointVerifier.RowOperation S)
  retention : Rat
  expectedTV : Rat
  expectedZeroDefect : Rat
  expectedDefect : Rat

structure Bindings (Cell : Type) (Value : Cell → Type) (S A O : Type) where
  rows : CellView Cell Value (S → A → List (O × Nat))
  positions : CellView Cell Value (S → Nat)
  hazards : CellView Cell Value (O → Bool)
  policy : CellView Cell Value (S → A)
  prototypes : CellView Cell Value (List S)
  parameters : CellView Cell Value (Parameters S)
  publishedP : CellView Cell Value (S → S → Rat)
  publishedC : CellView Cell Value (S → Nat → Rat)
  publishedU : CellView Cell Value (Nat → S → Rat)

section Decode
variable {Cell S A O : Type} {Value : Cell → Type}

def Bindings.scope (v : Bindings Cell Value S A O) : List Cell :=
  [v.rows.cell,v.positions.cell,v.hazards.cell,v.policy.cell,v.prototypes.cell,
   v.parameters.cell,v.publishedP.cell,v.publishedC.cell,v.publishedU.cell]

def decoded (cfg : ProfileRules.Schema S A O) (v : Bindings Cell Value S A O)
    (a : Assignment Cell Value) : Option (ObjecthoodRules.Raw S A O) := do
  let rows ← v.rows.read a
  let positions ← v.positions.read a
  let hazards ← v.hazards.read a
  let policy ← v.policy.read a
  let prototypes ← v.prototypes.read a
  let p ← v.parameters.read a
  let publishedP ← v.publishedP.read a
  let publishedC ← v.publishedC.read a
  let publishedU ← v.publishedU.read a
  let profile : ProfileRules.Raw S A O :=
    ⟨cfg.states,cfg.actions,rows,positions,hazards,cfg.destination,cfg.externalBlock,
      false,cfg.blocks,cfg.split,cfg.trajectory,cfg.depth⟩
  pure ⟨profile,policy,prototypes,p.rowScale,p.tau,p.epsilon,p.core,p.anchor,p.operations,
    publishedP,publishedC,publishedU,p.retention,p.expectedTV,p.expectedZeroDefect,p.expectedDefect⟩

theorem decoder_locality (cfg : ProfileRules.Schema S A O)
    (v : Bindings Cell Value S A O) {a b : Assignment Cell Value}
    (h : Agrees v.scope a b) : decoded cfg v a = decoded cfg v b := by
  have h1 := view_locality v.rows (h _ (by simp [Bindings.scope]))
  have h2 := view_locality v.positions (h _ (by simp [Bindings.scope]))
  have h3 := view_locality v.hazards (h _ (by simp [Bindings.scope]))
  have h4 := view_locality v.policy (h _ (by simp [Bindings.scope]))
  have h5 := view_locality v.prototypes (h _ (by simp [Bindings.scope]))
  have h6 := view_locality v.parameters (h _ (by simp [Bindings.scope]))
  have h7 := view_locality v.publishedP (h _ (by simp [Bindings.scope]))
  have h8 := view_locality v.publishedC (h _ (by simp [Bindings.scope]))
  have h9 := view_locality v.publishedU (h _ (by simp [Bindings.scope]))
  simp only [decoded,h1,h2,h3,h4,h5,h6,h7,h8,h9]

theorem missing_input (cfg : ProfileRules.Schema S A O)
    (v : Bindings Cell Value S A O) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ v.scope) (h : a k = none) : decoded cfg v a = none := by
  simp [Bindings.scope] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [decoded,CellView.read,h]

end Decode

section Rules
variable {Cell S A O : Type} {Value : Cell → Type} [DecidableEq S]
def Gate (cfg : ProfileRules.Schema S A O) (v : Bindings Cell Value S A O)
    (a : Assignment Cell Value) : Prop :=
  ∃ d, decoded cfg v a = some d ∧ ObjecthoodRules.Gate d
def Accept (cfg : ProfileRules.Schema S A O) (v : Bindings Cell Value S A O)
    (a : Assignment Cell Value) : Prop :=
  ∃ d, decoded cfg v a = some d ∧ ObjecthoodRules.Accept d

theorem gate_locality (cfg : ProfileRules.Schema S A O) (v : Bindings Cell Value S A O)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : Gate cfg v a ↔ Gate cfg v b := by
  simp only [Gate,decoder_locality cfg v h]
theorem acceptance_locality (cfg : ProfileRules.Schema S A O) (v : Bindings Cell Value S A O)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : Accept cfg v a ↔ Accept cfg v b := by
  simp only [Accept,decoder_locality cfg v h]
theorem missing_rejected (cfg : ProfileRules.Schema S A O)
    (v : Bindings Cell Value S A O) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ v.scope) (h : a k = none) : ¬ Gate cfg v a ∧ ¬ Accept cfg v a := by
  simp [Gate,Accept,missing_input cfg v a k hk h]

theorem accepted_unique (cfg : ProfileRules.Schema S A O)
    (v : Bindings Cell Value S A O) (a : Assignment Cell Value) (h : Accept cfg v a) :
    ∃ d, decoded cfg v a = some d ∧
      FixedPointVerifier.Probability d.profile.states (ObjecthoodRules.pi d) ∧
      FixedPointVerifier.Fixed d.profile.states (ObjecthoodRules.E d) (ObjecthoodRules.pi d) ∧
      ∀ x, FixedPointVerifier.Probability d.profile.states x →
        FixedPointVerifier.Fixed d.profile.states (ObjecthoodRules.E d) x → x = ObjecthoodRules.pi d := by
  obtain ⟨d,hd,ha⟩ := h
  have hp := ObjecthoodRules.checked_probability_fixed_unique d ha.1
  exact ⟨d,hd,hp⟩
end Rules
end CSTTT.TargetTheory.GenericHandoff.ObjecthoodCells
