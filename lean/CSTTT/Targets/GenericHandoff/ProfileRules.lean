import CSTTT.Targets.GenericHandoff.Substrate

/-! G6d-2a raw C2/C3 algorithms. State, Action and Outcome are arbitrary.
The block probe alphabet and expected trajectory are explicit raw audit data,
not a claimed universal profile theorem. No acceptance callback is supplied.
-/
namespace CSTTT.TargetTheory.GenericHandoff.ProfileRules

structure Raw (S A O : Type) where
  states : List S
  actions : List A
  rows : S → A → List (O × Nat)
  positions : S → Nat
  hazards : O → Bool
  destination : O → Option S
  externalBlock : O → Nat
  revealLabel : Bool
  blocks : List Nat
  split : S × S
  trajectory : Nat × Nat × Nat
  depth : Nat

section Rules
variable {S A O : Type} [DecidableEq S]

def predictive (d : Raw S A O) (s : S) :=
  (d.positions s, d.actions.map fun a => (d.rows s a).map fun e => d.hazards e.1)
def lower (d : Raw S A O) (s : S) :=
  (d.positions s, if d.revealLabel then some s else none)
def Promotion (d : Raw S A O) : Prop :=
  lower d d.split.1 = lower d d.split.2 ∧ predictive d d.split.1 ≠ predictive d d.split.2

def seed (d : Raw S A O) (s : S) :=
  if d.revealLabel then d.states.idxOf s else d.positions s
def block (d : Raw S A O) (classes : S → Nat) (o : O) :=
  match d.destination o with | some s => classes s | none => d.externalBlock o
def mass (d : Raw S A O) (classes : S → Nat) (s : S) (a : A) (b : Nat) :=
  (d.rows s a).foldl (fun n e => if block d classes e.1 = b then n + e.2 else n) 0
def signature (d : Raw S A O) (classes : S → Nat) (s : S) :=
  (classes s, d.actions.map fun a => d.blocks.map (mass d classes s a))
def step (d : Raw S A O) (classes : S → Nat) (s : S) :=
  ((d.states.map (signature d classes)).eraseDups).idxOf (signature d classes s)
def iterate (d : Raw S A O) : Nat → (S → Nat)
  | 0 => seed d
  | n + 1 => step d (iterate d n)
def first (d : Raw S A O) := iterate d d.depth
def second (d : Raw S A O) := step d (first d)
def count (d : Raw S A O) (classes : S → Nat) :=
  ((d.states.map classes).eraseDups).length
def SamePartition {X Y : Type} (f : S → X) (g : S → Y) : Prop :=
  ∀ s t, (f s = f t) ↔ (g s = g t)
def RecursiveProfile (d : Raw S A O) : Prop :=
  count d (seed d) = d.trajectory.1 ∧ count d (first d) = d.trajectory.2.1 ∧
  count d (second d) = d.trajectory.2.2 ∧
  SamePartition (first d) (second d) ∧ SamePartition (second d) (predictive d)

/-- A local rule receives only a successfully decoded raw record. There is
no default record and no supplied acceptance predicate. -/
def PromotionAt (d : Option (Raw S A O)) : Prop :=
  ∃ r, d = some r ∧ Promotion r
def ProfileAt (d : Option (Raw S A O)) : Prop :=
  ∃ r, d = some r ∧ RecursiveProfile r
omit [DecidableEq S] in
@[simp] theorem promotion_some (d : Raw S A O) : PromotionAt (some d) ↔ Promotion d := by
  simp [PromotionAt]
@[simp] theorem profile_some (d : Raw S A O) : ProfileAt (some d) ↔ RecursiveProfile d := by
  simp [ProfileAt]
omit [DecidableEq S] in
@[simp] theorem missing_promotion : ¬ PromotionAt (none : Option (Raw S A O)) := by
  simp [PromotionAt]
@[simp] theorem missing_profile : ¬ ProfileAt (none : Option (Raw S A O)) := by
  simp [ProfileAt]

omit [DecidableEq S] in
/-- A genuine split blocks factorization, not merely an assigned class label. -/
theorem promotion_nonfactorization (d : Raw S A O) (h : Promotion d) :
    ¬ ∃ f : (Nat × Option S) → (Nat × List (List Bool)),
      ∀ s, predictive d s = f (lower d s) := by
  rintro ⟨f,hf⟩
  apply h.2
  rw [hf, hf, h.1]

omit [DecidableEq S] in
theorem exposed_split_rejected (d : Raw S A O) (h : d.revealLabel = true)
    (hne : d.split.1 ≠ d.split.2) : ¬ Promotion d := by
  intro hp
  have he := congrArg Prod.snd hp.1
  simp [lower,h] at he
  exact hne he

omit [DecidableEq S] in
theorem constant_predictive_rejected (d : Raw S A O)
    (h : predictive d d.split.1 = predictive d d.split.2) : ¬ Promotion d :=
  fun hp => hp.2 h

theorem wrong_trajectory_rejected (d : Raw S A O)
    (h : count d (seed d) ≠ d.trajectory.1) : ¬ RecursiveProfile d :=
  fun hp => h hp.1

/-- An additional completion gate, not a replacement for the legacy family
assay: a genuinely fixed computed profile and coverage of every support block. -/
def BlockCoverage (d : Raw S A O) (c : S → Nat) : Prop :=
  ∀ s ∈ d.states, ∀ a ∈ d.actions, ∀ e ∈ d.rows s a, block d c e.1 ∈ d.blocks
def blockCoverageCheck (d : Raw S A O) (c : S → Nat) : Bool :=
  d.states.all fun s => d.actions.all fun a =>
    (d.rows s a).all fun e => decide (block d c e.1 ∈ d.blocks)
omit [DecidableEq S] in
theorem block_coverage_iff (d : Raw S A O) (c : S → Nat) :
    blockCoverageCheck d c = true ↔ BlockCoverage d c := by
  simp [blockCoverageCheck,BlockCoverage,List.all_eq_true]
def StableProfile (d : Raw S A O) : Prop :=
  RecursiveProfile d ∧ step d (second d) = second d ∧
    BlockCoverage d (first d) ∧ BlockCoverage d (second d)

theorem stable_forever (d : Raw S A O) (h : StableProfile d) (n : Nat) :
    iterate d (d.depth + 1 + n) = second d := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [Nat.add_succ,iterate]
    change step d (iterate d (d.depth + 1 + n)) = second d
    rw [ih,h.2.1]

theorem unstable_rejected (d : Raw S A O)
    (h : step d (second d) ≠ second d) : ¬ StableProfile d := fun hs => h hs.2.1

theorem omitted_block_rejected (d : Raw S A O) (s : S) (a : A) (e : O × Nat)
    (hs : s ∈ d.states) (ha : a ∈ d.actions) (he : e ∈ d.rows s a)
    (hb : block d (second d) e.1 ∉ d.blocks) : ¬ StableProfile d :=
  fun h => hb (h.2.2.2 s hs a ha e he)

end Rules

/-- Audit-domain data, independent of assigned primitives. -/
structure Schema (S A O : Type) where
  states : List S
  actions : List A
  destination : O → Option S
  externalBlock : O → Nat
  blocks : List Nat
  split : S × S
  trajectory : Nat × Nat × Nat
  depth : Nat

structure Bindings (Cell : Type) (Value : Cell → Type) (S A O : Type) where
  rows : CellView Cell Value (S → A → List (O × Nat))
  positions : CellView Cell Value (S → Nat)
  hazards : CellView Cell Value (O → Bool)
  reveal : CellView Cell Value Bool

section Decoder
variable {Cell S A O : Type} {Value : Cell → Type}

def Bindings.scope (v : Bindings Cell Value S A O) : List Cell :=
  [v.rows.cell,v.positions.cell,v.hazards.cell,v.reveal.cell]
def decoded (cfg : Schema S A O) (v : Bindings Cell Value S A O)
    (a : Assignment Cell Value) : Option (Raw S A O) := do
  let rows ← v.rows.read a
  let positions ← v.positions.read a
  let hazards ← v.hazards.read a
  let reveal ← v.reveal.read a
  pure ⟨cfg.states,cfg.actions,rows,positions,hazards,cfg.destination,
    cfg.externalBlock,reveal,cfg.blocks,cfg.split,cfg.trajectory,cfg.depth⟩

theorem decoded_locality (cfg : Schema S A O) (v : Bindings Cell Value S A O)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) :
    decoded cfg v a = decoded cfg v b := by
  have hr := view_locality v.rows (h _ (by simp [Bindings.scope]))
  have hp := view_locality v.positions (h _ (by simp [Bindings.scope]))
  have hh := view_locality v.hazards (h _ (by simp [Bindings.scope]))
  have hv := view_locality v.reveal (h _ (by simp [Bindings.scope]))
  simp only [decoded,hr,hp,hh,hv]

theorem missing_rows (cfg : Schema S A O) (v : Bindings Cell Value S A O)
    (a : Assignment Cell Value) (h : a v.rows.cell = none) : decoded cfg v a = none := by
  simp [decoded,CellView.read,h]
theorem missing_positions (cfg : Schema S A O) (v : Bindings Cell Value S A O)
    (a : Assignment Cell Value) (h : a v.positions.cell = none) : decoded cfg v a = none := by
  simp [decoded,CellView.read,h]
theorem missing_hazards (cfg : Schema S A O) (v : Bindings Cell Value S A O)
    (a : Assignment Cell Value) (h : a v.hazards.cell = none) : decoded cfg v a = none := by
  simp [decoded,CellView.read,h]
theorem missing_reveal (cfg : Schema S A O) (v : Bindings Cell Value S A O)
    (a : Assignment Cell Value) (h : a v.reveal.cell = none) : decoded cfg v a = none := by
  simp [decoded,CellView.read,h]

end Decoder

structure ClauseSchema (S A O : Type) extends Schema S A O where
  outcomes : List O
  rowScale : Nat
  referenceClasses : S → Nat

structure ClauseBindings (Cell : Type) (Value : Cell → Type) (S A O : Type) where
  primitives : Bindings Cell Value S A O
  classes : CellView Cell Value (S → Nat)

section Clauses
variable {Cell S A O : Type} {Value : Cell → Type}
  [DecidableEq S] [DecidableEq O]

def ClauseBindings.scope (v : ClauseBindings Cell Value S A O) :=
  v.primitives.scope ++ [v.classes.cell]
def decodedClause (cfg : ClauseSchema S A O) (v : ClauseBindings Cell Value S A O)
    (a : Assignment Cell Value) : Option (Raw S A O × (S → Nat)) := do
  let r ← decoded cfg.toSchema v.primitives a
  let labels ← v.classes.read a
  pure (r,labels)
def RowsValid (cfg : ClauseSchema S A O) (d : Raw S A O) : Prop :=
  (d.states.all fun s => d.actions.all fun act =>
    let row := d.rows s act
    let total := row.foldl (fun n e => n + e.2) 0
    row.all (fun e => decide (e.2 > 0 ∧ e.1 ∈ cfg.outcomes)) &&
      (total == 0 || total == cfg.rowScale)) = true
def Linked (cfg : ClauseSchema S A O) (d : Raw S A O) (labels : S → Nat) : Prop :=
  labels = cfg.referenceClasses ∧ SamePartition (predictive d) labels

/-- Complete finite domains are checked separately from the profile trajectory.
An empty enumeration cannot stand in for any inhabited carrier/action/outcome. -/
def DomainCheck (cfg : ClauseSchema S A O) : Prop :=
  cfg.states.Nodup ∧ cfg.actions.Nodup ∧ cfg.outcomes.Nodup ∧
  (∀ s, s ∈ cfg.states) ∧ (∀ a, a ∈ cfg.actions) ∧ (∀ o, o ∈ cfg.outcomes)

def Gate (cfg : ClauseSchema S A O) (v : ClauseBindings Cell Value S A O)
    (a : Assignment Cell Value) : Prop :=
  DomainCheck cfg ∧ ∃ d labels, decodedClause cfg v a = some (d,labels) ∧
    RowsValid cfg d ∧ Linked cfg d labels

def C2Accept (cfg : ClauseSchema S A O) (v : ClauseBindings Cell Value S A O)
    (a : Assignment Cell Value) : Prop :=
  DomainCheck cfg ∧ ∃ d labels, decodedClause cfg v a = some (d,labels) ∧
    RowsValid cfg d ∧ Linked cfg d labels ∧ Promotion d

def C3Accept (cfg : ClauseSchema S A O) (v : ClauseBindings Cell Value S A O)
    (a : Assignment Cell Value) : Prop :=
  DomainCheck cfg ∧ ∃ d labels, decodedClause cfg v a = some (d,labels) ∧
    RowsValid cfg d ∧ Linked cfg d labels ∧ RecursiveProfile d

omit [DecidableEq S] [DecidableEq O] in
theorem clause_decoder_locality (cfg : ClauseSchema S A O)
    (v : ClauseBindings Cell Value S A O) {a b : Assignment Cell Value}
    (h : Agrees v.scope a b) : decodedClause cfg v a = decodedClause cfg v b := by
  have hp := decoded_locality cfg.toSchema v.primitives
    (fun k hk => h k (by simp [ClauseBindings.scope,hk]))
  have hl := view_locality v.classes (h _ (by simp [ClauseBindings.scope]))
  simp only [decodedClause,hp,hl]

omit [DecidableEq S] in
theorem gate_locality (cfg : ClauseSchema S A O) (v : ClauseBindings Cell Value S A O)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : Gate cfg v a ↔ Gate cfg v b := by
  simp only [Gate,clause_decoder_locality cfg v h]
omit [DecidableEq S] in
theorem c2_locality (cfg : ClauseSchema S A O) (v : ClauseBindings Cell Value S A O)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : C2Accept cfg v a ↔ C2Accept cfg v b := by
  simp only [C2Accept,clause_decoder_locality cfg v h]
theorem c3_locality (cfg : ClauseSchema S A O) (v : ClauseBindings Cell Value S A O)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : C3Accept cfg v a ↔ C3Accept cfg v b := by
  simp only [C3Accept,clause_decoder_locality cfg v h]

theorem missing_clause_input (cfg : ClauseSchema S A O) (v : ClauseBindings Cell Value S A O)
    (a : Assignment Cell Value) (h : decodedClause cfg v a = none) :
    ¬ Gate cfg v a ∧ ¬ C2Accept cfg v a ∧ ¬ C3Accept cfg v a := by
  simp [Gate,C2Accept,C3Accept,h]

omit [DecidableEq S] in
theorem c2_nonfactorization (cfg : ClauseSchema S A O) (v : ClauseBindings Cell Value S A O)
    (a : Assignment Cell Value) (h : C2Accept cfg v a) :
    ∃ d labels, decodedClause cfg v a = some (d,labels) ∧
      ¬ ∃ f : (Nat × Option S) → (Nat × List (List Bool)),
        ∀ s, predictive d s = f (lower d s) := by
  obtain ⟨_,d,labels,hd,_,_,hp⟩ := h
  exact ⟨d,labels,hd,promotion_nonfactorization d hp⟩

omit [DecidableEq S] [DecidableEq O] in
theorem missing_consumed_cell (cfg : ClauseSchema S A O)
    (v : ClauseBindings Cell Value S A O) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ v.scope) (h : a k = none) : decodedClause cfg v a = none := by
  simp [ClauseBindings.scope,Bindings.scope] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl <;>
    simp [decodedClause,decoded,CellView.read,h]

theorem missing_cell_rejected (cfg : ClauseSchema S A O)
    (v : ClauseBindings Cell Value S A O) (a : Assignment Cell Value) (k : Cell)
    (hk : k ∈ v.scope) (h : a k = none) :
    ¬ Gate cfg v a ∧ ¬ C2Accept cfg v a ∧ ¬ C3Accept cfg v a :=
  missing_clause_input cfg v a (missing_consumed_cell cfg v a k hk h)


theorem invalid_rows_rejected (cfg : ClauseSchema S A O)
    (v : ClauseBindings Cell Value S A O) (a : Assignment Cell Value)
    (d : Raw S A O) (labels : S → Nat)
    (hd : decodedClause cfg v a = some (d,labels)) (hr : ¬ RowsValid cfg d) :
    ¬ Gate cfg v a ∧ ¬ C2Accept cfg v a ∧ ¬ C3Accept cfg v a := by
  have hg : ¬ Gate cfg v a := by
    rintro ⟨_,r,l,he,hrow,_⟩
    have eq := Option.some.inj (hd.symm.trans he)
    cases eq
    exact hr hrow
  refine ⟨hg,?_,?_⟩
  · rintro ⟨hdom,r,l,he,hrow,hl,_⟩; exact hg ⟨hdom,r,l,he,hrow,hl⟩
  · rintro ⟨hdom,r,l,he,hrow,hl,_⟩; exact hg ⟨hdom,r,l,he,hrow,hl⟩

omit [DecidableEq S] in
theorem changed_classes_rejected (cfg : ClauseSchema S A O)
    (v : ClauseBindings Cell Value S A O) (a : Assignment Cell Value)
    (d : Raw S A O) (labels : S → Nat)
    (hd : decodedClause cfg v a = some (d,labels)) (hr : labels ≠ cfg.referenceClasses) :
    ¬ Gate cfg v a := by
  rintro ⟨_,r,l,he,_,hl⟩
  have eq := Option.some.inj (hd.symm.trans he)
  cases eq
  exact hr hl.1

omit [DecidableEq S] [DecidableEq O] in
theorem missing_domain_state (cfg : ClauseSchema S A O) (s : S)
    (h : s ∉ cfg.states) : ¬ DomainCheck cfg := fun hd => h (hd.2.2.2.1 s)

end Clauses


end CSTTT.TargetTheory.GenericHandoff.ProfileRules
