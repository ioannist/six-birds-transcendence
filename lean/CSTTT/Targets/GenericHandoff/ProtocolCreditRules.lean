import CSTTT.Targets.GenericHandoff.Substrate

/-! Generic C5 protocol-credit surrogate. Vertices, edges, protocols, owners,
state/action/outcome/history domains and immutable cells are polymorphic.
Cycle products and provenance credits are computed; this is not full T5. -/
namespace CSTTT.TargetTheory.GenericHandoff.ProtocolCreditRules

inductive Credit where | self | other | none | ambiguous deriving DecidableEq, Repr

structure Tables (Id Edge Owner : Type) where
  edges : Id → List Edge
  owner : Id → Owner
  housing : Id → Owner

structure Schema (S A O V Ch Id H Owner Edge : Type) where
  states : List S
  actions : List A
  outcomes : List O
  vertices : List V
  protocols : List Id
  cycle : List V
  edgeFrom : Edge → V
  edgeTo : Edge → V
  edgeChannel : Edge → Ch
  selfChannel : Ch
  otherChannel : Ch
  destination : O → Option S
  rowScale : Nat
  anchor : V → H
  selfOwner : Owner
  otherOwner : Owner
  expected : Id → Credit

structure Raw (S A O Id H Owner Edge : Type) where
  tables : Tables Id Edge Owner
  rows : S → A → List (O × Nat)
  policy : S → A
  histories : H → List S

section Rules
variable {S A O V Ch Id H Owner Edge : Type}
  [DecidableEq S] [DecidableEq V] [DecidableEq Ch]
  (cfg : Schema S A O V Ch Id H Owner Edge)
  (d : Raw S A O Id H Owner Edge)

def count (id : Id) (a b : V) (ch : Ch) : Nat :=
  ((d.tables.edges id).filter fun e => decide (cfg.edgeFrom e = a) &&
    decide (cfg.edgeTo e = b) && decide (cfg.edgeChannel e = ch)).length

def cycleEdges : List (V × V) := cfg.cycle.zip (cfg.cycle.drop 1 ++ cfg.cycle.take 1)
def forward (id : Id) (ch : Ch) : Nat :=
  ((cycleEdges cfg).map fun e => count cfg d id e.1 e.2 ch).foldr (· * ·) 1
def reverse (id : Id) (ch : Ch) : Nat :=
  ((cycleEdges cfg).map fun e => count cfg d id e.2 e.1 ch).foldr (· * ·) 1

def credit (id : Id) : Credit :=
  let selfAsym := forward cfg d id cfg.selfChannel != reverse cfg d id cfg.selfChannel
  let otherAsym := forward cfg d id cfg.otherChannel != reverse cfg d id cfg.otherChannel
  if selfAsym && otherAsym then .ambiguous
  else if selfAsym then .self else if otherAsym then .other else .none

def weight (s t : S) : Nat :=
  ((d.rows s (d.policy s)).map fun e =>
    if cfg.destination e.1 = some t then e.2 else 0).sum

def supported (h : H) : Bool :=
  let path := d.histories h
  !path.isEmpty && ((path.zip (path.drop 1)).all fun e => decide (weight cfg d e.1 e.2 > 0))

def Rule : Prop :=
  (∀ id ∈ cfg.protocols, credit cfg d id = cfg.expected id) ∧
  (∀ id ∈ cfg.protocols,
    (credit cfg d id = .self → d.tables.owner id = cfg.selfOwner) ∧
    (credit cfg d id = .other → d.tables.owner id = cfg.otherOwner)) ∧
  (∀ v ∈ cfg.vertices, supported cfg d (cfg.anchor v) = true)

variable [DecidableEq O]
def RowsValid : Prop :=
  (cfg.states.all fun s => cfg.actions.all fun a =>
    let row := d.rows s a
    let total := row.foldl (fun n e => n + e.2) 0
    row.all (fun e => decide (e.2 > 0 ∧ e.1 ∈ cfg.outcomes)) &&
      (total == 0 || total == cfg.rowScale)) = true

def DomainCheck : Prop :=
  cfg.states.Nodup ∧ (∀ s, s ∈ cfg.states) ∧
  cfg.actions.Nodup ∧ (∀ a, a ∈ cfg.actions) ∧
  cfg.outcomes.Nodup ∧ (∀ o, o ∈ cfg.outcomes) ∧
  cfg.vertices.Nodup ∧ (∀ v, v ∈ cfg.vertices) ∧
  cfg.protocols.Nodup ∧ (∀ id, id ∈ cfg.protocols)

def CreditCoverage : Prop :=
  ∀ c ∈ [Credit.self,Credit.other,Credit.none], ∃ id ∈ cfg.protocols, cfg.expected id = c

def Gate : Prop :=
  DomainCheck cfg ∧ CreditCoverage cfg ∧ cfg.cycle.length ≥ 2 ∧
    cfg.selfChannel ≠ cfg.otherChannel ∧ RowsValid cfg d

def Accept : Prop := Gate cfg d ∧ Rule cfg d

theorem wrong_credit_rejected (id : Id) (hi : id ∈ cfg.protocols)
    (h : credit cfg d id ≠ cfg.expected id) : ¬ Accept cfg d := fun ha => h (ha.2.1 id hi)

theorem wrong_self_owner_rejected (id : Id) (hi : id ∈ cfg.protocols)
    (hc : credit cfg d id = .self) (h : d.tables.owner id ≠ cfg.selfOwner) :
    ¬ Accept cfg d := fun ha => h ((ha.2.2.1 id hi).1 hc)

theorem unsupported_anchor_rejected (v : V) (hv : v ∈ cfg.vertices)
    (h : supported cfg d (cfg.anchor v) ≠ true) : ¬ Accept cfg d :=
  fun ha => h (ha.2.2.2 v hv)

theorem empty_cycle_rejected (h : cfg.cycle = []) : ¬ Accept cfg d := by
  intro ha
  have hc := ha.1.2.2.1
  simp [h] at hc

omit [DecidableEq S] [DecidableEq O] in
theorem empty_edges_credit (id : Id) (h : d.tables.edges id = []) : credit cfg d id = .none := by
  have he (ch : Ch) : forward cfg d id ch = reverse cfg d id ch := by
    simp [forward,reverse,count,h]
  simp [credit,he]

theorem empty_generator_rejected (id : Id) (hi : id ∈ cfg.protocols)
    (hx : cfg.expected id ≠ .none) (he : d.tables.edges id = []) : ¬ Accept cfg d := by
  apply wrong_credit_rejected cfg d id hi
  rw [empty_edges_credit cfg d id he]
  exact Ne.symm hx


omit [DecidableEq S] [DecidableEq V] [DecidableEq Ch] in
theorem equal_channels_rejected (h : cfg.selfChannel = cfg.otherChannel) : ¬ Gate cfg d :=
  fun hg => hg.2.2.2.1 h

omit [DecidableEq S] [DecidableEq V] [DecidableEq Ch] in
theorem missing_self_role_rejected (h : ∀ id, cfg.expected id ≠ .self) : ¬ Gate cfg d := by
  intro hg
  obtain ⟨id,_,he⟩ := hg.2.1 .self (by simp)
  exact h id he

omit [DecidableEq S] [DecidableEq V] [DecidableEq Ch] in
theorem missing_state_rejected (s : S) (h : s ∉ cfg.states) : ¬ Gate cfg d :=
  fun hg => h (hg.1.2.1 s)

end Rules

/-- Raw table transport on a declared protocol comparison domain. -/
def Transport {SI TI SO TO SE TE : Type}
    (source : Tables SI SE SO) (target : Tables TI TE TO)
    (ids : List SI) (idMap : SI → TI) (edgeMap : SE → TE) (ownerMap : SO → TO) : Prop :=
  ∀ id ∈ ids, (source.edges id).map edgeMap = target.edges (idMap id) ∧
    ownerMap (source.owner id) = target.owner (idMap id) ∧
    ownerMap (source.housing id) = target.housing (idMap id)


structure Bindings (Cell : Type) (Value : Cell → Type) (S A O Id H Owner Edge : Type) where
  tables : CellView Cell Value (Tables Id Edge Owner)
  rows : CellView Cell Value (S → A → List (O × Nat))
  policy : CellView Cell Value (S → A)
  histories : CellView Cell Value (H → List S)

section Decoder
variable {Cell S A O V Ch Id H Owner Edge : Type} {Value : Cell → Type}

def Bindings.scope (v : Bindings Cell Value S A O Id H Owner Edge) : List Cell :=
  [v.tables.cell,v.rows.cell,v.policy.cell,v.histories.cell]

def decoded (v : Bindings Cell Value S A O Id H Owner Edge) (a : Assignment Cell Value) :
    Option (Raw S A O Id H Owner Edge) := do
  let tables ← v.tables.read a
  let rows ← v.rows.read a
  let policy ← v.policy.read a
  let histories ← v.histories.read a
  pure ⟨tables,rows,policy,histories⟩

theorem decoded_locality (v : Bindings Cell Value S A O Id H Owner Edge)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : decoded v a = decoded v b := by
  have ht := view_locality v.tables (h _ (by simp [Bindings.scope]))
  have hr := view_locality v.rows (h _ (by simp [Bindings.scope]))
  have hp := view_locality v.policy (h _ (by simp [Bindings.scope]))
  have hh := view_locality v.histories (h _ (by simp [Bindings.scope]))
  simp only [decoded,ht,hr,hp,hh]

theorem missing_consumed (v : Bindings Cell Value S A O Id H Owner Edge)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) :
    decoded v a = none := by
  simp only [Bindings.scope,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with h | h | h | h <;> subst k <;> simp [decoded,CellView.read,hm]

variable [DecidableEq S] [DecidableEq V] [DecidableEq Ch] [DecidableEq O]
def AssignedGate (cfg : Schema S A O V Ch Id H Owner Edge)
    (v : Bindings Cell Value S A O Id H Owner Edge) (a : Assignment Cell Value) : Prop :=
  ∃ d, decoded v a = some d ∧ Gate cfg d

def AssignedAccept (cfg : Schema S A O V Ch Id H Owner Edge)
    (v : Bindings Cell Value S A O Id H Owner Edge) (a : Assignment Cell Value) : Prop :=
  ∃ d, decoded v a = some d ∧ Accept cfg d

omit [DecidableEq S] [DecidableEq V] [DecidableEq Ch] in
theorem gate_locality (cfg : Schema S A O V Ch Id H Owner Edge)
    (v : Bindings Cell Value S A O Id H Owner Edge) {a b : Assignment Cell Value}
    (h : Agrees v.scope a b) : AssignedGate cfg v a ↔ AssignedGate cfg v b := by
  unfold AssignedGate; rw [decoded_locality v h]

theorem acceptance_locality (cfg : Schema S A O V Ch Id H Owner Edge)
    (v : Bindings Cell Value S A O Id H Owner Edge) {a b : Assignment Cell Value}
    (h : Agrees v.scope a b) : AssignedAccept cfg v a ↔ AssignedAccept cfg v b := by
  unfold AssignedAccept; rw [decoded_locality v h]

theorem missing_rejected (cfg : Schema S A O V Ch Id H Owner Edge)
    (v : Bindings Cell Value S A O Id H Owner Edge) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) :
    ¬ AssignedGate cfg v a ∧ ¬ AssignedAccept cfg v a := by
  have h := missing_consumed v a k hk hm
  simp [AssignedGate,AssignedAccept,h]

end Decoder
end CSTTT.TargetTheory.GenericHandoff.ProtocolCreditRules
