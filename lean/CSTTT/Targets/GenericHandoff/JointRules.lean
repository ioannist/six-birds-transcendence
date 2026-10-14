import CSTTT.Targets.GenericHandoff.Substrate

/-! Generic C7 recombination surrogate (M3 spec:23). All distributions,
quotients and receiver displays are interpreted from raw tables. Coupling is
independently declared, not a theorem about the stochastic carrier's dynamics. -/
namespace CSTTT.TargetTheory.GenericHandoff.JointRules
structure Tables (D H L R Assembly Observable : Type) where
  left : D → L → H
  right : D → R → H
  coupling : D → List (L × R)
  reassembly : D → Assembly
  observables : List Observable

structure Event (Stage Id : Type) where
  id : Id
  fromStage : Stage
  toStage : Stage
  atomic : Bool
  sourceSupport : Bool
  targetSupport : Bool
  deriving DecidableEq
structure Receiver where
  sourcePresent : Bool
  targetFunded : Bool
  funded : Bool
  mixedRequired : Bool
  deriving DecidableEq

structure Schema (S A O D H L R Assembly Observable Stage Id : Type) where
  states : List S
  actions : List A
  outcomes : List O
  histories : List H
  lefts : List L
  rights : List R
  assemblages : List D
  split : D × D
  jointObservable : Observable
  reassemble : Assembly → List (L × R)
  couplingSize : Nat
  exitId : Id
  destination : O → Option S
  rowScale : Nat
  canonicalP : S → S → Nat

structure Raw (S A O D H L R Assembly Observable Stage Id : Type) where
  joint : Tables D H L R Assembly Observable
  rows : S → A → List (O × Nat)
  policy : S → A
  histories : H → List S
  publishedP : S → S → Nat
  events : List (Event Stage Id)
  realized : List Stage
  receiver : Receiver

section Rules
variable {S A O D H L R Assembly Observable Stage Id : Type}
  [DecidableEq S] [DecidableEq Observable] [DecidableEq Stage] [DecidableEq Id]
  (cfg : Schema S A O D H L R Assembly Observable Stage Id)
  (d : Raw S A O D H L R Assembly Observable Stage Id)

def weight (s t : S) := ((d.rows s (d.policy s)).map fun e =>
  if cfg.destination e.1 = some t then e.2 else 0).sum

def supported (h : H) : Bool :=
  let path := d.histories h
  !path.isEmpty && ((path.zip (path.drop 1)).all fun e => decide (weight cfg d e.1 e.2 > 0))

def pairCount (id : D) (l r : H) : Nat :=
  ((d.joint.coupling id).filter fun p =>
    decide (d.histories (d.joint.left id p.1) = d.histories l) &&
    decide (d.histories (d.joint.right id p.2) = d.histories r)).length

def pairing (id : D) (l r : H) : Rat := (pairCount d id l r : Rat) / (d.joint.coupling id).length

def branchwise (id : D) :=
  (cfg.lefts.map fun l => d.histories (d.joint.left id l),
   cfg.rights.map fun r => d.histories (d.joint.right id r))

def distribution (id : D) : List (Nat × Nat) :=
  cfg.histories.flatMap fun l => cfg.histories.map fun r => (pairCount d id l r,(d.joint.coupling id).length)

def display (id : D) : List (Nat × Nat) :=
  if cfg.jointObservable ∈ d.joint.observables then distribution cfg d id else []
def recombination (id : D) := (branchwise cfg d id,display cfg d id)

def Strict : Prop := cfg.split.1 ≠ cfg.split.2 ∧
  branchwise cfg d cfg.split.1 = branchwise cfg d cfg.split.2 ∧
  recombination cfg d cfg.split.1 ≠ recombination cfg d cfg.split.2

def Local : Prop := ∀ id ∈ cfg.assemblages,
  d.joint.coupling id = cfg.reassemble (d.joint.reassembly id) ∧
  (d.joint.coupling id).length = cfg.couplingSize ∧ (d.joint.coupling id).Nodup

def Histories : Prop := ∀ h ∈ cfg.histories, supported cfg d h = true

def mixed : Bool := d.events.any fun e => decide (e.id ≠ cfg.exitId) &&
  e.atomic && e.sourceSupport && e.targetSupport && decide (e.fromStage ∈ d.realized) &&
  decide (e.toStage ∈ d.realized)
def active : Bool := d.receiver.sourcePresent && d.receiver.targetFunded && d.receiver.funded &&
  (!d.receiver.mixedRequired || mixed cfg d)
def receiverDisplay (id : D) : List (Nat × Nat) :=
  if mixed cfg d && active cfg d then display cfg d id else []

def Operational : Prop := mixed cfg d = true ∧ active cfg d = true ∧
  receiverDisplay cfg d cfg.split.1 ≠ receiverDisplay cfg d cfg.split.2 ∧
  (∀ s ∈ cfg.states, ∀ t ∈ cfg.states, weight cfg d s t = d.publishedP s t)

def Rule : Prop := Local cfg d ∧ Histories cfg d ∧ Strict cfg d ∧ Operational cfg d

variable [DecidableEq O]
def DomainCheck : Prop :=
  cfg.states.Nodup ∧ (∀ s, s ∈ cfg.states) ∧ cfg.actions.Nodup ∧ (∀ a, a ∈ cfg.actions) ∧
  cfg.outcomes.Nodup ∧ (∀ o, o ∈ cfg.outcomes) ∧
  cfg.histories.Nodup ∧ (∀ h, h ∈ cfg.histories) ∧
  cfg.lefts.Nodup ∧ (∀ l, l ∈ cfg.lefts) ∧ cfg.rights.Nodup ∧ (∀ r, r ∈ cfg.rights) ∧
  cfg.assemblages.Nodup ∧ (∀ id, id ∈ cfg.assemblages)
def RowsValid : Prop := (cfg.states.all fun s => cfg.actions.all fun a =>
  let row := d.rows s a
  row.all (fun e => decide (e.2 > 0 ∧ e.1 ∈ cfg.outcomes)) &&
    (row.foldl (fun n e => n + e.2) 0 == 0 || row.foldl (fun n e => n + e.2) 0 == cfg.rowScale)) = true

def Gate : Prop := DomainCheck cfg ∧ 0 < cfg.couplingSize ∧ RowsValid cfg d ∧
  d.publishedP = cfg.canonicalP ∧ (cfg.histories.map d.histories).Nodup

def SurrogateAccept : Prop := Gate cfg d ∧ Rule cfg d

omit [DecidableEq S] [DecidableEq Observable] [DecidableEq Stage] [DecidableEq Id] in
theorem zero_coupling_size_rejected (h : cfg.couplingSize = 0) : ¬ Gate cfg d := by
  intro hg
  have hp := hg.2.1
  simp [h] at hp

omit [DecidableEq S] [DecidableEq Observable] [DecidableEq Stage] [DecidableEq Id] in
theorem wrong_published_rows_rejected (h : d.publishedP ≠ cfg.canonicalP) : ¬ Gate cfg d :=
  fun hg => h hg.2.2.2.1

omit [DecidableEq S] [DecidableEq Observable] [DecidableEq Stage] [DecidableEq Id] in
theorem duplicate_path_rejected (h : ¬ (cfg.histories.map d.histories).Nodup) : ¬ Gate cfg d :=
  fun hg => h hg.2.2.2.2

theorem no_mixed_rejected (h : mixed cfg d ≠ true) : ¬ SurrogateAccept cfg d := fun ha => h ha.2.2.2.2.1

theorem inactive_rejected (h : active cfg d ≠ true) : ¬ SurrogateAccept cfg d := fun ha => h ha.2.2.2.2.2.1

theorem equal_displays_rejected (h : receiverDisplay cfg d cfg.split.1 = receiverDisplay cfg d cfg.split.2) :
    ¬ SurrogateAccept cfg d := fun ha => ha.2.2.2.2.2.2.1 h

theorem no_observable_rejected (h : cfg.jointObservable ∉ d.joint.observables) :
    ¬ SurrogateAccept cfg d := by
  apply equal_displays_rejected cfg d
  simp [receiverDisplay,display,h]

theorem operational_readout (h : SurrogateAccept cfg d) :
    mixed cfg d = true ∧ active cfg d = true ∧ display cfg d cfg.split.1 ≠ display cfg d cfg.split.2 := by
  rcases h.2.2.2.2 with ⟨hm,ha,hd,_⟩
  exact ⟨hm,ha,by simpa only [receiverDisplay,hm,ha,Bool.and_self,ite_true] using hd⟩
end Rules

/-- Transport on a shared comparison-index interface and potentially different
carrier types. Both branch records and the computed joint distributions travel. -/
def Transport {S T AS AT OS OT D H L R Assembly Observable Stage Id : Type}
    [DecidableEq S] [DecidableEq T]
    (sc : Schema S AS OS D H L R Assembly Observable Stage Id)
    (tc : Schema T AT OT D H L R Assembly Observable Stage Id)
    (s : Raw S AS OS D H L R Assembly Observable Stage Id)
    (t : Raw T AT OT D H L R Assembly Observable Stage Id) (stateMap : S → T) : Prop :=
  s.joint.observables = t.joint.observables ∧
  ∀ id ∈ sc.assemblages,
    ((branchwise sc s id).1.map (List.map stateMap),
      (branchwise sc s id).2.map (List.map stateMap)) = branchwise tc t id ∧
    s.joint.coupling id = t.joint.coupling id ∧ distribution sc s id = distribution tc t id

structure Bindings (Cell : Type) (Value : Cell → Type) (S A O D H L R Assembly Observable Stage Id : Type) where
  joint : CellView Cell Value (Tables D H L R Assembly Observable)
  rows : CellView Cell Value (S → A → List (O × Nat))
  policy : CellView Cell Value (S → A)
  histories : CellView Cell Value (H → List S)
  publishedP : CellView Cell Value (S → S → Nat)
  events : CellView Cell Value (List (Event Stage Id))
  realized : CellView Cell Value (List Stage)
  receiver : CellView Cell Value Receiver

section Decoder
variable {Cell S A O D H L R Assembly Observable Stage Id : Type} {Value : Cell → Type}
def Bindings.scope (v : Bindings Cell Value S A O D H L R Assembly Observable Stage Id) : List Cell :=
  [v.joint.cell,v.rows.cell,v.policy.cell,v.histories.cell,v.publishedP.cell,v.events.cell,v.realized.cell,v.receiver.cell]
def decoded (v : Bindings Cell Value S A O D H L R Assembly Observable Stage Id)
    (a : Assignment Cell Value) : Option (Raw S A O D H L R Assembly Observable Stage Id) := do
  let joint ← v.joint.read a
  let rows ← v.rows.read a
  let policy ← v.policy.read a
  let histories ← v.histories.read a
  let publishedP ← v.publishedP.read a
  let events ← v.events.read a
  let realized ← v.realized.read a
  let receiver ← v.receiver.read a
  pure ⟨joint,rows,policy,histories,publishedP,events,realized,receiver⟩

theorem decoded_locality (v : Bindings Cell Value S A O D H L R Assembly Observable Stage Id)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : decoded v a = decoded v b := by
  have hj := view_locality v.joint (h _ (by simp [Bindings.scope]))
  have hr := view_locality v.rows (h _ (by simp [Bindings.scope]))
  have hp := view_locality v.policy (h _ (by simp [Bindings.scope]))
  have hh := view_locality v.histories (h _ (by simp [Bindings.scope]))
  have hP := view_locality v.publishedP (h _ (by simp [Bindings.scope]))
  have he := view_locality v.events (h _ (by simp [Bindings.scope]))
  have hre := view_locality v.realized (h _ (by simp [Bindings.scope]))
  have hrc := view_locality v.receiver (h _ (by simp [Bindings.scope]))
  simp only [decoded,hj,hr,hp,hh,hP,he,hre,hrc]

theorem missing_consumed (v : Bindings Cell Value S A O D H L R Assembly Observable Stage Id)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) : decoded v a = none := by
  simp only [Bindings.scope,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with h | h | h | h | h | h | h | h <;> subst k <;> simp [decoded,CellView.read,hm]

variable [DecidableEq S] [DecidableEq Observable] [DecidableEq Stage] [DecidableEq Id] [DecidableEq O]
def AssignedGate (cfg : Schema S A O D H L R Assembly Observable Stage Id)
    (v : Bindings Cell Value S A O D H L R Assembly Observable Stage Id) (a : Assignment Cell Value) : Prop :=
  ∃ d, decoded v a = some d ∧ Gate cfg d

def AssignedAccept (cfg : Schema S A O D H L R Assembly Observable Stage Id)
    (v : Bindings Cell Value S A O D H L R Assembly Observable Stage Id) (a : Assignment Cell Value) : Prop :=
  ∃ d, decoded v a = some d ∧ SurrogateAccept cfg d

omit [DecidableEq S] [DecidableEq Observable] [DecidableEq Stage] [DecidableEq Id] in
theorem gate_locality (cfg : Schema S A O D H L R Assembly Observable Stage Id)
    (v : Bindings Cell Value S A O D H L R Assembly Observable Stage Id)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : AssignedGate cfg v a ↔ AssignedGate cfg v b := by
  unfold AssignedGate; rw [decoded_locality v h]

theorem acceptance_locality (cfg : Schema S A O D H L R Assembly Observable Stage Id)
    (v : Bindings Cell Value S A O D H L R Assembly Observable Stage Id)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : AssignedAccept cfg v a ↔ AssignedAccept cfg v b := by
  unfold AssignedAccept; rw [decoded_locality v h]

theorem missing_rejected (cfg : Schema S A O D H L R Assembly Observable Stage Id)
    (v : Bindings Cell Value S A O D H L R Assembly Observable Stage Id)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) :
    ¬ AssignedGate cfg v a ∧ ¬ AssignedAccept cfg v a := by
  have h := missing_consumed v a k hk hm
  simp [AssignedGate,AssignedAccept,h]
end Decoder
end CSTTT.TargetTheory.GenericHandoff.JointRules
