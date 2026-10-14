import CSTTT.Targets.GenericHandoff.ProfileRules

/-! Polymorphic C4 collision/connector surrogate (M3 spec:20).
Channels are raw instructions interpreted on raw rows/positions/hazards, never
supplied readout functions. Acceptance documents exposure, not full HIDD. -/
namespace CSTTT.TargetTheory.GenericHandoff.ExposureRules
inductive Channel where | position | availability | predictive deriving DecidableEq, Repr

structure Schema (S A O H : Type) where
  base : ProfileRules.ClauseSchema S A O
  connector : H

structure Raw (S A O H : Type) where
  rows : S → A → List (O × Nat)
  positions : S → Nat
  hazards : O → Bool
  channels : List Channel
  policy : S → A
  histories : H → List S
  classes : S → Nat

section Rules
variable {S A O H : Type} (cfg : Schema S A O H) (d : Raw S A O H)

def profile : ProfileRules.Raw S A O :=
  ⟨cfg.base.states,cfg.base.actions,d.rows,d.positions,d.hazards,cfg.base.destination,
    cfg.base.externalBlock,false,cfg.base.blocks,cfg.base.split,cfg.base.trajectory,cfg.base.depth⟩
def predictive := ProfileRules.predictive (profile cfg d)
def channel (c : Channel) (s : S) : (Nat × List A) × Option (Nat × List (List Bool)) :=
  match c with
  | .position => ((d.positions s,[]),none)
  | .availability => ((0,cfg.base.actions.filter fun a => !(d.rows s a).isEmpty),none)
  | .predictive => ((0,[]),some (predictive cfg d s))
def current (s : S) := d.channels.map fun c => channel cfg d c s
def connector := d.histories cfg.connector

variable [DecidableEq S]
def weight (s t : S) : Nat :=
  ((d.rows s (d.policy s)).map fun e => if cfg.base.destination e.1 = some t then e.2 else 0).sum

def Collision : Prop :=
  current cfg d cfg.base.split.1 = current cfg d cfg.base.split.2 ∧
    predictive cfg d cfg.base.split.1 ≠ predictive cfg d cfg.base.split.2

def Connector : Prop :=
  ((connector cfg d).zip ((connector cfg d).drop 1)).all
    (fun edge => decide (weight cfg d edge.1 edge.2 > 0)) = true ∧ Collision cfg d

def Exposed : Prop :=
  ∃ c ∈ d.channels,
    (∃ s t : S, channel cfg d c s ≠ channel cfg d c t) ∧
    (∀ s t : S, predictive cfg d s = predictive cfg d t → channel cfg d c s = channel cfg d c t)

def FullNonExposure : Prop := ¬ Exposed cfg d

variable [DecidableEq O]
def Gate : Prop :=
  ProfileRules.DomainCheck cfg.base ∧
  ProfileRules.RowsValid cfg.base (profile cfg d) ∧
  ProfileRules.Linked cfg.base (profile cfg d) d.classes ∧
  (connector cfg d).head? = some cfg.base.split.1 ∧
  (connector cfg d).getLast? = some cfg.base.split.2 ∧ (connector cfg d).length ≥ 2

def SurrogateAccept : Prop := Gate cfg d ∧ Collision cfg d ∧ Connector cfg d ∧ Exposed cfg d

theorem full_nonexposure_fails (h : SurrogateAccept cfg d) : ¬ FullNonExposure cfg d :=
  fun hn => hn h.2.2.2

theorem constant_predictive_rejected (q : Nat × List (List Bool))
    (h : ∀ s, predictive cfg d s = q) : ¬ SurrogateAccept cfg d := by
  intro ha
  exact ha.2.1.2 ((h _).trans (h _).symm)

theorem empty_channels_rejected (h : d.channels = []) : ¬ SurrogateAccept cfg d := by
  intro ha
  rcases ha.2.2.2 with ⟨c,hc,_⟩
  simp [h] at hc

theorem failed_connector_rejected (h : (connector cfg d).length < 2) : ¬ SurrogateAccept cfg d :=
  fun ha => (Nat.not_le_of_lt h) ha.1.2.2.2.2.2
omit [DecidableEq S] in
theorem changed_classes_rejected (h : d.classes ≠ cfg.base.referenceClasses) : ¬ Gate cfg d :=
  fun hg => h hg.2.2.1.1

omit [DecidableEq S] in
theorem collapsed_classes_rejected (s t : S) (h : predictive cfg d s = predictive cfg d t)
    (hn : cfg.base.referenceClasses s ≠ cfg.base.referenceClasses t) : ¬ Gate cfg d := by
  intro hg
  have he := (hg.2.2.1.2 s t).mp h
  rw [hg.2.2.1.1] at he
  exact hn he

end Rules

structure Bindings (Cell : Type) (Value : Cell → Type) (S A O H : Type) where
  rows : CellView Cell Value (S → A → List (O × Nat))
  positions : CellView Cell Value (S → Nat)
  hazards : CellView Cell Value (O → Bool)
  channels : CellView Cell Value (List Channel)
  policy : CellView Cell Value (S → A)
  histories : CellView Cell Value (H → List S)
  classes : CellView Cell Value (S → Nat)

section Decoder
variable {Cell S A O H : Type} {Value : Cell → Type}
def Bindings.scope (v : Bindings Cell Value S A O H) : List Cell :=
  [v.rows.cell,v.positions.cell,v.hazards.cell,v.channels.cell,v.policy.cell,v.histories.cell,v.classes.cell]

def decoded (v : Bindings Cell Value S A O H) (a : Assignment Cell Value) : Option (Raw S A O H) := do
  let rows ← v.rows.read a
  let positions ← v.positions.read a
  let hazards ← v.hazards.read a
  let channels ← v.channels.read a
  let policy ← v.policy.read a
  let histories ← v.histories.read a
  let classes ← v.classes.read a
  pure ⟨rows,positions,hazards,channels,policy,histories,classes⟩

theorem decoded_locality (v : Bindings Cell Value S A O H) {a b : Assignment Cell Value}
    (h : Agrees v.scope a b) : decoded v a = decoded v b := by
  have hr := view_locality v.rows (h _ (by simp [Bindings.scope]))
  have hp := view_locality v.positions (h _ (by simp [Bindings.scope]))
  have hh := view_locality v.hazards (h _ (by simp [Bindings.scope]))
  have hc := view_locality v.channels (h _ (by simp [Bindings.scope]))
  have hpol := view_locality v.policy (h _ (by simp [Bindings.scope]))
  have hhist := view_locality v.histories (h _ (by simp [Bindings.scope]))
  have hcls := view_locality v.classes (h _ (by simp [Bindings.scope]))
  simp only [decoded,hr,hp,hh,hc,hpol,hhist,hcls]

theorem missing_consumed (v : Bindings Cell Value S A O H) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) : decoded v a = none := by
  simp only [Bindings.scope,List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with h | h | h | h | h | h | h <;> subst k <;> simp [decoded,CellView.read,hm]

variable [DecidableEq S] [DecidableEq O]
def AssignedGate (cfg : Schema S A O H) (v : Bindings Cell Value S A O H)
    (a : Assignment Cell Value) : Prop := ∃ d, decoded v a = some d ∧ Gate cfg d

def AssignedAccept (cfg : Schema S A O H) (v : Bindings Cell Value S A O H)
    (a : Assignment Cell Value) : Prop := ∃ d, decoded v a = some d ∧ SurrogateAccept cfg d

omit [DecidableEq S] in
theorem gate_locality (cfg : Schema S A O H) (v : Bindings Cell Value S A O H)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : AssignedGate cfg v a ↔ AssignedGate cfg v b := by
  unfold AssignedGate; rw [decoded_locality v h]

theorem acceptance_locality (cfg : Schema S A O H) (v : Bindings Cell Value S A O H)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : AssignedAccept cfg v a ↔ AssignedAccept cfg v b := by
  unfold AssignedAccept; rw [decoded_locality v h]

theorem missing_rejected (cfg : Schema S A O H) (v : Bindings Cell Value S A O H)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) :
    ¬ AssignedGate cfg v a ∧ ¬ AssignedAccept cfg v a := by
  have h := missing_consumed v a k hk hm
  simp [AssignedGate,AssignedAccept,h]
end Decoder
end CSTTT.TargetTheory.GenericHandoff.ExposureRules
