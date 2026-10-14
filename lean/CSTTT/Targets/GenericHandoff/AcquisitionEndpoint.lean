import CSTTT.Targets.GenericHandoff.TemporalFactorCells
import CSTTT.Targets.GenericHandoff.AcquisitionExecution

/-! TTH-06 typed acquisition endpoint (G6_lane_spec.md:125–139).
Arbitrary finite coordinate alphabets, tables and instruction decoders. Both
carrier presentations use a common coordinate alphabet, with separate owners.
The enclosing binding must link these coordinates to its separately typed run
frames. Endpoints, classes, activation and phase-2 verdicts are DEFINED, never
supplied. Priority path lookup and all-record activation match frozen semantics.
-/
namespace CSTTT.TargetTheory.GenericHandoff.AcquisitionEndpoint
open RegisterInterpreter TemporalFactorRules
structure SupportedEvent (Stage Id : Type) where
  id : Id
  fromStage : Stage
  toStage : Stage
  atomic : Bool
  strictStep : Bool
  sourceSupport : Bool
  targetSupport : Bool
structure Schema (S A O H RouteId Stage Id Owner : Type) where
  source : TemporalFactorRules.Schema S A O H RouteId Stage Id Owner
  target : TemporalFactorRules.Schema S A O H RouteId Stage Id Owner
  entry : Stage
  exit : Stage
  exitEvent : Id
  fallback : S
  rowScale : Nat
  transfer : S → S
structure Bindings (Cell : Type) (Value : Cell → Type) (S A O H RouteId Stage Id Owner : Type) where
  source : TemporalFactorCells.Bindings Cell Value S A O H RouteId Stage Id Owner
  target : TemporalFactorCells.Bindings Cell Value S A O H RouteId Stage Id Owner
  events : CellView Cell Value (List (SupportedEvent Stage Id))
  receiver : CellView Cell Value AcquisitionExecution.Receiver
structure Data (S A O H RouteId Stage Id Owner : Type) where
  source : TemporalFactorRules.Raw S A O H RouteId Stage Id Owner
  target : TemporalFactorRules.Raw S A O H RouteId Stage Id Owner
  events : List (SupportedEvent Stage Id)
  receiver : AcquisitionExecution.Receiver
variable {Cell S A O H RouteId Stage Id Owner : Type} {Value : Cell → Type}
def Bindings.scope (v : Bindings Cell Value S A O H RouteId Stage Id Owner) : List Cell :=
  v.source.scope ++ v.target.scope ++ [v.events.cell,v.receiver.cell]
def decoded (v : Bindings Cell Value S A O H RouteId Stage Id Owner) (a : Assignment Cell Value) :
    Option (Data S A O H RouteId Stage Id Owner) := do
  let ds ← TemporalFactorCells.decoded v.source a
  let dt ← TemporalFactorCells.decoded v.target a
  let es ← v.events.read a
  let receiver ← v.receiver.read a
  pure ⟨ds,dt,es,receiver⟩
theorem decoder_locality (v : Bindings Cell Value S A O H RouteId Stage Id Owner)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : decoded v a = decoded v b := by
  have hs := TemporalFactorCells.decoder_locality v.source
    (fun k hk => h k (List.mem_append_left _ (List.mem_append_left _ hk)))
  have ht := TemporalFactorCells.decoder_locality v.target
    (fun k hk => h k (List.mem_append_left _ (List.mem_append_right _ hk)))
  have he := view_locality v.events (h _ (List.mem_append_right _ (by simp)))
  have hr := view_locality v.receiver (h _ (List.mem_append_right _ (by simp)))
  simp only [decoded,hs,ht,he,hr]
theorem missing_input (v : Bindings Cell Value S A O H RouteId Stage Id Owner)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) : decoded v a = none := by
  rcases List.mem_append.mp hk with hst | hex
  · rcases List.mem_append.mp hst with hs | ht
    · simp [decoded,TemporalFactorCells.missing_input v.source a k hs hm]
    · simp [decoded,TemporalFactorCells.missing_input v.target a k ht hm]
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at hex
    rcases hex with rfl | rfl <;> simp [decoded,CellView.read,hm]
variable [DecidableEq S] [DecidableEq O] [DecidableEq RouteId] [DecidableEq Stage]
  [DecidableEq Id] [DecidableEq Owner]
def tuple (d : TemporalFactorRules.Raw S A O H RouteId Stage Id Owner) (r : RouteId) :
    Option (List S × List Id) :=
  (TemporalFactorRules.route d r).map (fun v => (d.histories v.history,v.eventPath))
def event (d : Data S A O H RouteId Stage Id Owner) (id : Id) :=
  d.events.find? (fun e => decide (e.id = id))
def strict (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Data S A O H RouteId Stage Id Owner) (e : SupportedEvent Stage Id) : Bool :=
  e.atomic && e.strictStep && decide (e.fromStage ∈ d.target.realized) &&
  decide (e.toStage ∈ d.target.realized) &&
  decide (cfg.target.stages.idxOf e.toStage = cfg.target.stages.idxOf e.fromStage + cfg.target.stageAdvance)
def mixed (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Data S A O H RouteId Stage Id Owner) : Bool :=
  d.events.any fun e => decide (e.id ≠ cfg.exitEvent) && e.atomic && e.sourceSupport &&
    e.targetSupport && decide (e.fromStage ∈ d.target.realized) && decide (e.toStage ∈ d.target.realized)
def active (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Data S A O H RouteId Stage Id Owner) : Bool :=
  d.receiver.sourcePresent && d.receiver.targetFunded && d.receiver.funded &&
    (!d.receiver.mixedRequired || mixed cfg d)
def supported (cfg : TemporalFactorRules.Schema S A O H RouteId Stage Id Owner)
    (d : TemporalFactorRules.Raw S A O H RouteId Stage Id Owner) (hist : List S) : Bool :=
  !hist.isEmpty && (hist.zip (hist.drop 1)).all fun e =>
    decide (TemporalFactorRules.policyWeight cfg d e.1 e.2 > 0)
def path (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Data S A O H RouteId Stage Id Owner) (r : RouteId) : Bool :=
  match tuple d.target r with
  | none => false
  | some (hist,ids) =>
    !hist.isEmpty && supported cfg.target d.target hist && !ids.isEmpty &&
    ids.all (fun id => (event d id).any (strict cfg d)) &&
    (ids.zip (ids.drop 1)).all (fun p =>
      match event d p.1,event d p.2 with
      | some e,some f => decide (e.toStage = f.fromStage)
      | _,_ => false)
def available (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Data S A O H RouteId Stage Id Owner) : Bool :=
  d.target.resource.rechargeAvailable && decide (d.target.ledger.initial ≥ d.target.ledger.cost) &&
  decide (d.target.ledger.initial - d.target.ledger.cost + d.target.ledger.recharge > 0) &&
  decide (d.target.resource.owner = cfg.target.owner)
def phase2 (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Data S A O H RouteId Stage Id Owner) (r : RouteId) : Bool :=
  match tuple d.target r with
  | none => false
  | some (hist,ids) =>
    let s := hist.getLastD cfg.fallback
    let row := d.target.rows s (d.target.policy s)
    active cfg d && path cfg d r && supported cfg.source d.source hist &&
    match ids.head?,ids.getLast? with
    | some first,some last =>
      match event d first,event d last with
      | some start,some finish =>
        decide (start.fromStage = cfg.entry ∧ finish.toStage = cfg.exit) &&
        finish.targetSupport && !finish.sourceSupport && available cfg d && d.target.writers r &&
        !row.isEmpty && decide ((row.map Prod.snd).sum = cfg.rowScale) &&
        row.all (fun e => decide (e.2 > 0 ∧ e.1 ∈ cfg.target.base.outcomes))
      | _,_ => false
    | _,_ => false
def received (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Data S A O H RouteId Stage Id Owner) (h : H) : Option S :=
  if active cfg d then (d.target.histories h).getLast?.map cfg.transfer else none
def targetHistory (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Data S A O H RouteId Stage Id Owner) (h : H) : List S :=
  match received cfg d h with
  | none => []
  | some s => (d.source.histories h).dropLast ++ [s]
def atRoute (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Data S A O H RouteId Stage Id Owner) (r : RouteId) : Bool :=
  match tuple d.source r,tuple d.target r,TemporalFactorRules.route d.source r with
  | some (hist,ids),some targetTuple,some route =>
    match hist.getLast?,ids.getLast? with
    | some s,some eid =>
      match event d eid with
      | none => false
      | some e =>
        decide (targetTuple = (hist,ids)) && active cfg d && phase2 cfg d r &&
        decide (received cfg d route.history = some s) &&
        decide ((targetHistory cfg d route.history).getLast? = some s) &&
        decide (ProfileRules.predictive (TemporalFactorRules.profile cfg.target d.target) s =
          ProfileRules.predictive (TemporalFactorRules.profile cfg.source d.source) s) &&
        decide (e.toStage = cfg.exit) && e.targetSupport && !e.sourceSupport && strict cfg d e &&
        decide (e.toStage ∈ d.target.realized) &&
        decide (d.source.resource.owner = cfg.source.owner) &&
        decide (d.target.resource.owner = cfg.target.owner)
    | _,_ => false
  | _,_,_ => false
def Pass (cfg : Schema S A O H RouteId Stage Id Owner)
    (v : Bindings Cell Value S A O H RouteId Stage Id Owner) (a : Assignment Cell Value) : Prop :=
  ∃ d, decoded v a = some d ∧ cfg.source.routes ≠ [] ∧ cfg.source.routes.all (atRoute cfg d) = true
theorem locality (cfg : Schema S A O H RouteId Stage Id Owner)
    (v : Bindings Cell Value S A O H RouteId Stage Id Owner)
    {a b : Assignment Cell Value} (h : Agrees v.scope a b) : Pass cfg v a ↔ Pass cfg v b := by
  simp only [Pass,decoder_locality v h]
theorem missing_rejected (cfg : Schema S A O H RouteId Stage Id Owner)
    (v : Bindings Cell Value S A O H RouteId Stage Id Owner) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ v.scope) (hm : a k = none) : ¬ Pass cfg v a := by
  simp [Pass,missing_input v a k hk hm]
/-- Reception and raw terminal identity are consequences of the checked
execution rule, not fields in a certificate. -/
theorem receiver_state (cfg : Schema S A O H RouteId Stage Id Owner)
    (v : Bindings Cell Value S A O H RouteId Stage Id Owner) (a : Assignment Cell Value)
    (h : Pass cfg v a) (r : RouteId) (hr : r ∈ cfg.source.routes) :
    ∃ d route s, decoded v a = some d ∧ TemporalFactorRules.route d.source r = some route ∧
      received cfg d route.history = some s ∧
      (targetHistory cfg d route.history).getLast? = some s ∧ phase2 cfg d r = true := by
  obtain ⟨d,hd,_,hall⟩ := h
  have hp := List.all_eq_true.mp hall r hr
  unfold atRoute at hp
  split at hp
  · rename_i hist ids targetTuple route _ _ hroute
    split at hp
    · rename_i state eid _ _
      split at hp
      · contradiction
      · simp only [Bool.and_eq_true,decide_eq_true_eq] at hp
        exact ⟨d,route,state,hd,hroute,hp.1.1.1.1.1.1.1.1.1.2,hp.1.1.1.1.1.1.1.1.2,hp.1.1.1.1.1.1.1.1.1.1.2⟩
    · contradiction
  · contradiction

/-- A raw endpoint component, with its coordinate/domain types explicit.
The schemas and decoders are raw data; no endpoint proof is stored. -/
structure Interface (Cell : Type) (Value : Cell → Type) where
  State : Type
  Action : Type
  Outcome : Type
  History : Type
  Route : Type
  Stage : Type
  Id : Type
  Owner : Type
  stateEq : DecidableEq State
  outcomeEq : DecidableEq Outcome
  routeEq : DecidableEq Route
  stageEq : DecidableEq Stage
  idEq : DecidableEq Id
  ownerEq : DecidableEq Owner
  schema : Schema State Action Outcome History Route Stage Id Owner
  bindings : Bindings Cell Value State Action Outcome History Route Stage Id Owner

def Readout (raw : Interface Cell Value) (a : Assignment Cell Value) : Prop :=
  letI := raw.stateEq
  letI := raw.outcomeEq
  letI := raw.routeEq
  letI := raw.stageEq
  letI := raw.idEq
  letI := raw.ownerEq
  Pass raw.schema raw.bindings a

omit [DecidableEq S] [DecidableEq O] [DecidableEq RouteId] [DecidableEq Stage]
  [DecidableEq Id] [DecidableEq Owner] in
theorem missing_no_readout (raw : Interface Cell Value) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ raw.bindings.scope) (hm : a k = none) : ¬ Readout raw a := by
  letI := raw.stateEq
  letI := raw.outcomeEq
  letI := raw.routeEq
  letI := raw.stageEq
  letI := raw.idEq
  letI := raw.ownerEq
  exact missing_rejected _ _ _ _ hk hm

end CSTTT.TargetTheory.GenericHandoff.AcquisitionEndpoint
