import CSTTT.Targets.GenericHandoff.ProfileRules
import CSTTT.Targets.GenericHandoff.OperationalViability

/-! Finite-factor C6 raw rule extraction, at the declared surrogate grade.
Factor/action/outcome/history/route/event/stage/owner domains and numeric
parameters are arbitrary. This is a finite temporal audit constructor, not a
claim that unrestricted run-context recipes have a finite factor. A runtime
binding still requires its proved actual-support/run-readout lift.
No future model, code, acceptance predicate or uniqueness verdict is a field.
-/
namespace CSTTT.TargetTheory.GenericHandoff.TemporalFactorRules

inductive Observable where
  | predictive | order | tick | progress | record | route | maintenance | owner
  deriving DecidableEq

def interface : List Observable :=
  [.predictive,.order,.tick,.progress,.record,.route,.maintenance,.owner]

structure Event (Stage Id : Type) where
  id : Id
  fromStage : Stage
  toStage : Stage
  atomic : Bool
  strictStep : Bool

structure Route (RouteId H Id : Type) where
  id : RouteId
  history : H
  eventPath : List Id

structure Schema (S A O H RouteId Stage Id Owner : Type) where
  base : ProfileRules.ClauseSchema S A O
  owner : Owner
  histories : List H
  routes : List RouteId
  stages : List Stage
  events : List Id
  stageAdvance : Nat
  tickAdvance : Nat
  ledger : OperationalViability.Ledger
  coarsePair : O × O

structure Raw (S A O H RouteId Stage Id Owner : Type) where
  rows : S → A → List (O × Nat)
  positions : S → Nat
  hazards : O → Bool
  policy : S → A
  classes : S → Nat
  publishedP : S → S → Nat
  ticks : S → A → Nat
  resource : OperationalViability.Resource Owner
  ledger : OperationalViability.Ledger
  interface : List Observable
  histories : H → List S
  events : List (Event Stage Id)
  realized : List Stage
  receiverFunded : Bool
  routes : List (Route RouteId H Id)
  writers : RouteId → Bool

variable {S A O H RouteId Stage Id Owner : Type}
  [DecidableEq S] [DecidableEq O] [DecidableEq RouteId] [DecidableEq Stage]
  [DecidableEq Id]

def profile (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) :
    ProfileRules.Raw S A O :=
  ⟨cfg.base.states,cfg.base.actions,d.rows,d.positions,d.hazards,cfg.base.destination,
    cfg.base.externalBlock,false,cfg.base.blocks,cfg.base.split,cfg.base.trajectory,cfg.base.depth⟩

def prediction (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (o : O) : Sum (Nat × List (List Bool)) O :=
  match cfg.base.destination o with
  | some s => .inl (ProfileRules.predictive (profile cfg d) s)
  | none => .inr o

def row (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (o : O) (a : A) : List (O × Nat) :=
  match cfg.base.destination o with | some s => d.rows s a | none => []

def delta (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (o : O) (a : A) : Nat :=
  match cfg.base.destination o with | some s => d.ticks s a | none => 0

def outcomeClasses (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) :=
  (cfg.base.outcomes.map (prediction cfg d)).eraseDups

def mass (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (s : O) (a : A) (c : Sum (Nat × List (List Bool)) O) : Nat :=
  ((row cfg d s a).filter (fun e => decide (prediction cfg d e.1 = c))).foldl (fun n e => n + e.2) 0

/-- Exact finite class masses and raw tick increments; no assumed alignment
flag. A run adapter must derive successor-code alignment from these equations
and the actual updater before invoking class-mass word induction. -/
def FiniteBisim (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) : Prop :=
  ∀ s ∈ cfg.base.outcomes, ∀ t ∈ cfg.base.outcomes, ∀ a ∈ cfg.base.actions,
    prediction cfg d s = prediction cfg d t →
    (∀ c ∈ outcomeClasses cfg d, mass cfg d s a c = mass cfg d t a c) ∧
    delta cfg d s a = delta cfg d t a

def policyWeight (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (s t : S) : Nat :=
  ((d.rows s (d.policy s)).map fun e => if cfg.base.destination e.1 = some t then e.2 else 0).sum

def supported (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (h : H) : Bool :=
  let path := d.histories h
  !path.isEmpty && (path.zip (path.drop 1)).all (fun e => decide (policyWeight cfg d e.1 e.2 > 0))

def event (d : Raw S A O H RouteId Stage Id Owner) (id : Id) := d.events.find? (fun e => decide (e.id = id))
def route (d : Raw S A O H RouteId Stage Id Owner) (id : RouteId) := d.routes.find? (fun r => decide (r.id = id))

def strictEvent (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (e : Event Stage Id) : Bool :=
  e.atomic && e.strictStep && decide (e.fromStage ∈ d.realized) && decide (e.toStage ∈ d.realized) &&
    decide (cfg.stages.idxOf e.toStage = cfg.stages.idxOf e.fromStage + cfg.stageAdvance)

def path (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (id : RouteId) : Bool :=
  match route d id with
  | none => false
  | some r => supported cfg d r.history && !r.eventPath.isEmpty &&
    r.eventPath.all (fun id => (event d id).any (strictEvent cfg d)) &&
    (r.eventPath.zip (r.eventPath.drop 1)).all (fun p =>
      match event d p.1,event d p.2 with
      | some e,some f => decide (e.toStage = f.fromStage)
      | _,_ => false)

def paths (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) : Bool :=
  decide (d.realized = cfg.stages) && !cfg.routes.isEmpty && cfg.routes.all (path cfg d) &&
    cfg.events.all (fun id => d.routes.any (fun r => decide (id ∈ r.eventPath))) &&
    cfg.events.all (fun id => (event d id).any (strictEvent cfg d))

def ticks (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) : Bool :=
  cfg.base.states.all (fun s => cfg.base.actions.all (fun a => (d.rows s a).isEmpty || decide (d.ticks s a = cfg.tickAdvance)))

def Trace (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) : Prop :=
  d.receiverFunded = true ∧ d.resource.rechargeAvailable = true ∧ d.ledger.initial ≥ d.ledger.cost ∧
    ticks cfg d = true ∧ (!cfg.routes.isEmpty && cfg.routes.all d.writers) = true ∧
    paths cfg d = true ∧ d.resource.owner = cfg.owner

def Reference (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) : Prop :=
  ProfileRules.Linked cfg.base (profile cfg d) d.classes ∧
    ∀ s t, policyWeight cfg d s t = d.publishedP s t

def Funding (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) : Prop :=
  d.ledger.initial = cfg.ledger.initial ∧ d.ledger.cost = cfg.ledger.cost ∧
    d.ledger.recharge = cfg.ledger.recharge ∧ d.ledger.initial > 0 ∧
    d.ledger.initial - d.ledger.cost + d.ledger.recharge = d.ledger.initial

def Coarser (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) : Prop :=
  cfg.coarsePair.1 ≠ cfg.coarsePair.2 ∧ prediction cfg d cfg.coarsePair.1 = prediction cfg d cfg.coarsePair.2

def Accept (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) : Prop :=
  ProfileRules.DomainCheck cfg.base ∧ cfg.stageAdvance > 0 ∧ cfg.tickAdvance > 0 ∧
    ProfileRules.RowsValid cfg.base (profile cfg d) ∧ Reference cfg d ∧ Trace cfg d ∧ Funding cfg d ∧ d.interface = interface ∧ FiniteBisim cfg d ∧ Coarser cfg d

theorem zero_funding_rejected (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (bad : d.ledger.initial = 0) : ¬ Accept cfg d := by
  intro h
  have hp := h.2.2.2.2.2.2.1.2.2.2.1
  omega

theorem lost_writer_rejected (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (r : RouteId) (hr : r ∈ cfg.routes) (bad : d.writers r = false) : ¬ Accept cfg d := by
  intro h
  have ht := h.2.2.2.2.2.1.2.2.2.2.1
  have hwriter := List.all_eq_true.mp (Bool.and_eq_true_iff.mp ht).2 r hr
  rw [bad] at hwriter
  contradiction

theorem unrealized_event_rejected (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (id : Id) (hi : id ∈ cfg.events) (e : Event Stage Id) (he : event d id = some e)
    (bad : e.toStage ∉ d.realized) : ¬ Accept cfg d := by
  intro h
  have hp := h.2.2.2.2.2.1.2.2.2.2.2.1
  have hall := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hp).2 id hi
  simp [he,strictEvent,bad] at hall

theorem tick_alignment_rejected (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Raw S A O H RouteId Stage Id Owner) (s t : O) (hs : s ∈ cfg.base.outcomes)
    (ht : t ∈ cfg.base.outcomes) (a : A) (ha : a ∈ cfg.base.actions)
    (hp : prediction cfg d s = prediction cfg d t) (bad : delta cfg d s a ≠ delta cfg d t a) :
    ¬ FiniteBisim cfg d := fun h => bad (h s hs t ht a ha hp).2

theorem class_mass_rejected (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Raw S A O H RouteId Stage Id Owner) (s t : O) (hs : s ∈ cfg.base.outcomes)
    (ht : t ∈ cfg.base.outcomes) (a : A) (ha : a ∈ cfg.base.actions)
    (hp : prediction cfg d s = prediction cfg d t) (c : Sum (Nat × List (List Bool)) O)
    (hc : c ∈ outcomeClasses cfg d) (bad : mass cfg d s a c ≠ mass cfg d t a c) :
    ¬ FiniteBisim cfg d := fun h => bad ((h s hs t ht a ha hp).1 c hc)

end CSTTT.TargetTheory.GenericHandoff.TemporalFactorRules
