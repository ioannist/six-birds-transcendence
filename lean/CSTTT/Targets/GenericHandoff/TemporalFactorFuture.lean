import CSTTT.Targets.GenericHandoff.TemporalFactorRules
import CSTTT.Targets.GenericHandoff.FutureLumping

/-! Defined finite-factor temporal run lift. Actual outcomes are never replaced
by predictive representatives. This constructor has a conserved constant
ledger; unrestricted runtime recipes require a separately proved lift to it.
Successor-code alignment below is DERIVED from the raw tick equations, not a
stored flag. Acceptance/locality of the raw rule is separate from runtime
applicability, which this module does not assume automatically. -/
namespace CSTTT.TargetTheory.GenericHandoff.TemporalFactorRules
open CSTTT.TransportTheory

structure Run (O S Id : Type) where
  factor : O
  counter : Nat
  ticks : Nat
  residue : List S × List Id
  funded : Bool
  deriving DecidableEq

variable {S A O H RouteId Stage Id Owner : Type}
  [DecidableEq S] [DecidableEq O] [DecidableEq RouteId] [DecidableEq Stage] [DecidableEq Id]

abbrev Predictive (O : Type) := Sum (Nat × List (List Bool)) O

structure Code (O S Id Owner : Type) where
  predictive : Predictive O
  counter : Nat
  tickPhase : Nat
  residue : List S × List Id
  funded : Bool
  owner : Owner
  deriving DecidableEq

structure Observation (O S Id Owner : Type) where
  predictive : Predictive O
  order : Nat
  tickPhase : Nat
  progress : Nat
  record : Nat
  residue : List S × List Id
  maintenance : Bool
  owner : Owner
  deriving DecidableEq

def budgetAfter (d : Raw S A O H RouteId Stage Id Owner) : Nat :=
  d.ledger.initial - d.ledger.cost + d.ledger.recharge

def enabled (d : Raw S A O H RouteId Stage Id Owner) (x : Run O S Id) : Bool :=
  x.funded && d.resource.rechargeAvailable && decide (d.ledger.initial ≥ d.ledger.cost)

def registerTuple (d : Raw S A O H RouteId Stage Id Owner) (rid : RouteId) : Option (List S × List Id) := do
  let r ← route d rid
  pure (d.histories r.history,r.eventPath)

/-- First raw route match; no route name is fabricated at the readout boundary. -/
def writer (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (residue : List S × List Id) : Bool :=
  (cfg.routes.find? (fun rid => decide (registerTuple d rid = some residue))).any d.writers

def code (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (period : Nat) (x : Run O S Id) : Code O S Id Owner :=
  ⟨prediction cfg d x.factor,x.counter,x.ticks % period,x.residue,x.funded,d.resource.owner⟩

def observe (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (period : Nat) (x : Run O S Id) : Observation O S Id Owner :=
  ⟨prediction cfg d x.factor,x.counter,x.ticks % period,x.counter,
    if x.funded && writer cfg d x.residue then x.counter else 0,x.residue,x.funded,d.resource.owner⟩

def update (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (x : Run O S Id) (a : A) (o : O) : Run O S Id :=
  ⟨o,x.counter+cfg.stageAdvance,x.ticks+delta cfg d x.factor a,
    x.residue,x.funded && decide (budgetAfter d > 0)⟩

omit [DecidableEq S] [DecidableEq RouteId] [DecidableEq Stage] [DecidableEq Id] in
/-- Alignment is a real raw equation checked by FiniteBisim. All unbounded
counter/residue/funding contexts remain quantified in this theorem. -/
theorem successor_code_alignment (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Raw S A O H RouteId Stage Id Owner) (period : Nat) (h : FiniteBisim cfg d)
    (x y : Run O S Id) (hx : x.factor ∈ cfg.base.outcomes) (hy : y.factor ∈ cfg.base.outcomes)
    (hc : code cfg d period x = code cfg d period y) (a : A) (ha : a ∈ cfg.base.actions) (o : O) :
    code cfg d period (update cfg d x a o) = code cfg d period (update cfg d y a o) := by
  have hp := congrArg Code.predictive hc
  have hn := congrArg Code.counter hc
  have ht := congrArg Code.tickPhase hc
  have hr := congrArg Code.residue hc
  have hf := congrArg Code.funded hc
  have hd := (h x.factor hx y.factor hy a ha hp).2
  have hphase : (x.ticks + delta cfg d x.factor a) % period =
      (y.ticks + delta cfg d y.factor a) % period := by
    rw [Nat.add_mod x.ticks,Nat.add_mod y.ticks]
    change x.ticks % period = y.ticks % period at ht
    rw [ht,hd]
  change x.counter = y.counter at hn
  change x.residue = y.residue at hr
  change x.funded = y.funded at hf
  simp only [code,update,hn,hr,hf,hphase]

omit [DecidableEq O] [DecidableEq Stage] in
/-- All eight components are interpreted on the same run. -/
theorem observation_agreement (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Raw S A O H RouteId Stage Id Owner) (period : Nat) (x y : Run O S Id)
    (hc : code cfg d period x = code cfg d period y) :
    observe cfg d period x = observe cfg d period y := by
  have hp := congrArg Code.predictive hc
  have hn := congrArg Code.counter hc
  have ht := congrArg Code.tickPhase hc
  have hr := congrArg Code.residue hc
  have hf := congrArg Code.funded hc
  change prediction cfg d x.factor = prediction cfg d y.factor at hp
  change x.counter = y.counter at hn
  change x.ticks % period = y.ticks % period at ht
  change x.residue = y.residue at hr
  change x.funded = y.funded at hf
  simp only [observe,hp,hn,ht,hr,hf]

end CSTTT.TargetTheory.GenericHandoff.TemporalFactorRules
