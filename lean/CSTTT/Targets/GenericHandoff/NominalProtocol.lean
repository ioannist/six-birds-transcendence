import CSTTT.Targets.GenericHandoff.RawHandoff

/-! A raw nominal protocol with arbitrary finite alphabets and numeric parameters.
Rows, pasts, events, ticks, resources, ledger and writers are decoded together
from primitive instructions. Missing consumed cells reject. This protocol is a
separate semantic condition; failure alone does not refute the bare game. -/
namespace CSTTT.TargetTheory.GenericHandoff.NominalProtocol

structure Specification (S A O H Route Stage Id Owner Resource : Type) where
  sourceDestination : O → Option S
  viability : OperationalViability.Schema S A O Owner
  outcomes : List O
  routes : List Route
  stages : List Stage
  entry : Stage
  exit : Stage
  exitEvent : Id
  stageAdvance : Nat
  tickAdvance : Nat
  required : List Resource

structure Data (S A O H Route Stage Id Owner : Type) where
  sourceRows : S → A → List (O × Nat)
  rows : S → A → List (O × Nat)
  sourcePolicy : S → A
  policy : S → A
  ticks : S → A → Nat
  resource : OperationalViability.Resource Owner
  ledger : OperationalViability.Ledger
  histories : H → List S
  events : List (AcquisitionEndpoint.SupportedEvent Stage Id)
  realized : List Stage
  receiver : AcquisitionExecution.Receiver
  routeTable : List (TemporalFactorRules.Route Route H Id)
  writers : Route → Bool

structure Metadata (Resource : Type) where
  removedRoles : List ResourceRuntime.Role
  retained : List Resource
  sourcePresent : Bool

variable {S A O H Route Stage Id Owner Resource : Type}
  [DecidableEq S] [DecidableEq O] [DecidableEq Route] [DecidableEq Stage]
  [DecidableEq Id] [DecidableEq Owner] [DecidableEq Resource]

def tuple (d : Data S A O H Route Stage Id Owner) (rid : Route) : Option (List S × List Id) :=
  (d.routeTable.find? (fun r => decide (r.id = rid))).map (fun r => (d.histories r.history,r.eventPath))

def weight (destination : O → Option S) (rows : S → A → List (O × Nat))
    (policy : S → A) (s t : S) : Nat :=
  ((rows s (policy s)).map (fun e => if destination e.1 = some t then e.2 else 0)).sum

def supported (destination : O → Option S) (rows : S → A → List (O × Nat))
    (policy : S → A) (history : List S) : Bool :=
  !history.isEmpty && (history.zip (history.drop 1)).all (fun e => decide (weight destination rows policy e.1 e.2 > 0))

def event (d : Data S A O H Route Stage Id Owner) (id : Id) :=
  d.events.find? (fun e => decide (e.id = id))

def strict (cfg : Specification S A O H Route Stage Id Owner Resource)
    (d : Data S A O H Route Stage Id Owner) (e : AcquisitionEndpoint.SupportedEvent Stage Id) : Bool :=
  e.atomic && e.strictStep && decide (e.fromStage ∈ d.realized) && decide (e.toStage ∈ d.realized) &&
    decide (cfg.stages.idxOf e.toStage = cfg.stages.idxOf e.fromStage + cfg.stageAdvance)

def mixed (cfg : Specification S A O H Route Stage Id Owner Resource)
    (d : Data S A O H Route Stage Id Owner) : Bool :=
  d.events.any (fun e => decide (e.id ≠ cfg.exitEvent) && e.atomic && e.sourceSupport && e.targetSupport &&
    decide (e.fromStage ∈ d.realized) && decide (e.toStage ∈ d.realized))

def active (cfg : Specification S A O H Route Stage Id Owner Resource)
    (d : Data S A O H Route Stage Id Owner) : Bool :=
  d.receiver.sourcePresent && d.receiver.targetFunded && d.receiver.funded &&
    (!d.receiver.mixedRequired || mixed cfg d)

def path (cfg : Specification S A O H Route Stage Id Owner Resource)
    (d : Data S A O H Route Stage Id Owner) (history : List S) (ids : List Id) : Bool :=
  supported cfg.viability.destination d.rows d.policy history && !ids.isEmpty &&
    ids.all (fun id => (event d id).any (strict cfg d)) &&
    (ids.zip (ids.drop 1)).all (fun pair => match event d pair.1,event d pair.2 with
      | some e,some f => decide (e.toStage = f.fromStage)
      | _,_ => false)

def operational (d : Data S A O H Route Stage Id Owner) : OperationalViability.Raw S A O Owner :=
  ⟨d.rows,d.policy,d.resource,d.ledger⟩

def phase2 (cfg : Specification S A O H Route Stage Id Owner Resource)
    (d : Data S A O H Route Stage Id Owner) (rid : Route) : Bool :=
  match tuple d rid with
  | none => false
  | some (history,ids) => match history.getLast? with
    | none => false
    | some terminal => match ids.head? with
      | none => false
      | some first => match ids.getLast? with
        | none => false
        | some last => match event d first with
          | none => false
          | some start => match event d last with
            | none => false
            | some finish =>
              let row := d.rows terminal (d.policy terminal)
              active cfg d && path cfg d history ids && supported cfg.sourceDestination d.sourceRows d.sourcePolicy history &&
                decide (start.fromStage = cfg.entry ∧ finish.toStage = cfg.exit) &&
                finish.targetSupport && !finish.sourceSupport &&
                OperationalViability.available cfg.viability (operational d) &&
                d.writers rid && !row.isEmpty && decide ((row.map Prod.snd).sum = cfg.viability.scale) &&
                row.all (fun e => decide (e.2 > 0 ∧ e.1 ∈ cfg.outcomes))

def withdrawn (cfg : Specification S A O H Route Stage Id Owner Resource) (withdrawalData : Metadata Resource)
    (d : Data S A O H Route Stage Id Owner) : OperationalViability.Raw S A O Owner :=
  {operational d with resource := {d.resource with rechargeAvailable :=
    d.resource.rechargeAvailable && cfg.required.all (fun r => decide (r ∈ withdrawalData.retained))}}

def check (cfg : Specification S A O H Route Stage Id Owner Resource) (withdrawalData : Metadata Resource)
    (d : Data S A O H Route Stage Id Owner) : Prop :=
  (∀ role ∈ ResourceRuntime.roles, role ∈ withdrawalData.removedRoles) ∧
  (∀ role ∈ withdrawalData.removedRoles, role ∈ ResourceRuntime.roles) ∧ withdrawalData.sourcePresent = false ∧
  OperationalViability.available cfg.viability (withdrawn cfg withdrawalData d) = true ∧
  OperationalViability.LedgerCheck cfg.viability (withdrawn cfg withdrawalData d) ∧
  (∀ s ∈ cfg.viability.states, ∀ a ∈ cfg.viability.actions,
    (d.rows s a).isEmpty = false → d.ticks s a = cfg.tickAdvance) ∧
  cfg.routes ≠ [] ∧ (∀ rid ∈ cfg.routes, d.writers rid = true) ∧ d.routeTable ≠ [] ∧
  OperationalViability.PUnchanged cfg.viability (withdrawn cfg withdrawalData d) ∧
  ∀ rid ∈ cfg.routes, phase2 cfg d rid = true

end CSTTT.TargetTheory.GenericHandoff.NominalProtocol

namespace CSTTT.TargetTheory.GenericHandoff.NominalProtocol
open RegisterInterpreter RegisterInitialization

structure Views (Cell : Type) (Value : Cell → Type) (S A O H Route Stage Id Owner : Type) where
  sourceRows : CellView Cell Value (S → A → List (O × Nat))
  rows : CellView Cell Value (S → A → List (O × Nat))
  sourcePolicy : CellView Cell Value (S → A)
  policy : CellView Cell Value (S → A)
  ticks : CellView Cell Value (S → A → Nat)
  resource : CellView Cell Value (OperationalViability.Resource Owner)
  ledger : CellView Cell Value OperationalViability.Ledger
  histories : CellView Cell Value (H → List S)
  events : CellView Cell Value (List (AcquisitionEndpoint.SupportedEvent Stage Id))
  realized : CellView Cell Value (List Stage)
  receiver : CellView Cell Value AcquisitionExecution.Receiver
  routeTable : CellView Cell Value (List (TemporalFactorRules.Route Route H Id))
  writers : CellView Cell Value (Route → Bool)

variable {Cell S A O H Route Stage Id Owner Resource : Type} {Value : Cell → Type}

def reader (v : Views Cell Value S A O H Route Stage Id Owner) : StaticView Cell Value (Data S A O H Route Stage Id Owner) :=
  ⟨.map (fun x => ⟨x.1.1.1,x.1.1.2,x.1.2.1,x.1.2.2,
    x.2.1.1.1,x.2.1.1.2,x.2.1.2.1,x.2.1.2.2,
    x.2.2.1.1,x.2.2.1.2,x.2.2.2.1,x.2.2.2.2.1,x.2.2.2.2.2⟩)
    (.pair (.pair (.pair (StaticView.ofCell v.sourceRows).instruction (StaticView.ofCell v.rows).instruction)
        (.pair (StaticView.ofCell v.sourcePolicy).instruction (StaticView.ofCell v.policy).instruction))
      (.pair (.pair (.pair (StaticView.ofCell v.ticks).instruction (StaticView.ofCell v.resource).instruction)
          (.pair (StaticView.ofCell v.ledger).instruction (StaticView.ofCell v.histories).instruction))
        (.pair (.pair (StaticView.ofCell v.events).instruction (StaticView.ofCell v.realized).instruction)
          (.pair (StaticView.ofCell v.receiver).instruction
            (.pair (StaticView.ofCell v.routeTable).instruction (StaticView.ofCell v.writers).instruction)))))⟩

def views {SR TR D P Q HF : Type} {SRV : SR → Type} {TRV : TR → Type}
    (frames : FramePresentation.Raw Cell Value SR TR SRV TRV S A O HF H Route Stage Id Owner D P Q) :
    Views Cell Value S A O H Route Stage Id Owner :=
  ⟨frames.sourceCells.rows,frames.targetCells.rows,frames.sourceCells.policy,frames.targetCells.policy,
    frames.targetCells.ticks,frames.targetCells.resource,frames.targetCells.ledger,frames.targetCells.histories,
    frames.events,frames.targetCells.realized,frames.receiver,frames.targetCells.routes,frames.targetCells.writers⟩

variable [DecidableEq S] [DecidableEq O] [DecidableEq Route] [DecidableEq Stage]
  [DecidableEq Id] [DecidableEq Owner] [DecidableEq Resource]

def Pass (cfg : Specification S A O H Route Stage Id Owner Resource) (wd : Metadata Resource)
    (v : Views Cell Value S A O H Route Stage Id Owner) (a : Assignment Cell Value) : Prop :=
  ∃ d, (reader v).read a = some d ∧ check cfg wd d

theorem missing_no_pass (cfg : Specification S A O H Route Stage Id Owner Resource) (wd : Metadata Resource)
    (v : Views Cell Value S A O H Route Stage Id Owner) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ (reader v).dependencies) (hm : a k = none) : ¬ Pass cfg wd v a := by
  rintro ⟨d,hd,_⟩
  rw [(reader v).missing a k hk hm] at hd
  contradiction

theorem locality (cfg : Specification S A O H Route Stage Id Owner Resource) (wd : Metadata Resource)
    (v : Views Cell Value S A O H Route Stage Id Owner) {a b : Assignment Cell Value}
    (h : Agrees (reader v).dependencies a b) : Pass cfg wd v a ↔ Pass cfg wd v b := by
  unfold Pass
  rw [(reader v).locality h]

theorem source_present_no_pass (cfg : Specification S A O H Route Stage Id Owner Resource)
    (wd : Metadata Resource) (v : Views Cell Value S A O H Route Stage Id Owner)
    (a : Assignment Cell Value) (h : wd.sourcePresent = true) : ¬ Pass cfg wd v a := by
  rintro ⟨_,_,checked⟩
  have absent := checked.2.2.1
  rw [h] at absent
  contradiction

end CSTTT.TargetTheory.GenericHandoff.NominalProtocol
