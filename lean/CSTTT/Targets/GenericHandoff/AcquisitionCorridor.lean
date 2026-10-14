import CSTTT.Targets.GenericHandoff.ExecutionFrontier
import CSTTT.Corridor.AtomicChain

/-! G6d-4b: G4 geometry constructed from assigned acquisition events/routes.
The acquisition clock is the event-path clock (G6_lane_spec.md:104–145), not
the recurrent factor clock. Tick/progress/record in this G4 projection count
the declared funded acquisition events; run-level readouts remain separately
law-gated by ExecutionFrontier. No supplied leg, event graph or verdict enters.
Seed instructions read raw predictive/history coordinates. Their binding to
the executed G1c snapshot is an enclosing bridge obligation, not assumed here.
-/
namespace CSTTT.TargetTheory.GenericHandoff.AcquisitionCorridor
open RegisterInterpreter CSTTT.CorridorTheory.AtomicChain

structure Seeds (History : Type) where
  predictive : History → Nat
  history : History → List String

structure Names (Id : Type) where
  event : Id → String
  entry : String

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O Stage Id History RouteId : Type) where
  acquisition : AcquisitionExecution.Raw Cell Value R RV D A O Stage Id History RouteId
  schema : AcquisitionExecution.Schema Stage Id History RouteId
  names : Names Id
  seeds : StaticView Cell Value (Seeds History)

variable {Cell R D A O Stage Id History RouteId : Type}
  {Value : Cell → Type} {RV : R → Type}

structure View (Stage Id History RouteId : Type) where
  routes : RouteId → AcquisitionExecution.Route History Id
  events : Id → AcquisitionExecution.Event Stage
  realized : List Stage
  receiver : AcquisitionExecution.Receiver
  seeds : Seeds History

/-- Eager Option interpretation. A missing view has no fallback. -/
def read (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) : Option (View Stage Id History RouteId) := do
  let routes ← raw.acquisition.routes.read a
  let events ← raw.acquisition.events.read a
  let realized ← raw.acquisition.realized.read a
  let receiver ← raw.acquisition.receiver.read a
  let seeds ← raw.seeds.read a
  pure ⟨routes,events,realized,receiver,seeds⟩

variable [DecidableEq Stage]

def stagePath (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : View Stage Id History RouteId) (rid : RouteId) : List Stage :=
  raw.schema.entryStage :: (v.routes rid).path.map (fun id => (v.events id).toStage)

def owner (cfg : AcquisitionExecution.Schema Stage Id History RouteId) (count i : Nat) : Nat :=
  if i + 1 = count then cfg.target.code else cfg.source.code

/-- Support is expanded from actual incoming raw event flags. Entry support
is the declared source. No mixed-support label is introduced. -/
def support (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : View Stage Id History RouteId) (rid : RouteId) (i : Nat) (s : Stage) : List Nat :=
  if i = 0 then [raw.schema.source.code] else
    let incoming := (v.routes rid).path.filter (fun id => decide ((v.events id).toStage = s))
    (if incoming.any (fun id => (v.events id).sourceSupport) then [raw.schema.source.code] else []) ++
    (if incoming.any (fun id => (v.events id).targetSupport) then [raw.schema.target.code] else [])

def funded (v : View Stage Id History RouteId) : Bool :=
  v.receiver.sourcePresent && v.receiver.targetFunded && v.receiver.funded

def stages (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : View Stage Id History RouteId) (rid : RouteId) : List RawStage :=
  (stagePath raw v rid).mapIdx fun i s =>
    ⟨support raw v rid i s, decide (s ∈ v.realized) && funded v,
      ⟨v.seeds.predictive (v.routes rid).history,
        raw.schema.clock s,raw.schema.clock s,raw.schema.clock s,raw.schema.clock s,
        v.seeds.history (v.routes rid).history ++ ((v.routes rid).path.take i).map raw.names.event,
        if funded v then "funded" else "",owner raw.schema (stagePath raw v rid).length i⟩⟩

def events (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : View Stage Id History RouteId) (rid : RouteId) : List RawEvent :=
  ⟨raw.names.entry,raw.schema.source.code,0⟩ ::
    (v.routes rid).path.flatMap fun id =>
      (if (v.events id).sourceSupport then
        [⟨raw.names.event id ++ "-source",raw.schema.source.code,
          (stagePath raw v rid).idxOf (v.events id).toStage⟩] else []) ++
      (if (v.events id).targetSupport then
        [⟨raw.names.event id ++ "-target",raw.schema.target.code,
          (stagePath raw v rid).idxOf (v.events id).toStage⟩] else [])

def edges (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : View Stage Id History RouteId) (rid : RouteId) : List RawDependency :=
  (events raw v rid).flatMap fun p =>
    ((events raw v rid).filter (fun c => c.stage == p.stage + 1)).map (fun c => ⟨p.id,c.id⟩)

def updates (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : View Stage Id History RouteId) (rid : RouteId) : List ReadoutUpdate :=
  (v.routes rid).path.mapIdx fun i id =>
    let advance := (v.events id).orderAdvance
    ⟨0,advance,advance,advance,advance,[raw.names.event id],
      if funded v then "funded" else "",owner raw.schema (stagePath raw v rid).length (i+1)⟩

/-- The last actual mixed-support path event is the nonredundancy audit. A missing audit
cannot resolve in auditCheck: empty names are explicitly rejected below. -/
def auditName (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : View Stage Id History RouteId) (rid : RouteId) : String :=
  (((v.routes rid).path.filter (fun id => (v.events id).sourceSupport && (v.events id).targetSupport &&
    (v.events id).atomic)).getLast?.map raw.names.event).getD ""
def lastName (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : View Stage Id History RouteId) (rid : RouteId) : String :=
  ((v.routes rid).path.getLast?.map raw.names.event).getD ""

def leg (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : View Stage Id History RouteId) (rid : RouteId) : FiniteAtomicLeg where
  interventionMode := .mixedSupport
  source := raw.schema.source.code
  target := raw.schema.target.code
  stages := stages raw v rid
  events := events raw v rid
  dependencies := edges raw v rid
  updates := updates raw v rid
  base := default
  sourceContribution := default
  targetContribution := default
  sourceAudit := auditName raw v rid ++ "-source"
  targetAudit := auditName raw v rid ++ "-target"
  laterAudit := lastName raw v rid ++ "-target"

def ViewCheck (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (v : View Stage Id History RouteId) : Prop :=
  raw.schema.routes ≠ [] ∧ raw.schema.source ≠ raw.schema.target ∧
    raw.schema.stages.Nodup ∧ raw.names.entry ≠ "" ∧
    (∀ id ∈ raw.schema.eventIds, raw.names.event id ≠ "") ∧
    (∀ i j, i ∈ raw.schema.eventIds → j ∈ raw.schema.eventIds →
      raw.names.event i = raw.names.event j → i = j) ∧
    ∀ rid ∈ raw.schema.routes,
      (v.routes rid).history ∈ raw.schema.histories ∧
      AcquisitionExecution.PathCheck raw.schema v.events v.realized (v.routes rid).path ∧
      AcquisitionExecution.Activated v.receiver v.events v.realized (v.routes rid).path ∧
      auditName raw v rid ≠ "" ∧ lastName raw v rid ≠ "" ∧ AtomicLegPass (leg raw v rid)

def Pass (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) : Prop :=
  AcquisitionExecution.Ready raw.acquisition a ∧
    ∃ v, read raw a = some v ∧ ViewCheck raw v

def legs (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (rid : RouteId) : Option (List FiniteAtomicLeg) :=
  (read raw a).map (fun v => [leg raw v rid])

theorem constructs (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Pass raw a) (rid : RouteId) (hr : rid ∈ raw.schema.routes) :
    ∃ ls, legs raw a rid = some ls ∧ StrictCorridorWitness ls := by
  obtain ⟨_,v,hv,hc⟩ := h
  have hp := (hc.2.2.2.2.2.2 rid hr).2.2.2.2.2
  refine ⟨[leg raw v rid],by simp [legs,hv],strictTemporalCorridorComposition_generic _ ?_⟩
  refine ⟨by simp, hp, ?_⟩
  change some raw.schema.source.code ≠ some raw.schema.target.code
  intro he
  apply hc.2.1
  cases hs : raw.schema.source with
  | mk s =>
    cases ht : raw.schema.target with
    | mk t =>
      have eq : s = t := by simpa [hs,ht] using Option.some.inj he
      simp [eq]

/-- Multiple independently interpreted acquisition legs compose by the G4
theorem. The boundary check is recomputed on the constructed lists. -/
theorem compose (left right : List FiniteAtomicLeg)
    (hl : StrictCorridorWitness left) (hr : StrictCorridorWitness right)
    (join : boundaryCheck left right = true)
    (distinct : ((left ++ right).head?.map (·.source)) ≠ ((left ++ right).getLast?.map (·.target))) :
    StrictCorridorWitness (left ++ right) := append_corridor left right hl.pass hr.pass join distinct

theorem missing_atomic (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (hm : raw.acquisition.events.read a = none) : ¬ Pass raw a := by
  rintro ⟨_,v,hv,_⟩
  simp [read,hm] at hv

theorem missing_seed (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.seeds.dependencies) (hm : a k = none) :
    ¬ Pass raw a := by
  rintro ⟨_,v,hv,_⟩
  simp [read,raw.seeds.missing a k hk hm] at hv

theorem missing_acquisition_dependency (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.acquisition.dependencies) (hm : a k = none) :
    ¬ Pass raw a := fun h => AcquisitionExecution.missing_dependency_rejected _ _ k hk hm h.1

theorem inactive_receiver (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (v : View Stage Id History RouteId) (hv : read raw a = some v)
    (rid : RouteId) (hr : rid ∈ raw.schema.routes)
    (f : AcquisitionExecution.ActivationField)
    (bad : AcquisitionExecution.activationField v.receiver f = false) : ¬ Pass raw a := by
  rintro ⟨_,other,ho,hc⟩
  have he := Option.some.inj (ho.symm.trans hv)
  subst other
  have hs := AcquisitionExecution.activated_fields v.receiver v.events v.realized _
    (hc.2.2.2.2.2.2 rid hr).2.2.1 f
  rw [bad] at hs
  contradiction

theorem unrealized_path (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (v : View Stage Id History RouteId) (hv : read raw a = some v)
    (rid : RouteId) (hr : rid ∈ raw.schema.routes) (id : Id) (hid : id ∈ (v.routes rid).path)
    (bad : (v.events id).toStage ∉ v.realized) : ¬ Pass raw a := by
  rintro ⟨_,other,ho,hc⟩
  have he := Option.some.inj (ho.symm.trans hv)
  subst other
  obtain ⟨_,_,_,_,hall,_⟩ := (hc.2.2.2.2.2.2 rid hr).2.1
  exact bad (hall id hid).2.1

theorem broken_leg (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (v : View Stage Id History RouteId) (hv : read raw a = some v)
    (rid : RouteId) (hr : rid ∈ raw.schema.routes) (bad : ¬ AtomicLegPass (leg raw v rid)) :
    ¬ Pass raw a := by
  rintro ⟨_,other,ho,hc⟩
  have he := Option.some.inj (ho.symm.trans hv)
  subst other
  exact bad (hc.2.2.2.2.2.2 rid hr).2.2.2.2.2

/-- Named constructed-corridor readout. Failure guards below deny this
existential directly; failure of a sufficient Pass alone is not used. -/
def Readout (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (rid : RouteId) : Prop :=
  ∃ ls, legs raw a rid = some ls ∧ StrictCorridorWitness ls

theorem no_readout_missing_atomic (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (rid : RouteId) (hm : raw.acquisition.events.read a = none) :
    ¬ Readout raw a rid := by
  rintro ⟨ls,he,_⟩
  simp [legs,read,hm] at he

theorem no_readout_broken_leg (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (v : View Stage Id History RouteId) (hv : read raw a = some v)
    (rid : RouteId) (bad : ¬ AtomicLegPass (leg raw v rid)) : ¬ Readout raw a rid := by
  rintro ⟨ls,he,hw⟩
  have hs : ls = [leg raw v rid] := by simpa [legs,hv] using he.symm
  subst ls
  exact bad (chain_each_pass _ hw.pass.2.1 _ (by simp))

/-- A chain request contains only raw acquisition components and route
selectors. Its leg list is interpreted eagerly from one shared assignment. -/
abbrev Request := Raw Cell Value R RV D A O Stage Id History RouteId × RouteId

def chain (a : Assignment Cell Value) : List (Request (Cell := Cell) (Value := Value)
    (R := R) (RV := RV) (D := D) (A := A) (O := O) (Stage := Stage) (Id := Id)
    (History := History) (RouteId := RouteId)) → Option (List FiniteAtomicLeg)
  | [] => some []
  | (raw,rid)::rest => do
    let here ← legs raw a rid
    let tail ← chain a rest
    pure (here ++ tail)

def ChainPass (a : Assignment Cell Value)
    (requests : List (Request (Cell := Cell) (Value := Value) (R := R) (RV := RV)
      (D := D) (A := A) (O := O) (Stage := Stage) (Id := Id) (History := History) (RouteId := RouteId))) : Prop :=
  requests ≠ [] ∧ (∀ q ∈ requests, Pass q.1 a ∧ q.2 ∈ q.1.schema.routes) ∧
    ∃ ls, chain a requests = some ls ∧ CorridorPass ls

theorem constructs_chain (a : Assignment Cell Value)
    (requests : List (Request (Cell := Cell) (Value := Value) (R := R) (RV := RV)
      (D := D) (A := A) (O := O) (Stage := Stage) (Id := Id) (History := History) (RouteId := RouteId)))
    (hc : ChainPass a requests) :
    ∃ ls, chain a requests = some ls ∧ StrictCorridorWitness ls := by
  obtain ⟨_,_,ls,he,hp⟩ := hc
  exact ⟨ls,he,strictTemporalCorridorComposition_generic ls hp⟩

theorem chain_single (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (rid : RouteId) : chain a [(raw,rid)] = legs raw a rid := by
  simp only [chain]
  cases legs raw a rid <;> simp

theorem single_chain_pass (raw : Raw Cell Value R RV D A O Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Pass raw a) (rid : RouteId) (hr : rid ∈ raw.schema.routes) :
    ChainPass a [(raw,rid)] := by
  obtain ⟨ls,he,hw⟩ := constructs raw a h rid hr
  exact ⟨by simp,by simpa using And.intro h hr,ls,by simpa only [chain_single] using he,hw.pass⟩

theorem adjacent_rejected (a : Assignment Cell Value)
    (first second : Request (Cell := Cell) (Value := Value) (R := R) (RV := RV)
      (D := D) (A := A) (O := O) (Stage := Stage) (Id := Id) (History := History) (RouteId := RouteId))
    (l r : FiniteAtomicLeg) (hl : legs first.1 a first.2 = some [l])
    (hr : legs second.1 a second.2 = some [r]) (bad : AdjacentFrontierCheck l r = false) :
    ¬ ChainPass a [first,second] := by
  rintro ⟨_,_,ls,he,hp⟩
  have hs : ls = [l,r] := by simpa [chain,hl,hr] using he.symm
  subst ls
  have hc := hp.2.1
  simp [chainCheck,bad] at hc

end CSTTT.TargetTheory.GenericHandoff.AcquisitionCorridor
