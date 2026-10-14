import CSTTT.POS04.C8

/-! POS-04 corridor, from frozen `audit/M3_model_spec.md:31,40-42`.
Every certified event must be realized; mixed support, strict stage advance,
path composition, and intervention loss are recomputed from raw events. -/

namespace CSTTT.POS04

inductive CorridorVariant where
  | positive | detached | gap | brokenStep
  deriving DecidableEq, Repr

def corridorRealized : CorridorVariant → List Stage
  | .gap => realizedStages.filter (· != .mix1)
  | _ => realizedStages

def corridorEvent (v : CorridorVariant) (id : EventId) : Event :=
  let e := eventOf id
  if v = .detached && id = .mix1 then { e with sourceSupport := false }
  else if v = .brokenStep && id = .mix1 then { e with strictStep := false }
  else e

def corridorEvents (v : CorridorVariant) : List Event :=
  eventIds.map (corridorEvent v)

def corridorMixed (e : Event) : Bool :=
  e.sourceSupport && e.targetSupport && e.atomic

def corridorMixedRealized (v : CorridorVariant) (e : Event) : Bool :=
  corridorMixed e && decide (e.fromStage ∈ corridorRealized v) &&
    decide (e.toStage ∈ corridorRealized v)

def corridorMixedCount (v : CorridorVariant) : Nat :=
  ((corridorEvents v).filter (corridorMixedRealized v)).length

def corridorNoGap (v : CorridorVariant) : Bool :=
  corridorRealized v == stages &&
    (corridorEvents v).all (fun e =>
      e.fromStage ∈ corridorRealized v && e.toStage ∈ corridorRealized v)

def corridorStrict (v : CorridorVariant) : Bool :=
  (corridorEvents v).all fun e =>
    e.fromStage ∈ stages && e.toStage ∈ stages && e.atomic &&
      e.strictStep && stages.idxOf e.toStage == stages.idxOf e.fromStage + 1

def corridorRouteComposes (v : CorridorVariant) (id : RouteId) : Bool :=
  let path := (routeOf id).eventPath
  decide ((routeOf id).sourceHistory ∈ bridgeFrontier) &&
    !path.isEmpty && path.all (fun e =>
      e ∈ eventIds &&
      (corridorEvent v e).fromStage ∈ corridorRealized v &&
      (corridorEvent v e).toStage ∈ corridorRealized v) &&
    decide ((path.head?).map (fun e => (corridorEvent v e).fromStage) =
      some Stage.sourceLive) &&
    decide ((path.getLast?).map (fun e => (corridorEvent v e).toStage) =
      some Stage.targetExit) &&
    (path.zip (path.drop 1)).all (fun pair =>
      (corridorEvent v pair.1).toStage ==
        (corridorEvent v pair.2).fromStage)

def corridorPathsCompose (v : CorridorVariant) : Bool :=
  !routeIds.isEmpty && routeIds.all (corridorRouteComposes v) &&
    eventIds.all (fun e => routeIds.any (fun r => e ∈ (routeOf r).eventPath))

def corridorIntervenedEvent (side : SupportIntervention) (e : Event) : Event :=
  match side with
  | .removeSource => { e with sourceSupport := false }
  | .removeTarget => { e with targetSupport := false }

def corridorAfterIntervention (side : SupportIntervention) (e : Event) : Bool :=
  corridorMixed (corridorIntervenedEvent side e)

def corridorNonredundant (v : CorridorVariant) : Bool :=
  supportInterventions == [.removeSource,.removeTarget] &&
    corridorMixedCount v > 0 &&
    supportInterventions.all (fun side =>
      ((corridorEvents v).filter (corridorAfterIntervention side)).isEmpty)

def CorridorPass (v : CorridorVariant) : Prop :=
  corridorMixedCount v ≥ 2 ∧ corridorNoGap v = true ∧
  corridorStrict v = true ∧ corridorPathsCompose v = true ∧
  corridorNonredundant v = true ∧
  (corridorEvent v .exit).toStage = .targetExit ∧
  (corridorEvent v .exit).targetSupport = true ∧
  (corridorEvent v .exit).sourceSupport = false

theorem corridor_two_realized_mixed_legs :
    corridorMixedCount .positive = 2 := by decide

theorem corridor_positive : CorridorPass .positive := by
  unfold CorridorPass
  decide

theorem neg_corridor_detached_one_mixed_leg :
    corridorMixedCount .detached = 1 := by decide

theorem neg_corridor_detached_fails : ¬ CorridorPass .detached := by
  unfold CorridorPass
  decide

theorem neg_corridor_gap_no_gap_false :
    corridorNoGap .gap = false := by decide

theorem neg_corridor_gap_fails : ¬ CorridorPass .gap := by
  unfold CorridorPass
  decide

theorem corridor_broken_strict_step_fails :
    ¬ CorridorPass .brokenStep := by
  unfold CorridorPass
  decide

end CSTTT.POS04
