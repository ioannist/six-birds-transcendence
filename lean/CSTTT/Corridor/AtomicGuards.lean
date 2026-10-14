import CSTTT.Corridor.AtomicModels

namespace CSTTT.CorridorTheory.AtomicChain.Models

inductive RawField where
  | source | target | support | realization | events | dependencies | updates
  | base | sourceContribution | targetContribution | sourceAudit | targetAudit | laterAudit
  | predictive | order | tick | progress | record | residue | maintenance | owner
  deriving DecidableEq, Repr

def breakFrontier (f : RawField) (s : RawStage) : RawStage :=
  { s with frontier := match f with
    | .predictive => {s.frontier with predictive := 0}
    | .order => {s.frontier with order := min s.frontier.order 1}
    | .tick => {s.frontier with tick := 0}
    | .progress => {s.frontier with progress := min s.frontier.progress 1}
    | .record => {s.frontier with record := 0}
    | .residue => {s.frontier with residue := []}
    | .maintenance => {s.frontier with maintenance := ""}
    | .owner => {s.frontier with owner := 0}
    | _ => s.frontier }

def brokenField (f : RawField) (l : FiniteAtomicLeg) : FiniteAtomicLeg :=
  match f with
  | .source => {l with source := l.target}
  | .target => {l with target := l.source}
  | .support => {l with stages := l.stages.map (fun s => {s with support := []})}
  | .realization => {l with stages := l.stages.map (fun s => {s with realized := false})}
  | .events => {l with events := []}
  | .dependencies => {l with dependencies := []}
  | .updates => {l with updates := []}
  | .base => {l with base := ⟨1,0,0⟩}
  | .sourceContribution => {l with sourceContribution := default}
  | .targetContribution => {l with targetContribution := default}
  | .sourceAudit => {l with sourceAudit := "missing"}
  | .targetAudit => {l with targetAudit := "missing"}
  | .laterAudit => {l with laterAudit := "missing"}
  | _ => {l with stages := l.stages.map (breakFrontier f)}

/-- Per-field gate sensitivity: exactly the selected raw field family changes;
all independently recorded update recipes and other fields remain fixed. -/
theorem every_raw_field_guard (f : RawField) :
    ¬ AtomicLegPass (brokenField f left) := by
  cases f <;> unfold AtomicLegPass <;> decide

theorem every_readout_update_guard (f : RawField)
    (h : f = .predictive ∨ f = .order ∨ f = .tick ∨ f = .progress ∨
      f = .record ∨ f = .residue ∨ f = .maintenance ∨ f = .owner) :
    readoutCheck (brokenField f left) = false := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

inductive DetailField where
  | stageList | stageOrder | eventId | eventOwner | eventStage | dependencyParent | dependencyChild
  | basePredictive | baseTick | baseRecord
  | sourcePredictive | sourceTick | sourceRecord | targetPredictive | targetTick | targetRecord
  deriving DecidableEq, Repr

def brokenDetail (f : DetailField) : FiniteAtomicLeg :=
  match f with
  | .stageList => {left with stages := []}
  | .stageOrder => {left with stages := left.stages.reverse}
  | .eventId => {left with events := left.events.map (fun e => {e with id := "missing"})}
  | .eventOwner => {left with events := left.events.map (fun e => {e with owner := 0})}
  | .eventStage => {left with events := left.events.map (fun e => {e with stage := 0})}
  | .dependencyParent => {left with dependencies := left.dependencies.map (fun d => {d with parent := "missing"})}
  | .dependencyChild => {left with dependencies := left.dependencies.map (fun d => {d with child := "missing"})}
  | .basePredictive => {left with base := {left.base with predictive := 1}}
  | .baseTick => {left with base := {left.base with tick := 1}}
  | .baseRecord => {left with base := {left.base with record := 1}}
  | .sourcePredictive => {left with sourceContribution := {left.sourceContribution with predictive := 0}}
  | .sourceTick => {left with sourceContribution := {left.sourceContribution with tick := 1}}
  | .sourceRecord => {left with sourceContribution := {left.sourceContribution with record := 0}}
  | .targetPredictive => {left with targetContribution := {left.targetContribution with predictive := 0}}
  | .targetTick => {left with targetContribution := {left.targetContribution with tick := 0}}
  | .targetRecord => {left with targetContribution := {left.targetContribution with record := 0}}

theorem every_raw_detail_guard (f : DetailField) : ¬ AtomicLegPass (brokenDetail f) := by
  cases f <;> unfold AtomicLegPass <;> decide

/-- Removal of either contribution is essential in BOTH declared modes. -/
theorem mixed_support_removal_guard (side : Bool) :
    mixedCount {left with interventionMode := .mixedSupport}
      (some (if side then left.source else left.target)) = 0 := by
  cases side <;> decide

inductive UpdateField where
  | predictive | order | tick | progress | record | residue | maintenance | owner
  deriving DecidableEq, Repr

def breakUpdate (f : UpdateField) (u : ReadoutUpdate) : ReadoutUpdate :=
  match f with
  | .predictive => {u with predictiveAdvance := 0}
  | .order => {u with orderAdvance := 0}
  | .tick => {u with tickAdvance := 0}
  | .progress => {u with progressAdvance := 0}
  | .record => {u with recordAdvance := 0}
  | .residue => {u with appendResidue := []}
  | .maintenance => {u with nextMaintenance := ""}
  | .owner => {u with nextOwner := 0}

theorem every_update_recipe_guard (f : UpdateField) :
    readoutCheck {left with updates := left.updates.map (breakUpdate f)} = false := by
  cases f <;> decide

inductive InterfaceField where
  | carrier | predictive | order | tick | progress | record | residue | maintenance | owner
  | support | realization
  deriving DecidableEq, Repr

def breakInterface (f : InterfaceField) : FiniteAtomicLeg :=
  if f = .carrier then {right with source := right.target} else
  {right with stages := right.stages.mapIdx fun i s =>
    if i != 0 then s else
    match f with
    | .predictive => {s with frontier := {s.frontier with predictive := 0}}
    | .order => {s with frontier := {s.frontier with order := 0}}
    | .tick => {s with frontier := {s.frontier with tick := 0}}
    | .progress => {s with frontier := {s.frontier with progress := 0}}
    | .record => {s with frontier := {s.frontier with record := 0}}
    | .residue => {s with frontier := {s.frontier with residue := []}}
    | .maintenance => {s with frontier := {s.frontier with maintenance := ""}}
    | .owner => {s with frontier := {s.frontier with owner := 0}}
    | .support => {s with support := []}
    | .realization => {s with realized := false}
    | .carrier => s}

theorem every_interface_field_guard (f : InterfaceField) :
    AdjacentFrontierCheck left (breakInterface f) = false := by
  cases f <;> decide

def detached : FiniteAtomicLeg :=
  {left with stages := left.stages.map fun s =>
    if s.support.length > 1 then {s with support := [left.source]} else s}

def gap : FiniteAtomicLeg :=
  {left with stages := left.stages.mapIdx fun i s =>
    if i = 1 then {s with realized := false} else s}

/-- Translate ALL right-leg progress ranks by one. Its own strict update
laws remain true, but the shared frontier no longer equals the left exit. -/
def frontierMismatch : FiniteAtomicLeg :=
  {right with stages := right.stages.map fun s =>
    {s with frontier := {s.frontier with progress := s.frontier.progress + 1}}}

theorem detached_has_no_mixed_stage :
    detached.stages.any (fun s => decide
      (detached.source ∈ s.support ∧ detached.target ∈ s.support)) = false := by decide

theorem detached_fails : ¬ AtomicLegPass detached := by unfold AtomicLegPass; decide
theorem gap_fails : ¬ AtomicLegPass gap := by unfold AtomicLegPass; decide

theorem mismatched_leg_still_passes : AtomicLegPass frontierMismatch := by
  unfold AtomicLegPass; decide

theorem frontier_mismatch_fails : AdjacentFrontierCheck left frontierMismatch = false := by decide

theorem frontier_mismatch_no_corridor : ¬ CorridorPass [left,frontierMismatch] := by
  unfold CorridorPass; decide

theorem detached_no_witness : ¬ StrictCorridorWitness [detached,right] := by
  intro h
  have hf : ¬ CorridorPass [detached,right] := by unfold CorridorPass; decide
  exact hf h.pass

theorem gap_no_witness : ¬ StrictCorridorWitness [gap,right] := by
  intro h
  have hf : ¬ CorridorPass [gap,right] := by unfold CorridorPass; decide
  exact hf h.pass

theorem frontier_mismatch_no_witness : ¬ StrictCorridorWitness [left,frontierMismatch] := by
  intro h
  exact frontier_mismatch_no_corridor h.pass

end CSTTT.CorridorTheory.AtomicChain.Models
