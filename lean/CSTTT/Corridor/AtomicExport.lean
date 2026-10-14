import CSTTT.Corridor.AtomicGuards
import Lean

/-! Evaluated views of the operative COR JSON data, never independent tables. -/
namespace CSTTT.CorridorTheory.AtomicChain.Models
open Lean
private def obj := Json.mkObj
private def arr (xs : List Json) := Json.arr xs.toArray

def exportFrontier (f : Frontier) : Json := obj [
  ("predictive_rank",toJson f.predictive),("order_rank",toJson f.order),
  ("tick_index",toJson f.tick),("progress_rank",toJson f.progress),
  ("record_value",toJson f.record),("route_residue",toJson f.residue),
  ("maintenance_state",toJson f.maintenance),("maintenance_owner",toJson f.owner)]

def exportStages (xs : List RawStage) : Json := arr (xs.mapIdx fun i s => obj [
  ("stage",toJson i),("active_support",toJson s.support),
  ("temporal_realized",toJson s.realized),("signature",exportFrontier s.frontier)])

def exportEvents (xs : List RawEvent) : Json := arr (xs.map fun e => obj [
  ("event_id",toJson e.id),("owner",toJson e.owner),("stage",toJson e.stage)])

def exportDependencies (xs : List RawDependency) : Json :=
  arr (xs.map fun d => toJson [d.parent,d.child])

def exportProjection (p : Projection) : Json := toJson [p.predictive,p.tick,p.record]

def exportLeg (l : FiniteAtomicLeg) : Json := obj [
  ("intervention_mode",toJson (match l.interventionMode with | .additive => "additive" | .mixedSupport => "mixed-support")),
  ("source",toJson l.source),("target",toJson l.target),
  ("start_stage",toJson 0),("end_stage",toJson (l.stages.length-1)),
  ("base_projection",exportProjection l.base),
  ("source_contribution",exportProjection l.sourceContribution),
  ("target_contribution",exportProjection l.targetContribution),
  ("full_projection",exportProjection (fullProjection l)),
  ("source_removed_projection",exportProjection (addProjection l.base l.targetContribution)),
  ("target_removed_projection",exportProjection (addProjection l.base l.sourceContribution)),
  ("source_mixed_event",toJson l.sourceAudit),("target_mixed_event",toJson l.targetAudit),
  ("later_event",toJson l.laterAudit),
  ("updates",arr (l.updates.map fun u => obj [
    ("predictiveAdvance",toJson u.predictiveAdvance),("orderAdvance",toJson u.orderAdvance),
    ("tickAdvance",toJson u.tickAdvance),("progressAdvance",toJson u.progressAdvance),
    ("recordAdvance",toJson u.recordAdvance),("appendResidue",toJson u.appendResidue),
    ("nextMaintenance",toJson u.nextMaintenance),("nextOwner",toJson u.nextOwner)]))]

def exportEpisode (ss : List RawStage) (es : List RawEvent)
    (ds : List RawDependency) (cs : List Nat) : Json := obj [
  ("stages",exportStages ss),("events",exportEvents es),
  ("dependencies",exportDependencies ds),("carrier_chain",toJson cs)]

def atomicSnapshot : Json := obj [
  ("left",exportEpisode leftStages leftEvents leftDependencies leftCarriers),
  ("right",exportEpisode rightStages rightEvents rightDependencies rightCarriers),
  ("composed",exportEpisode composedStages composedEvents composedDependencies composedCarriers),
  ("left_leg",exportLeg left),("right_leg",exportLeg right),
  ("constructed",exportEpisode (chainStages [left,right]) (chainEvents [left,right])
    (chainDependencies [left,right]) [left.source,left.target,right.target])]
end CSTTT.CorridorTheory.AtomicChain.Models
