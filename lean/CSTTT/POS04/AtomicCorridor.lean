import CSTTT.Corridor.AtomicGuards
import CSTTT.POS04.RouteMemory
import CSTTT.POS04.C6

/-! POS-04 is ONE carrier-changing leg, with two mixed events, not two
handoffs. Source: Data.lean:123–190 and frozen M3_model_spec.md:22,31,40–46.
Adapter rules (not new model data): split a jointly supported event into its
source/target owned vertices; connect vertices on successive stages. Snapshot
counters are the declared path ordinal; predictive class is the unchanged
receiver terminal M-class. Encode raw route histories followed by the executed
event prefix. Funding/writer availability gates the snapshots. This is the
finite path audit, not a new full carrier or an unbounded objecthood claim.
Interventions use POS-04's declared support-deletion conjunction, NOT the COR
additive projection rule. Route-indexed discipline does not assert nonflatness. -/
namespace CSTTT.POS04
open CSTTT.CorridorTheory.AtomicChain
open CSTTT.Objecthood.T1Audit

def atomicCarrierCode (tag : Tag) : Nat := tags.idxOf tag

def atomicPosOwner (i : Nat) : Nat :=
  atomicCarrierCode (if i + 1 = stages.length then .target else .source)

def atomicPosSupport (i : Nat) : List Nat :=
  if i = 0 then [atomicCarrierCode .source]
  else if i + 1 = stages.length then [atomicCarrierCode .target]
  else [atomicCarrierCode .source,atomicCarrierCode .target]

def atomicPosResidue (id : RouteId) (i : Nat) : List String :=
  (sourceHistory (routeOf id).sourceHistory).map stateName ++
    ((routeOf id).eventPath.take i).map eventName

def atomicPosAvailable : Bool :=
  receiver.funded && receiver.sourcePresent && receiver.targetReceiverFunded &&
  c6StrictEvents && c6RealizedPaths .positive &&
  c6FundedTicks .positive .source && c6FundedTicks .positive .target &&
  c6Writers .positive .source && c6Writers .positive .target &&
  c8Available .funded .source && c8Available .funded .target &&
  decide (routeFutureOutput .positive .a = some 0 ∧
    routeFutureOutput .positive .b = some 1)

def atomicPosStages (id : RouteId) : List RawStage :=
  stages.mapIdx fun i stage =>
    ⟨atomicPosSupport i, decide (stage ∈ realizedStages) && atomicPosAvailable,
      ⟨taggedMClass .source ((sourceHistory (routeOf id).sourceHistory).getLastD .p0w0),
        i,i,i,i,atomicPosResidue id i,
        if atomicPosAvailable then "funded" else "",atomicPosOwner i⟩⟩

/-- Expansion is by actual Boolean support, not an invented carrier. -/
def atomicPosEvents : List RawEvent :=
  ⟨"source_live",atomicCarrierCode .source,0⟩ ::
  events.flatMap fun e =>
    (if e.sourceSupport then
      [⟨eventName e.id ++ "-source",atomicCarrierCode .source,stages.idxOf e.toStage⟩]
      else []) ++
    (if e.targetSupport then
      [⟨eventName e.id ++ "-target",atomicCarrierCode .target,stages.idxOf e.toStage⟩]
      else [])

def atomicPosDependencies : List RawDependency :=
  atomicPosEvents.flatMap fun a =>
    (atomicPosEvents.filter (fun b => b.stage == a.stage + 1)).map
      (fun b => ⟨a.id,b.id⟩)

def atomicPosUpdates : List ReadoutUpdate :=
  eventIds.mapIdx fun i e =>
    ⟨0,1,1,1,1,[eventName e],"funded",atomicPosOwner (i+1)⟩

def pos04AtomicLeg (id : RouteId) : FiniteAtomicLeg where
  interventionMode := .mixedSupport
  source := atomicCarrierCode .source
  target := atomicCarrierCode .target
  stages := atomicPosStages id
  events := atomicPosEvents
  dependencies := atomicPosDependencies
  updates := atomicPosUpdates
  -- Inactive additive-mode inputs; never used by the POS support rule.
  base := default
  sourceContribution := default
  targetContribution := default
  sourceAudit := "mix_2-source"
  targetAudit := "mix_2-target"
  laterAudit := "exit-target"

theorem pos04_atomic_leg_pass (id : RouteId) : AtomicLegPass (pos04AtomicLeg id) := by
  cases id <;> unfold AtomicLegPass <;> decide

theorem pos04_single_leg_pass (id : RouteId) :
    CSTTT.CorridorTheory.AtomicChain.CorridorPass [pos04AtomicLeg id] := by
  cases id <;> unfold CSTTT.CorridorTheory.AtomicChain.CorridorPass <;> decide

theorem pos04_single_leg_corridor (id : RouteId) :
    StrictCorridorWitness [pos04AtomicLeg id] :=
  strictTemporalCorridorComposition_generic _ (pos04_single_leg_pass id)

/-- The encoded exit register is exactly L7's raw tuple, not a route label. -/
theorem pos04_exit_residue_exact (id : RouteId) :
    (exit (pos04AtomicLeg id)).frontier.residue =
      (routeRegister id).1.map stateName ++ (routeRegister id).2.map eventName := by
  cases id <;> decide

theorem pos04_adapter_existing_audit :
    CSTTT.POS04.CorridorPass .positive ∧ C6Trace .positive .source ∧
      C6Trace .positive .target ∧ RouteMemoryPass .positive :=
  ⟨corridor_positive,c6_trace_each_tag .source,c6_trace_each_tag .target,route_memory_positive⟩

/-- L5 M link: the finite class coordinate denotes exactly raw action-support
and hazard M, not an independently interpreted rank label. -/
theorem pos04_atomic_M_link (s t : KState) :
    rawM .source s = rawM .source t ↔
      taggedMClass .source s = taggedMClass .source t :=
  rawM_iff_imported_M .source s t

/-- Applying COR's additive rule to POS-04's support-only intervention data
is rejected; the adapter must use the declared intervention semantics. -/
theorem pos04_wrong_intervention_mode (id : RouteId) :
    ¬ AtomicLegPass {pos04AtomicLeg id with interventionMode := .additive} := by
  cases id <;> unfold AtomicLegPass <;> decide

end CSTTT.POS04
