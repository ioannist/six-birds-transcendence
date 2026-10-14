import CSTTT.Targets.GenericHandoff.AcquisitionCorridor
import CSTTT.Targets.GenericHandoff.POS04ExecutionFrontier
import CSTTT.Targets.ComputedFIACH.AtomicAcquisition

/-! POS-04 specialization of the generic G4 acquisition constructor.
Provenance: G6_lane_spec.md:104–145; the stage clock is the declared corridor
path ordinal, distinct from the post-exit phase clock. Every support bit is
read from the same assigned event table as the execution-frontier adapter.
Predictive seeds use assigned action supports/positions/hazards (never stored M).
No new model values or intervention rules are introduced.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04AcquisitionCorridor
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open RegisterInterpreter POS04RegisterDynamics CSTTT.CorridorTheory.AtomicChain
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def rawPredictive (rows : KState → Action → List (Ambient × Nat))
    (positions : KState → Nat) (hazards : Ambient → Bool) (s : KState) :=
  (positions s, actions.map fun act => (rows s act).map fun e => hazards e.1)

def seeds : StaticView Cell Value (AcquisitionCorridor.Seeds RouteId) :=
  ⟨.map (fun (p : ((KState → Action → List (Ambient × Nat)) × ((KState → Nat) × (Ambient → Bool))) × (RouteId → List KState)) =>
    let predict := rawPredictive p.1.1 p.1.2.1 p.1.2.2
    { predictive := fun r => (kernel.map predict).eraseDups.idxOf (predict ((p.2 r).getLastD .p0w0))
      history := fun r => (p.2 r).map stateName })
    (.pair (.pair (.cell (Cell.rows Tag.source)) (.pair (.cell Cell.positions) (.cell Cell.hazards)))
      POS04ExecutionFrontier.pathExpr)⟩

def raw : AcquisitionCorridor.Raw Cell Value Register RegisterValue
    ComputedFIACH.LaneDisturbance Action Ambient CSTTT.POS04.Stage EventId RouteId RouteId :=
  ⟨POS04ExecutionFrontier.acquisition,POS04ExecutionFrontier.schema,⟨eventName,"source_live"⟩,seeds⟩

def dependencies : List Cell := POS04ExecutionFrontier.dependencies ++
  [.positions,.hazards]

/-- A total helper for describing an assignment's decoded raw values. The
generic Pass still requires every consumed view to be present before use. -/
def view (a : CSTTT.POS04.Assigned.Assignment) :
    AcquisitionCorridor.View CSTTT.POS04.Stage EventId RouteId RouteId :=
  ⟨POS04ExecutionFrontier.routeView.project ((a .routeTable).getD (canonicalValue .routeTable)),
   POS04ExecutionFrontier.eventView.project ((a .eventTable).getD (canonicalValue .eventTable)),
   (a .realized).getD (canonicalValue .realized),
   POS04ExecutionFrontier.receiverView.project ((a .receiverInput).getD (canonicalValue .receiverInput)),
   {predictive := fun r =>
      let predict := rawPredictive ((a (.rows .source)).getD (canonicalValue (.rows .source)))
        ((a .positions).getD (canonicalValue .positions)) ((a .hazards).getD (canonicalValue .hazards))
      (kernel.map predict).eraseDups.idxOf (predict
        ((POS04ExecutionFrontier.historyPath ((a .histories).getD (canonicalValue .histories))
          ((a .routeTable).getD (canonicalValue .routeTable)) r).getLastD .p0w0))
    history := fun r => (POS04ExecutionFrontier.historyPath
      ((a .histories).getD (canonicalValue .histories))
      ((a .routeTable).getD (canonicalValue .routeTable)) r).map stateName}⟩

theorem read_eq (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    AcquisitionCorridor.read raw a = some (view a) := by
  have hr := cell_value (hc .routeTable (by simp [dependencies,POS04ExecutionFrontier.dependencies]))
  have he := cell_value (hc .eventTable (by simp [dependencies,POS04ExecutionFrontier.dependencies]))
  have hz := cell_value (hc .realized (by simp [dependencies,POS04ExecutionFrontier.dependencies]))
  have hm := cell_value (hc .receiverInput (by simp [dependencies,POS04ExecutionFrontier.dependencies]))
  have hp := cell_value (hc .positions (by simp [dependencies]))
  have hh := cell_value (hc .hazards (by simp [dependencies]))
  have hs := cell_value (hc (.rows .source) (by simp [dependencies,POS04ExecutionFrontier.dependencies,
    temporalDependencies,coreDependencies]))
  have ht := cell_value (hc .histories (by simp [dependencies,POS04ExecutionFrontier.dependencies]))
  simp only [AcquisitionCorridor.read,raw,CellView.read,StaticView.read,seeds,
    POS04ExecutionFrontier.acquisition,POS04ExecutionFrontier.routeView,
    POS04ExecutionFrontier.eventView,POS04ExecutionFrontier.receiverView,POS04ExecutionFrontier.pathExpr,Expr.eval]
  rw [hr,he,hz,hm,hs,hp,hh,ht]
  rfl

/-- Arbitrary-partial acceptance adapter, in BOTH directions. This exposes
the exact generic G4 check on assigned values, not canonical truth alone.
Equivalence to the full G6c lineage readout is a later bridge obligation. -/
theorem pass_iff (a : CSTTT.POS04.Assigned.Assignment) (hc : Complete dependencies a) :
    AcquisitionCorridor.Pass raw a ↔ AcquisitionCorridor.ViewCheck raw (view a) := by
  have ha := (POS04ExecutionFrontier.ready a (fun k hk => hc k (List.mem_append_left _ hk))).1
  constructor
  · rintro ⟨_,v,hv,hpass⟩
    have he := Option.some.inj (hv.symm.trans (read_eq a hc))
    subst v
    exact hpass
  · intro hp
    exact ⟨ha,view a,read_eq a hc,hp⟩

theorem canonical_leg (r : RouteId) :
    AcquisitionCorridor.leg raw (view canonical) r = pos04AtomicLeg r := by
  cases r <;> decide +kernel

theorem canonical_check : AcquisitionCorridor.ViewCheck raw (view canonical) := by
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,?_⟩
  intro r hr
  refine ⟨by cases r <;> decide,by cases r <;> unfold AcquisitionExecution.PathCheck <;>
      refine ⟨.mix1,[.mix2,.exit],rfl,rfl,by decide,by decide,.exit,rfl,rfl,rfl,rfl⟩,
    by cases r <;> unfold AcquisitionExecution.Activated AcquisitionExecution.Mixed <;>
      refine ⟨rfl,rfl,rfl,fun _ => ⟨.mix1,by decide,by decide,by decide,rfl,rfl,rfl⟩⟩,
    by cases r <;> decide,by cases r <;> decide,?_⟩
  rw [canonical_leg]
  exact pos04_atomic_leg_pass r

theorem positive : AcquisitionCorridor.Pass raw canonical :=
  (pass_iff canonical (canonical_complete _)).mpr canonical_check

theorem positive_corridor (r : RouteId) :
    ∃ ls, AcquisitionCorridor.legs raw canonical r = some ls ∧ StrictCorridorWitness ls :=
  AcquisitionCorridor.constructs raw canonical positive r (by cases r <;> decide)

theorem missing_atomic_rejected (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ AcquisitionCorridor.Pass raw (Assigned.put a .eventTable none) := by
  apply AcquisitionCorridor.missing_atomic
  simp [raw,POS04ExecutionFrontier.acquisition,POS04ExecutionFrontier.eventView,CellView.read]

theorem missing_seed_field_rejected (a : CSTTT.POS04.Assigned.Assignment) (k : Cell)
    (hk : k ∈ seeds.dependencies) :
    ¬ AcquisitionCorridor.Pass raw (Assigned.put a k none) :=
  AcquisitionCorridor.missing_seed raw _ k hk (Assigned.put_same _ _ _)

/-- Registered detached support deletion; no source event vertex remains. -/
def detached := Assigned.mapCell canonical .eventTable
  (fun es => es.map (fun e => {e with sourceSupport := false}))
def gap := Assigned.mapCell canonical .realized (fun ss => ss.filter (· != .mix2))

theorem detached_rejected : ¬ AcquisitionCorridor.Pass raw detached := by
  apply AcquisitionCorridor.broken_leg raw detached (view detached)
    (read_eq detached (by intro k _; cases k <;> simp [detached,Assigned.mapCell,Assigned.put,canonical])) RouteId.a (by decide)
  unfold AtomicLegPass
  decide +kernel

theorem gap_rejected : ¬ AcquisitionCorridor.Pass raw gap := by
  apply AcquisitionCorridor.broken_leg raw gap (view gap)
    (read_eq gap (by intro k _; cases k <;> simp [gap,Assigned.mapCell,Assigned.put,canonical])) RouteId.a (by decide)
  unfold AtomicLegPass
  decide +kernel

theorem positive_chain (r : RouteId) : AcquisitionCorridor.ChainPass canonical [(raw,r)] :=
  AcquisitionCorridor.single_chain_pass raw canonical positive r (by cases r <;> decide)

theorem missing_atomic_no_corridor (a : CSTTT.POS04.Assigned.Assignment) (r : RouteId) :
    ¬ AcquisitionCorridor.Readout raw (Assigned.put a .eventTable none) r := by
  apply AcquisitionCorridor.no_readout_missing_atomic
  simp [raw,POS04ExecutionFrontier.acquisition,POS04ExecutionFrontier.eventView,CellView.read]

theorem detached_no_corridor (r : RouteId) : ¬ AcquisitionCorridor.Readout raw detached r := by
  apply AcquisitionCorridor.no_readout_broken_leg raw detached (view detached)
    (read_eq detached (by intro k _; cases k <;> simp [detached,Assigned.mapCell,Assigned.put,canonical])) r
  cases r <;> unfold AtomicLegPass <;> decide +kernel

theorem gap_no_corridor (r : RouteId) : ¬ AcquisitionCorridor.Readout raw gap r := by
  apply AcquisitionCorridor.no_readout_broken_leg raw gap (view gap)
    (read_eq gap (by intro k _; cases k <;> simp [gap,Assigned.mapCell,Assigned.put,canonical])) r
  cases r <;> unfold AtomicLegPass <;> decide +kernel

theorem predictive_raw_equation (a : CSTTT.POS04.Assigned.Assignment) (s : KState) :
    rawPredictive ((a (.rows .source)).getD (canonicalValue (.rows .source)))
      ((a .positions).getD (canonicalValue .positions))
      ((a .hazards).getD (canonicalValue .hazards)) s =
      predictive (runInputs6 a .source).base.base s := by
  simp [rawPredictive,predictive,runInputs6,extraInputs,inputs,Assigned.decode,clauseScope,commonScope]

theorem canonical_seed_M (r : RouteId) :
    (view canonical).seeds.predictive r = taggedMClass .source
      ((sourceHistory (routeOf r).sourceHistory).getLastD .p0w0) := by
  cases r <;> decide +kernel

/-- These are raw field interventions on the generic interface, not edits
to an already constructed witness. Legal constant predictive/owner readouts
are not rejected merely for being constant. Their G1c coherence is separate. -/
inductive GeometryField where
  | source | target | clock | eventName | entryName
  deriving DecidableEq

def brokenGeometry : GeometryField → AcquisitionCorridor.Raw Cell Value Register RegisterValue
    ComputedFIACH.LaneDisturbance Action Ambient CSTTT.POS04.Stage EventId RouteId RouteId
  | .source => {raw with schema := {raw.schema with source := raw.schema.target}}
  | .target => {raw with schema := {raw.schema with target := raw.schema.source}}
  | .clock => {raw with schema := {raw.schema with clock := fun _ => 0}}
  | .eventName => {raw with names := {raw.names with event := fun _ => ""}}
  | .entryName => {raw with names := {raw.names with entry := ""}}

theorem geometry_read (f : GeometryField) :
    AcquisitionCorridor.read (brokenGeometry f) canonical = some (view canonical) := by
  cases f <;> rfl

theorem geometry_field_guard (f : GeometryField) :
    ¬ AcquisitionCorridor.Pass (brokenGeometry f) canonical := by
  rintro ⟨_,v,hv,hcheck⟩
  have he := Option.some.inj (hv.symm.trans (geometry_read f))
  subst v
  cases f
  · exact hcheck.2.1 rfl
  · exact hcheck.2.1 rfl
  · have hpath := (hcheck.2.2.2.2.2.2 .a (by decide)).2.1
    rcases hpath with ⟨first,rest,hlist,_,hall,_⟩
    have hs := (hall .mix1 (by decide)).2.2.2.2.2.2.2.2
    change 0 = 0 + 1 at hs
    contradiction
  · exact hcheck.2.2.2.2.1 .mix1 (by decide) rfl
  · exact hcheck.2.2.2.1 rfl

def noFunding := Assigned.mapCell canonical .receiverInput (fun rec => {rec with funded := false})
theorem no_funding_rejected : ¬ AcquisitionCorridor.Pass raw noFunding := by
  apply AcquisitionCorridor.broken_leg raw noFunding (view noFunding)
    (read_eq noFunding (by intro k _; cases k <;> simp [noFunding,Assigned.mapCell,Assigned.put,canonical])) .a (by decide)
  unfold AtomicLegPass
  decide +kernel

def noHistory := Assigned.mapCell canonical .histories (fun _ _ => [])
theorem no_history_residue_rejected : ¬ AcquisitionCorridor.Pass raw noHistory := by
  apply AcquisitionCorridor.broken_leg raw noHistory (view noHistory)
    (read_eq noHistory (by intro k _; cases k <;> simp [noHistory,Assigned.mapCell,Assigned.put,canonical])) .a (by decide)
  unfold AtomicLegPass
  decide +kernel

def reversedHistories := ComputedFIACH.reversedHistories.assignment
theorem reversed_histories_pass : AcquisitionCorridor.Pass raw reversedHistories := by
  apply (pass_iff reversedHistories (by intro k _; cases k <;>
    simp [reversedHistories,ComputedFIACH.reversedHistories,ComputedFIACH.baseline,
      Assigned.mapCell,Assigned.put,canonical])).mpr
  refine ⟨by decide,by decide,by decide,by decide,by decide,by decide,?_⟩
  intro r _
  refine ⟨by cases r <;> decide,by cases r <;> unfold AcquisitionExecution.PathCheck <;>
      refine ⟨.mix1,[.mix2,.exit],rfl,rfl,by decide,by decide,.exit,rfl,rfl,rfl,rfl⟩,
    by cases r <;> unfold AcquisitionExecution.Activated AcquisitionExecution.Mixed <;>
      refine ⟨rfl,rfl,rfl,fun _ => ⟨.mix1,by decide,by decide,by decide,rfl,rfl,rfl⟩⟩,
    by cases r <;> decide,by cases r <;> decide,?_⟩
  cases r <;> unfold AtomicLegPass <;> decide +kernel

end CSTTT.TargetTheory.GenericHandoff.POS04AcquisitionCorridor
