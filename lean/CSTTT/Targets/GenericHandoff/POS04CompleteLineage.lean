import CSTTT.Targets.GenericHandoff.POS04ExecutionLocality
import CSTTT.Targets.GenericHandoff.POS04LineageFutureBoundary
import CSTTT.Targets.GenericHandoff.POS04RouteReadout
import CSTTT.Targets.GenericHandoff.POS04RecordComponent

/-! Complete, independently defined POS-04-family lineage readout. It
constructs G4 corridor witnesses; ties their seeds to actual G1c snapshots;
checks the finite typed maps, record arrows and receiver endpoint; and retains
the full route comparison plus actual closure-wide execution transport.

This is NOT inferred from the weaker ComputedFIACH.StrictTemporalLineage.
The relabeling regression proves that implication false. The sufficient gate
uses a bisimulation certificate; the semantic readout uses the full word law.
This is an arbitrary-assignment family adapter, not the final RawHandoff. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04CompleteLineage
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open RegisterInterpreter POS04RegisterDynamics CSTTT.TargetTheory.ComputedFIACH
open CSTTT.TransportTheory CSTTT.RecordTheory CSTTT.CorridorTheory.AtomicChain
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

abbrev staged (m : RawLaneModel) := image m.assignment

def CorridorReadout (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  ∀ r ∈ routeIds, AcquisitionCorridor.Readout POS04AcquisitionCorridor.raw a r

def SeedReadout (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  ∃ hs : ExecutionFrontier.Ready POS04ExecutionFrontier.raw a,
    ∀ v, AcquisitionCorridor.read POS04AcquisitionCorridor.raw a = some v →
      ExecutedAcquisitionCorridor.SeedCoherence POS04ExecutedCorridor.raw a hs v

/-- Typed finite-factor equations are additional to full execution transport;
they cannot substitute for it (the K-only branch regression). -/
def FactorReadout (m : RawLaneModel) : Prop :=
  Complete (POS04FactorTransport.view .source).dependencies (staged m) ∧
  Complete (POS04FactorTransport.view .target).dependencies (staged m) ∧
  POS04FactorTransport.FactorFields m

/-- The real computed arrows, not the optional stronger nonempty-arrow
certifier. Strict run record advancement is separately required on every
supported branch by the execution readout's independent positive recipes. -/
def RecordReadout (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  Complete POS04RecordComponent.view.dependencies a ∧
    ∀ i j, SourceArrow (assignedRecordTransport a) i j →
      TargetArrow (assignedRecordTransport a) i j

/-- Named complete lineage. Every object is interpreted from the same staged
assignment. The endpoint condition is the existing computed raw receiver/
corridor check; no stored endpoint, class or status enters. -/
def StrictTemporalLineage (m : RawLaneModel) : Prop :=
  CorridorReadout (staged m) ∧ SeedReadout (staged m) ∧ FactorReadout m ∧
  RecordReadout (staged m) ∧ TypedAcquisitionEndpointPass m ∧
  (Complete POS04RouteExecution.dependencies (staged m) ∧ POS04RouteReadout.RouteReadout (staged m)) ∧
  ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw (staged m)

/-- Sufficient, computed component gates. This is not the legacy lineage gate
and no converse from failure of a sufficient check to its conclusion is used. -/
def Valid (m : RawLaneModel) : Prop :=
  AcquisitionCorridor.Pass POS04AcquisitionCorridor.raw (staged m) ∧ SeedReadout (staged m) ∧
  FactorTransport.Pass (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    POS04FactorTransport.binding (staged m) ∧ RecordReadout (staged m) ∧
  TypedAcquisitionEndpointPass m ∧ POS04RouteExecution.RoutePass (staged m) ∧
  ExecutionBridge.Valid POS04ExecutionBridge.raw (staged m)

theorem soundness (m : RawLaneModel) (h : Valid m) : StrictTemporalLineage m := by
  obtain ⟨hc,hs,hf,hr,he,hrt,hx⟩ := h
  exact ⟨fun r hin => AcquisitionCorridor.constructs _ _ hc r hin,hs,
    (POS04FactorTransport.pass_iff m).mp hf,hr,he,
    (POS04RouteReadout.route_readout_partial_iff _).mp hrt,
    ExecutionBridge.semantic_soundness _ _ hx⟩

/-- Whole arbitrary-partial semantic adapter. The bridge's actual weights,
updates and full observations are visible on its entire computed closure;
route retention still quantifies over EVERY target response branch.
This is semantic-readout equivalence, not equivalence with the legacy gate. -/
theorem semantic_readout_iff (m : RawLaneModel) : StrictTemporalLineage m ↔
    CorridorReadout (staged m) ∧ SeedReadout (staged m) ∧ FactorReadout m ∧
    RecordReadout (staged m) ∧ TypedAcquisitionEndpointPass m ∧
    (Complete POS04RouteExecution.dependencies (staged m) ∧ POS04RouteReadout.RouteReadout (staged m)) ∧
    (ExecutionFrontier.SemanticReadout POS04ExecutionFrontier.raw (staged m) ∧
      ExecutionFrontier.SemanticReadout POS04ReceiverFrontier.raw (staged m) ∧
      POS04SemanticExecution.TransportLaws (staged m)) := by
  unfold StrictTemporalLineage
  rw [POS04SemanticExecution.semantic_bridge_iff]

/-- Exact G4 construction/readout adapter: no precomputed witness is supplied. -/
theorem corridor_coordinates_iff (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete POS04AcquisitionCorridor.dependencies a) :
    CorridorReadout a ↔ ∀ r ∈ routeIds,
      AtomicLegPass (AcquisitionCorridor.leg POS04AcquisitionCorridor.raw (POS04AcquisitionCorridor.view a) r) := by
  have hv := POS04AcquisitionCorridor.read_eq a hc
  constructor
  · intro h r hr
    obtain ⟨ls,he,hw⟩ := h r hr
    have hs : ls = [AcquisitionCorridor.leg POS04AcquisitionCorridor.raw (POS04AcquisitionCorridor.view a) r] := by
      simpa [AcquisitionCorridor.legs,hv] using he.symm
    subst ls
    exact chain_each_pass _ hw.pass.2.1 _ (List.mem_cons_self)
  · intro h r hr
    refine ⟨[AcquisitionCorridor.leg POS04AcquisitionCorridor.raw (POS04AcquisitionCorridor.view a) r],
      by simp [AcquisitionCorridor.legs,hv],strictTemporalCorridorComposition_generic _ ?_⟩
    refine ⟨by simp,h r hr,?_⟩
    change some (atomicCarrierCode .source) ≠ some (atomicCarrierCode .target)
    decide

/-- The coordinate equations are evaluated on the actual source folds at ALL
four declared snapshots. `coordinate` is decoded from the raw instruction,
not supplied; absence cannot witness its existential. -/
def SeedEquations (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  ∃ coordinate, POS04ExecutedCorridor.coordinate.read a = some coordinate ∧
    (∀ i j : Audited POS04ExecutionFrontier.audit,
      coordinate (POS04ExecutedCorridor.observed a i.val).predictive =
        coordinate (POS04ExecutedCorridor.observed a j.val).predictive →
      (POS04ExecutedCorridor.observed a i.val).predictive =
        (POS04ExecutedCorridor.observed a j.val).predictive) ∧
    ∀ histories, POS04ExecutionFrontier.acquisition.histories.read a = some histories →
      ∀ i ∈ POS04ExecutionFrontier.audit, i.2 = (histories i.1).length →
        (POS04AcquisitionCorridor.view a).seeds.predictive i.1 =
          coordinate (POS04ExecutedCorridor.observed a i).predictive ∧
        (POS04AcquisitionCorridor.view a).seeds.history i.1 =
          (POS04ExecutedCorridor.observed a i).residue.1.map stateName ∧
        (POS04AcquisitionCorridor.view a).seeds.history i.1 ++
          ((POS04AcquisitionCorridor.view a).routes i.1).path.map eventName =
          (POS04ExecutedCorridor.observed a i).residue.1.map stateName ++
            (POS04ExecutedCorridor.observed a i).residue.2.map eventName

theorem seed_equations_iff (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete POS04ExecutionFrontier.dependencies a) :
    ExecutedAcquisitionCorridor.SeedCoherence POS04ExecutedCorridor.raw a
      (POS04ExecutionFrontier.ready a hc) (POS04AcquisitionCorridor.view a) ↔ SeedEquations a := by
  unfold ExecutedAcquisitionCorridor.SeedCoherence SeedEquations
  simp only [POS04ExecutedCorridor.raw,POS04ExecutedCorridor.snapshot_equation a hc]
  rfl

theorem corridor_inputs (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete POS04ExecutionFrontier.dependencies a) :
    Complete POS04AcquisitionCorridor.dependencies a := by
  intro k hk
  rcases List.mem_append.mp hk with hh | he
  · exact hc k hh
  · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
    rcases he with rfl | rfl <;> apply hc
    all_goals simp [POS04ExecutionFrontier.dependencies,temporalDependencies,coreDependencies]

theorem seed_readout_iff (a : CSTTT.POS04.Assigned.Assignment) :
    SeedReadout a ↔ Complete POS04ExecutionFrontier.dependencies a ∧ SeedEquations a := by
  constructor
  · rintro ⟨hs,h⟩
    have hc := (POS04SemanticExecution.source_ready_iff a).mp hs
    exact ⟨hc,(seed_equations_iff a hc).mp
      (h _ (POS04AcquisitionCorridor.read_eq a (corridor_inputs a hc)))⟩
  · rintro ⟨hc,he⟩
    refine ⟨POS04ExecutionFrontier.ready a hc,?_⟩
    intro v hv
    have hval := Option.some.inj (hv.symm.trans (POS04AcquisitionCorridor.read_eq a (corridor_inputs a hc)))
    subst v
    exact (seed_equations_iff a hc).mpr he

/-- Compose the exact component adapters into the COMPLETE semantic readout.
Quantifies over every partial assignment; no legacy acceptance premise occurs.
In particular the RHS exposes actual closure-wide branch probabilities, actual
updaters and full observations, not only the K destination comparator. -/
theorem actual_readout_iff (m : RawLaneModel) : StrictTemporalLineage m ↔
    Complete POS04ExecutionFrontier.dependencies (staged m) ∧
    (∀ r ∈ routeIds, AtomicLegPass (AcquisitionCorridor.leg POS04AcquisitionCorridor.raw
      (POS04AcquisitionCorridor.view (staged m)) r)) ∧ SeedEquations (staged m) ∧
    (Complete (POS04FactorTransport.view .source).dependencies (staged m) ∧
      Complete (POS04FactorTransport.view .target).dependencies (staged m) ∧ POS04FactorTransport.FactorEquations m) ∧
    (Complete POS04RecordComponent.view.dependencies (staged m) ∧
      ∀ i j, SourceArrow (RecordComponent.transport POS04RecordComponent.cfg (POS04RecordComponent.data (staged m))) i j →
        TargetArrow (RecordComponent.transport POS04RecordComponent.cfg (POS04RecordComponent.data (staged m))) i j) ∧
    TypedAcquisitionEndpointPass m ∧
    (Complete POS04RouteExecution.dependencies (staged m) ∧ POS04RouteReadout.RouteReadout (staged m)) ∧
    (ExecutionFrontier.SemanticReadout POS04ExecutionFrontier.raw (staged m) ∧
      ExecutionFrontier.SemanticReadout POS04ReceiverFrontier.raw (staged m) ∧
      POS04SemanticExecution.TransportLaws (staged m)) := by
  constructor
  · intro h
    obtain ⟨hc,hseed⟩ := (seed_readout_iff _).mp h.2.1
    exact ⟨hc,(corridor_coordinates_iff _ (corridor_inputs _ hc)).mp h.1,hseed,
      ⟨h.2.2.1.1,h.2.2.1.2.1,(POS04FactorTransport.factor_equations_iff m).mpr h.2.2.1.2.2⟩,
      ⟨h.2.2.2.1.1,by simpa only [POS04RecordComponent.transport_equation] using h.2.2.2.1.2⟩,
      h.2.2.2.2.1,h.2.2.2.2.2.1,(POS04SemanticExecution.semantic_bridge_iff _).mp h.2.2.2.2.2.2⟩
  · rintro ⟨hc,hcorr,hseed,hfactor,hrecord,hendpoint,hroute,hexecution⟩
    exact ⟨(corridor_coordinates_iff _ (corridor_inputs _ hc)).mpr hcorr,
      (seed_readout_iff _).mpr ⟨hc,hseed⟩,
      ⟨hfactor.1,hfactor.2.1,(POS04FactorTransport.factor_equations_iff m).mp hfactor.2.2⟩,
      ⟨hrecord.1,by simpa only [POS04RecordComponent.transport_equation] using hrecord.2⟩,
      hendpoint,hroute,(POS04SemanticExecution.semantic_bridge_iff _).mpr hexecution⟩

/-- Status derives the complete Indexed/Retained comparison: raw distinct
paths, common receiver endpoint and every retained post-exit branch. -/
theorem route_status (m : RawLaneModel) (h : StrictTemporalLineage m) :
    RouteComponent.statusOf POS04ExecutionFrontier.schema POS04RouteExecution.routeRaw (staged m) = .routeIndexed :=
  (POS04RouteReadout.semantic_status_partial_binding _).mpr h.2.2.2.2.2.1

theorem baseline_seed : SeedReadout canonical :=
  ⟨POS04ExecutionFrontier.canonical_ready,fun v hv => POS04ExecutedCorridor.canonical_seed_coherence _ v hv⟩

theorem baseline_record : RecordReadout canonical := by
  refine ⟨canonical_complete _,?_⟩
  rw [← POS04RecordComponent.transport_equation]
  exact RecordComponent.sound _ _ POS04RecordComponent.positive_check

theorem baseline_endpoint : TypedAcquisitionEndpointPass baseline :=
  (lineage_checked_parts baseline baseline_lineage_lane).2.2

theorem positive_valid : Valid baseline := by
  simp only [Valid,staged,show baseline.assignment = canonical from rfl,image_canonical]
  exact ⟨POS04AcquisitionCorridor.positive,baseline_seed,POS04FactorTransport.positive,
    baseline_record,baseline_endpoint,POS04RouteExecution.positive,POS04ExecutionBridge.positive⟩

theorem positive : StrictTemporalLineage baseline := soundness baseline positive_valid

/-- Direct negative of the strengthened semantic conclusion. -/
theorem relabel_no_lineage : ¬ StrictTemporalLineage POS04LineageFutureBoundary.proposal :=
  fun h => POS04LineageFutureBoundary.no_complete_execution_readout h.2.2.2.2.2.2

/-- The old gate and named readout are deliberately retained as weaker evidence. -/
theorem legacy_does_not_imply_complete :
    ¬ (∀ m : RawLaneModel, ComputedFIACH.StrictTemporalLineage m → StrictTemporalLineage m) := by
  intro h
  exact relabel_no_lineage (h _ POS04LineageFutureBoundary.legacy_named_readout_accepts)

theorem missing_atomic_no_lineage (m : RawLaneModel) :
    ¬ StrictTemporalLineage {m with assignment := put m.assignment .eventTable none} := by
  intro h
  have hm : staged {m with assignment := put m.assignment .eventTable none} .eventTable = none :=
    image_delete_cell m.assignment .eventTable
  apply ExecutionBridge.missing_atomic_no_semantic_readout POS04ExecutionBridge.raw _ _ h.2.2.2.2.2.2
  simp [POS04ExecutionBridge.raw,POS04ExecutionFrontier.raw,POS04ExecutionFrontier.acquisition,
    POS04ExecutionFrontier.eventView,CellView.read,hm]

/-- Registered package deletion: the full execution layer is unchanged by
proved instruction locality, including all counter-bearing futures. -/
theorem package_control_seed : SeedReadout (staged packageDeletion) := by
  let a := staged packageDeletion
  have hc : Complete POS04ExecutionFrontier.dependencies a := by
    intro k hk
    have he := POS04ExecutionLocality.package_control_unchanged k
      (by intro he; subst k; revert hk; decide)
    change (image packageDeletion.assignment k).isSome = true
    rw [← he]; exact canonical_complete _ k hk
  have hac : Complete POS04AcquisitionCorridor.dependencies a := by
    intro k hk
    have he := POS04ExecutionLocality.package_control_unchanged k
      (by intro he; subst k; revert hk; decide)
    change (image packageDeletion.assignment k).isSome = true
    rw [← he]; exact canonical_complete _ k hk
  have ho (i : RouteId × Nat) :
      ExecutionFrontier.observation POS04ExecutionFrontier.raw a (POS04ExecutionFrontier.ready a hc) i =
        ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical POS04ExecutionFrontier.canonical_ready i := by
    rw [POS04ExecutedCorridor.snapshot_equation a hc,
      POS04ExecutedCorridor.snapshot_equation canonical (canonical_complete _)]
    unfold POS04ExecutedCorridor.observed
    have hw : ExecutionFrontier.historyPrefix POS04ExecutionFrontier.raw a i =
        ExecutionFrontier.historyPrefix POS04ExecutionFrontier.raw canonical i := rfl
    rw [hw,POS04ExecutionLocality.initial_unchanged,POS04ExecutionLocality.source_fold_unchanged,
      POS04ExecutionLocality.inputs_unchanged]
  dsimp only [a] at ho
  refine ⟨POS04ExecutionFrontier.ready a hc,?_⟩
  intro v hv
  have he := Option.some.inj (hv.symm.trans (POS04AcquisitionCorridor.read_eq a hac))
  have hview : POS04AcquisitionCorridor.view a = POS04AcquisitionCorridor.view canonical := rfl
  rw [hview] at he
  subst v
  obtain ⟨coordinate,hcoord,hinj,hseeds⟩ := POS04ExecutedCorridor.canonical_seed_coherence
    POS04ExecutionFrontier.canonical_ready _ (POS04AcquisitionCorridor.read_eq canonical (canonical_complete _))
  refine ⟨coordinate,?_,?_,?_⟩
  · have hr : POS04ExecutedCorridor.coordinate.read a = POS04ExecutedCorridor.coordinate.read canonical := rfl
    exact hr.trans hcoord
  · intro i j hsame
    simp only [POS04ExecutedCorridor.raw] at hsame ⊢
    rw [ho,ho] at hsame ⊢
    exact hinj i j hsame
  · intro words hw i hi hend
    have hword : POS04ExecutionFrontier.acquisition.histories.read a =
        POS04ExecutionFrontier.acquisition.histories.read canonical := rfl
    change POS04ExecutionFrontier.acquisition.histories.read a = some words at hw
    rw [hword] at hw
    simpa only [POS04ExecutedCorridor.raw,ho] using hseeds words hw i hi hend

theorem package_control_corridor : CorridorReadout (staged packageDeletion) := by
  intro r hr
  obtain ⟨ls,he,hw⟩ := POS04AcquisitionCorridor.positive_corridor r
  refine ⟨ls,?_,hw⟩
  exact he

theorem package_control_factor : FactorReadout packageDeletion := by
  refine ⟨?_,?_,?_⟩
  · intro k hk
    have he := POS04ExecutionLocality.package_control_unchanged k
      (by intro he; subst k; revert hk; decide)
    change (image packageDeletion.assignment k).isSome = true
    rw [← he]; exact canonical_complete _ k hk
  · intro k hk
    have he := POS04ExecutionLocality.package_control_unchanged k
      (by intro he; subst k; revert hk; decide)
    change (image packageDeletion.assignment k).isSome = true
    rw [← he]; exact canonical_complete _ k hk
  · apply (POS04FactorTransport.factor_equations_iff packageDeletion).mp
    exact POS04FactorTransport.canonical_equations

theorem package_control_record : RecordReadout (staged packageDeletion) := by
  refine ⟨?_,?_⟩
  · intro k hk
    have he := POS04ExecutionLocality.package_control_unchanged k
      (by intro he; subst k; revert hk; decide)
    change (image packageDeletion.assignment k).isSome = true
    rw [← he]; exact canonical_complete _ k hk
  · exact baseline_record.2

theorem package_control_route : Complete POS04RouteExecution.dependencies (staged packageDeletion) ∧
    POS04RouteReadout.RouteReadout (staged packageDeletion) := by
  refine ⟨?_,?_⟩
  · intro k hk
    have he := POS04ExecutionLocality.package_control_unchanged k
      (by intro he; subst k; revert hk; decide)
    change (image packageDeletion.assignment k).isSome = true
    rw [← he]; exact canonical_complete _ k hk
  · have hsupport := POS04ExecutionLocality.route_support_unchanged
    have harrival := POS04ExecutionLocality.route_arrival_unchanged
    have hinputs := POS04ExecutionLocality.inputs_unchanged
    have hinit := POS04ExecutionLocality.initial_unchanged
    have hword : POS04RouteExecution.wordFor (staged packageDeletion) = POS04RouteExecution.wordFor canonical := rfl
    have hpaths : POS04RouteExecution.pathsFor (staged packageDeletion) = POS04RouteExecution.pathsFor canonical := rfl
    have hevents : POS04RouteExecution.eventsFor (staged packageDeletion) = POS04RouteExecution.eventsFor canonical := rfl
    have hreceiver : POS04RouteExecution.receiverFor (staged packageDeletion) = POS04RouteExecution.receiverFor canonical := rfl
    have hresponse (x : Run6) : POS04RouteExecution.responseAction (staged packageDeletion) x =
        POS04RouteExecution.responseAction canonical x := rfl
    have hresidue : POS04RouteReadout.residueFor (staged packageDeletion) = POS04RouteReadout.residueFor canonical := rfl
    simpa only [POS04RouteReadout.RouteReadout,POS04RouteReadout.RetainedReadout,
      POS04RouteExecution.ResultReadout,POS04RouteExecution.ArrivalReadout,
      staged,hsupport,harrival,hinputs,hinit,hword,hpaths,hevents,hreceiver,hresponse,hresidue] using
        POS04RouteReadout.positive_readout

theorem package_control_lineage : StrictTemporalLineage packageDeletion :=
  ⟨package_control_corridor,package_control_seed,package_control_factor,package_control_record,
    (lineage_checked_parts _ package_deletion_lineage_lane).2.2,package_control_route,
    POS04ExecutionLocality.package_control_bridge⟩

theorem withdrawal_control_lineage : StrictTemporalLineage withdrawalDeletion := by
  obtain ⟨hc,hs,hf,hr,he,hroute,hx⟩ := positive
  exact ⟨hc,hs,hf,hr,(lineage_checked_parts _ withdrawal_deletion_lineage_lane).2.2,hroute,hx⟩

/-- Direct failure of the constructed G4 witness, not a gate-only failure. -/
theorem lineage_control_no_lineage : ¬ StrictTemporalLineage lineageDeletion := by
  intro h
  obtain ⟨ls,he,hw⟩ := h.1 .a (by decide)
  have hc : Complete POS04AcquisitionCorridor.dependencies (staged lineageDeletion) := by
    rw [show staged lineageDeletion = lineageArrival from lineage_staged_assignment]
    intro k _
    cases k with
    | rows t => cases t <;> rfl
    | lower t => cases t <;> rfl
    | protocols t => cases t <;> rfl
    | ticks t => cases t <;> rfl
    | joint t => cases t <;> rfl
    | resources t => cases t <;> rfl
    | _ => rfl
  have hread := POS04AcquisitionCorridor.read_eq (staged lineageDeletion) hc
  have hls : ls = [AcquisitionCorridor.leg POS04AcquisitionCorridor.raw
      (POS04AcquisitionCorridor.view (staged lineageDeletion)) .a] := by
    simpa [AcquisitionCorridor.legs,hread] using he.symm
  subst ls
  have hpass := chain_each_pass _ hw.pass.2.1
    (AcquisitionCorridor.leg POS04AcquisitionCorridor.raw
      (POS04AcquisitionCorridor.view (staged lineageDeletion)) .a) (by simp)
  have bad : ¬ AtomicLegPass (AcquisitionCorridor.leg POS04AcquisitionCorridor.raw
      (POS04AcquisitionCorridor.view (staged lineageDeletion)) .a) := by
    unfold AtomicLegPass
    decide +kernel
  exact bad hpass

theorem F_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ StrictTemporalLineage packageDeletion ∧
      ¬ PostWithdrawalFullAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ StrictTemporalLineage lineageDeletion ∧
      PostWithdrawalFullAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ StrictTemporalLineage withdrawalDeletion ∧
      ¬ PostWithdrawalFullAutonomy withdrawalDeletion) :=
  ⟨⟨package_deletion_no_realization,package_control_lineage,package_deletion_no_full_readout⟩,
    ⟨derive_package_lane _ lineage_deletion_package,lineage_control_no_lineage,
      derive_full_autonomy_lane _ lineage_deletion_AF⟩,
    ⟨derive_package_lane _ package_lane_positive,withdrawal_control_lineage,withdrawal_deletion_no_full_readout⟩⟩

theorem O_control_vectors :
    (¬ IntegratedTargetRealization packageDeletion ∧ StrictTemporalLineage packageDeletion ∧
      PostWithdrawalOperationalAutonomy packageDeletion) ∧
    (IntegratedTargetRealization lineageDeletion ∧ ¬ StrictTemporalLineage lineageDeletion ∧
      PostWithdrawalOperationalAutonomy lineageDeletion) ∧
    (IntegratedTargetRealization withdrawalDeletion ∧ StrictTemporalLineage withdrawalDeletion ∧
      ¬ PostWithdrawalOperationalAutonomy withdrawalDeletion) :=
  ⟨⟨package_deletion_no_realization,package_control_lineage,derive_operational_autonomy_lane _ package_deletion_AO⟩,
    ⟨derive_package_lane _ lineage_deletion_package,lineage_control_no_lineage,
      derive_operational_autonomy_lane _ lineage_deletion_AO⟩,
    ⟨derive_package_lane _ package_lane_positive,withdrawal_control_lineage,withdrawal_deletion_no_operational_readout⟩⟩

theorem operational_named_separation :
    (∃ m, ¬ IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧ PostWithdrawalOperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ ¬ StrictTemporalLineage m ∧ PostWithdrawalOperationalAutonomy m) ∧
    (∃ m, IntegratedTargetRealization m ∧ StrictTemporalLineage m ∧ ¬ PostWithdrawalOperationalAutonomy m) :=
  ⟨⟨packageDeletion,O_control_vectors.1⟩,⟨lineageDeletion,O_control_vectors.2.1⟩,
    ⟨withdrawalDeletion,O_control_vectors.2.2⟩⟩

/-- Regression on the EXACT unchanged legacy validators. Their soundness
statements remain valid for their weaker named lineage conclusion. -/
theorem relabel_legacy_F_accepts : validF ⟨POS04LineageFutureBoundary.proposal⟩ = true := by
  decide +kernel

theorem relabel_legacy_O_accepts : validO ⟨POS04LineageFutureBoundary.proposal⟩ = true := by
  decide +kernel

/-- The newly discovered intervention is a lineage-only separator under the
strengthened semantics. Package and autonomy positives consume their own
computed validators; legacy lineage is NEVER used to supply the new L field. -/
theorem relabel_F_vector : IntegratedTargetRealization POS04LineageFutureBoundary.proposal ∧
    ¬ StrictTemporalLineage POS04LineageFutureBoundary.proposal ∧
    PostWithdrawalFullAutonomy POS04LineageFutureBoundary.proposal := by
  have h := temporalFIACH_sound_F _ relabel_legacy_F_accepts
  exact ⟨h.1,relabel_no_lineage,h.2.2⟩

theorem relabel_O_vector : IntegratedTargetRealization POS04LineageFutureBoundary.proposal ∧
    ¬ StrictTemporalLineage POS04LineageFutureBoundary.proposal ∧
    PostWithdrawalOperationalAutonomy POS04LineageFutureBoundary.proposal := by
  have h := temporalFIACH_sound_O _ relabel_legacy_O_accepts
  exact ⟨h.1,relabel_no_lineage,h.2.2⟩

/-- Full-interface, all-state and all-word futures of BOTH actual interpreters. -/
theorem actual_full_futures (m : RawLaneModel) (h : StrictTemporalLineage m) (t : Tag) :
    FullFutureSufficient (actualFuture6 (staged m) t) := by
  cases t
  · obtain ⟨hr,_,_,_,_,hf,_,_⟩ := h.2.2.2.2.2.2.1
    exact (POS04SemanticExecution.full_future_iff _ .source
      ((POS04SemanticExecution.temporal_ready_iff _ .source).mp hr.2)).mp hf
  · obtain ⟨hr,_,_,_,_,hf,_,_⟩ := h.2.2.2.2.2.2.2.1
    exact (POS04SemanticExecution.full_future_iff _ .target
      ((POS04SemanticExecution.temporal_ready_iff _ .target).mp hr.2)).mp hf

/-- Every consumed source/target execution field has a direct semantic guard.
No assumption of readiness is combined with a missing-cell assumption. -/
theorem missing_source_no_lineage (m : RawLaneModel) (k : Cell)
    (hk : k ∈ POS04ExecutionFrontier.dependencies) :
    ¬ StrictTemporalLineage {m with assignment := put m.assignment (swapCell k) none} := by
  intro h
  obtain ⟨hs,_⟩ := h.2.2.2.2.2.2
  have hc := (POS04SemanticExecution.source_ready_iff _).mp hs.choose
  have hp := hc k hk
  change (image (put m.assignment (swapCell k) none) k).isSome = true at hp
  have hz : image (put m.assignment (swapCell k) none) k = none := image_delete_cell m.assignment k
  exact Bool.noConfusion ((congrArg Option.isSome hz).symm.trans hp)

theorem missing_target_no_lineage (m : RawLaneModel) (k : Cell)
    (hk : k ∈ POS04ReceiverFrontier.dependencies) :
    ¬ StrictTemporalLineage {m with assignment := put m.assignment (swapCell k) none} := by
  intro h
  obtain ⟨_,ht,_⟩ := h.2.2.2.2.2.2
  have hc := (POS04SemanticExecution.target_ready_iff _).mp ht.choose
  have hp := hc k hk
  change (image (put m.assignment (swapCell k) none) k).isSome = true at hp
  have hz : image (put m.assignment (swapCell k) none) k = none := image_delete_cell m.assignment k
  exact Bool.noConfusion ((congrArg Option.isSome hz).symm.trans hp)

end CSTTT.TargetTheory.GenericHandoff.POS04CompleteLineage
