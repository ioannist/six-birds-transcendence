import CSTTT.Targets.GenericHandoff.POS04ReceiverFrontier

/-! Two-sided actual-support execution transport on the shared POS-04 cells.
The target history is produced by the raw activated receiver. All four audit
snapshots execute their own assigned source/target rows. The eight-field
transport law covers the entire computed source closure, not only the audits.
This is the executed signature specialization, not yet the enclosing generic
factor/record/route bridge extraction or final StrictTemporalLineage theorem.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ExecutionBridge
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TransportTheory
open RegisterInterpreter POS04RegisterDynamics
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def raw : ExecutionBridge.Raw Cell Value Register Register RegisterValue RegisterValue
    LaneDisturbance Action Ambient CSTTT.POS04.PredictiveNow CSTTT.POS04.PredictiveNow
      (List KState × List EventId) Bool CSTTT.POS04.Stage EventId RouteId RouteId :=
  ⟨POS04ExecutionFrontier.raw,POS04ReceiverFrontier.raw,
    (fun k => .register k),acquisitionSnapshotMaps⟩

theorem translation_ready (a : CSTTT.POS04.Assigned.Assignment) : ExecutionBridge.TranslationReady raw a := by
  intro k j hj
  simp [raw,Expr.dependencies] at hj

theorem translate_eq (a : CSTTT.POS04.Assigned.Assignment)
    (h : ExecutionBridge.TranslationReady raw a) (x : Registers Register RegisterValue) :
    ExecutionBridge.translate raw a h x = x := by
  funext k
  exact Option.some.inj (ExecutionBridge.translate_equation raw a h x k).symm

/-- Closed baseline law checked for the actual raw programs. No baseline
0/1 route readout or positive endpoint label is a generic gate. -/
theorem canonical_laws
    (hs : ExecutionFrontier.Ready raw.source canonical)
    (ht : ExecutionFrontier.Ready raw.target canonical) :
    ExecutionBridge.Laws raw canonical hs ht (translation_ready canonical) := by
  constructor
  · rfl
  · rfl
  · change POS04ReceiverFrontier.acquisition.histories.read canonical = POS04ExecutionFrontier.acquisition.histories.read canonical
    rw [POS04ReceiverFrontier.word_equation canonical (canonical_complete _),
      POS04ExecutionFrontier.word_eq canonical (canonical_complete _)]
    apply congrArg some
    funext r
    cases r <;> decide +kernel
  · intro r
    rw [translate_eq]
    change ExecutionFrontier.initial POS04ExecutionFrontier.raw canonical _ r =
      ExecutionFrontier.initial POS04ReceiverFrontier.raw canonical _ r
    rw [POS04ExecutionFrontier.initial_eq canonical (canonical_complete _),
      POS04ReceiverFrontier.initial_equation canonical (canonical_complete _)]
    cases r <;> rfl
  · intro x hx da o
    rw [translate_eq]
    change RegisterFuture.weight (POS04RegisterFuture.raw .target) canonical _ x da o =
      RegisterFuture.weight (POS04RegisterFuture.raw .source) canonical _ x da o
    rw [← encode_decode x,POS04RegisterFuture.weight_eq canonical .target (canonical_complete _),
      POS04RegisterFuture.weight_eq canonical .source (canonical_complete _)]
    rfl
  · intro x hx d hd act ha o ho
    rw [translate_eq,translate_eq]
    change AcquisitionExecution.update POS04ExecutionFrontier.acquisition canonical _ x d act o =
      AcquisitionExecution.update POS04ReceiverFrontier.acquisition canonical _ x d act o
    rw [← encode_decode x,POS04ExecutionFrontier.actual_update canonical (canonical_complete _),
      POS04ReceiverFrontier.actual_update canonical (canonical_complete _)]
    rfl
  · intro x hx
    rw [translate_eq]
    change mapSnapshotReadout acquisitionSnapshotMaps
      (RegisterFuture.observation (POS04RegisterFuture.raw .source) canonical _ x) =
      RegisterFuture.observation (POS04RegisterFuture.raw .target) canonical _ x
    rw [← encode_decode x,POS04RegisterFuture.observation_eq canonical .source (canonical_complete _),
      POS04RegisterFuture.observation_eq canonical .target (canonical_complete _)]
    rfl

theorem positive : ExecutionBridge.Valid raw canonical :=
  ⟨POS04ExecutionFrontier.positive,POS04ReceiverFrontier.positive,
    translation_ready canonical,canonical_laws⟩

/-- A genuine different-past witness, with the target equality DERIVED by
the generic executed-map theorem. Only the source equality is computed here. -/
theorem different_pasts_same_predictive_image :
    acquisitionHistory canonical .source .a ≠ acquisitionHistory canonical .source .b ∧
    (ExecutionFrontier.observation raw.source canonical POS04ExecutionFrontier.canonical_ready (.a,2)).predictive =
      (ExecutionFrontier.observation raw.source canonical POS04ExecutionFrontier.canonical_ready (.b,2)).predictive ∧
    (ExecutionFrontier.observation raw.target canonical POS04ReceiverFrontier.canonical_ready (.a,2)).predictive =
      (ExecutionFrontier.observation raw.target canonical POS04ReceiverFrontier.canonical_ready (.b,2)).predictive := by
  have hs : (ExecutionFrontier.observation raw.source canonical POS04ExecutionFrontier.canonical_ready (.a,2)).predictive =
      (ExecutionFrontier.observation raw.source canonical POS04ExecutionFrontier.canonical_ready (.b,2)).predictive := by
    change (ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical _ (.a,2)).predictive =
      (ExecutionFrontier.observation POS04ExecutionFrontier.raw canonical _ (.b,2)).predictive
    rw [POS04ExecutedCorridor.snapshot_equation canonical (canonical_complete _),
      POS04ExecutedCorridor.snapshot_equation canonical (canonical_complete _)]
    decide +kernel
  refine ⟨by decide,hs,?_⟩
  exact ExecutionBridge.representative_independence raw canonical positive
    POS04ExecutionFrontier.canonical_ready POS04ReceiverFrontier.canonical_ready
    ⟨(.a,2),by decide⟩ ⟨(.b,2),by decide⟩ hs

/-- A partial-assignment characterization of THIS execution gate, not a claim
of equivalence with the not-yet-extracted final LineageLane. -/
theorem valid_iff (a : CSTTT.POS04.Assigned.Assignment) :
    ExecutionBridge.Valid raw a ↔
      ExecutionFrontier.Valid POS04ExecutionFrontier.raw a ∧
      ExecutionFrontier.Valid POS04ReceiverFrontier.raw a ∧
      ∀ hs ht, ExecutionBridge.Laws raw a hs ht (translation_ready a) := by
  constructor
  · rintro ⟨hs,ht,hm,hl⟩; exact ⟨hs,ht,hl⟩
  · rintro ⟨hs,ht,hl⟩; exact ⟨hs,ht,translation_ready a,hl⟩

theorem missing_atomic_no_bridge (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ ExecutionBridge.Valid raw (Assigned.put a .eventTable none) := by
  apply ExecutionBridge.missing_atomic_rejected
  simp [raw,POS04ExecutionFrontier.raw,POS04ExecutionFrontier.acquisition,
    POS04ExecutionFrontier.eventView,CellView.read]

/-- Sensitivity controls for the execution link, not new model declarations.
The source and receiver remain fixed while only target dynamics/readout change. -/
def uniformRows : List (Ambient × Rat) := ambientStates.map (fun o => (o,(1 : Rat)/ambientStates.length))
def uniformTarget := {raw.target with acquisition := {raw.target.acquisition with
  execution := {raw.target.acquisition.execution with row := .literal uniformRows}}}
def uniformBridge := {raw with target := uniformTarget}

theorem uniform_target_ready : ExecutionFrontier.Ready uniformTarget canonical := by
  refine ⟨?_,?_,?_,?_⟩
  · refine ⟨POS04ReceiverFrontier.canonical_ready.1.1,POS04ReceiverFrontier.canonical_ready.1.2.1,
      ?_,POS04ReceiverFrontier.canonical_ready.1.2.2.2.1,POS04ReceiverFrontier.canonical_ready.1.2.2.2.2⟩
    intro k hk; simp [uniformTarget,Expr.dependencies] at hk
  · intro k hk; simp [uniformTarget,ExecutionFrontier.temporal,Expr.dependencies] at hk
  · exact POS04ReceiverFrontier.canonical_ready.2.2.1
  · exact POS04ReceiverFrontier.canonical_ready.2.2.2

theorem uniform_weight (x : Registers Register RegisterValue) (da : LaneDisturbance × Action) :
    RegisterFuture.weight (ExecutionFrontier.temporal uniformTarget) canonical uniform_target_ready.2
      x da (.inK .p2w1) = (1 : Rat)/12 := by
  have he := RegisterFuture.row_eq (ExecutionFrontier.temporal uniformTarget) canonical uniform_target_ready.2 x da
  change some uniformRows = some _ at he
  have hr := Option.some.inj he
  unfold RegisterFuture.weight
  rw [← hr]
  decide +kernel

/-- Uniform substitution fails the branch-weight equation itself, even before
a target audit/bisimulation or corridor check is consulted. -/
theorem uniform_substitution_rejected : ¬ ExecutionBridge.Valid uniformBridge canonical := by
  let x := ExecutionFrontier.initial POS04ExecutionFrontier.raw canonical POS04ExecutionFrontier.canonical_ready .a
  have hx : ExecutionFrontier.Closure POS04ExecutionFrontier.raw canonical POS04ExecutionFrontier.canonical_ready x :=
    FutureClosure.root _ (List.mem_map.mpr ⟨(.a,1),by decide,rfl⟩)
  have hm : ExecutionBridge.TranslationReady uniformBridge canonical := translation_ready canonical
  apply ExecutionBridge.weight_mismatch_rejected uniformBridge canonical
    POS04ExecutionFrontier.canonical_ready uniform_target_ready hm x hx (.nominal,.cw) (.inK .p2w1)
  have he : ExecutionBridge.translate uniformBridge canonical hm x = x := translate_eq canonical hm x
  rw [he]
  change RegisterFuture.weight (ExecutionFrontier.temporal uniformTarget) canonical uniform_target_ready.2 x _ _ ≠ _
  rw [uniform_weight]
  unfold x
  rw [POS04ExecutionFrontier.initial_eq canonical (canonical_complete _)]
  change (1 : Rat)/12 ≠ RegisterFuture.weight (POS04RegisterFuture.raw .source) canonical _
    (encode (acquisitionInitialRun canonical .source .a)) (.nominal,.cw) (.inK .p2w1)
  rw [POS04RegisterFuture.weight_eq canonical .source (canonical_complete _)]
  decide +kernel

def stationaryTarget := {raw.target with acquisition := {raw.target.acquisition with
  execution := {raw.target.acquisition.execution with program := fun k => .register k}}}
def stationaryBridge := {raw with target := stationaryTarget}

theorem stationary_target_ready : ExecutionFrontier.Ready stationaryTarget canonical := by
  refine ⟨?_,POS04ReceiverFrontier.canonical_ready.2.1,?_,POS04ReceiverFrontier.canonical_ready.2.2.2⟩
  · refine ⟨POS04ReceiverFrontier.canonical_ready.1.1,POS04ReceiverFrontier.canonical_ready.1.2.1,
      POS04ReceiverFrontier.canonical_ready.1.2.2.1,?_,POS04ReceiverFrontier.canonical_ready.1.2.2.2.2⟩
    intro k j hj; simp [stationaryTarget,Expr.dependencies] at hj
  · intro k j hj; simp [stationaryTarget,ExecutionFrontier.temporal,Expr.dependencies] at hj

theorem stationary_update (x : Registers Register RegisterValue) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    AcquisitionExecution.update stationaryTarget.acquisition canonical stationary_target_ready.1 x d act o = x := by
  funext k
  exact Option.some.inj ((checked_execute_eq stationaryTarget.acquisition.execution.program canonical
    stationary_target_ready.1.2.2.2.1 x (d,act,o) k).symm)

/-- Identity successor substitution is rejected by the shared-update law,
not just because the displayed final counter happened to change. -/
theorem stationary_substitution_rejected : ¬ ExecutionBridge.Valid stationaryBridge canonical := by
  let x := ExecutionFrontier.initial POS04ExecutionFrontier.raw canonical POS04ExecutionFrontier.canonical_ready .a
  have hx : ExecutionFrontier.Closure POS04ExecutionFrontier.raw canonical POS04ExecutionFrontier.canonical_ready x :=
    FutureClosure.root _ (List.mem_map.mpr ⟨(.a,1),by decide,rfl⟩)
  have hm : ExecutionBridge.TranslationReady stationaryBridge canonical := translation_ready canonical
  apply ExecutionBridge.successor_mismatch_rejected stationaryBridge canonical
    POS04ExecutionFrontier.canonical_ready stationary_target_ready hm x hx
    .nominal (by decide) .cw (by decide) (.inK .p2w1) (by decide)
  have he : ∀ y, ExecutionBridge.translate stationaryBridge canonical hm y = y := translate_eq canonical hm
  rw [he,he]
  change AcquisitionExecution.update POS04ExecutionFrontier.acquisition canonical _ x .nominal .cw (.inK .p2w1) ≠
    AcquisitionExecution.update stationaryTarget.acquisition canonical stationary_target_ready.1 x .nominal .cw (.inK .p2w1)
  rw [stationary_update]
  intro bad
  have hc := congrFun bad Register.counter
  unfold x at hc
  rw [POS04ExecutionFrontier.initial_eq canonical (canonical_complete _),
    POS04ExecutionFrontier.actual_update canonical (canonical_complete _)] at hc
  change (1 : Nat) = 0 at hc
  contradiction

end CSTTT.TargetTheory.GenericHandoff.POS04ExecutionBridge
