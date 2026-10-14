import CSTTT.Targets.GenericHandoff.ExactFutureReindex
import CSTTT.Targets.GenericHandoff.SemanticExecutionBridge
import CSTTT.Targets.GenericHandoff.POS04ExecutionBridge

/-! Semantic adapter for POS-04's actual execution, not its bisimulation gate.
The equivalences retain all run states and all finite words. Source closure,
initial runs, target runs, probabilities and eight-field observations are
computed from the shared assignment; no derived execution is a raw argument.
Whole-lineage aggregation and the final RawHandoff binding remain separate.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04SemanticExecution
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TransportTheory
open RegisterInterpreter POS04RegisterDynamics
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem observation_embedding_injective : Function.Injective c6ObservationToBridge := by
  intro x y h
  cases x with
  | mk p n t g r s m o =>
    cases y with
    | mk p' n' t' g' r' s' m' o' =>
      simp only [c6ObservationToBridge,TemporalSnapshotReadout.mk.injEq] at h
      simp only [C6Observation.mk.injEq]
      exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
        h.2.2.2.2.2.2.1,tag_carrier_id_injective _ _ h.2.2.2.2.2.2.2⟩

/-- Exact semantic equivalence, rather than merely canonical truth or the
forward implication from C6Accept. No closure restriction is made. -/
theorem full_future_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag)
    (hc : Complete (temporalDependencies t) a) :
    FullFutureSufficient (POS04RegisterFuture.Model a t hc) ↔
      FullFutureSufficient (actualFuture6 a t) := by
  apply FutureReindex.sufficient_iff (actualFuture6 a t) (POS04RegisterFuture.Model a t hc)
    decodeRun Prod.snd c6ObservationToBridge
    (fun x => ⟨encode x,decode_encode x⟩) (fun act => ⟨(.nominal,act),rfl⟩)
    (fun _ _ h => observation_embedding_injective h) rfl
    (fun x => by simpa only [encode_decode] using POS04RegisterFuture.observation_eq a t hc (decodeRun x))
    (fun x da o => by simpa only [encode_decode] using POS04RegisterFuture.weight_eq a t hc (decodeRun x) da.1 da.2 o)
    (fun x da o => by simpa only [encode_decode,decode_encode] using
      (congrArg decodeRun (POS04RegisterFuture.next_eq a t hc (decodeRun x) da.1 da.2 o)))
  intro x y
  rw [← encode_decode x,← encode_decode y,POS04RegisterFuture.code_eq,POS04RegisterFuture.code_eq]
  exact ⟨fun h => c6_code_to_bridge_injective _ _ h,fun h => congrArg c6CodeToBridge h⟩

theorem temporal_ready_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    RegisterFuture.RawReady (POS04RegisterFuture.raw t) a ↔ Complete (temporalDependencies t) a := by
  constructor
  · intro h k hk
    simp only [temporalDependencies,coreDependencies,List.mem_append,List.mem_cons,
      List.not_mem_nil,or_false] at hk
    rcases hk with (hk | hk | hk) | (hk | hk | hk | hk | hk | hk)
    all_goals subst k
    all_goals solve
      | (apply h.1; simp [POS04RegisterFuture.raw,POS04RegisterFuture.enabledRow,rowExpression,Expr.dependencies])
      | (apply h.2.1 .ticks; simp [POS04RegisterFuture.raw,program,Expr.dependencies])
      | (apply h.2.2; simp [POS04RegisterFuture.raw,readouts,RegisterFuture.Readouts.dependencies,
          predictiveExpression,writerExpression,recordExpression,Expr.dependencies])
  · exact POS04RegisterFuture.ready a t

theorem source_ready_iff (a : CSTTT.POS04.Assigned.Assignment) :
    ExecutionFrontier.Ready POS04ExecutionFrontier.raw a ↔ Complete POS04ExecutionFrontier.dependencies a := by
  constructor
  · intro h k hk
    rcases List.mem_append.mp hk with ht | he
    · exact (temporal_ready_iff a .source).mp h.2 k ht
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with he | he | he | he | he | he
      all_goals subst k
      all_goals apply h.1.1
      all_goals simp [POS04ExecutionFrontier.raw,POS04ExecutionFrontier.acquisition,
        AcquisitionExecution.Raw.dependencies,POS04ExecutionFrontier.wordExpr,
        POS04ExecutionFrontier.pathExpr,POS04ExecutionFrontier.routeView,
        POS04ExecutionFrontier.eventView,POS04ExecutionFrontier.receiverView,
        StaticView.dependencies,Expr.dependencies]
  · exact POS04ExecutionFrontier.ready a

theorem target_ready_iff (a : CSTTT.POS04.Assigned.Assignment) :
    ExecutionFrontier.Ready POS04ReceiverFrontier.raw a ↔ Complete POS04ReceiverFrontier.dependencies a := by
  constructor
  · intro h k hk
    rcases List.mem_append.mp hk with ht | he
    · exact (temporal_ready_iff a .target).mp h.2 k ht
    · simp only [List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with he | he | he | he | he | he
      all_goals subst k
      all_goals apply h.1.1
      all_goals simp [POS04ReceiverFrontier.raw,POS04ReceiverFrontier.acquisition,
        POS04ExecutionFrontier.acquisition,AcquisitionExecution.Raw.dependencies,
        POS04ReceiverFrontier.wordExpr,POS04ReceiverFrontier.pathExpr,
        POS04ExecutionFrontier.routeView,POS04ExecutionFrontier.eventView,
        POS04ExecutionFrontier.receiverView,StaticView.dependencies,Expr.dependencies]
  · exact POS04ReceiverFrontier.ready a

def roots (a : CSTTT.POS04.Assigned.Assignment) : List Run6 :=
  POS04ExecutionFrontier.audit.map (fun i => acquisitionInitialRun a .source i.1)

def dynamics (a : CSTTT.POS04.Assigned.Assignment) : RawFutureDynamics Run6 (LaneDisturbance × Action) Ambient :=
  ⟨ambientStates,(fun x da o => actualWeight6 (runInputs6 a .source) x da.2 o),
    (fun x da o => actualUpdate6 (runInputs6 a .source) x da.2 o)⟩

abbrev Closure (a : CSTTT.POS04.Assigned.Assignment) := FutureClosure (dynamics a) (roots a)

theorem roots_eq (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete POS04ExecutionFrontier.dependencies a) :
    ExecutionFrontier.roots POS04ExecutionFrontier.raw a (POS04ExecutionFrontier.ready a hc) =
      (roots a).map encode := by
  unfold ExecutionFrontier.roots roots
  simp only [POS04ExecutionFrontier.raw,List.map_map]
  apply List.map_congr_left
  intro i hi
  exact POS04ExecutionFrontier.initial_eq a hc i.1

/-- Both directions cover the ENTIRE computed closure, including every
ambient outcome. No predictive-class representative is selected. -/
theorem closure_iff (a : CSTTT.POS04.Assigned.Assignment)
    (hc : Complete POS04ExecutionFrontier.dependencies a) (x : Run6) :
    ExecutionFrontier.Closure POS04ExecutionFrontier.raw a (POS04ExecutionFrontier.ready a hc) (encode x) ↔
      Closure a x := by
  constructor
  · intro hx
    have hd : ∀ (y : Registers Register RegisterValue),
        ExecutionFrontier.Closure POS04ExecutionFrontier.raw a (POS04ExecutionFrontier.ready a hc) y →
        Closure a (decodeRun y) := by
      intro y hy
      induction hy with
      | root y hm =>
        rw [roots_eq a hc] at hm
        obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hm
        exact FutureClosure.root _ (by simpa only [decode_encode] using hz)
      | @step y _ da o ho ih =>
        have hn := POS04RegisterFuture.next_eq a .source
          (fun k hk => hc k (List.mem_append_left _ hk)) (decodeRun y) da.1 da.2 o
        have hnext : decodeRun (RegisterFuture.next (POS04RegisterFuture.raw .source) a
            (POS04RegisterFuture.ready a .source (fun k hk => hc k (List.mem_append_left _ hk))) y da o) =
            actualUpdate6 (runInputs6 a .source) (decodeRun y) da.2 o := by
          simpa only [encode_decode,decode_encode] using congrArg decodeRun hn
        change Closure a (decodeRun (RegisterFuture.next (POS04RegisterFuture.raw .source) a
          (POS04RegisterFuture.ready a .source (fun k hk => hc k (List.mem_append_left _ hk))) y da o))
        rw [hnext]
        exact FutureClosure.step ih da o ho
    simpa only [decode_encode] using hd (encode x) hx
  · intro hx
    induction hx with
    | root x hm =>
      apply FutureClosure.root
      rw [roots_eq a hc]
      exact List.mem_map.mpr ⟨x,hm,rfl⟩
    | @step x _ da o ho ih =>
      have hs := FutureClosure.step ih da o ho
      change ExecutionFrontier.Closure POS04ExecutionFrontier.raw a (POS04ExecutionFrontier.ready a hc)
        (RegisterFuture.next (POS04RegisterFuture.raw .source) a
          (POS04RegisterFuture.ready a .source (fun k hk => hc k (List.mem_append_left _ hk))) (encode x) da o) at hs
      rw [POS04RegisterFuture.next_eq a .source
        (fun k hk => hc k (List.mem_append_left _ hk))] at hs
      exact hs

def word (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (r : RouteId) :
    List (LaneDisturbance × Action × Ambient) :=
  let path := acquisitionHistory a t r
  (path.zip (path.drop 1)).map (fun e => (.nominal,(runInputs6 a t).base.base.policy e.1,.inK e.2))

/-- Independently stated raw transport equations. Weight/successor/observer
laws cover every future-closure run, not merely the audited roots. -/
def TransportLaws (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  (∀ r, word a .target r = word a .source r) ∧
  (∀ r, acquisitionInitialRun a .source r = acquisitionInitialRun a .target r) ∧
  (∀ x, Closure a x → ∀ act o,
    actualWeight6 (runInputs6 a .target) x act o = actualWeight6 (runInputs6 a .source) x act o) ∧
  (∀ x, Closure a x → ∀ act ∈ actions, ∀ o ∈ ambientStates,
    actualUpdate6 (runInputs6 a .source) x act o = actualUpdate6 (runInputs6 a .target) x act o) ∧
  (∀ x, Closure a x → mapSnapshotReadout acquisitionSnapshotMaps
    (c6ObservationToBridge (observation6 (runInputs6 a .source) .source x)) =
    c6ObservationToBridge (observation6 (runInputs6 a .target) .target x))

theorem transport_laws_iff (a : CSTTT.POS04.Assigned.Assignment)
    (hs : Complete POS04ExecutionFrontier.dependencies a)
    (ht : Complete POS04ReceiverFrontier.dependencies a) :
    ExecutionBridge.Laws POS04ExecutionBridge.raw a (POS04ExecutionFrontier.ready a hs)
      (POS04ReceiverFrontier.ready a ht) (POS04ExecutionBridge.translation_ready a) ↔ TransportLaws a := by
  have sc : Complete (temporalDependencies .source) a := fun k hk => hs k (List.mem_append_left _ hk)
  have tc : Complete (temporalDependencies .target) a := fun k hk => ht k (List.mem_append_left _ hk)
  constructor
  · intro hl
    refine ⟨?_,?_,?_,?_,?_⟩
    · have hw := hl.words
      change POS04ReceiverFrontier.acquisition.histories.read a = POS04ExecutionFrontier.acquisition.histories.read a at hw
      rw [POS04ReceiverFrontier.word_equation a ht,POS04ExecutionFrontier.word_eq a hs] at hw
      exact congrFun (Option.some.inj hw)
    · intro r
      have he := hl.initial r
      rw [POS04ExecutionBridge.translate_eq] at he
      change ExecutionFrontier.initial POS04ExecutionFrontier.raw a _ r =
        ExecutionFrontier.initial POS04ReceiverFrontier.raw a _ r at he
      rw [POS04ExecutionFrontier.initial_eq a hs,POS04ReceiverFrontier.initial_equation a ht] at he
      simpa only [decode_encode] using congrArg decodeRun he
    · intro x hx act o
      have he := hl.rows (encode x) ((closure_iff a hs x).mpr hx) (.nominal,act) o
      rw [POS04ExecutionBridge.translate_eq] at he
      change RegisterFuture.weight (POS04RegisterFuture.raw .target) a _ (encode x) (.nominal,act) o =
        RegisterFuture.weight (POS04RegisterFuture.raw .source) a _ (encode x) (.nominal,act) o at he
      simpa only [POS04RegisterFuture.weight_eq a .target tc,POS04RegisterFuture.weight_eq a .source sc] using he
    · intro x hx act ha o ho
      have he := hl.successor (encode x) ((closure_iff a hs x).mpr hx) .nominal (by decide) act ha o ho
      rw [POS04ExecutionBridge.translate_eq,POS04ExecutionBridge.translate_eq] at he
      change AcquisitionExecution.update POS04ExecutionFrontier.acquisition a _ (encode x) .nominal act o =
        AcquisitionExecution.update POS04ReceiverFrontier.acquisition a _ (encode x) .nominal act o at he
      rw [POS04ExecutionFrontier.actual_update a hs,POS04ReceiverFrontier.actual_update a ht] at he
      simpa only [decode_encode] using congrArg decodeRun he
    · intro x hx
      have he := hl.observation (encode x) ((closure_iff a hs x).mpr hx)
      rw [POS04ExecutionBridge.translate_eq] at he
      change mapSnapshotReadout acquisitionSnapshotMaps (RegisterFuture.observation (POS04RegisterFuture.raw .source) a _ (encode x)) =
        RegisterFuture.observation (POS04RegisterFuture.raw .target) a _ (encode x) at he
      simpa only [POS04RegisterFuture.observation_eq a .source sc,POS04RegisterFuture.observation_eq a .target tc] using he
  · rintro ⟨hw,hi,hr,hn,ho⟩
    constructor
    · rfl
    · rfl
    · change POS04ReceiverFrontier.acquisition.histories.read a = POS04ExecutionFrontier.acquisition.histories.read a
      rw [POS04ReceiverFrontier.word_equation a ht,POS04ExecutionFrontier.word_eq a hs]
      exact congrArg some (funext hw)
    · intro r
      rw [POS04ExecutionBridge.translate_eq]
      change ExecutionFrontier.initial POS04ExecutionFrontier.raw a _ r =
        ExecutionFrontier.initial POS04ReceiverFrontier.raw a _ r
      rw [POS04ExecutionFrontier.initial_eq a hs,POS04ReceiverFrontier.initial_equation a ht,hi]
    · intro x hx da o
      rw [POS04ExecutionBridge.translate_eq]
      have hc := (closure_iff a hs (decodeRun x)).mp (by simpa only [encode_decode] using hx)
      change RegisterFuture.weight (POS04RegisterFuture.raw .target) a _ x da o =
        RegisterFuture.weight (POS04RegisterFuture.raw .source) a _ x da o
      rw [← encode_decode x,POS04RegisterFuture.weight_eq a .target tc,POS04RegisterFuture.weight_eq a .source sc]
      exact hr _ hc da.2 o
    · intro x hx d hd act ha o hout
      rw [POS04ExecutionBridge.translate_eq,POS04ExecutionBridge.translate_eq]
      have hc := (closure_iff a hs (decodeRun x)).mp (by simpa only [encode_decode] using hx)
      change AcquisitionExecution.update POS04ExecutionFrontier.acquisition a _ x d act o =
        AcquisitionExecution.update POS04ReceiverFrontier.acquisition a _ x d act o
      rw [← encode_decode x,POS04ExecutionFrontier.actual_update a hs,POS04ReceiverFrontier.actual_update a ht,hn _ hc act ha o hout]
    · intro x hx
      rw [POS04ExecutionBridge.translate_eq]
      have hc := (closure_iff a hs (decodeRun x)).mp (by simpa only [encode_decode] using hx)
      change mapSnapshotReadout acquisitionSnapshotMaps (RegisterFuture.observation (POS04RegisterFuture.raw .source) a _ x) =
        RegisterFuture.observation (POS04RegisterFuture.raw .target) a _ x
      rw [← encode_decode x,POS04RegisterFuture.observation_eq a .source sc,POS04RegisterFuture.observation_eq a .target tc]
      exact ho _ hc

theorem positive : ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw canonical :=
  ExecutionBridge.semantic_soundness _ _ POS04ExecutionBridge.positive

theorem canonical_transport : TransportLaws canonical :=
  (transport_laws_iff canonical (canonical_complete _) (canonical_complete _)).mp
    (POS04ExecutionBridge.canonical_laws _ _)

/-- Exact whole-execution semantic adapter, for arbitrary partial assignments.
Readiness is inferred from each semantic frame's own raw reads. This is not
an equivalence between the sufficient bisimulation gate and its conclusion. -/
theorem semantic_bridge_iff (a : CSTTT.POS04.Assigned.Assignment) :
    ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw a ↔
      ExecutionFrontier.SemanticReadout POS04ExecutionFrontier.raw a ∧
      ExecutionFrontier.SemanticReadout POS04ReceiverFrontier.raw a ∧ TransportLaws a := by
  constructor
  · rintro ⟨hs,ht,hm,hl⟩
    have cs := (source_ready_iff a).mp hs.choose
    have ct := (target_ready_iff a).mp ht.choose
    exact ⟨hs,ht,(transport_laws_iff a cs ct).mp (hl _ _)⟩
  · rintro ⟨hs,ht,hl⟩
    have cs := (source_ready_iff a).mp hs.choose
    have ct := (target_ready_iff a).mp ht.choose
    refine ⟨hs,ht,POS04ExecutionBridge.translation_ready a,?_⟩
    intro src tgt
    exact (transport_laws_iff a cs ct).mpr hl

theorem missing_atomic_no_readout (a : CSTTT.POS04.Assigned.Assignment) :
    ¬ ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw (put a .eventTable none) := by
  apply ExecutionBridge.missing_atomic_no_semantic_readout
  simp [POS04ExecutionBridge.raw,POS04ExecutionFrontier.raw,POS04ExecutionFrontier.acquisition,
    POS04ExecutionFrontier.eventView,CellView.read]

/-- Every consumed source cell is guarded at the semantic conclusion, with
no incompatible readiness premise on the caller. -/
theorem missing_source_input_no_readout (a : CSTTT.POS04.Assigned.Assignment) (k : Cell)
    (hk : k ∈ POS04ExecutionFrontier.dependencies) :
    ¬ ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw (put a k none) := by
  rintro ⟨hs,_⟩
  have hc := (source_ready_iff _).mp hs.choose
  have hp := hc k hk
  simp at hp

theorem missing_target_input_no_readout (a : CSTTT.POS04.Assigned.Assignment) (k : Cell)
    (hk : k ∈ POS04ReceiverFrontier.dependencies) :
    ¬ ExecutionBridge.SemanticReadout POS04ExecutionBridge.raw (put a k none) := by
  rintro ⟨_,ht,_⟩
  have hc := (target_ready_iff _).mp ht.choose
  have hp := hc k hk
  simp at hp

/-- Direct semantic guard at a genuinely supported endpoint. The cap agrees
at all audit roots, but fails the independent +1 recipe on the next step. -/
theorem capped_progress_no_semantic_readout :
    ¬ ExecutionFrontier.SemanticReadout POS04ExecutionFrontier.cappedProgress canonical := by
  let r : Run6 := ⟨.inK .p1w0,2,2,routeRegister .a,true⟩
  have hs : ExecutionFrontier.snapshot POS04ExecutionFrontier.raw canonical
      POS04ExecutionFrontier.canonical_ready (.a,2) = encode r := by
    unfold ExecutionFrontier.snapshot
    rw [POS04ExecutionFrontier.initial_eq canonical (canonical_complete _)]
    change AcquisitionExecution.foldHistory POS04ExecutionFrontier.acquisition canonical _
      (encode (acquisitionInitialRun canonical .source .a))
      [(.nominal,.cw,.inK .p2w1),(.nominal,.stay,.inK .p1w0)] = encode r
    rw [POS04ExecutedCorridor.fold_equation canonical (canonical_complete _)]
    rfl
  have hx := (ExecutionFrontier.snapshot_execution POS04ExecutionFrontier.raw canonical
    POS04ExecutionFrontier.canonical_ready POS04ExecutionFrontier.canonical_audit (.a,2) (by decide)).2
  rw [hs] at hx
  apply ExecutionFrontier.semantic_field_guard POS04ExecutionFrontier.cappedProgress canonical
    POS04ExecutionFrontier.capped_ready (encode r) hx .nominal (by decide) .cw (by decide)
    (.inK .p2w1) (by decide) .progress
  intro he
  unfold RegisterFuture.FieldLaw at he
  change (Expr.map (fun n : Nat => min n 2) (Expr.register Register.counter)).eval canonical
    (RegisterFuture.next (ExecutionFrontier.temporal POS04ExecutionFrontier.cappedProgress)
      canonical POS04ExecutionFrontier.capped_ready.2 (encode r) (.nominal,.cw) (.inK .p2w1)) () =
      (program .source .counter).eval canonical (encode r) (.nominal,.cw,.inK .p2w1) at he
  rw [show RegisterFuture.next (ExecutionFrontier.temporal POS04ExecutionFrontier.cappedProgress)
      canonical POS04ExecutionFrontier.capped_ready.2 (encode r) (.nominal,.cw) (.inK .p2w1) =
      encode (actualUpdate6 (runInputs6 canonical .source) r .cw (.inK .p2w1)) from
        checked_actual canonical .source (canonical_complete _) r .nominal .cw (.inK .p2w1)] at he
  change some (2 : Nat) = some (3 : Nat) at he
  contradiction

section
open POS04ExecutionBridge

/-- Direct semantic rejection of a uniform weight substitution. -/
theorem uniform_no_semantic_readout : ¬ ExecutionBridge.SemanticReadout uniformBridge canonical := by
  let x := ExecutionFrontier.initial POS04ExecutionFrontier.raw canonical POS04ExecutionFrontier.canonical_ready .a
  have hx : ExecutionFrontier.Closure POS04ExecutionFrontier.raw canonical POS04ExecutionFrontier.canonical_ready x :=
    FutureClosure.root _ (List.mem_map.mpr ⟨(.a,1),by decide,rfl⟩)
  have hm : ExecutionBridge.TranslationReady uniformBridge canonical := translation_ready canonical
  apply ExecutionBridge.semantic_weight_mismatch_rejected uniformBridge canonical
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

/-- Direct semantic rejection of an identity updater substitution. -/
theorem stationary_no_semantic_readout : ¬ ExecutionBridge.SemanticReadout stationaryBridge canonical := by
  let x := ExecutionFrontier.initial POS04ExecutionFrontier.raw canonical POS04ExecutionFrontier.canonical_ready .a
  have hx : ExecutionFrontier.Closure POS04ExecutionFrontier.raw canonical POS04ExecutionFrontier.canonical_ready x :=
    FutureClosure.root _ (List.mem_map.mpr ⟨(.a,1),by decide,rfl⟩)
  have hm : ExecutionBridge.TranslationReady stationaryBridge canonical := translation_ready canonical
  apply ExecutionBridge.semantic_successor_mismatch_rejected stationaryBridge canonical
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

end

end CSTTT.TargetTheory.GenericHandoff.POS04SemanticExecution
