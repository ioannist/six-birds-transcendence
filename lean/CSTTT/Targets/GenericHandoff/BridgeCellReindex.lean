import CSTTT.Targets.GenericHandoff.FrontierCellReindex

/-! Both raw execution frames, the actual register translation and its seven
laws move to a common primitive namespace. All gates remain exact on arbitrary
partial assignments, and the actual semantic readout is preserved separately. -/
namespace CSTTT.TargetTheory.GenericHandoff.BridgeCellReindex
open RegisterInterpreter CellReindex CSTTT.TransportTheory
variable {SC TC S T D A O P Q Residue Maintenance Stage Id History RouteId : Type}
  {SV : SC → Type} {TV : TC → Type} {SRV : S → Type} {TRV : T → Type}

def raw (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionBridge.Raw SC SV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId) :
    ExecutionBridge.Raw TC TV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId :=
  ⟨FrontierCellReindex.raw cell value r.source,FrontierCellReindex.raw cell value r.target,
    fun k => expression cell value (r.translation k),r.maps⟩

theorem translation_ready_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionBridge.Raw SC SV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) :
    ExecutionBridge.TranslationReady (raw cell value r) a ↔
      ExecutionBridge.TranslationReady r (pullback cell value a) :=
  forall_congr' (fun k => CellReindex.ready_iff cell value (r.translation k) a)

theorem translate_equation (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionBridge.Raw SC SV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) (h : ExecutionBridge.TranslationReady (raw cell value r) a)
    (j : ExecutionBridge.TranslationReady r (pullback cell value a)) (run : Registers S SRV) :
    ExecutionBridge.translate (raw cell value r) a h run =
      ExecutionBridge.translate r (pullback cell value a) j run := by
  funext k
  have he := evaluation cell value (r.translation k) a run ()
  change ((raw cell value r).translation k).eval a run () = _ at he
  rw [ExecutionBridge.translate_equation _ a h,ExecutionBridge.translate_equation _ _ j] at he
  exact Option.some.inj he

variable [DecidableEq O] [DecidableEq Stage] [DecidableEq P] [DecidableEq Q]
  [DecidableEq Residue] [DecidableEq Maintenance]

omit [DecidableEq Stage] [DecidableEq P] [DecidableEq Q] [DecidableEq Residue] [DecidableEq Maintenance] in
theorem laws_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionBridge.Raw SC SV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV)
    (hs : ExecutionFrontier.Ready (raw cell value r).source a)
    (ht : ExecutionFrontier.Ready (raw cell value r).target a)
    (hm : ExecutionBridge.TranslationReady (raw cell value r) a)
    (js : ExecutionFrontier.Ready r.source (pullback cell value a))
    (jt : ExecutionFrontier.Ready r.target (pullback cell value a))
    (jm : ExecutionBridge.TranslationReady r (pullback cell value a)) :
    ExecutionBridge.Laws (raw cell value r) a hs ht hm ↔
      ExecutionBridge.Laws r (pullback cell value a) js jt jm := by
  have hi := FrontierCellReindex.initial_equation cell value r.source a hs js
  have hj := FrontierCellReindex.initial_equation cell value r.target a ht jt
  have hc := FrontierCellReindex.closure_iff cell value r.source a hs js
  have hw := FrontierCellReindex.weight_equation cell value r.source a hs js
  have hz := FrontierCellReindex.weight_equation cell value r.target a ht jt
  have hu := FrontierCellReindex.update_equation cell value r.source a hs js
  have hv := FrontierCellReindex.update_equation cell value r.target a ht jt
  have ho := FrontierCellReindex.temporal_observation_equation cell value r.source a hs js
  have hp := FrontierCellReindex.temporal_observation_equation cell value r.target a ht jt
  have hmapped := translate_equation cell value r a hm jm
  constructor
  · intro h
    constructor
    · exact h.audit
    · exact h.outcomes
    · simpa only [raw,FrontierCellReindex.raw,AcquisitionCellReindex.raw,view_equation] using h.words
    · intro hist
      have he := h.initial hist
      change ExecutionBridge.translate (raw cell value r) a hm (ExecutionFrontier.initial (FrontierCellReindex.raw cell value r.source) a hs hist) =
        ExecutionFrontier.initial (FrontierCellReindex.raw cell value r.target) a ht hist at he
      simpa only [hmapped,hi,hj] using he
    · intro run hr da o
      have he := h.rows run ((hc run).mpr hr) da o
      change RegisterFuture.weight (ExecutionFrontier.temporal (FrontierCellReindex.raw cell value r.target)) a ht.2
        (ExecutionBridge.translate (raw cell value r) a hm run) da o =
        RegisterFuture.weight (ExecutionFrontier.temporal (FrontierCellReindex.raw cell value r.source)) a hs.2 run da o at he
      simpa only [hmapped,hw,hz] using he
    · intro run hr d hd act ha o ho'
      have he := h.successor run ((hc run).mpr hr) d hd act ha o ho'
      change ExecutionBridge.translate (raw cell value r) a hm
        (AcquisitionExecution.update (FrontierCellReindex.raw cell value r.source).acquisition a hs.1 run d act o) =
        AcquisitionExecution.update (FrontierCellReindex.raw cell value r.target).acquisition a ht.1
          (ExecutionBridge.translate (raw cell value r) a hm run) d act o at he
      simpa only [hmapped,hu,hv] using he
    · intro run hr
      have he := h.observation run ((hc run).mpr hr)
      change mapSnapshotReadout r.maps
        (RegisterFuture.observation (ExecutionFrontier.temporal (FrontierCellReindex.raw cell value r.source)) a hs.2 run) =
        RegisterFuture.observation (ExecutionFrontier.temporal (FrontierCellReindex.raw cell value r.target)) a ht.2
          (ExecutionBridge.translate (raw cell value r) a hm run) at he
      simpa only [hmapped,ho,hp] using he
  · intro h
    constructor
    · exact h.audit
    · exact h.outcomes
    · simpa only [raw,FrontierCellReindex.raw,AcquisitionCellReindex.raw,view_equation] using h.words
    · intro hist
      change ExecutionBridge.translate (raw cell value r) a hm (ExecutionFrontier.initial (FrontierCellReindex.raw cell value r.source) a hs hist) =
        ExecutionFrontier.initial (FrontierCellReindex.raw cell value r.target) a ht hist
      simpa only [hmapped,hi,hj] using h.initial hist
    · intro run hr da o
      change RegisterFuture.weight (ExecutionFrontier.temporal (FrontierCellReindex.raw cell value r.target)) a ht.2
        (ExecutionBridge.translate (raw cell value r) a hm run) da o =
        RegisterFuture.weight (ExecutionFrontier.temporal (FrontierCellReindex.raw cell value r.source)) a hs.2 run da o
      simpa only [hmapped,hw,hz] using h.rows run ((hc run).mp hr) da o
    · intro run hr d hd act ha o ho'
      change ExecutionBridge.translate (raw cell value r) a hm
        (AcquisitionExecution.update (FrontierCellReindex.raw cell value r.source).acquisition a hs.1 run d act o) =
        AcquisitionExecution.update (FrontierCellReindex.raw cell value r.target).acquisition a ht.1
          (ExecutionBridge.translate (raw cell value r) a hm run) d act o
      simpa only [hmapped,hu,hv] using h.successor run ((hc run).mp hr) d hd act ha o ho'
    · intro run hr
      change mapSnapshotReadout r.maps
        (RegisterFuture.observation (ExecutionFrontier.temporal (FrontierCellReindex.raw cell value r.source)) a hs.2 run) =
        RegisterFuture.observation (ExecutionFrontier.temporal (FrontierCellReindex.raw cell value r.target)) a ht.2
          (ExecutionBridge.translate (raw cell value r) a hm run)
      simpa only [hmapped,ho,hp] using h.observation run ((hc run).mp hr)

omit [DecidableEq Stage] [DecidableEq P] [DecidableEq Q] [DecidableEq Residue] [DecidableEq Maintenance] in
theorem law_family_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionBridge.Raw SC SV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) :
    (∃ hm : ExecutionBridge.TranslationReady (raw cell value r) a,
      ∀ hs ht, ExecutionBridge.Laws (raw cell value r) a hs ht hm) ↔
    (∃ jm : ExecutionBridge.TranslationReady r (pullback cell value a),
      ∀ js jt, ExecutionBridge.Laws r (pullback cell value a) js jt jm) := by
  constructor
  · rintro ⟨hm,hl⟩
    let jm := (translation_ready_iff cell value r a).mp hm
    refine ⟨jm,?_⟩
    intro js jt
    let hs := (FrontierCellReindex.ready_iff cell value r.source a).mpr js
    let ht := (FrontierCellReindex.ready_iff cell value r.target a).mpr jt
    exact (laws_iff cell value r a hs ht hm js jt jm).mp (hl hs ht)
  · rintro ⟨jm,hl⟩
    let hm := (translation_ready_iff cell value r a).mpr jm
    refine ⟨hm,?_⟩
    intro hs ht
    let js := (FrontierCellReindex.ready_iff cell value r.source a).mp hs
    let jt := (FrontierCellReindex.ready_iff cell value r.target a).mp ht
    exact (laws_iff cell value r a hs ht hm js jt jm).mpr (hl js jt)

theorem valid_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionBridge.Raw SC SV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) :
    ExecutionBridge.Valid (raw cell value r) a ↔ ExecutionBridge.Valid r (pullback cell value a) := by
  unfold ExecutionBridge.Valid
  change ExecutionFrontier.Valid (FrontierCellReindex.raw cell value r.source) a ∧
    ExecutionFrontier.Valid (FrontierCellReindex.raw cell value r.target) a ∧ _ ↔ _
  rw [FrontierCellReindex.valid_iff,FrontierCellReindex.valid_iff,law_family_iff]

theorem semantic_iff (cell : SC → TC) (value : (k : SC) → TV (cell k) → SV k)
    (r : ExecutionBridge.Raw SC SV S T SRV TRV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment TC TV) :
    ExecutionBridge.SemanticReadout (raw cell value r) a ↔
      ExecutionBridge.SemanticReadout r (pullback cell value a) := by
  unfold ExecutionBridge.SemanticReadout
  change ExecutionFrontier.SemanticReadout (FrontierCellReindex.raw cell value r.source) a ∧
    ExecutionFrontier.SemanticReadout (FrontierCellReindex.raw cell value r.target) a ∧ _ ↔ _
  rw [FrontierCellReindex.semantic_iff,FrontierCellReindex.semantic_iff,law_family_iff]

end CSTTT.TargetTheory.GenericHandoff.BridgeCellReindex
