import CSTTT.Targets.GenericHandoff.ExecutionBridge

/-! Semantic execution readouts for the complete lineage lane.
All futures, observations, closures, roots and snapshots are defined from the
raw instructions. The readout requires actual realized history execution,
full-interface ALL-state/ALL-word sufficiency, closure-wide readout laws and
actual subprobability rows. It does not require a particular bisimulation
certifier. The execution gate implies the readout, not conversely.
-/
namespace CSTTT.TargetTheory.GenericHandoff.ExecutionFrontier
open RegisterInterpreter CSTTT.TransportTheory
variable {Cell R D A O P Residue Maintenance Stage Id History RouteId : Type}
  {Value : Cell → Type} {RV : R → Type}
  [DecidableEq O] [DecidableEq Stage] [DecidableEq P]
  [DecidableEq Residue] [DecidableEq Maintenance]

def SemanticReadout
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) : Prop :=
  ∃ h : Ready raw a, AuditCheck raw a h ∧
    AcquisitionExecution.DomainCheck raw.schema raw.acquisition ∧ ExecutionDomain raw ∧ PathsAvailable raw a ∧
    FullFutureSufficient (RegisterFuture.future (temporal raw) a h.2) ∧
    RegisterFuture.ReadoutLawGate (temporal raw) raw.recipes a h.2 (roots raw a h) ∧ RowLawGate raw a h

theorem semantic_soundness
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Valid raw a) : SemanticReadout raw a := by
  obtain ⟨hr,ha,hd,he,hp,hb,hl,hrows⟩ := h
  exact ⟨hr,ha,hd,he,hp,FutureLumping.all_words _ hb,hl,hrows⟩

theorem semantic_snapshot
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hv : SemanticReadout raw a) :
    ∃ h : Ready raw a,
      FullFutureSufficient (RegisterFuture.future (temporal raw) a h.2) ∧
      RegisterFuture.ReadoutLawGate (temporal raw) raw.recipes a h.2 (roots raw a h) ∧
      RowLawGate raw a h ∧
      ∀ i : Audited raw.audit,
        Closure raw a h (snapshot raw a h i.val) ∧
        (frozen raw a h i).predictiveNow.futureSufficient ∧
        decodeFrozenSnapshot raw.audit (observation raw a h) (frozen raw a h i) = observation raw a h i.val := by
  obtain ⟨h,ha,_,_,_,hf,hl,hr⟩ := hv
  exact ⟨h,hf,hl,hr,fun i => ⟨(snapshot_execution raw a h ha i.val i.property).2,hf,rfl⟩⟩

theorem missing_atomic_no_semantic_readout
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hm : raw.acquisition.events.read a = none) :
    ¬ SemanticReadout raw a := by
  rintro ⟨_,_,_,_,hpaths,_⟩
  obtain ⟨_,_,_,_,_,he,_⟩ := hpaths
  rw [hm] at he
  contradiction

/-- A broken raw readout law refutes the semantic result itself. The field
parameter ranges over all nine reads, including writer and owner. -/
theorem semantic_field_guard
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (x : Registers R RV) (hx : Closure raw a h x)
    (d : D) (hd : d ∈ raw.acquisition.execution.disturbances)
    (act : A) (ha : act ∈ raw.acquisition.execution.actions)
    (o : O) (ho : o ∈ raw.acquisition.execution.outcomes) (f : RegisterFuture.Field)
    (bad : ¬ RegisterFuture.FieldLaw (temporal raw) raw.recipes a h.2 x (d,act) o f) :
    ¬ SemanticReadout raw a := by
  rintro ⟨h',_,_,_,_,_,hl,_⟩
  exact RegisterFuture.field_guard (temporal raw) raw.recipes a h.2 (roots raw a h)
    x hx d hd act ha o ho f bad hl

theorem semantic_nonadvancing_guard
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (x : Registers R RV) (hx : Closure raw a h x)
    (d : D) (hd : d ∈ raw.acquisition.execution.disturbances)
    (act : A) (ha : act ∈ raw.acquisition.execution.actions)
    (o : O) (ho : o ∈ raw.acquisition.execution.outcomes)
    (supported : RegisterFuture.weight (temporal raw) a h.2 x (d,act) o > 0)
    (bad : ¬ RegisterFuture.PositiveRecipes (temporal raw) raw.recipes a h.2 x (d,act) o) :
    ¬ SemanticReadout raw a := by
  rintro ⟨h',_,_,_,_,_,hl,_⟩
  exact bad (((hl.2.2.2.2.2.1 x hx d hd act ha o ho).2) supported)

theorem semantic_unavailable_receiver_guard
    (raw : Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (input : AcquisitionExecution.Receiver)
    (hr : raw.acquisition.receiver.read a = some input)
    (field : AcquisitionExecution.ActivationField)
    (bad : AcquisitionExecution.activationField input field = false) : ¬ SemanticReadout raw a := by
  rintro ⟨_,audit,_,_,hpaths,_⟩
  obtain ⟨i⟩ := audited_nonempty raw.audit audit.1
  obtain ⟨routes,events,realized,receiver,_,_,_,hi,hp⟩ := hpaths
  have he := Option.some.inj (hi.symm.trans hr)
  subst receiver
  have active := (hp i.val i.property).2.2.2
  have ht := AcquisitionExecution.activated_fields input events realized _ active field
  rw [bad] at ht
  contradiction

end CSTTT.TargetTheory.GenericHandoff.ExecutionFrontier

namespace CSTTT.TargetTheory.GenericHandoff.ExecutionBridge
open RegisterInterpreter CSTTT.TransportTheory
variable {Cell S T D A O P Q Residue Maintenance Stage Id History RouteId : Type}
  {Value : Cell → Type} {SV : S → Type} {TV : T → Type}
  [DecidableEq O] [DecidableEq Stage] [DecidableEq P] [DecidableEq Q]
  [DecidableEq Residue] [DecidableEq Maintenance]

/-- Complete semantic transport. Raw initial/history, weight, successor and
eight-field equations range over the actual whole source closure. The own
future/readout obligations of BOTH carriers are retained separately. -/
def SemanticReadout
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) : Prop :=
  ExecutionFrontier.SemanticReadout raw.source a ∧ ExecutionFrontier.SemanticReadout raw.target a ∧
    ∃ hm : TranslationReady raw a, ∀ hs ht, Laws raw a hs ht hm

theorem semantic_soundness
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hv : Valid raw a) : SemanticReadout raw a :=
  ⟨ExecutionFrontier.semantic_soundness raw.source a hv.1,
    ExecutionFrontier.semantic_soundness raw.target a hv.2.1,hv.2.2⟩

/-- Every field of the frozen signature, with futures about the defined real
dynamics. Finite snapshot images encode the realized unbounded values exactly. -/
theorem semantic_frozen_transport
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hv : SemanticReadout raw a) :
    ∃ hs : ExecutionFrontier.Ready raw.source a, ∃ ht : ExecutionFrontier.Ready raw.target a,
      ∃ _hm : TranslationReady raw a,
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal raw.source) a hs.2) ∧
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal raw.target) a ht.2) ∧
      ∃ hc : SnapshotMapCheck raw.source.audit (ExecutionFrontier.observation raw.source a hs)
          (ExecutionFrontier.observation raw.target a ht) raw.maps,
        ∀ i : Audited raw.source.audit,
          transportFrozenSnapshot raw.source.audit (ExecutionFrontier.observation raw.source a hs)
            (ExecutionFrontier.observation raw.target a ht) raw.maps hc
            (ExecutionFrontier.frozen raw.source a hs i) =
          frozenSnapshot (RegisterFuture.future (ExecutionFrontier.temporal raw.target) a ht.2)
            raw.source.audit (ExecutionFrontier.observation raw.target a ht) i := by
  obtain ⟨hs,ha,_,_,_,hsource,_,_⟩ := hv.1
  obtain ⟨ht,_,_,_,_,hft,_,_⟩ := hv.2.1
  obtain ⟨hm,hl⟩ := hv.2.2
  have hc := snapshot_map_check raw a hs ht hm (hl hs ht) ha
  refine ⟨hs,ht,hm,hsource,hft,hc,?_⟩
  intro i
  have he := frozen_snapshot_transport (RegisterFuture.future (ExecutionFrontier.temporal raw.source) a hs.2)
    raw.source.audit _ _ raw.maps hc i
  change transportFrozenSnapshot _ _ _ _ _ (frozenSnapshot _ _ _ _) = _
  rw [he]
  have hp : FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal raw.source) a hs.2) =
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal raw.target) a ht.2) :=
    propext ⟨fun _ => hft,fun _ => hsource⟩
  simp only [frozenSnapshot,hp,eq_self]

theorem semantic_representative_independence
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hv : SemanticReadout raw a)
    (hs : ExecutionFrontier.Ready raw.source a) (ht : ExecutionFrontier.Ready raw.target a)
    (i j : Audited raw.source.audit)
    (same : (ExecutionFrontier.observation raw.source a hs i.val).predictive =
      (ExecutionFrontier.observation raw.source a hs j.val).predictive) :
    (ExecutionFrontier.observation raw.target a ht i.val).predictive =
      (ExecutionFrontier.observation raw.target a ht j.val).predictive := by
  obtain ⟨_,ha,_⟩ := hv.1
  obtain ⟨hm,hl⟩ := hv.2.2
  have hc := snapshot_map_check raw a hs ht hm (hl hs ht) ha
  have hi := congrArg TemporalSnapshotReadout.predictive (hc i.val i.property)
  have hj := congrArg TemporalSnapshotReadout.predictive (hc j.val j.property)
  exact hi.symm.trans ((congrArg raw.maps.predictive same).trans hj)

theorem missing_atomic_no_semantic_readout
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hm : raw.source.acquisition.events.read a = none) :
    ¬ SemanticReadout raw a := fun hv =>
  ExecutionFrontier.missing_atomic_no_semantic_readout raw.source a hm hv.1

theorem semantic_weight_mismatch_rejected
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a)
    (x : Registers S SV) (hx : ExecutionFrontier.Closure raw.source a hs x)
    (da : D × A) (o : O)
    (bad : RegisterFuture.weight (ExecutionFrontier.temporal raw.target) a ht.2
      (translate raw a hm x) da o ≠ RegisterFuture.weight (ExecutionFrontier.temporal raw.source) a hs.2 x da o) :
    ¬ SemanticReadout raw a := by
  rintro ⟨_,_,hm',hl⟩
  exact bad ((hl hs ht).rows x hx da o)

theorem semantic_successor_mismatch_rejected
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a)
    (x : Registers S SV) (hx : ExecutionFrontier.Closure raw.source a hs x)
    (d : D) (hd : d ∈ raw.source.acquisition.execution.disturbances)
    (act : A) (ha : act ∈ raw.source.acquisition.execution.actions)
    (o : O) (ho : o ∈ raw.source.acquisition.execution.outcomes)
    (bad : translate raw a hm (AcquisitionExecution.update raw.source.acquisition a hs.1 x d act o) ≠
      AcquisitionExecution.update raw.target.acquisition a ht.1 (translate raw a hm x) d act o) :
    ¬ SemanticReadout raw a := by
  rintro ⟨_,_,hm',hl⟩
  exact bad ((hl hs ht).successor x hx d hd act ha o ho)

theorem semantic_field_mismatch_rejected {X : Type}
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a)
    (x : Registers S SV) (hx : ExecutionFrontier.Closure raw.source a hs x)
    (read : TemporalSnapshotReadout Q Residue Maintenance → X)
    (bad : read (mapSnapshotReadout raw.maps
      (RegisterFuture.observation (ExecutionFrontier.temporal raw.source) a hs.2 x)) ≠
      read (RegisterFuture.observation (ExecutionFrontier.temporal raw.target) a ht.2 (translate raw a hm x))) :
    ¬ SemanticReadout raw a := by
  rintro ⟨_,_,hm',hl⟩
  exact bad (congrArg read ((hl hs ht).observation x hx))

end CSTTT.TargetTheory.GenericHandoff.ExecutionBridge
