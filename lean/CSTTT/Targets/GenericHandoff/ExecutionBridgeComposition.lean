import CSTTT.Targets.GenericHandoff.ExecutionBridge
import CSTTT.Targets.GenericHandoff.RegisterSubstitution

/-! Composition of actual interpreted execution bridges. The middle raw frame
is shared, and all programs read the same immutable assignment. This is an
execution component, not a physical corridor or staged-cell composition. -/
namespace CSTTT.TargetTheory.GenericHandoff.ExecutionBridgeComposition
open RegisterInterpreter CSTTT.TransportTheory
variable {Cell S M T D A O P Q Z Residue Maintenance Stage Id History RouteId : Type}
  {Value : Cell → Type} {SV : S → Type} {MV : M → Type} {TV : T → Type}

def maps (first : SnapshotRawMaps P Q Residue Maintenance)
    (second : SnapshotRawMaps Q Z Residue Maintenance) : SnapshotRawMaps P Z Residue Maintenance :=
  ⟨second.predictive ∘ first.predictive,second.order ∘ first.order,
    second.tickPhase ∘ first.tickPhase,second.progress ∘ first.progress,
    second.record ∘ first.record,second.residue ∘ first.residue,
    second.maintenance ∘ first.maintenance,second.owner ∘ first.owner⟩

theorem maps_equation (first : SnapshotRawMaps P Q Residue Maintenance)
    (second : SnapshotRawMaps Q Z Residue Maintenance)
    (v : TemporalSnapshotReadout P Residue Maintenance) :
    mapSnapshotReadout (maps first second) v =
      mapSnapshotReadout second (mapSnapshotReadout first v) := rfl

def compose
    (first : ExecutionBridge.Raw Cell Value S M SV MV D A O P Q Residue Maintenance Stage Id History RouteId)
    (second : ExecutionBridge.Raw Cell Value M T MV TV D A O Q Z Residue Maintenance Stage Id History RouteId) :
    ExecutionBridge.Raw Cell Value S T SV TV D A O P Z Residue Maintenance Stage Id History RouteId :=
  ⟨first.source,second.target,RegisterSubstitution.program first.translation second.translation,
    maps first.maps second.maps⟩

theorem translation_ready
    (first : ExecutionBridge.Raw Cell Value S M SV MV D A O P Q Residue Maintenance Stage Id History RouteId)
    (second : ExecutionBridge.Raw Cell Value M T MV TV D A O Q Z Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hf : ExecutionBridge.TranslationReady first a)
    (hs : ExecutionBridge.TranslationReady second a) :
    ExecutionBridge.TranslationReady (compose first second) a :=
  RegisterSubstitution.program_ready first.translation second.translation a hf hs

/-- No readiness or middle-frame agreement is needed for this exact
interpretation equation on every partial assignment. -/
theorem partial_translation
    (first : ExecutionBridge.Raw Cell Value S M SV MV D A O P Q Residue Maintenance Stage Id History RouteId)
    (second : ExecutionBridge.Raw Cell Value M T MV TV D A O Q Z Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (x : Registers S SV) (r : T) :
    ((compose first second).translation r).eval a x () =
      RegisterSubstitution.evalPartial a
        (RegisterSubstitution.evaluateTranslation first.translation a x ()) () (second.translation r) :=
  RegisterSubstitution.program_evaluation first.translation second.translation a x () r

theorem translation_equation
    (first : ExecutionBridge.Raw Cell Value S M SV MV D A O P Q Residue Maintenance Stage Id History RouteId)
    (second : ExecutionBridge.Raw Cell Value M T MV TV D A O Q Z Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hf : ExecutionBridge.TranslationReady first a)
    (hs : ExecutionBridge.TranslationReady second a)
    (hc : ExecutionBridge.TranslationReady (compose first second) a) (x : Registers S SV) :
    ExecutionBridge.translate (compose first second) a hc x =
      ExecutionBridge.translate second a hs (ExecutionBridge.translate first a hf x) := by
  funext r
  have he := RegisterSubstitution.checked_evaluation first.translation (second.translation r) a hf x ()
  have hi : RegisterSubstitution.translate first.translation a hf x () =
      ExecutionBridge.translate first a hf x := by
    funext k
    exact Option.some.inj ((RegisterSubstitution.translation_equation first.translation a hf x () k).symm.trans
      (ExecutionBridge.translate_equation first a hf x k))
  rw [hi] at he
  exact Option.some.inj ((ExecutionBridge.translate_equation (compose first second) a hc x r).symm.trans
    (he.trans (ExecutionBridge.translate_equation second a hs _ r)))

variable [DecidableEq O] [DecidableEq Stage] [DecidableEq P] [DecidableEq Q] [DecidableEq Z]
  [DecidableEq Residue] [DecidableEq Maintenance]

omit [DecidableEq Stage] [DecidableEq P] [DecidableEq Q] [DecidableEq Z]
  [DecidableEq Residue] [DecidableEq Maintenance] in
/-- Universal domain coverage matters: raw closure includes zero-weight
successors and every disturbance/action argument. -/
theorem closure_transport
    (raw : ExecutionBridge.Raw Cell Value S M SV MV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : ExecutionBridge.TranslationReady raw a)
    (hl : ExecutionBridge.Laws raw a hs ht hm)
    (hd : AcquisitionExecution.DomainCheck raw.source.schema raw.source.acquisition)
    (ha : ExecutionFrontier.ExecutionDomain raw.source)
    (x : Registers S SV) (hx : ExecutionFrontier.Closure raw.source a hs x) :
    ExecutionFrontier.Closure raw.target a ht (ExecutionBridge.translate raw a hm x) := by
  induction hx with
  | root x hx =>
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    rw [hl.initial]
    exact FutureClosure.root _ (List.mem_map.mpr ⟨i,hl.audit.symm ▸ hi,rfl⟩)
  | step hx da o ho ih =>
    rcases da with ⟨d,act⟩
    have he := hl.successor _ hx d (hd.2.2.2.2.2.2.2 d) act (ha.2.2 act) o ho
    have hot : o ∈ (RegisterFuture.dynamics (ExecutionFrontier.temporal raw.target) a ht.2).outcomes := by
      change o ∈ raw.target.acquisition.execution.outcomes
      rw [hl.outcomes]
      exact ho
    have hn := FutureClosure.step ih (d,act) o hot
    change ExecutionFrontier.Closure raw.target a ht
      (ExecutionBridge.translate raw a hm
        (AcquisitionExecution.update raw.source.acquisition a hs.1 _ d act o))
    rw [he]
    exact hn

theorem valid
    (first : ExecutionBridge.Raw Cell Value S M SV MV D A O P Q Residue Maintenance Stage Id History RouteId)
    (second : ExecutionBridge.Raw Cell Value M T MV TV D A O Q Z Residue Maintenance Stage Id History RouteId)
    (middle : second.source = first.target) (a : Assignment Cell Value)
    (hf : ExecutionBridge.Valid first a) (hs : ExecutionBridge.Valid second a) :
    ExecutionBridge.Valid (compose first second) a := by
  rcases first with ⟨source,mid,f,fs⟩
  rcases second with ⟨mid',target,g,gs⟩
  cases middle
  obtain ⟨fm,fl⟩ := hf.2.2
  obtain ⟨gm,gl⟩ := hs.2.2
  have cm := translation_ready ⟨source,mid,f,fs⟩ ⟨mid,target,g,gs⟩ a fm gm
  refine ⟨hf.1,hs.2.1,cm,?_⟩
  intro hsource htarget
  obtain ⟨hmid,_,hd,ha,_⟩ := hf.2.1
  have lf := fl hsource hmid
  have lg := gl hmid htarget
  have hc := fun x hx => closure_transport ⟨source,mid,f,fs⟩ a hsource hmid fm lf
    (by obtain ⟨_,_,hd,_,_⟩ := hf.1; exact hd)
    (by obtain ⟨_,_,_,ha,_⟩ := hf.1; exact ha) x hx
  constructor
  · exact lg.audit.trans lf.audit
  · exact lg.outcomes.trans lf.outcomes
  · exact lg.words.trans lf.words
  · intro hist
    rw [translation_equation _ _ a fm gm cm]
    dsimp only [compose]
    rw [lf.initial,lg.initial]
  · intro x hx da o
    rw [translation_equation _ _ a fm gm cm]
    exact (lg.rows _ (hc x hx) da o).trans (lf.rows x hx da o)
  · intro x hx d hd act ha o ho
    simp only [translation_equation _ _ a fm gm cm]
    dsimp only [compose]
    rw [lf.successor x hx d hd act ha o ho]
    exact lg.successor _ (hc x hx) d
      (by obtain ⟨_,_,hdom,_,_⟩ := hf.2.1; exact hdom.2.2.2.2.2.2.2 d)
      act (by obtain ⟨_,_,_,hdom,_⟩ := hf.2.1; exact hdom.2.2 act)
      o (lf.outcomes.symm ▸ ho)
  · intro x hx
    rw [translation_equation _ _ a fm gm cm]
    dsimp only [compose]
    rw [maps_equation,lf.observation x hx]
    exact lg.observation _ (hc x hx)

end CSTTT.TargetTheory.GenericHandoff.ExecutionBridgeComposition
