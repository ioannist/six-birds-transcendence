import CSTTT.Targets.GenericHandoff.RegisterFuture
import CSTTT.Targets.GenericHandoff.FullFutureComposition

/-! Raw owner renaming. The new observer and code are interpreted from the
modified owner instruction; all other raw instructions are retained. Every
partial-assignment readiness/interpretation statement is exact. -/
namespace CSTTT.TargetTheory.GenericHandoff.OwnerRelabel
open CSTTT.TransportTheory RegisterInterpreter
variable {Cell R D A O P Residue Maintenance : Type}
  {Value : Cell → Type} {RV : R → Type}

def renamedReadouts (f : CarrierId → CarrierId)
    (r : RegisterFuture.Readouts Cell Value R RV P Residue Maintenance) :=
  {r with owner := .map f r.owner}
def renamedRaw (f : CarrierId → CarrierId) (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance) :=
  {raw with readouts := renamedReadouts f raw.readouts}
def image (f : CarrierId → CarrierId) (x : TemporalSnapshotReadout P Residue Maintenance) :=
  {x with owner := f x.owner}

theorem ready_iff (f : CarrierId → CarrierId) (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) : RegisterFuture.RawReady (renamedRaw f raw) a ↔ RegisterFuture.RawReady raw a := Iff.rfl

theorem read_map {X Y : Type} (f : X → Y) (e : Expr Cell Value R RV Unit X) (a : Assignment Cell Value)
    (h : Complete e.dependencies a) (x : Registers R RV) :
    RegisterFuture.read (.map f e) a h x=f (RegisterFuture.read e a h x) := by
  apply Option.some.inj
  rw [←RegisterFuture.read_eq]
  change (e.eval a x ()).map f=some (f (RegisterFuture.read e a h x))
  rw [RegisterFuture.read_eq]
  rfl

theorem observation_equation (f : CarrierId → CarrierId)
    (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RegisterFuture.RawReady raw a) (x : Registers R RV) :
    RegisterFuture.observation (renamedRaw f raw) a h x=image f (RegisterFuture.observation raw a h x) := by
  simp only [RegisterFuture.observation,renamedRaw,renamedReadouts,image,read_map]

theorem image_injective (f : CarrierId → CarrierId) (hf : Function.Injective f) :
    Function.Injective (image (P := P) (Residue := Residue) (Maintenance := Maintenance) f) := by
  intro x y h
  have hp := congrArg TemporalSnapshotReadout.predictive h
  have ho := congrArg TemporalSnapshotReadout.order h
  have ht := congrArg TemporalSnapshotReadout.tickPhase h
  have hg := congrArg TemporalSnapshotReadout.progress h
  have hd := congrArg TemporalSnapshotReadout.record h
  have hr := congrArg TemporalSnapshotReadout.residue h
  have hm := congrArg TemporalSnapshotReadout.maintenance h
  have hw := hf (congrArg TemporalSnapshotReadout.owner h)
  cases x; cases y
  simp_all [image]

variable [DecidableEq O]
theorem weight_equation (f : CarrierId → CarrierId)
    (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RegisterFuture.RawReady raw a) (x : Registers R RV) (da : D × A) (o : O) :
    RegisterFuture.weight (renamedRaw f raw) a h x da o=RegisterFuture.weight raw a h x da o := rfl
omit [DecidableEq O] in
theorem next_equation (f : CarrierId → CarrierId)
    (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RegisterFuture.RawReady raw a) (x : Registers R RV) (da : D × A) (o : O) :
    RegisterFuture.next (renamedRaw f raw) a h x da o=RegisterFuture.next raw a h x da o := rfl

theorem transport_laws {S CS VS : Type}
    (source : FullFutureModel S (D × A) O CS VS)
    (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RegisterFuture.RawReady raw a) (closed : S → Prop)
    (translate : S → Registers R RV) (oldImage : VS → TemporalSnapshotReadout P Residue Maintenance)
    (f : CarrierId → CarrierId) (hf : Function.Injective f)
    (parent : FullFutureComposition.Laws source (RegisterFuture.future raw a h) closed translate oldImage) :
    FullFutureComposition.Laws source (RegisterFuture.future (renamedRaw f raw) a h) closed translate (image f ∘ oldImage) := by
  refine ⟨parent.outcomes,(image_injective f hf).comp parent.imageInjective,parent.closedNext,?_,?_,?_⟩
  · intro x hx
    change RegisterFuture.observation (renamedRaw f raw) a h (translate x)=_
    rw [observation_equation]
    exact congrArg (image f) (parent.observation x hx)
  · intro x hx da o
    change RegisterFuture.weight (renamedRaw f raw) a h (translate x) da o=_
    rw [weight_equation]
    exact parent.weight x hx da o
  · intro x hx da o
    change RegisterFuture.next (renamedRaw f raw) a h (translate x) da o=_
    rw [next_equation]
    exact parent.next x hx da o

def codeImage (f : CarrierId → CarrierId) (x : TemporalRunCode P Residue Maintenance) :=
  {x with owner := f x.owner}

theorem code_image_equation (f : CarrierId → CarrierId) (x : TemporalSnapshotReadout P Residue Maintenance) :
    bridgeCodeOfObservation (image f x)=codeImage f (bridgeCodeOfObservation x) := rfl

theorem code_image_injective (f : CarrierId → CarrierId) (hf : Function.Injective f) :
    Function.Injective (codeImage (P := P) (Residue := Residue) (Maintenance := Maintenance) f) := by
  intro x y h
  have hp := congrArg TemporalRunCode.predictive h
  have ho := congrArg TemporalRunCode.order h
  have ht := congrArg TemporalRunCode.tickPhase h
  have hr := congrArg TemporalRunCode.residue h
  have hm := congrArg TemporalRunCode.maintenance h
  have hw := hf (congrArg TemporalRunCode.owner h)
  cases x; cases y
  simp_all [codeImage]

theorem interpreted_code (f : CarrierId → CarrierId)
    (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RegisterFuture.RawReady raw a) (x : Registers R RV) :
    (RegisterFuture.future (renamedRaw f raw) a h).code x=
      codeImage f ((RegisterFuture.future raw a h).code x) := by
  change bridgeCodeOfObservation (RegisterFuture.observation (renamedRaw f raw) a h x)=_
  rw [observation_equation,code_image_equation]
  rfl

theorem renaming_laws (f : CarrierId → CarrierId) (hf : Function.Injective f)
    (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RegisterFuture.RawReady raw a) :
    FullFutureComposition.Laws (RegisterFuture.future raw a h) (RegisterFuture.future (renamedRaw f raw) a h)
      (fun _ => True) id (image f) :=
  ⟨rfl,image_injective f hf,(by intros; trivial),
    (fun x _ => observation_equation f raw a h x),
    (fun x _ da o => weight_equation f raw a h x da o),
    (fun x _ da o => next_equation f raw a h x da o)⟩

theorem image_inverse (f inverse : CarrierId → CarrierId) (rightInverse : ∀ c, f (inverse c)=c)
    (x : TemporalSnapshotReadout P Residue Maintenance) : image f (image inverse x)=x := by
  cases x
  simp [image,rightInverse]

variable [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]

/-- Full-future sufficiency is transported through actual raw instructions.
The inverse is a primitive name instruction, not a supplied future equality. -/
theorem independently_sufficient (f inverse : CarrierId → CarrierId) (hf : Function.Injective f)
    (rightInverse : ∀ c, f (inverse c)=c)
    (raw : RegisterFuture.Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RegisterFuture.RawReady raw a)
    (parent : FullFutureSufficient (RegisterFuture.future raw a h)) :
    FullFutureSufficient (RegisterFuture.future (renamedRaw f raw) a h) := by
  intro x y same word trace
  have codeEq : (RegisterFuture.future raw a h).code x=(RegisterFuture.future raw a h).code y := by
    apply code_image_injective f hf
    simpa only [interpreted_code] using same
  let oldTrace := trace.map (image inverse)
  have traceEq : oldTrace.map (image f)=trace := by
    simp [oldTrace,List.map_map,Function.comp_def,image_inverse f inverse rightInverse]
  have left := FullFutureComposition.all_words _ _ _ _ _ (renaming_laws f hf raw a h) x trivial word oldTrace
  have right := FullFutureComposition.all_words _ _ _ _ _ (renaming_laws f hf raw a h) y trivial word oldTrace
  simp only [id_eq,traceEq] at left right
  exact left.trans ((parent x y codeEq word oldTrace).trans right.symm)

end CSTTT.TargetTheory.GenericHandoff.OwnerRelabel
