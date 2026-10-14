import CSTTT.Targets.GenericHandoff.NativeComposition.ObjecthoodProbe
import CSTTT.Targets.GenericHandoff.NativeComposition.EpisodeRules
import CSTTT.Targets.GenericHandoff.NativeComposition.MemoryFrames
import CSTTT.Targets.GenericHandoff.ObjecthoodProtocol

/-! Primitive C1 reference tables and Gaussian instructions live in a typed
supplementary cell. Factor rows, positions, hazards and the declared probe
policy consume the actual current or copied source Input. Both cells are
required on every partial assignment. No E, pi or verdict is a raw field. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeObjecthoodCells
open RegisterInterpreter ModeExecution

structure Supplement where
  prototypes : List Factor
  parameters : ObjecthoodCells.Parameters Factor
  publishedP : Factor → Factor → Rat
  publishedC : Factor → Nat → Rat
  publishedU : Nat → Factor → Rat

abbrev Cell := Sum Owner Owner
def Value : Cell → Type
  | .inl o => MemoryValue o
  | .inr _ => Supplement × Supplement

def selectSupplement (copy : Bool) (p : Supplement × Supplement) := if copy then p.2 else p.1
def supplement : Supplement :=
  let d := ObjecthoodProbe.raw
  ⟨d.prototypes,⟨d.rowScale,d.tau,d.epsilon,d.core,d.anchor,d.operations,d.retention,
    d.expectedTV,d.expectedZeroDefect,d.expectedDefect⟩,d.publishedP,d.publishedC,d.publishedU⟩

def data (i : Input) (s : Supplement) : ObjecthoodRules.Raw Factor Bool Factor :=
  let p := s.parameters
  ⟨TemporalFactorRules.profile (factorSchema false) i.temporal,ObjecthoodProbe.policy i.temporal,
    s.prototypes,p.rowScale,p.tau,p.epsilon,p.core,p.anchor,p.operations,s.publishedP,s.publishedC,s.publishedU,
    p.retention,p.expectedTV,p.expectedZeroDefect,p.expectedDefect⟩

def bindings (cell : Owner) (copy : Bool) : ObjecthoodCells.Bindings Cell Value Factor Bool Factor :=
  let native : MemoryValue cell → Input := MemoryFrames.selectInput copy
  let get : Supplement × Supplement → Supplement := selectSupplement copy
  ⟨⟨.inl cell,fun p => (native p).temporal.rows⟩,
    ⟨.inl cell,fun p => (native p).temporal.positions⟩,
    ⟨.inl cell,fun p => (native p).temporal.hazards⟩,
    ⟨.inl cell,fun p => ObjecthoodProbe.policy (native p).temporal⟩,
    ⟨.inr cell,fun p => (get p).prototypes⟩,
    ⟨.inr cell,fun p => (get p).parameters⟩,
    ⟨.inr cell,fun p => (get p).publishedP⟩,
    ⟨.inr cell,fun p => (get p).publishedC⟩,
    ⟨.inr cell,fun p => (get p).publishedU⟩⟩

theorem decoded (cell : Owner) (copy : Bool) (a : Assignment Cell Value) :
    ObjecthoodCells.decoded clauseSchema.toSchema (bindings cell copy) a=(do
      let n ← a (.inl cell)
      let s ← a (.inr cell)
      pure (data (MemoryFrames.selectInput copy n) (selectSupplement copy s))) := by
  cases hn : a (.inl cell) <;> cases hs : a (.inr cell) <;>
    simp [ObjecthoodCells.decoded,bindings,CellView.read,hn,hs,data,TemporalFactorRules.profile,factorSchema]

theorem acceptance_iff (cell : Owner) (copy : Bool) (a : Assignment Cell Value) :
    ObjecthoodCells.Accept clauseSchema.toSchema (bindings cell copy) a ↔
      ∃ n s, a (.inl cell)=some n ∧ a (.inr cell)=some s ∧
        ObjecthoodRules.Accept (data (MemoryFrames.selectInput copy n) (selectSupplement copy s)) := by
  simp only [ObjecthoodCells.Accept,decoded]
  cases a (.inl cell) <;> cases a (.inr cell) <;> simp

theorem missing_native (cell : Owner) (copy : Bool) (a : Assignment Cell Value)
    (hm : a (.inl cell)=none) : ¬ ObjecthoodCells.Accept clauseSchema.toSchema (bindings cell copy) a := by
  rw [acceptance_iff]
  simp [hm]
theorem missing_supplement (cell : Owner) (copy : Bool) (a : Assignment Cell Value)
    (hm : a (.inr cell)=none) : ¬ ObjecthoodCells.Accept clauseSchema.toSchema (bindings cell copy) a := by
  rw [acceptance_iff]
  simp [hm]

def nativeInputs (a : Assignment Cell Value) : Assignment Owner MemoryValue := fun o => a (.inl o)
def image (a : Assignment Cell Value) : Assignment Cell Value
  | .inl o => memoryImage (nativeInputs a) o
  | .inr o => (a (.inr (swapOwner o))).map (fun p => (p.1,p.1))

theorem copied_supplement_source (a : Assignment Cell Value) (o : Owner) :
    (image a (.inr (swapOwner o))).map (selectSupplement true)=
      (a (.inr o)).map (selectSupplement false) := by
  cases o <;> simp [image,selectSupplement,swapOwner,Option.map_map,Function.comp_def] <;> rfl

theorem copied_native_source (a : Assignment Cell Value) (o : Owner) :
    sourceInputs (nativeInputs (image a)) (swapOwner o)=currentInputs (nativeInputs a) o :=
  published_source (nativeInputs a) o

theorem publication_source_decoded (a : Assignment Cell Value) (o : Owner) :
    ObjecthoodCells.decoded clauseSchema.toSchema (bindings (swapOwner o) true) (image a)=
      ObjecthoodCells.decoded clauseSchema.toSchema (bindings o false) a := by
  cases o with
  | false =>
    cases hn : a (.inl false) <;> cases hs : a (.inr false) <;>
      simp [decoded,image,nativeInputs,memoryImage,memoryPublish,swapOwner,
        MemoryFrames.selectInput,selectSupplement,hn,hs]
  | true =>
    cases hn : a (.inl true) <;> cases hs : a (.inr true) <;>
      simp [decoded,image,nativeInputs,memoryImage,memoryPublish,swapOwner,
        MemoryFrames.selectInput,selectSupplement,hn,hs]

theorem data_publish (i : Input) (s : Supplement) : data (publish i) s=data i s := rfl
theorem round_data (n : Nat) : data (roundInput n) supplement=ObjecthoodProbe.raw := by
  induction n with
  | zero => rfl
  | succ n ih => exact (data_publish (roundInput n) supplement).trans ih

def reference : ObjecthoodProtocol.Reference Factor :=
  let d := ObjecthoodProbe.raw
  ⟨d.tau,d.epsilon,d.retention,d.publishedP,d.publishedC,d.publishedU,d.prototypes⟩

theorem publication_source_accept_iff (a : Assignment Cell Value) (o : Owner) :
    ObjecthoodProtocol.Accept clauseSchema.toSchema reference (bindings (swapOwner o) true) (image a) ↔
      ObjecthoodProtocol.Accept clauseSchema.toSchema reference (bindings o false) a := by
  simp only [ObjecthoodProtocol.Accept,publication_source_decoded]

theorem actual_round_accept (cell : Owner) (copy : Bool) (a : Assignment Cell Value) (n : Nat)
    (p : MemoryValue cell) (hp : a (.inl cell)=some p)
    (hn : MemoryFrames.selectInput copy p=roundInput n)
    (s : Supplement × Supplement) (hs : a (.inr cell)=some s)
    (hc : selectSupplement copy s=supplement) :
    ObjecthoodProtocol.Accept clauseSchema.toSchema reference (bindings cell copy) a := by
  refine ⟨ObjecthoodProbe.raw,?_,ObjecthoodProbe.actual_c1_accept,?_⟩
  · rw [decoded,hp,hs]
    simp only [bind,Option.bind_some,hn,hc,round_data]
    rfl
  · exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeObjecthoodCells
