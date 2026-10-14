import CSTTT.Transport.TemporalBridge

namespace CSTTT.RecordTheory

/-- Strict monotonicity is indexed by separately declared source and target
record orders. -/
def StrictlyMonotoneOn
    {SourceRecord TargetRecord : Type}
    (sourceLt : SourceRecord → SourceRecord → Prop)
    (targetLt : TargetRecord → TargetRecord → Prop)
    (mapRecord : SourceRecord → TargetRecord) : Prop :=
  ∀ a b, sourceLt a b → targetLt (mapRecord a) (mapRecord b)

/-- TTH-10. Strict source record progress remains strict after a record map
that is monotone for the declared arrow orders. -/
theorem monotoneRecordDescentTransportsArrow
    {SourceRecord TargetRecord : Type}
    (sourceLt : SourceRecord → SourceRecord → Prop)
    (targetLt : TargetRecord → TargetRecord → Prop)
    (mapRecord : SourceRecord → TargetRecord)
    (hmono : StrictlyMonotoneOn sourceLt targetLt mapRecord) :
    ∀ a b, sourceLt a b → targetLt (mapRecord a) (mapRecord b) := by
  exact hmono

/-- A named one-step interface used by the executable certificate layer. -/
theorem transportRecordArrowStep
    {SourceRecord TargetRecord : Type}
    (sourceLt : SourceRecord → SourceRecord → Prop)
    (targetLt : TargetRecord → TargetRecord → Prop)
    (mapRecord : SourceRecord → TargetRecord)
    (hmono : StrictlyMonotoneOn sourceLt targetLt mapRecord)
    (a b : SourceRecord)
    (hab : sourceLt a b) :
    targetLt (mapRecord a) (mapRecord b) := by
  exact monotoneRecordDescentTransportsArrow sourceLt targetLt mapRecord hmono a b hab

/-- Strict record transport composes. -/
theorem strictlyMonotone_comp
    {A B C : Type}
    (ltA : A → A → Prop)
    (ltB : B → B → Prop)
    (ltC : C → C → Prop)
    (f : A → B)
    (g : B → C)
    (hf : StrictlyMonotoneOn ltA ltB f)
    (hg : StrictlyMonotoneOn ltB ltC g) :
    StrictlyMonotoneOn ltA ltC (fun x => g (f x)) := by
  intro a b hab
  exact hg (f a) (f b) (hf a b hab)

end CSTTT.RecordTheory
