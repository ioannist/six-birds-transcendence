import CSTTT.Core.Finite

namespace CSTTT.DefectTheory

/-- Exact defect components distinguish hard gates from bounded soft defects. -/
structure DefectComponent where
  hard : Bool
  defect : Nat
  tolerance : Nat
  deriving DecidableEq, Repr

/-- The exact vector is a finite list of independently typed defect components. -/
abbrev DefectVector := List DefectComponent

/-- Hard gates require zero defect. Soft components require componentwise
    tolerance. No scalar average appears in the acceptance rule. -/
def ComponentAccepts (c : DefectComponent) : Prop :=
  if c.hard then c.defect = 0 else c.defect ≤ c.tolerance

def VectorAccepts (v : DefectVector) : Prop :=
  ∀ c ∈ v, ComponentAccepts c

/-- TTS-02a. Every accepted hard gate is exact. -/
theorem acceptedHardGateIsZero
    (v : DefectVector)
    (hAccept : VectorAccepts v)
    (c : DefectComponent)
    (hMem : c ∈ v)
    (hHard : c.hard = true) :
    c.defect = 0 := by
  have hComponent := hAccept c hMem
  simp [ComponentAccepts, hHard] at hComponent
  exact hComponent

/-- A no-worse vector has the same gate types and tolerances and no larger
    component defect. -/
def NoWorse (lower upper : List DefectComponent) : Prop :=
  ListForall₂
    (fun lo hi =>
      lo.hard = hi.hard ∧
      lo.tolerance = hi.tolerance ∧
      lo.defect ≤ hi.defect)
    lower upper

/-- Component acceptance is preserved when a defect is reduced without
    changing its gate type or tolerance. -/
theorem componentAcceptanceDownward
    {lower upper : DefectComponent}
    (sameHard : lower.hard = upper.hard)
    (sameTolerance : lower.tolerance = upper.tolerance)
    (defectOrder : lower.defect ≤ upper.defect)
    (upperAccepts : ComponentAccepts upper) :
    ComponentAccepts lower := by
  cases hUpperHard : upper.hard with
  | false =>
      have hLowerHard : lower.hard = false := sameHard.trans hUpperHard
      simp [ComponentAccepts, hUpperHard] at upperAccepts
      simp [ComponentAccepts, hLowerHard, sameTolerance]
      exact Nat.le_trans defectOrder upperAccepts
  | true =>
      have hLowerHard : lower.hard = true := sameHard.trans hUpperHard
      simp [ComponentAccepts, hUpperHard] at upperAccepts
      have hLowerZero : lower.defect = 0 := by
        have hLeZero : lower.defect ≤ 0 := by simpa [upperAccepts] using defectOrder
        exact Nat.eq_zero_of_le_zero hLeZero
      simp [ComponentAccepts, hLowerHard, hLowerZero]

/-- TTS-02b. Componentwise acceptance is downward closed. -/
theorem vectorAcceptanceDownwardClosed
    {lower upper : DefectVector}
    (hOrder : NoWorse lower upper)
    (hUpper : VectorAccepts upper) :
    VectorAccepts lower := by
  intro lowerComponent lowerMember
  induction hOrder with
  | nil => simp at lowerMember
  | @cons lo hi lowerTail upperTail hHead hTail ih =>
      simp only [List.mem_cons] at lowerMember
      rcases lowerMember with rfl | lowerMember
      · rcases hHead with ⟨sameHard, sameTolerance, defectOrder⟩
        exact componentAcceptanceDownward
          sameHard sameTolerance defectOrder (hUpper hi (by simp))
      · have hUpperTail : VectorAccepts upperTail := by
          intro component member
          exact hUpper component (by simp [member])
        exact ih hUpperTail lowerMember

/-- Equal scalar summaries can coexist with opposite exact-vector verdicts;
    the supplied witnesses make the limitation explicit. -/
theorem scalarSummaryDoesNotDetermineAcceptance
    {Profile : Type}
    (scalar : Profile → Nat)
    (accepts : Profile → Prop)
    (accepted rejected : Profile)
    (sameScalar : scalar accepted = scalar rejected)
    (hAccepted : accepts accepted)
    (hRejected : ¬ accepts rejected) :
    ∃ x y, scalar x = scalar y ∧ accepts x ∧ ¬ accepts y := by
  exact ⟨accepted, rejected, sameScalar, hAccepted, hRejected⟩

end CSTTT.DefectTheory
