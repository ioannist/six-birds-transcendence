import CSTTT.Corridor.FiniteTemporalCorridor
import CSTTT.Corridor.FiniteDirectSuccessor

namespace CSTTT.StrengtheningTheory

/-- The broader structural-lineage class is explicitly the disjunction of
    strict overlap evidence and direct-successor evidence. It does not alter
    the strict lineage field of Temporal-FIACH. -/
def GeneralizedTemporalContinuity
    {Model : Type}
    (overlap direct : Model → Prop)
    (m : Model) : Prop :=
  overlap m ∨ direct m

/-- Every strict-overlap witness embeds in the generalized class. -/
theorem overlapEmbedsGeneralized
    {Model : Type}
    {overlap direct : Model → Prop}
    {m : Model}
    (h : overlap m) :
    GeneralizedTemporalContinuity overlap direct m := by
  exact Or.inl h

/-- Every direct-successor witness embeds in the generalized class. -/
theorem directEmbedsGeneralized
    {Model : Type}
    {overlap direct : Model → Prop}
    {m : Model}
    (h : direct m) :
    GeneralizedTemporalContinuity overlap direct m := by
  exact Or.inr h

/-- Exact incomparability means that each evidence mode has a witness not
    accepted by the other. -/
def EvidenceModesIncomparable
    {Model : Type}
    (overlap direct : Model → Prop) : Prop :=
  (∃ m, overlap m ∧ ¬ direct m) ∧
  (∃ m, direct m ∧ ¬ overlap m)

/-- TTD-02. The two finite witnesses discharge the exact logical
    incomparability statement; no endpoint or identity premise is used. -/
theorem overlapDirectIncomparable
    {Model : Type}
    {overlap direct : Model → Prop}
    (overlapOnly : ∃ m, overlap m ∧ ¬ direct m)
    (directOnly : ∃ m, direct m ∧ ¬ overlap m) :
    EvidenceModesIncomparable overlap direct := by
  exact ⟨overlapOnly, directOnly⟩

/-- The generalized class strictly broadens overlap whenever a direct-only
    witness exists. -/
def StrictlyBroaderThan
    {Model : Type}
    (broad narrow : Model → Prop) : Prop :=
  (∀ m, narrow m → broad m) ∧
  (∃ m, broad m ∧ ¬ narrow m)

/-- TTS-01. Direct-only evidence makes the disjunctive class a strict
    broadening of overlap, while the strict Temporal-FIACH definition remains
    unchanged. -/
theorem generalizedStrictlyBroaderThanOverlap
    {Model : Type}
    {overlap direct : Model → Prop}
    (directOnly : ∃ m, direct m ∧ ¬ overlap m) :
    StrictlyBroaderThan
      (GeneralizedTemporalContinuity overlap direct)
      overlap := by
  constructor
  · intro m h
    exact overlapEmbedsGeneralized h
  · rcases directOnly with ⟨m, hDirect, hNotOverlap⟩
    exact ⟨m, directEmbedsGeneralized hDirect, hNotOverlap⟩

/-- A generalized path records evidence mode per leg. Concatenation preserves
    validity only under exact carrier and temporal-frontier agreement. -/
inductive ContinuityLegKind where
  | overlap
  | direct
  deriving DecidableEq, Repr

structure GeneralizedPathData (Signature : Type) where
  source : CarrierId
  target : CarrierId
  entry : Signature
  exit : Signature
  modes : List ContinuityLegKind
  everyLegValid : Prop
  noTemporalGap : Prop
  exactFrontiers : Prop

structure GeneralizedPathCertificate
    {Signature : Type}
    (d : GeneralizedPathData Signature) where
  endpointDistinct : d.source ≠ d.target
  nonemptyModes : d.modes ≠ []
  everyLegValid : d.everyLegValid
  noTemporalGap : d.noTemporalGap
  exactFrontiers : d.exactFrontiers

/-- Exact compatibility for generalized path concatenation. -/
def GeneralizedPathCompatible
    {Signature : Type}
    (left right : GeneralizedPathData Signature) : Prop :=
  left.target = right.source ∧ left.exit = right.entry

/-- Concatenate evidence modes without collapsing the path into a fictitious
    atomic edge. -/
def composeGeneralizedPath
    {Signature : Type}
    (left right : GeneralizedPathData Signature) : GeneralizedPathData Signature where
  source := left.source
  target := right.target
  entry := left.entry
  exit := right.exit
  modes := left.modes ++ right.modes
  everyLegValid := left.everyLegValid ∧ right.everyLegValid
  noTemporalGap := left.noTemporalGap ∧ right.noTemporalGap
  exactFrontiers := GeneralizedPathCompatible left right

/-- Mixed overlap/direct paths compose as paths under exact frontiers. -/
theorem generalizedPathComposition
    {Signature : Type}
    {left right : GeneralizedPathData Signature}
    (leftCert : GeneralizedPathCertificate left)
    (rightCert : GeneralizedPathCertificate right)
    (frontier : GeneralizedPathCompatible left right)
    (endpointsDistinct : left.source ≠ right.target) :
    Nonempty (GeneralizedPathCertificate (composeGeneralizedPath left right)) := by
  exact ⟨{
    endpointDistinct := endpointsDistinct
    nonemptyModes := by
      intro h
      have hParts : left.modes = [] ∧ right.modes = [] := List.append_eq_nil_iff.mp h
      exact leftCert.nonemptyModes hParts.1
    everyLegValid := ⟨leftCert.everyLegValid, rightCert.everyLegValid⟩
    noTemporalGap := ⟨leftCert.noTemporalGap, rightCert.noTemporalGap⟩
    exactFrontiers := frontier
  }⟩

end CSTTT.StrengtheningTheory
