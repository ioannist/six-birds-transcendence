import CSTTT.Targets.GenericHandoff.ClauseDispatcher
import CSTTT.Targets.GenericHandoff.PackageEngine

/-! The raw package boundary fixes the semantic callbacks to the CLOSED
clause dispatcher. Target local/global assignments are computed by the stage
and cover. No accepted : Index → Prop parameter is exposed. This construction
alone does not certify the later runtime lift or handoff lanes. -/
namespace CSTTT.TargetTheory.GenericHandoff.DispatchedPackage
open ClauseDispatcher
variable {SC TC : Type} {SV : SC → Type} {TV : TC → Type} [DecidableEq TC]

structure Raw (SC TC : Type) (SV : SC → Type) (TV : TC → Type) where
  language : TranslationLanguage SC TC SV TV
  stage : Stage (Index := Kind) language
  referenceStage : Stage (Index := Kind) language
  sourceScopes : Kind → List SC
  cover : RawCover Kind TC
  clauses : Package TC TV

/-- Every rule's transitive dependencies belong to its declared scope. -/
def ScopeCheck (m : Raw SC TC SV TV) :=
  DependenciesCovered m.cover (fun c => (m.clauses.rule c).scope)

def Valid (m : Raw SC TC SV TV) (source : Assignment SC SV) : Prop :=
  CoverCheck m.cover ∧ ScopeCheck m ∧
  StageTotal m.language source m.stage m.cover.scopes ∧
  ReferenceCheck m.language m.stage m.referenceStage m.cover.scopes ∧
  ValuePreserving m.language source m.stage m.referenceStage m.cover.scopes ∧
  SourceCoverage m.language m.stage m.sourceScopes m.cover.scopes ∧
  PackageEngine.LocalChecks m.language source m.stage m.cover (fun c => (m.clauses.rule c).accept) ∧
  EdgeCompatible m.cover (mappedLocal m.language source m.stage m.cover.scopes)

def global (m : Raw SC TC SV TV) (source : Assignment SC SV) :=
  PackageEngine.global m.language source m.stage m.cover

theorem constructs (m : Raw SC TC SV TV) (source : Assignment SC SV) (h : Valid m source) :
    (∀ c k, k ∈ m.cover.scopes c → global m source k =
      mappedLocal m.language source m.stage m.cover.scopes c k) ∧
    (∀ k, (global m source k).isSome = true) ∧ m.clauses.accept (global m source) := by
  exact PackageEngine.constructs m.language source m.stage m.cover _ _
    (fun c a b h => (m.clauses.rule c).locality h) h.1 h.2.1 h.2.2.1 h.2.2.2.2.2.2.1 h.2.2.2.2.2.2.2

/-- A failed target rule rejects validity at this boundary, regardless of all
other lane data. This is a selected real failure, not a stored verdict. -/
theorem failed_local_rejected (m : Raw SC TC SV TV) (source : Assignment SC SV) (c : Kind)
    (bad : ¬ (m.clauses.rule c).accept (mappedLocal m.language source m.stage m.cover.scopes c)) :
    ¬ Valid m source := fun h => bad (h.2.2.2.2.2.2.1 c)

omit [DecidableEq TC] in
theorem missing_scope_rejected (m : Raw SC TC SV TV) (c : Kind) (k : TC)
    (hk : k ∈ (m.clauses.rule c).scope) (bad : k ∉ m.cover.scopes c) : ¬ ScopeCheck m :=
  missing_dependency_scope_rejected m.cover _ hk bad

end CSTTT.TargetTheory.GenericHandoff.DispatchedPackage
