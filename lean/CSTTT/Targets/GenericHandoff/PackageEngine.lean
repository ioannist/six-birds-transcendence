import CSTTT.Targets.GenericHandoff.Substrate

/-! Dependent package gluing INTERPRETATION engine. Like StrategyGame, this
lemma is parametric in internal semantic relations. These callbacks are NOT
fields of RawHandoff or a substitute for its eight raw-rule dispatcher.
The raw boundary must instantiate them with the fixed clause algorithms and
prove their locality. Globals and locals below are always DEFINED from raw
stage/cell/cover data; neither is an independently supplied witness. -/
namespace CSTTT.TargetTheory.GenericHandoff.PackageEngine
variable {SC TC Index : Type} {SV : SC → Type} {TV : TC → Type} [DecidableEq TC]

def global (lang : TranslationLanguage SC TC SV TV) (source : Assignment SC SV)
    (stage : Stage (Index := Index) lang) (cover : RawCover Index TC) : Assignment TC TV :=
  glued cover (mappedLocal lang source stage cover.scopes)

/-- Internal locality contract; the dispatcher obtains this by cases on its
raw clause schemas. It is never an independently stored lane verdict. -/
def Locality (rules : Index → Assignment TC TV → Prop) (dependencies : Index → List TC) : Prop :=
  ∀ i a b, Agrees (dependencies i) a b → (rules i a ↔ rules i b)

def LocalChecks (lang : TranslationLanguage SC TC SV TV) (source : Assignment SC SV)
    (stage : Stage (Index := Index) lang) (cover : RawCover Index TC)
    (rules : Index → Assignment TC TV → Prop) : Prop :=
  ∀ i, rules i (mappedLocal lang source stage cover.scopes i)

/-- Target validity belongs to the fixed raw algorithms at the outer boundary.
This internal engine CONSTRUCTS a global accepted under those algorithms. -/
theorem constructs (lang : TranslationLanguage SC TC SV TV) (source : Assignment SC SV)
    (stage : Stage (Index := Index) lang) (cover : RawCover Index TC)
    (rules : Index → Assignment TC TV → Prop) (dependencies : Index → List TC)
    (locality : Locality rules dependencies) (coverCheck : CoverCheck cover)
    (scopeCheck : DependenciesCovered cover dependencies)
    (total : StageTotal lang source stage cover.scopes)
    (accepted : LocalChecks lang source stage cover rules)
    (compatible : EdgeCompatible cover (mappedLocal lang source stage cover.scopes)) :
    (∀ i k, k ∈ cover.scopes i →
      global lang source stage cover k = mappedLocal lang source stage cover.scopes i k) ∧
    (∀ k, (global lang source stage cover k).isSome = true) ∧
    (∀ i, rules i (global lang source stage cover)) := by
  have hr := glued_restricts cover (mappedLocal lang source stage cover.scopes) coverCheck compatible
  refine ⟨hr,?_,?_⟩
  · intro k
    obtain ⟨i,_,hk⟩ := coverCheck.1 k
    unfold global
    rw [hr i k hk]
    exact mapped_complete lang total i k hk
  · intro i
    apply (locality i _ _ (fun k hk => hr i k (scopeCheck i k hk))).mpr
    exact accepted i

/-- Existing global acceptance implies acceptance of each defined local;
there is no canonical-only or positive-only assumption. -/
theorem local_checks_iff_global (lang : TranslationLanguage SC TC SV TV) (source : Assignment SC SV)
    (stage : Stage (Index := Index) lang) (cover : RawCover Index TC)
    (rules : Index → Assignment TC TV → Prop) (dependencies : Index → List TC)
    (locality : Locality rules dependencies) (coverCheck : CoverCheck cover)
    (scopeCheck : DependenciesCovered cover dependencies)
    (compatible : EdgeCompatible cover (mappedLocal lang source stage cover.scopes)) :
    LocalChecks lang source stage cover rules ↔ ∀ i, rules i (global lang source stage cover) := by
  have hr := glued_restricts cover (mappedLocal lang source stage cover.scopes) coverCheck compatible
  constructor <;> intro h i
  · exact (locality i _ _ (fun k hk => hr i k (scopeCheck i k hk))).mpr (h i)
  · exact (locality i _ _ (fun k hk => hr i k (scopeCheck i k hk))).mp (h i)

omit [DecidableEq TC] in
/-- A deleted source primitive rejects before any clause helper can default.
The conclusion quantifies possible stage-total proofs, not conflicting premises. -/
theorem deleted_source_rejected (lang : TranslationLanguage SC TC SV TV) (source : Assignment SC SV)
    (stage : Stage (Index := Index) lang) (cover : RawCover Index TC) (i : Index) (k : TC)
    (arrow : CellArrow lang k) (hk : k ∈ cover.scopes i) (ha : stage i k = some arrow)
    (missing : source arrow.source = none) : ¬ StageTotal lang source stage cover.scopes :=
  missing_source_rejected lang hk ha missing

end CSTTT.TargetTheory.GenericHandoff.PackageEngine
