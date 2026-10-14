import CSTTT.Targets.GenericHandoff.PackageEngine

/-! Typed primitive-map composition for TTH-07. Instructions execute in
sequence with Option.bind. Intermediate scope coverage is interpreted before
reading the left arrow, so missing cells/scopes cannot acquire a fallback.
This is a package-map component, not a full handoff composition theorem. -/
namespace CSTTT.TargetTheory.GenericHandoff.StageComposition
variable {SC MC TC Index : Type} {SV : SC → Type} {MV : MC → Type} {TV : TC → Type}

def language (left : TranslationLanguage SC MC SV MV)
    (right : TranslationLanguage MC TC MV TV) : TranslationLanguage SC TC SV TV where
  Instruction s t := (mid : MC) × (left.Instruction s mid × right.Instruction mid t)
  execute instruction value :=
    (left.execute instruction.2.1 value).bind (right.execute instruction.2.2)

variable [DecidableEq MC]
def stage (left : TranslationLanguage SC MC SV MV)
    (right : TranslationLanguage MC TC MV TV)
    (first : Stage (Index := Index) left) (second : Stage (Index := Index) right)
    (middleScopes : Index → List MC) : Stage (Index := Index) (language left right) :=
  fun i t => do
    let r ← second i t
    if r.source ∈ middleScopes i then
      let l ← first i r.source
      pure ⟨l.source,⟨r.source,l.instruction,r.instruction⟩⟩
    else none

variable (left : TranslationLanguage SC MC SV MV) (right : TranslationLanguage MC TC MV TV)
  (first : Stage (Index := Index) left) (second : Stage (Index := Index) right)
  (middleScopes : Index → List MC)

theorem arrow_equation (i : Index) (t : TC) (r : CellArrow right t)
    (hr : second i t = some r) (hs : r.source ∈ middleScopes i)
    (l : CellArrow left r.source) (hl : first i r.source = some l) :
    stage left right first second middleScopes i t =
      some ⟨l.source,⟨r.source,l.instruction,r.instruction⟩⟩ := by
  simp [stage,hr,hs,hl]

theorem missing_right_arrow (i : Index) (t : TC) (h : second i t = none) :
    stage left right first second middleScopes i t = none := by simp [stage,h]

theorem missing_middle_scope (i : Index) (t : TC) (r : CellArrow right t)
    (hr : second i t = some r) (h : r.source ∉ middleScopes i) :
    stage left right first second middleScopes i t = none := by simp [stage,hr,h]

theorem missing_left_arrow (i : Index) (t : TC) (r : CellArrow right t)
    (hr : second i t = some r) (h : first i r.source = none) :
    stage left right first second middleScopes i t = none := by
  by_cases hs : r.source ∈ middleScopes i <;> simp [stage,hr,hs,h]

variable [DecidableEq TC]
/-- Exact sequential interpretation, even when any primitive or arrow is
absent. The intermediate scoped assignment is defined, never supplied. -/
theorem local_equation (a : Assignment SC SV) (targetScopes : Index → List TC)
    (i : Index) :
    mappedLocal (language left right) a (stage left right first second middleScopes) targetScopes i =
      mappedLocal right (mappedLocal left a first middleScopes i) second targetScopes i := by
  funext t
  by_cases ht : t ∈ targetScopes i
  · cases hr : second i t with
    | none => simp [mappedLocal,stage,ht,hr]
    | some r =>
      by_cases hs : r.source ∈ middleScopes i
      · cases hl : first i r.source with
        | none => simp [mappedLocal,stage,ht,hr,hs,hl]
        | some l =>
          cases a l.source <;> simp [mappedLocal,stage,ht,hr,hs,hl,language,Option.bind_assoc]
      · simp [mappedLocal,stage,ht,hr,hs]
  · simp [mappedLocal,ht]

theorem missing_middle_readout (a : Assignment SC SV) (targetScopes : Index → List TC)
    (i : Index) (t : TC) (r : CellArrow right t)
    (hr : second i t = some r) (hs : r.source ∉ middleScopes i) :
    mappedLocal (language left right) a (stage left right first second middleScopes) targetScopes i t = none := by
  by_cases ht : t ∈ targetScopes i
  all_goals simp [mappedLocal,ht,missing_middle_scope left right first second middleScopes i t r hr hs]

theorem missing_source_readout (a : Assignment SC SV) (targetScopes : Index → List TC)
    (i : Index) (t : TC) (r : CellArrow right t) (l : CellArrow left r.source)
    (hr : second i t = some r) (hs : r.source ∈ middleScopes i)
    (hl : first i r.source = some l) (ha : a l.source = none) :
    mappedLocal (language left right) a (stage left right first second middleScopes) targetScopes i t = none := by
  by_cases ht : t ∈ targetScopes i
  all_goals simp [mappedLocal,ht,arrow_equation left right first second middleScopes i t r hr hs l hl,ha]

theorem failed_first_instruction_readout (a : Assignment SC SV) (targetScopes : Index → List TC)
    (i : Index) (t : TC) (r : CellArrow right t) (l : CellArrow left r.source)
    (value : SV l.source) (hr : second i t = some r) (hs : r.source ∈ middleScopes i)
    (hl : first i r.source = some l) (ha : a l.source = some value)
    (bad : left.execute l.instruction value = none) :
    mappedLocal (language left right) a (stage left right first second middleScopes) targetScopes i t = none := by
  by_cases ht : t ∈ targetScopes i
  all_goals simp [mappedLocal,ht,arrow_equation left right first second middleScopes i t r hr hs l hl,ha,language,bad]

theorem failed_second_instruction_readout (a : Assignment SC SV) (targetScopes : Index → List TC)
    (i : Index) (t : TC) (r : CellArrow right t) (l : CellArrow left r.source)
    (value : SV l.source) (mid : MV r.source)
    (hr : second i t = some r) (hs : r.source ∈ middleScopes i)
    (hl : first i r.source = some l) (ha : a l.source = some value)
    (good : left.execute l.instruction value = some mid) (bad : right.execute r.instruction mid = none) :
    mappedLocal (language left right) a (stage left right first second middleScopes) targetScopes i t = none := by
  by_cases ht : t ∈ targetScopes i
  all_goals simp [mappedLocal,ht,arrow_equation left right first second middleScopes i t r hr hs l hl,ha,language,good,bad]

/-- Only coordinate/scope references are compared here. This does not supply
a package acceptance or a value-preservation conclusion. -/
def ScopeLink (targetScopes : Index → List TC) : Prop :=
  ∀ i t, t ∈ targetScopes i → ∀ r, second i t = some r → r.source ∈ middleScopes i

theorem local_on_global (a : Assignment SC SV)
    (middleCover : RawCover Index MC) (targetCover : RawCover Index TC)
    (hscopes : middleCover.scopes = middleScopes)
    (hc : CoverCheck middleCover)
    (he : EdgeCompatible middleCover (mappedLocal left a first middleCover.scopes))
    (hl : ScopeLink right second middleScopes targetCover.scopes) (i : Index) :
    mappedLocal (language left right) a (stage left right first second middleScopes) targetCover.scopes i =
      mappedLocal right (PackageEngine.global left a first middleCover) second targetCover.scopes i := by
  rw [local_equation]
  funext t
  by_cases ht : t ∈ targetCover.scopes i
  · cases hr : second i t with
    | none => simp [mappedLocal,ht,hr]
    | some r =>
      have hs := hl i t ht r hr
      have hx := glued_restricts middleCover (mappedLocal left a first middleCover.scopes) hc he i r.source
        (by simpa only [hscopes] using hs)
      change PackageEngine.global left a first middleCover r.source = _ at hx
      simp only [hscopes] at hx
      simp only [mappedLocal,ht,if_true,hr,Option.bind_some]
      exact congrArg (fun value => value.bind (right.execute r.instruction)) hx.symm
  · simp [mappedLocal,ht]

theorem global_equation (a : Assignment SC SV)
    (middleCover : RawCover Index MC) (targetCover : RawCover Index TC)
    (hscopes : middleCover.scopes = middleScopes)
    (hc : CoverCheck middleCover)
    (he : EdgeCompatible middleCover (mappedLocal left a first middleCover.scopes))
    (hl : ScopeLink right second middleScopes targetCover.scopes) :
    PackageEngine.global (language left right) a (stage left right first second middleScopes) targetCover =
      PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover := by
  exact congrArg (glued targetCover) (funext
    (local_on_global left right first second middleScopes a middleCover targetCover hscopes hc he hl))

omit [DecidableEq TC] in
theorem total (a : Assignment SC SV) (targetScopes : Index → List TC)
    (middle : Assignment MC MV)
    (hl : StageTotal left a first middleScopes)
    (hr : StageTotal right middle second targetScopes)
    (hs : ScopeLink right second middleScopes targetScopes) :
    StageTotal (language left right) a (stage left right first second middleScopes) targetScopes := by
  intro i t ht
  obtain ⟨r,her,_,hopr⟩ := hr i t ht
  obtain ⟨l,hel,hpresent,hopl⟩ := hl i r.source (hs i t ht r her)
  refine ⟨⟨l.source,⟨r.source,l.instruction,r.instruction⟩⟩,
    arrow_equation left right first second middleScopes i t r her (hs i t ht r her) l hel,
    hpresent,?_⟩
  intro value
  change ((left.execute l.instruction value).bind (right.execute r.instruction)) ≠ none
  cases hv : left.execute l.instruction value with
  | none => exact False.elim (hopl value hv)
  | some mid => simpa only [Option.bind_some] using hopr mid

omit [DecidableEq TC] in
theorem source_equation (i : Index) (t : TC) :
    (stage left right first second middleScopes i t).map (fun arrow => arrow.source) =
      ((second i t).map (fun arrow => arrow.source)).bind (fun mid =>
        if mid ∈ middleScopes i then (first i mid).map (fun arrow => arrow.source) else none) := by
  cases hr : second i t with
  | none => simp [stage,hr]
  | some r =>
    by_cases hs : r.source ∈ middleScopes i
    · cases hl : first i r.source <;> simp [stage,hr,hs,hl]
    · simp [stage,hr,hs]

omit [DecidableEq TC] in
theorem reference (firstRef : Stage (Index := Index) left)
    (secondRef : Stage (Index := Index) right) (targetScopes : Index → List TC)
    (hl : ReferenceCheck left first firstRef middleScopes)
    (hr : ReferenceCheck right second secondRef targetScopes) :
    ReferenceCheck (language left right) (stage left right first second middleScopes)
      (stage left right firstRef secondRef middleScopes) targetScopes := by
  intro i t ht
  rw [source_equation,source_equation,hr i t ht]
  have hf : (fun mid => if mid ∈ middleScopes i then (first i mid).map (fun arrow => arrow.source) else none) =
      (fun mid => if mid ∈ middleScopes i then (firstRef i mid).map (fun arrow => arrow.source) else none) := by
    funext mid
    by_cases hm : mid ∈ middleScopes i
    · simp only [hm,if_true]; exact hl i mid hm
    · simp [hm]
  rw [hf]

omit [DecidableEq MC] [DecidableEq TC] in
theorem scope_link_reference (secondRef : Stage (Index := Index) right)
    (targetScopes : Index → List TC)
    (hscope : ScopeLink right second middleScopes targetScopes)
    (href : ReferenceCheck right second secondRef targetScopes) :
    ScopeLink right secondRef middleScopes targetScopes := by
  intro i t ht r hr
  have h := href i t ht
  rw [hr] at h
  cases ha : second i t with
  | none => simp [ha] at h
  | some actual =>
    have hs : actual.source = r.source := by simpa [ha] using h
    simpa only [← hs] using hscope i t ht actual ha

theorem value_preserving (firstRef : Stage (Index := Index) left)
    (secondRef : Stage (Index := Index) right) (a : Assignment SC SV)
    (middleCover : RawCover Index MC) (targetCover : RawCover Index TC)
    (hscopes : middleCover.scopes = middleScopes)
    (hc : CoverCheck middleCover)
    (he : EdgeCompatible middleCover (mappedLocal left a first middleCover.scopes))
    (hscope : ScopeLink right second middleScopes targetCover.scopes)
    (href : ReferenceCheck right second secondRef targetCover.scopes)
    (hleft : ValuePreserving left a first firstRef middleScopes)
    (hright : ValuePreserving right (PackageEngine.global left a first middleCover)
      second secondRef targetCover.scopes) :
    ValuePreserving (language left right) a (stage left right first second middleScopes)
      (stage left right firstRef secondRef middleScopes) targetCover.scopes := by
  intro i t ht
  have prefixEq : mappedLocal left a first middleScopes i = mappedLocal left a firstRef middleScopes i := by
    funext mid
    by_cases hm : mid ∈ middleScopes i
    · exact hleft i mid hm
    · simp [mappedLocal,hm]
  have ha := local_on_global left right first second middleScopes a middleCover targetCover hscopes hc he hscope i
  have hb := local_on_global left right first secondRef middleScopes a middleCover targetCover hscopes hc he
    (scope_link_reference right second middleScopes secondRef targetCover.scopes hscope href) i
  rw [local_equation,local_equation,← prefixEq]
  rw [← local_equation left right first second middleScopes a targetCover.scopes i,
    ← local_equation left right first secondRef middleScopes a targetCover.scopes i,ha,hb]
  exact hright i t ht

omit [DecidableEq TC] in
theorem source_coverage (sourceScopes : Index → List SC) (targetScopes : Index → List TC)
    (hleft : SourceCoverage left first sourceScopes middleScopes)
    (hright : SourceCoverage right second middleScopes targetScopes) :
    SourceCoverage (language left right) (stage left right first second middleScopes) sourceScopes targetScopes := by
  intro i s hs
  obtain ⟨mid,hm,l,hl,hsource⟩ := hleft i s hs
  obtain ⟨t,ht,r,hr,hmiddle⟩ := hright i mid hm
  have hmap : (stage left right first second middleScopes i t).map (fun arrow => arrow.source) = some s := by
    rw [source_equation]
    simp [hr,hmiddle,hm,hl,hsource]
  cases ha : stage left right first second middleScopes i t with
  | none => simp [ha] at hmap
  | some arrow =>
    exact ⟨t,ht,arrow,ha,by simpa [ha] using hmap⟩

variable {FC : Type} {FV : FC → Type} [DecidableEq FC]
/-- Association changes only instruction packaging. Both interpreted routes
have the same output at every partial assignment, including every failure. -/
theorem local_associative (third : TranslationLanguage TC FC TV FV)
    (thirdStage : Stage (Index := Index) third) (targetScopes : Index → List TC)
    (finalScopes : Index → List FC) (a : Assignment SC SV) (i : Index) :
    mappedLocal (language (language left right) third) a
      (stage (language left right) third (stage left right first second middleScopes) thirdStage targetScopes)
      finalScopes i =
    mappedLocal (language left (language right third)) a
      (stage left (language right third) first (stage right third second thirdStage targetScopes) middleScopes)
      finalScopes i := by
  simp only [local_equation]

end CSTTT.TargetTheory.GenericHandoff.StageComposition
