import CSTTT.Targets.GenericHandoff.StageComposition

/-! Primitive-stage composition through the actual middle global's cover
selector. Prefix clauses may differ from the right clause. Selection depends
only on raw scope/ordering, never on whether a value is present. Missing
selected arrows or primitives remain absent. -/
namespace CSTTT.TargetTheory.GenericHandoff.GlobalStageComposition
variable {SC MC TC LI RI : Type} {SV : SC → Type} {MV : MC → Type} {TV : TC → Type}
variable [DecidableEq MC]

def selectedArrow (left : TranslationLanguage SC MC SV MV)
    (first : Stage (Index := LI) left) (middleCover : RawCover LI MC) (mid : MC) :
    Option (CellArrow left mid) :=
  (firstCover middleCover.scopes mid middleCover.indices).bind (fun i => first i mid)

def stage (left : TranslationLanguage SC MC SV MV) (right : TranslationLanguage MC TC MV TV)
    (first : Stage (Index := LI) left) (second : Stage (Index := RI) right)
    (middleCover : RawCover LI MC) : Stage (Index := RI) (StageComposition.language left right) :=
  fun i t => do
    let r ← second i t
    let l ← selectedArrow left first middleCover r.source
    pure ⟨l.source,⟨r.source,l.instruction,r.instruction⟩⟩

variable (left : TranslationLanguage SC MC SV MV) (right : TranslationLanguage MC TC MV TV)
    (first : Stage (Index := LI) left) (second : Stage (Index := RI) right)
    (middleCover : RawCover LI MC)

/-- No cover, compatibility, readiness or completeness premise. -/
theorem prefix_equation (a : Assignment SC SV) (mid : MC) :
    PackageEngine.global left a first middleCover mid =
      (selectedArrow left first middleCover mid).bind (fun l => (a l.source).bind (left.execute l.instruction)) := by
  cases hs : firstCover middleCover.scopes mid middleCover.indices with
  | none => simp [PackageEngine.global,glued,selectedArrow,hs]
  | some i =>
    have hm := (firstCover_supported hs).2
    simp [PackageEngine.global,glued,selectedArrow,hs,mappedLocal,hm]

theorem arrow_equation (i : RI) (t : TC) (r : CellArrow right t)
    (l : CellArrow left r.source) (hr : second i t = some r)
    (hl : selectedArrow left first middleCover r.source = some l) :
    stage left right first second middleCover i t =
      some ⟨l.source,⟨r.source,l.instruction,r.instruction⟩⟩ := by simp [stage,hr,hl]

theorem missing_selected_arrow (i : RI) (t : TC) (r : CellArrow right t)
    (hr : second i t = some r) (hl : selectedArrow left first middleCover r.source = none) :
    stage left right first second middleCover i t = none := by simp [stage,hr,hl]

theorem missing_selector (i : RI) (t : TC) (r : CellArrow right t)
    (hr : second i t = some r)
    (hs : firstCover middleCover.scopes r.source middleCover.indices = none) :
    stage left right first second middleCover i t = none := by simp [stage,hr,selectedArrow,hs]

theorem selected_no_fallback (mid : MC) (i : LI)
    (hs : firstCover middleCover.scopes mid middleCover.indices = some i)
    (ha : first i mid = none) : selectedArrow left first middleCover mid = none := by
  simp [selectedArrow,hs,ha]

theorem selected_global_absent (a : Assignment SC SV) (mid : MC)
    (h : selectedArrow left first middleCover mid = none) :
    PackageEngine.global left a first middleCover mid = none := by
  rw [prefix_equation,h]
  rfl

variable [DecidableEq TC]
/-- Exact sequential local interpretation for every partial assignment, even
with invalid/empty covers and absent selected primitives or arrows. -/
theorem local_equation (a : Assignment SC SV) (targetScopes : RI → List TC) (i : RI) :
    mappedLocal (StageComposition.language left right) a (stage left right first second middleCover) targetScopes i =
      mappedLocal right (PackageEngine.global left a first middleCover) second targetScopes i := by
  funext t
  by_cases ht : t ∈ targetScopes i
  · cases hr : second i t with
    | none => simp [mappedLocal,stage,ht,hr]
    | some r =>
      simp only [mappedLocal,ht,if_true,stage,hr,Option.bind_some]
      rw [prefix_equation]
      cases hp : selectedArrow left first middleCover r.source <;>
        simp [hp,StageComposition.language,Option.bind_assoc]
  · simp [mappedLocal,ht]

theorem global_equation (a : Assignment SC SV) (targetCover : RawCover RI TC) :
    PackageEngine.global (StageComposition.language left right) a
      (stage left right first second middleCover) targetCover =
    PackageEngine.global right (PackageEngine.global left a first middleCover) second targetCover :=
  congrArg (glued targetCover) (funext (local_equation left right first second middleCover a targetCover.scopes))

theorem missing_prefix_readout (a : Assignment SC SV) (targetScopes : RI → List TC)
    (i : RI) (t : TC) (r : CellArrow right t) (hr : second i t = some r)
    (hm : PackageEngine.global left a first middleCover r.source = none) :
    mappedLocal (StageComposition.language left right) a (stage left right first second middleCover) targetScopes i t = none := by
  rw [local_equation]
  by_cases ht : t ∈ targetScopes i <;> simp [mappedLocal,ht,hr,hm]

theorem missing_source_readout (a : Assignment SC SV) (targetScopes : RI → List TC)
    (i : RI) (t : TC) (r : CellArrow right t) (l : CellArrow left r.source)
    (hr : second i t = some r) (hl : selectedArrow left first middleCover r.source = some l)
    (ha : a l.source = none) :
    mappedLocal (StageComposition.language left right) a (stage left right first second middleCover) targetScopes i t = none := by
  by_cases ht : t ∈ targetScopes i
  all_goals simp [mappedLocal,ht,arrow_equation left right first second middleCover i t r l hr hl,ha]

omit [DecidableEq TC] in
theorem prefix_total (a : Assignment SC SV)
    (hc : CoverCheck middleCover) (h : StageTotal left a first middleCover.scopes) (mid : MC) :
    ∃ l, selectedArrow left first middleCover mid = some l ∧ (a l.source).isSome = true ∧
      ∀ value, left.execute l.instruction value ≠ none := by
  obtain ⟨i,hi⟩ := firstCover_exists (hc.1 mid)
  obtain ⟨l,hl,ha,hop⟩ := h i mid (firstCover_supported hi).2
  exact ⟨l,by simp [selectedArrow,hi,hl],ha,hop⟩

omit [DecidableEq TC] in
theorem total (a : Assignment SC SV) (targetScopes : RI → List TC)
    (hc : CoverCheck middleCover) (hl : StageTotal left a first middleCover.scopes)
    (hr : StageTotal right (PackageEngine.global left a first middleCover) second targetScopes) :
    StageTotal (StageComposition.language left right) a (stage left right first second middleCover) targetScopes := by
  intro i t ht
  obtain ⟨r,her,_,hopr⟩ := hr i t ht
  obtain ⟨l,hel,ha,hopl⟩ := prefix_total left first middleCover a hc hl r.source
  refine ⟨⟨l.source,⟨r.source,l.instruction,r.instruction⟩⟩,
    arrow_equation left right first second middleCover i t r l her hel,ha,?_⟩
  intro value
  change ((left.execute l.instruction value).bind (right.execute r.instruction)) ≠ none
  cases hv : left.execute l.instruction value with
  | none => exact False.elim (hopl value hv)
  | some mid => simpa only [Option.bind_some] using hopr mid

omit [DecidableEq TC] in
theorem source_equation (i : RI) (t : TC) :
    (stage left right first second middleCover i t).map (fun arrow => arrow.source) =
      ((second i t).map (fun arrow => arrow.source)).bind
        (fun mid => (selectedArrow left first middleCover mid).map (fun arrow => arrow.source)) := by
  cases hr : second i t with
  | none => simp [stage,hr]
  | some r => cases hl : selectedArrow left first middleCover r.source <;> simp [stage,hr,hl]

omit [DecidableEq TC] in
theorem prefix_reference (firstRef : Stage (Index := LI) left)
    (h : ReferenceCheck left first firstRef middleCover.scopes) (mid : MC) :
    (selectedArrow left first middleCover mid).map (fun arrow => arrow.source) =
      (selectedArrow left firstRef middleCover mid).map (fun arrow => arrow.source) := by
  cases hs : firstCover middleCover.scopes mid middleCover.indices with
  | none => simp [selectedArrow,hs]
  | some i => simpa [selectedArrow,hs] using h i mid (firstCover_supported hs).2

omit [DecidableEq TC] in
theorem reference (firstRef : Stage (Index := LI) left) (secondRef : Stage (Index := RI) right)
    (targetScopes : RI → List TC)
    (hl : ReferenceCheck left first firstRef middleCover.scopes)
    (hr : ReferenceCheck right second secondRef targetScopes) :
    ReferenceCheck (StageComposition.language left right) (stage left right first second middleCover)
      (stage left right firstRef secondRef middleCover) targetScopes := by
  intro i t ht
  rw [source_equation,source_equation,hr i t ht]
  have hp := funext (prefix_reference left first middleCover firstRef hl)
  rw [hp]

omit [DecidableEq TC] in
theorem prefix_values (a : Assignment SC SV) (firstRef : Stage (Index := LI) left)
    (h : ValuePreserving left a first firstRef middleCover.scopes) :
    PackageEngine.global left a first middleCover = PackageEngine.global left a firstRef middleCover := by
  have hl : mappedLocal left a first middleCover.scopes = mappedLocal left a firstRef middleCover.scopes := by
    funext i mid
    by_cases hm : mid ∈ middleCover.scopes i
    · exact h i mid hm
    · simp [mappedLocal,hm]
  exact congrArg (glued middleCover) hl

theorem value_preserving (a : Assignment SC SV) (firstRef : Stage (Index := LI) left)
    (secondRef : Stage (Index := RI) right) (targetScopes : RI → List TC)
    (hl : ValuePreserving left a first firstRef middleCover.scopes)
    (hr : ValuePreserving right (PackageEngine.global left a first middleCover) second secondRef targetScopes) :
    ValuePreserving (StageComposition.language left right) a (stage left right first second middleCover)
      (stage left right firstRef secondRef middleCover) targetScopes := by
  intro i t ht
  rw [local_equation,local_equation,← prefix_values left first middleCover a firstRef hl]
  exact hr i t ht

/-- Expected original-source references are derived from the independently
declared reference stage, not from successful actual primitive reads. -/
def footprint {L : TranslationLanguage SC TC SV TV} (reference : Stage (Index := RI) L)
    (targetScopes : RI → List TC) (i : RI) : List SC :=
  (targetScopes i).filterMap (fun t => (reference i t).map (fun arrow => arrow.source))

omit [DecidableEq MC] [DecidableEq TC] in
theorem reference_coverage {L : TranslationLanguage SC TC SV TV}
    (actual expected : Stage (Index := RI) L) (targetScopes : RI → List TC)
    (h : ReferenceCheck L actual expected targetScopes) :
    SourceCoverage L actual (footprint expected targetScopes) targetScopes := by
  intro i s hs
  obtain ⟨t,ht,he⟩ := List.mem_filterMap.mp hs
  have hm := (h i t ht).trans he
  cases ha : actual i t with
  | none => simp [ha] at hm
  | some arrow => exact ⟨t,ht,arrow,ha,by simpa [ha] using hm⟩

end CSTTT.TargetTheory.GenericHandoff.GlobalStageComposition
