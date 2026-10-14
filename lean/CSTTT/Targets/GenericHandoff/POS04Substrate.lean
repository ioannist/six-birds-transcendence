import CSTTT.Targets.GenericHandoff.Substrate
import CSTTT.POS04.Assigned.PackageControls

/-! Exact specialization of G6d-1, including arbitrary partial assignments.
The function-valued legacy arrow is a raw value translation instruction in this
adapter, not an acceptance function. Clause schemas are extracted separately. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04Adapter
open CSTTT.POS04

def language : TranslationLanguage CSTTT.POS04.Assigned.Cell CSTTT.POS04.Assigned.Cell CSTTT.POS04.Assigned.Value CSTTT.POS04.Assigned.Value :=
  ⟨(fun s t => CSTTT.POS04.Assigned.Value s → Option (CSTTT.POS04.Assigned.Value t)),fun f v => f v⟩
def stage (s : CSTTT.POS04.Assigned.RawStageMap) : Stage (Index := Clause) language :=
  fun c k => (s.arrows c k).map (fun arrow => ⟨arrow.source,arrow.operation⟩)
def cover (r : CSTTT.POS04.Assigned.RawPackageCover) : RawCover Clause CSTTT.POS04.Assigned.Cell :=
  ⟨clauses,r.scopes,fun i j => decide (r.parent i = some j ∨ r.parent j = some i)⟩

theorem decode_eq (scope : List CSTTT.POS04.Assigned.Cell) (a : CSTTT.POS04.Assigned.Assignment) :
    decode scope a = CSTTT.POS04.Assigned.decode scope a := rfl
theorem put_eq (a : CSTTT.POS04.Assigned.Assignment) (k : CSTTT.POS04.Assigned.Cell) (v : Option (CSTTT.POS04.Assigned.Value k)) :
    put a k v = CSTTT.POS04.Assigned.put a k v := rfl
theorem complete_iff (scope : List CSTTT.POS04.Assigned.Cell) (a : CSTTT.POS04.Assigned.Assignment) :
    Complete scope a ↔ CSTTT.POS04.Assigned.Complete scope a := Iff.rfl
theorem agrees_iff (scope : List CSTTT.POS04.Assigned.Cell) (a b : CSTTT.POS04.Assigned.Assignment) :
    Agrees scope a b ↔ CSTTT.POS04.Assigned.Agrees scope a b := Iff.rfl

theorem mapped_eq (a : CSTTT.POS04.Assigned.Assignment) (s : CSTTT.POS04.Assigned.RawStageMap) (r : CSTTT.POS04.Assigned.RawPackageCover)
    (c : Clause) : mappedLocal language a (stage s) r.scopes c = CSTTT.POS04.Assigned.mappedLocal a s r c := by
  funext k
  by_cases hk : k ∈ r.scopes c
  · simp only [mappedLocal,CSTTT.POS04.Assigned.mappedLocal,hk,if_true,stage]
    cases hs : s.arrows c k <;> rfl
  · simp [mappedLocal,CSTTT.POS04.Assigned.mappedLocal,hk]

theorem total_of_legacy (a : CSTTT.POS04.Assigned.Assignment) (s : CSTTT.POS04.Assigned.RawStageMap) (r : CSTTT.POS04.Assigned.RawPackageCover)
    (h : CSTTT.POS04.Assigned.MapTotal a s r) : StageTotal language a (stage s) r.scopes := by
  intro c k hk
  obtain ⟨arrow,ha,_,hv,hop⟩ := h c k hk
  exact ⟨⟨arrow.source,arrow.operation⟩,by simp [stage,ha],hv,hop⟩

/-- Exact characterization: the legacy totality additionally fixes the swap
source. Generic totality does not impose that particular coordinate map. -/
theorem total_legacy_iff (a : CSTTT.POS04.Assigned.Assignment) (s : CSTTT.POS04.Assigned.RawStageMap) (r : CSTTT.POS04.Assigned.RawPackageCover) :
    CSTTT.POS04.Assigned.MapTotal a s r ↔ StageTotal language a (stage s) r.scopes ∧
      (∀ c k, k ∈ r.scopes c → ∀ arrow, s.arrows c k = some arrow → arrow.source = CSTTT.POS04.Assigned.swapCell k) := by
  constructor
  · intro h
    refine ⟨total_of_legacy a s r h,?_⟩
    intro c k hk arrow ha
    obtain ⟨other,ho,he,_⟩ := h c k hk
    have eq : other = arrow := Option.some.inj (ho.symm.trans ha)
    subst other
    exact he
  · rintro ⟨ht,hs⟩ c k hk
    obtain ⟨arrow,ha,hv,hop⟩ := ht c k hk
    cases he : s.arrows c k with
    | none => simp [stage,he] at ha
    | some other =>
      have eq : (⟨other.source,other.operation⟩ : CellArrow language k) = arrow := by
        simpa [stage,he] using ha
      subst arrow
      exact ⟨other,rfl,hs c k hk other he,hv,hop⟩

theorem reference_mapped (a : CSTTT.POS04.Assigned.Assignment)
    (r : CSTTT.POS04.Assigned.RawPackageCover) (c : Clause) (k : CSTTT.POS04.Assigned.Cell)
    (hk : k ∈ r.scopes c) :
    mappedLocal language a (stage CSTTT.POS04.Assigned.canonicalStage) r.scopes c k =
      (a (CSTTT.POS04.Assigned.swapCell k)).map (CSTTT.POS04.Assigned.translatedValue k) := by
  rw [mapped_eq]
  simp only [CSTTT.POS04.Assigned.mappedLocal,hk,if_true,
    CSTTT.POS04.Assigned.canonicalStage,Option.bind_some]
  exact (Option.map_eq_bind (x := a (CSTTT.POS04.Assigned.swapCell k))
    (f := CSTTT.POS04.Assigned.translatedValue k)).symm

theorem values_legacy_iff (a : CSTTT.POS04.Assigned.Assignment)
    (s : CSTTT.POS04.Assigned.RawStageMap) (r : CSTTT.POS04.Assigned.RawPackageCover) :
    ValuePreserving language a (stage s) (stage CSTTT.POS04.Assigned.canonicalStage) r.scopes ↔
      CSTTT.POS04.Assigned.ValuePreserving a s r := by
  constructor <;> intro h c k hk
  · simpa only [mapped_eq,reference_mapped a r c k hk] using h c k hk
  · rw [reference_mapped a r c k hk,mapped_eq]
    exact h c k hk

theorem source_coverage_of_legacy (a : CSTTT.POS04.Assigned.Assignment)
    (s : CSTTT.POS04.Assigned.RawStageMap) (r : CSTTT.POS04.Assigned.RawPackageCover)
    (h : CSTTT.POS04.Assigned.MapTotal a s r) :
    SourceCoverage language (stage s) (CSTTT.POS04.Assigned.stagedSourceScope r) r.scopes := by
  intro c k hk
  obtain ⟨t,ht,arrow,ha,he⟩ := CSTTT.POS04.Assigned.stage_source_coverage h c k hk
  exact ⟨t,ht,⟨arrow.source,arrow.operation⟩,by simp [stage,ha],he⟩

theorem cover_checked (r : CSTTT.POS04.Assigned.RawPackageCover) (tag : Tag) (hc : CSTTT.POS04.Assigned.CoverCheck r tag) :
    CoverCheck (cover r) := by
  constructor
  · intro k
    obtain ⟨i,hi⟩ := hc.covers k
    exact ⟨i,by change i ∈ clauses; cases i <;> decide,hi⟩
  · intro i j k hi hj
    have path := hc.running i j k hi hj
    clear hi hj
    induction path with
    | refl i hi => exact .refl i hi
    | step hi hj he tail ih => exact .step hi hj (by simpa [cover,CSTTT.POS04.Assigned.RawPackageCover.adjacent] using he) ih

theorem compatibility_iff (a : CSTTT.POS04.Assigned.Assignment) (s : CSTTT.POS04.Assigned.RawStageMap) (r : CSTTT.POS04.Assigned.RawPackageCover) :
    EdgeCompatible (cover r) (mappedLocal language a (stage s) r.scopes) ↔ CSTTT.POS04.Assigned.EdgeCompatible a s r := by
  simp only [EdgeCompatible,CSTTT.POS04.Assigned.EdgeCompatible,cover,decide_eq_true_eq,mapped_eq,CSTTT.POS04.Assigned.RawPackageCover.adjacent]

theorem generic_global_eq_legacy (a : CSTTT.POS04.Assigned.Assignment) (s : CSTTT.POS04.Assigned.RawStageMap)
    (r : CSTTT.POS04.Assigned.RawPackageCover) (tag : Tag) (hc : CSTTT.POS04.Assigned.CoverCheck r tag)
    (he : CSTTT.POS04.Assigned.EdgeCompatible a s r) :
    glued (cover r) (mappedLocal language a (stage s) r.scopes) = CSTTT.POS04.Assigned.assembledAssignment a s r tag hc := by
  funext k
  obtain ⟨c,hk⟩ := hc.covers k
  rw [glued_restricts (cover r) _ (cover_checked r tag hc) ((compatibility_iff a s r).mpr he) c k hk,
    mapped_eq]
  exact (CSTTT.POS04.Assigned.assembled_restricts a s r tag hc he c k hk).symm

theorem canonical_stage_total (tag : Tag) :
    StageTotal language CSTTT.POS04.Assigned.canonical (stage CSTTT.POS04.Assigned.canonicalStage) (CSTTT.POS04.Assigned.arrivalCover tag).scopes :=
  total_of_legacy _ _ _ (CSTTT.POS04.Assigned.canonical_stage_total _)
theorem canonical_cover_checked (tag : Tag) : CoverCheck (cover (CSTTT.POS04.Assigned.arrivalCover tag)) :=
  cover_checked _ tag (CSTTT.POS04.Assigned.arrival_cover_check tag)
theorem canonical_compatible (tag : Tag) :
    EdgeCompatible (cover (CSTTT.POS04.Assigned.arrivalCover tag))
      (mappedLocal language CSTTT.POS04.Assigned.canonical (stage CSTTT.POS04.Assigned.canonicalStage) (CSTTT.POS04.Assigned.arrivalCover tag).scopes) :=
  (compatibility_iff _ _ _).mpr (CSTTT.POS04.Assigned.canonical_edge_compatibility tag)
theorem canonical_global (tag : Tag) :
    glued (cover (CSTTT.POS04.Assigned.arrivalCover tag))
      (mappedLocal language CSTTT.POS04.Assigned.canonical (stage CSTTT.POS04.Assigned.canonicalStage) (CSTTT.POS04.Assigned.arrivalCover tag).scopes) = CSTTT.POS04.Assigned.canonical := by
  funext k
  obtain ⟨c,hk⟩ := (CSTTT.POS04.Assigned.arrival_cover_check tag).covers k
  rw [glued_restricts _ _ (canonical_cover_checked tag) (canonical_compatible tag) c k hk,mapped_eq]
  exact CSTTT.POS04.Assigned.canonical_mapped_agrees _ c k hk

/-- The 160 legacy slots continue to reference exactly the shared cells. -/
theorem views_and_references :
    coordinates.length = 160 ∧ coordinates.Nodup ∧
    (∀ x : Coordinate, ∀ ref ∈ primitiveRefs x.tag x.clause,
      CSTTT.POS04.Assigned.resolveRef x.tag ref ∈ CSTTT.POS04.Assigned.viewScope x) :=
  ⟨CSTTT.POS04.Assigned.views_160.1,CSTTT.POS04.Assigned.views_160.2.1,CSTTT.POS04.Assigned.view_references_resolve⟩
theorem references_of_legacy (a : CSTTT.POS04.Assigned.Assignment)
    (s : CSTTT.POS04.Assigned.RawStageMap) (r : CSTTT.POS04.Assigned.RawPackageCover)
    (h : CSTTT.POS04.Assigned.MapTotal a s r) :
    ReferenceCheck language (stage s) (stage CSTTT.POS04.Assigned.canonicalStage) r.scopes := by
  intro c k hk
  obtain ⟨arrow,ha,he,_⟩ := h c k hk
  simp [stage,ha,CSTTT.POS04.Assigned.canonicalStage,he]

theorem typed_total_legacy_iff (a : CSTTT.POS04.Assigned.Assignment)
    (s : CSTTT.POS04.Assigned.RawStageMap) (r : CSTTT.POS04.Assigned.RawPackageCover) :
    CSTTT.POS04.Assigned.MapTotal a s r ↔ StageTotal language a (stage s) r.scopes ∧
      ReferenceCheck language (stage s) (stage CSTTT.POS04.Assigned.canonicalStage) r.scopes := by
  constructor
  · intro h
    exact ⟨total_of_legacy a s r h,references_of_legacy a s r h⟩
  · rintro ⟨ht,hr⟩
    apply (total_legacy_iff a s r).mpr
    refine ⟨ht,?_⟩
    intro c k hk arrow ha
    have he := hr c k hk
    simpa [stage,ha,CSTTT.POS04.Assigned.canonicalStage] using he

theorem coordinate_guard : ¬ ReferenceCheck language
    (stage CSTTT.POS04.Assigned.wrongCoordinateStage) (stage CSTTT.POS04.Assigned.canonicalStage)
    (CSTTT.POS04.Assigned.arrivalCover .target).scopes := by
  intro h
  have he := h .c2 (.rows .target) (by decide)
  change some (CSTTT.POS04.Assigned.Cell.rows .target) = some (.rows .source) at he
  contradiction

theorem dependencies_checked (r : CSTTT.POS04.Assigned.RawPackageCover)
    (tag : Tag) (hc : CSTTT.POS04.Assigned.CoverCheck r tag) :
    DependenciesCovered (cover r) (CSTTT.POS04.Assigned.clauseScope tag) := hc.dependencies

theorem dropped_map_guard : ¬ StageTotal language CSTTT.POS04.Assigned.canonical
    (stage CSTTT.POS04.Assigned.droppedStage) (CSTTT.POS04.Assigned.arrivalCover .target).scopes :=
  missing_arrow_rejected language (i := .c2) (k := .rows .target) (by decide) rfl

theorem changed_value_guard : ¬ ValuePreserving language CSTTT.POS04.Assigned.canonical
    (stage CSTTT.POS04.Assigned.changedValueStage) (stage CSTTT.POS04.Assigned.canonicalStage)
    (CSTTT.POS04.Assigned.arrivalCover .target).scopes :=
  fun h => CSTTT.POS04.Assigned.changed_map_not_preserving ((values_legacy_iff _ _ _).mp h)

theorem overlap_guard : ¬ EdgeCompatible (cover (CSTTT.POS04.Assigned.arrivalCover .target))
    (mappedLocal language CSTTT.POS04.Assigned.canonical
      (stage CSTTT.POS04.Assigned.changedValueStage) (CSTTT.POS04.Assigned.arrivalCover .target).scopes) :=
  fun h => CSTTT.POS04.Assigned.incompatible_overlap_rejected ((compatibility_iff _ _ _).mp h)

theorem dependency_scope_guard : ¬ DependenciesCovered
    (cover CSTTT.POS04.Assigned.missingScopeCover) (CSTTT.POS04.Assigned.clauseScope .target) :=
  missing_dependency_scope_rejected _ _ (i := .c2) (k := .rows .target) (by decide) (by decide)

/-- Disable just adjacency; keep indices, scopes, assignments and stage fixed. -/
def disconnectedCover : RawCover Clause CSTTT.POS04.Assigned.Cell :=
  { cover (CSTTT.POS04.Assigned.arrivalCover .target) with adjacent := fun _ _ => false }
theorem adjacency_guard : ¬ CoverCheck disconnectedCover := by
  apply disconnected_cover_rejected disconnectedCover (i := .c1) (j := .c2) (k := .rows .target)
    (by decide) (by decide) (by decide)
  intro a b ha hb he
  contradiction

/-- Delete only the covering enumeration; do not alter scopes or adjacency. -/
def unenumeratedCover : RawCover Clause CSTTT.POS04.Assigned.Cell :=
  { cover (CSTTT.POS04.Assigned.arrivalCover .target) with indices := [] }
theorem enumeration_guard : ¬ CoverCheck unenumeratedCover :=
  uncovered_cell_rejected unenumeratedCover (.rows .target) (by simp [unenumeratedCover])

/-- One missing primitive cannot be replaced by a canonical decoder default. -/
theorem missing_any_cell_guard (k : CSTTT.POS04.Assigned.Cell) :
    ¬ Complete CSTTT.POS04.Assigned.primitiveCells (put CSTTT.POS04.Assigned.canonical k none) :=
  missing_rejected _ _ k (CSTTT.POS04.Assigned.primitive_cells_complete k)

end CSTTT.TargetTheory.GenericHandoff.POS04Adapter
