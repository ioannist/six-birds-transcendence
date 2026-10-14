import CSTTT.Targets.GenericHandoff.DispatchedComposition
import CSTTT.Targets.GenericHandoff.POS04DispatchedStage

/-! Exact arbitrary-partial two-stage POS04 package adapter. Both raw tag
translations execute; the resulting primitive global is the original
assignment by the existing typed exchange involution. This is an inhabited
closed-package pipeline, not a two-hop Temporal-FIACH model. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04DispatchedComposition
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH
set_option maxRecDepth 16384
set_option maxHeartbeats 16000000

def raw := DispatchedComposition.compose POS04DispatchedStage.raw POS04DispatchedStage.raw

theorem target_image_twice (a : CSTTT.POS04.Assigned.Assignment) :
    DispatchedPackage.global raw a = image (image a) := by
  dsimp only [raw]
  rw [DispatchedComposition.target_equation]
  rw [POS04DispatchedStage.global_eq_image,POS04DispatchedStage.global_eq_image]

theorem target_equation (a : CSTTT.POS04.Assigned.Assignment) :
    DispatchedPackage.global raw a = a :=
  (target_image_twice a).trans (exchange_assignment_involution a)

theorem local_equation (a : CSTTT.POS04.Assigned.Assignment) (c : ClauseDispatcher.Kind) :
    mappedLocal raw.language a raw.stage raw.cover.scopes c =
      mappedLocal POS04DispatchedStage.raw.language (image a) POS04DispatchedStage.raw.stage
        POS04DispatchedStage.cover.scopes c := by
  dsimp only [raw]
  rw [DispatchedComposition.local_equation,POS04DispatchedStage.global_eq_image]
  rfl

theorem mapped_cell (a : CSTTT.POS04.Assigned.Assignment) (c : ClauseDispatcher.Kind) (k : Cell)
    (hk : k ∈ raw.cover.scopes c) :
    mappedLocal raw.language a raw.stage raw.cover.scopes c k = a k := by
  rw [local_equation]
  exact (congrFun (POS04DispatchedStage.mapped_eq (image a) c) k).trans
    ((congrFun (POS04Adapter.mapped_eq (image a) canonicalStage (arrivalCover .target) (POS04Dispatcher.clause c)) k).trans
      ((image_mapped (image a) (POS04Dispatcher.clause c) k hk).trans (congrFun (exchange_assignment_involution a) k)))

theorem edges (a : CSTTT.POS04.Assigned.Assignment) :
    EdgeCompatible raw.cover (mappedLocal raw.language a raw.stage raw.cover.scopes) := by
  intro i j k ha hi hj
  rw [mapped_cell a i k hi,mapped_cell a j k hj]

theorem total_iff (a : CSTTT.POS04.Assigned.Assignment) :
    StageTotal raw.language a raw.stage raw.cover.scopes ↔ CSTTT.POS04.Assigned.Complete primitiveCells a := by
  constructor
  · intro ht k hk
    have h := mapped_complete raw.language ht ClauseDispatcher.Kind.c1 k (primitive_cells_complete k)
    rw [mapped_cell a .c1 k (primitive_cells_complete k)] at h
    exact h
  · intro hc
    apply GlobalStageComposition.total POS04DispatchedStage.raw.language POS04DispatchedStage.raw.language
      POS04DispatchedStage.raw.stage POS04DispatchedStage.raw.stage POS04DispatchedStage.cover a raw.cover.scopes
      POS04DispatchedStage.cover_check ((POS04DispatchedStage.total_iff a).mpr hc)
    change StageTotal POS04DispatchedStage.raw.language (DispatchedPackage.global POS04DispatchedStage.raw a)
      POS04DispatchedStage.raw.stage POS04DispatchedStage.cover.scopes
    rw [POS04DispatchedStage.global_eq_image]
    apply (POS04DispatchedStage.total_iff (image a)).mpr
    intro k hk
    have h := hc (swapCell k) (primitive_cells_complete _)
    cases ha : a (swapCell k) with
    | none => simp [ha] at h
    | some value => simp [image,exchangeAssignment,ha]

theorem local_iff_target (a : CSTTT.POS04.Assigned.Assignment) :
    PackageEngine.LocalChecks raw.language a raw.stage raw.cover (fun c => (raw.clauses.rule c).accept) ↔
      (POS04Dispatcher.package .target).accept a := by
  have h := PackageEngine.local_checks_iff_global raw.language a raw.stage raw.cover
    (fun c => (raw.clauses.rule c).accept) (fun c => (raw.clauses.rule c).scope)
    (fun c x y hx => (raw.clauses.rule c).locality hx)
    POS04DispatchedStage.cover_check POS04DispatchedStage.scope_check (edges a)
  change _ ↔ (POS04Dispatcher.package .target).accept (DispatchedPackage.global raw a) at h
  rw [target_equation] at h
  exact h

theorem valid_iff (a : CSTTT.POS04.Assigned.Assignment) :
    DispatchedPackage.Valid raw a ↔
      CSTTT.POS04.Assigned.Complete primitiveCells a ∧ AssignedPackagePass a .target := by
  constructor
  · intro h
    exact ⟨(total_iff a).mp h.2.2.1,(POS04Dispatcher.package_accept_iff a .target).mp
      ((local_iff_target a).mp h.2.2.2.2.2.2.1)⟩
  · rintro ⟨hc,hp⟩
    exact ⟨POS04DispatchedStage.cover_check,POS04DispatchedStage.scope_check,(total_iff a).mpr hc,
      fun _ _ _ => rfl,fun _ _ _ => rfl,
      GlobalStageComposition.reference_coverage _ _ _ (fun _ _ _ => rfl),
      (local_iff_target a).mpr ((POS04Dispatcher.package_accept_iff a .target).mpr hp),edges a⟩

theorem positive : DispatchedPackage.Valid raw canonical := by
  apply DispatchedComposition.valid
  · exact POS04DispatchedStage.positive
  · rw [POS04DispatchedStage.global_eq_image,image_canonical]
    exact POS04DispatchedStage.positive

theorem target_acceptance_iff (a : CSTTT.POS04.Assigned.Assignment) :
    raw.clauses.accept (DispatchedPackage.global raw a) ↔ AssignedPackagePass a .target := by
  rw [target_equation]
  exact POS04Dispatcher.package_accept_iff a .target

theorem missing_cell_output (a : CSTTT.POS04.Assigned.Assignment) (k : Cell) :
    DispatchedPackage.global raw (CSTTT.POS04.Assigned.put a k none) k = none := by
  rw [target_equation]
  simp

theorem deleted_C_no_target_readout :
    ¬ raw.clauses.accept (DispatchedPackage.global raw (CSTTT.POS04.Assigned.put canonical .publishedC none)) := by
  rw [target_equation]
  exact POS04Dispatcher.deleted_C .target

/-- Cross-clause prefix selection is essential for this actual typed reader. -/
theorem row_source_outside_c2 : Cell.rows .source ∉ POS04DispatchedStage.cover.scopes .c2 := by decide

theorem row_prefix_is_c1 :
    firstCover POS04DispatchedStage.cover.scopes (Cell.rows .source) POS04DispatchedStage.cover.indices = some .c1 := by decide

theorem same_clause_scope_link_false :
    ¬ StageComposition.ScopeLink POS04DispatchedStage.raw.language POS04DispatchedStage.raw.stage
      POS04DispatchedStage.cover.scopes POS04DispatchedStage.cover.scopes := by
  intro h
  have hs := h ClauseDispatcher.Kind.c2 (Cell.rows .target) (by decide)
    (show GenericHandoff.CellArrow POS04DispatchedStage.raw.language (Cell.rows .target) from
      ⟨.rows .source,fun value => some (translatedValue (.rows .target) value)⟩) rfl
  exact row_source_outside_c2 hs

theorem same_clause_row_missing (a : CSTTT.POS04.Assigned.Assignment) :
    mappedLocal (StageComposition.language POS04DispatchedStage.raw.language POS04DispatchedStage.raw.language) a
      (StageComposition.stage POS04DispatchedStage.raw.language POS04DispatchedStage.raw.language
        POS04DispatchedStage.raw.stage POS04DispatchedStage.raw.stage POS04DispatchedStage.cover.scopes)
      POS04DispatchedStage.cover.scopes .c2 (.rows .target) = none := by
  exact StageComposition.missing_middle_readout POS04DispatchedStage.raw.language POS04DispatchedStage.raw.language
    POS04DispatchedStage.raw.stage POS04DispatchedStage.raw.stage POS04DispatchedStage.cover.scopes
    a POS04DispatchedStage.cover.scopes ClauseDispatcher.Kind.c2 (Cell.rows .target)
    (show GenericHandoff.CellArrow POS04DispatchedStage.raw.language (Cell.rows .target) from
      ⟨.rows .source,fun value => some (translatedValue (.rows .target) value)⟩) rfl row_source_outside_c2

theorem selected_row_equation (a : CSTTT.POS04.Assigned.Assignment) :
    mappedLocal raw.language a raw.stage raw.cover.scopes .c2 (.rows .target) = a (.rows .target) :=
  mapped_cell a .c2 (.rows .target) (by decide)

theorem same_clause_not_equivalent :
    mappedLocal (StageComposition.language POS04DispatchedStage.raw.language POS04DispatchedStage.raw.language) canonical
      (StageComposition.stage POS04DispatchedStage.raw.language POS04DispatchedStage.raw.language
        POS04DispatchedStage.raw.stage POS04DispatchedStage.raw.stage POS04DispatchedStage.cover.scopes)
      POS04DispatchedStage.cover.scopes .c2 (.rows .target) ≠
    mappedLocal raw.language canonical raw.stage raw.cover.scopes .c2 (.rows .target) := by
  rw [same_clause_row_missing,selected_row_equation]
  intro h
  change none = some (canonicalValue (.rows .target)) at h
  contradiction

end CSTTT.TargetTheory.GenericHandoff.POS04DispatchedComposition
