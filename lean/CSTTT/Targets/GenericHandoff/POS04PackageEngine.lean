import CSTTT.Targets.GenericHandoff.PackageEngine
import CSTTT.Targets.GenericHandoff.POS04Substrate
import CSTTT.Targets.ComputedFIACH.PackageImage

/-! Exact all-eight-clause POS-04 interpretation of the generic gluing engine.
This is a family adapter: the closed polymorphic eight-schema dispatcher is
still required before this can count as completed generic RawHandoff binding.
Every local/global acceptance here uses assigned primitives, not verdict fields.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04PackageEngine
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TargetTheory.ComputedFIACH

abbrev cover := POS04Adapter.cover (arrivalCover .target)
abbrev lang := POS04Adapter.language
abbrev stage := POS04Adapter.stage canonicalStage

def rules (c : Clause) (a : CSTTT.POS04.Assigned.Assignment) : Prop := clauseAccept a .target c

theorem locality : PackageEngine.Locality rules (clauseScope .target) :=
  fun c a b h => clause_accept_locality (a := a) (b := b) .target c h

theorem global_eq_image (a : CSTTT.POS04.Assigned.Assignment) :
    PackageEngine.global lang a stage cover = image a := by
  exact (POS04Adapter.generic_global_eq_legacy _ _ _ .target
    (arrival_cover_check .target) (image_edges a)).trans (image_eq_assembled a).symm

/-- Full P equivalence, including missing primitives, via CONSTRUCTED locals,
checked totality and actual clause algorithms. Nothing is replaced by a stored
acceptance field or an equality of canonical truth values. -/
def P (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  StageTotal lang a stage cover.scopes ∧ PackageEngine.LocalChecks lang a stage cover rules

theorem total_iff_complete (a : CSTTT.POS04.Assigned.Assignment) :
    StageTotal lang a stage cover.scopes ↔ CSTTT.POS04.Assigned.Complete primitiveCells a := by
  constructor
  · intro h k hk
    have ht := h .c1 (swapCell k) (primitive_cells_complete _)
    rcases ht with ⟨arrow,harrow,hpresent,_⟩
    have ha : stage .c1 (swapCell k) = some
        (⟨swapCell (swapCell k),(fun v => some (translatedValue (swapCell k) v))⟩ : CellArrow lang (swapCell k)) := by
      rfl
    have he := Option.some.inj (harrow.symm.trans ha)
    cases he
    change (a (swapCell (swapCell k))).isSome = true at hpresent
    rw [CSTTT.POS04.Assigned.swap_cell_involution] at hpresent
    exact hpresent
  · intro h
    exact POS04Adapter.total_of_legacy _ _ _ (image_total h)

theorem p_iff (a : CSTTT.POS04.Assigned.Assignment) : P a ↔ PackageLane a := by
  unfold P
  rw [total_iff_complete]
  rw [PackageEngine.local_checks_iff_global lang a stage cover rules (clauseScope .target)
    locality (POS04Adapter.canonical_cover_checked .target)
    (POS04Adapter.dependencies_checked _ .target (arrival_cover_check .target))
    ((POS04Adapter.compatibility_iff _ _ _).mpr (image_edges a)),global_eq_image]
  exact (package_lane_iff a).symm

theorem constructs (a : CSTTT.POS04.Assigned.Assignment) (h : P a) :
    (∀ c k, k ∈ cover.scopes c → PackageEngine.global lang a stage cover k =
      CSTTT.TargetTheory.GenericHandoff.mappedLocal lang a stage cover.scopes c k) ∧
    (∀ k, (PackageEngine.global lang a stage cover k).isSome = true) ∧
    AssignedPackagePass (PackageEngine.global lang a stage cover) .target :=
  PackageEngine.constructs lang a stage cover rules (clauseScope .target) locality
    (POS04Adapter.canonical_cover_checked .target)
    (POS04Adapter.dependencies_checked _ .target (arrival_cover_check .target)) h.1 h.2
    ((POS04Adapter.compatibility_iff _ _ _).mpr (image_edges a))

theorem positive : P canonical := (p_iff _).mpr package_lane_positive

theorem deleted_primitive (a : CSTTT.POS04.Assigned.Assignment) (k : Cell) :
    ¬ P (CSTTT.POS04.Assigned.put a k none) :=
  fun h => package_lane_missing k ((p_iff _).mp h)

/-- All published package-breaking assignment adapters transfer through the
SAME defined stage and gluing engine, not just deletion or canonical truth. -/
theorem package_controls (v : PackageControl) :
    ¬ P (exchangeAssignment (packageControl v)) := by
  intro hp
  have ha := (constructs _ hp).2.2
  rw [global_eq_image] at ha
  change AssignedPackagePass (exchangeAssignment (exchangeAssignment (packageControl v))) .target at ha
  rw [exchange_assignment_involution] at ha
  exact m3b_package_controls_reject v ha

end CSTTT.TargetTheory.GenericHandoff.POS04PackageEngine
