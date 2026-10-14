import CSTTT.Targets.ComputedFIACH.Decisions

/-! G6_lane_spec.md:26–102. The target image and its acceptance are defined
from the assignment. Exact equality with G2c's constructed global holds even
for partial assignments; no acceptance proof is used to establish gluing. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

abbrev image (a : Assignment) := exchangeAssignment a

theorem image_mapped (a : Assignment) (c : Clause) (k : Cell)
    (hk : k ∈ (arrivalCover .target).scopes c) :
    mappedLocal a canonicalStage (arrivalCover .target) c k = image a k := by
  have h := mapped_exchange_agrees (exchangeAssignment a) (arrivalCover .target) c k hk
  simpa only [exchange_assignment_involution] using h

theorem image_values (a : Assignment) : ValuePreserving a canonicalStage (arrivalCover .target) := by
  intro c k hk; exact image_mapped a c k hk

theorem image_edges (a : Assignment) : EdgeCompatible a canonicalStage (arrivalCover .target) := by
  intro i j k _ hi hj
  rw [image_mapped a i k hi,image_mapped a j k hj]

theorem image_eq_assembled (a : Assignment) :
    image a = assembledAssignment a canonicalStage (arrivalCover .target) .target
      (arrival_cover_check .target) := by
  funext k
  rw [assembled_restricts a canonicalStage (arrivalCover .target) .target
    (arrival_cover_check .target) (image_edges a) .c1 k (primitive_cells_complete k)]
  exact (image_mapped a .c1 k (primitive_cells_complete k)).symm

instance (a : Assignment) : Decidable (Complete primitiveCells a) := by
  unfold Complete; infer_instance

def packageLaneCheck (a : Assignment) : Bool :=
  decide (Complete primitiveCells a) && packageCheck (image a) .target

def PackageLane (a : Assignment) : Prop := packageLaneCheck a = true

theorem package_lane_iff (a : Assignment) :
    PackageLane a ↔ Complete primitiveCells a ∧ AssignedPackagePass (image a) .target := by
  simp [PackageLane,packageLaneCheck,package_check_iff]

theorem image_total {a : Assignment} (h : Complete primitiveCells a) :
    MapTotal a canonicalStage (arrivalCover .target) := by
  intro c k _
  exact ⟨⟨swapCell k,fun v => some (translatedValue k v)⟩,rfl,rfl,
    h _ (primitive_cells_complete _),by intro v; simp⟩

theorem package_lane_assembles {a : Assignment} (h : PackageLane a) :
    MapTotal a canonicalStage (arrivalCover .target) ∧
    ValuePreserving a canonicalStage (arrivalCover .target) ∧
    EdgeCompatible a canonicalStage (arrivalCover .target) ∧
    (∀ c k, k ∈ (arrivalCover .target).scopes c →
      image a k = mappedLocal a canonicalStage (arrivalCover .target) c k) ∧
    AssignedPackagePass (assembledAssignment a canonicalStage (arrivalCover .target)
      .target (arrival_cover_check .target)) .target := by
  obtain ⟨hc,hp⟩ := (package_lane_iff a).mp h
  exact ⟨image_total hc,image_values a,image_edges a,
    fun c k hk => (image_mapped a c k hk).symm,by rw [← image_eq_assembled]; exact hp⟩

theorem image_canonical : image canonical = canonical := by
  funext k
  simp only [image,exchangeAssignment,canonical,Option.map_some,translated_canonical_value]

theorem package_lane_positive : PackageLane canonical := by
  apply (package_lane_iff _).mpr
  exact ⟨canonical_complete _,by rw [image_canonical]; exact canonical_assigned_package .target⟩

theorem package_lane_missing {a : Assignment} (k : Cell) :
    ¬ PackageLane (put a k none) := by
  intro h
  exact missing_cell_rejected primitiveCells a k (primitive_cells_complete k)
    ((package_lane_iff _).mp h).1
end CSTTT.TargetTheory.ComputedFIACH
