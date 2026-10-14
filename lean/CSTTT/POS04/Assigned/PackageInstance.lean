import CSTTT.POS04.Assigned.PackageAssembly
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.PackageTheory

/-- Enumerate the typed primitive constructors, expanding every tagged family
on the two declared tags. This is not a list of copied logical slots. -/
def primitiveCells : List Cell :=
  [.rows .source,.rows .target,.lower .source,.lower .target,
   .positions,.hazards,.policy,.prototypes,.publishedP,.publishedC,.publishedU,.publishedM,.audit,
   .channels,.protocols .source,.protocols .target,.ticks .source,.ticks .target,.interface,
   .joint .source,.joint .target,.resources .source,.resources .target,.maintenance,
   .histories,.eventTable,.realized,.receiverInput,.routeTable,.writers]
theorem primitive_cells_complete (k : Cell) : k ∈ primitiveCells := by
  cases k <;> first | decide | (rename_i tag; cases tag <;> decide)

/-- Decoder-dependency closure of the star cover: C1's root view retains
all shared primitive cells; leaves retain their clause dependency scopes.
The 160 L5 logical coordinates remain views onto these same primitive cells. -/
def arrivalCover (tag : Tag) : RawPackageCover :=
  ⟨.c1,(fun c => if c = .c1 then none else some .c1),
    (fun c => if c = .c1 then 0 else 1),
    (fun c => if c = .c1 then primitiveCells else clauseScope tag c)⟩

theorem arrival_cover_check (tag : Tag) : CoverCheck (arrivalCover tag) tag := by
  constructor
  · rfl
  · intro c hc; change c ≠ .c1 at hc; exact ⟨.c1,by simp [arrivalCover,hc]⟩
  · intro c p hp
    by_cases hc : c = .c1
    · simp [arrivalCover,hc] at hp
    · have he : p = .c1 := by simpa [arrivalCover,hc] using hp.symm
      subst p
      simp [arrivalCover,hc]
  · intro k; exact ⟨.c1,primitive_cells_complete k⟩
  · intro i j k hi hj
    have hr : k ∈ (arrivalCover tag).scopes .c1 := primitive_cells_complete k
    by_cases hir : i = .c1
    · subst i
      by_cases hjr : j = .c1
      · subst j; exact .refl _ hr
      · exact .step hr hj (Or.inr (by simp [arrivalCover,hjr])) (.refl j hj)
    · by_cases hjr : j = .c1
      · subst j
        exact .step hi hr (Or.inl (by simp [arrivalCover,hir])) (.refl _ hr)
      · exact .step hi hr (Or.inl (by simp [arrivalCover,hir]))
          (.step hr hj (Or.inr (by simp [arrivalCover,hjr])) (.refl j hj))
  · intro c k hk
    by_cases hc : c = .c1
    · subst c; exact primitive_cells_complete k
    · simpa [arrivalCover,hc] using hk

theorem translated_canonical_value (k : Cell) : translatedValue k (canonicalValue (swapCell k)) = canonicalValue k := by
  cases k <;> try rfl
  case protocols tag =>
    cases tag <;> change ProtocolData.mk _ _ _ = ProtocolData.mk _ _ _ <;>
      congr 1 <;> funext p <;> cases p <;> rfl
  case resources tag => cases tag <;> rfl

theorem canonical_stage_total (r : RawPackageCover) : MapTotal canonical canonicalStage r := by
  intro c k _
  exact ⟨⟨swapCell k,fun v => some (translatedValue k v)⟩,rfl,rfl,rfl,by intro v; simp⟩
theorem canonical_stage_values (r : RawPackageCover) : ValuePreserving canonical canonicalStage r := by
  intro c k hk
  simp only [mappedLocal,hk,if_true,canonicalStage,canonical,Option.bind_some,Option.map_some]

theorem canonical_mapped_agrees (r : RawPackageCover) (c : Clause) (k : Cell) (hk : k ∈ r.scopes c) :
    mappedLocal canonical canonicalStage r c k = canonical k := by
  rw [canonical_stage_values r c k hk]
  simp only [canonical,Option.map_some,translated_canonical_value]

theorem canonical_assigned_package (tag : Tag) : AssignedPackagePass canonical tag := by
  intro c
  cases c with
  | c1 => exact (canonical_c123 tag).1
  | c2 => exact (canonical_c123 tag).2.1
  | c3 => exact (canonical_c123 tag).2.2
  | c4 => exact (canonical_c457 tag).1
  | c5 => exact (canonical_c457 tag).2.1
  | c6 => exact canonical_accept6 tag
  | c7 => exact (canonical_c457 tag).2.2
  | c8 => exact c8_canonical_accepts tag

theorem canonical_package_equivalence (tag : Tag) : AssignedPackagePass canonical tag ↔ PackagePass .funded tag := by
  constructor
  · intro h
    exact ⟨coordinates_complete,(c1_canonical_equivalence tag).mp (h .c1),
      (c2_canonical_equivalence tag).mp (h .c2),(c3_canonical_equivalence tag).mp (h .c3),
      (c4_canonical_equivalence tag).mp (h .c4),(c5_canonical_equivalence tag).mp (h .c5),
      (canonical_c6_equivalence tag).mp (h .c6),(c7_canonical_equivalence tag).mp (h .c7),
      (c8_canonical_equivalence tag).mp (h .c8)⟩
  · intro _; exact canonical_assigned_package tag

theorem canonical_target_locals (tag : Tag) : TargetLocalChecks canonical canonicalStage (arrivalCover tag) tag := by
  intro c
  apply (clause_accept_locality tag c (fun k hk =>
    canonical_mapped_agrees _ c k ((arrival_cover_check tag).dependencies c k hk))).mpr
  exact canonical_assigned_package tag c

theorem canonical_edge_compatibility (tag : Tag) : EdgeCompatible canonical canonicalStage (arrivalCover tag) := by
  intro i j k _ hi hj
  rw [canonical_mapped_agrees _ i k hi,canonical_mapped_agrees _ j k hj]

theorem pos04_staged_package :
    AssembledPackage canonical canonicalStage (arrivalCover .target) .target (arrival_cover_check .target) :=
  stagedHeterogeneousPackageAssembly_generic canonical canonicalStage (arrivalCover .target) .target
    (arrival_cover_check .target) (canonical_assigned_package .source)
    (canonical_stage_total _) (canonical_stage_values _) (canonical_target_locals _) (canonical_edge_compatibility _)

theorem pos04_assembled_assignment_canonical :
    assembledAssignment canonical canonicalStage (arrivalCover .target) .target (arrival_cover_check .target) = canonical := by
  funext k
  rw [pos04_staged_package.restrictions .c1 k (primitive_cells_complete k)]
  exact canonical_mapped_agrees _ _ _ (primitive_cells_complete k)

theorem pos04_arrival_package_L8 :
    AssignedPackagePass
      (assembledAssignment canonical canonicalStage (arrivalCover .target) .target (arrival_cover_check .target)) .target ∧
    PackagePass .funded .target :=
  ⟨pos04_staged_package.accepted,(canonical_package_equivalence _).mp (canonical_assigned_package _)⟩

end CSTTT.POS04.Assigned
