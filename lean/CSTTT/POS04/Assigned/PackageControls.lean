import CSTTT.POS04.Assigned.PackageGuards
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.PackageTheory

/-- A namespace exchange, derived from the declared typed value recipe.
Used to feed existing target interventions through the actual source map. -/
def exchangeAssignment (a : Assignment) : Assignment :=
  fun k => (a (swapCell k)).map (translatedValue k)
theorem swap_tag_involution (t : Tag) : swapTag (swapTag t) = t := by cases t <;> rfl
theorem swap_provenance_involution (p : ProvenanceOwner) : swapProvenance (swapProvenance p) = p := by cases p <;> rfl

theorem exchange_assignment_involution (a : Assignment) : exchangeAssignment (exchangeAssignment a) = a := by
  funext k
  cases k
  all_goals try (rename_i tag; cases tag)
  all_goals simp [exchangeAssignment,swapCell,translatedValue,swap_tag_involution,
      swap_provenance_involution,Option.map_map,Function.comp_def]
  all_goals simp only [swapTag]
  all_goals first | rfl | (change Option.map id _ = _; exact Option.map_id_apply)

theorem mapped_exchange_agrees (a : Assignment) (r : RawPackageCover) (c : Clause) (k : Cell)
    (hk : k ∈ r.scopes c) :
    mappedLocal (exchangeAssignment a) canonicalStage r c k = a k := by
  have he := congrFun (exchange_assignment_involution a) k
  simp only [mappedLocal,hk,if_true,canonicalStage,Option.bind_some]
  change ((exchangeAssignment a) (swapCell k)).bind (fun v => some (translatedValue k v)) = a k
  have hm := (Option.map_eq_bind (x := exchangeAssignment a (swapCell k)) (f := translatedValue k)).symm
  simp only [Function.comp_def] at hm
  exact hm.trans he

/-- The 14 package-breaking M3b interventions are applied to primitive cells,
exchanged to the source namespace and mapped through the same positive stage.
Locality identifies each computed target local with its actual mutated view. -/
theorem m3b_mapped_package_controls_reject (v : PackageControl) :
    ¬ TargetLocalChecks (exchangeAssignment (packageControl v)) canonicalStage (arrivalCover .target) .target := by
  intro h
  apply m3b_package_controls_reject v
  intro c
  apply (clause_accept_locality .target c (fun k hk =>
    mapped_exchange_agrees _ _ c k ((arrival_cover_check .target).dependencies c k hk))).mp
  exact h c

/-- Acceptance and gluing produce the prescribed global. They cannot
produce any of the package-breaking transformed assignments. -/
theorem m3b_no_assembled_control (v : PackageControl) (source : Assignment) (stage : RawStageMap)
    (r : RawPackageCover) (hc : CoverCheck r .target)
    (he : assembledAssignment source stage r .target hc = packageControl v) :
    ¬ AssembledPackage source stage r .target hc := by
  intro h
  have hp := h.accepted
  rw [he] at hp
  exact m3b_package_controls_reject v hp

end CSTTT.POS04.Assigned
