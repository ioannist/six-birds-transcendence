import CSTTT.POS04.Assigned.PackageInstance
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.PackageTheory

/-- Drop one required arrow, not a stored totality flag. -/
def droppedStage : RawStageMap := ⟨fun c k =>
  if c = .c2 ∧ k = .rows .target then none else canonicalStage.arrows c k⟩
theorem dropped_map_not_total : ¬ MapTotal canonical droppedStage (arrivalCover .target) := by
  intro h
  obtain ⟨arrow,he,_⟩ := h .c2 (.rows .target) (by decide)
  change none = some arrow at he
  contradiction

/-- Broken primitive-value operation on C2's shared hazard table. The input
cell remains present and the operation remains total, but values change. -/
def changedValueStage : RawStageMap := ⟨fun c k =>
  if h : c = .c2 ∧ k = .hazards then
    h.2.symm ▸ some (⟨.hazards,fun _ => some (fun _ => false)⟩ : CellArrow .hazards)
  else canonicalStage.arrows c k⟩

theorem changed_map_total : MapTotal canonical changedValueStage (arrivalCover .target) := by
  intro c k hk
  by_cases he : c = .c2 ∧ k = .hazards
  · obtain ⟨hc,hk⟩ := he; subst c; subst k
    exact ⟨⟨.hazards,fun _ => some (fun _ => false)⟩,rfl,rfl,rfl,by intro v; simp⟩
  · simpa [changedValueStage,he] using canonical_stage_total (arrivalCover .target) c k hk

theorem changed_map_not_preserving : ¬ ValuePreserving canonical changedValueStage (arrivalCover .target) := by
  intro h
  have he := h .c2 .hazards (by decide)
  have hd := congrArg (fun v : Option (Ambient → Bool) => v.map (fun f => f .p2w0)) he
  change some false = some true at hd
  contradiction

/-- Direct independent compatibility check fails on the actual overlap.
This method probe also fails value preservation; it is not advertised as an
isolated gluing-only ablation. -/
theorem incompatible_overlap_rejected : ¬ EdgeCompatible canonical changedValueStage (arrivalCover .target) := by
  intro h
  have he := h .c1 .c2 .hazards (Or.inr rfl) (primitive_cells_complete _) (by decide)
  have hd := congrArg (fun v : Option (Ambient → Bool) => v.map (fun f => f .p2w0)) he
  change some true = some false at hd
  contradiction

/-- Breaking only coordinate typing selects the wrong tagged row reference;
the raw row function is still the canonical one. -/
def wrongCoordinateStage : RawStageMap := ⟨fun c k =>
  if h : c = .c2 ∧ k = .rows .target then
    h.2.symm ▸ some (⟨.rows .target,fun v => some v⟩ : CellArrow (.rows .target))
  else canonicalStage.arrows c k⟩
theorem wrong_coordinate_rejected : ¬ MapTotal canonical wrongCoordinateStage (arrivalCover .target) := by
  intro h
  obtain ⟨arrow,he,hs,_⟩ := h .c2 (.rows .target) (by decide)
  change some (⟨.rows .target,fun v => some v⟩ : CellArrow (.rows .target)) = some arrow at he
  have ha := Option.some.inj he
  subst arrow
  change Cell.rows .target = .rows .source at hs
  contradiction

/-- Raw cover controls: every gate reads parent/rank/scopes, with no stale
adjacency. Root scoping is a dependency-closure view, not a new clause rule. -/
def wrongRootCover := { arrivalCover .target with root := Clause.c2 }
def cyclicParentCover := { arrivalCover .target with parent := fun _ => some .c1 }
def flatRankCover := { arrivalCover .target with rank := fun _ => 0 }
def missingScopeCover : RawPackageCover := { arrivalCover .target with scopes := (fun (c : Clause) =>
  if c = .c2 then ((clauseScope .target c).filter (fun k => decide (k ≠ Cell.rows .target)))
  else ((arrivalCover .target).scopes c)) }
theorem wrong_root_rejected : ¬ CoverCheck wrongRootCover .target := by
  intro h
  have he := h.rootParent
  change some Clause.c1 = none at he
  contradiction

theorem cyclic_parent_rejected : ¬ CoverCheck cyclicParentCover .target := by
  intro h
  have he := h.rootParent
  change some Clause.c1 = none at he
  contradiction
theorem flat_rank_rejected : ¬ CoverCheck flatRankCover .target := by
  intro h
  have he := h.decreasing .c2 .c1 rfl
  change (0 : Nat) < 0 at he
  omega
theorem missing_scope_rejected : ¬ CoverCheck missingScopeCover .target := by
  intro h
  have he := h.dependencies .c2 (.rows .target) (by decide)
  have hn : Cell.rows .target ∉ missingScopeCover.scopes .c2 := by decide
  exact hn he

/-- Any single real failed clause rejects the whole assigned package. -/
theorem package_rejects_clause {a : Assignment} {tag : Tag} {c : Clause}
    (h : ¬ clauseAccept a tag c) : ¬ AssignedPackagePass a tag := fun hp => h (hp c)
theorem source_assignment_guard (tag : Tag) : ¬ AssignedPackagePass (noRows canonical tag) tag :=
  package_rejects_clause (c := .c1) (c1_rows_guard tag)

/-- A broken raw row rejects the hard gate itself, without soft aggregation. -/
theorem package_hard_gate_guard (tag : Tag) : ¬ clauseGate (noRows canonical tag) tag .c1 := by
  intro h
  have he := h.2.2.2.2.2.2.2.1 .p1w0 .p2w1
  cases tag <;> change (0 : Nat) = 4 at he <;> contradiction

inductive PackageControl where
  | c1Table | c2Split | c3Profile | c4Expose | c5External | c6Future | c6Record
  | c7Aggregate | c7Transport | c7Uncoupled | c8Underfund | withdrawal | sourceAbsent | gap
  deriving DecidableEq, Repr

def packageControl : PackageControl → Assignment
  | .c1Table => negC1Table canonical | .c2Split => negC2Split canonical
  | .c3Profile => negC3Profile canonical | .c4Expose => expose4 canonical
  | .c5External => external5 canonical | .c6Future => futureBreak6 canonical
  | .c6Record => recordBreak6 canonical | .c7Aggregate => aggregate7 canonical
  | .c7Transport => transportBreak7 canonical | .c7Uncoupled => uncoupled7 canonical
  | .c8Underfund => underfund8 canonical | .withdrawal => withdraw8 (underfund8 canonical)
  | .sourceAbsent => sourceWithdrawn canonical | .gap => missingMix6 canonical

/-- M3b's package-breaking interventions, each via a selected real failed
clause on the same transformed assignment. This is not full cross-clause
side-effect attribution. NEG-C3-PROFILE still passes C3 but rejects C1. -/
theorem m3b_package_controls_reject (v : PackageControl) :
    ¬ AssignedPackagePass (packageControl v) .target := by
  cases v with
  | c1Table => exact package_rejects_clause (c := .c1) ((neg_c1_table_outcomes .target).1)
  | c2Split => exact package_rejects_clause (c := .c2) ((neg_c2_split_outcomes .target).2.1)
  | c3Profile => exact package_rejects_clause (c := .c1) ((neg_c3_profile_outcomes .target).1)
  | c4Expose => exact package_rejects_clause (c := .c4) (neg_c4_expose_outcome _)
  | c5External => exact package_rejects_clause (c := .c5) neg_c5_external_outcomes.2.1
  | c6Future => exact package_rejects_clause (c := .c6) neg_c6_future_assigned
  | c6Record => exact package_rejects_clause (c := .c6) neg_c6_record_assigned
  | c7Aggregate => exact package_rejects_clause (c := .c7) (neg_c7_aggregate_outcomes _)
  | c7Transport => exact package_rejects_clause (c := .c7) neg_c7_transport_outcomes.2.2.1
  | c7Uncoupled => exact package_rejects_clause (c := .c7) (neg_c7_uncoupled_outcomes _).2
  | c8Underfund => exact package_rejects_clause (c := .c8) neg_c8_underfund_outcome.2.1
  | withdrawal => exact package_rejects_clause (c := .c8) neg_autonomy_withdraw_assignment.2.2.1
  | sourceAbsent => exact package_rejects_clause (c := .c7) (c7_source_presence_guard _)
  | gap => exact package_rejects_clause (c := .c6) (missing_realized6_assigned _)

/-- NEG-C5-INTERNALIZED does not reject local package acceptance. Its failed
staged transport remains a separate check, not silently made a clause failure. -/
theorem m3b_internalized_package_still_passes (tag : Tag) :
    AssignedPackagePass (internalized5 canonical) tag := by
  intro c
  by_cases hc : c = .c5
  · subst c
    cases tag
    · exact neg_c5_internalized_outcomes.1
    · exact neg_c5_internalized_outcomes.2.1
  · apply (clause_accept_locality tag c ?_).mpr (canonical_assigned_package tag c)
    intro k hk
    have hn : k ≠ Cell.protocols .target := by
      intro he; subst k
      cases c <;> cases tag <;> first | contradiction | (simp [clauseScope,commonScope] at hk)
    simp [internalized5,mapCell,put,hn]

theorem m3b_internalized_transport_still_fails : ¬ C5Transport (internalized5 canonical) :=
  neg_c5_internalized_outcomes.2.2.1

end CSTTT.POS04.Assigned
