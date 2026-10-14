import CSTTT.Targets.GenericHandoff.POS04HistoricalEntryEquivalence

/-! Assignment-sensitive package agreement at historical runtime contexts.
The nominal protocol is interpreted before helper decoding. This is a
component equivalence, not the unfinished whole-game AF/AO adapter. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04HistoricalPackageEquivalence
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04RouteExecution POS04ResourceRuntime POS04HistoricalEntryEquivalence
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

theorem inside_iff (m : RawLaneModel) (r : Run6) :
    ResourceRuntime.Inside (model m).resourceSchema (HistoricalPackageRuntime.resources (model m))
      (HistoricalPackageRuntime.target (model m) m.assignment) (frame .target r) ↔
      POS04OperationalGame.Inside m r := by
  change (∃ s, s ∈ kernel ∧ some (match r.factor with
    | .inK t => some t | _ => none) = some (some s)) ↔ ∃ s, r.factor = .inK s
  have hk : ∀ s : KState, s ∈ kernel := by intro s; cases s <;> decide
  cases hf : r.factor <;> simp [hk]

/-- Completeness follows from P's actual all-cell totality. Retention maps
an existing resource primitive; it never manufactures a missing value. -/
theorem withdrawn_complete (m : RawLaneModel) (h : PackageLane m.assignment) :
    Complete primitiveCells (withdrawnAssignment m) := by
  have ht := ((POS04HistoricalRuntime.package_readout_iff m).mpr h).2.1
  rw [POS04HistoricalRuntime.target_eq] at ht
  exact mapCell_complete (.resources .target) _ (fun k _ => ht k)

theorem state_views (m : RawLaneModel) (h : PackageLane m.assignment) (s : KState) :
    stateViewsCheck (withdrawnAssignment m) s = true := by
  apply List.all_eq_true.mpr
  intro c _
  apply decide_eq_true
  intro k _
  exact withdrawn_complete m h k (primitive_cells_complete k)

theorem package_at_iff (m : RawLaneModel) (hp : POS04OperationalGame.Protocol m) (r : Run6) :
    HistoricalPackageRuntime.PackageAt (model m) m.assignment (frame .target r) ↔
      POS04FullGame.PackageAt m r := by
  have hP := POS04HistoricalRuntime.package_readout_iff m
  have hI := inside_iff m r
  have hC := POS04Dispatcher.package_accept_iff (withdrawnAssignment m) .target
  change (_ ∧ _ ∧ (POS04Dispatcher.package .target).accept
    (HistoricalPackageRuntime.runAssignment (model m) m.assignment (frame .target r))) ↔ _
  rw [POS04HistoricalRuntime.run_assignment_eq,hP,hI,hC]
  constructor
  · rintro ⟨hP,⟨s,hs⟩,hclause⟩
    refine ⟨hP,s,hs,?_⟩
    simp only [packageAtCheck,Bool.and_eq_true]
    exact ⟨⟨⟨hP,(package_check_iff _ _).mpr hclause⟩,state_views m hP s⟩,hp.2.2.1⟩
  · rintro ⟨hP,s,hs,hpkg⟩
    simp only [packageAtCheck,Bool.and_eq_true] at hpkg
    exact ⟨hP,⟨s,hs⟩,(package_check_iff _ _).mp hpkg.1.1.2⟩

end CSTTT.TargetTheory.GenericHandoff.POS04HistoricalPackageEquivalence
