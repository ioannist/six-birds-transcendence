import CSTTT.Targets.GenericHandoff.POS04ExactGameControls
import CSTTT.Targets.GenericHandoff.GameFiniteProjection

/-! Verified specialization of the polymorphic projection-converse engine.
All assigned rows and all funded register/counter contexts are quantified.
There is no representative choice in either the raw response or its updater.
These laws are proved for this family, not assumed for unrestricted recipes. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04OperationalGame
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH

def projection (r : Run) : KState := match r.factor with
  | .inK s => s
  | _ => .p0w0

theorem response_projects (m : RawLaneModel) (hp : Protocol m) (r : Run) (s : KState)
    (hs : r.factor = .inK s) (S : List KState)
    (responses : ∀ d, ∃ a, Legal m r d a ∧ StrategyGame.Normalized (rows m) r d a ∧
      ∀ o, StrategyGame.PositiveSupport (rows m) r d a o →
        projection (update m r d a o) ∈ S ∧ StepLaw m r d a o) :
    ∃ a ∈ actions, rowClosed8 (inputs m).viability s a S = true := by
  obtain ⟨a,ha,_,hnext⟩ := responses .nominal
  obtain ⟨ha,t,ht,hrow⟩ := ha
  have heq : t = s := by injection (ht.symm.trans hs)
  subst t
  have hf := closed_fields _ _ _ _ hrow
  refine ⟨a,ha,?_⟩
  simp only [rowClosed8,Bool.and_eq_true,List.all_eq_true]
  refine ⟨⟨by simpa using List.isEmpty_eq_false_iff.mpr hf.1,decide_eq_true hf.2.1⟩,?_⟩
  intro e he
  obtain ⟨hn,y,hy,_⟩ := hf.2.2 e he
  have hmem := (hnext e.1 (raw_support m hp r s hs .nominal a e he hn)).1
  have hm : y ∈ S := by simpa [projection,update,hy] using hmem
  simp [hy,hn,hm]

def projection_laws (m : RawLaneModel) (hp : Protocol m) :
    GameFiniteProjection.Laws (rows m) (update m) (Inside m) (ResourceClosed m)
      (Legal m) (StepLaw m) (retain8 (withdrawnInputs m) .target) projection where
  retention S r hi hr responses := by
    obtain ⟨s,hs⟩ := hi
    obtain ⟨a,ha,hrow⟩ := response_projects m hp r s hs S responses
    have hav := hr.1
    rw [viability_eq] at hrow hav
    simp only [projection,hs,retain8,Bool.and_eq_true,List.any_eq_true]
    exact ⟨hav,a,ha,hrow⟩

theorem game_entries_in_greatest (m : RawLaneModel) (h : Autonomy m) (r : Run) (hr : Entries m r) :
    projection r ∈ greatestO m := by
  rw [greatestO,← POS04Adapter.c8_engine_eq]
  exact GameFiniteProjection.entries_in_greatest kernel (fun s => by cases s <;> decide)
    _ (POS04Adapter.c8_retain_monotone _ _) projection (projection_laws m h.1) h r hr
end CSTTT.TargetTheory.GenericHandoff.POS04OperationalGame

namespace CSTTT.TargetTheory.GenericHandoff.POS04FullGame
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH
open POS04OperationalGame

def projection_laws (m : RawLaneModel) (hp : Protocol m) :
    GameFiniteProjection.Laws (rows m) (update m) (PackageAt m) (ResourceClosed m)
      (Legal m) (StepLaw m) (retainF m) projection where
  retention S r hi _ responses := by
    obtain ⟨_,s,hs,hpackage⟩ := hi
    obtain ⟨a,ha,hrow⟩ := response_projects m hp r s hs S responses
    rw [viability_eq] at hrow
    simp only [projection,hs,retainF,responseCheck,hp.2.1,hp.2.2.1,
      Bool.true_and,Bool.and_eq_true,List.any_eq_true]
    exact ⟨hpackage,a,ha,hrow⟩

theorem game_entries_in_greatest (m : RawLaneModel) (h : Autonomy m) (r : Run) (hr : Entries m r) :
    projection r ∈ greatestF m := by
  rw [← POS04Adapter.full_engine_eq]
  exact GameFiniteProjection.entries_in_greatest kernel (fun s => by cases s <;> decide)
    _ (POS04Adapter.full_retain_monotone m) projection (projection_laws m h.1) h r hr

end CSTTT.TargetTheory.GenericHandoff.POS04FullGame
