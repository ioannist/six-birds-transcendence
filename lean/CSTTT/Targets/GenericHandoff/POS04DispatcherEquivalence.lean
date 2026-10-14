import CSTTT.Targets.GenericHandoff.POS04Dispatcher
import CSTTT.Targets.GenericHandoff.POS04ProfileCompletion
import CSTTT.Targets.GenericHandoff.POS04OperationalCompletion
import CSTTT.Targets.GenericHandoff.POS04TemporalEquivalence
import CSTTT.Targets.GenericHandoff.POS04PackageEngine

/-! Exact closed-dispatcher equivalences. Every theorem quantifies over arbitrary
partial assignments; canonical acceptance alone is not used for the converse.
C3's extra stabilization and support-block gate is derived, not assumed. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04Dispatcher
open CSTTT.POS04 CSTTT.POS04.Assigned ClauseDispatcher

def clause : Kind → Clause
  | .c1 => .c1 | .c2 => .c2 | .c3 => .c3 | .c4 => .c4
  | .c5 => .c5 | .c6 => .c6 | .c7 => .c7 | .c8 => .c8

def kind : Clause → Kind
  | .c1 => .c1 | .c2 => .c2 | .c3 => .c3 | .c4 => .c4
  | .c5 => .c5 | .c6 => .c6 | .c7 => .c7 | .c8 => .c8

@[simp] theorem clause_kind (c : Clause) : clause (kind c) = c := by cases c <;> rfl
@[simp] theorem kind_clause (k : Kind) : kind (clause k) = k := by cases k <;> rfl

theorem clause_accept_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (k : Kind) :
    ((package t).rule k).accept a ↔ clauseAccept a t (clause k) := by
  cases k with
  | c1 => exact POS04ObjecthoodReference.generic_c1_iff a t
  | c2 => exact POS04ProfileRules.generic_c2_iff a t
  | c3 =>
    change (ProfileRules.C3Accept POS04ProfileRules.clauseSchema (POS04ProfileRules.clauseBindings t) a ∧ _) ↔ C3Accept a t
    rw [POS04ProfileRules.generic_c3_iff]
    exact ⟨And.left,fun h => ⟨h,POS04ProfileRules.accepted_completion a t h⟩⟩
  | c4 => exact POS04Exposure.generic_c4_iff a t
  | c5 => exact POS04ProtocolCredit.generic_c5_iff a t
  | c6 => exact POS04TemporalFactor.generic_c6_iff a t
  | c7 => exact POS04Joint.generic_c7_iff a t
  | c8 => exact POS04OperationalViability.dispatcher_c8_iff a t

theorem package_accept_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    (package t).accept a ↔ AssignedPackagePass a t := by
  constructor
  · intro h c; simpa using (clause_accept_iff a t (kind c)).mp (h (kind c))
  · intro h k; exact (clause_accept_iff a t k).mpr (h (clause k))

/-- Exact staged target-package P, with the independent complete-source gate. -/
def P (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  CSTTT.POS04.Assigned.Complete primitiveCells a ∧
    (package .target).accept (CSTTT.TargetTheory.ComputedFIACH.image a)

theorem p_iff (a : CSTTT.POS04.Assigned.Assignment) : P a ↔ CSTTT.TargetTheory.ComputedFIACH.PackageLane a := by
  unfold P
  rw [package_accept_iff]
  exact (CSTTT.TargetTheory.ComputedFIACH.package_lane_iff a).symm

theorem p_engine_iff (a : CSTTT.POS04.Assigned.Assignment) : P a ↔ POS04PackageEngine.P a :=
  (p_iff a).trans (POS04PackageEngine.p_iff a).symm

theorem deletion_failure (a : CSTTT.POS04.Assigned.Assignment) (k : Cell) :
    ¬ P (CSTTT.POS04.Assigned.put a k none) :=
  fun h => CSTTT.TargetTheory.ComputedFIACH.package_lane_missing k ((p_iff _).mp h)

theorem package_control_failure (v : PackageControl) :
    ¬ P (exchangeAssignment (packageControl v)) :=
  fun h => POS04PackageEngine.package_controls v ((p_engine_iff _).mp h)

/-- The staged global is constructed by locality and the checked cover. Its
closed-dispatcher acceptance is equivalent to the existing eight-clause result. -/
theorem constructs (a : CSTTT.POS04.Assigned.Assignment) (h : P a) :
    (∀ c k, k ∈ POS04PackageEngine.cover.scopes c →
      PackageEngine.global POS04PackageEngine.lang a POS04PackageEngine.stage POS04PackageEngine.cover k =
        mappedLocal POS04PackageEngine.lang a POS04PackageEngine.stage POS04PackageEngine.cover.scopes c k) ∧
    (∀ k, (PackageEngine.global POS04PackageEngine.lang a POS04PackageEngine.stage POS04PackageEngine.cover k).isSome = true) ∧
    (package .target).accept (PackageEngine.global POS04PackageEngine.lang a POS04PackageEngine.stage POS04PackageEngine.cover) := by
  have hp := POS04PackageEngine.constructs a ((p_engine_iff a).mp h)
  exact ⟨hp.1,hp.2.1,(package_accept_iff _ .target).mpr hp.2.2⟩

theorem positive : P canonical := (p_iff _).mpr CSTTT.TargetTheory.ComputedFIACH.package_lane_positive

end CSTTT.TargetTheory.GenericHandoff.POS04Dispatcher
