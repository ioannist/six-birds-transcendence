import CSTTT.Targets.GenericHandoff.POS04HistoricalSparseEquivalence
import CSTTT.Targets.GenericHandoff.POS04HistoricalZeroSupport

/-! Representation controls for StrictSparse, TTH-06. Rules fixed before checks:
modify target rows at the reached p2w1 only (source namespace before staging).
Outside/inside null controls append a ZERO entry to every action, respectively
at p2w0 and p1w0. Empty erases those action rows. Duplicate splits each weight
n>1 into 1 and n-1 on the SAME outcome; permutation reverses the list. Thus
neither duplicate freedom nor list order is added to operational legality.
Package/predictive schemas may separately read ordered hazard lists; no claim
that those schemas are invariant under a representation edit is assumed. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04SparseRegressions
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH RegisterInterpreter
open POS04ResourceRuntime POS04HistoricalEntryEquivalence
open POS04HistoricalSparseEquivalence
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def editRows (edit : List (Ambient × Nat) → List (Ambient × Nat)) : RawLaneModel :=
  {baseline with assignment := (mapCell canonical (.rows .source)
    (fun rows s a => if s = .p2w1 then edit (rows s a) else rows s a))}

def zeroInside : RawLaneModel := editRows (fun row => row ++ [(.inK .p1w0,0)])
abbrev zeroOutside := POS04HistoricalZeroSupport.diagnostic
def emptyResponses : RawLaneModel := editRows (fun _ => [])
def duplicatePositive : RawLaneModel := editRows (fun row => row.flatMap fun e =>
  if e.2 > 1 then [(e.1,1),(e.1,e.2-1)] else [e])
def permuted : RawLaneModel := editRows List.reverse

theorem baseline_full : FullAutonomy baseline := (full_iff_af _).mpr baseline_AF

theorem baseline_operational : OperationalAutonomy baseline := (operational_iff_ao _).mpr baseline_AO

theorem zero_inside_frozen_rejects : ¬ AO zeroInside := by
  change operationalAutonomyCheck zeroInside ≠ true
  decide +kernel

theorem zero_outside_frozen_rejects : ¬ AO zeroOutside :=
  POS04HistoricalZeroSupport.frozen_ao_rejects

theorem zero_inside_rejected : ¬ OperationalAutonomy zeroInside :=
  fun h => zero_inside_frozen_rejects ((operational_iff_ao _).mp h)

theorem zero_outside_rejected : ¬ OperationalAutonomy zeroOutside :=
  fun h => zero_outside_frozen_rejects ((operational_iff_ao _).mp h)

theorem zero_full_rejected : ¬ FullAutonomy zeroInside ∧ ¬ FullAutonomy zeroOutside := by
  have forward (m : RawLaneModel) (h : FullAutonomy m) : OperationalAutonomy m :=
    ⟨h.1,HistoricalPackageRuntime.sparse_full_implies_operational _ _ h.2⟩
  exact ⟨fun h => zero_inside_rejected (forward _ h),fun h => zero_outside_rejected (forward _ h)⟩

theorem empty_protocol_rejected :
    (POS04HistoricalRuntimeProtocol.check emptyResponses).read (image emptyResponses.assignment) ≠ some true := by
  intro he
  have hp := (POS04HistoricalRuntimeProtocol.check_iff _).mp he
  have hP := hp.2.2.2.1
  have bad : ¬ PUnchanged8 (withdrawnInputs emptyResponses) := by decide +kernel
  exact bad hP

theorem empty_rejected : (¬ FullAutonomy emptyResponses ∧ ¬ AF emptyResponses) ∧
    (¬ OperationalAutonomy emptyResponses ∧ ¬ AO emptyResponses) :=
  protocol_failure _ empty_protocol_rejected

/-- Duplicate positive entries remain legal. Splitting integer mass follows
n>1 ↦ (1,n-1); it neither invents nor removes probability. -/
theorem duplicate_operational : OperationalAutonomy duplicatePositive :=
  (operational_iff_ao _).mpr (by change operationalAutonomyCheck duplicatePositive = true; decide +kernel)

theorem permuted_operational : OperationalAutonomy permuted :=
  (operational_iff_ao _).mpr (by change operationalAutonomyCheck permuted = true; decide +kernel)

/-- A full certificate is constructed from an operational invariant only
when the SAME assigned package is separately proved at every factor. -/
theorem operational_and_package_full (m : RawLaneModel) (ho : AO m)
    (hp : PackageLane m.assignment) (hpackage : ∀ s, packageAtCheck m s = true) : AF m := by
  let cert := POS04OperationalGame.certificateOfAO m ho
  apply POS04FullGame.certificate_implies_af m
  exact {
    inside := cert.inside
    withdrawn := cert.withdrawn
    entriesNonempty := cert.entriesNonempty
    entriesInside := cert.entriesInside
    packageInside := fun r hr => by
      obtain ⟨s,hs⟩ := cert.packageInside r hr
      exact ⟨hp,s,hs,hpackage s⟩
    resourcesInside := cert.resourcesInside
    response := cert.response }

theorem duplicate_package : AssignedPackagePass (image duplicatePositive.assignment) .target := by
  decide +kernel

theorem permuted_package : AssignedPackagePass (image permuted.assignment) .target := by
  decide +kernel

theorem edited_complete (edit : List (Ambient × Nat) → List (Ambient × Nat)) :
    Complete primitiveCells (editRows edit).assignment :=
  by
  apply mapCell_complete (.rows .source)
    (fun rows s a => if s = .p2w1 then edit (rows s a) else rows s a)
  exact canonical_complete _

theorem edited_withdrawn (edit : List (Ambient × Nat) → List (Ambient × Nat)) :
    withdrawnAssignment (editRows edit) = image (editRows edit).assignment := by
  funext k
  cases k with
  | resources t => cases t <;> rfl
  | _ => rfl

theorem package_at_from_acceptance (m : RawLaneModel) (hp : PackageLane m.assignment)
    (hc : AssignedPackagePass (withdrawnAssignment m) .target)
    (ha : advancementCheck m = true) (s : KState) : packageAtCheck m s = true := by
  simp only [packageAtCheck,Bool.and_eq_true]
  exact ⟨⟨⟨hp,(package_check_iff _ _).mpr hc⟩,
    POS04HistoricalPackageEquivalence.state_views m hp s⟩,ha⟩

theorem duplicate_full : FullAutonomy duplicatePositive := by
  have ho := (operational_iff_ao _).mp duplicate_operational
  have hp := (package_lane_iff _).mpr ⟨edited_complete _,duplicate_package⟩
  apply (full_iff_af _).mpr (operational_and_package_full _ ho hp ?_)
  intro s
  apply package_at_from_acceptance _ hp
  · rw [edited_withdrawn]; exact duplicate_package
  · exact (POS04OperationalGame.certificateOfAO _ ho).withdrawn.2.2.1

theorem permuted_full : FullAutonomy permuted := by
  have ho := (operational_iff_ao _).mp permuted_operational
  have hp := (package_lane_iff _).mpr ⟨edited_complete _,permuted_package⟩
  apply (full_iff_af _).mpr (operational_and_package_full _ ho hp ?_)
  intro s
  apply package_at_from_acceptance _ hp
  · rw [edited_withdrawn]; exact permuted_package
  · exact (POS04OperationalGame.certificateOfAO _ ho).withdrawn.2.2.1

/-- These F instances retain exact comparison with the frozen package rules,
which may themselves inspect ordered hazard lists. No format invariance of
those distinct clause semantics is asserted. -/
theorem duplicate_full_equivalence : FullAutonomy duplicatePositive ↔ AF duplicatePositive := full_iff_af _
theorem permuted_full_equivalence : FullAutonomy permuted ↔ AF permuted := full_iff_af _

theorem diagnostic_support_only_still_holds :
    HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy
      POS04HistoricalZeroSupport.M POS04HistoricalZeroSupport.assignment :=
  POS04HistoricalZeroSupport.operational_game_accepts

/-- The same raw diagnostic separates the two NAMED game readouts. -/
theorem representation_sensitive_separation :
    HistoricalPackageRuntime.PostWithdrawalOperationalAutonomy
      POS04HistoricalZeroSupport.M POS04HistoricalZeroSupport.assignment ∧
    ¬ HistoricalPackageRuntime.SparseOperationalAutonomy
      POS04HistoricalZeroSupport.M POS04HistoricalZeroSupport.assignment := by
  refine ⟨diagnostic_support_only_still_holds,?_⟩
  intro h
  apply zero_outside_rejected
  exact ⟨(POS04HistoricalRuntimeProtocol.check_iff _).mpr POS04HistoricalZeroSupport.nominal_protocol,h⟩

/-- Every arbitrary-assignment representation case, including protocol
failure, falls under the same biconditionals; controls do not alter the rule. -/
theorem regression_vectors :
    (¬ OperationalAutonomy zeroInside ∧ ¬ OperationalAutonomy zeroOutside) ∧
    (¬ FullAutonomy emptyResponses ∧ ¬ OperationalAutonomy emptyResponses) ∧
    OperationalAutonomy duplicatePositive ∧ OperationalAutonomy permuted :=
  ⟨⟨zero_inside_rejected,zero_outside_rejected⟩,⟨empty_rejected.1.1,empty_rejected.2.1⟩,
    duplicate_operational,permuted_operational⟩

/-- Both versions, with the exact adopted representation controls. -/
theorem full_and_operational_regression_vectors :
    (FullAutonomy baseline ∧ OperationalAutonomy baseline) ∧
    (¬ FullAutonomy zeroInside ∧ ¬ OperationalAutonomy zeroInside) ∧
    (¬ FullAutonomy zeroOutside ∧ ¬ OperationalAutonomy zeroOutside) ∧
    (¬ FullAutonomy emptyResponses ∧ ¬ OperationalAutonomy emptyResponses) ∧
    (FullAutonomy duplicatePositive ∧ OperationalAutonomy duplicatePositive) ∧
    (FullAutonomy permuted ∧ OperationalAutonomy permuted) :=
  ⟨⟨baseline_full,baseline_operational⟩,⟨zero_full_rejected.1,zero_inside_rejected⟩,
    ⟨zero_full_rejected.2,zero_outside_rejected⟩,⟨empty_rejected.1.1,empty_rejected.2.1⟩,
    ⟨duplicate_full,duplicate_operational⟩,⟨permuted_full,permuted_operational⟩⟩

end CSTTT.TargetTheory.GenericHandoff.POS04SparseRegressions
