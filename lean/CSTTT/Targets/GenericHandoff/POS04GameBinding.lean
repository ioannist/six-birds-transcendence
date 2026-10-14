import CSTTT.Targets.GenericHandoff.GameFiniteConstructor
import CSTTT.Targets.ComputedFIACH.ExactAutonomyTransport

/-! Shared-assignment binding of the hybrid game kernel on the POS-04 interface.
This is a specialization, not the completed polymorphic RawHandoff. Rows,
updater, code, observer, closure and entries are defined from assigned C6 and
activated phase-2 execution. No semantic predicate is supplied by a caller.
Nominal is an explicit nonempty disturbance type, separate from Action.
C6 quotient futures are used here; the actual-factor support/lift adapter and
its equivalence to the G6 finite checks remain a separate completion gate. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04GameBinding
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH
open CSTTT.TransportTheory

abbrev Disturbance := LaneDisturbance
abbrev Run := Run6

def disturbances : List Disturbance := [.nominal]
theorem disturbance_domain_nonempty : disturbances ≠ [] := by decide
theorem disturbance_domain_covers (d : Disturbance) : d ∈ disturbances := by cases d; simp [disturbances]

/-- Every consumed future/response primitive, including predictive hazards
and positions, is required before a decoder default can enter a game. -/
def dependencies : List Cell := autonomyInputs ++ clauseScope .target .c6

def data (m : RawLaneModel) := runInputs6 (withdrawnAssignment m) .target

def rows (m : RawLaneModel) (r : Run) (_d : Disturbance) (a : Action) : List (CSTTT.POS04.PredictiveNow × Rat) :=
  if Complete dependencies (image m.assignment) then
    (outcomes6 (data m)).map fun o => (o,weight6 (data m) r a o)
  else []
def update (m : RawLaneModel) (r : Run) (_d : Disturbance) (a : Action) (o : CSTTT.POS04.PredictiveNow) : Run :=
  update6 (data m) r a o

def code (m : RawLaneModel) := code6 (data m)
def observer (m : RawLaneModel) := observation6 (data m) .target

def entryRun (m : RawLaneModel) (e : WithdrawalEntry) : Run :=
  ⟨e.factor,e.counter,e.ticks,e.register,(arrivalInputs m).base.receiver.funded⟩
/-- Includes the acquisition gate before defaults can form an entry. -/
def Entries (m : RawLaneModel) (r : Run) : Prop :=
  ∃ e ∈ entries m, 0 < e.numerator ∧ r = entryRun m e

def Withdrawal (m : RawLaneModel) : Prop :=
  Complete dependencies (image m.assignment) ∧ withdrawalCheck m = true

def ResourceClosed (m : RawLaneModel) (r : Run) : Prop :=
  Complete dependencies (image m.assignment) ∧
  RetainedResource.targetRecharge ∈ m.retained ∧
  (data m).resource.owner = .target ∧ (data m).resource.rechargeAvailable = true ∧
  enabled6 (data m) r = true

/-- Same coherent arrival package; assigned clause checks are recomputed on
withdrawn primitives. No acquisition source is read as a response dependency. -/
def PackageAt (m : RawLaneModel) (r : Run) : Prop :=
  PackageLane m.assignment ∧ AssignedPackagePass (withdrawnAssignment m) .target ∧
  (∃ s, r.factor = .inK s ∧ stateViewsCheck (withdrawnAssignment m) s = true) ∧
  (∀ a o, UpdateLaws6 (data m) .target r a o)

def Legal (m : RawLaneModel) (r : Run) (_d : Disturbance) (a : Action) : Prop :=
  ResourceClosed m r ∧ a ∈ actions ∧
  budget6 (data m) > 0 ∧ budget6 (data m) ≥ (data m).ledger.actionCost

def StepLaw (m : RawLaneModel) (r : Run) (d : Disturbance) (a : Action) (o : CSTTT.POS04.PredictiveNow) : Prop :=
  (update m r d a o).funded = true ∧
  budgetAfter6 (data m) = budget6 (data m) ∧ budgetAfter6 (data m) > 0 ∧
  (update m r d a o).counter > r.counter ∧
  (observer m (update m r d a o)).cumulativeProgress > (observer m r).cumulativeProgress ∧
  (observer m (update m r d a o)).endogenousRecordCount > (observer m r).endogenousRecordCount ∧
  (update m r d a o).ticks > r.ticks ∧
  (update m r d a o).residue = r.residue ∧
  (observer m (update m r d a o)).owner = .target

abbrev FullCertificate (m : RawLaneModel) :=
  StrategyGame.InvariantCertificate (rows m) (update m) (Entries m) (Withdrawal m)
    (PackageAt m) (ResourceClosed m) (Legal m) (StepLaw m)
def FullAutonomy (m : RawLaneModel) : Prop :=
  StrategyGame.GameReadout (rows m) (update m) (Entries m) (Withdrawal m)
    (PackageAt m) (ResourceClosed m) (Legal m) (StepLaw m)

def OperationalAt (m : RawLaneModel) (r : Run) : Prop :=
  C8Accept (withdrawnAssignment m) .target ∧
  ∃ s, r.factor = .inK s ∧ s ∈ greatest8 (withdrawnInputs m) .target
abbrev OperationalCertificate (m : RawLaneModel) :=
  StrategyGame.InvariantCertificate (rows m) (update m) (Entries m) (Withdrawal m)
    (OperationalAt m) (ResourceClosed m) (Legal m) (StepLaw m)
def OperationalAutonomy (m : RawLaneModel) : Prop :=
  StrategyGame.GameReadout (rows m) (update m) (Entries m) (Withdrawal m)
    (OperationalAt m) (ResourceClosed m) (Legal m) (StepLaw m)

theorem full_soundness (m : RawLaneModel) (cert : FullCertificate m) : FullAutonomy m :=
  StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ cert
theorem operational_soundness (m : RawLaneModel) (cert : OperationalCertificate m) : OperationalAutonomy m :=
  StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ cert

theorem full_implies_arrival_package (m : RawLaneModel) (h : FullAutonomy m) : PackageLane m.assignment :=
  StrategyGame.game_same_package_implies_arrival h

/-- Defined update laws apply to every run, hence every strategy play. -/
theorem all_run_readout_laws (m : RawLaneModel) (r : Run) (a : Action) (o : CSTTT.POS04.PredictiveNow) :
    UpdateLaws6 (data m) .target r a o := update_laws6 _ _ _ _ _

theorem future_owned (m : RawLaneModel) :
    (future6 (withdrawnAssignment m) .target).code = code m ∧
    (future6 (withdrawnAssignment m) .target).observe = observer m := ⟨rfl,rfl⟩

theorem updater_owned (m : RawLaneModel) (r : Run) (d : Disturbance) (a : Action) (o : CSTTT.POS04.PredictiveNow) :
    update m r d a o = (dynamics6 (withdrawnAssignment m) .target).update r a o := rfl

theorem rows_missing (m : RawLaneModel) (k : Cell) (hk : k ∈ dependencies)
    (hm : image m.assignment k = none) (r : Run) (d : Disturbance) (a : Action) :
    rows m r d a = [] := by
  have hn : ¬ Complete dependencies (image m.assignment) := by
    intro hc
    have he := hc k hk
    rw [hm] at he
    contradiction
  simp [rows,hn]

theorem missing_rejects_full (m : RawLaneModel) (k : Cell) (hk : k ∈ dependencies)
    (hm : image m.assignment k = none) : ¬ FullAutonomy m := by
  intro h
  have hc := h.1.1 k hk
  rw [hm] at hc
  contradiction

theorem missing_rejects_operational (m : RawLaneModel) (k : Cell) (hk : k ∈ dependencies)
    (hm : image m.assignment k = none) : ¬ OperationalAutonomy m := by
  intro h
  have hc := h.1.1 k hk
  rw [hm] at hc
  contradiction

theorem empty_phase2_rejects_both (m : RawLaneModel) (h : entries m = []) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have hn : ∀ r, ¬ Entries m r := by simp [Entries,h]
  exact ⟨StrategyGame.no_entries_no_game hn,StrategyGame.no_entries_no_game hn⟩

theorem missing_acquisition_dependency_rejects_both (m : RawLaneModel) (k : Cell)
    (hk : k ∈ phase2Dependencies) :
    ¬ FullAutonomy {m with assignment := put m.assignment (swapCell k) none} ∧
    ¬ OperationalAutonomy {m with assignment := put m.assignment (swapCell k) none} :=
  empty_phase2_rejects_both _ (phase2_missing_dependency_no_entries m k hk)

/-- Full-future sufficiency remains a separate assigned C6 gate and retains
its all-state, all-word quantifier. It is not implied by autonomy validity. -/
theorem assigned_full_future (m : RawLaneModel)
    (h : C6Accept (withdrawnAssignment m) .target) :
    FullFutureSufficient (future6 (withdrawnAssignment m) .target) :=
  c6_accept_sufficient h

/-- Concrete conserved-ledger/retained-register lift facts, proved on the
entire assigned C6 closure. This is not yet a factor-response LiftWitness. -/
theorem funded_closure_updates (m : RawLaneModel)
    (h : C6Accept (withdrawnAssignment m) .target) (r : Run)
    (hr : Closure6 (withdrawnAssignment m) .target r)
    (a : Action) (o : CSTTT.POS04.PredictiveNow) :
    budgetAfter6 (data m) = budget6 (data m) ∧ budgetAfter6 (data m) > 0 ∧
    (update m r .nominal a o).funded = true ∧
    (observer m (update m r .nominal a o)).endogenousRecordCount =
      (observer m r).endogenousRecordCount + 1 ∧
    (update m r .nominal a o).residue = r.residue := by
  obtain ⟨he,hp,hf,hrec⟩ := c6_accept_record_advancement h r hr a o
  exact ⟨he,hp,hf,hrec,rfl⟩

theorem source_absent_rejects_both (m : RawLaneModel)
    (h : (arrivalInputs m).base.receiver.sourcePresent = false) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  apply empty_phase2_rejects_both
  apply phase2_unavailable_no_entries
  intro r _
  exact no_source_rejects_phase2 m h r

/-- Direct game readout rejection: retained recharge is a necessary raw
resource condition at the nonempty activated entry, not just a failed check. -/
theorem recharge_withdrawn_rejects_both (m : RawLaneModel)
    (h : RetainedResource.targetRecharge ∉ m.retained) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have hn : ∀ r, ¬ ResourceClosed m r := by
    intro r hr
    exact h hr.2.1
  constructor <;> intro ha
  · obtain ⟨entry,he⟩ := ha.2.1
    obtain ⟨_,_,strategy,hs⟩ := ha
    exact hn entry (hs entry he entry [] StrategyGame.Play.initial).2.1
  · obtain ⟨entry,he⟩ := ha.2.1
    obtain ⟨_,_,strategy,hs⟩ := ha
    exact hn entry (hs entry he entry [] StrategyGame.Play.initial).2.1

end CSTTT.TargetTheory.GenericHandoff.POS04GameBinding
