import CSTTT.Targets.GenericHandoff.POS04GameBinding
import CSTTT.Targets.GenericHandoff.POS04ViableSet
import CSTTT.POS04.Assigned.C6ActualSupport

/-! Actual-support game binding. Outcomes are actual Ambient successors, not
predictive-class representatives. Every raw branch retains its weight and its
actual factor. All other interpreted fields are from the same assignment as
the acquisition. The old POS04GameBinding is the quotient-observer schema;
this binding is used for the actual-support autonomy certificate. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ActualGame
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH

abbrev Run := Run6
abbrev Disturbance := LaneDisturbance

def rows (m : RawLaneModel) (r : Run) (_d : Disturbance) (a : Action) : List (Ambient × Rat) :=
  if Complete POS04GameBinding.dependencies (image m.assignment) then actualRows6 (POS04GameBinding.data m) r a else []
def update (m : RawLaneModel) (r : Run) (_d : Disturbance) (a : Action) (o : Ambient) :=
  actualUpdate6 (POS04GameBinding.data m) r a o

def PackageAt (m : RawLaneModel) (r : Run) : Prop :=
  PackageLane m.assignment ∧ AssignedPackagePass (withdrawnAssignment m) .target ∧
  (∃ s, r.factor = .inK s ∧ stateViewsCheck (withdrawnAssignment m) s = true) ∧
  (∀ a o, ActualUpdateLaws6 (POS04GameBinding.data m) .target r a o)

def StepLaw (m : RawLaneModel) (r : Run) (d : Disturbance) (a : Action) (o : Ambient) : Prop :=
  (update m r d a o).funded = true ∧
  budgetAfter6 (POS04GameBinding.data m) = budget6 (POS04GameBinding.data m) ∧ budgetAfter6 (POS04GameBinding.data m) > 0 ∧
  (update m r d a o).counter > r.counter ∧
  (POS04GameBinding.observer m (update m r d a o)).cumulativeProgress > (POS04GameBinding.observer m r).cumulativeProgress ∧
  (POS04GameBinding.observer m (update m r d a o)).endogenousRecordCount > (POS04GameBinding.observer m r).endogenousRecordCount ∧
  (update m r d a o).ticks > r.ticks ∧ (update m r d a o).residue = r.residue ∧
  (POS04GameBinding.observer m (update m r d a o)).owner = .target

abbrev FullCertificate (m : RawLaneModel) :=
  StrategyGame.InvariantCertificate (rows m) (update m) (POS04GameBinding.Entries m) (POS04GameBinding.Withdrawal m)
    (PackageAt m) (POS04GameBinding.ResourceClosed m) (POS04GameBinding.Legal m) (StepLaw m)
def FullAutonomy (m : RawLaneModel) : Prop :=
  StrategyGame.GameReadout (rows m) (update m) (POS04GameBinding.Entries m) (POS04GameBinding.Withdrawal m)
    (PackageAt m) (POS04GameBinding.ResourceClosed m) (POS04GameBinding.Legal m) (StepLaw m)
abbrev OperationalCertificate (m : RawLaneModel) :=
  StrategyGame.InvariantCertificate (rows m) (update m) (POS04GameBinding.Entries m) (POS04GameBinding.Withdrawal m)
    (POS04GameBinding.OperationalAt m) (POS04GameBinding.ResourceClosed m) (POS04GameBinding.Legal m) (StepLaw m)
def OperationalAutonomy (m : RawLaneModel) : Prop :=
  StrategyGame.GameReadout (rows m) (update m) (POS04GameBinding.Entries m) (POS04GameBinding.Withdrawal m)
    (POS04GameBinding.OperationalAt m) (POS04GameBinding.ResourceClosed m) (POS04GameBinding.Legal m) (StepLaw m)

theorem full_soundness (m : RawLaneModel) (h : FullCertificate m) : FullAutonomy m :=
  StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ h
theorem operational_soundness (m : RawLaneModel) (h : OperationalCertificate m) : OperationalAutonomy m :=
  StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ h
theorem full_implies_arrival (m : RawLaneModel) (h : FullAutonomy m) : PackageLane m.assignment :=
  StrategyGame.game_same_package_implies_arrival h

/-- Context retains the real funded bit and the actual raw route register.
No bounded counter or hidden irrelevance premise is used. -/
def Context (m : RawLaneModel) (r : Run) : Prop :=
  r.funded = true ∧ writer6 (POS04GameBinding.data m) .target r.residue = true

def projection (r : Run) : KState := match r.factor with | .inK s => s | _ => .p0w0

/-- Exit states are excluded separately, so the projection's total extension
cannot conceal an exit. -/
def FactorContext (m : RawLaneModel) (r : Run) : Prop :=
  Context m r ∧ ∃ s, r.factor = .inK s

theorem baseline_dependencies : Complete POS04GameBinding.dependencies (image baseline.assignment) := by
  rw [show baseline.assignment = canonical from rfl,image_canonical]
  exact canonical_complete _
theorem baseline_data : POS04GameBinding.data baseline = runInputs6 canonical .target := by
  unfold POS04GameBinding.data
  rw [baseline_withdrawn]
theorem baseline_rows (r : Run) (d : Disturbance) (a : Action) :
    rows baseline r d a = actualRows6 (runInputs6 canonical .target) r a := by
  simp only [rows,if_pos baseline_dependencies,baseline_data]

theorem baseline_resource (r : Run) (h : Context baseline r) : POS04GameBinding.ResourceClosed baseline r := by
  refine ⟨baseline_dependencies,by decide,by rw [baseline_data]; rfl,
    by rw [baseline_data]; rfl,?_⟩
  simp only [POS04GameBinding.data,baseline_withdrawn,enabled6,h.1]
  rfl

theorem baseline_legal (r : Run) (h : Context baseline r) (d : Disturbance) (a : Action) :
    POS04GameBinding.Legal baseline r d a := by
  exact ⟨baseline_resource r h,by cases a <;> decide,
    by rw [baseline_data]; decide,by rw [baseline_data]; decide⟩

theorem baseline_package (r : Run) (h : FactorContext baseline r) : PackageAt baseline r := by
  obtain ⟨s,hs⟩ := h.2
  exact ⟨package_lane_positive,by rw [baseline_withdrawn]; exact canonical_assigned_package .target,
    ⟨s,hs,by rw [baseline_withdrawn]; unfold stateViewsCheck; decide⟩,
    fun a o => actual_update_laws6 _ _ _ _ _⟩

theorem baseline_step (r : Run) (h : FactorContext baseline r) (d : Disturbance)
    (a : Action) (o : Ambient) : StepLaw baseline r d a o := by
  obtain ⟨s,hs⟩ := h.2
  have hd : delta6 (POS04GameBinding.data baseline) r.factor a = 1 := by
    rw [baseline_data,hs]
    cases s <;> cases a <;> decide
  have hb : budgetAfter6 (POS04GameBinding.data baseline) = 1 := by rw [baseline_data]; decide
  simp only [StepLaw,update,actualUpdate6,POS04GameBinding.observer,observation6,h.1.1,h.1.2,
    hb,hd,show budget6 (POS04GameBinding.data baseline) = 1 from by rw [baseline_data]; rfl,
    show (POS04GameBinding.data baseline).resource.owner = .target from by rw [baseline_data]; rfl,
    Bool.true_and,if_true]
  simp only [show decide (1 > 0) = true from rfl,Bool.and_true,if_true,
    and_true,true_and]
  omega

/-- Positivity cannot manufacture a destination: every semantic supported
outcome occurs in the actual raw row. -/
theorem baseline_support (r : Run) (h : FactorContext baseline r) (d : Disturbance)
    (a : Action) (o : Ambient) (ho : StrategyGame.PositiveSupport (rows baseline) r d a o) :
    ∃ n, (o,n) ∈ actionRow .target (projection r) a ∧ n > 0 := by
  obtain ⟨s,hs⟩ := h.2
  obtain ⟨w,hw,hpos⟩ := ho
  rw [baseline_rows] at hw
  have he : enabled6 (runInputs6 canonical .target) r = true := by
    change enabled6 (POS04GameBinding.data baseline) r = true
    exact (baseline_resource r h.1).2.2.2.2
  simp only [actualRows6,he,if_true] at hw
  obtain ⟨e,hm,heq⟩ := List.mem_map.mp hw
  have ho : e.1 = o := congrArg Prod.fst heq
  have hp : 0 < e.2 := by
    have hp : ∀ e ∈ actionRow .target s a, 0 < e.2 := by cases s <;> cases a <;> decide
    exact hp e (by simpa [row6,hs] using hm)
  refine ⟨e.2,?_,hp⟩
  have hm' : e ∈ actionRow .target s a := by simpa only [row6,hs] using hm
  rcases e with ⟨dest,n⟩
  cases ho
  simpa [projection,hs] using hm'


theorem canonical_probability_rows (s : KState) (a : Action)
    (hn : (actionRow .target s a).isEmpty = false) :
    ((actionRow .target s a).all fun e => decide (0 < (e.2 : Rat) / 4)) = true ∧
    (((actionRow .target s a).map fun e => (e.2 : Rat) / 4).sum = 1) := by
  cases s <;> cases a <;> revert hn <;> decide +kernel

theorem baseline_normalized (r : Run) (h : FactorContext baseline r)
    (d : Disturbance) (a : Action) (S : List KState)
    (hr : responseCheck baseline S (projection r) d a = true) :
    StrategyGame.Normalized (rows baseline) r d a := by
  obtain ⟨s,hs⟩ := h.2
  have he : enabled6 (runInputs6 canonical .target) r = true := by
    change enabled6 (POS04GameBinding.data baseline) r = true
    exact (baseline_resource r h.1).2.2.2.2
  have hp : projection r = s := by simp [projection,hs]
  have hrow : rowClosed8 (clause8 canonical .target) s a S = true := by
    have hrow := (Bool.and_eq_true_iff.mp hr).2
    simpa only [withdrawnInputs,baseline_withdrawn,hp] using hrow
  have hn : (actionRow .target s a).isEmpty = false := by
    have hn := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hrow).1).1
    simpa using hn
  have hc := canonical_probability_rows s a hn
  have hrows : rows baseline r d a = (actionRow .target s a).map (fun e => (e.1,(e.2 : Rat)/4)) := by
    rw [baseline_rows]; simp only [actualRows6,he,if_true,row6,hs]; rfl
  unfold StrategyGame.Normalized
  rw [hrows]
  refine ⟨?_,?_,?_⟩
  · intro e hm
    obtain ⟨raw,hraw,heq⟩ := List.mem_map.mp hm
    subst e
    exact Rat.le_of_lt (of_decide_eq_true (List.all_eq_true.mp hc.1 raw hraw))
  · simpa only [List.map_map,Function.comp_def] using hc.2
  · unfold StrategyGame.PositiveSupport
    rw [hrows]
    cases hlist : actionRow .target s a with
    | nil => simp [hlist] at hn
    | cons e rest =>
      have hm : e ∈ actionRow .target s a := by simp [hlist]
      exact ⟨e.1,(e.2 : Rat)/4,List.mem_map.mpr ⟨e,by simp,rfl⟩,
        of_decide_eq_true (List.all_eq_true.mp hc.1 e hm)⟩

/-- The run-factor square commutes for EVERY semantic support branch;
package and resource preservation is established separately by the lift. -/
theorem baseline_support_lift (r : Run) (h : FactorContext baseline r)
    (S : List KState) (d : Disturbance) (a : Action)
    (hr : responseCheck baseline S (projection r) d a = true)
    (o : Ambient) (ho : StrategyGame.PositiveSupport (rows baseline) r d a o) :
    FactorContext baseline (update baseline r d a o) ∧
    projection (update baseline r d a o) ∈ S ∧ StepLaw baseline r d a o := by
  obtain ⟨n,hm,_⟩ := baseline_support r h d a o ho
  obtain ⟨y,hy,_,hS⟩ := response_all_support baseline S (projection r) d a hr (o,n) hm
  have hb : budgetAfter6 (POS04GameBinding.data baseline) > 0 := by rw [baseline_data]; decide
  refine ⟨⟨⟨?_,h.1.2⟩,y,hy⟩,?_,baseline_step r h d a o⟩
  · simp only [update,actualUpdate6,h.1.1,decide_eq_true hb,Bool.true_and]
  · have hy' : o = .inK y := hy
    simpa [update,actualUpdate6,projection,hy'] using hS

set_option maxRecDepth 8192 in
set_option maxHeartbeats 8000000 in
theorem baseline_entry_facts : ∀ e ∈ entries baseline,
    e.numerator > 0 ∧ e.factor ∈ ambientStates ∧
    (∃ s, e.factor = .inK s) ∧
    writer6 (POS04GameBinding.data baseline) .target e.register = true ∧
    (arrivalInputs baseline).base.receiver.funded = true := by decide

theorem baseline_entry_context (r : Run) (hr : POS04GameBinding.Entries baseline r) :
    FactorContext baseline r := by
  obtain ⟨e,he,_,rfl⟩ := hr
  obtain ⟨_,_,hf,hw,hfund⟩ := baseline_entry_facts e he
  exact ⟨⟨hfund,hw⟩,hf⟩

theorem baseline_entries_nonempty : ∃ r, POS04GameBinding.Entries baseline r := by
  let e : WithdrawalEntry := ⟨.inK .p2w1,4,(sourceHistory .repA,(routeOf .a).eventPath),1,1⟩
  refine ⟨POS04GameBinding.entryRun baseline e,e,?_,by decide,rfl⟩
  decide

/-- Constructed finite witness, quantified over EVERY viable factor set and
EVERY run context that satisfies the funded/register law. -/
def baseline_full_lift : GameFiniteConstructor.LiftWitness (rows baseline) (update baseline)
    (POS04GameBinding.Entries baseline) (POS04GameBinding.Withdrawal baseline)
    (PackageAt baseline) (POS04GameBinding.ResourceClosed baseline)
    (POS04GameBinding.Legal baseline) (StepLaw baseline) kernel (retainF baseline) where
  context := FactorContext baseline
  projection := projection
  withdrawn := ⟨baseline_dependencies,by decide⟩
  entriesNonempty := baseline_entries_nonempty
  entryContext := baseline_entry_context
  entryFactor r hr := by
    rw [POS04Adapter.full_engine_eq,baseline_greatestF]
    cases projection r <;> decide
  packageLift _ _ r hr _ := baseline_package r hr
  resourceLift _ _ r hr _ := baseline_resource r hr.1
  responseLift S hv r hr hs d := by
    have hf := hv (projection r) hs
    obtain ⟨a,ha,hresp⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp hf).2
    cases d
    exact ⟨a,baseline_legal r hr.1 .nominal a,
      baseline_normalized r hr .nominal a S hresp,
      fun o ho => baseline_support_lift r hr S .nominal a hresp o ho⟩

/-- Positive certificate is constructed by the finite engine; soundness then
constructs the strategy and inducts over its plays. -/
def baseline_full_certificate : FullCertificate baseline :=
  GameFiniteConstructor.certificate (fun s => by cases s <;> decide)
    (POS04Adapter.full_retain_monotone baseline) baseline_full_lift

theorem baseline_full_autonomy : FullAutonomy baseline :=
  full_soundness baseline baseline_full_certificate


def baseline_operational_lift : GameFiniteConstructor.LiftWitness (rows baseline) (update baseline)
    (POS04GameBinding.Entries baseline) (POS04GameBinding.Withdrawal baseline)
    (POS04GameBinding.OperationalAt baseline) (POS04GameBinding.ResourceClosed baseline)
    (POS04GameBinding.Legal baseline) (StepLaw baseline) kernel
    (retain8 (withdrawnInputs baseline) .target) where
  context := FactorContext baseline
  projection := projection
  withdrawn := ⟨baseline_dependencies,by decide⟩
  entriesNonempty := baseline_entries_nonempty
  entryContext := baseline_entry_context
  entryFactor r _ := by
    rw [POS04Adapter.c8_engine_eq]
    change projection r ∈ greatestO baseline
    rw [baseline_greatestO]
    cases projection r <;> decide
  packageLift S hv r hr hs := by
    refine ⟨?_,projection r,?_,?_⟩
    · rw [baseline_withdrawn]
      exact canonical_assigned_package .target .c8
    · obtain ⟨s,hs⟩ := hr.2
      simp [projection,hs]
    · exact greatest8_contains_viable _ _ S hv hs
  resourceLift _ _ r hr _ := baseline_resource r hr.1
  responseLift S hv r hr hs d := by
    have hf := hv (projection r) hs
    obtain ⟨a,ha,hrow⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp hf).2
    have hresp : responseCheck baseline S (projection r) d a = true := by
      cases d
      have hw : withdrawalCheck baseline = true := by decide
      have ha : advancementCheck baseline = true := by
        unfold advancementCheck; rw [baseline_withdrawn]; decide
      simp only [responseCheck,hw,ha,Bool.true_and,hrow]
    exact ⟨a,baseline_legal r hr.1 d a,baseline_normalized r hr d a S hresp,
      fun o ho => baseline_support_lift r hr S d a hresp o ho⟩

def baseline_operational_certificate : OperationalCertificate baseline :=
  GameFiniteConstructor.certificate (fun s => by cases s <;> decide)
    (POS04Adapter.c8_retain_monotone _ _) baseline_operational_lift

theorem baseline_operational_autonomy : OperationalAutonomy baseline :=
  operational_soundness baseline baseline_operational_certificate

/-- Missing primitives reject independently of decoder defaults. -/
theorem missing_rejects_both (m : RawLaneModel) (k : Cell)
    (hk : k ∈ POS04GameBinding.dependencies) (hm : image m.assignment k = none) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have hn : ¬ POS04GameBinding.Withdrawal m := by
    intro h
    have hp := h.1 k hk
    rw [hm] at hp
    contradiction
  exact ⟨StrategyGame.invalid_withdrawal_no_game hn,StrategyGame.invalid_withdrawal_no_game hn⟩

theorem empty_entries_rejects_both (m : RawLaneModel) (h : entries m = []) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  have hn : ∀ r, ¬ POS04GameBinding.Entries m r := by simp [POS04GameBinding.Entries,h]
  exact ⟨StrategyGame.no_entries_no_game hn,StrategyGame.no_entries_no_game hn⟩

theorem withdrawal_deletion_rejects_both :
    ¬ FullAutonomy withdrawalDeletion ∧ ¬ OperationalAutonomy withdrawalDeletion := by
  have hn : ∀ r, ¬ POS04GameBinding.ResourceClosed withdrawalDeletion r := by
    intro r h
    exact (by decide : RetainedResource.targetRecharge ∉ withdrawalDeletion.retained) h.2.1
  constructor <;> intro h
  · obtain ⟨r,hr⟩ := h.2.1
    obtain ⟨_,_,strategy,hs⟩ := h
    exact hn r (hs r hr r [] StrategyGame.Play.initial).2.1
  · obtain ⟨r,hr⟩ := h.2.1
    obtain ⟨_,_,strategy,hs⟩ := h
    exact hn r (hs r hr r [] StrategyGame.Play.initial).2.1

theorem package_deletion_rejects_full : ¬ FullAutonomy packageDeletion :=
  fun h => package_deletion_package (full_implies_arrival _ h)

/-- Genuine obstruction to arbitrary-partial-assignment AO equivalence.
Legacy AO does not consume hazards; the full future game binding does. -/
def missingHazard : RawLaneModel := {baseline with assignment := put canonical .hazards none}
set_option maxHeartbeats 8000000 in
set_option maxRecDepth 8192 in
theorem missing_hazard_legacy_AO : AO missingHazard := by
  unfold AO operationalAutonomyCheck
  have hg : greatestO missingHazard = kernel := baseline_greatestO
  rw [hg]
  unfold sharedAutonomyCheck
  decide

theorem missing_hazard_no_game : ¬ OperationalAutonomy missingHazard :=
  (missing_rejects_both missingHazard .hazards (by decide) (by rfl)).2

theorem arbitrary_partial_AO_equivalence_false :
    ¬ (∀ m : RawLaneModel, OperationalAutonomy m ↔ AO m) :=
  fun h => missing_hazard_no_game ((h missingHazard).mpr missing_hazard_legacy_AO)


theorem source_absent_rejects_both (m : RawLaneModel)
    (h : (arrivalInputs m).base.receiver.sourcePresent = false) :
    ¬ FullAutonomy m ∧ ¬ OperationalAutonomy m := by
  apply empty_entries_rejects_both
  apply phase2_unavailable_no_entries
  intro r _
  exact no_source_rejects_phase2 m h r

theorem missing_acquisition_rejects_both (m : RawLaneModel) (k : Cell)
    (hk : k ∈ phase2Dependencies) :
    ¬ FullAutonomy {m with assignment := put m.assignment (swapCell k) none} ∧
    ¬ OperationalAutonomy {m with assignment := put m.assignment (swapCell k) none} :=
  empty_entries_rejects_both _ (phase2_missing_dependency_no_entries m k hk)

/-- Canonical rows never identify two different actual support destinations.
The exact numerator is preserved for each branch, not just a Boolean support. -/
theorem canonical_branch_mass : ∀ s ∈ kernel, ∀ a ∈ actions,
    ∀ e ∈ actionRow .target s a,
    mass6 (runInputs6 canonical .target) (.inK s) a
      (predictive6 (runInputs6 canonical .target) e.1) = e.2 := by decide

theorem baseline_branch_simulation (r : Run) (h : FactorContext baseline r)
    (d : Disturbance) (a : Action) (o : Ambient)
    (ho : StrategyGame.PositiveSupport (rows baseline) r d a o) :
    StrategyGame.PositiveSupport (POS04GameBinding.rows baseline) r d a
      (predictive6 (POS04GameBinding.data baseline) o) ∧
    update baseline r d a o = POS04GameBinding.update baseline r d a
      (predictive6 (POS04GameBinding.data baseline) o) := by
  obtain ⟨s,hs⟩ := h.2
  obtain ⟨n,hm,hn⟩ := baseline_support r h d a o ho
  have hproj : projection r = s := by simp [projection,hs]
  rw [hproj] at hm
  have hmass := canonical_branch_mass s (by cases s <;> decide) a (by cases a <;> decide) (o,n) hm
  have hweight : weight6 (POS04GameBinding.data baseline) r a
      (predictive6 (POS04GameBinding.data baseline) o) = (n : Rat)/4 := by
    have he := (baseline_resource r h.1).2.2.2.2
    rw [baseline_data] at he
    simp only [baseline_data,weight6,he,if_true,hs,hmass]
  have hpositive : 0 < (n : Rat)/4 := by
    have hnonempty : (actionRow .target s a).isEmpty = false := by
      cases hl : actionRow .target s a with
      | nil => simp [hl] at hm
      | cons e es => rfl
    exact of_decide_eq_true (List.all_eq_true.mp (canonical_probability_rows s a hnonempty).1 (o,n) hm)
  constructor
  · refine ⟨(n : Rat)/4,?_,hpositive⟩
    simp only [POS04GameBinding.rows,if_pos baseline_dependencies]
    exact List.mem_map.mpr ⟨_,outcomes6_cover _ o,by simp only [hweight]⟩
  · change actualUpdate6 (POS04GameBinding.data baseline) r a o =
      update6 (POS04GameBinding.data baseline) r a (predictive6 (POS04GameBinding.data baseline) o)
    rw [baseline_data]
    exact canonical_actual_step6 .target r a s (o,n) hm

/-- Strategy-play simulation keeps the SAME actual run states and every raw
support branch. The invariant/context lift, rather than an arbitrary
representative choice, supplies the induction premise. -/
theorem baseline_play_simulation
    (strategy : StrategyGame.Strategy Run Disturbance Action) (entry : Run)
    (contexts : ∀ r past, StrategyGame.Play (rows baseline) (update baseline) strategy entry (r :: past) →
      FactorContext baseline r)
    {history : List Run}
    (hp : StrategyGame.Play (rows baseline) (update baseline) strategy entry history) :
    StrategyGame.Play (POS04GameBinding.rows baseline) (POS04GameBinding.update baseline) strategy entry history := by
  induction hp with
  | initial => exact StrategyGame.Play.initial
  | @step r past earlier d o supported ih =>
    have hs := baseline_branch_simulation r (contexts r past earlier) d (strategy (r :: past) d) o supported
    rw [hs.2]
    exact StrategyGame.Play.step ih d _ hs.1


/-- All nominal disturbance words are answered; each play admits every actual
positive-support branch of the response chosen by the causal strategy. -/
theorem baseline_answers_every_word :
    ∃ strategy, ∀ entry, POS04GameBinding.Entries baseline entry → ∀ word : List Disturbance,
      ∃ final, StrategyGame.WordExecution (rows baseline) (update baseline) strategy [entry] word final ∧
        StrategyGame.Play (rows baseline) (update baseline) strategy entry final :=
  StrategyGame.game_answers_every_word baseline_full_autonomy

/-- Close the simulation's context premise with the constructed finite lift.
There is no additional context-irrelevance assumption. -/
theorem baseline_constructed_play_simulation
    (entry : Run) (he : POS04GameBinding.Entries baseline entry) {history : List Run}
    (hp : StrategyGame.Play (rows baseline) (update baseline)
      (StrategyGame.causalStrategy (rows baseline) (update baseline)
        (POS04GameBinding.Entries baseline) (POS04GameBinding.Withdrawal baseline)
        (PackageAt baseline) (POS04GameBinding.ResourceClosed baseline)
        (POS04GameBinding.Legal baseline) (StepLaw baseline) baseline_full_certificate) entry history) :
    StrategyGame.Play (POS04GameBinding.rows baseline) (POS04GameBinding.update baseline)
      (StrategyGame.causalStrategy (rows baseline) (update baseline)
        (POS04GameBinding.Entries baseline) (POS04GameBinding.Withdrawal baseline)
        (PackageAt baseline) (POS04GameBinding.ResourceClosed baseline)
        (POS04GameBinding.Legal baseline) (StepLaw baseline) baseline_full_certificate) entry history := by
  apply baseline_play_simulation _ entry _ hp
  intro r past hplay
  exact (GameFiniteConstructor.finite_lift_play_context
    (fun s => by cases s <;> decide) (POS04Adapter.full_retain_monotone baseline)
    baseline_full_lift he hplay).1

end CSTTT.TargetTheory.GenericHandoff.POS04ActualGame
