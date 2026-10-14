import CSTTT.Targets.ComputedFIACH.AssignmentBridge

/-! G6 assignment-owned bridge run laws. All evolving fields are recipes
from assigned C6; no observer or code candidate is supplied. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TransportTheory
set_option maxRecDepth 8192
set_option maxHeartbeats 400000

theorem assigned_positive_tick (a : Assignment) (tag : Tag) (h : C6Accept a tag)
    (x : Run6) (act : Action) (o : CSTTT.POS04.PredictiveNow)
    (hp : 0 < (if enabled6 (runInputs6 a tag) x then
      mass6 (runInputs6 a tag) x.factor act o else 0)) :
    0 < delta6 (runInputs6 a tag) x.factor act := by
  have hm : 0 < mass6 (runInputs6 a tag) x.factor act o := by
    split at hp
    · exact hp
    · omega
  have ht := h.1.2.2.1.2.2.2.1
  cases hf : x.factor with
  | p2w0 => simp [hf,mass6,row6] at hm
  | p5w1 => simp [hf,mass6,row6] at hm
  | inK s =>
    have hn : ((runInputs6 a tag).base.base.rows s act).isEmpty = false := by
      cases hr : (runInputs6 a tag).base.base.rows s act with
      | nil => simp [mass6,row6,hf,hr] at hm
      | cons e rest => rfl
    have hs : s ∈ kernel := by cases s <;> decide
    have ha : act ∈ actions := by cases act <;> decide
    have hw := List.all_eq_true.mp (List.all_eq_true.mp ht s hs) act ha
    have he : (runInputs6 a tag).ticks s act = 1 := by
      simpa only [hn,Bool.false_or,decide_eq_true_eq] using hw
    simp [delta6,he]

theorem assignment_bridge_readout_updates (m : RawLaneModel)
    (h : ∀ t : Tag, C6Accept (image m.assignment) t)
    (x : AcquisitionRun) (act : Action) (o : CSTTT.POS04.PredictiveNow) :
    BridgeReadoutUpdateAt (assignmentRawBridge m) x act o := by
  have ho : ∀ t : Tag, (runInputs6 (image m.assignment) t).resource.owner = t :=
    fun t => (h t).1.2.2.1.2.2.2.2.2.2
  have hr : ∀ t : Tag, (runInputs6 (image m.assignment) t).resource.rechargeAvailable = true :=
    fun t => (h t).1.2.2.1.2.1
  have hb : ∀ t : Tag, budget6 (runInputs6 (image m.assignment) t) = 1 := by
    intro t
    exact (h t).1.2.2.2.2.2.1
  have ha : ∀ t : Tag, budgetAfter6 (runInputs6 (image m.assignment) t) = 1 := by
    intro t
    have hu := (h t).1.2.2.2.2.2
    simp [budgetAfter6,budget6,hu.1,hu.2.1,hu.2.2.1]
  have hc : ∀ t : Tag, (runInputs6 (image m.assignment) t).ledger.actionCost = 1 :=
    fun t => (h t).1.2.2.2.2.2.2.1
  have hcs : tagCarrierId .source = ⟨0⟩ := rfl
  have hct : tagCarrierId .target = ⟨1⟩ := rfl
  rcases x with ⟨tag,run⟩
  refine {
    sourceFactor := rfl
    targetFactor := rfl
    predictive := rfl
    sourcePredictive := ?_
    targetPredictive := ?_
    counter := rfl
    ticks := rfl
    progress := rfl
    supportedAdvances := ?_
    residue := rfl
    maintenance := ?_
    ownerPreserved := rfl
    owner := rfl
    sourceOwner := ?_
    targetOwner := ?_
    writerNow := ?_
    writerNext := ?_
    enabledNow := ?_
    enabledNext := ?_
    recordNow := ?_
    recordNext := ?_ }
  · intro s hs
    cases tag <;> cases hf : run.factor <;>
      simp only [assignmentRawBridge,hf,↓reduceIte,Option.some.injEq] at hs
    all_goals try contradiction
    all_goals subst s; simp only [assignmentRawBridge,predictive6,hf]
  · intro s hs
    cases tag <;> cases hf : run.factor <;>
      simp only [assignmentRawBridge,hf,↓reduceIte,Option.some.injEq] at hs
    all_goals try contradiction
    all_goals subst s; simp only [assignmentRawBridge,predictive6,hf]
  · intro hp
    exact ⟨assigned_positive_tick _ tag (h tag) run act o hp,by change 0 < 1; decide⟩
  · change (run.funded && decide (budgetAfter6 (runInputs6 (image m.assignment) tag) > 0)) =
      (run.funded && decide (budgetAfter6 (runInputs6 (image m.assignment) .source) > 0))
    rw [ha tag,ha .source]
  · intro s hs
    cases tag
    · rfl
    · simp only [assignmentRawBridge] at hs
      contradiction
  · intro s hs
    cases tag
    · simp only [assignmentRawBridge] at hs
      contradiction
    · rfl
  all_goals cases tag <;>
    simp [assignmentRawBridge,update6,observation6,enabled6,ho,hr,hb,ha,hc,hcs,hct]

theorem assignment_bridge_weight (m : RawLaneModel) (t : Tag) (x : Run6)
    (act : Action) (o : CSTTT.POS04.PredictiveNow) :
    (bridgeFutureModel (assignmentRawBridge m)).weight (t,x) act o =
      (future6 (image m.assignment) t).weight x act o := by
  cases he : enabled6 (runInputs6 (image m.assignment) t) x <;>
    simp [bridgeFutureModel,bridgeRunDynamics,assignmentRawBridge,future6,weight6,he]
  all_goals decide +kernel

theorem assignment_bridge_code_same_tag (m : RawLaneModel) (t : Tag) (x y : Run6) :
    bridgeRunCode (assignmentRawBridge m) (t,x) = bridgeRunCode (assignmentRawBridge m) (t,y) ↔
      (future6 (image m.assignment) t).code x = (future6 (image m.assignment) t).code y := by
  simp [bridgeRunCode,bridgeCodeOfObservation,bridgeRunObservation,assignmentRawBridge,
    future6,code6,TemporalRunCode.mk.injEq,C6Code.mk.injEq]

theorem assignment_bridge_code_tag (m : RawLaneModel)
    (h : ∀ t : Tag, C6Accept (image m.assignment) t) (x y : AcquisitionRun)
    (hc : bridgeRunCode (assignmentRawBridge m) x = bridgeRunCode (assignmentRawBridge m) y) :
    x.1 = y.1 := by
  have ho := congrArg TemporalRunCode.owner hc
  change tagCarrierId (runInputs6 (image m.assignment) x.1).resource.owner =
    tagCarrierId (runInputs6 (image m.assignment) y.1).resource.owner at ho
  have hx : (runInputs6 (image m.assignment) x.1).resource.owner = x.1 :=
    (h x.1).1.2.2.1.2.2.2.2.2.2
  have hy : (runInputs6 (image m.assignment) y.1).resource.owner = y.1 :=
    (h y.1).1.2.2.1.2.2.2.2.2.2
  rw [hx,hy] at ho
  cases hx : x.1 <;> cases hy : y.1
  all_goals try rfl
  all_goals rw [hx,hy] at ho
  all_goals have hn : tagCarrierId .source ≠ tagCarrierId .target := by decide
  all_goals first | exact False.elim (hn ho) | exact False.elim (hn ho.symm)

/-- A genuine all-state bisimulation of the bridge-owned full interface.
The owner readout prevents cross-tag code equality. No horizon bound or
candidate future function appears. -/
theorem assignment_bridge_full_bisim (m : RawLaneModel)
    (h : ∀ t : Tag, C6Accept (image m.assignment) t) : BridgeFutureBisim (assignmentRawBridge m) := by
  intro x y hc
  have ht := assignment_bridge_code_tag m h x y hc
  rcases x with ⟨t,x⟩
  rcases y with ⟨u,y⟩
  change t = u at ht
  subst u
  have hcode := (assignment_bridge_code_same_tag m t x y).mp hc
  have hb := bisim6_all_states (image m.assignment) t (h t).2.1 x y hcode
  constructor
  · exact congrArg frozenObservation6 hb.1
  · intro act o
    refine ⟨?_,?_⟩
    · rw [assignment_bridge_weight,assignment_bridge_weight]
      exact (hb.2 act o).1
    · exact (assignment_bridge_code_same_tag m t _ _).mpr (hb.2 act o).2

theorem assignment_bridge_all_words (m : RawLaneModel)
    (h : ∀ t : Tag, C6Accept (image m.assignment) t) : BridgeFutureSufficient (assignmentRawBridge m) :=
  bridge_defined_future_sufficient _ (assignment_bridge_full_bisim m h)

end CSTTT.TargetTheory.ComputedFIACH
