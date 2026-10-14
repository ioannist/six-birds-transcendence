import CSTTT.Targets.GenericHandoff.FutureLumping
import CSTTT.Targets.GenericHandoff.POS04RegisterFuture

/-! Exact, actual-support C6 one-step class checks for arbitrary partial
POS-04 assignments. Existing FiniteBisim6 suffices; ActualBisim6 is NOT assumed.
There is no supplied quotient future at the new induction-engine boundary. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04FutureLumping
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.TransportTheory CSTTT.Objecthood.T1Audit

/-- All non-predictive next-code coordinates are constant across outcomes of
one step. Therefore its fibers are exactly the computed predictive fibers. -/
theorem next_code_fiber (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (x y : Run6)
    (act : Action) (o : Ambient) :
    WeightedFibers.mass ambientStates (FutureLumping.NextCode (actualFuture6 a tag) x act)
      (actualWeight6 (runInputs6 a tag) y act)
      (FutureLumping.NextCode (actualFuture6 a tag) x act o) =
      weight6 (runInputs6 a tag) y act (predictive6 (runInputs6 a tag) o) := by
  rw [← actual_weight_class_sum6]
  apply WeightedFibers.sum_congr
  intro p hp
  simp only [FutureLumping.NextCode,actualFuture6,code6,actualUpdate6,C6Code.mk.injEq]
  simp only [and_true]

/-- The existing raw finite class-mass/tick equations prove the new direct
actual-model check on ALL runs. No closure-only quantifier is substituted. -/
theorem one_step (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (_hc : CSTTT.POS04.Assigned.Complete (clauseScope tag .c6) a)
    (hf : FiniteBisim6 (runInputs6 a tag)) : FutureLumping.OneStep (actualFuture6 a tag) := by
  intro x y hcode
  have hq := bisim6_all_states a tag hf x y hcode
  refine ⟨hq.1,?_⟩
  intro act
  constructor
  · intro o ho
    exact ((actual_quotient_step6 _ tag x act o).1.trans
      (hq.2 act (predictive6 (runInputs6 a tag) o)).2).trans
        (actual_quotient_step6 _ tag y act o).1.symm
  · intro o ho
    change WeightedFibers.mass ambientStates (FutureLumping.NextCode (actualFuture6 a tag) x act)
      (actualWeight6 (runInputs6 a tag) x act) _ =
      WeightedFibers.mass ambientStates (FutureLumping.NextCode (actualFuture6 a tag) x act)
      (actualWeight6 (runInputs6 a tag) y act) _
    rw [next_code_fiber,next_code_fiber]
    exact (hq.2 act (predictive6 (runInputs6 a tag) o)).1

theorem all_words (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : CSTTT.POS04.Assigned.Complete (clauseScope tag .c6) a)
    (hf : FiniteBisim6 (runInputs6 a tag)) : FullFutureSufficient (actualFuture6 a tag) :=
  FutureLumping.all_words _ (one_step a tag hc hf)

theorem accepted_all_words {a : CSTTT.POS04.Assigned.Assignment} {tag : Tag} (h : C6Accept a tag) :
    FullFutureSufficient (actualFuture6 a tag) := all_words a tag h.1.1.1 h.2.1

theorem canonical_one_step (tag : Tag) : FutureLumping.OneStep (actualFuture6 canonical tag) :=
  one_step canonical tag (canonical_complete _) (canonical_finite_bisim6 tag)

end CSTTT.TargetTheory.GenericHandoff.POS04FutureLumping
