import CSTTT.POS04.Assigned.C6Dynamics
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.TransportTheory

def canonicalRunInputs6 (tag : Tag) : RunInputs6 :=
  ⟨canonicalExtra tag,tickIncrement tag,
   ⟨resourceOwner tag,rechargeAvailableAfterWithdrawal tag⟩,ledger,futureInterface⟩
theorem canonical_run_inputs6 (tag : Tag) : runInputs6 canonical tag = canonicalRunInputs6 tag := by
  cases tag <;> rfl

theorem canonical_predictive6 (tag : Tag) (s : Ambient) :
    predictive6 (runInputs6 canonical tag) s = predictiveNow tag s := by
  cases tag <;> cases s with
  | inK k => cases k <;> decide
  | p2w0 => rfl
  | p5w1 => rfl

theorem canonical_M6_link (tag : Tag) (s t : KState) :
    predictive6 (runInputs6 canonical tag) (.inK s) =
      predictive6 (runInputs6 canonical tag) (.inK t) ↔ taggedMClass tag s = taggedMClass tag t := by
  rw [canonical_predictive6,canonical_predictive6]
  simpa only [predictiveNow,PredictiveNow.active.injEq] using rawM_iff_imported_M tag s t

def legacyOutcome6 (tag : Tag) (o : OutcomeClass) : PredictiveNow :=
  predictiveNow tag (classRepresentative o)
theorem canonical_outcomes6 (tag : Tag) :
    outcomes6 (runInputs6 canonical tag) =
      ([.m0,.m1,.m2,.exit2,.m3,.m4,.m5,.m6,.exit5] : List OutcomeClass).map (legacyOutcome6 tag) := by
  cases tag <;> decide
theorem canonical_representative6 (tag : Tag) (o : OutcomeClass) :
    representative6 (runInputs6 canonical tag) (legacyOutcome6 tag o) = classRepresentative o := by
  cases tag <;> cases o <;> decide
theorem canonical_mass6 (tag : Tag) (s : Ambient) (act : Action) (o : OutcomeClass) :
    mass6 (runInputs6 canonical tag) s act (legacyOutcome6 tag o) = classMass tag s act o := by
  cases tag <;> cases s with
  | inK k => cases k <;> cases act <;> cases o <;> decide
  | p2w0 => cases act <;> cases o <;> decide
  | p5w1 => cases act <;> cases o <;> decide

def legacyRun6 (tag : Tag) (x : Run6) : C6State :=
  ⟨tag,x.factor,x.counter,x.ticks,x.residue,x.funded⟩
def LedgerConservation6 (a : Assignment) (tag : Tag) : Prop :=
  budgetAfter6 (runInputs6 a tag) = budget6 (runInputs6 a tag)
theorem canonical_ledger_conservation6 (tag : Tag) : LedgerConservation6 canonical tag := by
  cases tag <;> rfl

theorem canonical_code6 (tag : Tag) (x : Run6) :
    code6 (runInputs6 canonical tag) x = q (legacyRun6 tag x) := by
  simp only [code6,q,legacyRun6,canonical_predictive6]
  cases tag <;> rfl

theorem canonical_writer6 (tag : Tag) (residue : List KState × List EventId) :
    writer6 (runInputs6 canonical tag) tag residue = writerForResidue .positive tag residue := by
  rw [canonical_run_inputs6]
  have ht (id : RouteId) : routeTuple (canonicalExtra tag) id = some (routeRegister id) := by
    cases tag <;> cases id <;> rfl
  change (if routeTuple (canonicalExtra tag) .a = some residue then recordWriterAvailable tag .a
      else if routeTuple (canonicalExtra tag) .b = some residue then recordWriterAvailable tag .b
      else false) = writerForResidue .positive tag residue
  rw [ht .a,ht .b]
  simp only [Option.some.injEq]
  simp only [eq_comm (a := routeRegister .a) (b := residue),
    eq_comm (a := routeRegister .b) (b := residue)]
  simp only [writerForResidue,c6Writer,recordWriterAvailable]
  by_cases ha : residue = routeRegister .a <;> by_cases hb : residue = routeRegister .b <;>
    simp [ha,hb]

theorem canonical_observation6 (tag : Tag) (x : Run6) :
    observation6 (runInputs6 canonical tag) tag x = observe .positive (legacyRun6 tag x) := by
  simp only [observation6,observe,legacyRun6,canonical_predictive6,canonical_writer6]
  cases tag <;> rfl

theorem canonical_weight6 (tag : Tag) (x : Run6) (act : Action) (o : OutcomeClass) :
    weight6 (runInputs6 canonical tag) x act (legacyOutcome6 tag o) =
    pos04RawFutureRow (legacyRun6 tag x) act o := by
  rw [weight6,canonical_mass6]
  have he : enabled6 (runInputs6 canonical tag) x =
      (x.funded && rechargeAvailableAfterWithdrawal tag) := by cases tag <;> simp [enabled6,runInputs6,decode,clauseScope,commonScope,canonical,canonicalValue,budget6,ledger,rechargeAvailableAfterWithdrawal]
  rw [he]
  rfl

theorem canonical_update6 (tag : Tag) (x : Run6) (act : Action) (o : OutcomeClass) :
    legacyRun6 tag (update6 (runInputs6 canonical tag) x act (legacyOutcome6 tag o)) =
    pos04RawFutureUpdate (legacyRun6 tag x) act o := by
  rw [update6,canonical_representative6]
  cases tag <;> cases h : x.factor with
  | inK k => simp [legacyRun6,pos04RawFutureUpdate,runInputs6,decode,clauseScope,commonScope,
      canonical,canonicalValue,delta6,budgetAfter6,budget6,rawFutureBudgetAfter,rawFutureBudget,ledger,h]
  | p2w0 => simp [legacyRun6,pos04RawFutureUpdate,runInputs6,decode,clauseScope,commonScope,
      canonical,canonicalValue,delta6,budgetAfter6,budget6,rawFutureBudgetAfter,rawFutureBudget,ledger,h]
  | p5w1 => simp [legacyRun6,pos04RawFutureUpdate,runInputs6,decode,clauseScope,commonScope,
      canonical,canonicalValue,delta6,budgetAfter6,budget6,rawFutureBudgetAfter,rawFutureBudget,ledger,h]

/-- Component links to G1b's actual full-interface model, not just the
older C6 candidate. The alphabet-order sum transport remains the next seam. -/
theorem canonical_weight6_fullfuture (tag : Tag) (x : Run6) (act : Action) (o : OutcomeClass) :
    (future6 canonical tag).weight x act (legacyOutcome6 tag o) =
      pos04FullFuture.weight (legacyRun6 tag x) act o :=
  (canonical_weight6 tag x act o).trans (pos04_raw_future_weight_link _ _ _).symm

theorem canonical_update6_fullfuture (tag : Tag) (x : Run6) (act : Action) (o : OutcomeClass) :
    legacyRun6 tag ((future6 canonical tag).next x act (legacyOutcome6 tag o)) =
      pos04FullFuture.next (legacyRun6 tag x) act o :=
  (canonical_update6 tag x act o).trans (pos04_raw_future_successor_link _ _ _).symm

def initial6 (a : Assignment) (tag : Tag) (s : KState) (id : RouteId) : Run6 :=
  let d := runInputs6 a tag
  ⟨.inK s,0,0,(routeTuple d.base id).getD ([],[]),d.base.receiver.funded⟩
theorem canonical_initial6_root (tag : Tag) (s : KState) (id : RouteId) :
    Closure6 canonical tag (initial6 canonical tag s id) := by
  apply FutureClosure.root
  cases tag <;> cases s <;> cases id <;> decide

def firstStep6 (tag : Tag) := update6 (runInputs6 canonical tag)
  (initial6 canonical tag .p1w0 .a) .cw (legacyOutcome6 tag .m3)
def secondStep6 (tag : Tag) := update6 (runInputs6 canonical tag)
  (firstStep6 tag) .stay (legacyOutcome6 tag .m1)
def thirdStep6 (tag : Tag) := update6 (runInputs6 canonical tag)
  (secondStep6 tag) .cw (legacyOutcome6 tag .m3)

theorem canonical_three_step_closure6 (tag : Tag) : Closure6 canonical tag (thirdStep6 tag) := by
  have ho (o : OutcomeClass) : legacyOutcome6 tag o ∈ outcomes6 (runInputs6 canonical tag) := by
    simpa only [canonical_predictive6] using outcomes6_cover (runInputs6 canonical tag) (classRepresentative o)
  exact closure6_step (closure6_step (closure6_step
    (canonical_initial6_root tag .p1w0 .a) .cw _ (ho .m3)) .stay _ (ho .m1)) .cw _ (ho .m3)

theorem canonical_three_steps_supported6 (tag : Tag) :
    weight6 (runInputs6 canonical tag) (initial6 canonical tag .p1w0 .a) .cw (legacyOutcome6 tag .m3) = 1 ∧
    weight6 (runInputs6 canonical tag) (firstStep6 tag) .stay (legacyOutcome6 tag .m1) = 3/4 ∧
    weight6 (runInputs6 canonical tag) (secondStep6 tag) .cw (legacyOutcome6 tag .m3) = 1 := by
  cases tag <;>
    change (4 : Rat) / 4 = 1 ∧ (3 : Rat) / 4 = 3/4 ∧ (4 : Rat) / 4 = 1 <;> grind

theorem canonical_merged_roots6 (tag : Tag) :
    Closure6 canonical tag (initial6 canonical tag .p0w0 .a) ∧
    Closure6 canonical tag (initial6 canonical tag .p0w1 .a) ∧
    code6 (runInputs6 canonical tag) (initial6 canonical tag .p0w0 .a) =
      code6 (runInputs6 canonical tag) (initial6 canonical tag .p0w1 .a) ∧
    initial6 canonical tag .p0w0 .a ≠ initial6 canonical tag .p0w1 .a := by
  refine ⟨canonical_initial6_root _ _ _,canonical_initial6_root _ _ _,?_,?_⟩
  · cases tag <;> decide
  · cases tag <;> decide
end CSTTT.POS04.Assigned
