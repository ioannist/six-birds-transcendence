import CSTTT.POS04.Assigned.C6ReadoutGuards
/-! G2b-3b: raw finite equations imply an all-state bisimulation, hence all
finite word laws. No closure restriction or supplied future function. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.TransportTheory

def projectedRow6 (d : RunInputs6) (s : Ambient) (act : Action) :=
  (row6 d s act).map fun e => (predictive6 d e.1,e.2)
def FiniteBisim6 (d : RunInputs6) : Prop :=
  ∀ s ∈ ambientStates, ∀ t ∈ ambientStates, ∀ act ∈ actions,
    predictive6 d s = predictive6 d t →
    ((outcomes6 d).all fun o => decide (mass6 d s act o = mass6 d t act o)) = true ∧
    delta6 d s act = delta6 d t act

theorem mass6_projected (d : RunInputs6) (s : Ambient) (act : Action) (o : PredictiveNow) :
    mass6 d s act o = ((projectedRow6 d s act).filter fun e => decide (e.1 = o)).foldl
      (fun n e => n + e.2) 0 := by
  simp only [projectedRow6,List.filter_map,List.foldl_map,mass6,Function.comp_def]

theorem mass6_absent (d : RunInputs6) (s : Ambient) (act : Action) (o : PredictiveNow)
    (ho : o ∉ outcomes6 d) : mass6 d s act o = 0 := by
  have he : (row6 d s act).filter (fun e => decide (predictive6 d e.1 = o)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e _ h
    have hp : predictive6 d e.1 = o := of_decide_eq_true h
    exact ho (hp ▸ outcomes6_cover d e.1)
  simp only [mass6,he,List.foldl_nil]

theorem bisim6_all_states (a : Assignment) (tag : Tag)
    (h : FiniteBisim6 (runInputs6 a tag)) : FullOneStepBisim (future6 a tag) := by
  let d := runInputs6 a tag
  intro x y hc
  have hp : predictive6 d x.factor = predictive6 d y.factor := congrArg C6Code.predictive hc
  have hn : x.counter = y.counter := congrArg C6Code.eventCount hc
  have ht : x.ticks % 2 = y.ticks % 2 := congrArg C6Code.tickPhase hc
  have hr : x.residue = y.residue := congrArg C6Code.routeResidue hc
  have hf : x.funded = y.funded := congrArg C6Code.maintenance hc
  have hs (s : Ambient) : s ∈ ambientStates := by
    cases s with
    | inK k => cases k <;> decide
    | p2w0 => decide
    | p5w1 => decide
  have ha (act : Action) : act ∈ actions := by cases act <;> decide
  constructor
  · change observation6 d tag x = observation6 d tag y
    simp only [observation6,hp,hn,ht,hr,hf]
  · intro act o
    obtain ⟨hmasses,hdelta⟩ := h x.factor (hs _) y.factor (hs _) act (ha _) hp
    constructor
    · change weight6 d x act o = weight6 d y act o
      have hm : mass6 d x.factor act o = mass6 d y.factor act o := by
        by_cases ho : o ∈ outcomes6 d
        · exact of_decide_eq_true (List.all_eq_true.mp hmasses o ho)
        · rw [mass6_absent d _ _ _ ho,mass6_absent d _ _ _ ho]
      simp only [weight6,enabled6,hf,hm]
    · change code6 d (update6 d x act o) = code6 d (update6 d y act o)
      change delta6 d x.factor act = delta6 d y.factor act at hdelta
      have hm : (x.ticks + delta6 d x.factor act) % 2 =
          (y.ticks + delta6 d y.factor act) % 2 := by
        rw [Nat.add_mod x.ticks, Nat.add_mod y.ticks,ht,hdelta]
      simp only [code6,update6,hn,hr,hf,hm]

theorem assigned6_all_words (a : Assignment) (tag : Tag)
    (h : FiniteBisim6 (runInputs6 a tag)) : FullFutureSufficient (future6 a tag) :=
  full_future_sufficient_of_bisim _ (bisim6_all_states a tag h)

theorem canonical_finite_bisim6 (tag : Tag) : FiniteBisim6 (runInputs6 canonical tag) := by
  cases tag <;> unfold FiniteBisim6 <;> decide

theorem canonical_all_states_future6 (tag : Tag) : FullFutureSufficient (future6 canonical tag) :=
  assigned6_all_words canonical tag (canonical_finite_bisim6 tag)

theorem closure6_all_words (a : Assignment) (tag : Tag)
    (h : FiniteBisim6 (runInputs6 a tag)) (x y : Run6)
    (_hx : Closure6 a tag x) (_hy : Closure6 a tag y)
    (hc : (future6 a tag).code x = (future6 a tag).code y) (word : List Action) (trace : List C6Observation) :
    fullFuture (future6 a tag) x word trace = fullFuture (future6 a tag) y word trace :=
  assigned6_all_words a tag h x y hc word trace

/-- Resolve raw-image order by expanding the nine summands and using exact
Rat additive laws. The induction remains over every finite word. -/
theorem canonical_word_law6 (tag : Tag) (x : Run6) (word : List Action) (trace : List C6Observation) :
    fullFuture (future6 canonical tag) x word trace =
      fullFuture pos04FullFuture (legacyRun6 tag x) word trace := by
  induction word generalizing x trace with
  | nil => simp only [fullFuture,future6,canonical_observation6,pos04FullFuture]
  | cons act rest ih =>
    cases trace with
    | nil => rfl
    | cons first tail =>
      simp only [fullFuture]
      change (if first = observation6 (runInputs6 canonical tag) tag x then
        ((outcomes6 (runInputs6 canonical tag)).map fun o =>
          weight6 (runInputs6 canonical tag) x act o * fullFuture (future6 canonical tag)
            (update6 (runInputs6 canonical tag) x act o) rest tail).sum else 0) =
        (if first = observe .positive (legacyRun6 tag x) then
          (outcomeClasses.map fun o => pos04FullFuture.weight (legacyRun6 tag x) act o *
            fullFuture pos04FullFuture (pos04FullFuture.next (legacyRun6 tag x) act o) rest tail).sum
          else 0)
      rw [canonical_observation6]
      by_cases ho : first = observe .positive (legacyRun6 tag x)
      · simp only [ho,if_true]
        rw [canonical_outcomes6,List.map_map]
        have hterm (o : OutcomeClass) :
            weight6 (runInputs6 canonical tag) x act (legacyOutcome6 tag o) *
              fullFuture (future6 canonical tag)
                (update6 (runInputs6 canonical tag) x act (legacyOutcome6 tag o)) rest tail =
            pos04FullFuture.weight (legacyRun6 tag x) act o *
              fullFuture pos04FullFuture (pos04FullFuture.next (legacyRun6 tag x) act o) rest tail := by
          change (future6 canonical tag).weight x act (legacyOutcome6 tag o) * _ = _
          rw [canonical_weight6_fullfuture,ih]
          change _ = _
          rw [← canonical_update6_fullfuture]
          rfl
        simp only [Function.comp_def]
        simp only [outcomeClasses,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
        rw [hterm .m0,hterm .m1,hterm .m2,hterm .exit2,hterm .m3,hterm .m4,hterm .m5,hterm .m6,hterm .exit5]
        simp only [Rat.add_assoc,Rat.add_comm,Rat.add_left_comm]
      · simp only [ho,if_false]

theorem canonical_word_law6_L6a (tag : Tag) (x : Run6) (word : List Action) (trace : List C6Observation) :
    fullFuture (future6 canonical tag) x word trace = F .positive (legacyRun6 tag x) word trace :=
  (canonical_word_law6 tag x word trace).trans (pos04_full_future_eq_c6 _ _ _)

def eraseTag6 (x : C6State) : Run6 := ⟨x.factor,x.eventCount,x.tickCount,x.routeResidue,x.funded⟩
theorem legacyRun6_erase (x : C6State) : legacyRun6 x.tag (eraseTag6 x) = x := by cases x <;> rfl

/-- Exact all-state quantifier, including arbitrary counters, residue and
funded bits. No claim that all such runs occur in the audit closure. -/
theorem canonical_future6_legacy_quantifier :
    (∀ tag, FullFutureSufficient (future6 canonical tag)) ↔ C6FutureSufficient .positive := by
  constructor
  · intro h x y hc word trace
    have ht := code_equal_tags hc
    have he : legacyRun6 x.tag (eraseTag6 y) = y := by rw [ht]; exact legacyRun6_erase y
    have hcode : code6 (runInputs6 canonical x.tag) (eraseTag6 x) =
        code6 (runInputs6 canonical x.tag) (eraseTag6 y) := by
      rw [canonical_code6,canonical_code6,legacyRun6_erase,he]
      exact hc
    have hh := h x.tag (eraseTag6 x) (eraseTag6 y) hcode word trace
    rw [canonical_word_law6_L6a,canonical_word_law6_L6a,legacyRun6_erase,he] at hh
    exact hh
  · intro h tag x y hc word trace
    rw [canonical_word_law6_L6a,canonical_word_law6_L6a]
    apply h
    change code6 (runInputs6 canonical tag) x = code6 (runInputs6 canonical tag) y at hc
    rwa [canonical_code6,canonical_code6] at hc

end CSTTT.POS04.Assigned
