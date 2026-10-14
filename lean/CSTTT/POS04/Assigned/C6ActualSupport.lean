import CSTTT.POS04.Assigned.C6Acceptance

/-! Actual-support refinement of the predictive C6 observer. The raw action
row supplies actual Ambient outcomes, including every positive branch. The
quotient future remains an observational model; it is not the autonomy updater.
No representative is selected by the actual updater. Authority:
M3_model_spec.md:22,30–33 and G6_lane_spec.md:147–300. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.TransportTheory

def actualRows6 (d : RunInputs6) (x : Run6) (a : Action) : List (Ambient × Rat) :=
  if enabled6 d x then (row6 d x.factor a).map fun e => (e.1,(e.2 : Rat) / 4)
  else []
def actualUpdate6 (d : RunInputs6) (x : Run6) (a : Action) (o : Ambient) : Run6 :=
  ⟨o,x.counter + 1,x.ticks + delta6 d x.factor a,x.residue,
   x.funded && decide (budgetAfter6 d > 0)⟩

structure ActualUpdateLaws6 (d : RunInputs6) (tag : Tag) (x : Run6)
    (a : Action) (o : Ambient) : Prop where
  factor : (actualUpdate6 d x a o).factor = o
  counter : (actualUpdate6 d x a o).counter = x.counter + 1
  ticks : (actualUpdate6 d x a o).ticks = x.ticks + delta6 d x.factor a
  progress : (observation6 d tag (actualUpdate6 d x a o)).cumulativeProgress = x.counter + 1
  record : (observation6 d tag (actualUpdate6 d x a o)).endogenousRecordCount =
    if (x.funded && decide (budgetAfter6 d > 0)) && writer6 d tag x.residue then x.counter + 1 else 0
  residue : (actualUpdate6 d x a o).residue = x.residue
  maintenance : (actualUpdate6 d x a o).funded = (x.funded && decide (budgetAfter6 d > 0))
  owner : (observation6 d tag (actualUpdate6 d x a o)).owner = d.resource.owner

theorem actual_update_laws6 (d : RunInputs6) (tag : Tag) (x : Run6) (a : Action) (o : Ambient) :
    ActualUpdateLaws6 d tag x a o := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Full observation and code commute with quotienting; the actual factor
is NOT identified with a chosen representative by this general theorem. -/
theorem actual_quotient_step6 (d : RunInputs6) (tag : Tag) (x : Run6) (a : Action) (o : Ambient) :
    code6 d (actualUpdate6 d x a o) = code6 d (update6 d x a (predictive6 d o)) ∧
    observation6 d tag (actualUpdate6 d x a o) =
      observation6 d tag (update6 d x a (predictive6 d o)) := by
  have hp := representative6_exact d (predictive6 d o) (outcomes6_cover d o)
  constructor <;> simp only [code6,observation6,actualUpdate6,update6,hp]

/-- Every actual canonical POS-04 successor is already a class representative.
This covers ALL actions, not just the canonical policy. It is a finite fact
about this model, not a premise for arbitrary assigned rows. -/
theorem canonical_actual_successors6 (tag : Tag) :
    ∀ s ∈ kernel, ∀ a ∈ actions, ∀ e ∈ actionRow tag s a,
      representative6 (runInputs6 canonical tag) (predictive6 (runInputs6 canonical tag) e.1) = e.1 := by
  cases tag <;> decide

theorem canonical_actual_step6 (tag : Tag) (x : Run6) (a : Action) (s : KState)
    (e : Ambient × Nat) (he : e ∈ actionRow tag s a) :
    actualUpdate6 (runInputs6 canonical tag) x a e.1 =
      update6 (runInputs6 canonical tag) x a (predictive6 (runInputs6 canonical tag) e.1) := by
  have h := canonical_actual_successors6 tag s (by cases s <;> decide) a
    (by cases a <;> decide) e he
  simp only [actualUpdate6,update6,h]

theorem actual_factor_preserved6 (d : RunInputs6) (x : Run6) (a : Action) (o : Ambient) :
    (actualUpdate6 d x a o).factor = o := rfl

/-- Probabilities pushed forward to predictive classes, with no branch lost.
This equality holds for arbitrary decoded rows, not just the canonical tables. -/
private theorem numerator_sum (xs : List (Ambient × Nat)) (n : Nat) :
    ((xs.map fun e => (e.2 : Rat)/4).sum) + (n : Rat)/4 =
      ((xs.foldl (fun (n : Nat) e => n + e.2) n : Nat) : Rat)/4 := by
  induction xs generalizing n with
  | nil => simp only [List.map_nil,List.sum_nil,List.foldl_nil,Rat.zero_add]
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons,List.foldl_cons]
    have hadd : (e.2 : Rat)/4 + (n : Rat)/4 = ((n+e.2 : Nat) : Rat)/4 := by
      simp only [Rat.natCast_add,Rat.div_def,Rat.add_mul]
      exact Rat.add_comm _ _
    rw [Rat.add_assoc,Rat.add_left_comm ((e.2 : Rat)/4),hadd,ih]

theorem actual_probability_pushforward6 (d : RunInputs6) (x : Run6) (a : Action) (c : PredictiveNow) :
    (((actualRows6 d x a).filter fun e => decide (predictive6 d e.1 = c)).map Prod.snd).sum =
      weight6 d x a c := by
  by_cases he : enabled6 d x = true
  · simp only [actualRows6,he,if_true,List.filter_map,List.map_map,Function.comp_def,weight6,mass6]
    have h := numerator_sum ((row6 d x.factor a).filter fun e => decide (predictive6 d e.1 = c)) 0
    simpa only [show ((0 : Nat) : Rat)/4 = 0 from by decide +kernel,Rat.add_zero] using h
  · have hf : enabled6 d x = false := Bool.eq_false_iff.mpr he
    simp [actualRows6,weight6,hf]

/-- Actual outcome probability, retaining the full raw factor rather than
collapsing it to the predictive class. -/
def actualWeight6 (d : RunInputs6) (x : Run6) (a : Action) (o : Ambient) : Rat :=
  (((actualRows6 d x a).filter fun e => decide (e.1 = o)).map Prod.snd).sum

def actualFuture6 (a : Assignment) (tag : Tag) : FullFutureModel Run6 Action Ambient C6Code C6Observation :=
  let d := runInputs6 a tag
  ⟨ambientStates,code6 d,observation6 d tag,actualWeight6 d,actualUpdate6 d⟩

/-- A raw, stronger (outcome-resolving) bisimulation check. It is proved on
canonical data; no extra hypothesis is added to the existing C6 acceptance. -/
def ActualBisim6 (d : RunInputs6) : Prop :=
  ∀ s ∈ ambientStates, ∀ t ∈ ambientStates, ∀ a ∈ actions,
    predictive6 d s = predictive6 d t → row6 d s a = row6 d t a ∧ delta6 d s a = delta6 d t a

theorem actual_bisim_all_states6 (a : Assignment) (tag : Tag)
    (h : ActualBisim6 (runInputs6 a tag)) : FullOneStepBisim (actualFuture6 a tag) := by
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
  constructor
  · change observation6 d tag x = observation6 d tag y
    simp only [observation6,hp,hn,ht,hr,hf]
  · intro act o
    obtain ⟨hrow,hdelta⟩ := h x.factor (hs _) y.factor (hs _) act (by cases act <;> decide) hp
    change row6 d x.factor act = row6 d y.factor act at hrow
    constructor
    · change actualWeight6 d x act o = actualWeight6 d y act o
      simp only [actualWeight6,actualRows6,enabled6,hf,hrow]
    · change code6 d (actualUpdate6 d x act o) = code6 d (actualUpdate6 d y act o)
      have hm : (x.ticks + delta6 d x.factor act) % 2 = (y.ticks + delta6 d y.factor act) % 2 := by
        rw [Nat.add_mod x.ticks,Nat.add_mod y.ticks,ht,hdelta]
      simp only [code6,actualUpdate6,hn,hr,hf,hm]

theorem canonical_actual_bisim6 (tag : Tag) : ActualBisim6 (runInputs6 canonical tag) := by
  cases tag <;> unfold ActualBisim6 <;> decide

theorem canonical_actual_all_words6 (tag : Tag) : FullFutureSufficient (actualFuture6 canonical tag) :=
  full_future_sufficient_of_bisim _ (actual_bisim_all_states6 _ _ (canonical_actual_bisim6 tag))


theorem actual_future_readouts6 (a : Assignment) (tag : Tag) :
    (actualFuture6 a tag).code = (future6 a tag).code ∧
    (actualFuture6 a tag).observe = (future6 a tag).observe := ⟨rfl,rfl⟩

theorem canonical_actual_coarser6 (tag : Tag) :
    (actualFuture6 canonical tag).code (initial6 canonical tag .p0w0 .a) =
      (actualFuture6 canonical tag).code (initial6 canonical tag .p0w1 .a) ∧
    initial6 canonical tag .p0w0 .a ≠ initial6 canonical tag .p0w1 .a :=
  (canonical_accept6 tag).2.2

end CSTTT.POS04.Assigned
