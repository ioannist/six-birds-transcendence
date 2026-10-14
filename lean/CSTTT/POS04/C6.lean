import CSTTT.POS04.C2C3

/-! C6 follows `audit/M3_model_spec.md:22,30-33`. The future interface is
predictive M, unfolded event order, tick phase, progress, endogenous record
count, route residue, maintenance state, and owner. The stochastic future law
below aggregates the raw action row by its observed predictive class. -/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

inductive C6Variant where
  | positive | negFuture | negRecord | missingMix1
  deriving DecidableEq, Repr

/-- `NEG-C6-FUTURE`: only target `p0w1/stay` gains a second tick. -/
def c6Tick (variant : C6Variant) (tag : Tag) (s : KState) (a : Action) : Nat :=
  if variant = .negFuture ∧ tag = .target ∧ s = .p0w1 ∧ a = .stay then 2
  else tickIncrement tag s a

/-- `NEG-C6-RECORD`: route B's target writer is unavailable. -/
def c6Writer (variant : C6Variant) (tag : Tag) (route : RouteId) : Bool :=
  if variant = .negRecord ∧ tag = .target ∧ route = .b then false
  else recordWriterAvailable tag route

def c6Realized (variant : C6Variant) : List Stage :=
  if variant = .missingMix1 then realizedStages.filter (· != .mix1)
  else realizedStages

def c6FundedTicks (variant : C6Variant) (tag : Tag) : Bool :=
  kernel.all fun s => actions.all fun a =>
    (actionRow tag s a).isEmpty || c6Tick variant tag s a == 1

def c6Writers (variant : C6Variant) (tag : Tag) : Bool :=
  !(routeIds.isEmpty) && routeIds.all (c6Writer variant tag)

def c6StrictEvents : Bool :=
  events.all fun e => e.atomic && e.strictStep &&
    ((stages.idxOf e.toStage) == (stages.idxOf e.fromStage) + 1)

def c6PathRealized (variant : C6Variant) (route : RouteId) : Bool :=
  let path := (routeOf route).eventPath
  !path.isEmpty &&
    path.all (fun id =>
      let e := eventOf id
      e.fromStage ∈ c6Realized variant && e.toStage ∈ c6Realized variant) &&
    (path.zip (path.drop 1)).all (fun pair =>
      (eventOf pair.1).toStage == (eventOf pair.2).fromStage)

def c6RealizedPaths (variant : C6Variant) : Bool :=
  c6Realized variant == stages &&
  !routeIds.isEmpty && routeIds.all (c6PathRealized variant) &&
  eventIds.all (fun id => routes.any (fun route => id ∈ route.eventPath))

def C6Trace (variant : C6Variant) (tag : Tag) : Prop :=
  receiver.funded = true ∧
  rechargeAvailableAfterWithdrawal tag = true ∧
  ledger.initialBudget ≥ ledger.actionCost ∧
  c6FundedTicks variant tag = true ∧
  c6Writers variant tag = true ∧
  c6StrictEvents = true ∧
  c6RealizedPaths variant = true ∧
  resourceOwner tag = tag

theorem c6_trace_each_tag (tag : Tag) : C6Trace .positive tag := by
  cases tag <;> unfold C6Trace <;> decide

theorem neg_c6_future_trace_fails : ¬ C6Trace .negFuture .target := by
  unfold C6Trace
  decide
theorem neg_c6_record_trace_fails : ¬ C6Trace .negRecord .target := by
  unfold C6Trace
  decide
theorem c6_missing_realized_stage_fails (tag : Tag) :
    ¬ C6Trace .missingMix1 tag := by
  cases tag <;> unfold C6Trace <;> decide

inductive PredictiveNow where
  | active (m : Nat × List (List Bool)) | exit2 | exit5
  deriving DecidableEq, BEq, Repr

def predictiveNow (tag : Tag) : Ambient → PredictiveNow
  | .inK s => .active (rawM tag s)
  | .p2w0 => .exit2
  | .p5w1 => .exit5

inductive OutcomeClass where
  | m0 | m1 | m2 | m3 | m4 | m5 | m6 | exit2 | exit5
  deriving DecidableEq, BEq, Repr

def outcomeClasses : List OutcomeClass :=
  [.m0,.m1,.m2,.m3,.m4,.m5,.m6,.exit2,.exit5]

def outcomeIndex : OutcomeClass → Nat
  | .m0 => 0 | .m1 => 1 | .m2 => 2 | .m3 => 3 | .m4 => 4
  | .m5 => 5 | .m6 => 6 | .exit2 => 7 | .exit5 => 8

def classOf (tag : Tag) : Ambient → OutcomeClass
  | .p2w0 => .exit2
  | .p5w1 => .exit5
  | .inK s =>
    match taggedMClass tag s with
    | 0 => .m0 | 1 => .m1 | 2 => .m2 | 3 => .m3
    | 4 => .m4 | 5 => .m5 | _ => .m6

def classRepresentative : OutcomeClass → Ambient
  | .m0 => .inK .p0w0 | .m1 => .inK .p1w0
  | .m2 => .inK .p1w1 | .m3 => .inK .p2w1
  | .m4 => .inK .p3w0 | .m5 => .inK .p4w0
  | .m6 => .inK .p5w0 | .exit2 => .p2w0 | .exit5 => .p5w1

theorem representative_preserves_predictive (tag : Tag) (factor : Ambient) :
    predictiveNow tag (classRepresentative (classOf tag factor)) =
      predictiveNow tag factor := by
  cases tag <;> cases factor with
  | inK s => cases s <;> decide
  | p2w0 => decide
  | p5w1 => decide

def c6Row (tag : Tag) (s : Ambient) (a : Action) : List (Ambient × Nat) :=
  match s with
  | .inK k => actionRow tag k a
  | .p2w0 | .p5w1 => []

def classMass (tag : Tag) (s : Ambient) (a : Action)
    (c : OutcomeClass) : Nat :=
  (c6Row tag s a).foldl (fun total entry =>
    if classOf tag entry.1 = c then total + entry.2 else total) 0

def classProfile (tag : Tag) (s : Ambient) (a : Action) : List Nat :=
  outcomeClasses.map (classMass tag s a)

/-- Finite weighted bisimulation check. Each row is aggregated by the raw
M partition (linked to imported T1 M in `rawM_iff_imported_M`), with exits
kept distinct. Its equality is over all nine outcome classes. -/
theorem class_profile_respects_predictive (tag : Tag) (s t : Ambient)
    (a : Action) (h : predictiveNow tag s = predictiveNow tag t) :
    classProfile tag s a = classProfile tag t a := by
  have hs : s ∈ ambientStates := by
    cases s with
    | inK k => cases k <;> decide
    | p2w0 => decide
    | p5w1 => decide
  have ht : t ∈ ambientStates := by
    cases t with
    | inK k => cases k <;> decide
    | p2w0 => decide
    | p5w1 => decide
  have ha : a ∈ actions := by cases a <;> decide
  have hFinite : ∀ u ∈ ambientStates, ∀ v ∈ ambientStates,
      ∀ b ∈ actions,
      predictiveNow tag u = predictiveNow tag v →
      classProfile tag u b = classProfile tag v b := by
    cases tag <;> decide
  exact hFinite s hs t ht a ha h

structure C6State where
  tag : Tag
  factor : Ambient
  eventCount : Nat
  tickCount : Nat
  routeResidue : List KState × List EventId
  funded : Bool
  deriving DecidableEq, Repr

structure C6Code where
  predictive : PredictiveNow
  eventCount : Nat
  tickPhase : Nat
  routeResidue : List KState × List EventId
  maintenance : Bool
  owner : Tag
  deriving DecidableEq, Repr

def q (x : C6State) : C6Code :=
  ⟨predictiveNow x.tag x.factor,x.eventCount,x.tickCount % 2,
   x.routeResidue,x.funded,resourceOwner x.tag⟩

def writerForResidue (variant : C6Variant) (tag : Tag)
    (residue : List KState × List EventId) : Bool :=
  if residue = routeRegister .a then c6Writer variant tag .a
  else if residue = routeRegister .b then c6Writer variant tag .b
  else false

structure C6Observation where
  predictive : PredictiveNow
  eventOrder : Nat
  tickPhase : Nat
  cumulativeProgress : Nat
  endogenousRecordCount : Nat
  routeResidue : List KState × List EventId
  maintenanceState : Bool
  owner : Tag
  deriving DecidableEq, Repr

def observe (variant : C6Variant) (x : C6State) : C6Observation :=
  ⟨predictiveNow x.tag x.factor,x.eventCount,x.tickCount % 2,
   x.eventCount,
   if x.funded && writerForResidue variant x.tag x.routeResidue then
     x.eventCount else 0,
   x.routeResidue,x.funded,resourceOwner x.tag⟩

def observeCode (variant : C6Variant) (code : C6Code) : C6Observation :=
  ⟨code.predictive,code.eventCount,code.tickPhase,code.eventCount,
   if code.maintenance && writerForResidue variant code.owner code.routeResidue then
     code.eventCount else 0,
   code.routeResidue,code.maintenance,code.owner⟩

theorem observe_factors_through_q (variant : C6Variant) (x : C6State) :
    observe variant x = observeCode variant (q x) := by
  cases h : x.tag <;> simp [observe,observeCode,q,resourceOwner,h]

theorem resource_owner_self (tag : Tag) : resourceOwner tag = tag := by
  cases tag <;> rfl

theorem code_equal_tags {x y : C6State} (h : q x = q y) :
    x.tag = y.tag := by
  have ho := congrArg C6Code.owner h
  calc
    x.tag = resourceOwner x.tag := (resource_owner_self x.tag).symm
    _ = resourceOwner y.tag := ho
    _ = y.tag := resource_owner_self y.tag

def c6Delta (variant : C6Variant) (tag : Tag) (factor : Ambient)
    (a : Action) : Nat :=
  match factor with
  | .inK s => c6Tick variant tag s a
  | .p2w0 | .p5w1 => 0

def positiveDelta : PredictiveNow → Nat
  | .active _ => 1
  | .exit2 | .exit5 => 0

theorem positive_delta_from_predictive (tag : Tag) (factor : Ambient)
    (a : Action) :
    c6Delta .positive tag factor a =
      positiveDelta (predictiveNow tag factor) := by
  cases tag <;> cases factor with
  | inK s => cases s <;> cases a <;> decide
  | p2w0 => cases a <;> decide
  | p5w1 => cases a <;> decide

def c6Next (variant : C6Variant) (x : C6State) (a : Action)
    (c : OutcomeClass) : C6State :=
  ⟨x.tag,classRepresentative c,x.eventCount + 1,
   x.tickCount + c6Delta variant x.tag x.factor a,
   x.routeResidue,x.funded⟩

def effectiveMass (x : C6State) (a : Action) (c : OutcomeClass) : Nat :=
  if x.funded && rechargeAvailableAfterWithdrawal x.tag then
    classMass x.tag x.factor a c else 0

def positiveNextCode (code : C6Code) (c : OutcomeClass) : C6Code :=
  ⟨predictiveNow code.owner (classRepresentative c),
   code.eventCount + 1,
   (code.tickPhase + positiveDelta code.predictive) % 2,
   code.routeResidue,code.maintenance,code.owner⟩

theorem positive_next_code (x : C6State) (a : Action)
    (c : OutcomeClass) :
    q (c6Next .positive x a c) = positiveNextCode (q x) c := by
  have hd := positive_delta_from_predictive x.tag x.factor a
  cases x.tag with
  | source =>
    simp only [q,c6Next,positiveNextCode,resourceOwner] at hd ⊢
    congr 1
    omega
  | target =>
    simp only [q,c6Next,positiveNextCode,resourceOwner] at hd ⊢
    congr 1
    omega

def F (variant : C6Variant) (x : C6State) :
    List Action → List C6Observation → Rat
  | [], trace => if trace = [observe variant x] then 1 else 0
  | a :: rest, trace =>
    match trace with
    | [] => 0
    | first :: tail =>
      if first = observe variant x then
        (outcomeClasses.map fun c =>
          ((effectiveMass x a c : Rat) / 4) *
            F variant (c6Next variant x a c) rest tail).sum
      else 0

def C6Bisim (variant : C6Variant) : Prop :=
  ∀ x y : C6State, q x = q y →
    observe variant x = observe variant y ∧
    ∀ a : Action,
      classProfile x.tag x.factor a = classProfile y.tag y.factor a ∧
      ∀ c : OutcomeClass,
        q (c6Next variant x a c) = q (c6Next variant y a c)

theorem class_mass_of_profile_eq (tag : Tag) (s t : Ambient)
    (a : Action) (h : classProfile tag s a = classProfile tag t a)
    (c : OutcomeClass) : classMass tag s a c = classMass tag t a c := by
  have hEntry := congrArg
    (fun xs : List Nat => xs.getD (outcomeIndex c) 0) h
  cases c <;> simpa [classProfile,outcomeClasses,outcomeIndex] using hEntry

theorem positive_bisim : C6Bisim .positive := by
  intro x y hCode
  have hTag : x.tag = y.tag := code_equal_tags hCode
  have hPred := congrArg C6Code.predictive hCode
  have hProfile : ∀ a : Action,
      classProfile x.tag x.factor a = classProfile y.tag y.factor a := by
    intro a
    rw [hTag]
    exact class_profile_respects_predictive y.tag x.factor y.factor a
      (by simpa [q,hTag] using hPred)
  constructor
  · rw [observe_factors_through_q,observe_factors_through_q,hCode]
  · intro a
    constructor
    · exact hProfile a
    · intro c
      rw [positive_next_code,positive_next_code,hCode]

/-- The induction uses the verified one-step bisimulation for both weighted
class masses and code-equal successors. No word-length bound is used. -/
theorem future_eq_of_bisim (variant : C6Variant) (hb : C6Bisim variant) :
    ∀ word : List Action, ∀ x y : C6State, q x = q y →
      ∀ trace : List C6Observation, F variant x word trace = F variant y word trace := by
  intro word
  induction word with
  | nil =>
    intro x y hCode trace
    have hObs := (hb x y hCode).1
    simp [F,hObs]
  | cons a rest ih =>
    intro x y hCode trace
    have hObs := (hb x y hCode).1
    have hProfile := ((hb x y hCode).2 a).1
    have hNext := ((hb x y hCode).2 a).2
    cases trace with
    | nil => rfl
    | cons first tail =>
      simp only [F]
      rw [hObs]
      by_cases hFirst : first = observe variant y
      · simp only [hFirst]
        have hTag : x.tag = y.tag := code_equal_tags hCode
        have hFunded := congrArg C6Code.maintenance hCode
        have hf : x.funded = y.funded := by simpa [q] using hFunded
        have hTerms :
            (outcomeClasses.map fun c =>
              ((effectiveMass x a c : Rat) / 4) *
                F variant (c6Next variant x a c) rest tail) =
            (outcomeClasses.map fun c =>
              ((effectiveMass y a c : Rat) / 4) *
                F variant (c6Next variant y a c) rest tail) := by
          apply List.map_congr_left
          intro c hc
          have hMass := class_mass_of_profile_eq x.tag x.factor y.factor a
            (by simpa [hTag] using hProfile) c
          rw [hTag] at hMass
          have hEff : effectiveMass x a c = effectiveMass y a c := by
            simp [effectiveMass,hTag,hf,hMass]
          rw [hEff]
          exact congrArg (((effectiveMass y a c : Rat) / 4) * ·)
            (ih (c6Next variant x a c) (c6Next variant y a c) (hNext c) tail)
        exact congrArg List.sum hTerms
      · simp [hFirst]

theorem c6_all_words_future_sufficient (x y : C6State)
    (h : q x = q y) (word : List Action) (trace : List C6Observation) :
    F .positive x word trace = F .positive y word trace :=
  future_eq_of_bisim .positive positive_bisim word x y h trace

def c6Witness (tag : Tag) (factor : KState) : C6State :=
  ⟨tag,.inK factor,0,0,routeRegister .a,true⟩

theorem c6_code_strictly_coarser_each_tag (tag : Tag) :
    q (c6Witness tag .p0w0) = q (c6Witness tag .p0w1) ∧
    c6Witness tag .p0w0 ≠ c6Witness tag .p0w1 := by
  cases tag <;> decide

def C6FutureSufficient (variant : C6Variant) : Prop :=
  ∀ x y : C6State, q x = q y →
    ∀ word : List Action, ∀ trace : List C6Observation,
      F variant x word trace = F variant y word trace

def C6Pass (variant : C6Variant) (tag : Tag) : Prop :=
  C6Trace variant tag ∧
  futureInterface = [.predictiveNow,.eventOrder,.tickPhase,
    .cumulativeProgress,.endogenousRecordCount,.routeResidue,
    .maintenanceState,.owner] ∧
  futureAlphabet = actions ∧
  C6FutureSufficient variant ∧
  q (c6Witness tag .p0w0) = q (c6Witness tag .p0w1) ∧
  c6Witness tag .p0w0 ≠ c6Witness tag .p0w1

theorem c6_each_tag (tag : Tag) : C6Pass .positive tag := by
  refine ⟨c6_trace_each_tag tag,by rfl,by rfl,?_,?_⟩
  · intro x y h word trace
    exact c6_all_words_future_sufficient x y h word trace
  · exact c6_code_strictly_coarser_each_tag tag

def c6FutureCounterexampleTrace : List C6Observation :=
  [observe .negFuture (c6Witness .target .p0w0),
   observe .negFuture
     (c6Next .negFuture (c6Witness .target .p0w0) .stay .m1)]

/-- `NEG-C6-FUTURE` changes only the target p0w1/stay tick increment.
The merged pair has different one-step full-interface trace probabilities. -/
theorem neg_c6_future_distinguishes :
    q (c6Witness .target .p0w0) = q (c6Witness .target .p0w1) ∧
    F .negFuture (c6Witness .target .p0w0) [.stay]
      c6FutureCounterexampleTrace ≠
    F .negFuture (c6Witness .target .p0w1) [.stay]
      c6FutureCounterexampleTrace := by decide +kernel

theorem neg_c6_future_not_sufficient : ¬ C6FutureSufficient .negFuture := by
  intro h
  exact neg_c6_future_distinguishes.2
    (h _ _ neg_c6_future_distinguishes.1 [.stay] c6FutureCounterexampleTrace)

theorem neg_c6_record_writers_fail : c6Writers .negRecord .target = false := by
  decide

theorem neg_c6_record_clause_fails : ¬ C6Pass .negRecord .target := by
  intro h
  exact neg_c6_record_trace_fails h.1

theorem c6_missing_stage_clause_fails (tag : Tag) :
    ¬ C6Pass .missingMix1 tag := by
  intro h
  exact c6_missing_realized_stage_fails tag h.1

end CSTTT.POS04
