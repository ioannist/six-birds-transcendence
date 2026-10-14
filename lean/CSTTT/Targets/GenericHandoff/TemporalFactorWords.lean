import CSTTT.Targets.GenericHandoff.TemporalFactorFuture
import CSTTT.Transport.LumpedFuture
import CSTTT.Targets.GenericHandoff.ProfileNormalization

/-! All-word soundness of the defined finite temporal constructor. The future
retains actual outcome branches, including repeated destinations in raw rows.
The probability and successor are computed; no candidate model is an argument.
The independent finite class-mass/tick equations supply applicability. -/
namespace CSTTT.TargetTheory.GenericHandoff.TemporalFactorRules
open CSTTT.TransportTheory CSTTT.TransportTheory.LumpedFuture

local instance {X Y : Type} [BEq X] [LawfulBEq X] [BEq Y] [LawfulBEq Y] : LawfulBEq (X ⊕ Y) where
  rfl := by intro x; cases x with | inl v => exact beq_self_eq_true v | inr v => exact beq_self_eq_true v
  eq_of_beq := by
    intro x y h
    cases x <;> cases y
    · exact congrArg Sum.inl (LawfulBEq.eq_of_beq h)
    · contradiction
    · contradiction
    · exact congrArg Sum.inr (LawfulBEq.eq_of_beq h)

variable {S A O H RouteId Stage Id Owner : Type}
  [DecidableEq S] [DecidableEq O] [DecidableEq RouteId] [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner]

def actualRows (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (x : Run O S Id) (a : A) : List (O × Rat) :=
  if enabled d x then (row cfg d x.factor a).map (fun e => (e.1,(e.2 : Rat) / cfg.base.rowScale)) else []

def weight (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (x : Run O S Id) (a : A) (o : O) : Rat :=
  (((actualRows cfg d x a).filter fun e => decide (e.1 = o)).map Prod.snd).sum

def future (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner) (period : Nat) :
    FullFutureModel (Run O S Id) A O (Code O S Id Owner) (Observation O S Id Owner) :=
  ⟨cfg.base.outcomes,code cfg d period,observe cfg d period,weight cfg d,update cfg d⟩

omit [DecidableEq O] in
private theorem numerator_sum (xs : List (O × Nat)) (scale n : Nat) :
    ((xs.map fun e => (e.2 : Rat)/scale).sum) + (n : Rat)/scale =
      ((xs.foldl (fun (n : Nat) e => n + e.2) n : Nat) : Rat)/scale := by
  induction xs generalizing n with
  | nil => simp only [List.map_nil,List.sum_nil,List.foldl_nil,Rat.zero_add]
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons,List.foldl_cons]
    have hadd : (e.2 : Rat)/scale + (n : Rat)/scale = ((n+e.2 : Nat) : Rat)/scale := by
      simp only [Rat.natCast_add,Rat.div_def,Rat.add_mul]
      exact Rat.add_comm _ _
    rw [Rat.add_assoc,Rat.add_left_comm ((e.2 : Rat)/scale),hadd,ih]

private theorem fiber_filter {X C : Type} [DecidableEq C]
    (q : X → C) (xs : List X) (w : X → Rat) (c : C) :
    fiber q xs w c = ((xs.filter fun o => decide (q o = c)).map w).sum := by
  induction xs with
  | nil => rfl
  | cons o os ih =>
    simp only [fiber] at ih
    by_cases h : q o = c <;> simp [fiber,h,ih,Rat.zero_add]

omit [DecidableEq S] [DecidableEq RouteId] [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner] in
/-- Exact pushforward, including duplicate raw row destinations. -/
theorem predictive_fiber (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Raw S A O H RouteId Stage Id Owner) (hd : ProfileRules.DomainCheck cfg.base)
    (x : Run O S Id) (a : A) (c : Predictive O) :
    WeightedFibers.mass cfg.base.outcomes (prediction cfg d) (weight cfg d x a) c =
      if enabled d x then (mass cfg d x.factor a c : Rat) / cfg.base.rowScale else 0 := by
  let rs := actualRows cfg d x a
  let f := fun o => if prediction cfg d o = c then (1 : Rat) else 0
  have hr := regroup rs cfg.base.outcomes Prod.fst Prod.snd f hd.2.2.1
    (fun e _ => hd.2.2.2.2.2 e.1)
  have hleft : (rs.map fun e => e.2 * f e.1).sum =
      ((rs.filter fun e => decide (prediction cfg d e.1 = c)).map Prod.snd).sum := by
    rw [← fiber_filter (fun (e : O × Rat) => prediction cfg d e.1) rs Prod.snd c]
    unfold fiber
    congr 1
    apply List.map_congr_left
    intro e _
    by_cases h : prediction cfg d e.1 = c <;> simp [f,h,Rat.mul_one,Rat.mul_zero]
  have hright : (cfg.base.outcomes.map fun o => fiber Prod.fst rs Prod.snd o * f o).sum =
      WeightedFibers.mass cfg.base.outcomes (prediction cfg d) (weight cfg d x a) c := by
    unfold WeightedFibers.mass WeightedFibers.sum
    congr 1
    apply List.map_congr_left
    intro o _
    have hm : fiber Prod.fst rs Prod.snd o = weight cfg d x a o := fiber_filter Prod.fst rs Prod.snd o
    by_cases h : prediction cfg d o = c <;> simp only [f,h,if_true,if_false,Rat.mul_one,Rat.mul_zero,hm]
  rw [hleft,hright] at hr
  rw [← hr]
  by_cases he : enabled d x = true
  · simp only [rs,actualRows,he,if_true,List.filter_map,List.map_map,Function.comp_def]
    have hn := numerator_sum ((row cfg d x.factor a).filter fun e => decide (prediction cfg d e.1 = c)) cfg.base.rowScale 0
    simpa only [show ((0 : Nat) : Rat) = 0 from rfl,Rat.div_def,Rat.zero_mul,Rat.add_zero,mass] using hn
  · have hf : enabled d x = false := Bool.eq_false_iff.mpr he
    simp [rs,actualRows,hf]

omit [DecidableEq Stage] in
theorem next_code_fiber (cfg : Schema S A O H RouteId Stage Id Owner)
    (d : Raw S A O H RouteId Stage Id Owner) (period : Nat) (x y : Run O S Id) (a : A) (o : O) :
    WeightedFibers.mass cfg.base.outcomes (FutureLumping.NextCode (future cfg d period) x a)
      (weight cfg d y a) (FutureLumping.NextCode (future cfg d period) x a o) =
      WeightedFibers.mass cfg.base.outcomes (prediction cfg d) (weight cfg d y a) (prediction cfg d o) := by
  apply WeightedFibers.sum_congr
  intro p _
  simp only [FutureLumping.NextCode,future,code,update,Code.mk.injEq,and_true]

omit [DecidableEq Stage] in
/-- No representative choice: alignment and class masses are checked on the
actual updater and full finite domains, for every run context and action. -/
theorem one_step (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (period : Nat) (hd : ProfileRules.DomainCheck cfg.base) (hb : FiniteBisim cfg d) :
    FutureLumping.OneStep (future cfg d period) := by
  intro x y hc
  refine ⟨observation_agreement cfg d period x y hc,?_⟩
  intro a
  constructor
  · intro o _
    exact successor_code_alignment cfg d period hb x y (hd.2.2.2.2.2 x.factor)
      (hd.2.2.2.2.2 y.factor) hc a (hd.2.2.2.2.1 a) o
  · intro o ho
    change WeightedFibers.mass cfg.base.outcomes (FutureLumping.NextCode (future cfg d period) x a)
      (weight cfg d x a) _ = WeightedFibers.mass cfg.base.outcomes (FutureLumping.NextCode (future cfg d period) x a)
      (weight cfg d y a) _
    rw [next_code_fiber,next_code_fiber,predictive_fiber cfg d hd,predictive_fiber cfg d hd]
    have hf : x.funded = y.funded := congrArg Code.funded hc
    have hp : prediction cfg d x.factor = prediction cfg d y.factor := congrArg Code.predictive hc
    have hmem : prediction cfg d o ∈ outcomeClasses cfg d := by
      exact (ProfileRules.dedup_mem _ _).mpr (List.mem_map.mpr ⟨o,ho,rfl⟩)
    have hm := (hb x.factor (hd.2.2.2.2.2 _) y.factor (hd.2.2.2.2.2 _) a (hd.2.2.2.2.1 _) hp).1 _ hmem
    simp only [enabled,hf,hm]

theorem all_words (cfg : Schema S A O H RouteId Stage Id Owner) (d : Raw S A O H RouteId Stage Id Owner)
    (period : Nat) (h : Accept cfg d) : FullFutureSufficient (future cfg d period) :=
  FutureLumping.all_words _ (one_step cfg d period h.1 h.2.2.2.2.2.2.2.2.1)

end CSTTT.TargetTheory.GenericHandoff.TemporalFactorRules
