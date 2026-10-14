import CSTTT.Targets.GenericHandoff.POS04RegisterFuture
import CSTTT.Targets.GenericHandoff.RegisterReadoutLaws

/-! Independent POS-04 update recipes: actual destination's raw predictive
readout; +1 order/progress; assigned tick delta; funded writer record;
retained raw provenance; conserved-ledger enabled state; unchanged raw owner.
No candidate readout is supplied, and no law is checked only at audit roots.
The numeric recipes are fixed BEFORE they are compared with the interpreter.
-/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RegisterReadoutLaws
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TransportTheory
open RegisterInterpreter POS04RegisterDynamics POS04RegisterFuture

set_option maxRecDepth 4096

def nextPredictive (tag : Tag) : E StepEnv CSTTT.POS04.PredictiveNow :=
  .map (fun (p : (KState → Nat) × (KState → Action → List (Ambient × Nat)) × (Ambient → Bool) × Ambient) =>
    match p.2.2.2 with
    | .inK s => .active (p.1 s,actions.map fun act => (p.2.1 s act).map fun e => p.2.2.1 e.1)
    | .p2w0 => .exit2 | .p5w1 => .exit5)
    (.pair (.cell Cell.positions) (.pair (.cell (Cell.rows tag))
      (.pair (.cell Cell.hazards) (.environment (fun e => e.2.2)))))

def nextRecord (tag : Tag) : E StepEnv Nat :=
  .map (fun (p : Bool × Bool × Nat) => if p.1 && p.2.1 then p.2.2 else 0)
    (.pair (program tag .funded) (.pair ((writerExpression tag).reenv (fun _ => ()))
      (program tag .counter)))

def recipes (tag : Tag) : RegisterFuture.StepRecipes Cell Value Register RegisterValue
    LaneDisturbance Action Ambient CSTTT.POS04.PredictiveNow (List KState × List EventId) Bool
  | .predictive => nextPredictive tag
  | .order | .progress => program tag .counter
  | .ticks => program tag .ticks
  | .writer => (writerExpression tag).reenv (fun _ => ())
  | .record => nextRecord tag
  | .residue => program tag .residue
  | .maintenance => program tag .funded
  | .owner => ((readouts tag).owner).reenv (fun _ => ())

theorem next_predictive_eval (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (r : Run6) (e : StepEnv) :
    (nextPredictive tag).eval a (encode r) e = some (predictive6 (runInputs6 a tag) e.2.2) := by
  have hp := cell_value (hc .positions (by simp [temporalDependencies]))
  have hr := cell_value (hc (.rows tag) (by simp [temporalDependencies,coreDependencies]))
  have hh := cell_value (hc .hazards (by simp [temporalDependencies]))
  simp only [nextPredictive,Expr.eval]
  rw [hp,hr,hh]
  cases tag <;> cases e.2.2 <;> rfl

/-- Every field equation holds on every run, hence on the entire computed
closure. This does not assert positivity on unsupported/unfunded runs. -/
theorem field_laws (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (r : Run6)
    (d : LaneDisturbance) (act : Action) (o : Ambient) (f : RegisterFuture.Field) :
    RegisterFuture.FieldLaw (raw tag) (recipes tag) a (ready a tag hc) (encode r) (d,act) o f := by
  have hp := program_actual a tag
    (fun k hk => hc k (List.mem_append_left _ hk)) r d act o
  have hl := cell_value (hc .maintenance (by simp [temporalDependencies,coreDependencies]))
  unfold RegisterFuture.FieldLaw
  rw [next_eq a tag hc]
  cases f with
  | predictive => exact (predictive_eval a tag hc _).trans (next_predictive_eval a tag hc r (d,act,o)).symm
  | order => exact (congrFun hp .counter).symm
  | ticks => exact (congrFun hp .ticks).symm
  | progress => exact (congrFun hp .counter).symm
  | writer =>
    simp only [raw,recipes,readouts,RegisterFuture.fieldExpr,Expr.reenv_eval,
      writer_eval a tag hc,actualUpdate6]
  | record =>
    change (recordExpression tag).eval a (encode (actualUpdate6 _ r act o)) () =
      (nextRecord tag).eval a (encode r) (d,act,o)
    rw [record_eval a tag hc]
    simp only [nextRecord,Expr.eval,Expr.reenv_eval]
    rw [show (program tag .funded).eval a (encode r) (d,act,o) = _ from congrFun hp .funded,
        show (program tag .counter).eval a (encode r) (d,act,o) = _ from congrFun hp .counter,
        writer_eval a tag hc]
    rfl
  | residue => exact (congrFun hp .residue).symm
  | maintenance => exact (congrFun hp .funded).symm
  | owner =>
    simp only [raw,recipes,readouts,RegisterFuture.fieldExpr,Expr.reenv_eval,Expr.eval]



def roots (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) := (roots6 a tag).map encode

/-- The actual updater retains funding and writer provenance across the full
closure, even for the zero-weight outputs included in closure generation. -/
theorem closure_funded_writer {a : CSTTT.POS04.Assigned.Assignment} {tag : Tag}
    (h : C6Accept a tag) (x : Registers Register RegisterValue)
    (hx : RegisterFuture.Closure (raw tag) a (ready a tag (accepted_complete h)) (roots a tag) x) :
    (decodeRun x).funded = true ∧ writer6 (runInputs6 a tag) tag (decodeRun x).residue = true := by
  have hp := h.1.2.2.2.2.2.2.2.2.2
  induction hx with
  | root x hm =>
    obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    simpa only [decode_encode] using c6_accept_funded_writer h r (FutureClosure.root r hr)
  | @step x hx da o ho ih =>
    change _
    have hn := next_eq a tag (accepted_complete h) (decodeRun x) da.1 da.2 o
    simp only [encode_decode] at hn
    change (decodeRun (RegisterFuture.next (raw tag) a (ready a tag (accepted_complete h)) x da o)).funded = true ∧
      writer6 (runInputs6 a tag) tag (decodeRun (RegisterFuture.next (raw tag) a (ready a tag (accepted_complete h)) x da o)).residue = true
    rw [hn,decode_encode]
    simp only [actualUpdate6,ih.1,ih.2,decide_eq_true hp,Bool.true_and,and_self]

private theorem supported_delta {a : CSTTT.POS04.Assigned.Assignment} {tag : Tag}
    (h : C6Accept a tag) (r : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient)
    (hp : RegisterFuture.weight (raw tag) a (ready a tag (accepted_complete h)) (encode r) (d,act) o > 0) :
    delta6 (runInputs6 a tag) r.factor act = 1 := by
  rw [weight_eq a tag (accepted_complete h)] at hp
  have ht := h.1.2.2.1.2.2.2.1
  unfold ticks6 at ht
  cases hf : r.factor with
  | p2w0 => simp [actualWeight6,actualRows6,row6,hf,show ¬ (0 : Rat) > 0 from by decide] at hp
  | p5w1 => simp [actualWeight6,actualRows6,row6,hf,show ¬ (0 : Rat) > 0 from by decide] at hp
  | inK s =>
    have hs := List.all_eq_true.mp (List.all_eq_true.mp ht s (by cases s <;> decide)) act
      (by cases act <;> decide)
    have hn : (row6 (runInputs6 a tag) r.factor act).isEmpty = false := by
      cases he : row6 (runInputs6 a tag) r.factor act with
      | nil => simp [actualWeight6,actualRows6,he,show ¬ (0 : Rat) > 0 from by decide] at hp
      | cons => rfl
    simp only [hf,row6] at hn
    simp only [hn,Bool.false_or,decide_eq_true_eq] at hs
    exact hs

private theorem roots_nonempty {a : CSTTT.POS04.Assigned.Assignment} {tag : Tag}
    (h : C6Accept a tag) : roots a tag ≠ [] := by
  have hp := h.1.2.2.1.2.2.2.2.2.1
  simp only [paths6,Bool.and_eq_true] at hp
  have ha := List.all_eq_true.mp hp.1.1.2 .a (by decide)
  unfold path6 at ha
  cases he : routeTuple (runInputs6 a tag).base .a with
  | none => simp [he] at ha
  | some residue =>
    have hm : (⟨.inK .p0w0,0,0,residue,(runInputs6 a tag).base.receiver.funded⟩ : Run6) ∈ roots6 a tag := by
      apply List.mem_flatMap.mpr
      refine ⟨.a,by decide,?_⟩
      simp only [he]
      exact List.mem_map.mpr ⟨.p0w0,by decide,rfl⟩
    intro hempty
    have hs : encode (⟨.inK .p0w0,0,0,residue,(runInputs6 a tag).base.receiver.funded⟩ : Run6) ∈ (roots6 a tag).map encode := List.mem_map.mpr ⟨_,hm,rfl⟩
    rw [show (roots6 a tag).map encode = [] from hempty] at hs
    contradiction

theorem positive_recipes {a : CSTTT.POS04.Assigned.Assignment} {tag : Tag}
    (h : C6Accept a tag) (x : Registers Register RegisterValue)
    (hx : RegisterFuture.Closure (raw tag) a (ready a tag (accepted_complete h)) (roots a tag) x)
    (d : LaneDisturbance) (act : Action) (o : Ambient)
    (hp : RegisterFuture.weight (raw tag) a (ready a tag (accepted_complete h)) x (d,act) o > 0) :
    RegisterFuture.PositiveRecipes (raw tag) (recipes tag) a (ready a tag (accepted_complete h)) x (d,act) o := by
  let r := decodeRun x
  have hxenc : encode r = x := encode_decode x
  have hf := closure_funded_writer h x hx
  change r.funded = true ∧ writer6 (runInputs6 a tag) tag r.residue = true at hf
  have hdelta := supported_delta h r d act o (by simpa only [hxenc] using hp)
  have hpos := h.1.2.2.2.2.2.2.2.2.2
  have hfield := field_laws a tag (accepted_complete h) r d act o .record
  unfold RegisterFuture.FieldLaw at hfield
  rw [next_eq a tag (accepted_complete h)] at hfield
  change (recordExpression tag).eval a (encode (actualUpdate6 _ r act o)) () = _ at hfield
  rw [record_eval a tag (accepted_complete h)] at hfield
  have hrecord : (recipes tag .record).eval a (encode r) (d,act,o) = some (r.counter+1) := by
    rw [← hfield]
    simp only [observation6,actualUpdate6,hf.1,hf.2,decide_eq_true hpos,Bool.true_and,if_true]
  unfold RegisterFuture.PositiveRecipes
  rw [← hxenc]
  refine ⟨r.counter+1,r.ticks+1,r.counter+1,r.counter+1,?_,?_,?_,hrecord,?_,?_,?_,?_⟩
  · rfl
  · have hp := program_actual a tag
      (fun k hk => accepted_complete h k (List.mem_append_left _ hk)) r d act o
    change execute (program tag) a (encode r) (d,act,o) .ticks = _
    rw [congrFun hp .ticks]
    simp only [encode,actualUpdate6,hdelta]
  · rfl
  · rw [observation_eq a tag (accepted_complete h)]
    exact Nat.lt_succ_self _
  · simp only [raw,readouts,Expr.eval,encode,Option.any_some,decide_eq_true_eq]
    exact Nat.lt_succ_self _
  · rw [observation_eq a tag (accepted_complete h)]
    exact Nat.lt_succ_self _
  · rw [observation_eq a tag (accepted_complete h)]
    simp only [c6ObservationToBridge,observation6,hf.1,hf.2,Bool.true_and,if_true]
    exact Nat.lt_succ_self _

/-- Nonempty audited roots, all field equations and positive supported
advancement in the generic gate; valid for every accepted partial assignment. -/
theorem readout_gate {a : CSTTT.POS04.Assigned.Assignment} {tag : Tag} (h : C6Accept a tag) :
    RegisterFuture.ReadoutLawGate (raw tag) (recipes tag) a (ready a tag (accepted_complete h)) (roots a tag) := by
  refine ⟨(by change [LaneDisturbance.nominal] ≠ []; decide),(by change actions ≠ []; decide),
    (by change ambientStates.Nodup; decide),(by change 2 > 0; decide),roots_nonempty h,?_,?_⟩
  · intro x hx d _ act _ o _
    constructor
    · intro f
      simpa only [encode_decode] using field_laws a tag (accepted_complete h) (decodeRun x) d act o f
    · exact positive_recipes h x hx d act o
  · intro x hx d hd act ha o hp
    change o ∈ ambientStates
    cases o with
    | inK k => cases k <;> decide
    | p2w0 => decide
    | p5w1 => decide



/-- Eddy's cap proposal changes ONLY progress, not the rows, updater, roots,
or independent step recipe. It is a guard, not new positive model data. -/
def cappedProgress (tag : Tag) := RegisterFuture.replaceReadout (raw tag) .progress
  (show E Unit Nat from .map (fun (n : Nat) => min n (2 : Nat)) (.register Register.counter))

theorem capped_ready (tag : Tag) : RegisterFuture.RawReady (cappedProgress tag) canonical :=
  ⟨canonical_complete _,fun _ => canonical_complete _,canonical_complete _⟩

private def afterTwo (tag : Tag) : Run6 :=
  let d := runInputs6 canonical tag
  actualUpdate6 d (actualUpdate6 d (initial6 canonical tag .p0w0 .a) .stay (.inK .p0w0)) .stay (.inK .p0w0)

private theorem after_two_closure (tag : Tag) :
    RegisterFuture.Closure (raw tag) canonical
      (ready canonical tag (accepted_complete (canonical_accept6 tag)))
      (roots canonical tag) (encode (afterTwo tag)) := by
  have hr : initial6 canonical tag .p0w0 .a ∈ roots6 canonical tag := by
    cases tag <;> decide
  have hx : RegisterFuture.Closure (raw tag) canonical
      (ready canonical tag (accepted_complete (canonical_accept6 tag)))
      (roots canonical tag) (encode (initial6 canonical tag .p0w0 .a)) :=
    FutureClosure.root _ (List.mem_map.mpr ⟨_,hr,rfl⟩)
  have step (r : Run6) (hx : RegisterFuture.Closure (raw tag) canonical
      (ready canonical tag (accepted_complete (canonical_accept6 tag)))
      (roots canonical tag) (encode r)) :
      RegisterFuture.Closure (raw tag) canonical
        (ready canonical tag (accepted_complete (canonical_accept6 tag)))
        (roots canonical tag) (encode (actualUpdate6 (runInputs6 canonical tag) r .stay (.inK .p0w0))) := by
    have hn := FutureClosure.step hx (.nominal,.stay) (.inK .p0w0) (by change Ambient.inK .p0w0 ∈ ambientStates; decide)
    change RegisterFuture.Closure (raw tag) canonical
      (ready canonical tag (accepted_complete (canonical_accept6 tag))) (roots canonical tag)
      (RegisterFuture.next (raw tag) canonical (ready canonical tag (accepted_complete (canonical_accept6 tag)))
        (encode r) (.nominal,.stay) (.inK .p0w0)) at hn
    rw [next_eq canonical tag (accepted_complete (canonical_accept6 tag))] at hn
    exact hn
  exact step _ (step _ hx)

theorem capped_progress_rejected (tag : Tag) :
    ¬ RegisterFuture.ReadoutLawGate (cappedProgress tag) (recipes tag) canonical
      (capped_ready tag) (roots canonical tag) := by
  have hr : RegisterFuture.Closure (cappedProgress tag) canonical (capped_ready tag)
      (roots canonical tag) (encode (afterTwo tag)) := after_two_closure tag
  apply RegisterFuture.field_guard _ _ _ _ _ _ hr .nominal (by change LaneDisturbance.nominal ∈ [LaneDisturbance.nominal]; decide) .stay
    (by change Action.stay ∈ actions; decide) (.inK .p0w0) (by change Ambient.inK .p0w0 ∈ ambientStates; decide) .progress
  unfold RegisterFuture.FieldLaw
  have hn : RegisterFuture.next (cappedProgress tag) canonical (capped_ready tag)
      (encode (afterTwo tag)) (.nominal,.stay) (.inK .p0w0) =
      encode (actualUpdate6 (runInputs6 canonical tag) (afterTwo tag) .stay (.inK .p0w0)) :=
    checked_actual canonical tag (canonical_complete _) _ _ _ _
  rw [hn]
  cases tag <;> simp only [cappedProgress,RegisterFuture.replaceReadout,RegisterFuture.Readouts.replace,
    RegisterFuture.fieldExpr,Expr.eval,encode,actualUpdate6,afterTwo,program,recipes] <;>
    change ¬ ((some 2 : Option Nat) = some 3) <;> decide

end CSTTT.TargetTheory.GenericHandoff.POS04RegisterReadoutLaws
