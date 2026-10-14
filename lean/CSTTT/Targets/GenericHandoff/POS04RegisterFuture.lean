import CSTTT.Targets.GenericHandoff.POS04RegisterDynamics
import CSTTT.Targets.GenericHandoff.FutureReindex

/-! POS-04 full temporal interpretation, with actual support and enabled-row
semantics. All eight readouts, code, weights and successors are interpreted
from the same partial assignment. No full-state branch is replaced by a class
representative. Probability lumping supplies the existing C6 word law without
strengthening its finite-bisimulation gate. This is a temporal component;
acquisition entries and the enclosing RawHandoff remain separate extractions. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04RegisterFuture
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH
open CSTTT.TransportTheory RegisterInterpreter POS04RegisterDynamics

set_option maxRecDepth 4096

def enabledRow (tag : Tag) : E (LaneDisturbance × Action) (List (Ambient × Rat)) :=
  .choose
    (.map (fun (p : Bool × ResourceData × Ledger) =>
      p.1 && p.2.1.rechargeAvailable && decide (p.2.2.initialBudget ≥ p.2.2.actionCost))
      (.pair (.register Register.funded) (.pair (.cell (Cell.resources tag)) (.cell Cell.maintenance))))
    (rowExpression tag) (.literal [])

def raw (tag : Tag) : RegisterFuture.Raw Cell Value Register RegisterValue
    LaneDisturbance Action Ambient CSTTT.POS04.PredictiveNow (List KState × List EventId) Bool :=
  ⟨ambientStates,actions,[.nominal],2,enabledRow tag,program tag,readouts tag⟩

theorem ready (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) : RegisterFuture.RawReady (raw tag) a := by
  refine ⟨?_,program_ready a tag (fun k hk => hc k (List.mem_append_left _ hk)),?_⟩
  · intro k hk
    apply hc k
    simp [raw,enabledRow,rowExpression,Expr.dependencies] at hk
    rcases hk with hk | hk | hk <;> subst k <;> simp [temporalDependencies,coreDependencies]
  · intro k hk
    apply hc k
    simp [raw,readouts,RegisterFuture.Readouts.dependencies,predictiveExpression,writerExpression,
      recordExpression,Expr.dependencies] at hk
    rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk | hk <;> subst k <;> simp [temporalDependencies,coreDependencies]

theorem enabled_row_eval (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (r : Run6) (d : LaneDisturbance) (act : Action) :
    (enabledRow tag).eval a (encode r) (d,act) = some (actualRows6 (runInputs6 a tag) r act) := by
  have hres := cell_value (hc (.resources tag) (by simp [temporalDependencies]))
  have hl := cell_value (hc .maintenance (by simp [temporalDependencies,coreDependencies]))
  have hrow := row_eval a tag (hc (.rows tag) (by simp [temporalDependencies,coreDependencies])) r d act
  simp only [enabledRow,Expr.eval,encode]
  rw [hres,hl,hrow]
  cases tag <;> rfl

private theorem read_value (e : E Unit X) (a : CSTTT.POS04.Assigned.Assignment)
    (h : Complete e.dependencies a) (r : Registers Register RegisterValue) (v : X)
    (hv : e.eval a r () = some v) : RegisterFuture.read e a h r = v :=
  Option.some.inj ((RegisterFuture.read_eq e a h r).symm.trans hv)

/-- Exact full interface, including maintenance, route and translated owner,
for ALL run states, not just roots. -/
theorem observation_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (r : Run6) :
    RegisterFuture.observation (raw tag) a (ready a tag hc) (encode r) =
      c6ObservationToBridge (observation6 (runInputs6 a tag) tag r) := by
  have ownerEval : (readouts tag).owner.eval a (encode r) () =
      some (tagCarrierId (runInputs6 a tag).resource.owner) := by
    have hr := cell_value (hc (.resources tag) (by simp [temporalDependencies]))
    simp only [readouts,Expr.eval]
    rw [hr]
    cases tag <;> rfl
  change (Expr.map (fun (r : ResourceData) => tagCarrierId r.owner) (.cell (Cell.resources tag)) : E Unit CarrierId).eval a (encode r) () = _ at ownerEval
  unfold RegisterFuture.observation
  simp only [raw,readouts]
  rw [read_value _ _ _ _ _ (predictive_eval a tag hc r),
      read_value _ _ _ _ _ (show (Expr.register Register.counter : E Unit Nat).eval a (encode r) () = some r.counter from rfl),
      read_value _ _ _ _ _ (show (Expr.register Register.ticks : E Unit Nat).eval a (encode r) () = some r.ticks from rfl),
      read_value _ _ _ _ _ (record_eval a tag hc r),
      read_value _ _ _ _ _ (show (Expr.register Register.residue : E Unit (List KState × List EventId)).eval a (encode r) () = some r.residue from rfl),
      read_value _ _ _ _ _ (show (Expr.register Register.funded : E Unit Bool).eval a (encode r) () = some r.funded from rfl),
      read_value _ _ _ _ _ ownerEval]
  rfl

/-- Exact all-state action-row equation, retaining every actual outcome. -/
theorem row_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (r : Run6) (d : LaneDisturbance) (act : Action) :
    RegisterFuture.row (raw tag) a (ready a tag hc) (encode r) (d,act) =
      actualRows6 (runInputs6 a tag) r act := by
  exact Option.some.inj ((RegisterFuture.row_eq _ _ _ _ _).symm.trans
    (enabled_row_eval a tag hc r d act))

theorem next_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (r : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    RegisterFuture.next (raw tag) a (ready a tag hc) (encode r) (d,act) o =
      encode (actualUpdate6 (runInputs6 a tag) r act o) :=
  checked_actual a tag (fun k hk => hc k (List.mem_append_left _ hk)) r d act o

private theorem numerator_filter (xs : List (Ambient × Rat)) (o : Ambient) :
    (xs.map fun e => if e.1 = o then e.2 else 0).sum =
      ((xs.filter fun e => decide (e.1 = o)).map Prod.snd).sum := by
  induction xs with
  | nil => rfl
  | cons e es ih => by_cases he : e.1 = o <;> simp [he,ih,Rat.zero_add]

theorem weight_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (r : Run6) (d : LaneDisturbance) (act : Action) (o : Ambient) :
    RegisterFuture.weight (raw tag) a (ready a tag hc) (encode r) (d,act) o =
      actualWeight6 (runInputs6 a tag) r act o := by
  unfold RegisterFuture.weight
  rw [row_eq a tag hc]
  exact numerator_filter _ _



private theorem observation_injective (x y : C6Observation)
    (h : c6ObservationToBridge x = c6ObservationToBridge y) : x = y := by
  cases x with
  | mk p n t g rec res maint owner =>
    cases y with
    | mk p' n' t' g' rec' res' maint' owner' =>
      simp only [c6ObservationToBridge,TemporalSnapshotReadout.mk.injEq] at h
      simp only [C6Observation.mk.injEq]
      exact ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1,
        h.2.2.2.2.2.2.1,tag_carrier_id_injective _ _ h.2.2.2.2.2.2.2⟩

noncomputable abbrev Model (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) := RegisterFuture.future (raw tag) a (ready a tag hc)

theorem code_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (r : Run6) :
    (Model a tag hc).code (encode r) = c6CodeToBridge (code6 (runInputs6 a tag) r) := by
  change bridgeCodeOfObservation (RegisterFuture.observation _ _ _ _) = _
  rw [observation_eq a tag hc]
  rfl

/-- Full probability trace law with owner representation and state registers
changed by a proved injection/bijection. Declared nominal disturbance words
project to action words; there is no horizon bound or root-only quantifier. -/
theorem word_law (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (r : Run6)
    (word : List (LaneDisturbance × Action)) (trace : List C6Observation) :
    fullFuture (Model a tag hc) (encode r) word (trace.map c6ObservationToBridge) =
      fullFuture (actualFuture6 a tag) r (word.map Prod.snd) trace := by
  simpa only [decode_encode] using FutureReindex.mapped_word_law
    (actualFuture6 a tag) (Model a tag hc) decodeRun Prod.snd c6ObservationToBridge
    observation_injective rfl
    (fun x => by simpa only [encode_decode] using observation_eq a tag hc (decodeRun x))
    (fun x da o => by simpa only [encode_decode] using weight_eq a tag hc (decodeRun x) da.1 da.2 o)
    (fun x da o => by simpa only [encode_decode,decode_encode] using
      (congrArg decodeRun (next_eq a tag hc (decodeRun x) da.1 da.2 o))) (encode r) word trace

/-- No stronger outcome-resolving bisimulation is assumed. The existing finite
class-probability check supplies exact all-state lumping, then word induction. -/
theorem all_words (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (hb : FiniteBisim6 (runInputs6 a tag)) :
    FullFutureSufficient (Model a tag hc) := by
  apply FutureReindex.sufficient_transport (actualFuture6 a tag) (Model a tag hc)
    decodeRun Prod.snd c6ObservationToBridge observation_injective rfl
    (fun x => by simpa only [encode_decode] using observation_eq a tag hc (decodeRun x))
    (fun x da o => by simpa only [encode_decode] using weight_eq a tag hc (decodeRun x) da.1 da.2 o)
    (fun x da o => by simpa only [encode_decode,decode_encode] using
      (congrArg decodeRun (next_eq a tag hc (decodeRun x) da.1 da.2 o)))
  · intro x y hxy
    have hx := code_eq a tag hc (decodeRun x)
    have hy := code_eq a tag hc (decodeRun y)
    simp only [encode_decode] at hx hy
    exact c6_code_to_bridge_injective _ _ (hx.symm.trans (hxy.trans hy))
  · exact actual_all_words6 a tag hb

/-- Exact connection to the committed quotient word law; the ACTUAL support
model remains the operational updater and carries every branch. -/
theorem quotient_word_law (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (hb : FiniteBisim6 (runInputs6 a tag))
    (r : Run6) (word : List (LaneDisturbance × Action)) (trace : List C6Observation) :
    fullFuture (Model a tag hc) (encode r) word (trace.map c6ObservationToBridge) =
      fullFuture (future6 a tag) r (word.map Prod.snd) trace := by
  rw [word_law,actual_word_law6 a tag hb]

theorem strictly_coarser (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (h : Coarser6 a tag) :
    (Model a tag hc).code (encode (initial6 a tag .p0w0 .a)) =
      (Model a tag hc).code (encode (initial6 a tag .p0w1 .a)) ∧
    encode (initial6 a tag .p0w0 .a) ≠ encode (initial6 a tag .p0w1 .a) := by
  constructor
  · rw [code_eq,code_eq]
    exact congrArg c6CodeToBridge h.1
  · intro he
    exact h.2 (by simpa only [decode_encode] using congrArg decodeRun he)

theorem accepted_complete {a : CSTTT.POS04.Assigned.Assignment} {tag : Tag}
    (h : C6Accept a tag) : Complete (temporalDependencies tag) a := by
  intro k hk
  apply h.1.1.1 k
  simp [temporalDependencies,coreDependencies] at hk
  rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk <;>
    subst k <;> cases tag <;> decide

theorem accepted_full_interface {a : CSTTT.POS04.Assigned.Assignment} {tag : Tag}
    (h : C6Accept a tag) :
    FullFutureSufficient (Model a tag (accepted_complete h)) ∧
    ((Model a tag (accepted_complete h)).code (encode (initial6 a tag .p0w0 .a)) =
      (Model a tag (accepted_complete h)).code (encode (initial6 a tag .p0w1 .a)) ∧
      encode (initial6 a tag .p0w0 .a) ≠ encode (initial6 a tag .p0w1 .a)) :=
  ⟨all_words a tag (accepted_complete h) h.2.1,strictly_coarser a tag (accepted_complete h) h.2.2⟩

end CSTTT.TargetTheory.GenericHandoff.POS04RegisterFuture
