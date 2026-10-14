import CSTTT.Targets.GenericHandoff.AcquisitionExecution
import CSTTT.Targets.GenericHandoff.RegisterSubstitution
/-! Actual supported acquisition sequencing. Every state is computed from raw
initializers, assigned histories, positive row support and updater/receiver
instructions. The middle initializer equation is checked separately. This is
a supported-execution component, not full Temporal-FIACH composition. -/
namespace CSTTT.TargetTheory.GenericHandoff.SupportedAcquisitionSequence
open RegisterInterpreter AcquisitionExecution
variable {Cell R S D A O Stage Id H Route : Type} {Value : Cell → Type} {RV : R → Type} {SV : S → Type}
  [DecidableEq D] [DecidableEq A] [DecidableEq O]
def supports (row : List (O × Rat)) (o : O) : Bool :=
  row.any (fun e => decide (e.1 = o ∧ 0 < e.2))
theorem supports_iff (row : List (O × Rat)) (o : O) :
    supports row o = true ↔ ∃ w, (o,w) ∈ row ∧ 0 < w := by
  simp only [supports,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨x,w⟩,hm,he,hp⟩
    change x = o at he
    subst x
    exact ⟨w,hm,hp⟩
  · rintro ⟨w,hm,hp⟩
    exact ⟨(o,w),hm,rfl,hp⟩
def stepCheck (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (r : Registers R RV) (d : D) (act : A) (o : O) : Bool :=
  decide (d ∈ raw.execution.disturbances ∧ act ∈ raw.execution.actions) && supports (rows raw a r d act) o
theorem step_check_iff (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (r : Registers R RV) (d : D) (act : A) (o : O) :
    stepCheck raw a r d act o = true ↔ d ∈ raw.execution.disturbances ∧ act ∈ raw.execution.actions ∧
      StrategyGame.PositiveSupport (rows raw a) r d act o := by
  simp only [stepCheck,Bool.and_eq_true,decide_eq_true_eq,supports_iff,StrategyGame.PositiveSupport]
  exact and_assoc
noncomputable def supportedFold (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) :
    Registers R RV → List (D × A × O) → Option (Registers R RV)
  | r, [] => some r
  | r, (d,act,o)::rest =>
    if stepCheck raw a r d act o then supportedFold raw a h (update raw a h r d act o) rest else none

theorem fold_some_iff (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (start final : Registers R RV)
    (word : List (D × A × O)) :
    supportedFold raw a h start word = some final ↔ HistoryExecution raw a h start word final := by
  induction word generalizing start with
  | nil =>
    constructor
    · intro he
      have he' : start = final := Option.some.inj he
      subst final
      exact HistoryExecution.nil _
    · intro he
      cases he
      rfl
  | cons step rest ih =>
    rcases step with ⟨d,act,o⟩
    constructor
    · intro he
      by_cases hc : stepCheck raw a start d act o = true
      · have hp := (step_check_iff raw a start d act o).mp hc
        simp only [supportedFold,hc,ite_true] at he
        exact HistoryExecution.step hp.1 hp.2.1 hp.2.2 ((ih _).mp he)
      · simp [supportedFold,hc] at he
    · intro he
      cases he with
      | step hd ha hp tail =>
        have hc := (step_check_iff raw a start d act o).mpr ⟨hd,ha,hp⟩
        simp only [supportedFold,hc,ite_true]
        exact (ih _).mpr tail

theorem checked_fold (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (start : Registers R RV) (word : List (D × A × O))
    (hc : HistoryCheck raw a h start word) :
    supportedFold raw a h start word = some (foldHistory raw a h start word) :=
  (fold_some_iff raw a h start _ word).mpr (history_check_executes raw a h start word hc)

theorem unsupported_no_execution (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (start : Registers R RV)
    (d : D) (act : A) (o : O) (rest : List (D × A × O))
    (hp : ¬ StrategyGame.PositiveSupport (rows raw a) start d act o) :
    supportedFold raw a h start ((d,act,o)::rest) = none := by
  have hc : stepCheck raw a start d act o ≠ true := fun ht => hp ((step_check_iff raw a start d act o).mp ht).2.2
  simp [supportedFold,hc]


noncomputable def fromStart (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (start : Registers R RV) (rid : Route) :
    Option (Registers R RV) := do
  let histories ← raw.histories.read a
  let routes ← raw.routes.read a
  let source ← supportedFold raw a h start (histories (routes rid).history)
  pure (receive raw a h source (routes rid).history rid)
noncomputable def firstArrival (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : Route) : Option (Registers R RV) := do
  let routes ← raw.routes.read a
  fromStart raw a h (initial raw a h (routes rid).history) rid
noncomputable def postExit (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : Route) (o : O)
    (arrival : Option (Registers R RV)) : Option (Registers R RV) := do
  let routes ← raw.routes.read a
  let arrived ← arrival
  let da ← raw.arrivalResponse.eval a arrived ((routes rid).history,rid)
  if stepCheck raw a arrived da.1 da.2 o then pure (update raw a h arrived da.1 da.2 o) else none
noncomputable def firstEntry (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : Route) (o : O) :=
  postExit raw a h rid o (firstArrival raw a h rid)

variable [DecidableEq Stage]
def RouteCheck (cfg : Schema Stage Id H Route)
    (raw : Raw Cell Value R RV D A O Stage Id H Route) (a : Assignment Cell Value) (rid : Route) : Prop :=
  ∃ histories routes events realized receiver,
    raw.histories.read a = some histories ∧ raw.routes.read a = some routes ∧
    raw.events.read a = some events ∧ raw.realized.read a = some realized ∧
    raw.receiver.read a = some receiver ∧ rid ∈ cfg.routes ∧
    (routes rid).history ∈ cfg.histories ∧ PathCheck cfg events realized (routes rid).path ∧
    Activated receiver events realized (routes rid).path

theorem from_start_sound (cfg : Schema Stage Id H Route)
    (raw : Raw Cell Value R RV D A O Stage Id H Route) (a : Assignment Cell Value) (h : Ready raw a)
    (rid : Route) (start arrived : Registers R RV)
    (hc : RouteCheck cfg raw a rid)
    (anchor : ∀ routes, raw.routes.read a = some routes → start = initial raw a h (routes rid).history)
    (he : fromStart raw a h start rid = some arrived) : Arrival cfg raw a h rid arrived := by
  obtain ⟨histories,routes,events,realized,receiver,hh,hr,hev,hreal,hrecv,hrid,hhid,hpath,hactive⟩ := hc
  cases hf : supportedFold raw a h start (histories (routes rid).history) with
  | none => simp [fromStart,hh,hr,hf] at he
  | some source =>
    have hsource := (fold_some_iff raw a h start source _).mp hf
    have hout : receive raw a h source (routes rid).history rid = arrived := by
      simpa [fromStart,hh,hr,hf] using he
    refine ⟨histories,routes,events,realized,receiver,hh,hr,hev,hreal,hrecv,hrid,hhid,hpath,hactive,source,?_,hout.symm⟩
    rw [anchor routes hr] at hsource
    exact hsource

theorem first_arrival_sound (cfg : Schema Stage Id H Route)
    (raw : Raw Cell Value R RV D A O Stage Id H Route) (a : Assignment Cell Value) (h : Ready raw a)
    (rid : Route) (arrived : Registers R RV) (hc : RouteCheck cfg raw a rid)
    (he : firstArrival raw a h rid = some arrived) : Arrival cfg raw a h rid arrived := by
  obtain ⟨histories,routes,events,realized,receiver,hh,hr,rest⟩ := hc
  have hc' : RouteCheck cfg raw a rid := ⟨histories,routes,events,realized,receiver,hh,hr,rest⟩
  have he' : fromStart raw a h (initial raw a h (routes rid).history) rid = some arrived := by
    simpa [firstArrival,hr] using he
  apply from_start_sound cfg raw a h rid _ arrived hc' _ he'
  intro other ho
  have eq := Option.some.inj (hr.symm.trans ho)
  subst other
  rfl

theorem post_exit_sound (cfg : Schema Stage Id H Route)
    (raw : Raw Cell Value R RV D A O Stage Id H Route) (a : Assignment Cell Value) (h : Ready raw a)
    (rid : Route) (o : O) (arrived entry : Registers R RV)
    (hd : DomainCheck cfg raw) (ha : Arrival cfg raw a h rid arrived)
    (hn : ∀ routes da, raw.routes.read a = some routes →
      raw.arrivalResponse.eval a arrived ((routes rid).history,rid) = some da →
      StrategyGame.Normalized (rows raw a) arrived da.1 da.2)
    (he : postExit raw a h rid o (some arrived) = some entry) : Entry cfg raw a h entry := by
  obtain ⟨histories,routes,events,realized,receiver,hh,hr,rest⟩ := ha
  have ha' : Arrival cfg raw a h rid arrived := ⟨histories,routes,events,realized,receiver,hh,hr,rest⟩
  cases hp : raw.arrivalResponse.eval a arrived ((routes rid).history,rid) with
  | none => simp [postExit,hr,hp] at he
  | some da =>
    by_cases hs : stepCheck raw a arrived da.1 da.2 o = true
    · have hok := (step_check_iff raw a arrived da.1 da.2 o).mp hs
      have hout : update raw a h arrived da.1 da.2 o = entry := by simpa [postExit,hr,hp,hs] using he
      exact ⟨hd,rid,arrived,routes,da,o,ha',hr,hp,hok.1,hok.2.1,hn routes da hr hp,hok.2.2,hout.symm⟩
    · simp [postExit,hr,hp,hs] at he

noncomputable def nextArrival
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k)) (a : Assignment Cell Value)
    (hf : Ready first a) (hs : Ready second a) (hb : RegisterSubstitution.Ready boundary a)
    (leftRoute rightRoute : Route) (o : O) : Option (Registers S SV) := do
  let actual ← firstEntry first a hf leftRoute o
  fromStart second a hs (RegisterSubstitution.translate boundary a hb actual ()) rightRoute

theorem next_arrival_sound
    (cfg : Schema Stage Id H Route)
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k)) (a : Assignment Cell Value)
    (hf : Ready first a) (hs : Ready second a) (hb : RegisterSubstitution.Ready boundary a)
    (leftRoute rightRoute : Route) (o : O) (arrived : Registers S SV)
    (hc : RouteCheck cfg second a rightRoute)
    (anchor : ∀ actual routes, firstEntry first a hf leftRoute o = some actual →
      second.routes.read a = some routes → RegisterSubstitution.translate boundary a hb actual () =
        initial second a hs (routes rightRoute).history)
    (he : nextArrival first second boundary a hf hs hb leftRoute rightRoute o = some arrived) :
    Arrival cfg second a hs rightRoute arrived := by
  cases hl : firstEntry first a hf leftRoute o with
  | none => simp [nextArrival,hl] at he
  | some actual =>
    apply from_start_sound cfg second a hs rightRoute _ arrived hc (fun routes => anchor actual routes hl)
    simpa [nextArrival,hl] using he

omit [DecidableEq Stage] in
theorem first_none_next_none
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k)) (a : Assignment Cell Value)
    (hf : Ready first a) (hs : Ready second a) (hb : RegisterSubstitution.Ready boundary a)
    (leftRoute rightRoute : Route) (o : O)
    (hm : firstEntry first a hf leftRoute o = none) :
    nextArrival first second boundary a hf hs hb leftRoute rightRoute o = none := by
  simp [nextArrival,hm]


theorem first_entry_sound (cfg : Schema Stage Id H Route)
    (raw : Raw Cell Value R RV D A O Stage Id H Route) (a : Assignment Cell Value) (h : Ready raw a)
    (rid : Route) (o : O) (entry : Registers R RV)
    (hd : DomainCheck cfg raw) (hc : RouteCheck cfg raw a rid)
    (hn : ∀ arrived routes da, raw.routes.read a = some routes →
      raw.arrivalResponse.eval a arrived ((routes rid).history,rid) = some da →
      StrategyGame.Normalized (rows raw a) arrived da.1 da.2)
    (he : firstEntry raw a h rid o = some entry) : Entry cfg raw a h entry := by
  cases ha : firstArrival raw a h rid with
  | none =>
    cases hr : raw.routes.read a <;> simp [firstEntry,postExit,ha,hr] at he
  | some arrived =>
    apply post_exit_sound cfg raw a h rid o arrived entry hd (first_arrival_sound cfg raw a h rid arrived hc ha) (hn arrived)
    simpa [firstEntry,ha] using he

noncomputable def nextEntry
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k)) (a : Assignment Cell Value)
    (hf : Ready first a) (hs : Ready second a) (hb : RegisterSubstitution.Ready boundary a)
    (leftRoute rightRoute : Route) (firstOutcome secondOutcome : O) :=
  postExit second a hs rightRoute secondOutcome
    (nextArrival first second boundary a hf hs hb leftRoute rightRoute firstOutcome)

theorem next_entry_sound
    (cfg : Schema Stage Id H Route)
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k)) (a : Assignment Cell Value)
    (hf : Ready first a) (hs : Ready second a) (hb : RegisterSubstitution.Ready boundary a)
    (leftRoute rightRoute : Route) (firstOutcome secondOutcome : O) (entry : Registers S SV)
    (hd : DomainCheck cfg second) (hc : RouteCheck cfg second a rightRoute)
    (anchor : ∀ actual routes, firstEntry first a hf leftRoute firstOutcome = some actual →
      second.routes.read a = some routes → RegisterSubstitution.translate boundary a hb actual () =
        initial second a hs (routes rightRoute).history)
    (hn : ∀ arrived routes da, second.routes.read a = some routes →
      second.arrivalResponse.eval a arrived ((routes rightRoute).history,rightRoute) = some da →
      StrategyGame.Normalized (rows second a) arrived da.1 da.2)
    (he : nextEntry first second boundary a hf hs hb leftRoute rightRoute firstOutcome secondOutcome = some entry) :
    Entry cfg second a hs entry := by
  cases ha : nextArrival first second boundary a hf hs hb leftRoute rightRoute firstOutcome with
  | none =>
    cases hr : second.routes.read a <;> simp [nextEntry,postExit,ha,hr] at he
  | some arrived =>
    apply post_exit_sound cfg second a hs rightRoute secondOutcome arrived entry hd
      (next_arrival_sound cfg first second boundary a hf hs hb leftRoute rightRoute firstOutcome arrived hc anchor ha) (hn arrived)
    simpa [nextEntry,ha] using he


/-- Completeness concerns the actual supported execution relation, not merely
success of the unguarded history fold. -/
theorem first_arrival_complete (cfg : Schema Stage Id H Route)
    (raw : Raw Cell Value R RV D A O Stage Id H Route) (a : Assignment Cell Value) (h : Ready raw a)
    (rid : Route) (arrived : Registers R RV) (ha : Arrival cfg raw a h rid arrived) :
    firstArrival raw a h rid = some arrived := by
  obtain ⟨histories,routes,events,realized,receiver,hh,hr,_,_,_,_,_,_,_,source,he,hout⟩ := ha
  have hf := (fold_some_iff raw a h _ source (histories (routes rid).history)).mpr he
  simp [firstArrival,fromStart,hh,hr,hf,hout]

theorem first_arrival_iff (cfg : Schema Stage Id H Route)
    (raw : Raw Cell Value R RV D A O Stage Id H Route) (a : Assignment Cell Value) (h : Ready raw a)
    (rid : Route) (arrived : Registers R RV) (hc : RouteCheck cfg raw a rid) :
    firstArrival raw a h rid = some arrived ↔ Arrival cfg raw a h rid arrived :=
  ⟨first_arrival_sound cfg raw a h rid arrived hc,first_arrival_complete cfg raw a h rid arrived⟩

def ResponseCheck (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (rid : Route) (o : O) : Prop :=
  ∀ arrived routes, raw.routes.read a = some routes → ∃ da,
    raw.arrivalResponse.eval a arrived ((routes rid).history,rid) = some da ∧
    da.1 ∈ raw.execution.disturbances ∧ da.2 ∈ raw.execution.actions ∧
    StrategyGame.Normalized (rows raw a) arrived da.1 da.2 ∧
    StrategyGame.PositiveSupport (rows raw a) arrived da.1 da.2 o

omit [DecidableEq Stage] in
theorem post_exit_exists (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : Route) (o : O)
    (routes : Route → AcquisitionExecution.Route H Id) (hr : raw.routes.read a = some routes)
    (arrived : Registers R RV) (hc : ResponseCheck raw a rid o) :
    ∃ entry, postExit raw a h rid o (some arrived) = some entry := by
  obtain ⟨da,hd,hl,ha,_,hp⟩ := hc arrived routes hr
  have hs := (step_check_iff raw a arrived da.1 da.2 o).mpr ⟨hl,ha,hp⟩
  exact ⟨update raw a h arrived da.1 da.2 o,by simp [postExit,hr,hd,hs]⟩

omit [DecidableEq D] [DecidableEq A] [DecidableEq O] [DecidableEq Stage] in
theorem response_normalized (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (rid : Route) (o : O) (hc : ResponseCheck raw a rid o)
    (arrived : Registers R RV) (routes : Route → AcquisitionExecution.Route H Id) (da : D × A)
    (hr : raw.routes.read a = some routes)
    (hd : raw.arrivalResponse.eval a arrived ((routes rid).history,rid) = some da) :
    StrategyGame.Normalized (rows raw a) arrived da.1 da.2 := by
  obtain ⟨actual,he,_,_,hn,_⟩ := hc arrived routes hr
  have eq := Option.some.inj (he.symm.trans hd)
  subst actual
  exact hn

structure CheckedAt
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k))
    (leftCfg rightCfg : Schema Stage Id H Route) (a : Assignment Cell Value)
    (hf : Ready first a) (hs : Ready second a) (hb : RegisterSubstitution.Ready boundary a)
    (leftRoute rightRoute : Route) (leftOutcome rightOutcome : O) : Prop where
  leftDomain : DomainCheck leftCfg first
  rightDomain : DomainCheck rightCfg second
  leftRouteCheck : RouteCheck leftCfg first a leftRoute
  rightRouteCheck : RouteCheck rightCfg second a rightRoute
  leftWord : ∀ histories routes, first.histories.read a = some histories → first.routes.read a = some routes →
    HistoryCheck first a hf (initial first a hf (routes leftRoute).history) (histories (routes leftRoute).history)
  rightWord : ∀ actual histories routes, firstEntry first a hf leftRoute leftOutcome = some actual →
    second.histories.read a = some histories → second.routes.read a = some routes →
    HistoryCheck second a hs (RegisterSubstitution.translate boundary a hb actual ()) (histories (routes rightRoute).history)
  leftResponse : ResponseCheck first a leftRoute leftOutcome
  rightResponse : ResponseCheck second a rightRoute rightOutcome
  middleInitial : ∀ actual routes, firstEntry first a hf leftRoute leftOutcome = some actual →
    second.routes.read a = some routes → RegisterSubstitution.translate boundary a hb actual () =
      initial second a hs (routes rightRoute).history

/-- Readiness choices expose actual raw evaluation. Both entries and the
middle initialization interface concern the computed outputs, not free states. -/
def Readout
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k))
    (leftCfg rightCfg : Schema Stage Id H Route) (a : Assignment Cell Value)
    (leftRoute rightRoute : Route) (leftOutcome rightOutcome : O) : Prop :=
  ∃ hf : Ready first a, ∃ hs : Ready second a, ∃ hb : RegisterSubstitution.Ready boundary a,
    ∃ before after,
      firstEntry first a hf leftRoute leftOutcome = some before ∧ Entry leftCfg first a hf before ∧
      nextEntry first second boundary a hf hs hb leftRoute rightRoute leftOutcome rightOutcome = some after ∧
      Entry rightCfg second a hs after ∧
      ∀ routes, second.routes.read a = some routes →
        RegisterSubstitution.translate boundary a hb before () = initial second a hs (routes rightRoute).history

theorem constructs
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k))
    (leftCfg rightCfg : Schema Stage Id H Route) (a : Assignment Cell Value)
    (hf : Ready first a) (hs : Ready second a) (hb : RegisterSubstitution.Ready boundary a)
    (leftRoute rightRoute : Route) (leftOutcome rightOutcome : O)
    (hc : CheckedAt first second boundary leftCfg rightCfg a hf hs hb leftRoute rightRoute leftOutcome rightOutcome) :
    Readout first second boundary leftCfg rightCfg a leftRoute rightRoute leftOutcome rightOutcome := by
  obtain ⟨lh,lr,le,ls,lv,hlh,hlr,_⟩ := hc.leftRouteCheck
  have hfold := checked_fold first a hf _ _ (hc.leftWord lh lr hlh hlr)
  let firstArrived := receive first a hf (foldHistory first a hf (initial first a hf (lr leftRoute).history)
    (lh (lr leftRoute).history)) (lr leftRoute).history leftRoute
  have hfirst : firstArrival first a hf leftRoute = some firstArrived := by
    simp [firstArrival,fromStart,hlh,hlr,hfold,firstArrived]
  obtain ⟨before,hbefore⟩ := post_exit_exists first a hf leftRoute leftOutcome lr hlr firstArrived hc.leftResponse
  have hbe : firstEntry first a hf leftRoute leftOutcome = some before := by simpa [firstEntry,hfirst] using hbefore
  have hentry := first_entry_sound leftCfg first a hf leftRoute leftOutcome before hc.leftDomain hc.leftRouteCheck
    (response_normalized first a leftRoute leftOutcome hc.leftResponse) hbe
  obtain ⟨rh,rr,re,rs,rv,hrh,hrr,_⟩ := hc.rightRouteCheck
  let middle := RegisterSubstitution.translate boundary a hb before ()
  have hrword := checked_fold second a hs middle _ (hc.rightWord before rh rr hbe hrh hrr)
  let arrived := receive second a hs (foldHistory second a hs middle (rh (rr rightRoute).history)) (rr rightRoute).history rightRoute
  have har : nextArrival first second boundary a hf hs hb leftRoute rightRoute leftOutcome = some arrived := by
    simp [nextArrival,hbe,fromStart,hrh,hrr,hrword,arrived,middle]
  obtain ⟨after,hafter⟩ := post_exit_exists second a hs rightRoute rightOutcome rr hrr arrived hc.rightResponse
  have hae : nextEntry first second boundary a hf hs hb leftRoute rightRoute leftOutcome rightOutcome = some after := by
    simpa [nextEntry,har] using hafter
  have hlast := next_entry_sound rightCfg first second boundary a hf hs hb leftRoute rightRoute leftOutcome rightOutcome after
    hc.rightDomain hc.rightRouteCheck hc.middleInitial (response_normalized second a rightRoute rightOutcome hc.rightResponse) hae
  exact ⟨hf,hs,hb,before,after,hbe,hentry,hae,hlast,fun routes hr => hc.middleInitial before routes hbe hr⟩



omit [DecidableEq Stage] in
theorem fold_append (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (start : Registers R RV)
    (first rest : List (D × A × O)) :
    supportedFold raw a h start (first++rest) = (supportedFold raw a h start first).bind
      (fun middle => supportedFold raw a h middle rest) := by
  induction first generalizing start with
  | nil => rfl
  | cons e tail ih =>
    rcases e with ⟨d,act,o⟩
    simp only [List.cons_append,supportedFold]
    split <;> simp [ih]

omit [DecidableEq Stage] in
theorem fold_none_iff (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (start : Registers R RV) (word : List (D × A × O)) :
    supportedFold raw a h start word = none ↔ ¬ ∃ final, HistoryExecution raw a h start word final := by
  constructor
  · intro hn ⟨final,he⟩
    have hs := (fold_some_iff raw a h start final word).mpr he
    rw [hn] at hs
    contradiction
  · intro hn
    cases hs : supportedFold raw a h start word with
    | none => rfl
    | some final => exact False.elim (hn ⟨final,(fold_some_iff raw a h start final word).mp hs⟩)

omit [DecidableEq Stage] in
theorem fold_terminal_defined (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (start final : Registers R RV) (word : List (D × A × O))
    (he : supportedFold raw a h start word = some final) : final = foldHistory raw a h start word :=
  history_terminal_defined raw a h ((fold_some_iff raw a h start final word).mp he)

omit [DecidableEq Stage] in
theorem post_exit_none (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : Route) (o : O) :
    postExit raw a h rid o none = none := by
  cases hr : raw.routes.read a <;> simp [postExit,hr]

theorem first_none_no_readout
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k))
    (leftCfg rightCfg : Schema Stage Id H Route) (a : Assignment Cell Value)
    (leftRoute rightRoute : Route) (leftOutcome rightOutcome : O)
    (hn : ∀ hf : Ready first a, firstEntry first a hf leftRoute leftOutcome = none) :
    ¬ Readout first second boundary leftCfg rightCfg a leftRoute rightRoute leftOutcome rightOutcome := by
  rintro ⟨hf,_,_,before,_,he,_⟩
  rw [hn hf] at he
  contradiction

theorem next_none_no_readout
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k))
    (leftCfg rightCfg : Schema Stage Id H Route) (a : Assignment Cell Value)
    (leftRoute rightRoute : Route) (leftOutcome rightOutcome : O)
    (hn : ∀ (hf : Ready first a) (hs : Ready second a) (hb : RegisterSubstitution.Ready boundary a),
      nextEntry first second boundary a hf hs hb leftRoute rightRoute leftOutcome rightOutcome = none) :
    ¬ Readout first second boundary leftCfg rightCfg a leftRoute rightRoute leftOutcome rightOutcome := by
  rintro ⟨hf,hs,hb,before,after,_,_,he,_⟩
  rw [hn hf hs hb] at he
  contradiction

theorem missing_first_no_readout
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k))
    (leftCfg rightCfg : Schema Stage Id H Route) (a : Assignment Cell Value)
    (leftRoute rightRoute : Route) (leftOutcome rightOutcome : O)
    (k : Cell) (hk : k ∈ first.dependencies) (hm : a k = none) :
    ¬ Readout first second boundary leftCfg rightCfg a leftRoute rightRoute leftOutcome rightOutcome := by
  rintro ⟨hf,_⟩
  exact (missing_dependency_rejected first a k hk hm) hf

theorem missing_second_no_readout
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k))
    (leftCfg rightCfg : Schema Stage Id H Route) (a : Assignment Cell Value)
    (leftRoute rightRoute : Route) (leftOutcome rightOutcome : O)
    (k : Cell) (hk : k ∈ second.dependencies) (hm : a k = none) :
    ¬ Readout first second boundary leftCfg rightCfg a leftRoute rightRoute leftOutcome rightOutcome := by
  rintro ⟨_,hs,_⟩
  exact (missing_dependency_rejected second a k hk hm) hs

theorem missing_boundary_no_readout
    (first : Raw Cell Value R RV D A O Stage Id H Route)
    (second : Raw Cell Value S SV D A O Stage Id H Route)
    (boundary : (k : S) → Expr Cell Value R RV Unit (SV k))
    (leftCfg rightCfg : Schema Stage Id H Route) (a : Assignment Cell Value)
    (leftRoute rightRoute : Route) (leftOutcome rightOutcome : O)
    (r : S) (k : Cell) (hk : k ∈ (boundary r).dependencies) (hm : a k = none) :
    ¬ Readout first second boundary leftCfg rightCfg a leftRoute rightRoute leftOutcome rightOutcome := by
  rintro ⟨_,_,hb,_⟩
  have hp := hb r k hk
  rw [hm] at hp
  contradiction

end CSTTT.TargetTheory.GenericHandoff.SupportedAcquisitionSequence
