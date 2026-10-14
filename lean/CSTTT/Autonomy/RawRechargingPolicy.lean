import CSTTT.Targets.GenericHandoff.StaticView
import CSTTT.Targets.GenericHandoff.ClauseDispatcher
import CSTTT.Targets.GenericHandoff.ViableSet
import Init.Data.Rat.Lemmas

namespace CSTTT.AutonomyTheory.RawRechargingPolicy
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
-- Class (b): raw operational policy construction or derived law.
structure EventState (X : Type) where
  factor : X
  progress : Nat
  record : Nat
  balance : Rat
-- Class (b): raw operational policy construction or derived law.
structure Branch (X : Type) where
  destination : X
  progressIncrement : Nat
  recordIncrement : Nat
  debit : Rat
  credit : Rat
-- Class (b): raw operational policy construction or derived law.
structure Response (X A O : Type) where
  action : A
  owner : CarrierId
  rows : List (O × Rat)
  branch : O → Branch X
-- Class (b): raw operational policy construction or derived law.
structure Raw (Cell : Type) (Value : Cell → Type) (X D A O : Type) where
  states : FiniteEnum X
  disturbances : FiniteEnum D
  outcomes : FiniteEnum O
  target : CarrierId
  clauses : ClauseDispatcher.Package Cell Value
  cells : (k : Cell) → Expr Cell Value Unit (fun _ => Unit) X (Value k)
  response : StaticView Cell Value (X → D → Response X A O)
  initialFactor : StaticView Cell Value X
  initialProgress : StaticView Cell Value Nat
  initialRecord : StaticView Cell Value Nat
  initialBalance : StaticView Cell Value Rat
variable {Cell X D A O : Type} {Value : Cell → Type}
-- Class (b): raw operational policy construction or derived law.
def Ready (m : Raw Cell Value X D A O) (a : Assignment Cell Value) : Prop :=
  Complete m.response.dependencies a ∧ Complete m.initialFactor.dependencies a ∧
  Complete m.initialProgress.dependencies a ∧ Complete m.initialRecord.dependencies a ∧
  Complete m.initialBalance.dependencies a
-- Class (b): raw operational policy construction or derived law.
noncomputable def table (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a) :
    X → D → Response X A O := Classical.choose (m.response.present a h.1)
-- Class (b): raw operational policy construction or derived law.
theorem table_eq (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a) :
    m.response.read a=some (table m a h) := Classical.choose_spec (m.response.present a h.1)
-- Class (b): raw operational policy construction or derived law.
noncomputable def initial (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a) : EventState X :=
  ⟨Classical.choose (m.initialFactor.present a h.2.1),
   Classical.choose (m.initialProgress.present a h.2.2.1),
   Classical.choose (m.initialRecord.present a h.2.2.2.1),
   Classical.choose (m.initialBalance.present a h.2.2.2.2)⟩
-- Class (b): raw operational policy construction or derived law.
def decodeInitial (m : Raw Cell Value X D A O) (a : Assignment Cell Value) : Option (EventState X) := do
  let factor ← m.initialFactor.read a
  let progress ← m.initialProgress.read a
  let record ← m.initialRecord.read a
  let balance ← m.initialBalance.read a
  pure ⟨factor,progress,record,balance⟩

-- Class (b): raw operational policy construction or derived law.
theorem initial_eq (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a) :
    decodeInitial m a=some (initial m a h) := by
  have factor : m.initialFactor.read a=some (initial m a h).factor := Classical.choose_spec (m.initialFactor.present a h.2.1)
  have progress : m.initialProgress.read a=some (initial m a h).progress := Classical.choose_spec (m.initialProgress.present a h.2.2.1)
  have record : m.initialRecord.read a=some (initial m a h).record := Classical.choose_spec (m.initialRecord.present a h.2.2.2.1)
  have balance : m.initialBalance.read a=some (initial m a h).balance := Classical.choose_spec (m.initialBalance.present a h.2.2.2.2)
  simp only [decodeInitial,factor,progress,record,balance]
  rfl

-- Class (b): raw operational policy construction or derived law.
def dependencies (m : Raw Cell Value X D A O) : List Cell :=
  m.response.dependencies ++ m.initialFactor.dependencies ++ m.initialProgress.dependencies ++
    m.initialRecord.dependencies ++ m.initialBalance.dependencies

-- Class (b): raw operational policy construction or derived law.
theorem ready_iff (m : Raw Cell Value X D A O) (a : Assignment Cell Value) :
    Ready m a ↔ Complete (dependencies m) a := by
  simp [Ready,Complete,dependencies,List.mem_append]
  grind

-- Class (b): raw operational policy construction or derived law.
theorem missing_response_actual_none (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (k : Cell) (consumed : k∈m.response.dependencies) (missing : a k=none) : m.response.read a=none :=
  m.response.missing a k consumed missing

-- Class (b): raw operational policy construction or derived law.
theorem missing_response_not_ready (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (missing : m.response.read a=none) : ¬ Ready m a := by
  intro ready
  have decoded := table_eq m a ready
  rw [missing] at decoded
  contradiction

-- Class (b): raw operational policy construction or derived law.
theorem missing_balance_actual_none (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (missing : m.initialBalance.read a=none) : decodeInitial m a=none := by
  unfold decodeInitial
  cases m.initialFactor.read a <;> cases m.initialProgress.read a <;>
    cases m.initialRecord.read a <;> simp [missing]

-- Class (b): raw operational policy construction or derived law.
def factorAssignment (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (x : X) : Assignment Cell Value :=
  fun k => (m.cells k).eval a (fun _ => ()) x
-- Class (b): raw operational policy construction or derived law.
def PackageAt (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (x : X) : Prop :=
  m.clauses.accept (factorAssignment m a x)
-- Class (b): raw operational policy construction or derived law.
def ratMax (a b : Rat) : Rat := if a≤b then b else a
-- Class (b): raw operational policy construction or derived law.
theorem le_ratMax_left (a b : Rat) : a≤ratMax a b := by
  unfold ratMax
  split <;> simp_all [Rat.le_refl]
-- Class (b): raw operational policy construction or derived law.
theorem le_ratMax_right (a b : Rat) : b≤ratMax a b := by
  unfold ratMax
  split
  · exact Rat.le_refl
  · rename_i greater
    exact Rat.le_of_lt (Rat.not_le.mp greater)
-- Class (b): raw operational policy construction or derived law.
def maxCost (costs : List Rat) : Rat := costs.foldr ratMax 0
-- Class (b): raw operational policy construction or derived law.
theorem cost_member_bounded (costs : List Rat) (c : Rat) (member : c∈costs) : c≤maxCost costs := by
  induction costs with
  | nil => simp at member
  | cons first rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · exact le_ratMax_left _ _
    · exact Rat.le_trans (ih member) (le_ratMax_right _ _)
-- Class (b): raw operational policy construction or derived law.
theorem max_cost_nonnegative (costs : List Rat) : 0≤maxCost costs := by
  induction costs with
  | nil => exact Rat.le_refl
  | cons first rest ih => exact Rat.le_trans ih (le_ratMax_right _ _)
-- Class (b): raw operational policy construction or derived law.
noncomputable def costs (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a) : List Rat :=
  m.states.elems.flatMap (fun x => m.disturbances.elems.flatMap
    (fun d => m.outcomes.elems.map (fun o => ((table m a h x d).branch o).debit)))
-- Class (b): raw operational policy construction or derived law.
noncomputable def reserve (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a) : Rat :=
  maxCost (costs m a h)
-- Class (b): raw operational policy construction or derived law.
theorem raw_cost_bounded (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (x : X) (d : D) (o : O) : ((table m a h x d).branch o).debit≤reserve m a h := by
  apply cost_member_bounded
  exact List.mem_flatMap.mpr ⟨x,m.states.complete x,
    List.mem_flatMap.mpr ⟨d,m.disturbances.complete d,List.mem_map.mpr ⟨o,m.outcomes.complete o,rfl⟩⟩⟩
-- Class (b): raw operational policy construction or derived law.
def Normalized (rows : List (O × Rat)) : Prop :=
  (∀ e∈rows, 0≤e.2) ∧ (rows.map Prod.snd).sum=1 ∧ ∃ o w, (o,w)∈rows ∧ 0<w
-- Class (b): raw operational policy construction or derived law.
noncomputable def Retains (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (S : List X) (x : X) : Prop :=
  PackageAt m a x ∧ ∀ d,
    let r := table m a h x d
    r.owner=m.target ∧ Normalized r.rows ∧ ∀ o w, (o,w)∈r.rows → 0<w →
      (r.branch o).destination∈S ∧ 0<(r.branch o).progressIncrement ∧
      0<(r.branch o).recordIncrement ∧ 0≤(r.branch o).debit ∧ (r.branch o).debit≤(r.branch o).credit
-- Class (b): raw operational policy construction or derived law.
noncomputable def retain (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (S : List X) (x : X) : Bool := by
  classical
  exact decide (Retains m a h S x)
-- Class (b): raw operational policy construction or derived law.
@[simp] theorem retain_true_iff (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (S : List X) (x : X) : retain m a h S x=true ↔ Retains m a h S x := by
  classical
  simp [retain]
-- Class (b): raw operational policy construction or derived law.
theorem retain_monotone (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a) :
    ViableSet.Monotone (retain m a h) := by
  intro S T inclusion x holds
  rw [retain_true_iff] at holds ⊢
  refine ⟨holds.1,fun d => ?_⟩
  have hd := holds.2 d
  refine ⟨hd.1,hd.2.1,fun o w member positive => ?_⟩
  have branch := hd.2.2 o w member positive
  exact ⟨inclusion branch.1,branch.2⟩
variable [DecidableEq X]
-- Class (b): raw operational policy construction or derived law.
noncomputable def greatest (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a) : List X :=
  ViableSet.greatest m.states.elems (retain m a h)
-- Class (b): raw operational policy construction or derived law.
theorem greatest_retains (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (x : X) (inside : x∈greatest m a h) : Retains m a h (greatest m a h) x :=
  (retain_true_iff _ _ _ _ _).mp
    (ViableSet.greatest_viable m.states.elems m.states.complete (retain m a h) (retain_monotone m a h) x inside)
-- Class (b): raw operational policy construction or derived law.
theorem ledger_monotone (balance debit credit : Rat) (recharge : debit≤credit) :
    balance≤balance-debit+credit := by
  have cancellation : balance-debit+debit=balance := by
    simp [Rat.sub_eq_add_neg,Rat.add_assoc,Rat.neg_add_cancel,Rat.add_zero]
  have bound : balance-debit+debit≤balance-debit+credit := Rat.add_le_add_left.mpr recharge
  rwa [cancellation] at bound

-- Class (b): raw operational policy construction or derived law.
def step (branch : Branch X) (x : EventState X) : EventState X :=
  ⟨branch.destination,x.progress+branch.progressIncrement,x.record+branch.recordIncrement,
    x.balance-branch.debit+branch.credit⟩

-- Class (b): raw operational policy construction or derived law.
def findPresent (rows : List (O × Rat)) (normalized : Normalized rows) :
    (rows.find? (fun e => decide (0<e.2))).isSome := by
  obtain ⟨o,w,member,positive⟩ := normalized.2.2
  exact List.find?_isSome.mpr ⟨(o,w),member,by simpa using positive⟩

-- Class (b): raw operational policy construction or derived law.
def firstPositive (rows : List (O × Rat)) (normalized : Normalized rows) : O × Rat :=
  (rows.find? (fun e => decide (0<e.2))).get (findPresent rows normalized)

-- Class (b): raw operational policy construction or derived law.
theorem first_positive_spec (rows : List (O × Rat)) (normalized : Normalized rows) :
    firstPositive rows normalized∈rows ∧ 0<(firstPositive rows normalized).2 := by
  have decoded : rows.find? (fun e => decide (0<e.2))=some (firstPositive rows normalized) :=
    (Option.some_get _).symm
  exact ⟨List.mem_of_find?_eq_some decoded,by simpa using List.find?_some decoded⟩

-- Class (b): raw operational policy construction or derived law.
noncomputable def Safe (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a) :=
  {x : EventState X // x.factor∈greatest m a h ∧ reserve m a h≤x.balance}

-- Class (b): raw operational policy construction or derived law.
noncomputable def safeStep (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (x : Safe m a h) (d : D) : Safe m a h := by
  let r := table m a h x.1.factor d
  have retained := (greatest_retains m a h x.1.factor x.2.1).2 d
  let p := firstPositive r.rows retained.2.1
  have selected := first_positive_spec r.rows retained.2.1
  have branch := retained.2.2 p.1 p.2 selected.1 selected.2
  exact ⟨step (r.branch p.1) x.1,branch.1,
    Rat.le_trans x.2.2 (ledger_monotone _ _ _ branch.2.2.2.2)⟩

-- Class (b): raw operational policy construction or derived law.
noncomputable def TotalComputedPolicy (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a) : Prop :=
  (initial m a h).factor∈greatest m a h ∧ reserve m a h≤(initial m a h).balance

-- Class (b): raw operational policy construction or derived law.
noncomputable def safeTrajectory (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (total : TotalComputedPolicy m a h) (stream : Nat → D) : Nat → Safe m a h
  | 0 => ⟨initial m a h,total⟩
  | n+1 => safeStep m a h (safeTrajectory m a h total stream n) (stream n)

-- Class (b): raw operational policy construction or derived law.
noncomputable def StepOf (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (x : EventState X) (d : D) (y : EventState X) : Prop :=
  let r := table m a h x.factor d
  ∃ o w, (o,w)∈r.rows ∧ 0<w ∧ r.owner=m.target ∧ y=step (r.branch o) x ∧
    0<(r.branch o).progressIncrement ∧ 0<(r.branch o).recordIncrement ∧
    0≤(r.branch o).debit ∧ (r.branch o).debit≤x.balance ∧ (r.branch o).debit≤(r.branch o).credit

-- Class (b): raw operational policy construction or derived law.
theorem safe_step_actual (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (x : Safe m a h) (d : D) : StepOf m a h x.1 d (safeStep m a h x d).1 := by
  let r := table m a h x.1.factor d
  have retained := (greatest_retains m a h x.1.factor x.2.1).2 d
  let p := firstPositive r.rows retained.2.1
  have selected := first_positive_spec r.rows retained.2.1
  have branch := retained.2.2 p.1 p.2 selected.1 selected.2
  exact ⟨p.1,p.2,selected.1,selected.2,retained.1,rfl,branch.2.1,branch.2.2.1,branch.2.2.2.1,
    Rat.le_trans (raw_cost_bounded m a h x.1.factor d p.1) x.2.2,branch.2.2.2.2⟩

-- Class (b): raw operational policy construction or derived law.
theorem actual_step_increments (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (x y : EventState X) (d : D) (law : StepOf m a h x d y) :
    x.progress<y.progress ∧ x.record<y.record ∧ x.balance≤y.balance := by
  obtain ⟨o,w,_,_,_,rfl,progress,record,_,_,recharge⟩ := law
  exact ⟨by dsimp [step]; omega,by dsimp [step]; omega,ledger_monotone _ _ _ recharge⟩

-- Class (b): raw operational policy construction or derived law.
theorem all_streams_infinite_run (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (total : TotalComputedPolicy m a h) (stream : Nat → D) :
    ∃ run : Nat → EventState X, run 0=initial m a h ∧ ∀ n,
      (run n).factor∈greatest m a h ∧ PackageAt m a (run n).factor ∧
      StepOf m a h (run n) (stream n) (run (n+1)) ∧
      (run n).progress<(run (n+1)).progress ∧ (run n).record<(run (n+1)).record ∧
      reserve m a h≤(run n).balance ∧ 0≤(run n).balance := by
  refine ⟨fun n => (safeTrajectory m a h total stream n).1,rfl,?_⟩
  intro n
  let x := safeTrajectory m a h total stream n
  have law := safe_step_actual m a h x (stream n)
  have advances := actual_step_increments m a h x.1 (safeStep m a h x (stream n)).1 (stream n) law
  exact ⟨x.2.1,(greatest_retains m a h x.1.factor x.2.1).1,law,advances.1,advances.2.1,x.2.2,
    Rat.le_trans (max_cost_nonnegative _) x.2.2⟩

-- Class (b): raw operational policy construction or derived law.
theorem greatest_fixed (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a) :
    ViableSet.prune (retain m a h) (greatest m a h)=greatest m a h :=
  ViableSet.greatest_fixed m.states.elems m.states.complete (retain m a h) (retain_monotone m a h)

-- Class (b): raw operational policy construction or derived law.
theorem greatest_contains_every_viable (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (S : List X) (viable : ∀ x∈S, Retains m a h S x) : S⊆greatest m a h :=
  ViableSet.greatest_contains_viable m.states.elems m.states.complete (retain m a h) (retain_monotone m a h) S
    (fun x member => (retain_true_iff _ _ _ _ _).mpr (viable x member))

-- Class (b): raw operational policy construction or derived law.
noncomputable def outcomeTrajectory (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (stream : Nat → D) (outcomes : Nat → O) : Nat → EventState X
  | 0 => initial m a h
  | n+1 => step ((table m a h (outcomeTrajectory m a h stream outcomes n).factor (stream n)).branch (outcomes n))
      (outcomeTrajectory m a h stream outcomes n)

-- Class (b): raw operational policy construction or derived law.
noncomputable def SupportedOutcomes (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (stream : Nat → D) (outcomes : Nat → O) : Prop :=
  ∀ n, ∃ weight, (outcomes n,weight)∈(table m a h (outcomeTrajectory m a h stream outcomes n).factor (stream n)).rows ∧ 0<weight

-- Class (b): raw operational policy construction or derived law.
theorem every_supported_run_safe (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (total : TotalComputedPolicy m a h) (stream : Nat → D) (outcomes : Nat → O)
    (supported : SupportedOutcomes m a h stream outcomes) :
    ∀ n, (outcomeTrajectory m a h stream outcomes n).factor∈greatest m a h ∧
      reserve m a h≤(outcomeTrajectory m a h stream outcomes n).balance := by
  intro n
  induction n with
  | zero => exact total
  | succ n ih =>
    let x := outcomeTrajectory m a h stream outcomes n
    have retained := (greatest_retains m a h x.factor ih.1).2 (stream n)
    obtain ⟨w,member,positive⟩ := supported n
    have branch := retained.2.2 (outcomes n) w member positive
    exact ⟨branch.1,Rat.le_trans ih.2 (ledger_monotone _ _ _ branch.2.2.2.2)⟩

-- Class (b): raw operational policy construction or derived law.
theorem every_supported_actual_step (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (total : TotalComputedPolicy m a h) (stream : Nat → D) (outcomes : Nat → O)
    (supported : SupportedOutcomes m a h stream outcomes) (n : Nat) :
    StepOf m a h (outcomeTrajectory m a h stream outcomes n) (stream n) (outcomeTrajectory m a h stream outcomes (n+1)) := by
  let x := outcomeTrajectory m a h stream outcomes n
  have inside := every_supported_run_safe m a h total stream outcomes supported n
  have retained := (greatest_retains m a h x.factor inside.1).2 (stream n)
  obtain ⟨w,member,positive⟩ := supported n
  have branch := retained.2.2 (outcomes n) w member positive
  exact ⟨outcomes n,w,member,positive,retained.1,rfl,branch.2.1,branch.2.2.1,branch.2.2.2.1,
    Rat.le_trans (raw_cost_bounded m a h x.factor (stream n) (outcomes n)) inside.2,branch.2.2.2.2⟩

-- Class (b): raw operational policy construction or derived law.
theorem all_supported_streams_infinite_laws (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (total : TotalComputedPolicy m a h) (stream : Nat → D) (outcomes : Nat → O)
    (supported : SupportedOutcomes m a h stream outcomes) (n : Nat) :
    let x := outcomeTrajectory m a h stream outcomes n
    let y := outcomeTrajectory m a h stream outcomes (n+1)
    x.factor∈greatest m a h ∧ PackageAt m a x.factor ∧ StepOf m a h x (stream n) y ∧
      x.progress<y.progress ∧ x.record<y.record ∧ reserve m a h≤x.balance ∧ 0≤x.balance := by
  have inside := every_supported_run_safe m a h total stream outcomes supported n
  have law := every_supported_actual_step m a h total stream outcomes supported n
  have advances := actual_step_increments m a h _ _ (stream n) law
  exact ⟨inside.1,(greatest_retains m a h _ inside.1).1,law,advances.1,advances.2.1,inside.2,
    Rat.le_trans (max_cost_nonnegative _) inside.2⟩

-- Class (b): raw operational policy construction or derived law.
noncomputable def selectedOutcomes (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (total : TotalComputedPolicy m a h) (stream : Nat → D) (n : Nat) : O :=
  let x := safeTrajectory m a h total stream n
  let r := table m a h x.1.factor (stream n)
  (firstPositive r.rows ((greatest_retains m a h x.1.factor x.2.1).2 (stream n)).2.1).1

-- Class (b): raw operational policy construction or derived law.
theorem selected_matches_actual (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (total : TotalComputedPolicy m a h) (stream : Nat → D) :
    ∀ n, outcomeTrajectory m a h stream (selectedOutcomes m a h total stream) n=
      (safeTrajectory m a h total stream n).1 := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih => simp only [outcomeTrajectory,ih]; rfl

-- Class (b): raw operational policy construction or derived law.
theorem every_disturbance_has_supported_outcomes (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (total : TotalComputedPolicy m a h) (stream : Nat → D) :
    ∃ outcomes, SupportedOutcomes m a h stream outcomes := by
  refine ⟨selectedOutcomes m a h total stream,?_⟩
  intro n
  rw [selected_matches_actual]
  let x := safeTrajectory m a h total stream n
  let r := table m a h x.1.factor (stream n)
  let normalized := ((greatest_retains m a h x.1.factor x.2.1).2 (stream n)).2.1
  have selected := first_positive_spec r.rows normalized
  exact ⟨(firstPositive r.rows normalized).2,selected.1,selected.2⟩

-- Class (b): raw operational policy construction or derived law.
def depletedBalance (budget : Nat) : Nat → Rat
  | 0 => (budget : Rat)
  | n+1 => depletedBalance budget n-1

-- Class (b): raw operational policy construction or derived law.
theorem debit_without_recharge_step (balance : Rat) : balance-1+0=balance-1 := by
  simp [Rat.add_zero]

-- Class (b): raw operational policy construction or derived law.
theorem depleted_balance_exact (budget : Nat) (n : Nat) :
    depletedBalance budget n=(budget : Rat)-(n : Rat) := by
  induction n with
  | zero => change (budget : Rat)=(budget : Rat)-0; grind
  | succ n ih =>
    simp only [depletedBalance,ih,Rat.natCast_add]
    grind

-- Class (b): raw operational policy construction or derived law.
theorem finite_budget_without_recharge_eventually_insolvent (budget : Nat) :
    depletedBalance budget (budget+1)=(-1 : Rat) ∧ ¬ 0≤depletedBalance budget (budget+1) := by
  rw [depleted_balance_exact,Rat.natCast_add]
  have equal : (budget : Rat)-((budget : Rat)+1)=(-1 : Rat) := by grind
  have one : ((1 : Nat) : Rat)=1 := by decide +kernel
  rw [one,equal]
  exact ⟨rfl,by decide +kernel⟩

-- Class (b): raw operational policy construction or derived law.
theorem actual_unit_cost_depletion (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : Ready m a)
    (stream : Nat → D) (outcomes : Nat → O) (budget : Nat)
    (start : (initial m a h).balance=(budget : Rat))
    (debit : ∀ x d o, ((table m a h x d).branch o).debit=1)
    (credit : ∀ x d o, ((table m a h x d).branch o).credit=0) :
    ∀ n, (outcomeTrajectory m a h stream outcomes n).balance=depletedBalance budget n := by
  intro n
  induction n with
  | zero => exact start
  | succ n ih =>
    simp only [outcomeTrajectory,step,debit,credit,Rat.add_zero,depletedBalance]
    rw [ih]

-- Class (b): raw operational policy construction or derived law.
theorem actual_unrecharged_run_not_solvent_forever (m : Raw Cell Value X D A O)
    (a : Assignment Cell Value) (h : Ready m a) (stream : Nat → D) (outcomes : Nat → O) (budget : Nat)
    (start : (initial m a h).balance=(budget : Rat))
    (debit : ∀ x d o, ((table m a h x d).branch o).debit=1)
    (credit : ∀ x d o, ((table m a h x d).branch o).credit=0) :
    ¬ ∀ n, 0≤(outcomeTrajectory m a h stream outcomes n).balance := by
  intro solvent
  have atFailure := solvent (budget+1)
  rw [actual_unit_cost_depletion m a h stream outcomes budget start debit credit] at atFailure
  exact (finite_budget_without_recharge_eventually_insolvent budget).2 atFailure





end CSTTT.AutonomyTheory.RawRechargingPolicy

namespace CSTTT.AutonomyTheory.RawRechargingPolicy
open CSTTT.TargetTheory.GenericHandoff RegisterInterpreter
variable {Cell X D A O : Type} {Value : Cell → Type}
-- Class (b): exact initial decoding on every partial primitive assignment.
theorem decode_initial_some_iff (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (x : EventState X) :
    decodeInitial m a=some x ↔ m.initialFactor.read a=some x.factor ∧
      m.initialProgress.read a=some x.progress ∧ m.initialRecord.read a=some x.record ∧
      m.initialBalance.read a=some x.balance := by
  cases x
  cases hf : m.initialFactor.read a <;> cases hp : m.initialProgress.read a <;>
    cases hr : m.initialRecord.read a <;> cases hb : m.initialBalance.read a <;>
    simp [decodeInitial,hf,hp,hr,hb]
-- Class (b): actual initial None iff some one of its four consumed reads is absent.
theorem decode_initial_none_iff (m : Raw Cell Value X D A O) (a : Assignment Cell Value) :
    decodeInitial m a=none ↔ m.initialFactor.read a=none ∨
      m.initialProgress.read a=none ∨ m.initialRecord.read a=none ∨
      m.initialBalance.read a=none := by
  cases hf : m.initialFactor.read a <;> cases hp : m.initialProgress.read a <;>
    cases hr : m.initialRecord.read a <;> cases hb : m.initialBalance.read a <;>
    simp [decodeInitial,hf,hp,hr,hb]
end CSTTT.AutonomyTheory.RawRechargingPolicy
