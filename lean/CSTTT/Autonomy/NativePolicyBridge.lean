import CSTTT.Autonomy.RawRechargingPolicy
import CSTTT.Targets.GenericHandoff.ResourceRuntime
import CSTTT.Targets.GenericHandoff.RegisterInitialization

namespace CSTTT.AutonomyTheory.NativePolicyBridge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open CSTTT.AutonomyTheory.RawRechargingPolicy
variable {Cell R X D A O Res Residue Hist : Type} {Value : Cell → Type} {RV : R → Type}
variable [DecidableEq X]
-- Class (b): explicit native selected-policy correspondence construction.
def decodeNative (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue)
    (account : Res) (a : Assignment Cell Value) (run : Registers R RV) : Option (EventState X) := do
  let candidate ← native.factor.eval a run ()
  let factor ← candidate
  let progress ← native.progress.eval a run ()
  let record ← native.record.eval a run ()
  let accounts ← native.accounts.eval a run ()
  pure ⟨factor,progress,record,((accounts account).balance : Rat)⟩
-- Class (b): explicit native selected-policy correspondence construction.
structure LocalBinding (m : Raw Cell Value X D A O) (a : Assignment Cell Value) (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue)
    (cfg : ResourceRuntime.Schema X Res) (nh : ResourceRuntime.Ready native a)
    (p : InitialProgram Cell Value R RV Hist) (ph : RegisterInitialization.Ready p a) (hist : Hist) where
  account : Res
  auxiliary : Registers R RV → EventState X → Prop
  nativeCells : (k : Cell) → Expr Cell Value R RV Unit (Value k)
  target : cfg.target=m.target
  init : decodeNative native account a (RegisterInitialization.initial p a ph hist)=some (initial m a h) ∧
    auxiliary (RegisterInitialization.initial p a ph hist) (initial m a h)
  packageCells : ∀ r x, decodeNative native account a r=some x → auxiliary r x →
    ∀ k, (nativeCells k).eval a r ()=(m.cells k).eval a (fun _ => ()) x.factor
  row : ∀ r x, decodeNative native account a r=some x → auxiliary r x → ∀ d,
    native.execution.row.eval a r (d,(table m a h x.factor d).action)=some (table m a h x.factor d).rows
  update : ∀ r x, decodeNative native account a r=some x → auxiliary r x →
    x.factor∈greatest m a h → reserve m a h≤x.balance → ∀ d o w,
    (o,w)∈(table m a h x.factor d).rows → 0<w →
    let next := ResourceRuntime.update native a nh r d (table m a h x.factor d).action o
    let y := step ((table m a h x.factor d).branch o) x
    decodeNative native account a next=some y ∧ auxiliary next y
  closed : ∀ r x, decodeNative native account a r=some x → auxiliary r x →
    x.factor∈greatest m a h → reserve m a h≤x.balance → ResourceRuntime.ResourceClosed cfg native a r
  legal : ∀ r x, decodeNative native account a r=some x → auxiliary r x →
    x.factor∈greatest m a h → reserve m a h≤x.balance → ∀ d,
    ResourceRuntime.Legal cfg native a r d (table m a h x.factor d).action
  advancement : ∀ r x, decodeNative native account a r=some x → auxiliary r x →
    x.factor∈greatest m a h → reserve m a h≤x.balance → ∀ d o w,
    (o,w)∈(table m a h x.factor d).rows → 0<w →
    ResourceRuntime.StepLaw cfg native a nh r d (table m a h x.factor d).action o
-- Class (b): explicit native selected-policy correspondence construction.
noncomputable def nativeRun (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue) (nh : ResourceRuntime.Ready native a)
    (p : InitialProgram Cell Value R RV Hist) (ph : RegisterInitialization.Ready p a) (hist : Hist)
    (stream : Nat → D) (outcomes : Nat → O) : Nat → Registers R RV
  | 0 => RegisterInitialization.initial p a ph hist
  | n+1 =>
    let x := outcomeTrajectory m a h stream outcomes n
    ResourceRuntime.update native a nh (nativeRun m a h native nh p ph hist stream outcomes n)
      (stream n) (table m a h x.factor (stream n)).action (outcomes n)
-- Class (b): explicit native selected-policy correspondence construction.
theorem native_run_related (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue)
    (cfg : ResourceRuntime.Schema X Res) (nh : ResourceRuntime.Ready native a)
    (p : InitialProgram Cell Value R RV Hist) (ph : RegisterInitialization.Ready p a) (hist : Hist)
    (b : LocalBinding m a h native cfg nh p ph hist)
    (total : TotalComputedPolicy m a h) (stream : Nat → D) (outcomes : Nat → O)
    (supported : SupportedOutcomes m a h stream outcomes) : ∀ n,
    decodeNative native b.account a (nativeRun m a h native nh p ph hist stream outcomes n)=
      some (outcomeTrajectory m a h stream outcomes n) ∧
    b.auxiliary (nativeRun m a h native nh p ph hist stream outcomes n) (outcomeTrajectory m a h stream outcomes n) := by
  intro n
  induction n with
  | zero => exact b.init
  | succ n ih =>
    obtain ⟨w,member,positive⟩ := supported n
    have safe := every_supported_run_safe m a h total stream outcomes supported n
    exact b.update _ _ ih.1 ih.2 safe.1 safe.2 (stream n) (outcomes n) w member positive
-- Class (b): explicit native selected-policy correspondence construction.
theorem native_support_iff (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue)
    (cfg : ResourceRuntime.Schema X Res) (nh : ResourceRuntime.Ready native a)
    (p : InitialProgram Cell Value R RV Hist) (ph : RegisterInitialization.Ready p a) (hist : Hist)
    (b : LocalBinding m a h native cfg nh p ph hist) (r : Registers R RV) (x : EventState X)
    (decoded : decodeNative native b.account a r=some x) (aux : b.auxiliary r x) (d : D) (o : O) :
    StrategyGame.PositiveSupport (ResourceRuntime.rows native a) r d (table m a h x.factor d).action o ↔
      ∃ w, (o,w)∈(table m a h x.factor d).rows ∧ 0<w := by
  unfold StrategyGame.PositiveSupport ResourceRuntime.rows
  rw [b.row r x decoded aux d]
  rfl

-- Class (b): explicit native selected-policy correspondence construction.
theorem every_native_supported_related (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue)
    (cfg : ResourceRuntime.Schema X Res) (nh : ResourceRuntime.Ready native a)
    (p : InitialProgram Cell Value R RV Hist) (ph : RegisterInitialization.Ready p a) (hist : Hist)
    (b : LocalBinding m a h native cfg nh p ph hist) (total : TotalComputedPolicy m a h)
    (stream : Nat → D) (outcomes : Nat → O)
    (supported : ∀ n, StrategyGame.PositiveSupport (ResourceRuntime.rows native a)
      (nativeRun m a h native nh p ph hist stream outcomes n) (stream n)
      (table m a h (outcomeTrajectory m a h stream outcomes n).factor (stream n)).action (outcomes n)) :
    ∀ n, let x := outcomeTrajectory m a h stream outcomes n
      let r := nativeRun m a h native nh p ph hist stream outcomes n
      decodeNative native b.account a r=some x ∧ b.auxiliary r x ∧
        x.factor∈greatest m a h ∧ reserve m a h≤x.balance := by
  intro n
  induction n with
  | zero => exact ⟨b.init.1,b.init.2,total⟩
  | succ n ih =>
    let x := outcomeTrajectory m a h stream outcomes n
    let r := nativeRun m a h native nh p ph hist stream outcomes n
    obtain ⟨w,member,positive⟩ := (native_support_iff m a h native cfg nh p ph hist b r x ih.1 ih.2.1 (stream n) (outcomes n)).mp (supported n)
    have related := b.update r x ih.1 ih.2.1 ih.2.2.1 ih.2.2.2 (stream n) (outcomes n) w member positive
    have retained := (greatest_retains m a h x.factor ih.2.2.1).2 (stream n)
    have branch := retained.2.2 (outcomes n) w member positive
    exact ⟨related.1,related.2,branch.1,Rat.le_trans ih.2.2.2 (ledger_monotone _ _ _ branch.2.2.2.2)⟩

-- Class (b): explicit native selected-policy correspondence construction.
theorem every_native_supported_generic (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue)
    (cfg : ResourceRuntime.Schema X Res) (nh : ResourceRuntime.Ready native a)
    (p : InitialProgram Cell Value R RV Hist) (ph : RegisterInitialization.Ready p a) (hist : Hist)
    (b : LocalBinding m a h native cfg nh p ph hist) (total : TotalComputedPolicy m a h)
    (stream : Nat → D) (outcomes : Nat → O)
    (supported : ∀ n, StrategyGame.PositiveSupport (ResourceRuntime.rows native a)
      (nativeRun m a h native nh p ph hist stream outcomes n) (stream n)
      (table m a h (outcomeTrajectory m a h stream outcomes n).factor (stream n)).action (outcomes n)) :
    SupportedOutcomes m a h stream outcomes := by
  intro n
  have related := every_native_supported_related m a h native cfg nh p ph hist b total stream outcomes supported n
  exact (native_support_iff m a h native cfg nh p ph hist b _ _ related.1 related.2.1 (stream n) (outcomes n)).mp (supported n)

-- Class (b): explicit native selected-policy correspondence construction.
theorem every_native_supported_operational_laws (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue)
    (cfg : ResourceRuntime.Schema X Res) (nh : ResourceRuntime.Ready native a)
    (p : InitialProgram Cell Value R RV Hist) (ph : RegisterInitialization.Ready p a) (hist : Hist)
    (b : LocalBinding m a h native cfg nh p ph hist) (total : TotalComputedPolicy m a h)
    (stream : Nat → D) (outcomes : Nat → O)
    (supported : ∀ n, StrategyGame.PositiveSupport (ResourceRuntime.rows native a)
      (nativeRun m a h native nh p ph hist stream outcomes n) (stream n)
      (table m a h (outcomeTrajectory m a h stream outcomes n).factor (stream n)).action (outcomes n)) (n : Nat) :
    let x := outcomeTrajectory m a h stream outcomes n
    let y := outcomeTrajectory m a h stream outcomes (n+1)
    let r := nativeRun m a h native nh p ph hist stream outcomes n
    m.clauses.accept (fun k => (b.nativeCells k).eval a r ()) ∧
    ResourceRuntime.ResourceClosed cfg native a r ∧
    ResourceRuntime.Legal cfg native a r (stream n) (table m a h x.factor (stream n)).action ∧
    ResourceRuntime.StepLaw cfg native a nh r (stream n) (table m a h x.factor (stream n)).action (outcomes n) ∧
    decodeNative native b.account a r=some x ∧
    x.progress<y.progress ∧ x.record<y.record ∧ 0≤x.balance := by
  have related := every_native_supported_related m a h native cfg nh p ph hist b total stream outcomes supported n
  have gs := every_native_supported_generic m a h native cfg nh p ph hist b total stream outcomes supported
  have gl := all_supported_streams_infinite_laws m a h total stream outcomes gs n
  obtain ⟨w,member,positive⟩ := gs n
  have cells := funext (b.packageCells _ _ related.1 related.2.1)
  have package : m.clauses.accept (fun k => (b.nativeCells k).eval a (nativeRun m a h native nh p ph hist stream outcomes n) ()) := by
    rw [cells]
    exact gl.2.1
  exact ⟨package,b.closed _ _ related.1 related.2.1 related.2.2.1 related.2.2.2,
    b.legal _ _ related.1 related.2.1 related.2.2.1 related.2.2.2 (stream n),
    b.advancement _ _ related.1 related.2.1 related.2.2.1 related.2.2.2 (stream n) (outcomes n) w member positive,
    related.1,gl.2.2.2.1,gl.2.2.2.2.1,gl.2.2.2.2.2.2⟩
-- Class (b): explicit native selected-policy correspondence construction.
noncomputable def nativePolicy (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue) (account : Res)
    (r : Registers R RV) (d : D) : Option A :=
  (decodeNative native account a r).map fun x => (table m a h x.factor d).action

-- Class (b): explicit native selected-policy correspondence construction.
theorem native_policy_read (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue) (account : Res)
    (r : Registers R RV) (x : EventState X)
    (decoded : decodeNative native account a r=some x) (d : D) :
    nativePolicy m a h native account r d=some (table m a h x.factor d).action := by
  simp only [nativePolicy,decoded,Option.map_some]

-- Class (b): explicit native selected-policy correspondence construction.
theorem missing_native_policy_rejects (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue) (account : Res)
    (r : Registers R RV) (missing : decodeNative native account a r=none) (d : D) :
    nativePolicy m a h native account r d=none := by
  simp only [nativePolicy,missing,Option.map_none]

-- Class (b): explicit native selected-policy correspondence construction.
theorem every_disturbance_has_native_supported_outcomes (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue)
    (cfg : ResourceRuntime.Schema X Res) (nh : ResourceRuntime.Ready native a)
    (p : InitialProgram Cell Value R RV Hist) (ph : RegisterInitialization.Ready p a) (hist : Hist)
    (b : LocalBinding m a h native cfg nh p ph hist) (total : TotalComputedPolicy m a h)
    (stream : Nat → D) : ∃ outcomes : Nat → O, ∀ n,
    StrategyGame.PositiveSupport (ResourceRuntime.rows native a)
      (nativeRun m a h native nh p ph hist stream outcomes n) (stream n)
      (table m a h (outcomeTrajectory m a h stream outcomes n).factor (stream n)).action (outcomes n) := by
  obtain ⟨outcomes,supported⟩ := CSTTT.AutonomyTheory.RawRechargingPolicy.every_disturbance_has_supported_outcomes m a h total stream
  refine ⟨outcomes,?_⟩
  intro n
  have related := native_run_related m a h native cfg nh p ph hist b total stream outcomes supported n
  exact (native_support_iff m a h native cfg nh p ph hist b _ _ related.1 related.2 (stream n) (outcomes n)).mpr (supported n)
end CSTTT.AutonomyTheory.NativePolicyBridge
namespace CSTTT.AutonomyTheory.NativePolicyBridge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open CSTTT.AutonomyTheory.RawRechargingPolicy
variable {Cell R X D A O Res Residue Hist : Type} {Value : Cell → Type} {RV : R → Type}
variable [DecidableEq X]
-- Class (b): actual decoded policy drives optional recursion; absence propagates.
noncomputable def optionalNativeRun (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue) (nh : ResourceRuntime.Ready native a)
    (account : Res) (p : InitialProgram Cell Value R RV Hist) (ph : RegisterInitialization.Ready p a) (hist : Hist)
    (stream : Nat → D) (outcomes : Nat → O) : Nat → Option (Registers R RV)
  | 0 => some (RegisterInitialization.initial p a ph hist)
  | n+1 => do
    let previous ← optionalNativeRun m a h native nh account p ph hist stream outcomes n
    let action ← nativePolicy m a h native account previous (stream n)
    pure (ResourceRuntime.update native a nh previous (stream n) action (outcomes n))
-- Class (b): equality with the actual native controller on every supported stream.
theorem optional_native_run_eq (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue)
    (cfg : ResourceRuntime.Schema X Res) (nh : ResourceRuntime.Ready native a)
    (p : InitialProgram Cell Value R RV Hist) (ph : RegisterInitialization.Ready p a) (hist : Hist)
    (b : LocalBinding m a h native cfg nh p ph hist) (total : TotalComputedPolicy m a h)
    (stream : Nat → D) (outcomes : Nat → O)
    (supported : ∀ n, StrategyGame.PositiveSupport (ResourceRuntime.rows native a)
      (nativeRun m a h native nh p ph hist stream outcomes n) (stream n)
      (table m a h (outcomeTrajectory m a h stream outcomes n).factor (stream n)).action (outcomes n)) :
    ∀ n, optionalNativeRun m a h native nh b.account p ph hist stream outcomes n=
      some (nativeRun m a h native nh p ph hist stream outcomes n) := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    have related := every_native_supported_related m a h native cfg nh p ph hist b total stream outcomes supported n
    have action := native_policy_read m a h native b.account _ _ related.1 (stream n)
    simp only [optionalNativeRun,ih,Option.bind_eq_bind,Option.bind_some,action]
    rfl
-- Class (b): an absent optional trajectory has no next policy state.
theorem optional_native_run_missing (m : Raw Cell Value X D A O) (a : Assignment Cell Value)
    (h : CSTTT.AutonomyTheory.RawRechargingPolicy.Ready m a)
    (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue) (nh : ResourceRuntime.Ready native a)
    (account : Res) (p : InitialProgram Cell Value R RV Hist) (ph : RegisterInitialization.Ready p a) (hist : Hist)
    (stream : Nat → D) (outcomes : Nat → O) (n : Nat)
    (missing : optionalNativeRun m a h native nh account p ph hist stream outcomes n=none) :
    optionalNativeRun m a h native nh account p ph hist stream outcomes (n+1)=none := by
  simp only [optionalNativeRun,missing,Option.bind_eq_bind,Option.bind_none]
end CSTTT.AutonomyTheory.NativePolicyBridge

namespace CSTTT.AutonomyTheory.NativePolicyBridge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open CSTTT.AutonomyTheory.RawRechargingPolicy
variable {Cell R X D A O Res Residue : Type} {Value : Cell → Type} {RV : R → Type}
-- Class (b): exact native decoder return on every partial primitive assignment and register state.
theorem decode_native_some_iff (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue)
    (account : Res) (a : Assignment Cell Value) (run : Registers R RV) (x : EventState X) :
    decodeNative native account a run=some x ↔
      native.factor.eval a run ()=some (some x.factor) ∧
      native.progress.eval a run ()=some x.progress ∧
      native.record.eval a run ()=some x.record ∧
      ∃ accounts, native.accounts.eval a run ()=some accounts ∧
        ((accounts account).balance : Rat)=x.balance := by
  cases x with
  | mk factor progress record balance =>
    cases hf : native.factor.eval a run () with
    | none => simp [decodeNative,hf]
    | some f =>
      cases f with
      | none => simp [decodeNative,hf]
      | some f =>
        cases hp : native.progress.eval a run () <;>
          cases hr : native.record.eval a run () <;>
          cases ha : native.accounts.eval a run () <;>
          simp [decodeNative,hf,hp,hr,ha,EventState.mk.injEq]
-- Class (b): exact native absence, including an absent optional factor inside a present expression.
theorem decode_native_none_iff (native : ResourceRuntime.Raw Cell Value R RV D A O X Res Residue)
    (account : Res) (a : Assignment Cell Value) (run : Registers R RV) :
    decodeNative native account a run=none ↔
      native.factor.eval a run ()=none ∨ native.factor.eval a run ()=some none ∨
      native.progress.eval a run ()=none ∨ native.record.eval a run ()=none ∨
      native.accounts.eval a run ()=none := by
  cases hf : native.factor.eval a run () with
  | none => simp [decodeNative,hf]
  | some f =>
    cases f with
    | none => simp [decodeNative,hf]
    | some f =>
      cases hp : native.progress.eval a run () <;>
        cases hr : native.record.eval a run () <;>
        cases ha : native.accounts.eval a run () <;>
        simp [decodeNative,hf,hp,hr,ha]
end CSTTT.AutonomyTheory.NativePolicyBridge
