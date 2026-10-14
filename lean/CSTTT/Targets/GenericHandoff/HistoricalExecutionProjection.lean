import CSTTT.Targets.GenericHandoff.HistoricalAcquisition
import CSTTT.Targets.GenericHandoff.ExecutionFrontier

/-! The raw binding between funded execution and historical coordinates.
The projection and outcome decoder are RAW instructions on the same assignment;
all objects are interpreted here. The checked equations range over the entire
actual supported closure. Historical support cannot supply these equations.
This is a generic comparison component, not the complete lineage assembler.
The enclosing interface must identify the decoded historical table with its own
historical-acquisition table and identify its receiver reset instructions. -/
namespace CSTTT.TargetTheory.GenericHandoff.HistoricalExecutionProjection
open RegisterInterpreter CSTTT.TransportTheory

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O P Factor Residue Maintenance Stage Id History RouteId : Type) where
  frontier : ExecutionFrontier.Raw Cell Value R RV D A O P Residue Maintenance Stage Id History RouteId
  factor : Expr Cell Value R RV Unit Factor
  destination : StaticView Cell Value (O → Factor)
  historyRows : StaticView Cell Value (Factor → A → List (Factor × Rat))

variable {Cell R D A O P Factor Residue Maintenance Stage Id History RouteId : Type}
  {Value : Cell → Type} {RV : R → Type}

abbrev Ready (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) :=
  ExecutionFrontier.Ready raw.frontier a ∧ Complete raw.factor.dependencies a ∧
    Complete raw.destination.dependencies a ∧ Complete raw.historyRows.dependencies a

noncomputable def factor (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (x : Registers R RV) : Factor :=
  RegisterFuture.read raw.factor a h.2.1 x

noncomputable def destination (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) : O → Factor := Classical.choose (raw.destination.present a h.2.2.1)

noncomputable def historyRows (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) : Factor → A → List (Factor × Rat) :=
  Classical.choose (raw.historyRows.present a h.2.2.2)

variable [DecidableEq O]

/-- Raw list equations, not an assumed simulation flag. Every branch,
probability and update in the actual closure participates. -/
structure Laws (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) : Prop where
  rows : ∀ x, ExecutionFrontier.Closure raw.frontier a h.1 x → ∀ d act,
    (AcquisitionExecution.rows raw.frontier.acquisition a x d act).map
      (fun e => (destination raw a h e.1,e.2)) = historyRows raw a h (factor raw a h x) act
  successor : ∀ x, ExecutionFrontier.Closure raw.frontier a h.1 x → ∀ d act o,
    StrategyGame.PositiveSupport (AcquisitionExecution.rows raw.frontier.acquisition a) x d act o →
    factor raw a h (AcquisitionExecution.update raw.frontier.acquisition a h.1.1 x d act o) =
      destination raw a h o

def Valid (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) : Prop := ∃ h : Ready raw a, Laws raw a h

/-- Word induction over ACTUAL support. The history terminal is the actual
factor-coordinate image; no predictive representative or source-funded flag
is substituted for a supported execution. -/
theorem fold_projects (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (hl : Laws raw a h)
    (x : Registers R RV) (hx : ExecutionFrontier.Closure raw.frontier a h.1 x)
    (word : List (D × A × O)) (hc : ExecutionFrontier.PrefixCheck raw.frontier a h.1 x word) :
    factor raw a h (AcquisitionExecution.foldHistory raw.frontier.acquisition a h.1.1 x word) =
      HistoricalSupport.fold (factor raw a h x) (word.map fun e => (e.2.1,destination raw a h e.2.2)) := by
  induction word generalizing x with
  | nil => rfl
  | cons step rest ih =>
    rcases step with ⟨d,act,o⟩
    have hn : ExecutionFrontier.Closure raw.frontier a h.1
        (AcquisitionExecution.update raw.frontier.acquisition a h.1.1 x d act o) := by
      have hs := FutureClosure.step hx (d,act) o hc.2.2.1
      simpa only [RegisterFuture.dynamics,ExecutionFrontier.updater_shared] using hs
    simp only [AcquisitionExecution.foldHistory,List.map_cons,HistoricalSupport.fold]
    rw [ih _ hn hc.2.2.2.2.2,hl.successor x hx d act o hc.2.2.2.1]

/-- One actual positive branch survives in the projected RAW support table.
The proof does not rely on an aggregate weight hiding a missing destination. -/
theorem support_projects (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (hl : Laws raw a h)
    (x : Registers R RV) (hx : ExecutionFrontier.Closure raw.frontier a h.1 x)
    (d : D) (act : A) (o : O)
    (hp : StrategyGame.PositiveSupport (AcquisitionExecution.rows raw.frontier.acquisition a) x d act o) :
    ∃ w, (destination raw a h o,w) ∈ historyRows raw a h (factor raw a h x) act ∧ 0 < w := by
  obtain ⟨w,hw,hpos⟩ := hp
  refine ⟨w,?_,hpos⟩
  rw [← hl.rows x hx d act]
  exact List.mem_map.mpr ⟨(o,w),hw,rfl⟩

theorem missing_projection_rejected (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.factor.dependencies) (hm : a k = none) : ¬ Valid raw a := by
  rintro ⟨h,_⟩
  have hp := h.2.1 k hk
  rw [hm] at hp
  contradiction

theorem missing_decoder_rejected (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.destination.dependencies) (hm : a k = none) : ¬ Valid raw a := by
  rintro ⟨h,_⟩
  have hp := h.2.2.1 k hk
  rw [hm] at hp
  contradiction

theorem missing_table_rejected (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.historyRows.dependencies) (hm : a k = none) : ¬ Valid raw a := by
  rintro ⟨h,_⟩
  have hp := h.2.2.2 k hk
  rw [hm] at hp
  contradiction

/-- A wrong successor anywhere in the actual closure rejects the generic
comparison gate. The absence premise is not conjoined with valid laws. -/
theorem successor_mismatch_rejected (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (x : Registers R RV)
    (hx : ExecutionFrontier.Closure raw.frontier a h.1 x) (d : D) (act : A) (o : O)
    (hp : StrategyGame.PositiveSupport (AcquisitionExecution.rows raw.frontier.acquisition a) x d act o)
    (bad : factor raw a h (AcquisitionExecution.update raw.frontier.acquisition a h.1.1 x d act o) ≠ destination raw a h o) :
    ¬ Valid raw a := by
  rintro ⟨h',laws⟩
  exact bad (laws.successor x hx d act o hp)

theorem row_mismatch_rejected (raw : Raw Cell Value R RV D A O P Factor Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : Ready raw a) (x : Registers R RV)
    (hx : ExecutionFrontier.Closure raw.frontier a h.1 x) (d : D) (act : A)
    (bad : (AcquisitionExecution.rows raw.frontier.acquisition a x d act).map
      (fun e => (destination raw a h e.1,e.2)) ≠ historyRows raw a h (factor raw a h x) act) : ¬ Valid raw a := by
  rintro ⟨h',laws⟩
  exact bad (laws.rows x hx d act)



end CSTTT.TargetTheory.GenericHandoff.HistoricalExecutionProjection
