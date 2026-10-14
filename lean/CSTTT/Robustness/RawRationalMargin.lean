import CSTTT.Robustness.RationalRegisters
import CSTTT.Targets.GenericHandoff.FinalHandoff

/-! Generic binding of the register extension to one owning raw handoff (b).
The entire original source run and profile remain under erasure. Extended Rat
observers measure the original coordinate plus operational offset registers.
Whole inherited F/O gates are evaluated on the projected original source,
not on a new hypothetical Rat-valued version of the original checker. -/
namespace CSTTT.RobustnessTheory.RawRationalMargin
open CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open ExactFiveMargins RationalRegisters

variable {Cell R Env X : Type} {Value : Cell → Type} {RV : R → Type}
-- Class (b): reindex an initial/static instruction without a run argument.
def inflateStatic {X : Type} (e : Expr Cell Value Empty NoValue Env X) : Expr Cell Value R RV Env X :=
  match e with
  | .literal v => .literal v
  | .cell k => .cell k
  | .register r => nomatch r
  | .environment f => .environment f
  | .map f arg => .map f (inflateStatic arg)
  | .pair x y => .pair (inflateStatic x) (inflateStatic y)
  | .choose c x y => .choose (inflateStatic c) (inflateStatic x) (inflateStatic y)

-- Class (b): exact interpretation law for every partial assignment.
theorem inflate_eval (e : Expr Cell Value Empty NoValue Env X)
    (a : Assignment Cell Value) (run : Registers R RV) (env : Env) :
    (inflateStatic e).eval a run env=e.eval a noRegisters env := by
  induction e <;> simp_all [inflateStatic,Expr.eval]
  rename_i r
  exact nomatch r

variable {SC SR TR S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint : Type}
  {SourceValue : SC → Type} {SRV : SR → Type} {TRV : TR → Type}
local notation "Model" => FinalHandoff.Raw SC Cell SourceValue Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint

-- Class (b): all five expressions come from the SAME old owning raw frame.
def originalObserver (m : Model) : Coordinate → Expr Cell Value SR SRV Unit Rat
  | .predictive => .map (fun v : (P → Nat) × P => (v.1 v.2 : Rat))
      (.pair (inflateStatic m.base.predictiveCoordinate.instruction) m.base.frames.sourceFrame.readouts.predictive)
  | .order => .map (fun n : Nat => (n : Rat)) m.base.frames.sourceFrame.readouts.order
  | .tick => .map (fun n : Nat => (n : Rat)) m.base.frames.sourceFrame.readouts.ticks
  | .progress => .map (fun n : Nat => (n : Rat)) m.base.frames.sourceFrame.readouts.progress
  | .record => .map (fun n : Nat => (n : Rat)) m.base.frames.sourceFrame.readouts.record

-- Class (b): exact coordinate/profile decoding, including missing inputs.
theorem predictive_observer_eq (m : Model) (a : Assignment Cell Value) (run : Registers SR SRV) :
    (originalObserver m .predictive).eval a run ()=(do
      let coordinate ← m.base.predictiveCoordinate.read a
      let p ← m.base.frames.sourceFrame.readouts.predictive.eval a run ()
      pure (coordinate p : Rat)) := by
  simp only [originalObserver,Expr.eval,inflate_eval,StaticView.read]
  cases m.base.predictiveCoordinate.instruction.eval a noRegisters () <;>
    cases m.base.frames.sourceFrame.readouts.predictive.eval a run () <;> rfl

-- Class (b): correction is a new optional primitive, not a derived verdict.
structure Input (SC : Type) (SourceValue : SC → Type) where
  source : Assignment SC SourceValue
  correction : Option Vector

variable [DecidableEq Cell] [DecidableEq S] [DecidableEq O] [DecidableEq Route]
  [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner]
-- Class (b): the owning constructor supplies EVERY original target cell.
def target (m : Model) (input : Input SC SourceValue) :
    Assignment (ExtendedCell Cell) (ExtendedValue Value) :=
  extendAssignment (OwningHandoff.target m.base input.source) input.correction

-- Class (b): exact erasure of all original partial source data.
theorem target_projection (m : Model) (input : Input SC SourceValue) :
    projectAssignment (target m input)=OwningHandoff.target m.base input.source := rfl

-- Class (b): actual raw initializer; no candidate initial run is supplied.
def initializer (m : Model) := correctedInitializer m.base.frames.sourceFrame.acquisition.initializer
-- Class (b): actual raw acquisition program plus consumed correction cell.
def program (m : Model) := correctedProgram m.base.frames.sourceFrame.acquisition.execution.program
-- Class (b): actual old rows are reindexed, not supplied support predicates.
def row (m : Model) := liftExpr (embedCells m.base.frames.sourceFrame.acquisition.execution.row)
-- Class (b): five actual extended observers.
def observer (m : Model) (i : Coordinate) := correctedNumeric (originalObserver m i) i
-- Class (b): original complete profile readout is retained under erasure.
def profile (m : Model) := liftExpr (embedCells m.base.frames.sourceFrame.readouts.predictive)

-- Class (b): every original run/profile survives, including missing static reads.
theorem profile_erasure (m : Model) (input : Input SC SourceValue) (run : @LiftRun SR SRV) :
    (profile m).eval (target m input) run ()=
      m.base.frames.sourceFrame.readouts.predictive.eval (OwningHandoff.target m.base input.source) (erase run) () := by
  rw [profile,lift_eval,embed_eval,target_projection]

-- Class (b): optional actual row equality, so no missing row is fabricated.
theorem row_erasure (m : Model) (input : Input SC SourceValue) (run : @LiftRun SR SRV) (d : D) (act : A) :
    (row m).eval (target m input) run (d,act)=
      m.base.frames.sourceFrame.acquisition.execution.row.eval
        (OwningHandoff.target m.base input.source) (erase run) (d,act) := by
  rw [row,lift_eval,embed_eval,target_projection]

-- Class (b): support consumes the optional actual row, never a default row.
def Supported (m : Model) (input : Input SC SourceValue) (run : @LiftRun SR SRV)
    (d : D) (act : A) (outcome : O) : Prop :=
  ∃ rows, (row m).eval (target m input) run (d,act)=some rows ∧
    ∃ weight, (outcome,weight)∈rows ∧ 0<weight

-- Class (b): exact support equivalence on every partial original input.
theorem supported_erasure (m : Model) (input : Input SC SourceValue) (run : @LiftRun SR SRV)
    (d : D) (act : A) (outcome : O) :
    Supported m input run d act outcome ↔
      ∃ rows, m.base.frames.sourceFrame.acquisition.execution.row.eval
        (OwningHandoff.target m.base input.source) (erase run) (d,act)=some rows ∧
        ∃ weight, (outcome,weight)∈rows ∧ 0<weight := by
  unfold Supported
  rw [row_erasure]

-- Class (b): aggregated actual optional probability includes all duplicate entries.
def outcomeWeight (m : Model) (input : Input SC SourceValue) (run : @LiftRun SR SRV)
    (d : D) (act : A) (outcome : O) : Option Rat :=
  ((row m).eval (target m input) run (d,act)).map
    (fun rows => ((rows.filter (fun e => e.1 == outcome)).map Prod.snd).sum)

-- Class (b): exact aggregated weight equality, retaining missing-row absence.
theorem outcome_weight_erasure (m : Model) (input : Input SC SourceValue) (run : @LiftRun SR SRV)
    (d : D) (act : A) (outcome : O) :
    outcomeWeight m input run d act outcome=
      (m.base.frames.sourceFrame.acquisition.execution.row.eval
        (OwningHandoff.target m.base input.source) (erase run) (d,act)).map
        (fun rows => ((rows.filter (fun e => e.1 == outcome)).map Prod.snd).sum) := by
  rw [outcomeWeight,row_erasure]

-- Class (b): every partial input; readiness is derived from raw dependencies.
theorem program_ready_iff (m : Model) (input : Input SC SourceValue) :
    ProgramReady (program m) (target m input) ↔
      ProgramReady m.base.frames.sourceFrame.acquisition.execution.program
        (OwningHandoff.target m.base input.source) ∧ input.correction≠none := by
  rw [program,corrected_ready_iff,target_projection]
  rfl

-- Class (b): missing correction refutes actual program readiness.
theorem missing_correction_not_ready (m : Model) (input : Input SC SourceValue)
    (missing : input.correction=none) : ¬ ProgramReady (program m) (target m input) := by
  rw [program_ready_iff]
  simp [missing]

-- Class (b): the old complete source execution and an actual correction cell.
def EventReady (m : Model) (input : Input SC SourceValue) : Prop :=
  ExecutionFrontier.Ready m.base.frames.sourceFrame (OwningHandoff.target m.base input.source) ∧ input.correction≠none

-- Class (b): actual raw extended initialization from source primitives.
noncomputable def initialRun (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (hist : H) : @LiftRun SR SRV :=
  RegisterInitialization.initial (initializer m) (target m input)
    ((corrected_initial_ready_iff _ _).mpr ready.1.1.2.1) hist

-- Class (b): actual raw extended acquisition updater.
noncomputable def updateRun (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (run : @LiftRun SR SRV) (d : D) (act : A) (outcome : O) : @LiftRun SR SRV :=
  checkedExecute (program m) (target m input)
    ((program_ready_iff m input).mpr ⟨ready.1.1.2.2.2.1,ready.2⟩) run (d,act,outcome)

-- Class (b): erasure returns the original actual source initializer.
theorem initial_run_erasure (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (hist : H) :
    erase (initialRun m input ready hist)=
      ExecutionFrontier.initial m.base.frames.sourceFrame (OwningHandoff.target m.base input.source) ready.1 hist := by
  unfold initialRun initializer
  rw [corrected_initial_erases]
  rfl

-- Class (b): offsets are derived zeros, never supplied initial measurements.
theorem initial_run_offsets (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (hist : H) :
    offsets (initialRun m input ready hist)=fun _ => 0 :=
  corrected_initial_offsets _ _ _ hist

-- Class (b): erasure returns the original actual acquisition update.
theorem update_run_erasure (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (run : @LiftRun SR SRV) (d : D) (act : A) (outcome : O) :
    erase (updateRun m input ready run d act outcome)=
      AcquisitionExecution.update m.base.frames.sourceFrame.acquisition
        (OwningHandoff.target m.base input.source) ready.1.1 (erase run) d act outcome := by
  unfold updateRun program
  rw [corrected_update_erases]
  rfl

-- Class (b): the consumed correction changes actual operational registers.
theorem update_run_offsets (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (run : @LiftRun SR SRV) (d : D) (act : A) (outcome : O)
    (delta : Vector) (decoded : input.correction=some delta) :
    offsets (updateRun m input ready run d act outcome)=fun i => offsets run i+delta i :=
  corrected_offset_update _ _ _ run (d,act,outcome) delta decoded

-- Class (b): actual optional numeric observer, retaining all original reads.
theorem observer_read (m : Model) (input : Input SC SourceValue) (run : @LiftRun SR SRV) (i : Coordinate) :
    (observer m i).eval (target m input) run ()=
      ((originalObserver m i).eval (OwningHandoff.target m.base input.source) (erase run) ()).map
        (fun v => v+offsets run i) := by
  rw [observer,corrected_numeric_read,target_projection]

-- Class (b): all five optional expressions are consumed without defaults.
def readVector (read : Coordinate → Option Rat) : Option Vector := do
  let predictive ← read .predictive
  let order ← read .order
  let tick ← read .tick
  let progress ← read .progress
  let record ← read .record
  pure fun i => match i with
    | .predictive => predictive | .order => order | .tick => tick
    | .progress => progress | .record => record

-- Class (b): one missing coordinate refutes the whole actual numeric readout.
theorem read_vector_missing (read : Coordinate → Option Rat) (i : Coordinate) (missing : read i=none) :
    readVector read=none := by
  cases i <;> cases hp : read .predictive <;> cases ho : read .order <;>
    cases ht : read .tick <;> cases hg : read .progress <;> cases hr : read .record <;>
    simp_all [readVector]

-- Class (b): the full vector is assembled only from decoded raw values.
theorem read_vector_some (read : Coordinate → Option Rat) (v : Vector) (decoded : ∀ i, read i=some (v i)) :
    readVector read=some v := by
  simp only [readVector,decoded]
  apply congrArg some
  funext i
  cases i <;> rfl

-- Class (b): exact raw first-event readout on the extended execution.
noncomputable def eventAdvance (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (hist : H) (d : D) (act : A) (outcome : O) : Option Vector := do
  let before := initialRun m input ready hist
  let after := updateRun m input ready before d act outcome
  let old ← readVector (fun i => (observer m i).eval (target m input) before ())
  let next ← readVector (fun i => (observer m i).eval (target m input) after ())
  pure fun i => next i-old i

-- Class (b): values must be decoded from the SAME original actual event.
def OriginalReads (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (hist : H) (d : D) (act : A) (outcome : O)
    (before after : Vector) : Prop :=
  (∀ i, (originalObserver m i).eval (OwningHandoff.target m.base input.source)
    (ExecutionFrontier.initial m.base.frames.sourceFrame (OwningHandoff.target m.base input.source) ready.1 hist) ()=some (before i)) ∧
  (∀ i, (originalObserver m i).eval (OwningHandoff.target m.base input.source)
    (AcquisitionExecution.update m.base.frames.sourceFrame.acquisition (OwningHandoff.target m.base input.source) ready.1.1
      (ExecutionFrontier.initial m.base.frames.sourceFrame (OwningHandoff.target m.base input.source) ready.1 hist) d act outcome) ()=some (after i))

-- Class (b): the before/after bridge is proved from actual raw execution.
theorem actual_event_advance (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (hist : H) (d : D) (act : A) (outcome : O)
    (before after delta : Vector) (decoded : input.correction=some delta)
    (old : ∀ i, (originalObserver m i).eval (OwningHandoff.target m.base input.source)
      (ExecutionFrontier.initial m.base.frames.sourceFrame (OwningHandoff.target m.base input.source) ready.1 hist) ()=some (before i))
    (next : ∀ i, (originalObserver m i).eval (OwningHandoff.target m.base input.source)
      (AcquisitionExecution.update m.base.frames.sourceFrame.acquisition (OwningHandoff.target m.base input.source) ready.1.1
        (ExecutionFrontier.initial m.base.frames.sourceFrame (OwningHandoff.target m.base input.source) ready.1 hist) d act outcome) ()=some (after i)) :
    eventAdvance m input ready hist d act outcome=some (fun i => (after i-before i)+delta i) := by
  have beforeReads : ∀ i, (observer m i).eval (target m input) (initialRun m input ready hist) ()=some (before i) := by
    intro i
    rw [observer_read,initial_run_erasure,initial_run_offsets,old]
    simp [Rat.add_zero]
  have afterReads : ∀ i, (observer m i).eval (target m input)
      (updateRun m input ready (initialRun m input ready hist) d act outcome) ()=some (after i+delta i) := by
    intro i
    rw [observer_read,update_run_erasure,initial_run_erasure,update_run_offsets m input ready _ d act outcome delta decoded,
      initial_run_offsets,next]
    simp [Rat.zero_add]
  unfold eventAdvance
  dsimp only
  rw [read_vector_some _ before beforeReads,read_vector_some _ (fun i => after i+delta i) afterReads]
  apply congrArg some
  funext i
  simpa [Rat.add_zero] using realized_difference (before i) (after i) 0 (delta i)

variable [DecidableEq Resource] [DecidableEq P] [DecidableEq Q]
-- Class (b): inherited full F gate; its scope is the original raw projection.
def hardGate_F (m : Model) (input : Input SC SourceValue) : Prop :=
  FinalHandoff.HandoffPass_F m input.source
-- Class (b): inherited full O gate; its scope is the original raw projection.
def hardGate_O (m : Model) (input : Input SC SourceValue) : Prop :=
  FinalHandoff.HandoffPass_O m input.source
-- Class (b): every original partial source assignment and correction Option.
theorem hard_gate_iff_F (m : Model) (input : Input SC SourceValue) (delta : Option Vector) :
    hardGate_F m {input with correction := delta} ↔ hardGate_F m input := Iff.rfl
-- Class (b): every original partial source assignment and correction Option.
theorem hard_gate_iff_O (m : Model) (input : Input SC SourceValue) (delta : Option Vector) :
    hardGate_O m {input with correction := delta} ↔ hardGate_O m input := Iff.rfl

-- Class (b): actual rational operational box, with inherited original F gate.
theorem bounded_event_F (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (hist : H) (d : D) (act : A) (outcome : O)
    (before after delta radius : Vector) (decoded : input.correction=some delta)
    (reads : OriginalReads m input ready hist d act outcome before after)
    (margin : PositiveCertifiedMargin (fun i => after i-before i) radius)
    (box : WithinBox radius delta) (gate : FinalHandoff.HandoffPass_F m input.source) :
    eventAdvance m input ready hist d act outcome=some (fun i => (after i-before i)+delta i) ∧
      (∀ i, 0<(after i-before i)+delta i) ∧ hardGate_F m input :=
  ⟨actual_event_advance m input ready hist d act outcome before after delta decoded reads.1 reads.2,
    all_five_positive _ radius delta margin box,gate⟩

-- Class (b): actual rational operational box, with inherited original O gate.
theorem bounded_event_O (m : Model) (input : Input SC SourceValue)
    (ready : EventReady m input) (hist : H) (d : D) (act : A) (outcome : O)
    (before after delta radius : Vector) (decoded : input.correction=some delta)
    (reads : OriginalReads m input ready hist d act outcome before after)
    (margin : PositiveCertifiedMargin (fun i => after i-before i) radius)
    (box : WithinBox radius delta) (gate : FinalHandoff.HandoffPass_O m input.source) :
    eventAdvance m input ready hist d act outcome=some (fun i => (after i-before i)+delta i) ∧
      (∀ i, 0<(after i-before i)+delta i) ∧ hardGate_O m input :=
  ⟨actual_event_advance m input ready hist d act outcome before after delta decoded reads.1 reads.2,
    all_five_positive _ radius delta margin box,gate⟩

end CSTTT.RobustnessTheory.RawRationalMargin
