import CSTTT.Robustness.ExactFiveMargins
import CSTTT.Targets.GenericHandoff.RegisterInitialization

/-! Raw rational-register and correction-cell lift (b). Initializers, programs,
and observers are interpreted instructions. Erasure retains the complete old
run; fractional advances belong to the extended observer carrier. -/
namespace CSTTT.RobustnessTheory.RationalRegisters
open CSTTT.TargetTheory.GenericHandoff RegisterInterpreter
open ExactFiveMargins
-- Class (b): new construction or derived law.
inductive LiftRegister (R : Type) where
  | base (r : R) | offset (i : Coordinate)
-- Class (b): new construction or derived law.
def LiftValue {R : Type} (RV : R → Type) : LiftRegister R → Type
  | .base r => RV r
  | .offset _ => Rat
variable {Cell R Env X : Type} {Value : Cell → Type} {RV : R → Type}
-- Class (b): new construction or derived law.
abbrev LiftRun := Registers (LiftRegister R) (LiftValue RV)
-- Class (b): new construction or derived law.
def erase (run : @LiftRun R RV) : Registers R RV := fun r => run (.base r)
-- Class (b): new construction or derived law.
def offsets (run : @LiftRun R RV) : Vector := fun i => run (.offset i)
-- Class (b): new construction or derived law.
def pack (run : Registers R RV) (offset : Vector) : @LiftRun R RV
  | .base r => run r
  | .offset i => offset i

-- Class (b): new construction or derived law.
def liftExpr {X : Type} (e : Expr Cell Value R RV Env X) : Expr Cell Value (LiftRegister R) (LiftValue RV) Env X :=
  match e with
  | .literal v => .literal v
  | .cell k => .cell k
  | .register r => (.register (LiftRegister.base r) : Expr Cell Value (LiftRegister R) (LiftValue RV) Env (RV r))
  | .environment f => .environment f
  | .map f arg => .map f (liftExpr arg)
  | .pair x y => .pair (liftExpr x) (liftExpr y)
  | .choose c x y => .choose (liftExpr c) (liftExpr x) (liftExpr y)

-- Class (b): new construction or derived law.
theorem lift_eval (e : Expr Cell Value R RV Env X) (a : Assignment Cell Value)
    (run : @LiftRun R RV) (env : Env) :
    (liftExpr e).eval a run env=e.eval a (erase run) env := by
  induction e <;> simp_all [liftExpr,Expr.eval,erase]

-- Class (b): new construction or derived law.
theorem lift_dependencies (e : Expr Cell Value R RV Env X) :
    (liftExpr e).dependencies=e.dependencies := by
  induction e <;> simp_all [liftExpr,Expr.dependencies]

-- Class (b): new construction or derived law.
def liftProgram (p : Program Cell Value R RV Env)
    (correction : Expr Cell Value R RV Env Vector) :
    Program Cell Value (LiftRegister R) (LiftValue RV) Env
  | .base r => liftExpr (p r)
  | .offset i => .map (fun v : Rat × Vector => v.1+v.2 i)
      (.pair (.register (LiftRegister.offset (R:=R) i) : Expr Cell Value (LiftRegister R) (LiftValue RV) Env Rat) (liftExpr correction))

-- Class (b): new construction or derived law.
theorem ready_iff (p : Program Cell Value R RV Env)
    (correction : Expr Cell Value R RV Env Vector) (a : Assignment Cell Value) :
    ProgramReady (liftProgram p correction) a ↔
      ProgramReady p a ∧ Complete correction.dependencies a := by
  constructor
  · intro ready
    refine ⟨fun r => ?_,?_⟩
    · simpa [liftProgram,lift_dependencies] using ready (.base r)
    · simpa [liftProgram,Expr.dependencies,lift_dependencies] using ready (.offset .order)
  · rintro ⟨program,correction⟩ reg
    cases reg with
    | base r => simpa [liftProgram,lift_dependencies] using program r
    | offset i => simpa [liftProgram,Expr.dependencies,lift_dependencies] using correction

-- Class (b): new construction or derived law.
theorem actual_update_erases (p : Program Cell Value R RV Env)
    (correction : Expr Cell Value R RV Env Vector) (a : Assignment Cell Value)
    (ready : ProgramReady (liftProgram p correction) a) (run : @LiftRun R RV) (env : Env) :
    erase (checkedExecute (liftProgram p correction) a ready run env)=
      checkedExecute p a ((ready_iff p correction a).mp ready).1 (erase run) env := by
  funext r
  apply Option.some.inj
  have old := checked_execute_eq p a ((ready_iff p correction a).mp ready).1 (erase run) env r
  have new := checked_execute_eq (liftProgram p correction) a ready run env (.base r)
  change (liftExpr (p r)).eval a run env=some _ at new
  rw [lift_eval] at new
  exact new.symm.trans old

-- Class (b): new construction or derived law.
theorem actual_offset_update (p : Program Cell Value R RV Env)
    (correction : Expr Cell Value R RV Env Vector) (a : Assignment Cell Value)
    (ready : ProgramReady (liftProgram p correction) a) (run : @LiftRun R RV) (env : Env)
    (delta : Vector) (decoded : correction.eval a (erase run) env=some delta) :
    offsets (checkedExecute (liftProgram p correction) a ready run env)=
      fun i => offsets run i+delta i := by
  funext i
  apply Option.some.inj
  have update := checked_execute_eq (liftProgram p correction) a ready run env (.offset i)
  change _=some (offsets (checkedExecute (liftProgram p correction) a ready run env) i) at update
  simp only [execute,liftProgram,Expr.eval,lift_eval,decoded,offsets] at update
  exact update.symm

-- Class (b): new construction or derived law.
def liftedNumeric (e : Expr Cell Value R RV Env Rat) (i : Coordinate) :
    Expr Cell Value (LiftRegister R) (LiftValue RV) Env Rat :=
  .map (fun p : Rat × Rat => p.1+p.2) (.pair (liftExpr e) (.register (LiftRegister.offset (R:=R) i) : Expr Cell Value (LiftRegister R) (LiftValue RV) Env Rat))

-- Class (b): new construction or derived law.
theorem actual_numeric_read (e : Expr Cell Value R RV Env Rat) (i : Coordinate)
    (a : Assignment Cell Value) (run : @LiftRun R RV) (env : Env) :
    (liftedNumeric e i).eval a run env=
      (e.eval a (erase run) env).map (fun v => v+offsets run i) := by
  simp only [liftedNumeric,Expr.eval,lift_eval]
  cases e.eval a (erase run) env <;> rfl

-- Class (b): new construction or derived law.
theorem realized_advance (p : Program Cell Value R RV Env)
    (correction : Expr Cell Value R RV Env Vector)
    (e : Expr Cell Value R RV Env Rat) (i : Coordinate)
    (a : Assignment Cell Value) (ready : ProgramReady (liftProgram p correction) a)
    (run : @LiftRun R RV) (env : Env) (delta : Vector) (before after : Rat)
    (decoded : correction.eval a (erase run) env=some delta)
    (old : e.eval a (erase run) env=some before)
    (next : e.eval a (checkedExecute p a ((ready_iff p correction a).mp ready).1 (erase run) env) env=some after) :
    (liftedNumeric e i).eval a run env=some (before+offsets run i) ∧
    (liftedNumeric e i).eval a (checkedExecute (liftProgram p correction) a ready run env) env=
      some (after+offsets run i+delta i) := by
  constructor
  · simp [actual_numeric_read,old]
  · rw [actual_numeric_read,actual_update_erases,actual_offset_update p correction a ready run env delta decoded,next]
    simp [Rat.add_assoc]

-- Class (b): new construction or derived law.
theorem realized_difference (before after offset delta : Rat) :
    (after+offset+delta)-(before+offset)=(after-before)+delta := by
  apply Rat.add_right_cancel (before+offset)
  calc
    ((after+offset+delta)-(before+offset))+(before+offset) = after+offset+delta := by
      simp [Rat.sub_eq_add_neg,Rat.add_assoc,Rat.neg_add_cancel,Rat.add_zero]
    _ = ((after-before)+delta)+(before+offset) := by
      rw [Rat.sub_eq_add_neg]
      calc
        after+offset+delta = (after+(delta+offset))+(-before+before) := by
          rw [Rat.neg_add_cancel,Rat.add_zero]
          simp only [Rat.add_comm,Rat.add_left_comm]
        _ = ((after + -before)+delta)+(before+offset) := by simp only [Rat.add_comm,Rat.add_left_comm,Rat.add_assoc]

-- Class (b): new construction or derived law.
theorem missing_correction_rejects (p : Program Cell Value R RV Env)
    (correction : Expr Cell Value R RV Env Vector) (a : Assignment Cell Value)
    (k : Cell) (consumed : k∈correction.dependencies) (missing : a k=none) :
    ¬ ProgramReady (liftProgram p correction) a := by
  intro ready
  have present := ((ready_iff p correction a).mp ready).2 k consumed
  rw [missing] at present
  contradiction

-- Class (b): new construction or derived law.
theorem missing_correction_actual_output (p : Program Cell Value R RV Env)
    (correction : Expr Cell Value R RV Env Vector) (a : Assignment Cell Value)
    (run : @LiftRun R RV) (env : Env)
    (missing : correction.eval a (erase run) env=none) (i : Coordinate) :
    execute (liftProgram p correction) a run env (.offset i)=none := by
  simp [execute,liftProgram,Expr.eval,lift_eval,missing]

-- An explicit exact quarter correction cannot be a natural-valued original
-- order readout after the old zero-counter initial state.
-- Class (b): new construction or derived law.
theorem quarter_not_original_nat_readout (n : Nat) : (n : Rat)≠(5/4 : Rat) := by
  intro equal
  have denominator := congrArg Rat.den equal
  have fourth : (5/4 : Rat).den=4 := by decide +kernel
  rw [Rat.den_natCast,fourth] at denominator
  contradiction

open RegisterInitialization

-- Class (b): new construction or derived law.
def liftInitializer (p : InitialProgram Cell Value R RV Env) :
    InitialProgram Cell Value (LiftRegister R) (LiftValue RV) Env
  | .base r => p r
  | .offset _ => .literal (0 : Rat)

-- Class (b): new construction or derived law.
theorem initial_ready_iff (p : InitialProgram Cell Value R RV Env) (a : Assignment Cell Value) :
    Ready (liftInitializer p) a ↔ Ready p a := by
  constructor
  · intro ready r
    exact ready (.base r)
  · intro ready reg
    cases reg with
    | base r => exact ready r
    | offset i => simp [liftInitializer,Expr.dependencies,Complete]

-- Class (b): new construction or derived law.
theorem actual_initial_erases (p : InitialProgram Cell Value R RV Env) (a : Assignment Cell Value)
    (ready : Ready (liftInitializer p) a) (env : Env) :
    erase (initial (liftInitializer p) a ready env)=
      initial p a ((initial_ready_iff p a).mp ready) env := by
  funext r
  apply Option.some.inj
  exact (initial_eq (liftInitializer p) a ready env (.base r)).symm.trans
    (initial_eq p a ((initial_ready_iff p a).mp ready) env r)

-- Class (b): new construction or derived law.
theorem actual_initial_offsets (p : InitialProgram Cell Value R RV Env) (a : Assignment Cell Value)
    (ready : Ready (liftInitializer p) a) (env : Env) :
    offsets (initial (liftInitializer p) a ready env)=fun _ => 0 := by
  funext i
  apply Option.some.inj
  exact (initial_eq (liftInitializer p) a ready env (.offset i)).symm

-- Class (b): new construction or derived law.
theorem quarter_not_original_nat_difference (a b : Nat) :
    (b : Rat)-(a : Rat)≠(5/4 : Rat) := by
  intro equal
  have cast : (b : Rat)-(a : Rat)=((Int.ofNat b-Int.ofNat a : Int) : Rat) := by
    rw [Rat.intCast_sub]
    rfl
  rw [cast] at equal
  have denominator := congrArg Rat.den equal
  have fourth : (5/4 : Rat).den=4 := by decide +kernel
  rw [Rat.den_intCast,fourth] at denominator
  contradiction

-- Class (b): new construction or derived law.
inductive ExtendedCell (Cell : Type) where
  | base (k : Cell) | correction
  deriving DecidableEq

-- Class (b): new construction or derived law.
def ExtendedValue {Cell : Type} (Value : Cell → Type) : ExtendedCell Cell → Type
  | .base k => Value k
  | .correction => Vector

-- Class (b): new construction or derived law.
def projectAssignment (a : Assignment (ExtendedCell Cell) (ExtendedValue Value)) :
    Assignment Cell Value := fun k => a (.base k)

-- Class (b): new construction or derived law.
def extendAssignment (a : Assignment Cell Value) (delta : Option Vector) :
    Assignment (ExtendedCell Cell) (ExtendedValue Value)
  | .base k => a k
  | .correction => delta

-- Class (b): new construction or derived law.
def embedCells {X : Type} (e : Expr Cell Value R RV Env X) :
    Expr (ExtendedCell Cell) (ExtendedValue Value) R RV Env X :=
  match e with
  | .literal v => .literal v
  | .cell k => (.cell (ExtendedCell.base k) : Expr (ExtendedCell Cell) (ExtendedValue Value) R RV Env (Value k))
  | .register r => .register r
  | .environment f => .environment f
  | .map f arg => .map f (embedCells arg)
  | .pair x y => .pair (embedCells x) (embedCells y)
  | .choose c x y => .choose (embedCells c) (embedCells x) (embedCells y)

-- Class (b): new construction or derived law.
theorem embed_eval (e : Expr Cell Value R RV Env X)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value)) (run : Registers R RV) (env : Env) :
    (embedCells e).eval a run env=e.eval (projectAssignment a) run env := by
  induction e <;> simp_all [embedCells,Expr.eval,projectAssignment]

-- Class (b): new construction or derived law.
theorem embed_dependencies (e : Expr Cell Value R RV Env X) :
    (embedCells e).dependencies=e.dependencies.map ExtendedCell.base := by
  induction e <;> simp_all [embedCells,Expr.dependencies,List.map_append]

-- Class (b): new construction or derived law.
theorem embedded_complete_iff (e : Expr Cell Value R RV Env X)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value)) :
    Complete (embedCells e).dependencies a ↔ Complete e.dependencies (projectAssignment a) := by
  simp [Complete,embed_dependencies,projectAssignment]

-- Class (b): new construction or derived law.
def correctedProgram (p : Program Cell Value R RV Env) :
    Program (ExtendedCell Cell) (ExtendedValue Value) (LiftRegister R) (LiftValue RV) Env :=
  liftProgram (fun r => embedCells (p r))
    (.cell (ExtendedCell.correction : ExtendedCell Cell))

-- Class (b): new construction or derived law.
theorem corrected_ready_iff (p : Program Cell Value R RV Env)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value)) :
    ProgramReady (correctedProgram p) a ↔
      ProgramReady p (projectAssignment a) ∧ a .correction≠none := by
  rw [correctedProgram,ready_iff]
  have program : ProgramReady (fun r => embedCells (p r)) a ↔ ProgramReady p (projectAssignment a) := by
    unfold ProgramReady
    simp only [embedded_complete_iff]
  rw [program]
  cases h : a ExtendedCell.correction <;> simp [Expr.dependencies,Complete,h]

-- Class (b): new construction or derived law.
theorem absent_raw_correction_rejects (p : Program Cell Value R RV Env)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value)) (missing : a .correction=none) :
    ¬ ProgramReady (correctedProgram p) a := by
  rw [corrected_ready_iff]
  simp [missing]

-- Class (b): new construction or derived law.
theorem project_extend (a : Assignment Cell Value) (delta : Option Vector) :
    projectAssignment (extendAssignment a delta)=a := rfl

-- Class (b): new construction or derived law.
theorem embedded_program_ready (p : Program Cell Value R RV Env)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value)) :
    ProgramReady (fun r => embedCells (p r)) a ↔ ProgramReady p (projectAssignment a) := by
  unfold ProgramReady
  simp only [embedded_complete_iff]

-- Class (b): new construction or derived law.
theorem embedded_execute (p : Program Cell Value R RV Env)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value))
    (ready : ProgramReady (fun r => embedCells (p r)) a) (run : Registers R RV) (env : Env) :
    checkedExecute (fun r => embedCells (p r)) a ready run env=
      checkedExecute p (projectAssignment a) ((embedded_program_ready p a).mp ready) run env := by
  funext r
  apply Option.some.inj
  have new := checked_execute_eq (fun r => embedCells (p r)) a ready run env r
  rw [execute,embed_eval] at new
  exact new.symm.trans (checked_execute_eq p (projectAssignment a)
    ((embedded_program_ready p a).mp ready) run env r)

-- Class (b): new construction or derived law.
theorem corrected_update_erases (p : Program Cell Value R RV Env)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value))
    (ready : ProgramReady (correctedProgram p) a) (run : @LiftRun R RV) (env : Env) :
    erase (checkedExecute (correctedProgram p) a ready run env)=
      checkedExecute p (projectAssignment a) ((corrected_ready_iff p a).mp ready).1 (erase run) env := by
  unfold correctedProgram at ready ⊢
  rw [actual_update_erases,embedded_execute]

-- Class (b): new construction or derived law.
theorem corrected_offset_update (p : Program Cell Value R RV Env)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value))
    (ready : ProgramReady (correctedProgram p) a) (run : @LiftRun R RV) (env : Env)
    (delta : Vector) (decoded : a .correction=some delta) :
    offsets (checkedExecute (correctedProgram p) a ready run env)=
      fun i => offsets run i+delta i :=
  actual_offset_update _ _ a ready run env delta decoded

-- Class (b): new construction or derived law.
def correctedInitializer (p : InitialProgram Cell Value R RV Env) :
    InitialProgram (ExtendedCell Cell) (ExtendedValue Value) (LiftRegister R) (LiftValue RV) Env :=
  liftInitializer (fun r => embedCells (p r))

-- Class (b): new construction or derived law.
theorem corrected_initial_ready_iff (p : InitialProgram Cell Value R RV Env)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value)) :
    Ready (correctedInitializer p) a ↔ Ready p (projectAssignment a) := by
  rw [correctedInitializer,initial_ready_iff]
  unfold Ready
  simp only [embedded_complete_iff]

-- Class (b): new construction or derived law.
theorem corrected_initial_erases (p : InitialProgram Cell Value R RV Env)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value))
    (ready : Ready (correctedInitializer p) a) (env : Env) :
    erase (initial (correctedInitializer p) a ready env)=
      initial p (projectAssignment a) ((corrected_initial_ready_iff p a).mp ready) env := by
  funext r
  apply Option.some.inj
  have new := initial_eq (correctedInitializer p) a ready env (.base r)
  change (embedCells (p r)).eval a noRegisters env=some _ at new
  rw [embed_eval] at new
  exact new.symm.trans (initial_eq p (projectAssignment a)
    ((corrected_initial_ready_iff p a).mp ready) env r)

-- Class (b): new construction or derived law.
theorem corrected_initial_offsets (p : InitialProgram Cell Value R RV Env)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value))
    (ready : Ready (correctedInitializer p) a) (env : Env) :
    offsets (initial (correctedInitializer p) a ready env)=fun _ => 0 :=
  actual_initial_offsets _ a ready env

-- Class (b): new construction or derived law.
def correctedNumeric (e : Expr Cell Value R RV Env Rat) (i : Coordinate) :
    Expr (ExtendedCell Cell) (ExtendedValue Value) (LiftRegister R) (LiftValue RV) Env Rat :=
  liftedNumeric (embedCells e) i

-- Class (b): new construction or derived law.
theorem corrected_numeric_read (e : Expr Cell Value R RV Env Rat) (i : Coordinate)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value)) (run : @LiftRun R RV) (env : Env) :
    (correctedNumeric e i).eval a run env=
      (e.eval (projectAssignment a) (erase run) env).map (fun v => v+offsets run i) := by
  rw [correctedNumeric,actual_numeric_read,embed_eval]

-- Class (b): new construction or derived law.
theorem corrected_rows_read {O : Type} (e : Expr Cell Value R RV Env (List (O × Rat)))
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value)) (run : @LiftRun R RV) (env : Env) :
    (liftExpr (embedCells e)).eval a run env=e.eval (projectAssignment a) (erase run) env := by
  rw [lift_eval,embed_eval]

-- Class (b): new construction or derived law.
theorem corrected_raw_offset_missing (p : Program Cell Value R RV Env)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value)) (run : @LiftRun R RV) (env : Env)
    (missing : a .correction=none) (i : Coordinate) :
    execute (correctedProgram p) a run env (.offset i)=none :=
  missing_correction_actual_output (fun r => embedCells (p r))
    (.cell (ExtendedCell.correction : ExtendedCell Cell)) a run env missing i

-- Class (b): new construction or derived law.
theorem corrected_event_difference (p : Program Cell Value R RV Env)
    (observers : Coordinate → Expr Cell Value R RV Unit Rat)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value))
    (ready : ProgramReady (correctedProgram p) a) (run : @LiftRun R RV) (env : Env)
    (delta before after : Vector) (decoded : a .correction=some delta)
    (old : ∀ i, (observers i).eval (projectAssignment a) (erase run) ()=some (before i))
    (next : ∀ i, (observers i).eval (projectAssignment a)
      (checkedExecute p (projectAssignment a) ((corrected_ready_iff p a).mp ready).1 (erase run) env) ()=some (after i)) :
    ∀ i, (correctedNumeric (observers i) i).eval a run ()=some (before i+offsets run i) ∧
      (correctedNumeric (observers i) i).eval a
        (checkedExecute (correctedProgram p) a ready run env) ()=
        some (after i+offsets run i+delta i) ∧
      (after i+offsets run i+delta i)-(before i+offsets run i)=(after i-before i)+delta i := by
  intro i
  refine ⟨?_,?_,realized_difference _ _ _ _⟩
  · rw [corrected_numeric_read,old]
    rfl
  · rw [corrected_numeric_read,corrected_update_erases,corrected_offset_update p a ready run env delta decoded,next]
    simp [Rat.add_assoc]

-- Class (b): new construction or derived law.
theorem corrected_all_five_positive (p : Program Cell Value R RV Env)
    (observers : Coordinate → Expr Cell Value R RV Unit Rat)
    (a : Assignment (ExtendedCell Cell) (ExtendedValue Value))
    (ready : ProgramReady (correctedProgram p) a) (run : @LiftRun R RV) (env : Env)
    (delta before after radius : Vector) (decoded : a .correction=some delta)
    (old : ∀ i, (observers i).eval (projectAssignment a) (erase run) ()=some (before i))
    (next : ∀ i, (observers i).eval (projectAssignment a)
      (checkedExecute p (projectAssignment a) ((corrected_ready_iff p a).mp ready).1 (erase run) env) ()=some (after i))
    (margin : PositiveCertifiedMargin (fun i => after i-before i) radius)
    (box : WithinBox radius delta) :
    ∀ i, ∃ actualBefore actualAfter : Rat,
      (correctedNumeric (observers i) i).eval a run ()=some actualBefore ∧
      (correctedNumeric (observers i) i).eval a
        (checkedExecute (correctedProgram p) a ready run env) ()=some actualAfter ∧
      0<actualAfter-actualBefore := by
  intro i
  have reads := corrected_event_difference p observers a ready run env delta before after decoded old next i
  exact ⟨_,_,reads.1,reads.2.1,reads.2.2 ▸ all_five_positive _ radius delta margin box i⟩





end CSTTT.RobustnessTheory.RationalRegisters
