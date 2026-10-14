import CSTTT.Targets.GenericHandoff.RegisterInterpreter
import CSTTT.Transport.RawBridge

/-! Raw temporal component: interpreted registers, rows and eight readouts.
Every derived function is defined here. `Ready` is evidence about raw reads,
not an observer, dynamics, code or future verdict. Unbounded recipes are allowed;
there is no automatic finite-context lift. The closure is inductively generated
by the actual interpreted update. Readout laws cover every state in it.

This component has no acquisition protocol, package, or supplied entry set.
`roots` below is an INTERNAL interpretation argument; the enclosing RawHandoff
must derive it from acquisition execution. This is not yet that assembler. -/
namespace CSTTT.TargetTheory.GenericHandoff.RegisterFuture
open RegisterInterpreter CSTTT.TransportTheory

structure Readouts (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (P Residue Maintenance : Type) where
  predictive : Expr Cell Value R RV Unit P
  order : Expr Cell Value R RV Unit Nat
  ticks : Expr Cell Value R RV Unit Nat
  progress : Expr Cell Value R RV Unit Nat
  writer : Expr Cell Value R RV Unit Bool
  record : Expr Cell Value R RV Unit Nat
  residue : Expr Cell Value R RV Unit Residue
  maintenance : Expr Cell Value R RV Unit Maintenance
  owner : Expr Cell Value R RV Unit CarrierId

structure Raw (Cell : Type) (Value : Cell → Type) (R : Type) (RV : R → Type)
    (D A O P Residue Maintenance : Type) where
  outcomes : List O
  actions : List A
  disturbances : List D
  tickPeriod : Nat
  row : Expr Cell Value R RV (D × A) (List (O × Rat))
  program : Program Cell Value R RV (D × A × O)
  readouts : Readouts Cell Value R RV P Residue Maintenance

variable {Cell R D A O P Residue Maintenance : Type}
  {Value : Cell → Type} {RV : R → Type}

def Readouts.dependencies (r : Readouts Cell Value R RV P Residue Maintenance) :=
  r.predictive.dependencies ++ r.order.dependencies ++ r.ticks.dependencies ++
    r.progress.dependencies ++ r.writer.dependencies ++ r.record.dependencies ++
    r.residue.dependencies ++ r.maintenance.dependencies ++ r.owner.dependencies

def RawReady (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) : Prop :=
  Complete raw.row.dependencies a ∧ ProgramReady raw.program a ∧
    Complete raw.readouts.dependencies a

noncomputable def read (e : Expr Cell Value R RV Unit P) (a : Assignment Cell Value)
    (h : Complete e.dependencies a) (run : Registers R RV) : P :=
  Classical.choose (e.present_of_complete a h run ())

theorem read_eq (e : Expr Cell Value R RV Unit P) (a : Assignment Cell Value)
    (h : Complete e.dependencies a) (run : Registers R RV) :
    e.eval a run () = some (read e a h run) :=
  Classical.choose_spec (e.present_of_complete a h run ())

theorem read_proof_irrel (e : Expr Cell Value R RV Unit P) (a : Assignment Cell Value)
    (h k : Complete e.dependencies a) (run : Registers R RV) : read e a h run = read e a k run := rfl

theorem subready {L T : List Cell} {a : Assignment Cell Value}
    (h : Complete L a) (hT : T ⊆ L) : Complete T a := fun k hk => h k (hT hk)

noncomputable def observation (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (run : Registers R RV) :
    TemporalSnapshotReadout P Residue Maintenance := by
  have hr := h.2.2
  let r := raw.readouts
  have pred : Complete r.predictive.dependencies a := subready hr (by intro k hk; simpa only [Readouts.dependencies,List.mem_append] using (show k ∈ r.dependencies from by simp [Readouts.dependencies,hk]))
  have ord : Complete r.order.dependencies a := subready hr (by intro k hk; simpa only [Readouts.dependencies,List.mem_append] using (show k ∈ r.dependencies from by simp [Readouts.dependencies,hk]))
  have tick : Complete r.ticks.dependencies a := subready hr (by intro k hk; simpa only [Readouts.dependencies,List.mem_append] using (show k ∈ r.dependencies from by simp [Readouts.dependencies,hk]))
  have progress : Complete r.progress.dependencies a := subready hr (by intro k hk; simpa only [Readouts.dependencies,List.mem_append] using (show k ∈ r.dependencies from by simp [Readouts.dependencies,hk]))
  have record : Complete r.record.dependencies a := subready hr (by intro k hk; simpa only [Readouts.dependencies,List.mem_append] using (show k ∈ r.dependencies from by simp [Readouts.dependencies,hk]))
  have residue : Complete r.residue.dependencies a := subready hr (by intro k hk; simpa only [Readouts.dependencies,List.mem_append] using (show k ∈ r.dependencies from by simp [Readouts.dependencies,hk]))
  have maintenance : Complete r.maintenance.dependencies a := subready hr (by intro k hk; simpa only [Readouts.dependencies,List.mem_append] using (show k ∈ r.dependencies from by simp [Readouts.dependencies,hk]))
  have owner : Complete r.owner.dependencies a := subready hr (by intro k hk; simpa only [Readouts.dependencies,List.mem_append] using (show k ∈ r.dependencies from by simp [Readouts.dependencies,hk]))
  exact ⟨read r.predictive a pred run,read r.order a ord run,
    read r.ticks a tick run % raw.tickPeriod,read r.progress a progress run,
    read r.record a record run,read r.residue a residue run,
    read r.maintenance a maintenance run,read r.owner a owner run⟩

noncomputable def row (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (run : Registers R RV) (da : D × A) :
    List (O × Rat) := Classical.choose (raw.row.present_of_complete a h.1 run da)

theorem row_eq (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (run : Registers R RV) (da : D × A) :
    raw.row.eval a run da = some (row raw a h run da) :=
  Classical.choose_spec (raw.row.present_of_complete a h.1 run da)

noncomputable def next (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (run : Registers R RV) (da : D × A) (o : O) :
    Registers R RV := checkedExecute raw.program a h.2.1 run (da.1,da.2,o)

variable [DecidableEq O]
/-- Duplicate raw destinations are summed, not discarded or replaced by a
predictive representative. Each actual outcome remains a register input. -/
noncomputable def weight (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (run : Registers R RV) (da : D × A) (o : O) : Rat :=
  ((row raw a h run da).map fun e => if e.1 = o then e.2 else 0).sum

noncomputable def future (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) :
    FullFutureModel (Registers R RV) (D × A) O (TemporalRunCode P Residue Maintenance)
      (TemporalSnapshotReadout P Residue Maintenance) :=
  ⟨raw.outcomes,(fun run => bridgeCodeOfObservation (observation raw a h run)),
   observation raw a h,weight raw a h,next raw a h⟩

noncomputable def dynamics (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) : RawFutureDynamics (Registers R RV) (D × A) O :=
  ⟨raw.outcomes,weight raw a h,next raw a h⟩
abbrev Closure (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (roots : List (Registers R RV)) :=
  FutureClosure (dynamics raw a h) roots

theorem owned_dynamics (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (roots : List (Registers R RV)) :
    FutureDynamicsCheck (future raw a h) (dynamics raw a h) roots :=
  ⟨rfl,fun _ _ _ _ => ⟨rfl,rfl⟩⟩

variable [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance]
/-- Bisimulation is an equation on the interpreted raw instructions, not a
supplied future/observer. The theorem retains the ALL-state quantifier. -/
def Bisimulation (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) : Prop :=
  FullOneStepBisim (future raw a h)

theorem all_words (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (hb : Bisimulation raw a h) :
    FullFutureSufficient (future raw a h) := full_future_sufficient_of_bisim _ hb

omit [DecidableEq O] [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance] in
theorem missing_row_rejected (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.row.dependencies) (hm : a k = none) :
    ¬ RawReady raw a := by
  intro h
  have hp := h.1 k hk
  rw [hm] at hp
  contradiction

omit [DecidableEq O] [DecidableEq P] [DecidableEq Residue] [DecidableEq Maintenance] in
theorem missing_readout_rejected (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.readouts.dependencies) (hm : a k = none) :
    ¬ RawReady raw a := by
  intro h
  have hp := h.2.2 k hk
  rw [hm] at hp
  contradiction

end CSTTT.TargetTheory.GenericHandoff.RegisterFuture
