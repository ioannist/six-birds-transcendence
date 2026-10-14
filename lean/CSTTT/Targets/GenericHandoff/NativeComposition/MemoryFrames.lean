import CSTTT.Targets.GenericHandoff.NativeComposition.Simulation
import CSTTT.Targets.GenericHandoff.NativeComposition.SourceMemory
import CSTTT.Targets.GenericHandoff.FutureCellReindex

/-! Both retrospective temporal frames read the actual source copy or current
publication in the shared memory namespace. All interpreter equations quantify
over every partial assignment and every unbounded register state. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.MemoryFrames
open RegisterInterpreter

def selectInput (source : Bool) (p : Input × Input) : Input := if source then p.2 else p.1
def inputs (source : Bool) (a : Assignment Owner MemoryValue) : Assignment Owner Value :=
  fun o => (a o).map (selectInput source)
abbrev raw (cell : Owner) (source : Bool) (owner : Owner) (names : Owner → CarrierId) :
    RegisterFuture.Raw Owner MemoryValue Unit (fun _ => Frame.State) Unit Bool Factor Frame.Predictive Frame.Residue Bool :=
  FutureCellReindex.raw (SV := Value) (TV := MemoryValue) id (fun (_ : Owner) (p : Input × Input) => selectInput source p) (Frame.raw cell false owner names)

def bindings (cell : Owner) (source : Bool) :
    TemporalFactorCells.Bindings Owner MemoryValue Factor Bool Factor History Route Stage Bool Owner :=
  let get : (Input × Input) → FactorData := fun p => (selectInput source p).temporal
  ⟨⟨cell,fun p => (get p).rows⟩,⟨cell,fun p => (get p).positions⟩,
    ⟨cell,fun p => (get p).hazards⟩,⟨cell,fun p => (get p).policy⟩,
    ⟨cell,fun p => (get p).classes⟩,⟨cell,fun p => (get p).publishedP⟩,
    ⟨cell,fun p => (get p).ticks⟩,⟨cell,fun p => (get p).resource⟩,
    ⟨cell,fun p => (get p).ledger⟩,⟨cell,fun p => (get p).interface⟩,
    ⟨cell,fun p => (get p).histories⟩,⟨cell,fun p => (get p).events⟩,
    ⟨cell,fun p => (get p).realized⟩,⟨cell,fun p => (get p).receiverFunded⟩,
    ⟨cell,fun p => (get p).routes⟩,⟨cell,fun p => (get p).writers⟩⟩

theorem decoded (cell : Owner) (source : Bool) (a : Assignment Owner MemoryValue) :
    TemporalFactorCells.decoded (bindings cell source) a =
      (a cell).map (fun p => (selectInput source p).temporal) := by
  cases ha : a cell <;> simp [bindings,TemporalFactorCells.decoded,CellView.read,ha]

theorem ready (cell : Owner) (source : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (ha : (a cell).isSome=true) :
    RegisterFuture.RawReady (raw cell source owner names) a := by
  apply (FutureCellReindex.ready_iff (SV := Value) (TV := MemoryValue) id (fun (_ : Owner) (p : Input × Input) => selectInput source p) (Frame.raw cell false owner names) a).mpr
  apply Frame.ready cell false owner names _
  simpa [CellReindex.pullback] using ha

theorem ready_iff (cell : Owner) (source : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) :
    RegisterFuture.RawReady (raw cell source owner names) a ↔ (a cell).isSome=true := by
  constructor
  · intro h
    have hp := h.1 cell
    apply hp
    simp only [raw,FutureCellReindex.raw,CellReindex.dependencies]
    simp [Frame.raw,Frame.rowExpr,Frame.pairExpr,Frame.dataExpr,Expr.dependencies,Expr.reenv_dependencies]
  · exact ready cell source owner names a

theorem next (cell : Owner) (source : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : RegisterFuture.RawReady (raw cell source owner names) a)
    (p : Input × Input) (hp : a cell=some p) (x : Frame.Registers) (da : Unit × Bool) (o : Factor) :
    RegisterFuture.next (raw cell source owner names) a h x da o =
      Frame.pack (TemporalFactorRules.update (factorSchema owner) (selectInput source p).temporal (x ()) da.2 o) := by
  have j := (FutureCellReindex.ready_iff (SV := Value) (TV := MemoryValue) id (fun (_ : Owner) (p : Input × Input) => selectInput source p) (Frame.raw cell false owner names) a).mp h
  rw [FutureCellReindex.next_equation (SV := Value) (TV := MemoryValue) id (fun (_ : Owner) (p : Input × Input) => selectInput source p) (Frame.raw cell false owner names) a h j]
  exact Frame.next_equation cell false owner names _ j (selectInput source p)
    (by change (a cell).map (selectInput source)=some _; rw [hp]; rfl) x da o

theorem row (cell : Owner) (source : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : RegisterFuture.RawReady (raw cell source owner names) a)
    (p : Input × Input) (hp : a cell=some p) (x : Frame.Registers) (da : Unit × Bool) :
    RegisterFuture.row (raw cell source owner names) a h x da =
      TemporalFactorRules.actualRows (factorSchema owner) (selectInput source p).temporal (x ()) da.2 := by
  have j := (FutureCellReindex.ready_iff (SV := Value) (TV := MemoryValue) id (fun (_ : Owner) (p : Input × Input) => selectInput source p) (Frame.raw cell false owner names) a).mp h
  rw [FutureCellReindex.row_equation (SV := Value) (TV := MemoryValue) id (fun (_ : Owner) (p : Input × Input) => selectInput source p) (Frame.raw cell false owner names) a h j]
  exact Frame.row_equation cell false owner names _ j (selectInput source p)
    (by change (a cell).map (selectInput source)=some _; rw [hp]; rfl) x da

theorem observation (cell : Owner) (source : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner MemoryValue) (h : RegisterFuture.RawReady (raw cell source owner names) a)
    (p : Input × Input) (hp : a cell=some p) (x : Frame.Registers) :
    RegisterFuture.observation (raw cell source owner names) a h x =
      TemporalRuntimeCoherence.observationImage names
        (TemporalFactorRules.observe (factorSchema owner) (selectInput source p).temporal 2 (x ())) := by
  have j := (FutureCellReindex.ready_iff (SV := Value) (TV := MemoryValue) id (fun (_ : Owner) (p : Input × Input) => selectInput source p) (Frame.raw cell false owner names) a).mp h
  rw [FutureCellReindex.observation_equation (SV := Value) (TV := MemoryValue) id (fun (_ : Owner) (p : Input × Input) => selectInput source p) (Frame.raw cell false owner names) a h j]
  exact Frame.observation_equation cell false owner names _ j (selectInput source p)
    (by change (a cell).map (selectInput source)=some _; rw [hp]; rfl) x

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.MemoryFrames
