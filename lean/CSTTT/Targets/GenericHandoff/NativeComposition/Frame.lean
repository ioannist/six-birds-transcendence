import CSTTT.Targets.GenericHandoff.NativeComposition.Inputs
import CSTTT.Targets.GenericHandoff.TemporalRuntimeCoherence

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.Frame
open RegisterInterpreter
abbrev State := TemporalFactorRules.Run Factor Factor Bool
abbrev Registers := RegisterInterpreter.Registers Unit (fun _ => State)
abbrev Predictive := TemporalFactorRules.Predictive Factor
abbrev Residue := List Factor × List Bool
abbrev Data := FactorData

def pack (s : State) : Registers := fun _ => s
def dataExpr (cell : Owner) (inverse : Bool) : Expr Owner Value Unit (fun _ => State) Unit Data :=
  .map (fun i => (if inverse then restore i else i).temporal) (.cell cell)
def pairExpr (cell : Owner) (inverse : Bool) :
    Expr Owner Value Unit (fun _ => State) Unit (Data × State) :=
  .pair (dataExpr cell inverse) (.register ())
def table {X : Type} (cell : Owner) (inverse : Bool) (f : Data × State → X) :
    Expr Owner Value Unit (fun _ => State) Unit X := .map f (pairExpr cell inverse)

def rowExpr (cell : Owner) (inverse : Bool) (owner : Owner) :
    Expr Owner Value Unit (fun _ => State) (Unit × Bool) (List (Factor × Rat)) :=
  .map (fun p => TemporalFactorRules.actualRows (factorSchema owner) p.1.1 p.1.2 p.2.2)
    (.pair ((pairExpr cell inverse).reenv (fun _ => ())) (.environment id))
def updateExpr (cell : Owner) (inverse : Bool) (owner : Owner) :
    Expr Owner Value Unit (fun _ => State) (Unit × Bool × Factor) State :=
  .map (fun p => TemporalFactorRules.update (factorSchema owner) p.1.1 p.1.2 p.2.2.1 p.2.2.2)
    (.pair ((pairExpr cell inverse).reenv (fun _ => ())) (.environment id))

def readouts (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId) :
    RegisterFuture.Readouts Owner Value Unit (fun _ => State) Predictive Residue Bool where
  predictive := table cell inverse (fun p => TemporalFactorRules.prediction (factorSchema owner) p.1 p.2.factor)
  order := table cell inverse (fun p => p.2.counter)
  ticks := table cell inverse (fun p => p.2.ticks)
  progress := table cell inverse (fun p => p.2.counter)
  writer := table cell inverse (fun p => TemporalFactorRules.writer (factorSchema owner) p.1 p.2.residue)
  record := table cell inverse (fun p => if p.2.funded && TemporalFactorRules.writer (factorSchema owner) p.1 p.2.residue then p.2.counter else 0)
  residue := table cell inverse (fun p => p.2.residue)
  maintenance := table cell inverse (fun p => p.2.funded)
  owner := table cell inverse (fun p => names p.1.resource.owner)

def raw (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId) :
    RegisterFuture.Raw Owner Value Unit (fun _ => State) Unit Bool Factor Predictive Residue Bool :=
  ⟨factors,[false,true],[()],2,rowExpr cell inverse owner,fun _ => updateExpr cell inverse owner,
    readouts cell inverse owner names⟩

theorem ready (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner Value) (ha : (a cell).isSome = true) :
    RegisterFuture.RawReady (raw cell inverse owner names) a := by
  refine ⟨?_,?_,?_⟩
  · intro k hk
    have he : k=cell := by
      simpa [raw,rowExpr,pairExpr,dataExpr,Expr.dependencies,Expr.reenv_dependencies] using hk
    subst k; exact ha
  · intro r k hk
    have he : k=cell := by
      simpa [raw,updateExpr,pairExpr,dataExpr,Expr.dependencies,Expr.reenv_dependencies] using hk
    subst k; exact ha
  · intro k hk
    have he : k=cell := by
      simpa [raw,readouts,RegisterFuture.Readouts.dependencies,table,pairExpr,dataExpr,Expr.dependencies] using hk
    subst k; exact ha

theorem data_evaluation (cell : Owner) (inverse : Bool) (a : Assignment Owner Value) (x : Registers) :
    (dataExpr cell inverse).eval a x () =
      (a cell).map (fun i => (if inverse then restore i else i).temporal) := rfl

theorem pair_evaluation (cell : Owner) (inverse : Bool) (a : Assignment Owner Value)
    (i : Input) (hi : a cell = some i) (x : Registers) :
    (pairExpr cell inverse).eval a x () = some ((if inverse then restore i else i).temporal,x ()) := by
  simp [pairExpr,Expr.eval,data_evaluation,hi]

theorem table_evaluation {X : Type} (cell : Owner) (inverse : Bool) (a : Assignment Owner Value)
    (i : Input) (hi : a cell = some i) (x : Registers) (f : Data × State → X) :
    (table cell inverse f).eval a x () = some (f ((if inverse then restore i else i).temporal,x ())) := by
  simp [table,Expr.eval,pair_evaluation,hi]

theorem table_read {X : Type} (cell : Owner) (inverse : Bool) (a : Assignment Owner Value)
    (i : Input) (hi : a cell = some i) (x : Registers) (f : Data × State → X)
    (h : Complete (table cell inverse f).dependencies a) :
    RegisterFuture.read (table cell inverse f) a h x = f ((if inverse then restore i else i).temporal,x ()) := by
  exact Option.some.inj ((RegisterFuture.read_eq _ _ h x).symm.trans (table_evaluation cell inverse a i hi x f))

theorem next_equation (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner Value) (h : RegisterFuture.RawReady (raw cell inverse owner names) a)
    (i : Input) (hi : a cell = some i) (x : Registers) (da : Unit × Bool) (o : Factor) :
    RegisterFuture.next (raw cell inverse owner names) a h x da o =
      pack (TemporalFactorRules.update (factorSchema owner) (if inverse then restore i else i).temporal (x ()) da.2 o) := by
  funext r
  cases r
  have he := checked_execute_eq (raw cell inverse owner names).program a h.2.1 x (da.1,da.2,o) ()
  have hp := pair_evaluation cell inverse a i hi x
  simp only [execute,raw,updateExpr,Expr.eval,Expr.reenv_eval,hp] at he
  exact (Option.some.inj he).symm

theorem row_equation (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner Value) (h : RegisterFuture.RawReady (raw cell inverse owner names) a)
    (i : Input) (hi : a cell = some i) (x : Registers) (da : Unit × Bool) :
    RegisterFuture.row (raw cell inverse owner names) a h x da =
      TemporalFactorRules.actualRows (factorSchema owner) (if inverse then restore i else i).temporal (x ()) da.2 := by
  have he := RegisterFuture.row_eq (raw cell inverse owner names) a h x da
  have hp := pair_evaluation cell inverse a i hi x
  simp only [raw,rowExpr,Expr.eval,Expr.reenv_eval,hp] at he
  exact (Option.some.inj he).symm

theorem observation_equation (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner Value) (h : RegisterFuture.RawReady (raw cell inverse owner names) a)
    (i : Input) (hi : a cell = some i) (x : Registers) :
    RegisterFuture.observation (raw cell inverse owner names) a h x =
      TemporalRuntimeCoherence.observationImage names
        (TemporalFactorRules.observe (factorSchema owner) (if inverse then restore i else i).temporal 2 (x ())) := by
  simp only [RegisterFuture.observation,raw,readouts,table_read cell inverse a i hi,
    TemporalRuntimeCoherence.observationImage,TemporalFactorRules.observe]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.Frame
