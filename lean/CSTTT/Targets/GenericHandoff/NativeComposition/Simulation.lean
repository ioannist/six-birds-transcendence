import CSTTT.Targets.GenericHandoff.NativeComposition.Frame

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.Frame
open RegisterInterpreter

def coherence (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId) :
    TemporalRuntimeCoherence.Raw Owner Value Unit (fun _ => State)
      Factor Bool Factor History Route Stage Bool Owner Unit :=
  ⟨factorSchema owner,factorBindings cell inverse,raw cell inverse owner names,.register (),names⟩

theorem coherence_ready (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner Value) (i : Input) (hi : a cell = some i) :
    TemporalRuntimeCoherence.Ready (coherence cell inverse owner names) a := by
  refine ⟨⟨(if inverse then restore i else i).temporal,?_⟩,ready cell inverse owner names a ?_,?_⟩
  · change TemporalFactorCells.decoded (factorBindings cell inverse) a = _
    rw [decoded_factor,hi]; rfl
  · simp [hi]
  · intro k hk; simp [coherence,Expr.dependencies] at hk

theorem coherence_data (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner Value) (i : Input) (hi : a cell = some i)
    (h : TemporalRuntimeCoherence.Ready (coherence cell inverse owner names) a) :
    TemporalRuntimeCoherence.data (coherence cell inverse owner names) a h =
      (if inverse then restore i else i).temporal := by
  have hd := TemporalRuntimeCoherence.decoded_data (coherence cell inverse owner names) a h
  change TemporalFactorCells.decoded (factorBindings cell inverse) a = _ at hd
  rw [decoded_factor,hi] at hd
  exact (Option.some.inj hd).symm

theorem coherence_project (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId)
    (a : Assignment Owner Value) (h : TemporalRuntimeCoherence.Ready (coherence cell inverse owner names) a)
    (x : Registers) : TemporalRuntimeCoherence.project (coherence cell inverse owner names) a h x = x () := by
  have he := RegisterFuture.read_eq (coherence cell inverse owner names).projection a h.2.2 x
  change some (x ()) = some (TemporalRuntimeCoherence.project (coherence cell inverse owner names) a h x) at he
  exact (Option.some.inj he).symm

theorem coherence_laws (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId)
    (injective : Function.Injective names) (a : Assignment Owner Value) (i : Input) (hi : a cell = some i)
    (h : TemporalRuntimeCoherence.Ready (coherence cell inverse owner names) a) :
    TemporalRuntimeCoherence.Laws (coherence cell inverse owner names) a h := by
  refine ⟨injective,rfl,?_,?_,?_,?_,?_,?_⟩
  · intro x da
    simp only [coherence_project,coherence_data cell inverse owner names a i hi]
    exact row_equation cell inverse owner names a h.2.1 i hi x da
  · intro x da o
    simp only [coherence_project,coherence_data cell inverse owner names a i hi]
    change (RegisterFuture.next (raw cell inverse owner names) a h.2.1 x da o) () = _
    rw [next_equation cell inverse owner names a h.2.1 i hi]
    rfl
  · intro x
    simp only [coherence_project,coherence_data cell inverse owner names a i hi]
    exact observation_equation cell inverse owner names a h.2.1 i hi x
  · intro x
    simp only [coherence_project]
    exact table_evaluation cell inverse a i hi x (fun p => p.2.ticks)
  · intro x
    simp only [coherence_project,coherence_data cell inverse owner names a i hi]
    exact table_evaluation cell inverse a i hi x
      (fun p => TemporalFactorRules.writer (factorSchema owner) p.1 p.2.residue)
  · intro p hp
    exact ⟨pack p,coherence_project cell inverse owner names a h (pack p)⟩

theorem coherence_valid (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId)
    (injective : Function.Injective names) (a : Assignment Owner Value) (i : Input) (hi : a cell = some i)
    (ha : TemporalFactorRules.Accept (factorSchema owner) (if inverse then restore i else i).temporal) :
    TemporalRuntimeCoherence.Valid (coherence cell inverse owner names) a := by
  let h := coherence_ready cell inverse owner names a i hi
  refine ⟨h,?_,coherence_laws cell inverse owner names injective a i hi h⟩
  rw [coherence_data cell inverse owner names a i hi h]
  exact ha

local instance : DecidableEq (CSTTT.TransportTheory.TemporalSnapshotReadout Predictive Residue Bool) :=
  CSTTT.TransportTheory.instDecidableEqTemporalSnapshotReadout

theorem all_unbounded_words (cell : Owner) (inverse : Bool) (owner : Owner) (names : Owner → CarrierId)
    (injective : Function.Injective names) (a : Assignment Owner Value) (i : Input) (hi : a cell = some i)
    (ha : TemporalFactorRules.Accept (factorSchema owner) (if inverse then restore i else i).temporal) :
    ∃ h : TemporalRuntimeCoherence.Ready (coherence cell inverse owner names) a,
      CSTTT.TransportTheory.FullFutureSufficient (RegisterFuture.future (raw cell inverse owner names) a h.2.1) :=
  TemporalRuntimeCoherence.soundness (coherence cell inverse owner names) a
    (coherence_valid cell inverse owner names injective a i hi ha)

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.Frame
