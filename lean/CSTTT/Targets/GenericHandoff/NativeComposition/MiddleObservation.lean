import CSTTT.Targets.GenericHandoff.NativeComposition.MiddleFuture
import CSTTT.Transport.SnapshotImages

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.MiddleFuture
open RegisterInterpreter ModeExecution EpisodeMap CSTTT.TransportTheory

abbrev Observation := TemporalSnapshotReadout Frame.Predictive Frame.Residue Bool

def observation (x : Frame.State) : Observation :=
  TemporalRuntimeCoherence.observationImage firstNames
    (TemporalFactorRules.observe (factorSchema true) (roundInput 1).temporal 2 x)

theorem source_observation (x : Frame.Registers) :
    RegisterFuture.observation source nativeAssignment source_ready x=observation (x ()) :=
  MemoryFrames.observation true false true firstNames nativeAssignment source_ready (episodePair 0) rfl x

theorem target_observation (x : Frame.Registers) :
    RegisterFuture.observation target nativeAssignment target_ready x=observation (x ()) := by
  rw [MemoryFrames.observation false true true secondNames nativeAssignment target_ready (episodePair 1) rfl]
  rfl

theorem middle_writer (h : Factor) :
    TemporalFactorRules.writer (factorSchema true) (roundInput 1).temporal (List.replicate 4 h,[false,true])=true := by
  rcases h with ⟨p,v,j⟩
  cases p <;> cases v <;> cases j <;> rfl

def maps : SnapshotRawMaps Frame.Predictive Frame.Predictive Frame.Residue Bool :=
  ⟨id,(·+2),id,(·+2),(·+2),id,id,id⟩

theorem shifted_observation (x : Frame.Registers) (hx : SourceClosure x) :
    mapSnapshotReadout maps (observation (x ()))=observation (shifted (x ())) := by
  obtain ⟨hf,h,hr⟩ := closure_shape x hx
  have hp : ((x ()).ticks+2)%2=(x ()).ticks%2 := by omega
  simp only [observation,TemporalRuntimeCoherence.observationImage,TemporalFactorRules.observe,
    shifted,mapSnapshotReadout,maps,hf,hr,middle_writer,Bool.true_and,ite_true,id_eq,hp]

theorem translated_observation (x : Frame.Registers) (hx : SourceClosure x) :
    mapSnapshotReadout maps (RegisterFuture.observation source nativeAssignment source_ready x)=
      RegisterFuture.observation target nativeAssignment target_ready
        (RegisterSubstitution.translate translation nativeAssignment map_ready x ()) := by
  rw [source_observation,target_observation,translation_on_closure x hx]
  exact shifted_observation x hx

theorem source_row (x : Frame.Registers) (da : Unit × Bool) :
    RegisterFuture.row source nativeAssignment source_ready x da=
      if (x ()).funded then [(destination (x ()).factor da.2,(1:Rat))] else [] := by
  rw [MemoryFrames.row true false true firstNames nativeAssignment source_ready (episodePair 0) rfl]
  exact round_rows true 1 (x ()) da.2

theorem target_row (x : Frame.Registers) (da : Unit × Bool) :
    RegisterFuture.row target nativeAssignment target_ready x da=
      if (x ()).funded then [(destination (x ()).factor da.2,(1:Rat))] else [] := by
  rw [MemoryFrames.row false true true secondNames nativeAssignment target_ready (episodePair 1) rfl]
  exact round_rows true 1 (x ()) da.2

theorem translated_weight (x : Frame.Registers) (hx : SourceClosure x) (da : Unit × Bool) (o : Factor) :
    RegisterFuture.weight target nativeAssignment target_ready
      (RegisterSubstitution.translate translation nativeAssignment map_ready x ()) da o=
    RegisterFuture.weight source nativeAssignment source_ready x da o := by
  simp only [RegisterFuture.weight,target_row,source_row,translation_on_closure x hx]
  rfl

theorem maps_injective : Function.Injective (mapSnapshotReadout maps) := by
  intro x y he
  have hp := congrArg TemporalSnapshotReadout.predictive he
  have ho := congrArg TemporalSnapshotReadout.order he
  have ht := congrArg TemporalSnapshotReadout.tickPhase he
  have hg := congrArg TemporalSnapshotReadout.progress he
  have hd := congrArg TemporalSnapshotReadout.record he
  have hr := congrArg TemporalSnapshotReadout.residue he
  have hm := congrArg TemporalSnapshotReadout.maintenance he
  have hw := congrArg TemporalSnapshotReadout.owner he
  cases x; cases y
  simp only [mapSnapshotReadout,maps,id_eq] at hp ho ht hg hd hr hm hw
  congr <;> omega

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.MiddleFuture
