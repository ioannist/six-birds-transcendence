import CSTTT.Targets.GenericHandoff.NativeComposition.NativeStages
import CSTTT.Targets.GenericHandoff.NativeComposition.MemoryFrames

/-! A whole-future episode translation has a distinct job from the physical
identity boundary on the actual entry. Its raw program replays the assigned
history selected by the CURRENT factor and preserves the actual incoming past.
Away from initialized roots this is instruction evaluation, not Arrival. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.EpisodeMap
open RegisterInterpreter ModeExecution

def assignedWord (p : Input × Input) (h : Factor) : List (Unit × Bool × Factor) :=
  ((p.2.temporal.histories h).zip ((p.2.temporal.histories h).drop 1)).map
    (fun e => ((),p.2.temporal.policy e.1,e.2))
def sourceFold (p : Input × Input) (x : Frame.State) : Frame.State :=
  (assignedWord p x.factor).foldl
    (fun s e => TemporalFactorRules.update (factorSchema false) p.2.temporal s e.2.1 e.2.2) x

def program (p : Input × Input) (x : Frame.State) : Frame.State :=
  let source := sourceFold p x
  let target := received p false (source,false)
  TemporalFactorRules.update (factorSchema false) p.1.temporal target.1 false target.1.factor

def doublePast (x : Frame.State) : Frame.State :=
  ⟨x.factor,x.counter+2,x.ticks+2,(x.residue.1++x.residue.1,x.residue.2),x.funded⟩

theorem native_program (x : Frame.State) : program (episodePair 0) x=doublePast x := by
  have hw : assignedWord (episodePair 0) x.factor=[((),false,x.factor)] := rfl
  simp only [program,sourceFold]
  rw [hw]
  simp only [List.foldl_cons,List.foldl_nil,episodePair,round_update]
  simp [received,stepState,doublePast,roundInput,canonicalInput,publish,factorData]

def halfPast (x : Frame.State) : Frame.State :=
  {x with residue := (x.residue.1.take (x.residue.1.length/2),x.residue.2)}

/-- Raw typed instruction consumes the actual first publication and derives
its source replay; no free translated state or future object is supplied. -/
def translation : (k : Unit) → Expr Owner MemoryValue Unit (fun _ => Frame.State) Unit Frame.State :=
  fun _ => .map (fun p : (Input × Input) × Frame.State => program p.1 (halfPast p.2))
    (.pair (.cell true) (.register ()))

theorem translation_ready (a : Assignment Owner MemoryValue) (ha : (a true).isSome=true) :
    RegisterSubstitution.Ready translation a := by
  intro r k hk
  have he : k=true := by simpa [translation,Expr.dependencies] using hk
  subst k
  exact ha

theorem translation_missing (a : Assignment Owner MemoryValue) (hm : a true=none)
    (x : Frame.Registers) : (translation ()).eval a x ()=none := by
  simp [translation,Expr.eval,hm]

def shifted (x : Frame.State) : Frame.State :=
  ⟨x.factor,x.counter+2,x.ticks+2,x.residue,x.funded⟩

theorem past_restored (x : Frame.State) (past : List Factor)
    (hp : x.residue.1=past++past) : program (episodePair 0) (halfPast x)=shifted x := by
  rw [native_program]
  simp only [doublePast,halfPast,hp,half_double]
  have he : (past++past,x.residue.2)=x.residue := by rw [← hp]
  rw [he]
  rfl

theorem shifted_successor (x : Frame.State) (o : Factor) :
    shifted (stepState x o)=stepState (shifted x) o := rfl

theorem native_translation (h : RegisterSubstitution.Ready translation nativeAssignment)
    (x : Frame.Registers) :
    RegisterSubstitution.translate translation nativeAssignment h x () =
      Frame.pack (program (episodePair 0) (halfPast (x ()))) := by
  funext r
  have he := RegisterSubstitution.translation_equation translation nativeAssignment h x () r
  change some (program (episodePair 0) (halfPast (x ()))) =
    some (RegisterSubstitution.translate translation nativeAssignment h x () r) at he
  exact (Option.some.inj he).symm

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.EpisodeMap
