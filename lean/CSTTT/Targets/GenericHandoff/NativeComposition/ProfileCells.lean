import CSTTT.Targets.GenericHandoff.NativeComposition.MemoryFrames
import CSTTT.Targets.GenericHandoff.NativeComposition.EpisodeRules
import CSTTT.Targets.GenericHandoff.ClauseDispatcher

/-! Native C2/C3 read the same assigned rows/positions/hazards as C6, plus the
actual assigned reveal instruction. Publication preserves these raw profiles;
missing cells still reject at the decoder. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ProfileCells
open RegisterInterpreter

def data (i : Input) : ProfileRules.Raw Factor Bool Factor :=
  {TemporalFactorRules.profile (factorSchema false) i.temporal with revealLabel := i.reveal}
def bindings (cell : Owner) (source : Bool) : ProfileRules.ClauseBindings Owner MemoryValue Factor Bool Factor :=
  let get : Input × Input → Input := MemoryFrames.selectInput source
  ⟨⟨⟨cell,fun p => (get p).temporal.rows⟩,⟨cell,fun p => (get p).temporal.positions⟩,
      ⟨cell,fun p => (get p).temporal.hazards⟩,⟨cell,fun p => (get p).reveal⟩⟩,
    ⟨cell,fun p => (get p).temporal.classes⟩⟩

theorem decoded (cell : Owner) (source : Bool) (a : Assignment Owner MemoryValue) :
    ProfileRules.decodedClause clauseSchema (bindings cell source) a =
      (a cell).map (fun p => (data (MemoryFrames.selectInput source p),
        (MemoryFrames.selectInput source p).temporal.classes)) := by
  cases ha : a cell <;> simp [ProfileRules.decodedClause,ProfileRules.decoded,bindings,CellView.read,ha,data,
    TemporalFactorRules.profile,clauseSchema,factorSchema]

theorem publication_profile (i : Input) : data (publish i)=data i := rfl

theorem round_profile (n : Nat) : data (ModeExecution.roundInput n)=profile := by
  induction n with
  | zero => rfl
  | succ n ih => exact (publication_profile (ModeExecution.roundInput n)).trans ih

theorem round_classes (n : Nat) : (ModeExecution.roundInput n).temporal.classes=labels := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem stable_profile : ProfileRules.StableProfile profile := by
  have hs : ProfileRules.step profile (ProfileRules.first profile)=labels := second_profile_equation
  rw [first_profile_equation] at hs
  have hb : ProfileRules.blockCoverageCheck profile labels=true := by decide +kernel
  refine ⟨recursive_profile false,?_,?_,?_⟩
  · rw [second_profile_equation]; exact hs
  · rw [first_profile_equation]; exact (ProfileRules.block_coverage_iff profile labels).mp hb
  · rw [second_profile_equation]; exact (ProfileRules.block_coverage_iff profile labels).mp hb

theorem native_clause_decode (cell : Owner) (source : Bool) (a : Assignment Owner MemoryValue)
    (p : Input × Input) (hp : a cell=some p) (n : Nat)
    (hn : MemoryFrames.selectInput source p=ModeExecution.roundInput n) :
    ProfileRules.decodedClause clauseSchema (bindings cell source) a=some (profile,labels) := by
  rw [decoded,hp]
  simp only [Option.map_some,hn,round_profile,round_classes]

theorem c2 (cell : Owner) (source : Bool) (a : Assignment Owner MemoryValue)
    (p : Input × Input) (hp : a cell=some p) (n : Nat)
    (hn : MemoryFrames.selectInput source p=ModeExecution.roundInput n) :
    ProfileRules.C2Accept clauseSchema (bindings cell source) a := by
  refine ⟨factor_domain,profile,labels,native_clause_decode cell source a p hp n hn,?_,linked false,promotion false⟩
  simp only [ProfileRules.RowsValid]; decide +kernel

theorem c3 (cell : Owner) (source : Bool) (a : Assignment Owner MemoryValue)
    (p : Input × Input) (hp : a cell=some p) (n : Nat)
    (hn : MemoryFrames.selectInput source p=ModeExecution.roundInput n) :
    (ClauseDispatcher.Rule.c3 inferInstance inferInstance clauseSchema (bindings cell source)).accept a := by
  refine ⟨⟨factor_domain,profile,labels,native_clause_decode cell source a p hp n hn,?_,linked false,recursive_profile false⟩,
    profile,labels,native_clause_decode cell source a p hp n hn,stable_profile⟩
  simp only [ProfileRules.RowsValid]; decide +kernel

theorem missing (cell : Owner) (source : Bool) (a : Assignment Owner MemoryValue) (hm : a cell=none) :
    ProfileRules.decodedClause clauseSchema (bindings cell source) a=none := by
  rw [decoded,hm]
  rfl

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ProfileCells
