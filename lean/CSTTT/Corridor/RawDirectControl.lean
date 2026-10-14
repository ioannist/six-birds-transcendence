import CSTTT.Corridor.RawDirectSuccessor
namespace CSTTT.CorridorTheory.RawDirectControl
open CSTTT.CorridorTheory.AtomicChain CSTTT.CorridorTheory.RawDirectSuccessor

def controlCheck (m : ControlModel) : Bool :=
  match directProjection m with
  | some (raw,boundary) => directCheck raw boundary m.input
  | none => false

theorem control_readout_iff (m : ControlModel) : DirectMode m ↔ controlCheck m=true := by
  cases hp : directProjection m with
  | none => simp [DirectMode,controlCheck,hp]
  | some pair =>
    rcases pair with ⟨raw,boundary⟩
    rw [controlCheck,hp]
    constructor
    · rintro ⟨r,b,projection,readout⟩
      rw [hp] at projection
      cases projection
      exact readout
    · intro readout
      exact ⟨raw,boundary,hp,readout⟩

theorem projected_direct (m : ControlModel) (raw : Raw) (b : Boundary)
    (projection : directProjection m=some (raw,b)) (direct : DirectMode m) :
    ImmediateDirect raw b m.input := by
  obtain ⟨r,c,hp,hd⟩ := direct
  rw [projection] at hp
  cases hp
  exact hd

def BadOperationalPattern (m : ControlModel) : Prop :=
  ∃ raw b, directProjection m=some (raw,b) ∧
    (DetachedCopy raw m.input ∨ ArchivalReplay raw m.input ∨
      StorageMediated raw m.input ∨ TemporalGap b)

theorem control_excludes_patterns (m : ControlModel) (direct : DirectMode m) :
    ¬ BadOperationalPattern m := by
  rintro ⟨raw,b,projection,pattern⟩
  have exclusions := actual_direct_exclusions raw b m.input
    (projected_direct m raw b projection direct)
  rcases pattern with detached | archive | store | gap
  · exact exclusions.1 detached
  · exact exclusions.2.1 archive
  · exact exclusions.2.2.1 store
  · exact exclusions.2.2.2 gap

theorem source_deleted_control_rejected (m : ControlModel) (raw : Raw) (b : Boundary)
    (projection : directProjection m=some (raw,b)) (direct : DirectMode m) :
    ¬ DirectMode {m with input := deleteSource raw m.input} := by
  intro after
  exact source_removed_not_direct raw b m.input (projected_direct m raw b projection direct)
    (projected_direct {m with input := deleteSource raw m.input} raw b projection after)

theorem actual_control_fire_single_use (m : ControlModel) (direct : DirectMode m) :
    ∃ raw b d next, directProjection m=some (raw,b) ∧ fire raw m.input=some (d,next) ∧
      generated raw next=[] ∧ fire raw next=none ∧ ¬ DirectMode {m with input := next} := by
  obtain ⟨raw,b,projection,readout⟩ := direct
  obtain ⟨d,next,fired,empty,repeated,rejected⟩ := actual_fire_single_use raw b m.input readout
  refine ⟨raw,b,d,next,projection,fired,empty,repeated,?_⟩
  intro after
  exact rejected (projected_direct {m with input := next} raw b projection after)

theorem no_generated_control_rejected (m : ControlModel) (raw : Raw) (b : Boundary)
    (projection : directProjection m=some (raw,b)) (empty : generated raw m.input=[]) :
    ¬ DirectMode m := by
  intro direct
  exact no_generated_target_not_direct raw b m.input empty
    (projected_direct m raw b projection direct)

theorem data_path_requires_edge (graph : List DataEdge) (payload : Frontier)
    (source target : EventId) (path : DataPath graph payload source target) :
    ∃ edge, edge∈graph := by
  cases path with
  | one edge member carried => exact ⟨edge,member⟩
  | extend source middle target previous edge member carried parent child => exact ⟨edge,member⟩

theorem empty_data_graph_rejected (m : ControlModel) (empty : m.dataGraph=[]) :
    ¬ DataReachable m := by
  rintro ⟨input,payload,assigned,carried,path⟩
  obtain ⟨edge,member⟩ := data_path_requires_edge _ _ _ _ path
  rw [empty] at member
  simp at member

end CSTTT.CorridorTheory.RawDirectControl
