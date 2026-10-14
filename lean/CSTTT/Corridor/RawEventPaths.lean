import CSTTT.Corridor.RawDirectSeparation
namespace CSTTT.CorridorTheory.RawEventPaths
open CSTTT.CorridorTheory.AtomicChain CSTTT.CorridorTheory.RawDirectSuccessor
open CSTTT.CorridorTheory.RawDirectSeparation

/-- Positive-length paths use actual generation dependencies. This is a
separate graph from the data-channel graph and from generalized typed legs. -/
inductive EventPath (graph : List RawDependency) : Nat → EventId → EventId → Prop where
  | one (edge : RawDependency) (member : edge∈graph) : EventPath graph 1 edge.parent edge.child
  | extend {n : Nat} {source middle : EventId} (previous : EventPath graph n source middle)
      (edge : RawDependency) (member : edge∈graph) (parent : edge.parent=middle) :
      EventPath graph (n+1) source edge.child

theorem projected_dependencies_forward (m : ControlModel) (raw : Raw) (b : Boundary)
    (projection : directProjection m=some (raw,b)) :
    m.episode.dependencies.all (dependencyCheck m.episode)=true := by
  unfold directProjection at projection
  cases hs : eventAt m.episode m.episode.sourceAudit <;> simp [hs] at projection
  rename_i source
  cases ht : eventAt m.episode m.episode.targetAudit <;> simp [ht] at projection
  rename_i target
  cases hss : m.episode.stages[source.stage]? <;> simp [hss] at projection
  cases hts : m.episode.stages[target.stage]? <;> simp [hts] at projection
  cases hu : m.episode.updates[source.stage]? <;> simp [hu] at projection
  obtain ⟨gate,_,_⟩ := projection
  exact List.all_eq_true.mpr gate.2.2.2

theorem checked_dependency_events (episode : FiniteAtomicLeg) (edge : RawDependency)
    (checked : dependencyCheck episode edge=true) :
    ∃ source target, eventAt episode edge.parent=some source ∧
      eventAt episode edge.child=some target ∧ source.stage<target.stage := by
  unfold dependencyCheck at checked
  cases hs : eventAt episode edge.parent <;> simp [hs] at checked
  rename_i source
  cases ht : eventAt episode edge.child <;> simp [ht] at checked
  rename_i target
  exact ⟨source,target,rfl,rfl,checked⟩

theorem path_stage_bound (episode : FiniteAtomicLeg)
    (forward : episode.dependencies.all (dependencyCheck episode)=true)
    {n : Nat} {source target : EventId} (path : EventPath episode.dependencies n source target)
    (left right : RawEvent) (sourceFound : eventAt episode source=some left)
    (targetFound : eventAt episode target=some right) : left.stage+n≤right.stage := by
  induction path generalizing left right with
  | one edge member =>
    have checked := (List.all_eq_true.mp forward) edge member
    obtain ⟨a,b,ha,hb,step⟩ := checked_dependency_events episode edge checked
    rw [sourceFound] at ha
    rw [targetFound] at hb
    cases ha
    cases hb
    omega
  | extend previous edge member parent ih =>
    have checked := (List.all_eq_true.mp forward) edge member
    obtain ⟨middle,last,hm,hl,step⟩ := checked_dependency_events episode edge checked
    rw [parent] at hm
    rw [targetFound] at hl
    cases hl
    have before := ih left middle sourceFound hm
    omega

/-- Genuine direct succession leaves no room for any path with two or more
generation edges through an intermediate event, irrespective of its tags. -/
theorem direct_excludes_every_mediated_generation_path (m : ControlModel)
    (direct : DirectMode m) (n : Nat) (mediated : 2≤n) :
    ¬ EventPath m.episode.dependencies n m.episode.sourceAudit m.episode.targetAudit := by
  intro path
  obtain ⟨raw,b,projection,readout⟩ := direct
  have forward := projected_dependencies_forward m raw b projection
  obtain ⟨source,target,hs,ht,adjacent⟩ := direct_audit_adjacent m ⟨raw,b,projection,readout⟩
  have bound := path_stage_bound m.episode forward path source target hs ht
  omega

end CSTTT.CorridorTheory.RawEventPaths
