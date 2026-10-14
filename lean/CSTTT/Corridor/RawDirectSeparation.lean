import CSTTT.Corridor.RawDirectSuccessor
namespace CSTTT.CorridorTheory.RawDirectSeparation
open CSTTT.CorridorTheory.AtomicChain CSTTT.CorridorTheory.RawDirectSuccessor

theorem overlap_audit (m : ControlModel) (h : OverlapMode m) : auditCheck m.episode=true := by
  simp only [OverlapMode,AtomicLegPass,AtomicLegCheck,Bool.and_eq_true] at h
  have hi := h.1.2
  simp only [interventionCheck,Bool.and_eq_true] at hi
  exact hi.2

theorem projected_audit_events (m : ControlModel) (raw : Raw) (b : Boundary)
    (h : directProjection m=some (raw,b)) :
    ∃ source target, eventAt m.episode m.episode.sourceAudit=some source ∧
      eventAt m.episode m.episode.targetAudit=some target ∧
      b.sourceStage=source.stage ∧ b.targetStage=target.stage := by
  unfold directProjection at h
  cases hs : eventAt m.episode m.episode.sourceAudit <;> simp [hs] at h
  rename_i source
  cases ht : eventAt m.episode m.episode.targetAudit <;> simp [ht] at h
  rename_i target
  cases hss : m.episode.stages[source.stage]? <;> simp [hss] at h
  cases hts : m.episode.stages[target.stage]? <;> simp [hts] at h
  cases hu : m.episode.updates[source.stage]? <;> simp [hu] at h
  obtain ⟨_,_,hb⟩ := h
  cases hb
  exact ⟨source,target,rfl,rfl,rfl,rfl⟩

theorem direct_audit_adjacent (m : ControlModel) (h : DirectMode m) :
    ∃ source target, eventAt m.episode m.episode.sourceAudit=some source ∧
      eventAt m.episode m.episode.targetAudit=some target ∧ source.stage+1=target.stage := by
  obtain ⟨raw,b,hp,hd⟩ := h
  obtain ⟨source,target,hs,ht,hbs,hbt⟩ := projected_audit_events m raw b hp
  obtain ⟨edge,c,_,_,_,_,hg⟩ := (direct_readout_iff raw b m.input).mp hd
  simp only [Geometry] at hg
  rcases hg with ⟨_,_,_,_,_,_,_,_,_,_,_,_,hnext,_,_,hstage,_⟩
  exact ⟨source,target,hs,ht,by omega⟩

theorem overlap_not_direct (m : ControlModel) (h : OverlapMode m) : ¬ DirectMode m := by
  intro hd
  obtain ⟨source,target,hs,ht,hnext⟩ := direct_audit_adjacent m hd
  have ha := overlap_audit m h
  unfold auditCheck at ha
  rw [hs,ht] at ha
  cases he : eventAt m.episode m.episode.laterAudit <;> simp [he] at ha
  omega

theorem direct_not_overlap (m : ControlModel) (h : DirectMode m) : ¬ OverlapMode m := by
  intro ho
  exact overlap_not_direct m ho h

end CSTTT.CorridorTheory.RawDirectSeparation
