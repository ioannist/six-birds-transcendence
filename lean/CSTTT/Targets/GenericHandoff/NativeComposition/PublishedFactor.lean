import CSTTT.Targets.GenericHandoff.NativeComposition.Inputs

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition

theorem published_factor_accept (owner : Owner) :
    TemporalFactorRules.Accept (factorSchema (swapOwner owner)) (publish (canonicalInput owner)).temporal := by
  obtain ⟨hd,hs,ht,hr,hlink,htrace,hfund,hinterface,hbisim,hcoarse⟩ := factor_accept (swapOwner owner)
  refine ⟨hd,hs,ht,hr,hlink,?_,hfund,hinterface,hbisim,hcoarse⟩
  cases owner <;> simp only [TemporalFactorRules.Trace] <;> decide +kernel

theorem twice_published_factor_accept (owner : Owner) :
    TemporalFactorRules.Accept (factorSchema owner) (publish (publish (canonicalInput owner))).temporal := by
  obtain ⟨hd,hs,ht,hr,hlink,htrace,hfund,hinterface,hbisim,hcoarse⟩ := factor_accept owner
  refine ⟨hd,hs,ht,hr,hlink,?_,hfund,hinterface,hbisim,hcoarse⟩
  cases owner <;> simp only [TemporalFactorRules.Trace] <;> decide +kernel

theorem actual_history_lengths (owner : Owner) (h : History) :
    ((canonicalInput owner).temporal.histories h).length = 2 ∧
    ((publish (canonicalInput owner)).temporal.histories h).length = 4 ∧
    ((publish (publish (canonicalInput owner))).temporal.histories h).length = 8 := by
  exact ⟨rfl,rfl,rfl⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition
