import CSTTT.Targets.GenericHandoff.NativeComposition.ProfileCells

/-! Frozen stronger primitive candidate: a probe is unavailable on invisible
states. Safe acquisition and its supported histories are unchanged. All
profiles and C6 masses below are computed again from these actual rows. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.AvailabilityFactor

def rows (s : Factor) (a : Bool) : List (Factor × Nat) :=
  if a && !s.2.1 then [] else [(destination s a,1)]
def temporal (owner : Owner) : FactorData := {factorData owner with rows := rows}
def input (owner : Owner) : Input := {canonicalInput owner with temporal := temporal owner}
def profile := TemporalFactorRules.profile (factorSchema false) (temporal false)

theorem safe_rows (s : Factor) : rows s false=[(s,1)] := rfl
theorem probe_rows (s : Factor) : rows s true=if s.2.1 then [(probe s,1)] else [] := by
  cases hv : s.2.1 <;> simp [rows,destination,hv]
theorem safe_policy_weight (owner : Owner) (s t : Factor) :
    TemporalFactorRules.policyWeight (factorSchema owner) (temporal owner) s t=
      if s=t then 1 else 0 := by
  simp [TemporalFactorRules.policyWeight,factorSchema,temporal,factorData,clauseSchema,rows,destination]

theorem prediction_equation (owner : Owner) (s : Factor) :
    TemporalFactorRules.prediction (factorSchema owner) (temporal owner) s=
      .inl (bit s.1,[[s.2.1],if s.2.1 then [true] else []]) := by
  rcases s with ⟨p,v,j⟩
  cases p <;> cases v <;> cases j <;> rfl

theorem prediction_iff (owner : Owner) (s t : Factor) :
    TemporalFactorRules.prediction (factorSchema owner) (temporal owner) s=
      TemporalFactorRules.prediction (factorSchema owner) (temporal owner) t ↔
      s.1=t.1 ∧ s.2.1=t.2.1 := by
  rw [prediction_equation,prediction_equation]
  rcases s with ⟨p,v,j⟩
  rcases t with ⟨q,w,k⟩
  change (Sum.inl (bit p,[[v],if v then [true] else []]) : TemporalFactorRules.Predictive Factor)=
    .inl (bit q,[[w],if w then [true] else []]) ↔ p=q ∧ v=w
  cases p <;> cases v <;> cases q <;> cases w <;> decide +kernel

theorem linked (owner : Owner) : ProfileRules.Linked clauseSchema
    (TemporalFactorRules.profile (factorSchema owner) (temporal owner)) labels := by
  change ProfileRules.Linked clauseSchema profile labels
  refine ⟨rfl,?_⟩
  intro s t
  rcases s with ⟨p,v,j⟩
  rcases t with ⟨q,w,k⟩
  cases p <;> cases v <;> cases j <;> cases q <;> cases w <;> cases k <;> decide +kernel

theorem promotion : ProfileRules.Promotion profile := by
  unfold ProfileRules.Promotion
  decide +kernel
theorem first_profile : ProfileRules.first profile=labels := by
  funext s
  rcases s with ⟨p,v,j⟩
  cases p <;> cases v <;> cases j <;> decide +kernel
theorem second_profile : ProfileRules.second profile=labels := by
  change ProfileRules.step profile (ProfileRules.first profile)=labels
  rw [first_profile]
  funext s
  rcases s with ⟨p,v,j⟩
  cases p <;> cases v <;> cases j <;> decide +kernel
theorem recursive_profile : ProfileRules.RecursiveProfile profile := by
  unfold ProfileRules.RecursiveProfile
  rw [first_profile,second_profile]
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,?_,?_⟩
  · intro s t; rfl
  · intro s t; exact ((linked false).2 s t).symm
theorem stable_profile : ProfileRules.StableProfile profile := by
  have hs : ProfileRules.step profile labels=labels := by
    have h := second_profile
    change ProfileRules.step profile (ProfileRules.first profile)=labels at h
    rwa [first_profile] at h
  have hb : ProfileRules.blockCoverageCheck profile labels=true := by decide +kernel
  refine ⟨recursive_profile,?_,?_,?_⟩
  · rw [second_profile]; exact hs
  · rw [first_profile]; exact (ProfileRules.block_coverage_iff profile labels).mp hb
  · rw [second_profile]; exact (ProfileRules.block_coverage_iff profile labels).mp hb

theorem class_mass (owner : Owner) (s : Factor) (a : Bool)
    (c : Sum (Nat × List (List Bool)) Factor) :
    TemporalFactorRules.mass (factorSchema owner) (temporal owner) s a c=
      if a && !s.2.1 then 0 else
        if TemporalFactorRules.prediction (factorSchema owner) (temporal owner) (destination s a)=c then 1 else 0 := by
  unfold TemporalFactorRules.mass TemporalFactorRules.row
  change (((if a && !s.2.1 then [] else [(destination s a,1)]) : List (Factor × Nat)).filter
    (fun e => decide (TemporalFactorRules.prediction (factorSchema owner) (temporal owner) e.1=c))).foldl
      (fun n e => n+e.2) 0 = _
  by_cases ha : (a && !s.2.1)=true
  · simp [ha]
  · by_cases hc : TemporalFactorRules.prediction (factorSchema owner) (temporal owner) (destination s a)=c
    all_goals simp [ha,hc]

theorem predictive_successor (owner : Owner) (s t : Factor) (a : Bool)
    (hp : TemporalFactorRules.prediction (factorSchema owner) (temporal owner) s=
      TemporalFactorRules.prediction (factorSchema owner) (temporal owner) t) :
    TemporalFactorRules.prediction (factorSchema owner) (temporal owner) (destination s a)=
      TemporalFactorRules.prediction (factorSchema owner) (temporal owner) (destination t a) := by
  obtain ⟨hphase,hvisible⟩ := (prediction_iff owner s t).mp hp
  cases a
  · exact hp
  · rw [prediction_equation,prediction_equation]
    simp only [destination,ite_true,probe]
    rw [hphase,hvisible]

theorem finite_bisim (owner : Owner) : TemporalFactorRules.FiniteBisim (factorSchema owner) (temporal owner) := by
  intro s hs t ht a ha hp
  refine ⟨?_,rfl⟩
  intro c hc
  rw [class_mass,class_mass,predictive_successor owner s t a hp,(prediction_iff owner s t).mp hp |>.2]

theorem factor_accept (owner : Owner) : TemporalFactorRules.Accept (factorSchema owner) (temporal owner) := by
  cases owner
  all_goals refine ⟨factor_domain,by decide +kernel,by decide +kernel,?_,?_,?_,?_,rfl,finite_bisim _,?_⟩
  all_goals first
    | (simp only [ProfileRules.RowsValid]; decide +kernel)
    | (exact ⟨linked _,safe_policy_weight _⟩)
    | (simp only [TemporalFactorRules.Trace]; decide +kernel)
    | (simp only [TemporalFactorRules.Funding]; decide +kernel)
    | (simp only [TemporalFactorRules.Coarser]; decide +kernel)

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.AvailabilityFactor
