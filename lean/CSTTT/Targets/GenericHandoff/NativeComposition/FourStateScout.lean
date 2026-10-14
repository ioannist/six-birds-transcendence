import CSTTT.Targets.GenericHandoff.TemporalFactorCells
import CSTTT.Targets.GenericHandoff.TemporalFactorFuture

/-! Native two-hop construction, raw factor primitives. This is one integrated
candidate's finite clause data; full runtime/receiver/package assembly is still
required. Visible classes and hidden witnesses come from actual raw profiles. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.FourStateScout
abbrev Factor := Bool × Bool
abbrev Stage := Fin 3
abbrev History := Factor
abbrev Route := Factor
abbrev Owner := Bool

def factors : List Factor := [(false,false),(false,true),(true,false),(true,true)]
def stages : List Stage := [0,1,2]
def labels (s : Factor) : Nat := if s.1 then 1 else 0

def clauseSchema : ProfileRules.ClauseSchema Factor Unit Factor where
  states := factors
  actions := [()]
  destination := some
  externalBlock := fun _ => 0
  blocks := [0,1]
  split := ((false,false),(true,false))
  trajectory := (1,2,2)
  depth := 1
  outcomes := factors
  rowScale := 1
  referenceClasses := labels

def factorSchema (owner : Owner) : TemporalFactorRules.Schema Factor Unit Factor History Route Stage Bool Owner :=
  ⟨clauseSchema,owner,factors,factors,stages,[false,true],1,1,⟨1,1,1⟩,((false,false),(false,true))⟩

def factorData (owner : Owner) : TemporalFactorRules.Raw Factor Unit Factor History Route Stage Bool Owner where
  rows := fun s _ => [(s,1)]
  positions := fun _ => 0
  hazards := Prod.fst
  policy := fun _ => ()
  classes := labels
  publishedP := fun s t => if s=t then 1 else 0
  ticks := fun _ _ => 1
  resource := ⟨owner,true⟩
  ledger := ⟨1,1,1⟩
  interface := TemporalFactorRules.interface
  histories := fun s => [s,s]
  events := [⟨false,0,1,true,true⟩,⟨true,1,2,true,true⟩]
  realized := stages
  receiverFunded := true
  routes := factors.map (fun s => ⟨s,s,[false,true]⟩)
  writers := fun _ => true

theorem factor_mem (s : Factor) : s ∈ factors := by
  rcases s with ⟨v,h⟩
  cases v <;> cases h <;> decide +kernel

theorem factor_domain : ProfileRules.DomainCheck clauseSchema := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,factor_mem,?_,factor_mem⟩
  intro a; cases a; simp [clauseSchema]

theorem prediction_equation (owner : Owner) (s : Factor) :
    TemporalFactorRules.prediction (factorSchema owner) (factorData owner) s =
      .inl (0,[[s.1]]) := rfl

theorem linked (owner : Owner) : ProfileRules.Linked clauseSchema
    (TemporalFactorRules.profile (factorSchema owner) (factorData owner)) labels := by
  cases owner
  all_goals refine ⟨rfl,?_⟩
  all_goals intro s t
  all_goals rcases s with ⟨v,h⟩; rcases t with ⟨w,j⟩
  all_goals cases v <;> cases h <;> cases w <;> cases j <;> decide +kernel

theorem promotion (owner : Owner) : ProfileRules.Promotion
    (TemporalFactorRules.profile (factorSchema owner) (factorData owner)) := by
  cases owner <;> simp only [ProfileRules.Promotion] <;> decide +kernel

theorem profile_not_recursive (owner : Owner) : ¬ ProfileRules.RecursiveProfile
    (TemporalFactorRules.profile (factorSchema owner) (factorData owner)) := by
  intro h
  have hc : ProfileRules.second (TemporalFactorRules.profile (factorSchema owner) (factorData owner)) (false,false) =
      ProfileRules.second (TemporalFactorRules.profile (factorSchema owner) (factorData owner)) (true,false) := rfl
  have hp := (h.2.2.2.2 (false,false) (true,false)).mp hc
  have bad : ProfileRules.predictive (TemporalFactorRules.profile (factorSchema owner) (factorData owner)) (false,false) ≠
      ProfileRules.predictive (TemporalFactorRules.profile (factorSchema owner) (factorData owner)) (true,false) := by
    change (0,[[false]]) ≠ (0,[[true]])
    decide +kernel
  exact bad hp

theorem policy_weight (owner : Owner) (s t : Factor) :
    TemporalFactorRules.policyWeight (factorSchema owner) (factorData owner) s t =
      if s=t then 1 else 0 := by
  simp [TemporalFactorRules.policyWeight,factorSchema,factorData,clauseSchema]

theorem class_mass (owner : Owner) (s : Factor) (a : Unit)
    (c : Sum (Nat × List (List Bool)) Factor) :
    TemporalFactorRules.mass (factorSchema owner) (factorData owner) s a c =
      if (.inl (0,[[s.1]]) : Sum (Nat × List (List Bool)) Factor) = c then 1 else 0 := by
  unfold TemporalFactorRules.mass
  change (([(s,1)] : List (Factor × Nat)).filter (fun e => decide
    (TemporalFactorRules.prediction (factorSchema owner) (factorData owner) e.1 = c))).foldl
      (fun n e => n+e.2) 0 = _
  simp only [List.filter_cons,List.filter_nil,prediction_equation]
  by_cases hc : (Sum.inl (0,[[s.1]]) : Sum (Nat × List (List Bool)) Factor) = c
  all_goals simp [hc]

theorem finite_bisim (owner : Owner) : TemporalFactorRules.FiniteBisim (factorSchema owner) (factorData owner) := by
  intro s hs t ht a ha hp
  refine ⟨?_,rfl⟩
  intro c hc
  rw [prediction_equation,prediction_equation] at hp
  rw [class_mass,class_mass,hp]

theorem factor_accept (owner : Owner) : TemporalFactorRules.Accept (factorSchema owner) (factorData owner) := by
  cases owner
  all_goals refine ⟨factor_domain,by decide +kernel,by decide +kernel,?_,?_,?_,?_,rfl,finite_bisim _,?_⟩
  all_goals first
    | (simp only [ProfileRules.RowsValid]; decide +kernel)
    | (exact ⟨linked _,policy_weight _⟩)
    | (simp only [TemporalFactorRules.Trace]; decide +kernel)
    | (simp only [TemporalFactorRules.Funding]; decide +kernel)
    | (simp only [TemporalFactorRules.Coarser]; decide +kernel)

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.FourStateScout
