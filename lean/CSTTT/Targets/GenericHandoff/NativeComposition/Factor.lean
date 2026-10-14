import CSTTT.Targets.GenericHandoff.TemporalFactorCells
import CSTTT.Targets.GenericHandoff.TemporalFactorFuture

/-! Connected native C2/C3/C6 primitives for the two-hop runtime construction.
A probe action splits equal-phase states by their visible bit. The hidden bit
remains genuinely coarse. These raw clauses still require runtime/package
assembly before a full handoff can be claimed. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition
abbrev Factor := Bool × Bool × Bool
abbrev Stage := Fin 3
abbrev History := Factor
abbrev Route := Factor
abbrev Owner := Bool

def factors : List Factor := [(false,false,false),(false,false,true),(false,true,false),(false,true,true),
  (true,false,false),(true,false,true),(true,true,false),(true,true,true)]
def stages : List Stage := [0,1,2]
def bit (b : Bool) : Nat := if b then 1 else 0
def labels (s : Factor) : Nat := 2*bit s.1 + bit s.2.1
def probe (s : Factor) : Factor := (if s.2.1 then !s.1 else s.1,s.2)
def destination (s : Factor) (a : Bool) := if a then probe s else s

def clauseSchema : ProfileRules.ClauseSchema Factor Bool Factor where
  states := factors
  actions := [false,true]
  destination := some
  externalBlock := fun _ => 0
  blocks := [0,1,2,3]
  split := ((false,false,false),(false,true,false))
  trajectory := (2,4,4)
  depth := 1
  outcomes := factors
  rowScale := 1
  referenceClasses := labels

def factorSchema (owner : Owner) : TemporalFactorRules.Schema Factor Bool Factor History Route Stage Bool Owner :=
  ⟨clauseSchema,owner,factors,factors,stages,[false,true],1,1,⟨1,1,1⟩,((false,false,false),(false,false,true))⟩

def factorData (owner : Owner) : TemporalFactorRules.Raw Factor Bool Factor History Route Stage Bool Owner where
  rows := fun s a => [(destination s a,1)]
  positions := fun s => bit s.1
  hazards := fun s => s.2.1
  policy := fun _ => false
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

def profile := TemporalFactorRules.profile (factorSchema false) (factorData false)

theorem factor_mem (s : Factor) : s ∈ factors := by
  rcases s with ⟨p,v,h⟩
  cases p <;> cases v <;> cases h <;> decide +kernel

theorem factor_domain : ProfileRules.DomainCheck clauseSchema := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,factor_mem,?_,factor_mem⟩
  intro a; cases a <;> simp [clauseSchema]

theorem prediction_equation (owner : Owner) (s : Factor) :
    TemporalFactorRules.prediction (factorSchema owner) (factorData owner) s =
      .inl (bit s.1,[[s.2.1],[s.2.1]]) := rfl

theorem prediction_iff (owner : Owner) (s t : Factor) :
    TemporalFactorRules.prediction (factorSchema owner) (factorData owner) s =
      TemporalFactorRules.prediction (factorSchema owner) (factorData owner) t ↔
      s.1=t.1 ∧ s.2.1=t.2.1 := by
  rw [prediction_equation,prediction_equation]
  rcases s with ⟨p,v,h⟩
  rcases t with ⟨q,w,j⟩
  change (Sum.inl (bit p,[[v],[v]]) : TemporalFactorRules.Predictive Factor) = .inl (bit q,[[w],[w]]) ↔ p=q ∧ v=w
  cases p <;> cases v <;> cases q <;> cases w <;> decide +kernel

theorem linked (owner : Owner) : ProfileRules.Linked clauseSchema
    (TemporalFactorRules.profile (factorSchema owner) (factorData owner)) labels := by
  change ProfileRules.Linked clauseSchema profile labels
  refine ⟨rfl,?_⟩
  intro s t
  rcases s with ⟨p,v,h⟩
  rcases t with ⟨q,w,j⟩
  cases p <;> cases v <;> cases h <;> cases q <;> cases w <;> cases j <;> decide +kernel

theorem promotion (owner : Owner) : ProfileRules.Promotion
    (TemporalFactorRules.profile (factorSchema owner) (factorData owner)) := by
  change ProfileRules.Promotion profile
  simp only [ProfileRules.Promotion]
  decide +kernel

theorem first_profile_equation : ProfileRules.first profile = labels := by
  funext s
  rcases s with ⟨p,v,h⟩
  cases p <;> cases v <;> cases h <;> decide +kernel

theorem second_profile_equation : ProfileRules.second profile = labels := by
  change ProfileRules.step profile (ProfileRules.first profile) = labels
  rw [first_profile_equation]
  funext s
  rcases s with ⟨p,v,h⟩
  cases p <;> cases v <;> cases h <;> decide +kernel

theorem recursive_profile (owner : Owner) : ProfileRules.RecursiveProfile
    (TemporalFactorRules.profile (factorSchema owner) (factorData owner)) := by
  change ProfileRules.RecursiveProfile profile
  unfold ProfileRules.RecursiveProfile
  rw [first_profile_equation,second_profile_equation]
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,?_,?_⟩
  · intro s t; rfl
  · intro s t
    exact ((linked false).2 s t).symm

theorem policy_weight (owner : Owner) (s t : Factor) :
    TemporalFactorRules.policyWeight (factorSchema owner) (factorData owner) s t =
      if s=t then 1 else 0 := by
  simp [TemporalFactorRules.policyWeight,factorSchema,factorData,clauseSchema,destination]

theorem class_mass (owner : Owner) (s : Factor) (a : Bool)
    (c : Sum (Nat × List (List Bool)) Factor) :
    TemporalFactorRules.mass (factorSchema owner) (factorData owner) s a c =
      if TemporalFactorRules.prediction (factorSchema owner) (factorData owner) (destination s a) = c then 1 else 0 := by
  unfold TemporalFactorRules.mass
  change (([(destination s a,1)] : List (Factor × Nat)).filter (fun e => decide
    (TemporalFactorRules.prediction (factorSchema owner) (factorData owner) e.1 = c))).foldl
      (fun n e => n+e.2) 0 = _
  by_cases hc : TemporalFactorRules.prediction (factorSchema owner) (factorData owner) (destination s a) = c
  all_goals simp [hc]

theorem predictive_successor (owner : Owner) (s t : Factor) (a : Bool)
    (hp : TemporalFactorRules.prediction (factorSchema owner) (factorData owner) s =
      TemporalFactorRules.prediction (factorSchema owner) (factorData owner) t) :
    TemporalFactorRules.prediction (factorSchema owner) (factorData owner) (destination s a) =
      TemporalFactorRules.prediction (factorSchema owner) (factorData owner) (destination t a) := by
  obtain ⟨hphase,hvisible⟩ := (prediction_iff owner s t).mp hp
  cases a
  · exact hp
  · rw [prediction_equation,prediction_equation]
    simp only [destination,ite_true,probe]
    rw [hphase,hvisible]

theorem finite_bisim (owner : Owner) : TemporalFactorRules.FiniteBisim (factorSchema owner) (factorData owner) := by
  intro s hs t ht a ha hp
  refine ⟨?_,rfl⟩
  intro c hc
  rw [class_mass,class_mass,predictive_successor owner s t a hp]

theorem factor_accept (owner : Owner) : TemporalFactorRules.Accept (factorSchema owner) (factorData owner) := by
  cases owner
  all_goals refine ⟨factor_domain,by decide +kernel,by decide +kernel,?_,?_,?_,?_,rfl,finite_bisim _,?_⟩
  all_goals first
    | (simp only [ProfileRules.RowsValid]; decide +kernel)
    | (exact ⟨linked _,policy_weight _⟩)
    | (simp only [TemporalFactorRules.Trace]; decide +kernel)
    | (simp only [TemporalFactorRules.Funding]; decide +kernel)
    | (simp only [TemporalFactorRules.Coarser]; decide +kernel)

end CSTTT.TargetTheory.GenericHandoff.NativeComposition
