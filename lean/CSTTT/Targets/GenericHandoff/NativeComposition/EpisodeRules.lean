import CSTTT.Targets.GenericHandoff.NativeComposition.Acquisition

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
open RegisterInterpreter

def roundInput : Nat → Input
  | 0 => canonicalInput false
  | n+1 => publish (roundInput n)
def episodePair (n : Nat) : MemoryValue false := (roundInput (n+1),roundInput n)

theorem update_publish (owner : Owner) (i : Input) (x : Frame.State) (act : Bool) (o : Factor) :
    TemporalFactorRules.update (factorSchema owner) (publish i).temporal x act o =
      TemporalFactorRules.update (factorSchema owner) i.temporal x act o := rfl

theorem rows_publish (owner : Owner) (i : Input) (x : Frame.State) (act : Bool) :
    TemporalFactorRules.actualRows (factorSchema owner) (publish i).temporal x act =
      TemporalFactorRules.actualRows (factorSchema owner) i.temporal x act := rfl

def stepState (x : Frame.State) (o : Factor) : Frame.State :=
  ⟨o,x.counter+1,x.ticks+1,x.residue,x.funded⟩

theorem round_update (owner : Owner) (n : Nat) (x : Frame.State) (act : Bool) (o : Factor) :
    TemporalFactorRules.update (factorSchema owner) (roundInput n).temporal x act o = stepState x o := by
  induction n with
  | zero =>
    simp [roundInput,canonicalInput,factorData,factorSchema,clauseSchema,TemporalFactorRules.update,
      TemporalFactorRules.delta,TemporalFactorRules.budgetAfter,stepState]
  | succ n ih => exact (update_publish owner (roundInput n) x act o).trans ih

theorem round_rows (owner : Owner) (n : Nat) (x : Frame.State) (act : Bool) :
    TemporalFactorRules.actualRows (factorSchema owner) (roundInput n).temporal x act =
      if x.funded then [(destination x.factor act,(1:Rat))] else [] := by
  induction n with
  | zero =>
    have hrat : (1:Rat)/1=1 := by decide +kernel
    simp [hrat,roundInput,canonicalInput,factorData,factorSchema,clauseSchema,TemporalFactorRules.actualRows,
      TemporalFactorRules.row,TemporalFactorRules.enabled]
  | succ n ih => exact (rows_publish owner (roundInput n) x act).trans ih

theorem episode_update (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (h : AcquisitionExecution.Ready (acquisition cell sourceOwner start stride) a)
    (n : Nat) (hp : a cell=some (episodePair n)) (x : Registers) (d : Unit) (act : Bool) (o : Factor) :
    AcquisitionExecution.update (acquisition cell sourceOwner start stride) a h x d act o =
      pack (stepState (x ()).1 o,(x ()).2) := by
  rw [acquisition_update cell sourceOwner start stride a h (episodePair n) hp]
  by_cases hm : (x ()).2=swapOwner sourceOwner
  all_goals simp only [hm,ite_true,ite_false,episodePair,round_update]

theorem episode_rows (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (n : Nat) (hp : a cell=some (episodePair n))
    (x : Registers) (d : Unit) (act : Bool) :
    AcquisitionExecution.rows (acquisition cell sourceOwner start stride) a x d act =
      if (x ()).1.funded then [(destination (x ()).1.factor act,(1:Rat))] else [] := by
  rw [acquisition_rows cell sourceOwner start stride a (episodePair n) hp]
  by_cases hm : (x ()).2=swapOwner sourceOwner
  all_goals simp only [hm,ite_true,ite_false,episodePair,round_rows]

theorem episode_step_check (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (n : Nat) (hp : a cell=some (episodePair n))
    (x : Registers) (hf : (x ()).1.funded=true) :
    SupportedAcquisitionSequence.stepCheck (acquisition cell sourceOwner start stride) a x () false (x ()).1.factor = true := by
  simp only [SupportedAcquisitionSequence.stepCheck,episode_rows cell sourceOwner start stride a n hp,hf,ite_true]
  simp [acquisition,execution,SupportedAcquisitionSequence.supports,destination]
  decide +kernel

theorem episode_positive_unique (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (n : Nat) (hp : a cell=some (episodePair n))
    (x : Registers) (d : Unit) (act : Bool) (o : Factor) :
    StrategyGame.PositiveSupport (AcquisitionExecution.rows (acquisition cell sourceOwner start stride) a) x d act o ↔
      (x ()).1.funded=true ∧ o=destination (x ()).1.factor act := by
  rw [StrategyGame.PositiveSupport,episode_rows cell sourceOwner start stride a n hp]
  cases (x ()).1.funded <;> simp
  constructor
  · rintro ⟨w,he,_⟩
    have ho : o=destination (x ()).1.factor act := he.1
    exact ho
  · intro ho
    subst o
    exact ⟨1,⟨rfl,rfl⟩,by decide +kernel⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.ModeExecution
