import CSTTT.Targets.GenericHandoff.NativeComposition.NativeSemantics
import CSTTT.Targets.GenericHandoff.NativeComposition.PackageBundle

/-! The repaired primitive package supplies the actual shared mode execution.
Safe rows remain supported; unavailable probe rows remain empty. No runtime
input is replaced by the earlier always-available candidate. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationExecution
open RegisterInterpreter ModeExecution

def roundInput : Nat → Input
  | 0 => AvailabilityFactor.input false
  | n+1 => publish (roundInput n)
def episodePair (n : Nat) : MemoryValue false := (roundInput (n+1),roundInput n)
def nativeAssignment := NativePackageBundle.nativeInputs NativePackageBundle.canonical

theorem assigned_pair (cell : Owner) :
    nativeAssignment cell=some (episodePair (if cell then 0 else 1)) := by
  cases cell <;> rfl
abbrev firstAcquisition := acquisition true false 0 1
abbrev secondAcquisition := acquisition false true 2 2

theorem round_update (owner : Owner) (n : Nat) (x : Frame.State) (act : Bool) (o : Factor) :
    TemporalFactorRules.update (factorSchema owner) (roundInput n).temporal x act o=stepState x o := by
  induction n with
  | zero =>
    simp [roundInput,AvailabilityFactor.input,AvailabilityFactor.temporal,canonicalInput,factorData,
      factorSchema,clauseSchema,TemporalFactorRules.update,TemporalFactorRules.delta,
      TemporalFactorRules.budgetAfter,stepState]
  | succ n ih => exact (update_publish owner (roundInput n) x act o).trans ih

theorem round_rows (owner : Owner) (n : Nat) (x : Frame.State) (act : Bool) :
    TemporalFactorRules.actualRows (factorSchema owner) (roundInput n).temporal x act=
      if x.funded then (if act && !x.factor.2.1 then [] else [(destination x.factor act,(1:Rat))]) else [] := by
  induction n with
  | zero =>
    have hrat : (1:Rat)/1=1 := by decide +kernel
    cases act <;> cases hv : x.factor.2.1
    all_goals
    simp [hrat,roundInput,AvailabilityFactor.input,AvailabilityFactor.temporal,AvailabilityFactor.rows,
      canonicalInput,factorData,factorSchema,clauseSchema,TemporalFactorRules.actualRows,
      TemporalFactorRules.row,TemporalFactorRules.enabled,hv]
  | succ n ih => exact (rows_publish owner (roundInput n) x act).trans ih

theorem episode_update (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (h : AcquisitionExecution.Ready (acquisition cell sourceOwner start stride) a)
    (n : Nat) (hp : a cell=some (episodePair n)) (x : Registers) (d : Unit) (act : Bool) (o : Factor) :
    AcquisitionExecution.update (acquisition cell sourceOwner start stride) a h x d act o=
      pack (stepState (x ()).1 o,(x ()).2) := by
  rw [acquisition_update cell sourceOwner start stride a h (episodePair n) hp]
  by_cases hm : (x ()).2=swapOwner sourceOwner
  all_goals simp only [hm,ite_true,ite_false,episodePair,round_update]

theorem episode_rows (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (n : Nat) (hp : a cell=some (episodePair n))
    (x : Registers) (d : Unit) (act : Bool) :
    AcquisitionExecution.rows (acquisition cell sourceOwner start stride) a x d act=
      if (x ()).1.funded then
        (if act && !(x ()).1.factor.2.1 then [] else [(destination (x ()).1.factor act,(1:Rat))]) else [] := by
  rw [acquisition_rows cell sourceOwner start stride a (episodePair n) hp]
  by_cases hm : (x ()).2=swapOwner sourceOwner
  all_goals simp only [hm,ite_true,ite_false,episodePair,round_rows]

theorem safe_episode_rows (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (n : Nat) (hp : a cell=some (episodePair n)) (x : Registers) (d : Unit) :
    AcquisitionExecution.rows (acquisition cell sourceOwner start stride) a x d false=
      if (x ()).1.funded then [((x ()).1.factor,(1:Rat))] else [] := by
  rw [episode_rows cell sourceOwner start stride a n hp]
  rfl

theorem episode_step_check (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (n : Nat) (hp : a cell=some (episodePair n))
    (x : Registers) (hf : (x ()).1.funded=true) :
    SupportedAcquisitionSequence.stepCheck (acquisition cell sourceOwner start stride) a x () false (x ()).1.factor=true := by
  simp only [SupportedAcquisitionSequence.stepCheck,safe_episode_rows cell sourceOwner start stride a n hp,hf,ite_true]
  simp [acquisition,execution,SupportedAcquisitionSequence.supports]
  decide +kernel

theorem safe_positive_unique (cell sourceOwner : Owner) (start stride : Nat)
    (a : Assignment Owner MemoryValue) (n : Nat) (hp : a cell=some (episodePair n))
    (x : Registers) (d : Unit) (o : Factor) :
    StrategyGame.PositiveSupport (AcquisitionExecution.rows (acquisition cell sourceOwner start stride) a) x d false o ↔
      (x ()).1.funded=true ∧ o=(x ()).1.factor := by
  rw [StrategyGame.PositiveSupport,safe_episode_rows cell sourceOwner start stride a n hp]
  cases (x ()).1.funded <;> simp
  constructor
  · rintro ⟨w,he,_⟩; exact he.1
  · intro ho; subst o; exact ⟨1,⟨rfl,rfl⟩,by decide +kernel⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationExecution
