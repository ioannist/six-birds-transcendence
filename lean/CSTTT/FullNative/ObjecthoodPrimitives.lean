import CSTTT.FullNative.SnapshotExecution
import CSTTT.Targets.GenericHandoff.ObjecthoodRules

namespace CSTTT.FullNative.Objecthood
open CSTTT.TargetTheory.GenericHandoff
open FixedPointVerifier
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

def P (s t : State) : Rat :=
  ((rationalRows model s false).map fun e => if e.1=t then e.2 else 0).sum
def prototypes : List State :=
  states.filter fun s => (states.filter fun t => decide (classes model s=classes model t)).head? = some s
theorem prototypes_formula : prototypes = states.filter (fun s => !s.replica) := by
  simp only [prototypes,first_profile_equation]
  decide +kernel

theorem prototype_count : prototypes.length=16 ∧ prototypes.Nodup := by
  rw [prototypes_formula]
  decide +kernel

theorem prototype_classes : prototypes.map (classes model) = List.range 16 := by
  simp only [prototypes_formula,first_profile_equation]
  decide +kernel

def prototype (k : Fin 16) : State :=
  prototypes.get ⟨k.val,by rw [prototype_count.1]; exact k.isLt⟩
def C (s : State) (k : Fin 16) : Rat :=
  if classes model s=classes model (prototype k) then 1 else 0
def U (k : Fin 16) (s : State) : Rat :=
  if classes model s=classes model (prototype k) then
    1/((states.filter fun t => decide (classes model (prototype k)=classes model t)).length : Rat) else 0
def CU (s t : State) : Rat :=
  ((List.finRange 16).map fun k => C s k*U k t).sum
def epsilon (perturb : Bool) : Rat := if perturb then 1/16 else 0
def perturbed (perturb : Bool) (s t : State) : Rat :=
  (1-epsilon perturb)*P s t+epsilon perturb/32
def closure (perturb squared : Bool) : Matrix State :=
  ObjecthoodRules.product states
    (ObjecthoodRules.power states (perturbed perturb) (if squared then 2 else 1)) CU

theorem P_formula (s t : State) :
    P s t = if t.outside ∨ t.phase=s.phase then 0 else (weight s t.u t.v:Rat)/16 := by
  cases s with
  | mk p u v r phase =>
    cases t with
    | mk q x y replica tick =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;>
        cases q <;> cases x <;> cases y <;> cases replica <;> cases tick <;> decide +kernel

theorem fiber_count (p : State) :
    (states.filter fun t => decide (classes model p=classes model t)).length=2 := by
  simp only [first_profile_equation]
  cases p with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> decide +kernel

theorem prototype_code : ∀ k : Fin 16, classes model (prototype k)=k.val := by
  simp only [prototype,first_profile_equation,prototypes_formula]
  decide +kernel

theorem C_equation (s : State) (k : Fin 16) :
    C s k = if classes model s=k.val then 1 else 0 := by
  simp only [C,prototype_code]

theorem U_equation (k : Fin 16) (s : State) :
    U k s = if classes model s=k.val then 1/2 else 0 := by
  unfold U
  rw [fiber_count,prototype_code]
  by_cases h : classes model s=k.val <;> simp only [h,if_true,if_false] <;> decide +kernel

theorem CU_formula (s t : State) :
    CU s t = if eraseReplica s=eraseReplica t then 1/2 else 0 := by
  simp only [CU,C_equation,U_equation,first_profile_equation]
  cases s with
  | mk p u v r phase =>
    cases t with
    | mk q x y replica tick =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;>
        cases q <;> cases x <;> cases y <;> cases replica <;> cases tick <;> decide +kernel

theorem P_stochastic : (∀ s t, 0≤P s t) ∧ (∀ s, mass states (P s)=1) := by
  simp only [P_formula]
  constructor
  · intro s t
    cases s with
    | mk p u v r phase =>
      cases t with
      | mk q x y replica tick =>
        cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;>
          cases q <;> cases x <;> cases y <;> cases replica <;> cases tick <;> decide +kernel
  · intro s
    cases s with
    | mk p u v r phase =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> decide +kernel

theorem perturbed_positive (s t : State) : 0<perturbed true s t := by
  have h := P_stochastic.1 s t
  unfold perturbed epsilon
  grind


end CSTTT.FullNative.Objecthood
