import CSTTT.FullNative.ObjecthoodPrimitives
import CSTTT.FullNative.PositiveMatrix

namespace CSTTT.FullNative.Objecthood
open CSTTT.TargetTheory.GenericHandoff
open FixedPointVerifier
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

def stationary (perturb : Bool) (s : State) : Rat :=
  if s.outside then epsilon perturb/32 else
  if s.u=s.v then (if perturb then 1457/22144 else 3/44)
  else (if perturb then 2449/44288 else 5/88)

theorem stationary_probability (perturb : Bool) : Probability states (stationary perturb) := by
  constructor
  · intro s
    cases s with
    | mk p u v r phase =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases perturb <;> decide +kernel
  · cases perturb <;> decide +kernel

theorem stationary_nonuniform (perturb : Bool) : stationary perturb≠(fun _ => (1:Rat)/32) := by
  intro h
  have hs := congrFun h (⟨true,false,false,false,false⟩:State)
  cases perturb with
  | false => exact (by decide +kernel : stationary false ⟨true,false,false,false,false⟩≠(1:Rat)/32) hs
  | true => exact (by decide +kernel : stationary true ⟨true,false,false,false,false⟩≠(1:Rat)/32) hs

theorem stationary_one_step (perturb : Bool) : Fixed states (perturbed perturb) (stationary perturb) := by
  intro s
  simp only [FixedPointVerifier.dot,perturbed,P_formula]
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases perturb <;> decide +kernel

theorem transition_exposure (perturb : Bool) :
    ObjecthoodRules.product states (perturbed perturb) CU = perturbed perturb := by
  funext s t
  simp only [ObjecthoodRules.product,perturbed,P_formula,CU_formula]
  cases s with
  | mk p u v r phase =>
    cases t with
    | mk q x y replica tick =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;>
        cases q <;> cases x <;> cases y <;> cases replica <;> cases tick <;> cases perturb <;> decide +kernel

theorem closure_power (perturb squared : Bool) :
    closure perturb squared = ObjecthoodRules.power states (perturbed perturb) (if squared then 2 else 1) := by
  unfold closure
  have h := PositiveMatrix.product_identity_left states state_domain.1 state_mem (perturbed perturb)
  cases squared <;> simp only [Bool.false_eq_true,if_false,if_true,ObjecthoodRules.power]
  · rw [h,transition_exposure]
  · rw [h,PositiveMatrix.product_assoc,transition_exposure]

theorem stationary_closure (perturb squared : Bool) :
    Fixed states (closure perturb squared) (stationary perturb) := by
  rw [closure_power]
  exact PositiveMatrix.fixed_power states state_domain.1 state_mem _ _ (stationary_one_step perturb) _

theorem perturbed_closure_positive (squared : Bool) :
    ∀ s t, 0<closure true squared s t := by
  rw [closure_power]
  have h := PositiveMatrix.product_identity_left states state_domain.1 state_mem (perturbed true)
  cases squared <;> simp only [Bool.false_eq_true,if_false,if_true,ObjecthoodRules.power]
  · rw [h]
    exact perturbed_positive
  · rw [h]
    exact PositiveMatrix.positive_product states state_mem _ _ perturbed_positive
      (fun s t => Rat.le_of_lt (perturbed_positive s t)) (fun t => perturbed_positive t t)

theorem perturbed_stationary_unique (squared : Bool) (x : Vector State)
    (probability : Probability states x) (fixed : Fixed states (closure true squared) x) :
    x=stationary true := by
  apply PositiveMatrix.positive_stationary_unique states (by decide) state_mem (closure true squared)
    (stationary true) x (perturbed_closure_positive squared)
  · intro s
    cases s with
    | mk p u v r phase =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> decide +kernel
  · exact (stationary_probability true).2
  · exact probability.2
  · exact stationary_closure true squared
  · exact fixed

def core : List State := states.filter fun s => !s.outside

theorem core_closed (s : State) (t : State) (edge : 0<P s t) : t∈core := by
  have outside : t.outside=false := by
    cases h : t.outside with
    | false => rfl
    | true =>
      have hz : P s t=0 := by simp [P_formula,h]
      rw [hz] at edge
      exact False.elim ((by decide : ¬(0:Rat)<0) edge)
  simp [core,state_mem,outside]

theorem retention (perturb : Bool) :
    mass core (stationary perturb) = (if perturb then 31/32 else 1) ∧
    (15:Rat)/16 ≤ mass core (stationary perturb) := by
  cases perturb <;> decide +kernel

def phaseLaw (phase : Bool) (s : State) : Rat :=
  if s.phase=phase then 2*stationary false s else 0

theorem phase_probability (phase : Bool) : Probability states (phaseLaw phase) := by
  constructor
  · intro s
    cases s with
    | mk p u v r tick =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases tick <;> cases phase <;> decide +kernel
  · cases phase <;> decide +kernel

theorem phase_step (phase : Bool) : PositiveMatrix.push states P (phaseLaw phase) = phaseLaw (!phase) := by
  funext s
  simp only [PositiveMatrix.push,dot,P_formula]
  cases s with
  | mk p u v r tick =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases tick <;> cases phase <;> decide +kernel

theorem unperturbed_eq : perturbed false=P := by
  funext s t
  change (1-(0:Rat))*P s t+0/32=P s t
  have hz : (0:Rat)/32=0 := by decide +kernel
  rw [hz]
  grind

theorem phase_fixed_squared (phase : Bool) : Fixed states (closure false true) (phaseLaw phase) := by
  rw [closure_power,unperturbed_eq]
  simp only [if_true,ObjecthoodRules.power]
  rw [PositiveMatrix.product_identity_left states state_domain.1 state_mem P]
  intro s
  change (PositiveMatrix.push states (ObjecthoodRules.product states P P) (phaseLaw phase)) s=phaseLaw phase s
  rw [PositiveMatrix.push_product,phase_step,phase_step]
  simp

theorem squared_unperturbed_nonunique :
    Probability states (phaseLaw false) ∧ Probability states (phaseLaw true) ∧
    Fixed states (closure false true) (phaseLaw false) ∧
    Fixed states (closure false true) (phaseLaw true) ∧ phaseLaw false≠phaseLaw true := by
  refine ⟨phase_probability false,phase_probability true,phase_fixed_squared false,
    phase_fixed_squared true,?_⟩
  intro h
  have hs := congrFun h FullInterface.rootState
  exact (by decide +kernel : phaseLaw false FullInterface.rootState≠phaseLaw true FullInterface.rootState) hs

end CSTTT.FullNative.Objecthood
