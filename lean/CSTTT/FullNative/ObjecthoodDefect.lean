import CSTTT.FullNative.ObjecthoodBaseline

namespace CSTTT.FullNative.Objecthood
open CSTTT.TargetTheory.GenericHandoff FixedPointVerifier
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

/-! Algebraic audit formulas, proved equal to products of the actual frozen
transition matrix. They are derived acceleration certificates, never raw
transition data or post-evaluation primitives. The carrier retains phase. -/
def spatial (s : State) : Rat := if s.outside then 2 else (diagonal s:Rat)
def twoZero (s t : State) : Rat :=
  if t.outside ∨ t.phase≠s.phase then 0 else
  if t.u=t.v then (24-3*spatial s)/128 else (8+3*spatial s)/128
def fourZero (s t : State) : Rat :=
  if t.outside ∨ t.phase≠s.phase then 0 else
  if t.u=t.v then (1176-27*spatial s)/8192 else (872+27*spatial s)/8192
def uniformAfterOne (t : State) : Rat :=
  if t.outside then 0 else if t.u=t.v then 17/256 else 15/256
def uniformAfterTwo (t : State) : Rat :=
  if t.outside then 0 else if t.u=t.v then 141/2048 else 115/2048
def uniformAfterThree (t : State) : Rat :=
  if t.outside then 0 else if t.u=t.v then 1113/16384 else 935/16384
def two (perturb : Bool) (s t : State) : Rat :=
  let e := epsilon perturb
  let a := 1-e
  a*a*twoZero s t+e/32+e*a*uniformAfterOne t
def four (perturb : Bool) (s t : State) : Rat :=
  let e := epsilon perturb
  let a := 1-e
  a*a*a*a*fourZero s t+e/32+e*a*uniformAfterOne t+
    e*a*a*uniformAfterTwo t+e*a*a*a*uniformAfterThree t

theorem uniform_after_one :
    PositiveMatrix.push states P (fun _ => (1:Rat)/32) = uniformAfterOne := by
  funext s
  simp only [PositiveMatrix.push,dot,P_formula]
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> decide +kernel

theorem uniform_after_two : PositiveMatrix.push states P uniformAfterOne = uniformAfterTwo := by
  funext s
  simp only [PositiveMatrix.push,dot,P_formula]
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> decide +kernel

theorem uniform_after_three : PositiveMatrix.push states P uniformAfterTwo = uniformAfterThree := by
  funext s
  simp only [PositiveMatrix.push,dot,P_formula]
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> decide +kernel

theorem two_equation (perturb : Bool) :
    ObjecthoodRules.product states (perturbed perturb) (perturbed perturb) = two perturb := by
  funext s t
  simp only [ObjecthoodRules.product,perturbed,P_formula]
  cases s with
  | mk p u v r phase =>
    cases t with
    | mk q x y replica tick =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;>
        cases q <;> cases x <;> cases y <;> cases replica <;> cases tick <;> cases perturb <;> decide +kernel

theorem four_equation (perturb : Bool) :
    ObjecthoodRules.product states (two perturb) (two perturb) = four perturb := by
  funext s t
  cases s with
  | mk p u v r phase =>
    cases t with
    | mk q x y replica tick =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;>
        cases q <;> cases x <;> cases y <;> cases replica <;> cases tick <;> cases perturb <;> decide +kernel

theorem closure_one (perturb : Bool) : closure perturb false = perturbed perturb := by
  rw [closure_power]
  simp only [Bool.false_eq_true,if_false,ObjecthoodRules.power]
  exact PositiveMatrix.product_identity_left states state_domain.1 state_mem _

theorem closure_two (perturb : Bool) : closure perturb true = two perturb := by
  rw [closure_power]
  simp only [if_true,ObjecthoodRules.power]
  rw [PositiveMatrix.product_identity_left states state_domain.1 state_mem _,two_equation]

def absRat (x : Rat) : Rat := if x<0 then -x else x
def defect (perturb squared : Bool) : Rat :=
  (states.map fun s => (mass states fun t =>
    absRat (ObjecthoodRules.product states (closure perturb squared) (closure perturb squared) s t-
      closure perturb squared s t))/2).foldl max 0

theorem exact_defect (perturb squared : Bool) :
    defect perturb squared = if perturb then
      (if squared then 30675375/268435456 else 465/512)
      else (if squared then 195/2048 else 1) := by
  unfold defect
  cases squared
  · rw [closure_one,two_equation]
    simp only [P_formula,perturbed]
    cases perturb <;> decide +kernel
  · rw [closure_two,four_equation]
    cases perturb <;> decide +kernel

def coreUniform (s : State) : Rat := if s.outside then 0 else 1/16
def stationaryTV (perturb : Bool) : Rat :=
  (mass states fun s => absRat (stationary perturb s-coreUniform s))/2

theorem exact_stationaryTV (perturb : Bool) :
    stationaryTV perturb = if perturb then 319/5536 else 1/22 := by
  cases perturb <;> decide +kernel

end CSTTT.FullNative.Objecthood
