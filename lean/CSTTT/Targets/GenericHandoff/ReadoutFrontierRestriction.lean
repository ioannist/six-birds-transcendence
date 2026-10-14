import CSTTT.Targets.GenericHandoff.RegisterReadoutLaws

/-! Internal closure restriction engine. The new frontier is instantiated with
DEFINED acquisition roots, not accepted as a candidate at RawHandoff. Rows and
updater remain identical, including every actual outcome and unbounded run. -/
namespace CSTTT.TargetTheory.GenericHandoff.RegisterFuture
open RegisterInterpreter CSTTT.TransportTheory
variable {Cell R D A O P Residue Maintenance : Type} {Value : Cell → Type} {RV : R → Type}
    [DecidableEq O]

theorem closure_from_reached_roots
    (raw : Raw Cell Value R RV D A O P Residue Maintenance) (a : Assignment Cell Value)
    (h : RawReady raw a) (oldRoots newRoots : List (Registers R RV))
    (hr : ∀ r ∈ newRoots, Closure raw a h oldRoots r)
    (x : Registers R RV) (hx : Closure raw a h newRoots x) : Closure raw a h oldRoots x := by
  induction hx with
  | root x hm => exact hr x hm
  | step _ da o ho ih => exact FutureClosure.step ih da o ho

theorem restrict_readout_gate
    (raw : Raw Cell Value R RV D A O P Residue Maintenance)
    (law : StepRecipes Cell Value R RV D A O P Residue Maintenance)
    (a : Assignment Cell Value) (h : RawReady raw a) (oldRoots newRoots : List (Registers R RV))
    (gate : ReadoutLawGate raw law a h oldRoots) (nonempty : newRoots ≠ [])
    (hr : ∀ r ∈ newRoots, Closure raw a h oldRoots r) : ReadoutLawGate raw law a h newRoots := by
  refine ⟨gate.1,gate.2.1,gate.2.2.1,gate.2.2.2.1,nonempty,?_,?_⟩
  · intro x hx d hd act ha o ho
    exact gate.2.2.2.2.2.1 x (closure_from_reached_roots raw a h oldRoots newRoots hr x hx) d hd act ha o ho
  · intro x hx d hd act ha o hp
    exact gate.2.2.2.2.2.2 x (closure_from_reached_roots raw a h oldRoots newRoots hr x hx) d hd act ha o hp
end CSTTT.TargetTheory.GenericHandoff.RegisterFuture
