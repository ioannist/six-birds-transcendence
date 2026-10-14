import CSTTT.FullNative.HistoryFactor

/-! Actual funded cycle/provenance obligations for frozen FULL-NATIVE-01. -/
namespace CSTTT.FullNative.Credit
open AccountExecution PhysicalExecution SnapshotExecution
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 8000000

def cycle : List State := [⟨false,false,false,false,false⟩,⟨false,false,true,false,true⟩,
  ⟨false,true,true,false,false⟩,⟨false,false,false,false,true⟩,
  ⟨false,false,true,false,false⟩,⟨false,true,true,false,true⟩]

def edges (c : List State) : List (State × State) := c.zip (c.drop 1++c.take 1)

def edgeProb (s t : State) : Rat :=
  ((rationalRows model s false).map fun e => if e.1=t then e.2 else 0).sum

def product (c : List State) : Rat := ((edges c).map fun e => edgeProb e.1 e.2).foldl (·*·) 1

def reversed : List State := cycle.take 1++(cycle.drop 1).reverse

theorem actual_cycle_weights : (edges cycle).map (fun e => weight e.1 e.2.u e.2.v)=[3,3,2,3,3,2] := by
  decide +kernel

theorem actual_reverse_weights : (edges reversed).map (fun e => weight e.1 e.2.u e.2.v)=[1,2,3,1,2,3] := by
  decide +kernel

theorem cycle_supported : (edges cycle).all (fun e => decide
    ((e.2,weight e.1 e.2.u e.2.v)∈rows e.1 false ∧ 0<weight e.1 e.2.u e.2.v))=true := by
  decide +kernel

theorem reverse_supported : (edges reversed).all (fun e => decide
    ((e.2,weight e.1 e.2.u e.2.v)∈rows e.1 false ∧ 0<weight e.1 e.2.u e.2.v))=true := by
  decide +kernel

theorem directionality : product cycle=324/(16:Rat)^6 ∧ product reversed=36/(16:Rat)^6 ∧
    product cycle≠product reversed := by decide +kernel


open AccountExecution PhysicalExecution SnapshotExecution

end CSTTT.FullNative.Credit
