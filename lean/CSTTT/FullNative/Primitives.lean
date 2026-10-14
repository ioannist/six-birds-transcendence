import CSTTT.Targets.GenericHandoff.ProfileRules
import CSTTT.FullNative.WeightedFuture

/-! FULL-NATIVE-01, frozen by commit 9a194ea before evaluation.
All physical rows, including the resident clock phase and replica sampler,
come from that recipe. No terminal class, distribution or verdict is stored.
The 32-state carrier is the charge=true invariant account sector, not the
unbounded historical audit or environmental energy-stream carrier. -/
namespace CSTTT.FullNative
set_option autoImplicit false

structure State where
  outside : Bool
  u : Bool
  v : Bool
  replica : Bool
  phase : Bool
  deriving DecidableEq, Repr

def bits : List Bool := [false,true]
def kernels : List (Bool × Bool) := [(false,false),(false,true),(true,false),(true,true)]
def states : List State :=
  bits.flatMap fun p => bits.flatMap fun u => bits.flatMap fun v =>
    bits.flatMap fun r => bits.map fun phase => ⟨p,u,v,r,phase⟩
def bit (b : Bool) : Nat := if b then 1 else 0
def kernelCode (s : State) : Nat := 2*bit s.u + bit s.v
def publicLens (s : State) : Nat :=
  if s.outside then 1 + 2*kernelCode s + bit s.phase else 0

def diagonal (s : State) : Nat :=
  if s.u then (if s.v then 2 else 3) else (if s.v then 3 else 1)
def weight (s : State) (u v : Bool) : Nat :=
  if s.outside then 2 else if u = v then diagonal s else 4 - diagonal s

def rows (s : State) (a : Bool) : List (State × Nat) :=
  if a then [(⟨true,s.u,s.v,s.replica,!s.phase⟩,16)] else
    kernels.flatMap fun uv => bits.map fun r =>
      (⟨false,uv.1,uv.2,r,!s.phase⟩,weight s uv.1 uv.2)

structure Model where
  rows : State → Bool → List (State × Nat)
  publicLens : State → Nat

def model : Model := ⟨rows,publicLens⟩
def flatten (d : Model) : Model :=
  {d with rows := fun s a => if a then d.rows s a else
    kernels.flatMap fun uv => bits.map fun r =>
      (⟨false,uv.1,uv.2,r,!s.phase⟩,2)}

def rationalRows (d : Model) (s : State) (a : Bool) : List (State × Rat) :=
  (d.rows s a).map fun e => (e.1,(e.2 : Rat)/16)

/-- The old hazard-list predictor is deliberately not used as a full future
code. Weighted refinement uses the actual public seed and actual transitions.
The dormant legacy hazards field is required by the imported raw record type,
but is never read by seed/signature/step/iterate. -/
def profile (d : Model) : TargetTheory.GenericHandoff.ProfileRules.Raw State Bool State :=
  ⟨states,bits,d.rows,d.publicLens,(fun _ => false),some,(fun _ => 0),false,
    List.range 32,(⟨false,false,false,false,false⟩,⟨false,false,true,false,false⟩),
    (9,16,16),1⟩
def classes (d : Model) : State → Nat :=
  TargetTheory.GenericHandoff.ProfileRules.first (profile d)

end CSTTT.FullNative
