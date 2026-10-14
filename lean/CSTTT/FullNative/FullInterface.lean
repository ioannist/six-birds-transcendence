import CSTTT.FullNative.PhysicalFuture
import CSTTT.Targets.GenericHandoff.TemporalFactorFuture

/-! The complete original eight-role observation, with explicit (stronger)
behavioral predictive extraction. This module interprets the canonical funded
local-generator sector and matched history contexts. Its account/receipt
simulation in the larger physical execution is a separate required bridge;
no free funding or historical-validity claim follows from these algebraic laws.
-/
namespace CSTTT.FullNative.FullInterface
open TargetTheory.GenericHandoff
set_option autoImplicit false

structure Context where
  order : Nat
  localRecords : Nat
  rootedRoute : List State × List Nat
  charge : Bool
  owner : Fin 3
  deriving DecidableEq, Repr

structure Run where
  current : State
  context : Context
  deriving DecidableEq, Repr

def advanceContext (c : Context) : Context :=
  {c with order := c.order+1, localRecords := c.localRecords+1}

def advance (r : Run) (s : State) : Run := ⟨s,advanceContext r.context⟩

def rows (r : Run) (a : Bool) : List (Run × Rat) :=
  if r.context.charge then
    (rationalRows model r.current a).map fun e => (advance r e.1,e.2)
  else []

/-- Exact type of the original full temporal observation. The predictive
value changes extraction explicitly; all eight original roles remain. -/
def observe (r : Run) : TemporalFactorRules.Observation State State Nat (Fin 3) :=
  ⟨.inl (classes model r.current,[]),r.context.order,bit r.current.phase,
    r.context.order,r.context.localRecords,r.context.rootedRoute,
    r.context.charge,r.context.owner⟩

def code (r : Run) : Nat × Context := ⟨classes model r.current,r.context⟩
def project (r : Run) : Shape × Context := ⟨eraseReplica r.current,r.context⟩
def representative (q : Shape × Context) : Run :=
  ⟨FullNative.representative q.1,q.2⟩

theorem projected_rows (r : Run) (a : Bool) :
    (rows r a).map (fun e => (project e.1,e.2)) =
      WeightedFuture.projectedRows rows project representative (project r) a := by
  by_cases charged : r.context.charge = true
  · have hp := congrArg (fun rs : List (Shape × Rat) =>
        rs.map fun e => ((e.1,advanceContext r.context),e.2))
      (FullNative.projected_rows r.current a)
    simpa [rows,charged,WeightedFuture.projectedRows,project,representative,
      advance,List.map_map,Function.comp_def] using hp
  · have hc : r.context.charge = false := Bool.eq_false_iff.mpr charged
    simp [rows,hc,WeightedFuture.projectedRows,project,representative]

theorem observation_projection :
    observe = fun r => observe (representative (project r)) := by
  funext r
  simp only [observe,first_profile_equation]
  rfl

theorem code_projection_exact (r s : Run) : code r = code s ↔ project r = project s := by
  simp only [code,project,Prod.mk.injEq,classes_shape_exact]

theorem all_words (r s : Run) (same : code r = code s)
    (word : List Bool)
    (trace : List (TemporalFactorRules.Observation State State Nat (Fin 3))) :
    WeightedFuture.law rows observe r word trace = WeightedFuture.law rows observe s word trace := by
  rw [observation_projection]
  exact WeightedFuture.equal_projection_all_words rows (fun q => observe (representative q))
    project representative projected_rows r s ((code_projection_exact r s).mp same) word trace

theorem matched_full_future_exact (r s : Run) (context : r.context = s.context) :
    (∀ word trace, WeightedFuture.law rows observe r word trace =
      WeightedFuture.law rows observe s word trace) ↔
      classes model r.current = classes model s.current := by
  constructor
  · intro laws
    have witness := laws [] [observe r]
    have obs : observe r = observe s := by
      by_cases h : observe r = observe s
      · exact h
      · simp [WeightedFuture.law,h] at witness
    have h := congrArg TemporalFactorRules.Observation.predictive obs
    exact congrArg (fun x => x.1) (Sum.inl.inj h)
  · intro same
    exact all_words r s (by simp [code,same,context])

/-- Every changing role is fixed by an actual native row/update equation;
the resident phase equation uses supported raw transitions. -/
theorem supported_update (r : Run) (a : Bool) (s : State) (n : Nat)
    (supported : (s,n) ∈ FullNative.rows r.current a) :
    (observe (advance r s)).order = (observe r).order+1 ∧
    (observe (advance r s)).tickPhase = bit (!r.current.phase) ∧
    (observe (advance r s)).progress = (observe r).progress+1 ∧
    (observe (advance r s)).record = (observe r).record+1 ∧
    (observe (advance r s)).residue = (observe r).residue ∧
    (observe (advance r s)).maintenance = (observe r).maintenance ∧
    (observe (advance r s)).owner = (observe r).owner := by
  refine ⟨rfl,?_,rfl,rfl,rfl,rfl,rfl⟩
  change bit s.phase = bit (!r.current.phase)
  rw [supported_phase r.current a s n supported]

theorem disabled_rows (r : Run) (a : Bool) (disabled : r.context.charge = false) :
    rows r a = [] := by simp [rows,disabled]

def rootState : State := ⟨false,false,false,false,false⟩
def replicaLeft : State := ⟨false,false,false,false,true⟩
def replicaRight : State := ⟨false,false,false,true,true⟩

/-- Same rooted context, same elapsed order and record count, two actual
positive successors. The replica fiber is reachable, not an impossible pair
of histories with differing immutable roots. The physical transaction bridge
must still establish that this funded-sector row is enabled in execution. -/
theorem reachable_replica_fiber (c : Context) (charged : c.charge = true) :
    let root : Run := ⟨rootState,c⟩
    let left := advance root replicaLeft
    let right := advance root replicaRight
    (left,(1:Rat)/16) ∈ rows root false ∧
    (right,(1:Rat)/16) ∈ rows root false ∧
    left ≠ right ∧ left.context = right.context ∧ code left = code right := by
  dsimp only
  refine ⟨?_,?_,?_,rfl,?_⟩
  · simp [rows,charged,rationalRows,model,FullNative.rows,kernels,bits,
      weight,diagonal,rootState,replicaLeft,advance]
  · simp [rows,charged,rationalRows,model,FullNative.rows,kernels,bits,
      weight,diagonal,rootState,replicaRight,advance]
  · intro h
    have bad := congrArg (fun r : Run => r.current.replica) h
    contradiction
  · simp only [code,advance,first_profile_equation]
    rfl

end CSTTT.FullNative.FullInterface
