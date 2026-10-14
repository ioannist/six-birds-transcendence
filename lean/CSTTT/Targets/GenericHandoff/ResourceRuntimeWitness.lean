import CSTTT.Targets.GenericHandoff.ResourceRuntime
import CSTTT.Targets.GenericHandoff.RegisterOperational

/-! Nonemptiness of the unrestricted resource COMPONENT, not a new FIACH
model or package claim. The rule is a deterministic maintenance action with
one paid/recharged resource and unit event advancement, as in the registered
G6 nominal ledger. Budget, cost, recharge and carrier identifiers are arbitrary
parameters. Solvency and conservation are proved premises, not flags. This
specialization is deliberately simple; unrestricted Raw permits nonconserved,
context-dependent prices and multiple resources. No completeness is claimed.
-/
namespace CSTTT.TargetTheory.GenericHandoff.ResourceRuntimeWitness
open RegisterInterpreter ResourceRuntime

abbrev Value : Bool → Type := fun b => if b then Withdrawal Unit else RegisterOperational.Finance
abbrev RV : Unit → Type := fun _ => Nat

def schema (source target : CarrierId) : Schema Unit Unit := ⟨[()],[()],source,target⟩

/-- Raw rule: the one declared response pays cost and receives recharge;
each successful nominal step advances each event counter by one. -/
def raw : ResourceRuntime.Raw Bool Value Unit RV Unit Unit Unit Unit Unit Unit where
  execution := {
    disturbances := [()]
    actions := [()]
    outcomes := [()]
    row := .literal [((),1)]
    program := fun _ => .map (· + 1) (.register ()) }
  accounts := .map (fun f : RegisterOperational.Finance =>
    fun _ => ⟨some f.owner,f.rechargeAvailable,f.budget⟩) (.cell false)
  required := .literal [()]
  charge := .map (fun f : RegisterOperational.Finance =>
    ⟨f.owner,[()],fun _ => f.cost,fun _ => f.recharge⟩) (.cell false)
  advances := .literal ⟨1,1,1,1⟩
  factor := .literal (some ())
  order := .register ()
  ticks := .register ()
  progress := .register ()
  record := .register ()
  writer := .literal true
  residue := .literal ()
  sourcePresent := .literal false
  withdrawal := ⟨true,id⟩

def assignment (target : CarrierId) (budget cost recharge : Nat) : Assignment Bool Value
  | false => some ⟨target,true,budget,cost,recharge⟩
  | true => some ⟨roles,fun _ => [],[],[()]⟩

theorem ready (target : CarrierId) (budget cost recharge : Nat) :
    Ready raw (assignment target budget cost recharge) := by
  refine ⟨?_,?_,?_⟩
  · intro k hk; cases k <;> rfl
  · intro reg k hk; simp [raw,Expr.dependencies] at hk
  · intro k hk; cases k <;> rfl

theorem actual_step (target : CarrierId) (budget cost recharge : Nat) (r : Registers Unit RV) :
    update raw (assignment target budget cost recharge) (ready target budget cost recharge) r () () () =
      fun _ => r () + 1 := by
  funext reg
  cases reg
  have he := checked_execute_eq raw.execution.program (assignment target budget cost recharge)
    (ready target budget cost recharge).2.1 r ((),(),()) ()
  simpa [execute,raw,Expr.eval] using Option.some.inj he.symm

/-- This constructs the invariant certificate from priced raw equations.
The auxiliary invariant is all runs in the enumerated one-factor kernel; it
stores no autonomy proof. Resource positivity and strict updates are substantive. -/
theorem certificate (source target : CarrierId)
    (budget cost recharge : Nat) (positive : budget > 0) (funded : cost ≤ budget)
    (conserved : budget - cost + recharge = budget) :
    Nonempty (Certificate (schema source target) raw (assignment target budget cost recharge)
      (ready target budget cost recharge) (fun r => r () = 0)) := by
  let a := assignment target budget cost recharge
  have res (r : Registers Unit RV) : ResourceClosed (schema source target) raw a r := by
    refine ⟨(fun _ => ⟨some target,true,budget⟩),[()],⟨roles,fun _ => [],[],[()]⟩,
      rfl,rfl,rfl,rfl,rfl,by simp,by simp,?_,by simp⟩
    intro resource hr
    exact ⟨rfl,rfl,positive⟩
  have legal (r : Registers Unit RV) : Legal (schema source target) raw a r () () := by
    refine ⟨by simp [raw],by simp [raw],(fun _ => ⟨some target,true,budget⟩),[()],
      ⟨target,[()],fun _ => cost,fun _ => recharge⟩,⟨roles,fun _ => [],[],[()]⟩,
      rfl,rfl,rfl,rfl,rfl,by simp,by simp,by simp,by simp [schema],?_⟩
    intro resource hr
    exact ⟨rfl,rfl,funded,by simpa [conserved] using positive⟩
  have step (r : Registers Unit RV) : StepLaw (schema source target) raw a
      (ready target budget cost recharge) r () () () := by
    refine ⟨res _,(fun _ => ⟨some target,true,budget⟩),(fun _ => ⟨some target,true,budget⟩),
      ⟨target,[()],fun _ => cost,fun _ => recharge⟩,⟨1,1,1,1⟩,r (),r (),r (),r (),
      rfl,rfl,rfl,rfl,by decide,by decide,by decide,by decide,?_,rfl,?_,rfl,?_,rfl,?_,rfl,?_,rfl⟩
    · intro resource hr; exact conserved.symm
    all_goals rw [actual_step]; rfl
  refine ⟨{ inside := fun r => r () ≥ 0
            withdrawn := ?_
            entriesNonempty := ⟨fun _ => 0,rfl⟩
            entriesInside := fun _ _ => Nat.zero_le _
            packageInside := ?_
            resourcesInside := fun r _ => res r
            response := ?_ }⟩
  · refine ⟨?_,?_⟩
    · refine ⟨by simp [schema],by simp [schema],by simp [raw],?_,?_,?_,?_,?_⟩
      all_goals intro u; cases u; simp [raw,schema]
    · refine ⟨⟨roles,fun _ => [],[],[()]⟩,rfl,?_,?_,?_,by simp,by simp [schema],by simp⟩
      · exact fun _ h => h
      · exact fun _ h => h
      · intro role hr; simp
  · intro r hr; exact ⟨(),by simp [schema],rfl⟩
  · intro r hr d; cases d
    refine ⟨(),legal r,?_,?_⟩
    · refine ⟨?_,by change (1 : Rat) + 0 = 1; exact Rat.add_zero 1,(),1,by simp [rows,raw,Expr.eval],by decide⟩
      intro e he
      simp [rows,raw,Expr.eval] at he
      subst e
      decide
    · intro o ho; cases o; exact ⟨Nat.zero_le _,step r⟩

/-- Zero funding cannot satisfy this priced component even though its factor
alphabet has one element and its auxiliary invariant is a full-kernel one. -/
theorem zero_budget_rejected (source target : CarrierId) (cost recharge : Nat)
    (r : Registers Unit RV) :
    ¬ ResourceClosed (schema source target) raw (assignment target 0 cost recharge) r :=
  depleted_required_rejected _ _ _ r _ [()] rfl rfl () (by simp) rfl

theorem capped_record_rejected (source target : CarrierId) (budget cost recharge cap : Nat)
    (r : Registers Unit RV) (hc : cap ≤ r ()) :
    ¬ StepLaw (schema source target) {raw with record := .map (min · cap) (.register ())}
      (assignment target budget cost recharge) (ready target budget cost recharge) r () () () := by
  apply nonadvancing_field_rejected _ _ _ _ r () () () .record cap cap
  · change some (min (r ()) cap) = some cap
    rw [Nat.min_eq_right hc]
  · change some (min ((update raw (assignment target budget cost recharge) (ready target budget cost recharge) r () () ()) ()) cap) = some cap
    rw [actual_step]
    simp only
    rw [Nat.min_eq_right (by omega)]
  · exact Nat.le_refl _

end CSTTT.TargetTheory.GenericHandoff.ResourceRuntimeWitness
