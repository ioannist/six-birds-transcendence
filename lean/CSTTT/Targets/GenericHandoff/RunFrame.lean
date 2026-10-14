import CSTTT.Targets.GenericHandoff.RegisterInterpreter

/-! Exact register embedding in one typed run frame. This changes representation,
not dynamics: instructions retain their static dependencies and evaluate on the
decoded frame. It allows a raw acquisition updater to retain its carrier mode,
using source rows before reception and target rows afterwards. -/
namespace CSTTT.TargetTheory.GenericHandoff.RunFrame
open RegisterInterpreter

abbrev Values (State : Type) : Unit → Type := fun _ => State
def pack (s : State) : Registers Unit (Values State) := fun _ => s

variable {Cell R Env State X : Type} {Value : Cell → Type} {RV : R → Type}

def embed (decode : State → Registers R RV)
    {X : Type} (e : Expr Cell Value R RV Env X) : Expr Cell Value Unit (Values State) Env X :=
  match e with
  | .literal x => .literal x
  | .cell k => .cell k
  | .register r => .map (fun s => decode s r) (.register ())
  | .environment f => .environment f
  | .map f e => .map f (embed decode e)
  | .pair e f => .pair (embed decode e) (embed decode f)
  | .choose c e f => .choose (embed decode c) (embed decode e) (embed decode f)

theorem dependencies (decode : State → Registers R RV)
    (e : Expr Cell Value R RV Env X) : (embed decode e).dependencies = e.dependencies := by
  induction e <;> simp_all [embed,Expr.dependencies]

theorem evaluation (decode : State → Registers R RV)
    (e : Expr Cell Value R RV Env X) (a : Assignment Cell Value) (s : State) (env : Env) :
    (embed decode e).eval a (pack s) env = e.eval a (decode s) env := by
  induction e <;> simp_all [embed,Expr.eval,pack]

/-- Every consumed cell remains consumed, including unselected branches. -/
theorem missing (decode : State → Registers R RV)
    (e : Expr Cell Value R RV Env X) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ e.dependencies) (hm : a k = none) (s : State) (env : Env) :
    (embed decode e).eval a (pack s) env = none := by
  rw [evaluation]
  exact e.missing a k hk hm _ _

end CSTTT.TargetTheory.GenericHandoff.RunFrame
