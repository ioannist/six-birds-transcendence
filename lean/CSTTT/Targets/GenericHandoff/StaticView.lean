import CSTTT.Targets.GenericHandoff.RegisterInitialization

/-! A static raw instruction can read several shared primitive cells without
reading a candidate run. It generalizes a one-cell projection, not a verdict. -/
namespace CSTTT.TargetTheory.GenericHandoff
open RegisterInterpreter RegisterInitialization

structure StaticView (Cell : Type) (Value : Cell → Type) (X : Type) where
  instruction : Expr Cell Value Empty NoValue Unit X

variable {Cell X : Type} {Value : Cell → Type}
def StaticView.read (v : StaticView Cell Value X) (a : Assignment Cell Value) : Option X :=
  v.instruction.eval a noRegisters ()
def StaticView.dependencies (v : StaticView Cell Value X) : List Cell := v.instruction.dependencies
def StaticView.ofCell (v : CellView Cell Value X) : StaticView Cell Value X :=
  ⟨.map v.project (.cell v.cell)⟩
theorem StaticView.ofCell_read (v : CellView Cell Value X) (a : Assignment Cell Value) :
    (StaticView.ofCell v).read a = v.read a := rfl
theorem StaticView.locality (v : StaticView Cell Value X) {a b : Assignment Cell Value}
    (h : Agrees v.dependencies a b) : v.read a = v.read b := v.instruction.locality h _ _
theorem StaticView.missing (v : StaticView Cell Value X) (a : Assignment Cell Value)
    (k : Cell) (hk : k ∈ v.dependencies) (hm : a k = none) : v.read a = none :=
  v.instruction.missing a k hk hm _ _
theorem StaticView.present (v : StaticView Cell Value X) (a : Assignment Cell Value)
    (h : Complete v.dependencies a) : ∃ x, v.read a = some x :=
  v.instruction.present_of_complete a h _ _
end CSTTT.TargetTheory.GenericHandoff
