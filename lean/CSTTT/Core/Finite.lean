import Std

namespace CSTTT

universe u v

/-- An explicit finite presentation used instead of importing a larger finite-type library. -/
structure FiniteEnum (α : Type u) where
  elems : List α
  complete : ∀ x : α, x ∈ elems

/-- A binary relation with separately typed domain and codomain. -/
def HRel (α : Type u) (β : Type v) := α → β → Prop

/-- Pointwise relation between lists of the same length. -/
inductive ListForall₂ {α : Type u} {β : Type v}
    (relation : α → β → Prop) : List α → List β → Prop where
  | nil : ListForall₂ relation [] []
  | cons {a : α} {b : β} {as : List α} {bs : List β} :
      relation a b → ListForall₂ relation as bs →
      ListForall₂ relation (a :: as) (b :: bs)

/-- A token with a stable machine identifier and a human-readable label. -/
structure NamedToken where
  code : Nat
  label : String
  deriving DecidableEq, Repr

/-- A trace whose nonemptiness is carried by construction. -/
structure NonemptyTrace (α : Type u) where
  first : α
  rest : List α

namespace NonemptyTrace

def toList (t : NonemptyTrace α) : List α := t.first :: t.rest

end NonemptyTrace

end CSTTT
