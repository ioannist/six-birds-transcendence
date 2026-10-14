import CSTTT.FullNative.IAPSAdjudication
import CSTTT.FullNative.InternalizedCredit
import CSTTT.FullNative.JointClaims
import CSTTT.Targets.GenericHandoff.NativeComposition.OriginalInterfaceObstruction

/-! G31a: parametric, disjoint legacy embedding. The old argument can be any
existing raw type, so the commuting laws cover heterogeneous old operators,
observers and predicates without replacing their definitions. -/
namespace CSTTT.FullNative02
set_option autoImplicit false

inductive Mode (Old New : Type) where
  | legacy : Old → Mode Old New
  | fullNative02 : New → Mode Old New

namespace Mode
variable {Old New A V : Type}

def operate (old : Old → A → Old) (new : New → A → New) : Mode Old New → A → Mode Old New
  | .legacy x, a => .legacy (old x a)
  | .fullNative02 x, a => .fullNative02 (new x a)

def observe (old : Old → V) (new : New → V) : Mode Old New → V
  | .legacy x => old x
  | .fullNative02 x => new x

def rows (old : Old → A → List (Old × Rat)) (new : New → A → List (New × Rat)) :
    Mode Old New → A → List (Mode Old New × Rat)
  | .legacy x, a => (old x a).map fun e => (.legacy e.1,e.2)
  | .fullNative02 x, a => (new x a).map fun e => (.fullNative02 e.1,e.2)

def protocol (run : New → Option New) : Mode Old New → Option (Mode Old New)
  | .legacy _ => none
  | .fullNative02 x => (run x).map .fullNative02

def predicate (old : Old → Prop) (new : New → Prop) : Mode Old New → Prop
  | .legacy x => old x
  | .fullNative02 x => new x

theorem operator_commutes (old : Old → A → Old) (new : New → A → New) (x : Old) (a : A) :
    operate old new (.legacy x) a = .legacy (old x a) := rfl

theorem observer_commutes (old : Old → V) (new : New → V) (x : Old) :
    observe old new (.legacy x) = old x := rfl

theorem rows_commute (old : Old → A → List (Old × Rat))
    (new : New → A → List (New × Rat)) (x : Old) (a : A) :
    rows old new (.legacy x) a = (old x a).map (fun e => (.legacy e.1,e.2)) := rfl

theorem legacy_closed (old : Old → A → List (Old × Rat))
    (new : New → A → List (New × Rat)) (x : Old) (a : A) (y : Mode Old New) (p : Rat)
    (h : (y,p) ∈ rows old new (.legacy x) a) : ∃ z, y = .legacy z := by
  obtain ⟨e,_,he⟩ := List.mem_map.mp h
  exact ⟨e.1,(congrArg Prod.fst he).symm⟩

theorem new_protocol_rejects_legacy (run : New → Option New) (x : Old) :
    protocol run (.legacy x) = none := rfl

theorem old_predicate_iff (old : Old → Prop) (new : New → Prop) (x : Old) :
    predicate old new (.legacy x) ↔ old x := Iff.rfl

/-- Applies equally to positive and negative old theorems at their complete
original quantifiers: instantiate Old with their argument tuple. -/
theorem declaration_preserved (old : Old → Prop) (new : New → Prop) (x : Old)
    (proof : old x) : predicate old new (.legacy x) := proof

theorem every_old_word_law [DecidableEq V]
    (old : Old → A → List (Old × Rat)) (new : New → A → List (New × Rat))
    (oldObserve : Old → V) (newObserve : New → V) (x : Old) (word : List A) (trace : List V) :
    FullNative.WeightedFuture.law (rows old new) (observe oldObserve newObserve)
      (.legacy x) word trace = FullNative.WeightedFuture.law old oldObserve x word trace := by
  induction word generalizing x trace with
  | nil => rfl
  | cons a rest ih =>
    cases trace with
    | nil => rfl
    | cons v tail =>
      simp only [FullNative.WeightedFuture.law,observe,rows,List.foldr_map,ih]

end Mode
end CSTTT.FullNative02
