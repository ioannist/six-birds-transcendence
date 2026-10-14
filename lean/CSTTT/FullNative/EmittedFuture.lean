import CSTTT.FullNative.SnapshotExecution

/-! Derived all-word and actual-execution obligations for frozen FULL-NATIVE-01. -/
namespace CSTTT.FullNative.Binding
set_option autoImplicit false
set_option maxHeartbeats 8000000

def emittedLaw {S : Type} (rs : S → Bool → List (S × Rat)) (observe : S → Nat) :
    S → List Bool → List Nat → Rat
  | _,[],[] => 1
  | _,[],_::_ => 0
  | _,_::_,[] => 0
  | s,a::as,o::os =>
    (rs s a).foldr (fun e acc => (if observe e.1=o then e.2*emittedLaw rs observe e.1 as os else 0)+acc) 0

theorem no_emissionsR {S : Type} (rs : List (S × Rat)) :
    rs.foldr (fun _ acc => (0:Rat)+acc) 0=0 := by
  induction rs with
  | nil => rfl
  | cons e rs ih => simp only [List.foldr_cons,ih];grind

theorem filtered_scaleR {S : Type} (rs : List (S × Rat)) (observe : S → Nat) (o : Nat) (n : Rat) :
    rs.foldr (fun e acc => (if observe e.1=o then e.2*n else 0)+acc) 0 =
      (rs.foldr (fun e acc => (if observe e.1=o then e.2 else 0)+acc) 0)*n := by
  induction rs with
  | nil => simp only [List.foldr_nil];grind
  | cons e rs ih =>
    simp only [List.foldr_cons,ih]
    by_cases h : observe e.1=o <;> simp only [h,if_true,if_false] <;> grind

theorem projected_emitted_law {S Q : Type} (rs : S → Bool → List (S × Rat))
    (observe : Q → Nat) (project : S → Q) (representative : Q → S)
    (aligned : ∀ s a, (rs s a).map (fun e => (project e.1,e.2))=
      WeightedFuture.projectedRows rs project representative (project s) a)
    (s : S) (word : List Bool) (outputs : List Nat) :
    emittedLaw rs (fun s => observe (project s)) s word outputs=
      emittedLaw (WeightedFuture.projectedRows rs project representative) observe (project s) word outputs := by
  induction word generalizing s outputs with
  | nil => cases outputs <;> rfl
  | cons a rest ih =>
    cases outputs with
    | nil => rfl
    | cons o os =>
      simp only [emittedLaw]
      rw [←aligned s a,List.foldr_map]
      congr 1
      funext e acc
      rw [ih e.1 os]

def independentLaw (rate : Bool → Nat → Rat) : List Bool → List Nat → Rat
  | [],[] => 1
  | [],_::_ => 0
  | _::_,[] => 0
  | a::as,o::os => rate a o*independentLaw rate as os

theorem constant_emitted_law {S : Type} (rs : S → Bool → List (S × Rat))
    (observe : S → Nat) (rate : Bool → Nat → Rat)
    (margins : ∀ s a o, (rs s a).foldr (fun e acc => (if observe e.1=o then e.2 else 0)+acc) 0=rate a o)
    (s : S) (word : List Bool) (outputs : List Nat) :
    emittedLaw rs observe s word outputs=independentLaw rate word outputs := by
  induction word generalizing s outputs with
  | nil => cases outputs <;> rfl
  | cons a rest ih =>
    cases outputs with
    | nil => rfl
    | cons o os => simp only [emittedLaw,ih,filtered_scaleR,margins,independentLaw]

end CSTTT.FullNative.Binding
