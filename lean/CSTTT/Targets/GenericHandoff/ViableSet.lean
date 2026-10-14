import CSTTT.Core.Finite

/-! G6d-1b: finite viable-set engine. It reads a raw retention function; a
monotonicity proof is required, never an asserted greatest-set verdict. This
module makes NO run-to-factor claim. Such a lift must be proved separately. -/
namespace CSTTT.TargetTheory.GenericHandoff.ViableSet
variable {X : Type} [DecidableEq X]

def subsets : List X → List (List X)
  | [] => [[]]
  | x :: rest => subsets rest ++ (subsets rest).map (x :: ·)
def Viable (retain : List X → X → Bool) (S : List X) : Prop :=
  ∀ x ∈ S, retain S x = true
def Monotone (retain : List X → X → Bool) : Prop :=
  ∀ {A B : List X}, A ⊆ B → ∀ x, retain A x = true → retain B x = true
def prune (retain : List X → X → Bool) (S : List X) := S.filter (retain S)
def greatest (carrier : List X) (retain : List X → X → Bool) :=
  carrier.filter fun x => (subsets carrier).any fun S =>
    decide (x ∈ S) && S.all (retain S)

omit [DecidableEq X] in
theorem prune_mono (retain : List X → X → Bool) (hm : Monotone retain)
    {A B : List X} (hAB : A ⊆ B) : prune retain A ⊆ prune retain B := by
  intro x hx
  obtain ⟨ha,hr⟩ := List.mem_filter.mp hx
  exact List.mem_filter.mpr ⟨hAB ha,hm hAB x hr⟩

omit [DecidableEq X] in
theorem filter_mem_subsets (p : X → Bool) (xs : List X) : xs.filter p ∈ subsets xs := by
  induction xs with
  | nil => simp [subsets]
  | cons x xs ih => cases h : p x <;> simp [h,subsets,ih]

theorem member_greatest (carrier : List X) (hc : ∀ x, x ∈ carrier)
    (retain : List X → X → Bool) (x : X) :
    x ∈ greatest carrier retain ↔ ∃ S ∈ subsets carrier, x ∈ S ∧ Viable retain S := by
  simp [greatest,List.mem_filter,hc x,List.any_eq_true,Bool.and_eq_true,Viable,List.all_eq_true]

theorem greatest_contains_viable (carrier : List X) (hc : ∀ x, x ∈ carrier)
    (retain : List X → X → Bool) (hm : Monotone retain)
    (S : List X) (hv : Viable retain S) : S ⊆ greatest carrier retain := by
  let normalized := carrier.filter (fun x => decide (x ∈ S))
  have he : ∀ x, x ∈ normalized ↔ x ∈ S := by intro x; simp [normalized,hc x]
  have hn : Viable retain normalized := by
    intro x hx
    exact hm (fun _ ht => (he _).mpr ht) x (hv x ((he x).mp hx))
  intro x hx
  exact (member_greatest carrier hc retain x).mpr
    ⟨normalized,filter_mem_subsets _ carrier,(he x).mpr hx,hn⟩

theorem greatest_viable (carrier : List X) (hc : ∀ x, x ∈ carrier)
    (retain : List X → X → Bool) (hm : Monotone retain) :
    Viable retain (greatest carrier retain) := by
  intro x hx
  obtain ⟨S,_,hs,hv⟩ := (member_greatest carrier hc retain x).mp hx
  exact hm (greatest_contains_viable carrier hc retain hm S hv) x (hv x hs)

theorem greatest_fixed (carrier : List X) (hc : ∀ x, x ∈ carrier)
    (retain : List X → X → Bool) (hm : Monotone retain) :
    prune retain (greatest carrier retain) = greatest carrier retain :=
  List.filter_eq_self.mpr (greatest_viable carrier hc retain hm)

theorem no_viable_member_empty (carrier : List X) (hc : ∀ x, x ∈ carrier)
    (retain : List X → X → Bool) (hm : Monotone retain)
    (h : ∀ S x, retain S x = false) : greatest carrier retain = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have hv := greatest_viable carrier hc retain hm x hx
  rw [h] at hv
  contradiction
end CSTTT.TargetTheory.GenericHandoff.ViableSet
