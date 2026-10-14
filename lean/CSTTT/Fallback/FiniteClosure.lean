import CSTTT.Core.Finite

namespace CSTTT.FallbackTheory.FiniteClosure
variable {A : Type}
-- Class (b): pointwise inclusion of executable finite relations.
def Below (p q : A → Bool) : Prop := ∀ x, p x=true → q x=true
-- Class (b): raw operator iteration, with no supplied fixed point.
def iterate (next : (A → Bool) → A → Bool) (seed : A → Bool) : Nat → A → Bool
  | 0 => seed
  | n+1 => next (iterate next seed n)
-- Class (b): canonical finite presentation of an actual computed relation.
def present (frame : CSTTT.FiniteEnum A) (p : A → Bool) : List A := frame.elems.filter p
-- Class (b): finite presentation detects equality of every actual relation bit.
theorem presentation_injective (frame : CSTTT.FiniteEnum A) : Function.Injective (present frame) := by
  intro p q equal
  funext x
  have hp : x∈present frame p ↔ p x=true := by simp [present,frame.complete x]
  have hq : x∈present frame q ↔ q x=true := by simp [present,frame.complete x]
  have same : p x=true ↔ q x=true := hp.symm.trans (equal ▸ hq)
  exact Bool.eq_iff_iff.mpr same
-- Class (b): inclusion yields an actual sublist in the common raw finite ordering.
theorem below_sublist (frame : CSTTT.FiniteEnum A) (p q : A → Bool) (below : Below p q) :
    List.Sublist (present frame p) (present frame q) := by
  apply List.sublist_filter_iff.mpr
  refine ⟨present frame p,List.filter_sublist,?_⟩
  symm
  apply List.filter_eq_self.mpr
  intro x member
  exact below x (List.mem_filter.mp member).2
-- Class (b): genuine relation growth forces strict finite cardinal growth, even with repeated enum entries.
theorem strict_growth (frame : CSTTT.FiniteEnum A) (p q : A → Bool)
    (below : Below p q) (different : p≠q) : (present frame p).length < (present frame q).length := by
  have sub := below_sublist frame p q below
  have le := sub.length_le
  apply Classical.byContradiction
  intro h
  have eq := sub.eq_of_length (by omega)
  exact different (presentation_injective frame eq)
-- Class (b): one computed fixed point makes every subsequent iterate identical.
theorem fixed_tail (next : (A → Bool) → A → Bool) (seed : A → Bool) (n : Nat)
    (fixed : next (iterate next seed n)=iterate next seed n) :
    ∀ extra, iterate next seed (n+extra)=iterate next seed n := by
  intro extra
  induction extra with
  | zero => simp
  | succ extra ih => simpa [Nat.add_succ,iterate,ih] using fixed
-- Class (b): an inflationary executable operator reaches a computed fixed point in at most raw enum length steps.
theorem finite_fixed_exists (frame : CSTTT.FiniteEnum A) (next : (A → Bool) → A → Bool)
    (seed : A → Bool) (inflation : ∀ p, Below p (next p)) :
    ∃ n, n≤frame.elems.length ∧ next (iterate next seed n)=iterate next seed n := by
  apply Classical.byContradiction
  intro absent
  have different : ∀ n, n≤frame.elems.length → iterate next seed n≠next (iterate next seed n) := by
    intro n bound equal
    exact absent ⟨n,bound,equal.symm⟩
  have growth : ∀ n, n≤frame.elems.length+1 → n≤(present frame (iterate next seed n)).length := by
    intro n
    induction n with
    | zero => intro _; omega
    | succ n ih =>
      intro bound
      have prior := ih (by omega)
      have strict := strict_growth frame (iterate next seed n) (next (iterate next seed n))
        (inflation _) (different n (by omega))
      change n+1≤(present frame (next (iterate next seed n))).length
      omega
  have tooMany := growth (frame.elems.length+1) (by omega)
  have finiteBound := List.length_filter_le (p := iterate next seed (frame.elems.length+1)) (l := frame.elems)
  unfold present at tooMany
  omega
-- Class (b): the specific enum-length iterate is fixed, not an opaque selected witness.
theorem enum_length_fixed (frame : CSTTT.FiniteEnum A) (next : (A → Bool) → A → Bool)
    (seed : A → Bool) (inflation : ∀ p, Below p (next p)) :
    next (iterate next seed frame.elems.length)=iterate next seed frame.elems.length := by
  obtain ⟨n,bound,fixed⟩ := finite_fixed_exists frame next seed inflation
  have same := fixed_tail next seed n fixed (frame.elems.length-n)
  have index : n+(frame.elems.length-n)=frame.elems.length := by omega
  rw [index] at same
  rw [same]
  exact fixed
-- Class (b): monotone raw operators keep every iterate inside every closed upper relation containing the seed.
theorem iterate_least (next : (A → Bool) → A → Bool) (seed upper : A → Bool)
    (monotone : ∀ p q, Below p q → Below (next p) (next q))
    (seedBelow : Below seed upper) (closed : Below (next upper) upper) :
    ∀ n, Below (iterate next seed n) upper := by
  intro n
  induction n with
  | zero => exact seedBelow
  | succ n ih =>
    intro x member
    exact closed x (monotone _ _ ih x member)
-- Class (b): explicit finite closure is the computed bounded iterate.
def closure (frame : CSTTT.FiniteEnum A) (next : (A → Bool) → A → Bool) (seed : A → Bool) : A → Bool :=
  iterate next seed frame.elems.length
-- Class (b): explicit bounded closure is a least fixed point under raw monotonicity/inflation premises.
theorem closure_least_fixed (frame : CSTTT.FiniteEnum A) (next : (A → Bool) → A → Bool)
    (seed : A → Bool) (inflation : ∀ p, Below p (next p))
    (monotone : ∀ p q, Below p q → Below (next p) (next q)) :
    next (closure frame next seed)=closure frame next seed ∧
      ∀ upper, Below seed upper → Below (next upper) upper → Below (closure frame next seed) upper := by
  exact ⟨enum_length_fixed frame next seed inflation,fun upper hs hc => iterate_least next seed upper monotone hs hc _⟩
end CSTTT.FallbackTheory.FiniteClosure

namespace CSTTT.FallbackTheory.FiniteHorn
open CSTTT.FallbackTheory.FiniteClosure
variable {A : Type} [DecidableEq A]
-- Class (b): a declared finite Horn instruction; no ancestry or final verdict field.
structure Rule (A : Type) where
  prerequisites : List A
  conclusion : A
-- Class (b): executable guard and existing predecessors are required; empty-premise rules never fire.
def fires (enabled : Rule A → Bool) (p : A → Bool) (rule : Rule A) : Bool :=
  decide (rule.prerequisites≠[]) && enabled rule && rule.prerequisites.all p
-- Class (b): computed inflationary rule application retains seeds and prior relation members.
def gamma (seed : A → Bool) (rules : List (Rule A)) (enabled : Rule A → Bool)
    (p : A → Bool) (x : A) : Bool :=
  seed x || p x || rules.any (fun rule => decide (rule.conclusion=x) && fires enabled p rule)
-- Class (b): exact every-assignment rule firing equivalence.
theorem fires_iff (enabled : Rule A → Bool) (p : A → Bool) (rule : Rule A) :
    fires enabled p rule=true ↔ rule.prerequisites≠[] ∧ enabled rule=true ∧ ∀ a∈rule.prerequisites, p a=true := by
  simp [fires,List.all_eq_true,and_assoc]
-- Class (b): exact every-assignment Gamma expansion with no supplied output relation.
theorem gamma_iff (seed : A → Bool) (rules : List (Rule A)) (enabled : Rule A → Bool)
    (p : A → Bool) (x : A) :
    gamma seed rules enabled p x=true ↔ seed x=true ∨ p x=true ∨
      ∃ rule∈rules, rule.conclusion=x ∧ rule.prerequisites≠[] ∧ enabled rule=true ∧
        ∀ a∈rule.prerequisites, p a=true := by
  simp [gamma,List.any_eq_true,fires_iff,or_assoc]
-- Class (b): actual Gamma is inflationary without a hypothesis on raw rule guards.
theorem gamma_inflation (seed : A → Bool) (rules : List (Rule A)) (enabled : Rule A → Bool) :
    ∀ p, Below p (gamma seed rules enabled p) := by
  intro p x member
  exact (gamma_iff seed rules enabled p x).mpr (Or.inr (Or.inl member))
-- Class (b): actual finite rule Gamma is monotone in its predecessor relation.
theorem gamma_monotone (seed : A → Bool) (rules : List (Rule A)) (enabled : Rule A → Bool) :
    ∀ p q, Below p q → Below (gamma seed rules enabled p) (gamma seed rules enabled q) := by
  intro p q below x member
  rcases (gamma_iff seed rules enabled p x).mp member with seeded|previous|⟨rule,mem,conclusion,nonempty,guard,predecessors⟩
  · exact (gamma_iff seed rules enabled q x).mpr (Or.inl seeded)
  · exact (gamma_iff seed rules enabled q x).mpr (Or.inr (Or.inl (below x previous)))
  · exact (gamma_iff seed rules enabled q x).mpr
      (Or.inr (Or.inr ⟨rule,mem,conclusion,nonempty,guard,fun a ha => below a (predecessors a ha)⟩))
-- Class (b): every genuinely new nonseed Gamma member has an actual already-related predecessor.
theorem gamma_no_ex_nihilo (seed : A → Bool) (rules : List (Rule A)) (enabled : Rule A → Bool)
    (p : A → Bool) (x : A) (member : gamma seed rules enabled p x=true)
    (notSeed : seed x=false) (notPrevious : p x=false) :
    ∃ rule∈rules, rule.conclusion=x ∧ enabled rule=true ∧ ∃ predecessor∈rule.prerequisites, p predecessor=true := by
  rcases (gamma_iff seed rules enabled p x).mp member with h|h|⟨rule,mem,conclusion,nonempty,guard,all⟩
  · simp [notSeed] at h
  · simp [notPrevious] at h
  · obtain ⟨a,tail,eq⟩ := List.exists_cons_of_ne_nil nonempty
    refine ⟨rule,mem,conclusion,guard,a,?_,all a ?_⟩ <;> simp [eq]
-- Class (b): actual Horn ancestry is computed by the raw finite bound; no arbitrary fixed-point field is accepted.
def ancestry (frame : CSTTT.FiniteEnum A) (seed : A → Bool) (rules : List (Rule A))
    (enabled : Rule A → Bool) : A → Bool := closure frame (gamma seed rules enabled) seed
-- Class (b): actual Horn ancestry stabilizes and is the least closed relation containing the computed seed.
theorem ancestry_least_fixed (frame : CSTTT.FiniteEnum A) (seed : A → Bool) (rules : List (Rule A))
    (enabled : Rule A → Bool) :
    gamma seed rules enabled (ancestry frame seed rules enabled)=ancestry frame seed rules enabled ∧
      ∀ upper, Below seed upper → Below (gamma seed rules enabled upper) upper →
        Below (ancestry frame seed rules enabled) upper :=
  closure_least_fixed frame _ seed (gamma_inflation seed rules enabled) (gamma_monotone seed rules enabled)
-- Class (b): genuine computed seeds are retained by every raw iteration and the final ancestry.
theorem ancestry_contains_seed (frame : CSTTT.FiniteEnum A) (seed : A → Bool) (rules : List (Rule A))
    (enabled : Rule A → Bool) : Below seed (ancestry frame seed rules enabled) := by
  have retained : ∀ n, Below seed (iterate (gamma seed rules enabled) seed n) := by
    intro n
    induction n with
    | zero => intro x member; exact member
    | succ n ih =>
      intro x member
      exact gamma_inflation seed rules enabled _ x (ih x member)
  exact retained _
-- Class (b): an excluded component stays excluded when no seed enters and every entering rule needs an excluded predecessor.
theorem component_exclusion (frame : CSTTT.FiniteEnum A) (seed : A → Bool) (rules : List (Rule A))
    (enabled : Rule A → Bool) (blocked : A → Bool)
    (seedOutside : ∀ x, seed x=true → blocked x=false)
    (ruleOutside : ∀ rule∈rules, enabled rule=true → blocked rule.conclusion=true →
      ∃ predecessor∈rule.prerequisites, blocked predecessor=true) :
    ∀ x, ancestry frame seed rules enabled x=true → blocked x=false := by
  let upper : A → Bool := fun x => !blocked x
  have seedBelow : Below seed upper := by
    intro x member
    simp [upper,seedOutside x member]
  have closed : Below (gamma seed rules enabled upper) upper := by
    intro x member
    rcases (gamma_iff seed rules enabled upper x).mp member with h|h|⟨rule,mem,conclusion,nonempty,guard,all⟩
    · exact seedBelow x h
    · exact h
    · by_cases clear : blocked x=false
      · simp [upper,clear]
      · have blockedHere : blocked x=true := by cases value : blocked x <;> simp_all
        have blockedConclusion : blocked rule.conclusion=true := conclusion ▸ blockedHere
        obtain ⟨predecessor,prerequisite,blockedPredecessor⟩ := ruleOutside rule mem guard blockedConclusion
        have contradiction := all predecessor prerequisite
        simp [upper,blockedPredecessor] at contradiction
  have below := (ancestry_least_fixed frame seed rules enabled).2 upper seedBelow closed
  intro x member
  simpa [upper] using below x member
end CSTTT.FallbackTheory.FiniteHorn
