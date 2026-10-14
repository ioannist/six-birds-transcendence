import CSTTT.Core.Finite

/-! G6d-2a algebraic seam. Raw row operations are checked against the normalized
system computed from a rational transition matrix. The same operations compute
the candidate from the normalization RHS. No candidate, inverse, or uniqueness
verdict is supplied. All solutions, not a displayed finite sample, are covered. -/
namespace CSTTT.TargetTheory.GenericHandoff.FixedPointVerifier
variable {X : Type} [DecidableEq X]
abbrev Vector (X : Type) := X → Rat
abbrev Matrix (X : Type) := X → X → Rat

def dot (xs : List X) (a x : Vector X) : Rat := (xs.map fun j => a j * x j).sum

omit [DecidableEq X] in
theorem dot_add (xs : List X) (a b x : Vector X) :
    dot xs (fun j => a j + b j) x = dot xs a x + dot xs b x := by
  induction xs with
  | nil => simp [dot] <;> grind
  | cons j js ih =>
    simp only [dot,List.map_cons,List.sum_cons] at ih ⊢
    grind [Rat.add_mul]

omit [DecidableEq X] in
theorem dot_scale (xs : List X) (q : Rat) (a x : Vector X) :
    dot xs (fun j => q * a j) x = q * dot xs a x := by
  induction xs with
  | nil => simp [dot] <;> grind
  | cons j js ih =>
    simp only [dot,List.map_cons,List.sum_cons] at ih ⊢
    grind [Rat.mul_add]

omit [DecidableEq X] in
theorem dot_sub (xs : List X) (a b x : Vector X) :
    dot xs (fun j => a j - b j) x = dot xs a x - dot xs b x := by
  induction xs with
  | nil => simp [dot] <;> grind
  | cons j js ih =>
    simp only [dot,List.map_cons,List.sum_cons] at ih ⊢
    grind

def identity : Matrix X := fun i j => if i = j then 1 else 0

theorem dot_indicator (xs : List X) (hn : xs.Nodup) (i : X) (x : Vector X) :
    dot xs (identity i) x = if i ∈ xs then x i else 0 := by
  induction xs with
  | nil => simp [dot] <;> grind
  | cons j js ih =>
    have h := List.nodup_cons.mp hn
    have hr := ih h.2
    by_cases he : i = j
    · subst j
      simp [dot,identity] at hr ⊢
      rw [hr]
      simp [h.1] <;> grind
    · simp only [dot,List.map_cons,List.sum_cons,identity,he,if_false] at hr ⊢
      simp only [Rat.zero_mul,Rat.zero_add]
      rw [hr]
      simp [he]

structure System (X : Type) where
  matrix : Matrix X
  rhs : Vector X

def Solves (xs : List X) (s : System X) (x : Vector X) : Prop :=
  ∀ i, dot xs (s.matrix i) x = s.rhs i

inductive RowOperation (X : Type) where
  | swap (i j : X)
  | scale (i : X) (q : Rat)
  | add (i j : X) (q : Rat)

/-- Elementary operations act on both the matrix and RHS. -/
def applyOperation (op : RowOperation X) (s : System X) : System X :=
  match op with
  | .swap i j =>
    ⟨(fun k => if k = i then s.matrix j else if k = j then s.matrix i else s.matrix k),
     (fun k => if k = i then s.rhs j else if k = j then s.rhs i else s.rhs k)⟩
  | .scale i q =>
    ⟨(fun k t => if k = i then q * s.matrix k t else s.matrix k t),
     (fun k => if k = i then q * s.rhs k else s.rhs k)⟩
  | .add i j q =>
    ⟨(fun k t => if k = i then s.matrix k t + q * s.matrix j t else s.matrix k t),
     (fun k => if k = i then s.rhs k + q * s.rhs j else s.rhs k)⟩

theorem operation_preserves_solution (xs : List X) (op : RowOperation X)
    (s : System X) (x : Vector X) (h : Solves xs s x) : Solves xs (applyOperation op s) x := by
  intro k
  cases op with
  | swap i j =>
    by_cases hi : k = i
    · simpa [applyOperation,hi] using h j
    · by_cases hj : k = j
      · have hji : j ≠ i := fun he => hi (hj.trans he)
        simpa [applyOperation,hi,hj,hji] using h i
      · simpa [applyOperation,hi,hj] using h k
  | scale i q =>
    by_cases hi : k = i
    · simp only [applyOperation,hi,if_true]
      rw [dot_scale,h i]
    · simpa [applyOperation,hi] using h k
  | add i j q =>
    by_cases hi : k = i
    · simp only [applyOperation,hi,if_true]
      rw [dot_add,dot_scale,h i,h j]
    · simpa [applyOperation,hi] using h k

def reduce (ops : List (RowOperation X)) (s : System X) : System X :=
  ops.foldl (fun acc op => applyOperation op acc) s

theorem reduction_preserves_solution (xs : List X) (ops : List (RowOperation X))
    (s : System X) (x : Vector X) (h : Solves xs s x) : Solves xs (reduce ops s) x := by
  induction ops generalizing s with
  | nil => exact h
  | cons op ops ih => exact ih _ (operation_preserves_solution xs op s x h)

/-- One stationary equation is replaced by normalization; every true normalized
fixed distribution satisfies this constructed square system. -/
def normalized (E : Matrix X) (anchor : X) : System X :=
  ⟨(fun i j => if i = anchor then 1 else E j i - identity i j),
   (fun i => if i = anchor then 1 else 0)⟩
def mass (xs : List X) (x : Vector X) := (xs.map x).sum
def Fixed (xs : List X) (E : Matrix X) (x : Vector X) : Prop :=
  ∀ i, dot xs (fun j => E j i) x = x i
def Probability (xs : List X) (x : Vector X) : Prop :=
  (∀ i, 0 ≤ x i) ∧ mass xs x = 1

def candidate (E : Matrix X) (anchor : X) (ops : List (RowOperation X)) : Vector X :=
  (reduce ops (normalized E anchor)).rhs

/-- Finite extensional checks, not a flag about uniqueness. Residual/probability
are checked on the derived candidate, since only sound forward row operations
are needed for uniqueness. A zero scaling cannot manufacture an accepted
candidate: final identity and original-system residual remain mandatory. -/
def checkCore (xs : List X) (E : Matrix X) (anchor : X) (ops : List (RowOperation X)) : Bool :=
  xs.all (fun i => xs.all fun j =>
    decide ((reduce ops (normalized E anchor)).matrix i j = identity i j)) &&
  xs.all (fun i => decide (0 ≤ candidate E anchor ops i)) &&
  decide (mass xs (candidate E anchor ops) = 1) &&
  xs.all (fun i => decide (dot xs (fun j => E j i) (candidate E anchor ops) = candidate E anchor ops i))

/-- Duplicate enumerations are rejected before matrix computations. The
finite interface separately proves its enumeration covers every state. -/
def check (xs : List X) (E : Matrix X) (anchor : X) (ops : List (RowOperation X)) : Bool :=
  decide xs.Nodup && checkCore xs E anchor ops

theorem duplicate_enumeration_rejected (x : X) (xs : List X) (E : Matrix X)
    (anchor : X) (ops : List (RowOperation X)) : check (x :: x :: xs) E anchor ops = false := by
  simp [check,List.nodup_cons]

omit [DecidableEq X] in
theorem missing_enumeration_rejected (xs : List X) (x : X) (h : x ∉ xs) :
    ¬ (∀ i, i ∈ xs) := fun hc => h (hc x)

theorem normalized_of_fixed (xs : List X) (hn : xs.Nodup) (hc : ∀ i, i ∈ xs)
    (E : Matrix X) (anchor : X) (x : Vector X)
    (hp : Probability xs x) (hf : Fixed xs E x) : Solves xs (normalized E anchor) x := by
  intro i
  by_cases hi : i = anchor
  · simpa [normalized,dot,mass,hi] using hp.2
  · simp only [normalized,hi,if_false]
    rw [dot_sub,dot_indicator xs hn,if_pos (hc i),hf i]
    grind

theorem check_sound (xs : List X) (hc : ∀ i, i ∈ xs)
    (E : Matrix X) (anchor : X) (ops : List (RowOperation X)) (h : check xs E anchor ops = true) :
    Probability xs (candidate E anchor ops) ∧ Fixed xs E (candidate E anchor ops) ∧
    (∀ x, Probability xs x → Fixed xs E x → x = candidate E anchor ops) := by
  have hh := h
  simp only [check,Bool.and_eq_true] at hh
  have hn : xs.Nodup := of_decide_eq_true hh.1
  have h := hh.2
  simp only [checkCore,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at h
  refine ⟨⟨fun i => h.1.1.2 i (hc i),h.1.2⟩,fun i => h.2 i (hc i),?_⟩
  intro x hp hf
  have hs := reduction_preserves_solution xs ops (normalized E anchor) x
    (normalized_of_fixed xs hn hc E anchor x hp hf)
  funext i
  have row : (reduce ops (normalized E anchor)).matrix i = identity i := by
    funext j
    exact h.1.1.1 i (hc i) j (hc j)
  have he := hs i
  rw [row,dot_indicator xs hn,if_pos (hc i)] at he
  exact he

/-- Guard on any broken reduction entry; residual and positivity cannot mask it. -/
theorem changed_reduction_rejected (xs : List X) (E : Matrix X) (anchor : X)
    (ops : List (RowOperation X)) {i j : X} (hi : i ∈ xs) (hj : j ∈ xs)
    (hne : (reduce ops (normalized E anchor)).matrix i j ≠ identity i j) :
    check xs E anchor ops = false := by
  cases hh : check xs E anchor ops with
  | false => rfl
  | true =>
    simp only [check,Bool.and_eq_true] at hh
    have hh := hh.2
    simp only [checkCore,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hh
    exact False.elim (hne (hh.1.1.1 i hi j hj))
theorem bad_mass_rejected (xs : List X) (E : Matrix X) (anchor : X)
    (ops : List (RowOperation X)) (hne : mass xs (candidate E anchor ops) ≠ 1) :
    check xs E anchor ops = false := by
  cases hh : check xs E anchor ops with
  | false => rfl
  | true =>
    simp only [check,Bool.and_eq_true] at hh
    have hh := hh.2
    simp only [checkCore,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hh
    exact False.elim (hne hh.1.2)

theorem bad_residual_rejected (xs : List X) (E : Matrix X) (anchor : X)
    (ops : List (RowOperation X)) {i : X} (hi : i ∈ xs)
    (hne : dot xs (fun j => E j i) (candidate E anchor ops) ≠ candidate E anchor ops i) :
    check xs E anchor ops = false := by
  cases hh : check xs E anchor ops with
  | false => rfl
  | true =>
    simp only [check,Bool.and_eq_true] at hh
    have hh := hh.2
    simp only [checkCore,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hh
    exact False.elim (hne (hh.2 i hi))

theorem negative_candidate_rejected (xs : List X) (E : Matrix X) (anchor : X)
    (ops : List (RowOperation X)) {i : X} (hi : i ∈ xs)
    (hneg : candidate E anchor ops i < 0) : check xs E anchor ops = false := by
  cases hh : check xs E anchor ops with
  | false => rfl
  | true =>
    simp only [check,Bool.and_eq_true] at hh
    have hh := hh.2
    simp only [checkCore,Bool.and_eq_true,List.all_eq_true,decide_eq_true_eq] at hh
    have hp := hh.1.1.2 i hi
    grind
end CSTTT.TargetTheory.GenericHandoff.FixedPointVerifier
