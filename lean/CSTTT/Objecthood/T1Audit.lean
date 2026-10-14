import Lean

namespace CSTTT.Objecthood.T1Audit

/-- The ten states of T1's canonical deadline kernel, in the published order.
Source: `../six-birds-consciousness/lab/sixbirds_consciousness/labs/t1_l1_self_wheel.py`,
lines 23–69 (`WheelState`, `CORE`, `EXPECTED_DEADLINE_KERNEL`) and 921–935. -/
inductive KState where
  | p0w0 | p0w1 | p1w0 | p1w1 | p2w1
  | p3w0 | p3w1 | p4w0 | p4w1 | p5w0
  deriving DecidableEq, Repr

def kernel : List KState :=
  [.p0w0, .p0w1, .p1w0, .p1w1, .p2w1,
   .p3w0, .p3w1, .p4w0, .p4w1, .p5w0]

/-- Source: `t1_l1_self_wheel.py`, lines 43–48. -/
def core : List KState := [.p1w0, .p1w1, .p2w1, .p5w0]

inductive Action where | stay | cw | ccw deriving DecidableEq, Repr

/-- Source: `t1_l1_self_wheel.py`, lines 924–935 and 1052–1067. -/
def canonicalPolicy : List Action :=
  [.stay, .stay, .cw, .ccw, .stay,
   .stay, .stay, .stay, .stay, .stay]

/-- Source: `t1_l1_self_wheel.py`, lines 85–95, 165–178, 625–659,
and the kernel order above. These are the seven realized canonical M classes. -/
def mClasses : List Nat := [0, 0, 1, 2, 3, 4, 4, 5, 5, 6]

/-- Four times T1's canonical closed-loop Markov matrix P.
Source: `t1_l1_self_wheel.py`, lines 109–161, 604–622, 895–907.
Rows and columns follow `kernel`; the checker under `scripts/` compares every
entry with `canonical_closed_loop_matrix` computed from the sibling data. -/
def pRows : List (List Nat) :=
  [[0,0,2,2,0,0,0,0,0,0],
   [0,0,2,2,0,0,0,0,0,0],
   [0,0,0,0,4,0,0,0,0,0],
   [0,0,0,0,0,0,0,0,0,4],
   [0,0,3,1,0,0,0,0,0,0],
   [0,0,2,2,0,0,0,0,0,0],
   [0,0,2,2,0,0,0,0,0,0],
   [0,0,2,2,0,0,0,0,0,0],
   [0,0,2,2,0,0,0,0,0,0],
   [0,0,1,3,0,0,0,0,0,0]]

abbrev I := Fin 10

def stateAt (i : I) : KState := kernel.getD i.val .p0w0
def pNum (i j : I) : Nat := (pRows.getD i.val []).getD j.val 0
def mClass (i : I) : Nat := mClasses.getD i.val 0

def sum10 (f : I → Nat) : Nat :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9
def sumRat (f : I → Rat) : Rat :=
  f 0 + f 1 + f 2 + f 3 + f 4 + f 5 + f 6 + f 7 + f 8 + f 9

/-- A rational matrix with a common positive denominator. -/
structure ScaledMatrix where
  den : Nat
  num : I → I → Nat

def product (a b : ScaledMatrix) : ScaledMatrix :=
  ⟨a.den * b.den, fun i j => sum10 (fun k => a.num i k * b.num k j)⟩

def entry (a : ScaledMatrix) (i j : I) : Rat := (a.num i j : Rat) / a.den

def P : ScaledMatrix := ⟨4, pNum⟩

/-- T1's `P_ε=(1−ε)P+ε Uniform(K)` at ε=1/16. Since P has
denominator four and |K|=10, `(75*pNum+2)/320` is that exact mixture.
Source: `t1_l1_self_wheel.py`, lines 568–570 and 662–682. -/
def Peps : ScaledMatrix := ⟨320, fun i j => 75 * pNum i j + 2⟩

theorem peps_is_t1_mixture (i j : I) :
    entry Peps i j = (15/16 : Rat) * entry P i j + 1/160 := by
  simp only [entry, Peps, P]
  grind

def Peps2 : ScaledMatrix := product Peps Peps

def classSize (i : I) : Nat :=
  sum10 (fun j => if mClass i = mClass j then 1 else 0)

/-- `C U` is the uniform prototype on each realized M fiber. Every fiber has
size one or two, so this table is scaled by two and computed from `mClass`.
Source: `t1_l1_self_wheel.py`, lines 625–659. -/
def CU : ScaledMatrix :=
  ⟨2, fun i j => if mClass i = mClass j then 2 / classSize i else 0⟩

def E2eps : ScaledMatrix := product Peps2 CU
def E2epsSquared : ScaledMatrix := product E2eps E2eps

def P2 : ScaledMatrix := product P P
def E2zero : ScaledMatrix := product P2 CU
def E2zeroSquared : ScaledMatrix := product E2zero E2zero

/-- A proof certificate for reducing symbolic fixed-point equations. The
matrix remains defined by `product Peps2 CU`; every certificate entry is
checked against that definition below. -/
private def eRows : List (List Nat) :=
  [[1280,1280,6080,6080,92480,1280,1280,1280,1280,92480],
   [1280,1280,6080,6080,92480,1280,1280,1280,1280,92480],
   [1280,1280,141080,51080,2480,1280,1280,1280,1280,2480],
   [1280,1280,51080,141080,2480,1280,1280,1280,1280,2480],
   [1280,1280,6080,6080,137480,1280,1280,1280,1280,47480],
   [1280,1280,6080,6080,92480,1280,1280,1280,1280,92480],
   [1280,1280,6080,6080,92480,1280,1280,1280,1280,92480],
   [1280,1280,6080,6080,92480,1280,1280,1280,1280,92480],
   [1280,1280,6080,6080,92480,1280,1280,1280,1280,92480],
   [1280,1280,6080,6080,47480,1280,1280,1280,1280,137480]]

theorem eRows_verified :
    ∀ i j : I, E2eps.num i j = (eRows.getD i.val []).getD j.val 0 := by
  decide

theorem kernel_size : kernel.length = 10 := by decide
theorem core_size : core.length = 4 := by decide
theorem p_rows_shape : pRows.length = 10 ∧ pRows.all (fun row => row.length == 10) := by decide
theorem p_rows_stochastic : ∀ i : I, sum10 (pNum i) = 4 := by decide
theorem m_fibers_nonempty_and_small : ∀ i : I, classSize i = 1 ∨ classSize i = 2 := by decide
theorem cu_rows_stochastic : ∀ i : I, sum10 (CU.num i) = 2 := by decide
theorem eps_rows_stochastic : ∀ i : I, sum10 (Peps.num i) = 320 := by decide
theorem eps2_denominator : Peps2.den = 102400 := by decide
theorem e2eps_denominator : E2eps.den = 204800 := by decide
theorem e2eps_rows_stochastic : ∀ i : I, sum10 (E2eps.num i) = E2eps.den := by decide

/-- T1's displayed fixed distribution, scaled to denominator 4960.
Source: `t1_l1_self_wheel.py`, lines 828–872 and 984–1008;
`THEOREMS.md`, T1 theorem, lines 20–24. -/
def piWeights : List Nat :=
  [31,31,1216,1216,1171,31,31,31,31,1171]

def piNum (i : I) : Nat := piWeights.getD i.val 0
def pi (i : I) : Rat := (piNum i : Rat) / 4960

def uniform (_ : I) : Rat := 1/10
def coreUniform (i : I) : Rat := if stateAt i ∈ core then 1/4 else 0

def IsProbability (μ : I → Rat) : Prop :=
  (∀ i, 0 ≤ μ i) ∧ sumRat μ = 1

def IsFixed (a : ScaledMatrix) (μ : I → Rat) : Prop :=
  ∀ j, μ j * a.den = sumRat (fun i => μ i * (a.num i j : Rat))

theorem pi_num_sum : sum10 piNum = 4960 := by decide
theorem pi_num_fixed :
    ∀ j : I, piNum j * E2eps.den =
      sum10 (fun i => piNum i * E2eps.num i j) := by
  decide

theorem pi_described :
    pi 0 = 1/160 ∧ pi 1 = 1/160 ∧
    pi 2 = 38/155 ∧ pi 3 = 38/155 ∧
    pi 4 = 1171/4960 ∧
    pi 5 = 1/160 ∧ pi 6 = 1/160 ∧
    pi 7 = 1/160 ∧ pi 8 = 1/160 ∧
    pi 9 = 1171/4960 := by
  have h0 : piNum 0 = 31 := by decide
  have h1 : piNum 1 = 31 := by decide
  have h2 : piNum 2 = 1216 := by decide
  have h3 : piNum 3 = 1216 := by decide
  have h4 : piNum 4 = 1171 := by decide
  have h5 : piNum 5 = 31 := by decide
  have h6 : piNum 6 = 31 := by decide
  have h7 : piNum 7 = 31 := by decide
  have h8 : piNum 8 = 31 := by decide
  have h9 : piNum 9 = 1171 := by decide
  simp only [pi, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9]
  grind

theorem pi_probability : IsProbability pi := by
  rcases pi_described with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  constructor
  · intro i
    grind [pi]
  · simp only [sumRat]
    rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
    grind

theorem pi_fixed : IsFixed E2eps pi := by
  intro j
  have hn := pi_num_fixed j
  simp only [sum10] at hn
  have hr :
      (piNum j : Rat) * E2eps.den =
      (piNum 0 : Rat) * E2eps.num 0 j +
      (piNum 1 : Rat) * E2eps.num 1 j +
      (piNum 2 : Rat) * E2eps.num 2 j +
      (piNum 3 : Rat) * E2eps.num 3 j +
      (piNum 4 : Rat) * E2eps.num 4 j +
      (piNum 5 : Rat) * E2eps.num 5 j +
      (piNum 6 : Rat) * E2eps.num 6 j +
      (piNum 7 : Rat) * E2eps.num 7 j +
      (piNum 8 : Rat) * E2eps.num 8 j +
      (piNum 9 : Rat) * E2eps.num 9 j := by
    exact_mod_cast hn
  simp only [sumRat, pi]
  grind

theorem e_transient_column :
    ∀ i j : I,
      (j = 0 ∨ j = 1 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) →
      E2eps.num i j = 1280 := by decide

theorem e_column_p1w0 (i : I) :
    E2eps.num i 2 = if i = 2 then 141080 else if i = 3 then 51080 else 6080 := by
  decide +revert

theorem e_column_p1w1 (i : I) :
    E2eps.num i 3 = if i = 3 then 141080 else if i = 2 then 51080 else 6080 := by
  decide +revert

theorem e_column_p2w1 (i : I) :
    E2eps.num i 4 =
      if i = 4 then 137480 else if i = 9 then 47480
      else if i = 2 ∨ i = 3 then 2480 else 92480 := by
  decide +revert

private theorem transient_fixed (μ : I → Rat)
    (h : IsFixed E2eps μ) (hn : sumRat μ = 1)
    (j : I) (hj : j = 0 ∨ j = 1 ∨ j = 5 ∨ j = 6 ∨ j = 7 ∨ j = 8) :
    μ j = 1/160 := by
  have hc (i : I) : E2eps.num i j = 1280 := e_transient_column i j hj
  have hf := h j
  simp only [sumRat, hc, e2eps_denominator] at hf
  simp only [sumRat] at hn
  grind

private theorem core_fixed (μ : I → Rat)
    (h : IsFixed E2eps μ) (hn : sumRat μ = 1) :
    μ 2 = 38/155 ∧ μ 3 = 38/155 ∧
    μ 4 = 1171/4960 ∧ μ 9 = 1171/4960 := by
  have ht0 : μ 0 = 1/160 := transient_fixed μ h hn 0 (by decide)
  have ht1 : μ 1 = 1/160 := transient_fixed μ h hn 1 (by decide)
  have ht5 : μ 5 = 1/160 := transient_fixed μ h hn 5 (by decide)
  have ht6 : μ 6 = 1/160 := transient_fixed μ h hn 6 (by decide)
  have ht7 : μ 7 = 1/160 := transient_fixed μ h hn 7 (by decide)
  have ht8 : μ 8 = 1/160 := transient_fixed μ h hn 8 (by decide)
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  simp only [sumRat, e2eps_denominator] at h2 h3 h4 hn
  simp only [e_column_p1w0] at h2
  simp only [e_column_p1w1] at h3
  simp only [e_column_p2w1] at h4
  simp at h2 h3 h4
  grind

/-- The fixed-point conclusion is over *every* rational probability
distribution, not merely the displayed candidate. The six constant
transient columns force their masses from normalization; the other three
column equations and normalization determine the four CORE masses. -/
theorem pi_unique (μ : I → Rat)
    (hp : IsProbability μ) (hf : IsFixed E2eps μ) : μ = pi := by
  have ht0 : μ 0 = 1/160 := transient_fixed μ hf hp.2 0 (by decide)
  have ht1 : μ 1 = 1/160 := transient_fixed μ hf hp.2 1 (by decide)
  have ht5 : μ 5 = 1/160 := transient_fixed μ hf hp.2 5 (by decide)
  have ht6 : μ 6 = 1/160 := transient_fixed μ hf hp.2 6 (by decide)
  have ht7 : μ 7 = 1/160 := transient_fixed μ hf hp.2 7 (by decide)
  have ht8 : μ 8 = 1/160 := transient_fixed μ hf hp.2 8 (by decide)
  rcases core_fixed μ hf hp.2 with ⟨hc2,hc3,hc4,hc9⟩
  rcases pi_described with ⟨p0,p1,p2,p3,p4,p5,p6,p7,p8,p9⟩
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨
      i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 := by decide +revert
  grind (splits := 20)

theorem pi_nonuniform : pi ≠ uniform := by
  intro h
  have h0 := congrFun h (0 : I)
  have p0 := pi_described.1
  simp [uniform] at h0
  grind

theorem core_indices :
    ∀ i : I, (stateAt i ∈ core) ↔ (i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 9) := by
  decide

def coreMass (μ : I → Rat) : Rat :=
  sumRat (fun i => if stateAt i ∈ core then μ i else 0)

theorem pi_core_mass : coreMass pi = 77/80 := by
  rcases pi_described with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  simp only [coreMass, sumRat]
  simp [core_indices]
  rw [h2,h3,h4,h9]
  grind

theorem pi_core_retention : coreMass pi ≥ 3/4 := by
  rw [pi_core_mass]
  grind

def absRat (x : Rat) : Rat := if x < 0 then -x else x

/-- Total variation on K relative to the distribution uniform on CORE.
Source: `t1_l1_self_wheel.py`, lines 557–559 and 1097–1112. -/
def tvFromCoreUniform (μ : I → Rat) : Rat :=
  sumRat (fun i => absRat (μ i - coreUniform i)) / 2

theorem pi_tv_from_core_uniform : tvFromCoreUniform pi = 3/80 := by
  rcases pi_described with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9⟩
  simp only [tvFromCoreUniform, sumRat]
  simp [coreUniform, core_indices, absRat]
  rw [h0,h1,h2,h3,h4,h5,h6,h7,h8,h9]
  grind

def natAbsDiff (a b : Nat) : Nat := if a ≤ b then b - a else a - b

def rowDefectNumerator (a : ScaledMatrix) (i : I) : Nat :=
  sum10 (fun j => natAbsDiff ((product a a).num i j) (a.den * a.num i j))

def max10 (f : I → Nat) : Nat :=
  max (f 0) (max (f 1) (max (f 2) (max (f 3) (max (f 4)
    (max (f 5) (max (f 6) (max (f 7) (max (f 8) (f 9)))))))))

/-- T1's `δ = 1/2 max_z ||E²(z,-)-E(z,-)||₁` in exact scaled
integer arithmetic. `product a a` has denominator `a.den²`, so each
absolute numerator difference is divided by `2*a.den²` after summing.
Source: `t1_l1_self_wheel.py`, lines 685–709. -/
def defect (a : ScaledMatrix) : Rat :=
  (max10 (rowDefectNumerator a) : Rat) /
    ((2 * a.den * a.den : Nat) : Rat)

theorem e2eps_defect_numerator :
    max10 (rowDefectNumerator E2eps) = 12607200000 := by decide

theorem e2eps_defect : defect E2eps = 78795/524288 := by
  unfold defect
  rw [e2eps_defect_numerator, e2eps_denominator]
  grind

theorem e2zero_denominator : E2zero.den = 32 := by decide
theorem e2zero_defect_numerator :
    max10 (rowDefectNumerator E2zero) = 256 := by decide
theorem e2zero_defect : defect E2zero = 1/8 := by
  unfold defect
  rw [e2zero_defect_numerator, e2zero_denominator]
  grind

end CSTTT.Objecthood.T1Audit
