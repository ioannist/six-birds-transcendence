import CSTTT.Targets.GenericHandoff.ProfileRules
import CSTTT.Targets.GenericHandoff.FixedPointVerifier

/-! G6d-2a C1 operator seam. Arbitrary finite carriers/actions/outcomes;
quotients, P, C, U, perturbation, staging and candidate are computed. Raw
comparison tables and numerical audit targets are not verdicts. The typed
C1 decoder and full POS-04 family equivalence remain a separate seam. -/
namespace CSTTT.TargetTheory.GenericHandoff.ObjecthoodRules
open FixedPointVerifier

structure Raw (S A O : Type) where
  profile : ProfileRules.Raw S A O
  policy : S → A
  prototypes : List S
  rowScale : Nat
  tau : Nat
  epsilon : Rat
  core : List S
  anchor : S
  operations : List (RowOperation S)
  publishedP : S → S → Rat
  publishedC : S → Nat → Rat
  publishedU : Nat → S → Rat
  retention : Rat
  expectedTV : Rat
  expectedZeroDefect : Rat
  expectedDefect : Rat

section Rules
variable {S A O : Type} [DecidableEq S]

def classes (d : Raw S A O) := d.prototypes.map (ProfileRules.predictive d.profile)
def classOf (d : Raw S A O) := ProfileRules.predictive d.profile
def fiber (d : Raw S A O) (s : S) :=
  d.profile.states.filter fun t => decide (classOf d t = classOf d s)

def P (d : Raw S A O) (s t : S) : Rat :=
  ((d.profile.rows s (d.policy s)).map fun e =>
    if d.profile.destination e.1 = some t then (e.2 : Rat) else 0).sum / d.rowScale

def C (d : Raw S A O) (s : S) (k : Nat) : Rat :=
  match d.prototypes[k]? with
  | none => 0
  | some p => if classOf d s = classOf d p then 1 else 0
def U (d : Raw S A O) (k : Nat) (s : S) : Rat :=
  match d.prototypes[k]? with
  | none => 0
  | some p => if classOf d s = classOf d p then 1 / ((fiber d p).length : Rat) else 0
def CU (d : Raw S A O) (s t : S) : Rat :=
  ((List.range d.prototypes.length).map fun k => C d s k * U d k t).sum

def product (xs : List S) (a b : Matrix S) (s t : S) : Rat :=
  (xs.map fun k => a s k * b k t).sum
def power (xs : List S) (a : Matrix S) : Nat → Matrix S
  | 0 => identity
  | n + 1 => product xs (power xs a n) a
def perturbed (d : Raw S A O) (s t : S) : Rat :=
  (1 - d.epsilon) * P d s t + d.epsilon / (d.profile.states.length : Rat)
def Ezero (d : Raw S A O) := product d.profile.states (power d.profile.states (P d) d.tau) (CU d)
def E (d : Raw S A O) := product d.profile.states (power d.profile.states (perturbed d) d.tau) (CU d)
def pi (d : Raw S A O) := candidate (E d) d.anchor d.operations

def uniform (d : Raw S A O) (_ : S) : Rat := 1 / (d.profile.states.length : Rat)
def coreUniform (d : Raw S A O) (s : S) : Rat :=
  if s ∈ d.core then 1 / (d.core.length : Rat) else 0
def coreMass (d : Raw S A O) : Rat := (d.core.map (pi d)).sum
def absRat (x : Rat) : Rat := if x < 0 then -x else x
def TV (d : Raw S A O) : Rat :=
  ((d.profile.states.map fun s => absRat (pi d s - coreUniform d s)).sum) / 2
def defect (d : Raw S A O) (a : Matrix S) : Rat :=
  (d.profile.states.map fun s =>
    ((d.profile.states.map fun t => absRat (product d.profile.states a a s t - a s t)).sum) / 2
  ).foldl max 0

/-- Raw quotient coverage and first-occurrence class ordering. Empty/missing
prototype lookups yield zero, but cannot support an accepted reconstruction. -/
def QuotientCheck (d : Raw S A O) : Prop :=
  (classes d).Nodup ∧ (∀ s, s ∈ d.profile.states) ∧
  (∀ p ∈ d.prototypes, p ∈ d.profile.states) ∧
  (∀ s, classOf d s ∈ classes d) ∧
  (∀ (k : Fin d.prototypes.length) (p : S), d.prototypes[k.val]? = some p →
    (d.profile.states.filter fun s => decide (classOf d s = classOf d p)).head? = some p)
def Reconstruction (d : Raw S A O) : Prop :=
  (∀ s t, P d s t = d.publishedP s t) ∧
  (∀ s (k : Fin d.prototypes.length), C d s k.val = d.publishedC s k.val) ∧
  (∀ (k : Fin d.prototypes.length) s, U d k.val s = d.publishedU k.val s)
def KernelCheck (d : Raw S A O) : Prop :=
  d.profile.states.Nodup ∧ d.profile.states ≠ [] ∧ 0 < d.rowScale ∧
  0 ≤ d.epsilon ∧ d.epsilon ≤ 1 ∧
  (∀ s, s ∈ d.profile.states) ∧
  (∀ s t, 0 ≤ P d s t) ∧ (∀ s, mass d.profile.states (P d s) = 1) ∧
  d.core.Nodup ∧ d.core ≠ [] ∧
  (∀ s ∈ d.core, s ∈ d.profile.states) ∧
  (∀ s ∈ d.core, ∀ t, 0 < P d s t → t ∈ d.core)

/-- Full raw action support, including forbidden empty actions. This prevents
zero-weight entries or an omitted action from supporting the predictive class. -/
def SupportCheck (d : Raw S A O) : Prop :=
  d.profile.actions.Nodup ∧ (∀ a, a ∈ d.profile.actions) ∧
  (∀ s a e, e ∈ d.profile.rows s a → 0 < e.2) ∧
  (∀ s a, let total := ((d.profile.rows s a).map Prod.snd).sum
    total = 0 ∨ total = d.rowScale)

def Gate (d : Raw S A O) : Prop :=
  KernelCheck d ∧ QuotientCheck d ∧ Reconstruction d ∧ SupportCheck d ∧
  check d.profile.states (E d) d.anchor d.operations = true

def Accept (d : Raw S A O) : Prop :=
  Gate d ∧ pi d ≠ uniform d ∧ coreMass d ≥ d.retention ∧
  TV d = d.expectedTV ∧ defect d (Ezero d) = d.expectedZeroDefect ∧
  defect d (E d) = d.expectedDefect

theorem checked_probability_fixed_unique (d : Raw S A O) (h : Gate d) :
    Probability d.profile.states (pi d) ∧ Fixed d.profile.states (E d) (pi d) ∧
    (∀ x, Probability d.profile.states x → Fixed d.profile.states (E d) x → x = pi d) :=
  check_sound d.profile.states h.1.2.2.2.2.2.1 (E d) d.anchor d.operations h.2.2.2.2

theorem accept_sound (d : Raw S A O) (h : Accept d) :
    Probability d.profile.states (pi d) ∧ Fixed d.profile.states (E d) (pi d) ∧
    (∀ x, Probability d.profile.states x → Fixed d.profile.states (E d) x → x = pi d) ∧
    pi d ≠ uniform d ∧ coreMass d ≥ d.retention ∧
    TV d = d.expectedTV ∧ defect d (Ezero d) = d.expectedZeroDefect ∧
    defect d (E d) = d.expectedDefect := by
  have hp := checked_probability_fixed_unique d h.1
  exact ⟨hp.1,hp.2.1,hp.2.2,h.2⟩

theorem missing_class_rejected (d : Raw S A O) (s : S)
    (h : classOf d s ∉ classes d) : ¬ Gate d := fun hg => h (hg.2.1.2.2.2.1 s)
theorem changed_P_rejected (d : Raw S A O) (s t : S)
    (h : P d s t ≠ d.publishedP s t) : ¬ Gate d := fun hg => h (hg.2.2.1.1 s t)
theorem changed_C_rejected (d : Raw S A O) (s : S) (k : Nat)
    (hk : k < d.prototypes.length) (h : C d s k ≠ d.publishedC s k) : ¬ Gate d :=
  fun hg => h (hg.2.2.1.2.1 s ⟨k,hk⟩)
theorem changed_U_rejected (d : Raw S A O) (k : Nat) (s : S)
    (hk : k < d.prototypes.length) (h : U d k s ≠ d.publishedU k s) : ¬ Gate d :=
  fun hg => h (hg.2.2.1.2.2 ⟨k,hk⟩ s)

theorem operator_congruence (d e : Raw S A O)
    (hs : d.profile.states = e.profile.states) (hp : P d = P e)
    (hcu : CU d = CU e) (heps : d.epsilon = e.epsilon) (htau : d.tau = e.tau) :
    E d = E e := by
  have he : perturbed d = perturbed e := by
    funext s t
    simp only [perturbed,hs,heps]
    rw [show P d s t = P e s t from congrFun (congrFun hp s) t]
  simp only [E,hs,hcu,htau,he]

theorem zero_scale_rejected (d : Raw S A O) (h : d.rowScale = 0) : ¬ Gate d := by
  intro hg
  have hp := hg.1.2.2.1
  simp [h] at hp

theorem empty_core_rejected (d : Raw S A O) (h : d.core = []) : ¬ Gate d :=
  fun hg => hg.1.2.2.2.2.2.2.2.2.2.1 h

theorem leaking_core_rejected (d : Raw S A O) (s t : S) (hs : s ∈ d.core)
    (hp : 0 < P d s t) (ht : t ∉ d.core) : ¬ Gate d :=
  fun hg => ht (hg.1.2.2.2.2.2.2.2.2.2.2.2 s hs t hp)

theorem uniform_candidate_rejected (d : Raw S A O) (h : pi d = uniform d) : ¬ Accept d :=
  fun ha => ha.2.1 h

theorem bad_retention_rejected (d : Raw S A O) (h : ¬ coreMass d ≥ d.retention) : ¬ Accept d :=
  fun ha => h ha.2.2.1

theorem bad_TV_rejected (d : Raw S A O) (h : TV d ≠ d.expectedTV) : ¬ Accept d :=
  fun ha => h ha.2.2.2.1

theorem bad_zero_defect_rejected (d : Raw S A O)
    (h : defect d (Ezero d) ≠ d.expectedZeroDefect) : ¬ Accept d :=
  fun ha => h ha.2.2.2.2.1

theorem bad_defect_rejected (d : Raw S A O)
    (h : defect d (E d) ≠ d.expectedDefect) : ¬ Accept d :=
  fun ha => h ha.2.2.2.2.2

theorem omitted_action_rejected (d : Raw S A O) (a : A)
    (h : a ∉ d.profile.actions) : ¬ Gate d := fun hg => h (hg.2.2.2.1.2.1 a)

theorem zero_weight_rejected (d : Raw S A O) (s : S) (a : A) (e : O × Nat)
    (he : e ∈ d.profile.rows s a) (hz : e.2 = 0) : ¬ Gate d := by
  intro hg
  have hp := hg.2.2.2.1.2.2.1 s a e he
  simp [hz] at hp

end Rules
end CSTTT.TargetTheory.GenericHandoff.ObjecthoodRules
