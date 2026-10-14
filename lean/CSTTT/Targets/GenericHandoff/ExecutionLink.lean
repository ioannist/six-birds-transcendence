import CSTTT.Targets.GenericHandoff.ResourceRuntime
import CSTTT.Targets.GenericHandoff.RegisterFuture
import CSTTT.Targets.GenericHandoff.StrictSparseGame

/-! Checked register-representation link for the shared TTH-06 runtime.
The embedding is a family of raw typed instructions. Its interpreted map is
defined here; rows and successors are always the two actual raw programs.
Checks range over EVERY run context and EVERY declared support branch, so a
link cannot be certified merely by agreement at the audit snapshots.

The enclosing binding must select its source/target programs from the shared
runtime. This module provides the per-instance lifting obligation and its
inductive consequence; it does not supply a finite-context assumption. -/
namespace CSTTT.TargetTheory.GenericHandoff.ExecutionLink
open RegisterInterpreter

structure Raw (Cell : Type) (Value : Cell → Type) (S T : Type)
    (SV : S → Type) (TV : T → Type) (D A O : Type) where
  source : ResourceRuntime.Execution Cell Value S SV D A O
  target : ResourceRuntime.Execution Cell Value T TV D A O
  embedding : (k : T) → Expr Cell Value S SV Unit (TV k)

variable {Cell S T D A O : Type} {Value : Cell → Type}
    {SV : S → Type} {TV : T → Type}

def ExecutionReady (e : ResourceRuntime.Execution Cell Value S SV D A O)
    (a : Assignment Cell Value) : Prop :=
  Complete e.row.dependencies a ∧ ProgramReady e.program a

def Ready (raw : Raw Cell Value S T SV TV D A O) (a : Assignment Cell Value) : Prop :=
  ExecutionReady raw.source a ∧ ExecutionReady raw.target a ∧
    ∀ k, Complete (raw.embedding k).dependencies a

def rows (e : ResourceRuntime.Execution Cell Value S SV D A O)
    (a : Assignment Cell Value) (x : Registers S SV) (d : D) (act : A) : List (O × Rat) :=
  (e.row.eval a x (d,act)).getD []

/-- Row-derived support coverage, not a supplied domain-validity flag. Every
positive listed branch must remain in the domain used by successor checks. -/
def SupportCoverage (e : ResourceRuntime.Execution Cell Value S SV D A O)
    (a : Assignment Cell Value) : Prop :=
  ∀ x d act o, StrategyGame.PositiveSupport (rows e a) x d act o → o ∈ e.outcomes

noncomputable def update (e : ResourceRuntime.Execution Cell Value S SV D A O)
    (a : Assignment Cell Value) (h : ExecutionReady e a)
    (x : Registers S SV) (d : D) (act : A) (o : O) : Registers S SV :=
  checkedExecute e.program a h.2 x (d,act,o)

noncomputable def embed (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) (x : Registers S SV) : Registers T TV :=
  fun k => RegisterFuture.read (raw.embedding k) a (h.2.2 k) x

theorem embed_equation (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) (x : Registers S SV) (k : T) :
    (raw.embedding k).eval a x () = some (embed raw a h x k) :=
  RegisterFuture.read_eq _ _ _ _

structure Laws (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) : Prop where
  disturbances : raw.target.disturbances = raw.source.disturbances
  actions : raw.target.actions = raw.source.actions
  outcomes : raw.target.outcomes = raw.source.outcomes
  rows : ∀ x d act, rows raw.target a (embed raw a h x) d act = rows raw.source a x d act
  supportCoverage : SupportCoverage raw.source a ∧ SupportCoverage raw.target a
  successor : ∀ x, ∀ d ∈ raw.source.disturbances, ∀ act ∈ raw.source.actions,
    ∀ o ∈ raw.source.outcomes,
      embed raw a h (update raw.source a h.1 x d act o) =
        update raw.target a h.2.1 (embed raw a h x) d act o

def Pass (raw : Raw Cell Value S T SV TV D A O) (a : Assignment Cell Value) : Prop :=
  ∃ h : Ready raw a, Laws raw a h

/-- An actual positive branch cannot evade the successor law by omission from
the declared outcome list. No outcome-domain premise is supplied here. -/
theorem positive_successor (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) (hl : Laws raw a h)
    (x : Registers S SV) (d : D) (hd : d ∈ raw.source.disturbances)
    (act : A) (ha : act ∈ raw.source.actions) (o : O)
    (hp : StrategyGame.PositiveSupport (rows raw.source a) x d act o) :
    embed raw a h (update raw.source a h.1 x d act o) =
      update raw.target a h.2.1 (embed raw a h x) d act o :=
  hl.successor x d hd act ha o (hl.supportCoverage.1 x d act o hp)

/-- List-level equality retains the selected-response StrictSparse check as
well as normalization and every positive branch. Duplicate positive entries
and permutations are not forbidden by this link. -/
theorem support_iff (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) (hl : Laws raw a h)
    (x : Registers S SV) (d : D) (act : A) (o : O) :
    StrategyGame.PositiveSupport (rows raw.target a) (embed raw a h x) d act o ↔
      StrategyGame.PositiveSupport (rows raw.source a) x d act o := by
  unfold StrategyGame.PositiveSupport
  rw [hl.rows]

theorem normalized_iff (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) (hl : Laws raw a h)
    (x : Registers S SV) (d : D) (act : A) :
    StrategyGame.Normalized (rows raw.target a) (embed raw a h x) d act ↔
      StrategyGame.Normalized (rows raw.source a) x d act := by
  unfold StrategyGame.Normalized
  rw [hl.rows]
  simp only [support_iff raw a h hl]

theorem strict_sparse_iff (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) (hl : Laws raw a h)
    (x : Registers S SV) (d : D) (act : A) :
    StrictSparseGame.StrictSparse (rows raw.target a (embed raw a h x) d act) ↔
      StrictSparseGame.StrictSparse (rows raw.source a x d act) := by
  rw [hl.rows]

noncomputable def fold (e : ResourceRuntime.Execution Cell Value S SV D A O)
    (a : Assignment Cell Value) (h : ExecutionReady e a) :
    Registers S SV → List (D × A × O) → Registers S SV
  | x, [] => x
  | x, (d,act,o)::word => fold e a h (update e a h x d act o) word

def Supported (e : ResourceRuntime.Execution Cell Value S SV D A O)
    (a : Assignment Cell Value) (h : ExecutionReady e a) :
    Registers S SV → List (D × A × O) → Prop
  | _, [] => True
  | x, (d,act,o)::word => d ∈ e.disturbances ∧ act ∈ e.actions ∧ o ∈ e.outcomes ∧
      StrategyGame.PositiveSupport (rows e a) x d act o ∧
      Supported e a h (update e a h x d act o) word

theorem supported_positive_step (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) (hl : Laws raw a h)
    (x : Registers S SV) (d : D) (hd : d ∈ raw.source.disturbances)
    (act : A) (ha : act ∈ raw.source.actions) (o : O)
    (hp : StrategyGame.PositiveSupport (rows raw.source a) x d act o)
    (word : List (D × A × O))
    (tail : Supported raw.source a h.1 (update raw.source a h.1 x d act o) word) :
    Supported raw.source a h.1 x ((d,act,o)::word) :=
  ⟨hd,ha,hl.supportCoverage.1 x d act o hp,hp,tail⟩

/-- Every actual supported word, by induction, not a bounded audit or a
choice of predictive-class representative. All raw successor outcomes survive. -/
theorem supported_fold (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) (hl : Laws raw a h)
    (x : Registers S SV) (word : List (D × A × O))
    (hw : Supported raw.source a h.1 x word) :
    embed raw a h (fold raw.source a h.1 x word) =
      fold raw.target a h.2.1 (embed raw a h x) word := by
  induction word generalizing x with
  | nil => rfl
  | cons e word ih =>
    rcases e with ⟨d,act,o⟩
    simp only [fold]
    rw [ih _ hw.2.2.2.2,hl.successor x d hw.1 act hw.2.1 o hw.2.2.1]

theorem supported_word_iff (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) (hl : Laws raw a h)
    (x : Registers S SV) (word : List (D × A × O)) :
    Supported raw.target a h.2.1 (embed raw a h x) word ↔ Supported raw.source a h.1 x word := by
  induction word generalizing x with
  | nil => exact Iff.rfl
  | cons e word ih =>
    rcases e with ⟨d,act,o⟩
    simp only [Supported,hl.disturbances,hl.actions,hl.outcomes,support_iff raw a h hl]
    constructor
    · rintro ⟨hd,ha,ho,hp,hrest⟩
      rw [← hl.successor x d hd act ha o ho] at hrest
      exact ⟨hd,ha,ho,hp,(ih _).mp hrest⟩
    · rintro ⟨hd,ha,ho,hp,hrest⟩
      refine ⟨hd,ha,ho,hp,?_⟩
      rw [← hl.successor x d hd act ha o ho]
      exact (ih _).mpr hrest

theorem missing_source_row_rejected (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.source.row.dependencies)
    (hm : a k = none) : ¬ Pass raw a := by
  rintro ⟨h,_⟩
  have hc := h.1.1 k hk
  rw [hm] at hc
  contradiction

theorem missing_embedding_rejected (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (k : Cell) (r : T) (hk : k ∈ (raw.embedding r).dependencies)
    (hm : a k = none) : ¬ Pass raw a := by
  rintro ⟨h,_⟩
  have hc := h.2.2 r k hk
  rw [hm] at hc
  contradiction

theorem missing_target_row_rejected (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (k : Cell) (hk : k ∈ raw.target.row.dependencies)
    (hm : a k = none) : ¬ Pass raw a := by
  rintro ⟨h,_⟩
  have hc := h.2.1.1 k hk
  rw [hm] at hc
  contradiction

theorem missing_source_program_rejected (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (r : S) (k : Cell) (hk : k ∈ (raw.source.program r).dependencies)
    (hm : a k = none) : ¬ Pass raw a := by
  rintro ⟨h,_⟩
  have hc := h.1.2 r k hk
  rw [hm] at hc
  contradiction

theorem missing_target_program_rejected (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (r : T) (k : Cell) (hk : k ∈ (raw.target.program r).dependencies)
    (hm : a k = none) : ¬ Pass raw a := by
  rintro ⟨h,_⟩
  have hc := h.2.1.2 r k hk
  rw [hm] at hc
  contradiction

theorem domain_mismatch_rejected (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value)
    (bad : raw.target.disturbances ≠ raw.source.disturbances ∨
      raw.target.actions ≠ raw.source.actions ∨ raw.target.outcomes ≠ raw.source.outcomes) : ¬ Pass raw a := by
  rintro ⟨_,hl⟩
  rcases bad with hd | ha | ho
  · exact hd hl.disturbances
  · exact ha hl.actions
  · exact ho hl.outcomes

theorem omitted_source_support_rejected (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (x : Registers S SV) (d : D) (act : A) (o : O)
    (hp : StrategyGame.PositiveSupport (rows raw.source a) x d act o)
    (missing : o ∉ raw.source.outcomes) : ¬ Pass raw a :=
  fun ⟨_,hl⟩ => missing (hl.supportCoverage.1 x d act o hp)

theorem omitted_target_support_rejected (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (x : Registers T TV) (d : D) (act : A) (o : O)
    (hp : StrategyGame.PositiveSupport (rows raw.target a) x d act o)
    (missing : o ∉ raw.target.outcomes) : ¬ Pass raw a :=
  fun ⟨_,hl⟩ => missing (hl.supportCoverage.2 x d act o hp)

theorem rows_mismatch_rejected (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) (x : Registers S SV) (d : D) (act : A)
    (bad : rows raw.target a (embed raw a h x) d act ≠ rows raw.source a x d act) : ¬ Pass raw a :=
  fun ⟨_,hl⟩ => bad (hl.rows x d act)

theorem successor_mismatch_rejected (raw : Raw Cell Value S T SV TV D A O)
    (a : Assignment Cell Value) (h : Ready raw a) (x : Registers S SV)
    (d : D) (hd : d ∈ raw.source.disturbances) (act : A) (ha : act ∈ raw.source.actions)
    (o : O) (ho : o ∈ raw.source.outcomes)
    (bad : embed raw a h (update raw.source a h.1 x d act o) ≠
      update raw.target a h.2.1 (embed raw a h x) d act o) : ¬ Pass raw a :=
  fun ⟨_,hl⟩ => bad (hl.successor x d hd act ha o ho)

end CSTTT.TargetTheory.GenericHandoff.ExecutionLink
