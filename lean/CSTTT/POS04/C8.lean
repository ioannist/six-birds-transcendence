import CSTTT.POS04.C7

/-! C8 follows `audit/M3_model_spec.md:24,32`. The viability set is obtained
by repeatedly deleting states without a funded, closed response. Its initial
set is the exact T1 kernel and its bound is that kernel's cardinality. -/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

inductive C8Variant where | funded | negUnderfund deriving DecidableEq, Repr

def c8Recharge (v : C8Variant) (tag : Tag) : Bool :=
  if v = .negUnderfund && tag = .target then false
  else rechargeAvailableAfterWithdrawal tag

def c8Available (v : C8Variant) (tag : Tag) : Bool :=
  c8Recharge v tag && decide (ledger.initialBudget ≥ ledger.actionCost) &&
    decide (ledger.initialBudget - ledger.actionCost + ledger.rechargePerAction > 0) &&
    decide (resourceOwner tag = tag)

def c8RowClosed (tag : Tag) (s : KState) (a : Action)
    (candidate : List KState) : Bool :=
  let row := actionRow tag s a
  !row.isEmpty &&
    decide ((row.map Prod.snd).sum = 4) &&
    row.all (fun entry => entry.2 > 0 &&
      match entry.1 with
      | .inK t => decide (t ∈ candidate)
      | .p2w0 | .p5w1 => false)

def c8Retain (v : C8Variant) (tag : Tag) (candidate : List KState)
    (s : KState) : Bool :=
  c8Available v tag && actions.any (fun a => c8RowClosed tag s a candidate)

def c8Prune (v : C8Variant) (tag : Tag) (candidate : List KState) :
    List KState :=
  candidate.filter (c8Retain v tag candidate)

def c8Iterate (v : C8Variant) (tag : Tag) : Nat → List KState
  | 0 => kernel
  | n+1 => c8Prune v tag (c8Iterate v tag n)

def c8Greatest (v : C8Variant) (tag : Tag) : List KState :=
  c8Iterate v tag kernel.length

/-- Any finite candidate subset is viable exactly when every one of its
states survives the same raw funding and closed-response test used by prune. -/
def C8Viable (v : C8Variant) (tag : Tag) (S : List KState) : Prop :=
  ∀ s ∈ S, c8Retain v tag S s = true

def C8LedgerHolds (v : C8Variant) (tag : Tag) : Prop :=
  c8Recharge v tag = true ∧ ledger.initialBudget = 1 ∧
  ledger.actionCost = 1 ∧ ledger.rechargePerAction = 1 ∧
  ledger.initialBudget - ledger.actionCost + ledger.rechargePerAction =
    ledger.initialBudget

def C8Pass (v : C8Variant) (tag : Tag) : Prop :=
  c8Greatest v tag ≠ [] ∧ c8Available v tag = true ∧
  C8LedgerHolds v tag ∧
  ∀ s ∈ kernel, ∀ t ∈ kernel,
    rowWeight (actionRow tag s (canonicalAction s)) t = taggedPNum tag s t

/-- Enlarging the candidate set cannot remove a funded response whose entire
positive support was already inside the smaller candidate set. -/
theorem c8_row_closed_mono (tag : Tag) (s : KState) (a : Action)
    (A B : List KState) (hAB : A ⊆ B)
    (h : c8RowClosed tag s a A = true) :
    c8RowClosed tag s a B = true := by
  simp only [c8RowClosed, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  intro entry he
  have hp := h.2 entry he
  cases entry with
  | mk destination weight =>
      cases destination with
      | inK t =>
          simp only [decide_eq_true_eq] at hp ⊢
          exact ⟨hp.1, hAB hp.2⟩
      | p2w0 => simp at hp
      | p5w1 => simp at hp

theorem c8_retain_mono (v : C8Variant) (tag : Tag)
    (A B : List KState) (s : KState) (hAB : A ⊆ B)
    (h : c8Retain v tag A s = true) :
    c8Retain v tag B s = true := by
  simp only [c8Retain, Bool.and_eq_true, List.any_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  obtain ⟨a, ha, hsafe⟩ := h.2
  exact ⟨a, ha, c8_row_closed_mono tag s a A B hAB hsafe⟩

/-- Monotonicity of the actual POS-04 deletion operator, for every variant. -/
theorem c8_prune_mono (v : C8Variant) (tag : Tag)
    (A B : List KState) (hAB : A ⊆ B) :
    c8Prune v tag A ⊆ c8Prune v tag B := by
  intro s hs
  have hs' := List.mem_filter.mp hs
  exact List.mem_filter.mpr ⟨hAB hs'.1,
    c8_retain_mono v tag A B s hAB hs'.2⟩

theorem c8_viable_subset_iterate (v : C8Variant) (tag : Tag)
    (S : List KState) (h : C8Viable v tag S) (n : Nat) :
    S ⊆ c8Iterate v tag n := by
  induction n with
  | zero =>
      intro s _
      cases s <;> simp [c8Iterate, kernel]
  | succ n ih =>
      intro s hs
      exact List.mem_filter.mpr ⟨ih hs,
        c8_retain_mono v tag S (c8Iterate v tag n) s ih (h s hs)⟩

theorem c8_greatest_is_fixed (v : C8Variant) (tag : Tag) :
    c8Prune v tag (c8Greatest v tag) = c8Greatest v tag := by
  cases v <;> cases tag <;> decide

theorem c8_greatest_is_viable (v : C8Variant) (tag : Tag) :
    C8Viable v tag (c8Greatest v tag) := by
  intro s hs
  have hfixed := c8_greatest_is_fixed v tag
  have hmem : s ∈ c8Prune v tag (c8Greatest v tag) := by
    rw [hfixed]
    exact hs
  exact (List.mem_filter.mp hmem).2

/-- Every viable finite subset of the kernel survives every deletion round,
hence is included in the computed fixed point. -/
theorem c8_greatest_contains_every_viable (v : C8Variant) (tag : Tag)
    (S : List KState) (h : C8Viable v tag S) :
    S ⊆ c8Greatest v tag :=
  c8_viable_subset_iterate v tag S h kernel.length

theorem c8_funded_greatest_is_kernel (tag : Tag) :
    c8Greatest .funded tag = kernel := by cases tag <;> decide

theorem c8_funded_is_fixed (tag : Tag) :
    c8Prune .funded tag (c8Greatest .funded tag) = c8Greatest .funded tag := by
  exact c8_greatest_is_fixed .funded tag

theorem c8_funded_is_viable (tag : Tag) :
    C8Viable .funded tag (c8Greatest .funded tag) := by
  exact c8_greatest_is_viable .funded tag

/-- The funded instance of the generic greatest-fixed-point theorem. -/
theorem c8_funded_greatest (tag : Tag) (S : List KState)
    (h : C8Viable .funded tag S) :
    ∀ s ∈ S, s ∈ c8Greatest .funded tag :=
  c8_greatest_contains_every_viable .funded tag S h

theorem c8_funded_P_unchanged (tag : Tag) :
    ∀ s ∈ kernel, ∀ t ∈ kernel,
      rowWeight (actionRow tag s (canonicalAction s)) t =
        taggedPNum tag s t := by
  cases tag <;> decide

theorem c8_funded_each_tag (tag : Tag) : C8Pass .funded tag := by
  cases tag <;> simp only [C8Pass, C8LedgerHolds] <;> decide

theorem neg_c8_underfund_empty :
    c8Greatest .negUnderfund .target = [] := by decide

theorem neg_c8_underfund_no_viable_state (S : List KState)
    (h : C8Viable .negUnderfund .target S) : S = [] := by
  have hsub := c8_greatest_contains_every_viable
    .negUnderfund .target S h
  cases S with
  | nil => rfl
  | cons s rest =>
      have hs : s ∈ c8Greatest .negUnderfund .target :=
        hsub (by simp)
      rw [neg_c8_underfund_empty] at hs
      simp at hs

theorem neg_c8_underfund_collapse :
    c8Greatest .negUnderfund .target = [] ∧
    (∀ S : List KState, C8Viable .negUnderfund .target S → S = []) :=
  ⟨neg_c8_underfund_empty, neg_c8_underfund_no_viable_state⟩

/-! The withdrawal check uses a receiver input with source presence removed.
Target funding is owned by the target resource, while a source-tag response
requires that source to remain present. This makes the target independence
equation explicit rather than reading `ledger.sourceAvailableAfterWithdrawal`. -/
def c8WithdrawnReceiver : Receiver :=
  { receiver with sourcePresent := false }

def c8AvailableWithReceiver (r : Receiver) (v : C8Variant)
    (tag : Tag) : Bool :=
  c8Available v tag && (if tag = .source then r.sourcePresent else true)

def c8ReceiverRetain (r : Receiver) (v : C8Variant) (tag : Tag)
    (candidate : List KState) (s : KState) : Bool :=
  c8AvailableWithReceiver r v tag &&
    actions.any (fun a => c8RowClosed tag s a candidate)

def c8ReceiverPrune (r : Receiver) (v : C8Variant) (tag : Tag)
    (candidate : List KState) : List KState :=
  candidate.filter (c8ReceiverRetain r v tag candidate)

def c8ReceiverIterate (r : Receiver) (v : C8Variant) (tag : Tag) :
    Nat → List KState
  | 0 => kernel
  | n+1 => c8ReceiverPrune r v tag (c8ReceiverIterate r v tag n)

def c8ReceiverGreatest (r : Receiver) (v : C8Variant) (tag : Tag) :
    List KState :=
  c8ReceiverIterate r v tag kernel.length

def C8ReceiverViable (r : Receiver) (v : C8Variant) (tag : Tag)
    (S : List KState) : Prop :=
  ∀ s ∈ S, c8ReceiverRetain r v tag S s = true

def C8ReceiverPass (r : Receiver) (v : C8Variant) (tag : Tag) : Prop :=
  c8ReceiverGreatest r v tag ≠ [] ∧
  c8AvailableWithReceiver r v tag = true ∧
  C8LedgerHolds v tag ∧
  ∀ s ∈ kernel, ∀ t ∈ kernel,
    rowWeight (actionRow tag s (canonicalAction s)) t = taggedPNum tag s t

theorem c8_target_available_independent_of_source (r : Receiver)
    (v : C8Variant) :
    c8AvailableWithReceiver r v .target = c8Available v .target := by
  simp [c8AvailableWithReceiver]

theorem c8_target_receiver_retains_independent_of_source (r : Receiver)
    (v : C8Variant) (S : List KState) (s : KState) :
    c8ReceiverRetain r v .target S s = c8Retain v .target S s := by
  simp [c8ReceiverRetain, c8Retain,
    c8_target_available_independent_of_source]

theorem c8_target_receiver_iterate_independent_of_source (r : Receiver)
    (v : C8Variant) (n : Nat) :
    c8ReceiverIterate r v .target n = c8Iterate v .target n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [c8ReceiverIterate, c8Iterate, c8ReceiverPrune,
        c8Prune, ih]
      congr 1
      funext s
      exact c8_target_receiver_retains_independent_of_source
        r v (c8Iterate v .target n) s

theorem c8_target_receiver_greatest_independent_of_source (r : Receiver)
    (v : C8Variant) :
    c8ReceiverGreatest r v .target = c8Greatest v .target :=
  c8_target_receiver_iterate_independent_of_source r v kernel.length

theorem c8_target_receiver_viable_independent_of_source (r : Receiver)
    (v : C8Variant) (S : List KState) :
    C8ReceiverViable r v .target S ↔ C8Viable v .target S := by
  simp [C8ReceiverViable, C8Viable,
    c8_target_receiver_retains_independent_of_source]

/-- Re-run the same target C8 test with an explicit source-absent receiver. -/
theorem c8_target_only_after_withdrawal :
    c8WithdrawnReceiver.sourcePresent = false ∧
    c8ReceiverGreatest c8WithdrawnReceiver .funded .target = kernel ∧
    C8ReceiverViable c8WithdrawnReceiver .funded .target
      (c8ReceiverGreatest c8WithdrawnReceiver .funded .target) ∧
    C8ReceiverPass c8WithdrawnReceiver .funded .target := by
  have hgreatest : c8ReceiverGreatest c8WithdrawnReceiver .funded .target =
      kernel := by
    rw [c8_target_receiver_greatest_independent_of_source]
    exact c8_funded_greatest_is_kernel .target
  have hviable : C8ReceiverViable c8WithdrawnReceiver .funded .target
      (c8ReceiverGreatest c8WithdrawnReceiver .funded .target) := by
    rw [c8_target_receiver_viable_independent_of_source,
      c8_target_receiver_greatest_independent_of_source]
    exact c8_funded_is_viable .target
  have hpass : C8ReceiverPass c8WithdrawnReceiver .funded .target := by
    simp only [C8ReceiverPass,
      c8_target_receiver_greatest_independent_of_source,
      c8_target_available_independent_of_source]
    exact c8_funded_each_tag .target
  exact ⟨rfl, hgreatest, hviable, hpass⟩

theorem c8_missing_recharge_fails : ¬ C8Pass .negUnderfund .target := by
  simp only [C8Pass, C8LedgerHolds]
  decide

end CSTTT.POS04
