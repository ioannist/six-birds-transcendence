import CSTTT.POS04.Assigned.C8Adapters
/-! Method sensitivity guards, not new model declarations. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit

theorem c8_missing_rejected (a : Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c8) : ¬ C8Accept (put a k none) tag := by
  intro h
  exact missing_cell_rejected _ a k hk h.1.1

theorem unavailable8_no_viable (d : ViabilityInputs) (tag : Tag)
    (h : available8 d tag = false) (S : List KState) (hv : Viable8 d tag S) : S = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro s hs
  have hg := greatest8_contains_viable d tag S hv hs
  rw [unavailable8_empty d tag h] at hg
  simp at hg

def noResponses8 (a : Assignment) (tag : Tag) :=
  put a (.rows tag) (some (fun _ _ => []))
def wrongPolicy8 (a : Assignment) := put a .policy (some (fun _ => .stay))
def wrongOwner8 (a : Assignment) (tag : Tag) := mapCell a (.resources tag)
  (fun r => {r with owner := if tag = .source then .target else .source})
def noRecharge8 (a : Assignment) (tag : Tag) := mapCell a (.resources tag)
  (fun r => {r with rechargeAvailable := false})
def zeroBudget8 (a : Assignment) := mapCell a .maintenance
  (fun l => {l with initialBudget := 0})
def doubledCost8 (a : Assignment) := mapCell a .maintenance
  (fun l => {l with actionCost := l.actionCost + l.actionCost})
def zeroReturn8 (a : Assignment) := mapCell a .maintenance
  (fun l => {l with rechargePerAction := 0})

theorem c8_rows_guard (tag : Tag) : ¬ C8Accept (noResponses8 canonical tag) tag := by
  intro h
  have hp := h.2.2.2.2 .p1w0 (by decide) .p2w1 (by decide)
  cases tag <;> change 0 = 4 at hp <;> contradiction

theorem c8_policy_guard (tag : Tag) : ¬ C8Accept (wrongPolicy8 canonical) tag := by
  intro h
  have hp := h.2.2.2.2 .p1w0 (by decide) .p2w1 (by decide)
  cases tag <;> change 0 = 4 at hp <;> contradiction

theorem c8_owner_guard (tag : Tag) : ¬ C8Accept (wrongOwner8 canonical tag) tag := by
  intro h
  have hn : available8 (clause8 (wrongOwner8 canonical tag) tag) tag = false := by
    cases tag <;> decide
  exact Bool.false_ne_true (hn.symm.trans h.2.2.1)

theorem c8_recharge_guard (tag : Tag) : ¬ C8Accept (noRecharge8 canonical tag) tag := by
  intro h
  have hn : available8 (clause8 (noRecharge8 canonical tag) tag) tag = false := by
    cases tag <;> decide
  exact Bool.false_ne_true (hn.symm.trans h.2.2.1)
theorem c8_budget_guard (tag : Tag) : ¬ C8Accept (zeroBudget8 canonical) tag := by
  intro h
  have hn : available8 (clause8 (zeroBudget8 canonical) tag) tag = false := by cases tag <;> decide
  exact Bool.false_ne_true (hn.symm.trans h.2.2.1)
theorem c8_cost_guard (tag : Tag) : ¬ C8Accept (doubledCost8 canonical) tag := by
  intro h
  have hn : available8 (clause8 (doubledCost8 canonical) tag) tag = false := by cases tag <;> decide
  exact Bool.false_ne_true (hn.symm.trans h.2.2.1)
theorem c8_return_guard (tag : Tag) : ¬ C8Accept (zeroReturn8 canonical) tag := by
  intro h
  have hn : available8 (clause8 (zeroReturn8 canonical) tag) tag = false := by cases tag <;> decide
  exact Bool.false_ne_true (hn.symm.trans h.2.2.1)
theorem c8_source_presence_guard : ¬ ReceiverC8Accept (withdraw8 canonical) .source := by
  intro h
  have hn : available8 (receiverData8 (withdraw8 canonical) .source) .source = false := by decide
  exact Bool.false_ne_true (hn.symm.trans h.2.2.2.1)

theorem receiver_c8_missing_rejected (a : Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ receiverScope8 tag) : ¬ ReceiverC8Accept (put a k none) tag := by
  intro h
  exact missing_cell_rejected _ a k hk h.1

/-- Nonempty proper gfp: only the first state has a funded response. A raw
method instance, not a new scientific model or a stored viability verdict. -/
def singletonInputs8 : ViabilityInputs :=
  { legacyViability8 .funded .target with
    rows := fun s a => if s = .p0w0 ∧ a = .stay then [(.inK .p0w0,4)] else [] }
theorem singleton8_viable : Viable8 singletonInputs8 .target [.p0w0] := by
  intro s hs
  have he : s = .p0w0 := by simpa using hs
  subst s
  decide
theorem singleton8_greatest_membership (s : KState) :
    s ∈ greatest8 singletonInputs8 .target ↔ s = .p0w0 := by
  constructor
  · intro hs
    have hv := greatest8_viable singletonInputs8 .target s hs
    cases s <;> simp [retain8,singletonInputs8,actions,rowClosed8] at hv ⊢
  · intro hs
    subst s
    exact greatest8_contains_viable _ _ _ singleton8_viable (by simp)

theorem neg_underfund8_no_viable (S : List KState)
    (h : Viable8 (clause8 (underfund8 canonical) .target) .target S) : S = [] :=
  unavailable8_no_viable _ _ (by decide) S h

theorem c8_canonical_funded_P (tag : Tag) (s t : KState) :
    rowWeight (fundedRow8 (clause8 canonical tag) tag s ((clause8 canonical tag).policy s)) t =
    taggedPNum tag s t := accepted_funded_P_unchanged (c8_canonical_accepts tag) s t

theorem prune8_fixed_iff_viable (d : ViabilityInputs) (tag : Tag) (S : List KState) :
    prune8 d tag S = S ↔ Viable8 d tag S := List.filter_eq_self

theorem greatest8_contains_every_fixed (d : ViabilityInputs) (tag : Tag) (S : List KState)
    (h : prune8 d tag S = S) : S ⊆ greatest8 d tag :=
  greatest8_contains_viable d tag S ((prune8_fixed_iff_viable d tag S).mp h)

end CSTTT.POS04.Assigned
