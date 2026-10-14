import CSTTT.POS04.Assigned.C8
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit

/-- Availability gates a response; it never rescales or substitutes its row. -/
def fundedRow8 (d : ViabilityInputs) (tag : Tag) (s : KState) (a : Action) :=
  if available8 d tag then d.rows s a else []
theorem funded_row8_unchanged (d : ViabilityInputs) (tag : Tag)
    (h : available8 d tag = true) (s : KState) (a : Action) :
    fundedRow8 d tag s a = d.rows s a := by simp [fundedRow8,h]
theorem accepted_funded_P_unchanged {a : Assignment} {tag : Tag}
    (h : C8Accept a tag) (s t : KState) :
    rowWeight (fundedRow8 (clause8 a tag) tag s ((clause8 a tag).policy s)) t =
    taggedPNum tag s t := by
  rw [funded_row8_unchanged _ _ h.2.2.1]
  have hs : s ∈ kernel := by cases s <;> decide
  have ht : t ∈ kernel := by cases t <;> decide
  exact h.2.2.2.2 s hs t ht

theorem greatest8_eq_kernel (d : ViabilityInputs) (tag : Tag)
    (h : Viable8 d tag kernel) : greatest8 d tag = kernel := by
  apply List.filter_eq_self.mpr
  intro s hs
  exact (List.mem_filter.mp (greatest8_contains_viable d tag kernel h hs)).2

/-- Actual raw recharge deletion, shared with autonomy withdrawal control. -/
def underfund8 (a : Assignment) := mapCell a (.resources .target)
  (fun r => {r with rechargeAvailable := false})
def withdraw8 (a : Assignment) := mapCell a .receiverInput
  (fun r => {r with sourcePresent := false})
def controls8 (v : C8Variant) :=
  match v with | .funded => canonical | .negUnderfund => underfund8 canonical

def legacyViability8 (v : C8Variant) (tag : Tag) : ViabilityInputs :=
  ⟨actionRow tag,canonicalAction,⟨resourceOwner tag,c8Recharge v tag⟩,ledger⟩
theorem controls8_complete (v : C8Variant) (scope : List Cell) : Complete scope (controls8 v) := by
  cases v with
  | funded => exact canonical_complete _
  | negUnderfund => exact mapCell_complete _ _ (canonical_complete _)
theorem controls8_inputs (v : C8Variant) (tag : Tag) :
    clauseInputs (controls8 v) tag .c8 = legacyInputs .positive .positive .position tag := by
  cases v <;> cases tag <;> rfl
theorem controls8_gate (v : C8Variant) (tag : Tag) : C8Gate (controls8 v) tag := by
  refine ⟨controls8_complete _ _,?_⟩
  rw [controls8_inputs]
  exact legacy_rows_valid _ _ _ _
theorem controls8_raw (v : C8Variant) (tag : Tag) :
    clause8 (controls8 v) tag = legacyViability8 v tag := by cases v <;> cases tag <;> rfl

theorem legacy8_available (v : C8Variant) (tag : Tag) :
    available8 (legacyViability8 v tag) tag = c8Available v tag := by cases tag <;> simp [available8,legacyViability8,c8Available]
theorem legacy8_row_closed (v : C8Variant) (tag : Tag) (s : KState)
    (a : Action) (S : List KState) :
    rowClosed8 (legacyViability8 v tag) s a S = c8RowClosed tag s a S := rfl
theorem legacy8_retain (v : C8Variant) (tag : Tag) (S : List KState) (s : KState) :
    retain8 (legacyViability8 v tag) tag S s = c8Retain v tag S s := by
  simp only [retain8,c8Retain,legacy8_available,legacy8_row_closed]
theorem legacy8_viable (v : C8Variant) (tag : Tag) (S : List KState) :
    Viable8 (legacyViability8 v tag) tag S ↔ C8Viable v tag S := by
  simp only [Viable8,C8Viable,legacy8_retain]

theorem controls8_greatest (v : C8Variant) (tag : Tag) :
    greatest8 (clause8 (controls8 v) tag) tag = c8Greatest v tag := by
  rw [controls8_raw]
  cases v with
  | funded =>
    rw [c8_funded_greatest_is_kernel]
    exact greatest8_eq_kernel _ _ ((legacy8_viable _ _ _).mpr (by simpa only [c8_funded_greatest_is_kernel] using c8_funded_is_viable tag))
  | negUnderfund =>
    cases tag with
    | source =>
      have he : legacyViability8 .negUnderfund .source = legacyViability8 .funded .source := rfl
      rw [he]
      have hg : c8Greatest .negUnderfund .source = kernel := by decide
      rw [hg]
      exact greatest8_eq_kernel _ _ ((legacy8_viable _ _ _).mpr (by simpa only [c8_funded_greatest_is_kernel] using c8_funded_is_viable .source))
    | target =>
      rw [neg_c8_underfund_empty]
      exact unavailable8_empty _ _ (by decide)

theorem controls8_equivalence (v : C8Variant) (tag : Tag) :
    C8Accept (controls8 v) tag ↔ C8Pass v tag := by
  unfold C8Accept
  rw [controls8_greatest,controls8_raw,legacy8_available]
  change (C8Gate (controls8 v) tag ∧ C8Pass v tag) ↔ C8Pass v tag
  exact and_iff_right (controls8_gate v tag)

theorem c8_canonical_equivalence (tag : Tag) : C8Accept canonical tag ↔ C8Pass .funded tag :=
  controls8_equivalence .funded tag
theorem c8_canonical_accepts (tag : Tag) : C8Accept canonical tag :=
  (c8_canonical_equivalence tag).mpr (c8_funded_each_tag tag)
theorem neg_c8_underfund_outcome :
    greatest8 (clause8 (underfund8 canonical) .target) .target = [] ∧
    ¬ C8Accept (underfund8 canonical) .target ∧ C8Accept (underfund8 canonical) .source := by
  refine ⟨?_,?_,?_⟩
  · exact (controls8_greatest .negUnderfund .target).trans neg_c8_underfund_empty
  · exact fun h => c8_missing_recharge_fails ((controls8_equivalence _ _).mp h)
  · apply (controls8_equivalence .negUnderfund .source).mpr
    exact c8_funded_each_tag .source

/-- Package scopes do not read receiver presence. Withdrawal changes the
receiver only, leaving the package input and algorithm identical on both tags. -/
theorem clause8_withdraw (a : Assignment) (tag : Tag) :
    clause8 (withdraw8 a) tag = clause8 a tag := by
  apply clause8_locality
  intro k hk
  have hn : k ≠ Cell.receiverInput := by
    intro he
    subst k
    cases tag <;> simp [clauseScope] at hk
  exact mapCell_other_cell a .receiverInput k _ hn

/-- Even deleting the receiver input cannot affect package C8. Availability
for a receiver is checked separately, on the larger receiver scope. -/
theorem package8_ignores_receiver (a : Assignment) (tag : Tag) (r : Option Receiver) :
    C8Accept (put a .receiverInput r) tag ↔ C8Accept a tag := by
  apply c8_accept_locality
  intro k hk
  have hn : k ≠ Cell.receiverInput := by
    intro he
    subst k
    cases tag <;> simp [clauseScope] at hk
  exact put_other a .receiverInput k r hn

theorem withdraw8_gate (v : C8Variant) (tag : Tag) : C8Gate (withdraw8 (controls8 v)) tag := by
  refine ⟨mapCell_complete _ _ (controls8_complete _ _),?_⟩
  have he : clauseInputs (withdraw8 (controls8 v)) tag .c8 =
      legacyInputs .positive .positive .position tag := by cases v <;> cases tag <;> rfl
  rw [he]
  exact legacy_rows_valid _ _ _ _

theorem withdrawn8_package_equivalence (v : C8Variant) (tag : Tag) :
    C8Accept (withdraw8 (controls8 v)) tag ↔ C8Pass v tag := by
  unfold C8Accept
  rw [clause8_withdraw]
  have h := controls8_equivalence v tag
  simp only [C8Accept,controls8_gate,true_and] at h
  simpa only [withdraw8_gate,true_and] using h

/-- Receiver-specific source availability is an additional gate. Its input
is derived, never supplied: it uses the same package rows/ledger/resource, and
removes recharge availability for a source response when source is absent.
The greatest-set algorithm is the shared arbitrary-data greatest8. -/
def receiverScope8 (tag : Tag) := clauseScope tag .c8 ++ [.receiverInput]
def receiverPresent8 (a : Assignment) : Bool :=
  ((a .receiverInput).map Receiver.sourcePresent).getD false
def receiverData8 (a : Assignment) (tag : Tag) : ViabilityInputs :=
  let d := clause8 a tag
  { d with resource := { d.resource with rechargeAvailable :=
      d.resource.rechargeAvailable && (if tag = .source then receiverPresent8 a else true) } }
def ReceiverC8Accept (a : Assignment) (tag : Tag) : Prop :=
  Complete (receiverScope8 tag) a ∧ C8Gate a tag ∧
  greatest8 (receiverData8 a tag) tag ≠ [] ∧
  available8 (receiverData8 a tag) tag = true ∧
  Ledger8 (clause8 a tag) ∧ PUnchanged8 (clause8 a tag)

theorem receiver_data8_target (a : Assignment) :
    receiverData8 a .target = clause8 a .target := by
  simp [receiverData8]

theorem receiver_data8_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (receiverScope8 tag) a b) : receiverData8 a tag = receiverData8 b tag := by
  have hc : Agrees (clauseScope tag .c8) a b := fun k hk => h k (List.mem_append_left _ hk)
  have hp := h .receiverInput (by simp [receiverScope8])
  simp only [receiverData8,clause8_locality hc,receiverPresent8,hp]
theorem receiver_c8_accept_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (receiverScope8 tag) a b) : ReceiverC8Accept a tag ↔ ReceiverC8Accept b tag := by
  have hc : Agrees (clauseScope tag .c8) a b := fun k hk => h k (List.mem_append_left _ hk)
  have hcomp : Complete (receiverScope8 tag) a ↔ Complete (receiverScope8 tag) b := by
    unfold Complete
    constructor <;> intro hv k hk
    · rw [← h k hk]; exact hv k hk
    · rw [h k hk]; exact hv k hk
  simp only [ReceiverC8Accept,hcomp,c8_gate_locality hc,clause8_locality hc,
    receiver_data8_locality h]

theorem withdrawn8_equivalence (v : C8Variant) :
    ReceiverC8Accept (withdraw8 (controls8 v)) .target ↔ C8ReceiverPass c8WithdrawnReceiver v .target := by
  simp only [ReceiverC8Accept,receiver_data8_target]
  have hg := withdraw8_gate v .target
  have hc : Complete (receiverScope8 .target) (withdraw8 (controls8 v)) :=
    mapCell_complete _ _ (controls8_complete _ _)
  simp only [hc,hg,true_and,clause8_withdraw]
  have he := controls8_equivalence v .target
  simp only [C8Accept,controls8_gate,true_and] at he
  rw [he]
  simp only [C8ReceiverPass,c8_target_receiver_greatest_independent_of_source,
    c8_target_available_independent_of_source,C8Pass]

theorem c8_target_only_assignment :
    receiverPresent8 (withdraw8 canonical) = false ∧
    greatest8 (receiverData8 (withdraw8 canonical) .target) .target = kernel ∧
    Viable8 (receiverData8 (withdraw8 canonical) .target) .target
      (greatest8 (receiverData8 (withdraw8 canonical) .target) .target) ∧
    ReceiverC8Accept (withdraw8 canonical) .target ∧ C8Accept (withdraw8 canonical) .target := by
  refine ⟨rfl,?_,greatest8_viable _ _,?_,?_⟩
  · rw [receiver_data8_target,clause8_withdraw]
    exact (controls8_greatest .funded .target).trans (c8_funded_greatest_is_kernel .target)
  · exact (withdrawn8_equivalence .funded).mpr c8_target_only_after_withdrawal.2.2.2
  · exact (withdrawn8_package_equivalence .funded .target).mpr (c8_funded_each_tag .target)

theorem neg_autonomy_withdraw_assignment :
    greatest8 (receiverData8 (withdraw8 (underfund8 canonical)) .target) .target = [] ∧
    ¬ ReceiverC8Accept (withdraw8 (underfund8 canonical)) .target ∧
    ¬ C8Accept (withdraw8 (underfund8 canonical)) .target ∧
    C8Accept (withdraw8 (underfund8 canonical)) .source := by
  refine ⟨?_,?_,?_,?_⟩
  · rw [receiver_data8_target,clause8_withdraw]
    exact neg_c8_underfund_outcome.1
  · intro h
    have hp := (withdrawn8_equivalence .negUnderfund).mp h
    have hn := hp.1
    rw [neg_autonomy_withdraw_empty] at hn
    exact hn rfl
  · exact fun h => c8_missing_recharge_fails ((withdrawn8_package_equivalence .negUnderfund .target).mp h)
  · exact (withdrawn8_package_equivalence .negUnderfund .source).mpr (c8_funded_each_tag .source)

/-- Exact per-tag package C8 outcomes in M3b: both recharge-removal
interventions reject target C8 only. Presence removal alone rejects neither. -/
theorem c8_m3b_per_tag_outcomes :
    (C8Accept (underfund8 canonical) .source ∧ ¬ C8Accept (underfund8 canonical) .target) ∧
    (C8Accept (withdraw8 (underfund8 canonical)) .source ∧
      ¬ C8Accept (withdraw8 (underfund8 canonical)) .target) ∧
    (C8Accept (withdraw8 canonical) .source ∧ C8Accept (withdraw8 canonical) .target) := by
  exact ⟨⟨neg_c8_underfund_outcome.2.2,neg_c8_underfund_outcome.2.1⟩,
    ⟨neg_autonomy_withdraw_assignment.2.2.2,neg_autonomy_withdraw_assignment.2.2.1⟩,
    (withdrawn8_package_equivalence .funded .source).mpr (c8_funded_each_tag .source),
    (withdrawn8_package_equivalence .funded .target).mpr (c8_funded_each_tag .target)⟩

end CSTTT.POS04.Assigned
