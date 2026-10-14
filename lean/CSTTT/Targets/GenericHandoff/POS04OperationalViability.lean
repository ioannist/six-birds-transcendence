import CSTTT.Targets.GenericHandoff.OperationalViability
import CSTTT.Targets.GenericHandoff.POS04ViableSet
import CSTTT.Targets.GenericHandoff.POS04ObjecthoodQuotient
import CSTTT.POS04.Assigned.C8Guards

/-! Exact arbitrary-partial-assignment specialization of operational C8.
Package C8 is independent of receiver presence. No new run-to-factor claim is
hidden in this finite-operator adapter. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04OperationalViability
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

def schema (tag : Tag) : OperationalViability.Schema KState Action Ambient Tag :=
  ⟨kernel,actions,(fun o => match o with | .inK s => some s | _ => none),4,tag,
    ⟨ledger.initialBudget,ledger.actionCost,ledger.rechargePerAction⟩,
    (fun s t => pNum (index s) (index t))⟩
def raw (d : ViabilityInputs) : OperationalViability.Raw KState Action Ambient Tag :=
  ⟨d.rows,d.policy,⟨d.resource.owner,d.resource.rechargeAvailable⟩,
    ⟨d.budget.initialBudget,d.budget.actionCost,d.budget.rechargePerAction⟩⟩

theorem available_eq (d : ViabilityInputs) (tag : Tag) :
    OperationalViability.available (schema tag) (raw d) = available8 d tag := rfl

theorem row_closed_eq (d : ViabilityInputs) (tag : Tag) (s : KState) (a : Action) (set : List KState) :
    OperationalViability.rowClosed (schema tag) (raw d) s a set = rowClosed8 d s a set := by
  unfold OperationalViability.rowClosed rowClosed8
  apply congrArg (fun f => !((d.rows s a).isEmpty) && decide (((d.rows s a).map Prod.snd).sum = 4) &&
    (d.rows s a).all f)
  funext e
  cases e.1 <;> rfl

theorem retain_eq (d : ViabilityInputs) (tag : Tag) :
    OperationalViability.retain (schema tag) (raw d) = retain8 d tag := by
  funext set s
  simp only [OperationalViability.retain,retain8,available_eq,row_closed_eq]
  rfl

theorem greatest_eq (d : ViabilityInputs) (tag : Tag) :
    OperationalViability.greatest (schema tag) (raw d) = greatest8 d tag := by
  unfold OperationalViability.greatest
  rw [retain_eq]
  exact POS04Adapter.c8_engine_eq d tag

theorem weight_eq (d : ViabilityInputs) (tag : Tag) (s t : KState) :
    OperationalViability.weight (schema tag) (raw d) s t = rowWeight (d.rows s (d.policy s)) t := by
  rw [POS04ObjecthoodQuotient.rowWeight_sum]
  unfold OperationalViability.weight
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  cases e.1 <;> simp [schema]

theorem domain_checked (tag : Tag) : OperationalViability.DomainCheck (schema tag) :=
  by cases tag <;> exact ⟨by decide,(by intro s; cases s <;> decide),by decide,
    (by intro a; cases a <;> decide),by decide,by decide⟩

theorem rule_iff (d : ViabilityInputs) (tag : Tag) :
    OperationalViability.Accept (schema tag) (raw d) ↔
    greatest8 d tag ≠ [] ∧ available8 d tag = true ∧ Ledger8 d ∧ PUnchanged8 d := by
  unfold OperationalViability.Accept
  rw [and_iff_right (domain_checked tag),greatest_eq,available_eq]
  simp only [OperationalViability.PUnchanged,weight_eq]
  rfl

def bindings (tag : Tag) : OperationalViability.Bindings Cell Value KState Action Ambient Tag :=
  ⟨⟨.rows tag,id⟩,⟨.policy,id⟩,
   ⟨.resources tag,fun r => ⟨r.owner,r.rechargeAvailable⟩⟩,
   ⟨.maintenance,fun l => ⟨l.initialBudget,l.actionCost,l.rechargePerAction⟩⟩⟩

theorem scope_eq (tag : Tag) : (bindings tag).scope = clauseScope tag .c8 := rfl

set_option maxHeartbeats 2000000 in
open Classical in
theorem decoded_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    OperationalViability.decoded (bindings tag) a =
      if Complete (clauseScope tag .c8) a then some (raw (viabilityInputs a tag)) else none := by
  cases hr : a (.rows tag) <;> cases hp : a .policy <;>
    cases hres : a (.resources tag) <;> cases hl : a .maintenance <;>
    simp [OperationalViability.decoded,bindings,CellView.read,Complete,clauseScope,
      raw,viabilityInputs,hr,hp,hres,hl]

theorem raw_scoped (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    raw (viabilityInputs a tag) = raw (clause8 a tag) := by cases tag <;> rfl

/-- The row well-formedness check remains an independent computed assigned
input gate; the generic viability rule itself supplies the other conditions. -/
def AssignedAccept (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) : Prop :=
  RowsValid (clauseInputs a tag .c8) ∧
  OperationalViability.AssignedAccept (schema tag) (bindings tag) a

theorem generic_c8_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    AssignedAccept a tag ↔ C8Accept a tag := by
  unfold AssignedAccept OperationalViability.AssignedAccept C8Accept C8Gate Ready
  rw [decoded_eq,raw_scoped]
  have hc : Complete (clauseScope tag .c8) a ↔
      CSTTT.POS04.Assigned.Complete (clauseScope tag .c8) a := Iff.rfl
  simp only [hc]
  by_cases h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c8) a <;> simp [h,rule_iff]

theorem canonical_accept (tag : Tag) : AssignedAccept canonical tag :=
  (generic_c8_iff _ _).mpr (c8_canonical_accepts tag)
theorem control_equivalence (v : C8Variant) (tag : Tag) :
    AssignedAccept (controls8 v) tag ↔ C8Pass v tag :=
  (generic_c8_iff _ _).trans (controls8_equivalence v tag)

theorem underfund_control :
    ¬ AssignedAccept (underfund8 canonical) .target ∧ AssignedAccept (underfund8 canonical) .source :=
  ⟨fun h => neg_c8_underfund_outcome.2.1 ((generic_c8_iff _ _).mp h),
   (generic_c8_iff _ _).mpr neg_c8_underfund_outcome.2.2⟩

theorem withdrawal_independent (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    AssignedAccept (withdraw8 a) tag ↔ AssignedAccept a tag := by
  rw [generic_c8_iff,generic_c8_iff]
  unfold C8Accept
  rw [clause8_withdraw]
  have hg : C8Gate (withdraw8 a) tag ↔ C8Gate a tag := by
    apply ready_locality
    intro k hk
    have hn : k ≠ Cell.receiverInput := by
      intro he; subst k; cases tag <;> simp [clauseScope] at hk
    exact mapCell_other_cell a .receiverInput k _ hn
  rw [hg]
theorem missing_rejected (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c8) : ¬ AssignedAccept (put a k none) tag :=
  fun h => c8_missing_rejected a tag k hk ((generic_c8_iff _ _).mp h)

theorem withdrawn_control_equivalence (v : C8Variant) (tag : Tag) :
    AssignedAccept (withdraw8 (controls8 v)) tag ↔ C8Pass v tag :=
  (generic_c8_iff _ _).trans (withdrawn8_package_equivalence v tag)

theorem rows_guard (tag : Tag) : ¬ AssignedAccept (noResponses8 canonical tag) tag :=
  fun h => c8_rows_guard tag ((generic_c8_iff _ _).mp h)

theorem policy_guard (tag : Tag) : ¬ AssignedAccept (wrongPolicy8 canonical) tag :=
  fun h => c8_policy_guard tag ((generic_c8_iff _ _).mp h)

theorem owner_guard (tag : Tag) : ¬ AssignedAccept (wrongOwner8 canonical tag) tag :=
  fun h => c8_owner_guard tag ((generic_c8_iff _ _).mp h)

theorem recharge_guard (tag : Tag) : ¬ AssignedAccept (noRecharge8 canonical tag) tag :=
  fun h => c8_recharge_guard tag ((generic_c8_iff _ _).mp h)

theorem budget_guard (tag : Tag) : ¬ AssignedAccept (zeroBudget8 canonical) tag :=
  fun h => c8_budget_guard tag ((generic_c8_iff _ _).mp h)

theorem cost_guard (tag : Tag) : ¬ AssignedAccept (doubledCost8 canonical) tag :=
  fun h => c8_cost_guard tag ((generic_c8_iff _ _).mp h)

theorem return_guard (tag : Tag) : ¬ AssignedAccept (zeroReturn8 canonical) tag :=
  fun h => c8_return_guard tag ((generic_c8_iff _ _).mp h)

end CSTTT.TargetTheory.GenericHandoff.POS04OperationalViability
