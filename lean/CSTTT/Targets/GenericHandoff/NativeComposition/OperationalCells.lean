import CSTTT.Targets.GenericHandoff.NativeComposition.AvailabilityPublication

/-! C8 uses the same selected native rows, safe policy, ledger and resource
owner as C6 and actual acquisition. The greatest viable set is computed;
no viability set or verdict is a primitive field. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOperationalCells
open RegisterInterpreter

def schema (owner : Owner) : OperationalViability.Schema Factor Bool Factor Owner :=
  ⟨factors,[false,true],some,1,owner,⟨1,1,1⟩,fun s t => if s=t then 1 else 0⟩
def data (i : Input) : OperationalViability.Raw Factor Bool Factor Owner :=
  ⟨i.temporal.rows,i.temporal.policy,i.temporal.resource,i.temporal.ledger⟩
def bindings (cell : Owner) (copy : Bool) : OperationalViability.Bindings Owner MemoryValue Factor Bool Factor Owner :=
  let get := MemoryFrames.selectInput copy
  ⟨⟨cell,fun p => (get p).temporal.rows⟩,⟨cell,fun p => (get p).temporal.policy⟩,
    ⟨cell,fun p => (get p).temporal.resource⟩,⟨cell,fun p => (get p).temporal.ledger⟩⟩

theorem decoded (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) :
    OperationalViability.decoded (bindings cell copy) a=
      (a cell).map (fun p => data (MemoryFrames.selectInput copy p)) := by
  cases ha : a cell <;> simp [OperationalViability.decoded,bindings,CellView.read,ha,data]
theorem acceptance_iff (owner cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) :
    OperationalCells.Accept (schema owner) factors (bindings cell copy) a ↔
      ∃ p, a cell=some p ∧ OperationalViability.Accept (schema owner) (data (MemoryFrames.selectInput copy p)) ∧
        OperationalCells.RowsValid (schema owner) factors (data (MemoryFrames.selectInput copy p)) := by
  simp only [OperationalCells.Accept,decoded]
  cases a cell <;> simp
theorem missing_rejected (owner cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) (hm : a cell=none) :
    ¬ OperationalCells.Accept (schema owner) factors (bindings cell copy) a := by
  rw [acceptance_iff]
  simp [hm]

theorem greatest_equation (owner : Owner) :
    OperationalViability.greatest (schema owner) (data (AvailabilityFactor.input owner))=factors := by
  cases owner <;> decide +kernel
theorem actual_accept (owner : Owner) :
    OperationalViability.Accept (schema owner) (data (AvailabilityFactor.input owner)) := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · change factors.Nodup ∧ (∀ s : Factor, s∈factors) ∧
      ([false,true] : List Bool).Nodup ∧ (∀ a : Bool, a∈[false,true]) ∧
      ([false,true] : List Bool)≠[] ∧ (1 : Nat)>0
    refine ⟨by decide +kernel,factor_mem,by decide +kernel,?_,by decide +kernel,by decide +kernel⟩
    intro a; cases a <;> decide +kernel
  · rw [greatest_equation]; decide +kernel
  · cases owner <;> rfl
  · cases owner <;> exact ⟨rfl,rfl,rfl,rfl,rfl⟩
  · intro s hs t ht
    exact AvailabilityFactor.safe_policy_weight owner s t
theorem actual_rows_valid (owner : Owner) :
    OperationalCells.RowsValid (schema owner) factors (data (AvailabilityFactor.input owner)) := by
  refine ⟨factor_mem,?_⟩
  intro s hs a ha
  change (∀ e ∈ AvailabilityFactor.rows s a, e.2>0 ∧ e.1∈factors) ∧
      ((AvailabilityFactor.rows s a).map Prod.snd).sum=0 ∨
    (∀ e ∈ AvailabilityFactor.rows s a, e.2>0 ∧ e.1∈factors) ∧
      ((AvailabilityFactor.rows s a).map Prod.snd).sum=1
  by_cases hb : (a && !s.2.1)=true
  · left; simp [AvailabilityFactor.rows,hb]
  · right
    refine ⟨?_,by simp [AvailabilityFactor.rows,hb]⟩
    intro e he
    have heq : e=(destination s a,1) := by simpa [AvailabilityFactor.rows,hb] using he
    subst e
    exact ⟨Nat.zero_lt_succ _,factor_mem _⟩

theorem selected_data (cell : Owner) (copy : Bool) :
    data (AvailabilityPublication.selected cell copy)=
      data (AvailabilityFactor.input (AvailabilityPublication.dataOwner cell copy)) := by
  cases cell <;> cases copy <;> rfl
theorem canonical_decoded (cell : Owner) (copy : Bool) :
    OperationalViability.decoded (bindings cell copy) AvailabilityPublication.native=
      some (data (AvailabilityFactor.input (AvailabilityPublication.dataOwner cell copy))) := by
  cases cell <;> cases copy <;> rfl
theorem c8 (cell : Owner) (copy : Bool) :
    OperationalCells.Accept (schema (AvailabilityPublication.dataOwner cell copy)) factors
      (bindings cell copy) AvailabilityPublication.native :=
  ⟨_,canonical_decoded cell copy,actual_accept _,actual_rows_valid _⟩

def cutRecharge (i : Input) : Input :=
  {i with temporal := {i.temporal with resource := {i.temporal.resource with rechargeAvailable := false}}}
theorem cut_actual_c8_rejected (owner : Owner) (i : Input) :
    ¬ OperationalViability.Accept (schema owner) (data (cutRecharge i)) :=
  OperationalViability.no_recharge_rejected _ _ rfl
theorem cut_actual_greatest_empty (owner : Owner) (i : Input) :
    OperationalViability.greatest (schema owner) (data (cutRecharge i))=[] := by
  apply OperationalViability.unavailable_empty _ _ factor_mem
  simp [OperationalViability.available,data,cutRecharge]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeOperationalCells
