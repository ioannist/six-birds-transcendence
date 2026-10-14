import CSTTT.FullNative.OriginalPackage
import CSTTT.Prospects.Statements

/-! G28 TTN-02: the original PublicShadowCountermodel predicate with G27's
actual whole-package acceptance, not a supplied hidden bit. Both points are
historical native target executions; their frozen CURRENT observations agree.
The negative point is a supported funded prefix with a rejected cycle audit. -/
namespace CSTTT.FullNative.PublicShadow
open AccountExecution PhysicalExecution SnapshotExecution SharedPackage OriginalPackage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

def before : Raw := targetRaw false
def beforeExecution : Execution := targetExecution false
def afterExecution : Execution := Binding.splitExecution beforeExecution false
def after : Raw := ⟨mount before.world before.owner afterExecution,before.owner⟩
def shadow (p : Raw) : Option (Nat × Nat × Nat) := (execution p).map Binding.actualCurrent

theorem before_read : execution before=some beforeExecution := target_read false
theorem decoded_owner (p : Raw) (x : Execution) (read : execution p=some x) : x.resident.owner=p.owner := by
  cases present : p.world.carriers p.owner with
  | none => simp [execution,present] at read
  | some resident =>
    by_cases owner : resident.owner=p.owner
    · have equal : x=⟨p.world.accounts,resident⟩ := by simpa [execution,present,owner] using read.symm
      rw [equal]
      exact owner
    · simp [execution,present,owner] at read

theorem decoded_resident (p : Raw) (x : Execution) (read : execution p=some x) :
    p.world.carriers p.owner=some x.resident := by
  cases present : p.world.carriers p.owner with
  | none => simp [execution,present] at read
  | some resident =>
    by_cases owner : resident.owner=p.owner
    · have equal : x=⟨p.world.accounts,resident⟩ := by simpa [execution,present,owner] using read.symm
      simpa only [equal] using present
    · simp [execution,present,owner] at read

theorem mounted_read (p : Raw) (x : Execution) (owner : x.resident.owner=p.owner) :
    execution ⟨mount p.world p.owner x,p.owner⟩=some x := by
  simp [execution,mount,putOwner,owner]

theorem after_read : execution after=some afterExecution :=
  mounted_read before afterExecution (decoded_owner before beforeExecution before_read)
theorem before_accepted : Accept before := source_and_both_targets.2 false
theorem after_sector : sector afterExecution := Binding.actual_split_sectors _ (actual_ready.2 false).1 false

theorem shadow_inside (p : Raw) (x : Execution) (read : execution p=some x)
    (funded : sector x) (inside : x.resident.current.outside=false) : shadow p=some (0,16,16) := by
  rw [shadow,read,Option.map_some,Binding.actual_current_sector x funded,Binding.inside_public _ inside]

theorem actual_shadow_equal : shadow before=shadow after :=
  (shadow_inside before beforeExecution before_read (actual_ready.2 false).1 (actual_ready.2 false).2.1).trans
    (shadow_inside after afterExecution after_read after_sector rfl).symm

theorem after_credit_rejected : credit afterExecution=.rejected := by decide +kernel
theorem actual_c5_rejected : ¬C5 afterExecution := by
  intro h
  have bad := h.1
  rw [after_credit_rejected] at bad
  contradiction

theorem after_package_rejected : ¬Accept after := by
  apply (raw_gate_rejected after afterExecution after_read ?_).1
  intro h
  have bad := h.2.2
  rw [after_credit_rejected] at bad
  contradiction

theorem actual_histories : Historical before.world ∧ Historical after.world :=
  ⟨Credit.credited_both_historical,(actual_historical_splits false).2 false⟩

theorem actual_step :
    (after.world,weight beforeExecution.resident.current false false)∈
      nativeRows renewable before.world before.owner false :=
  Binding.world_split_supported before.world before.owner beforeExecution.resident
    (decoded_resident before beforeExecution before_read) (decoded_owner before beforeExecution before_read)
    (actual_ready.2 false).1 false

theorem actual_profile_different :
    classes model beforeExecution.resident.current≠classes model afterExecution.resident.current := by decide +kernel

theorem actual_countertrace :
    (frame beforeExecution).context.order=6 ∧ (frame afterExecution).context.order=7 ∧
    afterExecution.resident.receipts.length=7 ∧ afterExecution.accounts.portCursor 1=7 ∧
    (afterExecution.resident.receipts.head?).map Receipt.serial=some 25 ∧
    (afterExecution.resident.receipts.head?).map Receipt.issuer=some (.localGenerator 1) ∧
    (afterExecution.resident.receipts.head?).map Receipt.energy=some (some ()) ∧
    Viability.core (Viability.quote afterExecution)=true := by decide +kernel

theorem funded_clock_survives : ClockAudit afterExecution :=
  ⟨ClockClosure.every_word_continues _ after_sector,
    fun y word path => ClockClosure.route_registers path after_sector,
    ClockClosure.maintained_words_continue _ after_sector rfl⟩

/-- CURRENT equality cannot be silently widened to all public futures: the
registered probe exposes the phase difference on its actual next public lens. -/
theorem public_future_extension_countertrace :
    Binding.emittedLaw (normalizedRows renewable) (fun x => publicLens x.resident.current)
      beforeExecution [true] [2]=1 ∧
    Binding.emittedLaw (normalizedRows renewable) (fun x => publicLens x.resident.current)
      afterExecution [true] [2]=0 := by
  constructor
  · rw [Binding.actual_emitted_law publicLens beforeExecution (actual_ready.2 false).1]
    decide +kernel
  · rw [Binding.actual_emitted_law publicLens afterExecution after_sector]
    decide +kernel

/-- Full original generic TTN-02 predicate, instantiated with the actual G27
package predicate and its fixed CURRENT interface. No hidden verdict input. -/
theorem full_ttn02 : CSTTT.Prospects.PublicShadowCountermodel Raw
    (Option (Nat × Nat × Nat)) shadow Accept :=
  ⟨before,after,actual_shadow_equal,before_accepted,after_package_rejected⟩

theorem full_ttn02_with_actual_readouts :
    Historical before.world ∧ Historical after.world ∧
    shadow before=shadow after ∧ Accept before ∧ ¬Accept after ∧ ¬C5 afterExecution :=
  ⟨actual_histories.1,actual_histories.2,actual_shadow_equal,before_accepted,
    after_package_rejected,actual_c5_rejected⟩

end CSTTT.FullNative.PublicShadow
