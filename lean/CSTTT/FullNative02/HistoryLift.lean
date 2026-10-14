import CSTTT.FullNative02.FactorLift

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000

def epochIdentity (w : World) (owner : Nat) : Option (ROM × Token × Temporal.Residue × Nat) :=
  (access w owner).map fun data =>
    (data.2.1,data.2.2,⟨data.2.1,data.1.birth,data.1.birthCursor,data.1.roots⟩,data.1.owner)

theorem native_epoch_identity (w : World) (owner : Nat) (r : Resident) (rom : ROM) (key : Token)
    (enabled : access w owner=some (r,rom,key)) (action : Bool) (e : State × Nat) :
    epochIdentity (advance renewable w owner r rom key action e) owner=epochIdentity w owner := by
  simp only [epochIdentity,renewable_access_after _ _ _ _ _ enabled action e,enabled,Option.map_some]

theorem retained_epoch_identity (owner : Nat) (start w : World)
    (accepted : Epoch.accept start owner=true) (history : Retained owner start w) :
    epochIdentity w owner=epochIdentity start owner := by
  induction history with
  | root => rfl
  | @next w past v n edge ih =>
    obtain ⟨r,key,enabled,_,_,_⟩ := Epoch.accepted_access _ owner (retained_acceptance _ _ _ accepted past)
    rw [native_rows_from_access _ _ _ _ _ _ enabled false] at edge
    obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
    have world : v=advance renewable w owner r .canonical32 key false e := (congrArg Prod.fst eq).symm
    rw [world,native_epoch_identity _ _ _ _ _ enabled false e,ih]
  | @foreign w past other different action v n edge ih =>
    obtain ⟨r,key,enabled,_,_,_⟩ := Epoch.accepted_access _ owner (retained_acceptance _ _ _ accepted past)
    cases foreign : access w other with
    | none => simp [nativeRows,foreign] at edge
    | some data =>
      rcases data with ⟨s,rom,k⟩
      rw [native_rows_from_access _ _ _ _ _ _ foreign action] at edge
      obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
      have world : v=advance renewable w other s rom k action e := (congrArg Prod.fst eq).symm
      rw [world]
      simpa only [epochIdentity,enabled,foreign_access_after _ _ _ _ _ _ _ _ _ enabled foreign different action e,
        Option.map_some] using ih

theorem native_custody (supply : Supply) (w v : World) (owner : Nat) (action : Bool)
    (n : Nat) (edge : (v,n)∈nativeRows supply w owner action) :
    v.accounts.custody=w.accounts.custody := by
    cases enabled : access w owner with
    | none => simp [nativeRows,enabled] at edge
    | some data =>
      rcases data with ⟨r,rom,key⟩
      simp only [nativeRows,enabled] at edge
      obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
      cases eq
      rfl

theorem retained_custody (owner : Nat) (start w : World) (history : Retained owner start w) :
    w.accounts.custody=start.accounts.custody := by
  induction history with
  | root => rfl
  | next past v n edge ih => exact (native_custody _ _ _ _ _ _ edge).trans ih
  | foreign past other different action v n edge ih => exact (native_custody _ _ _ _ _ _ edge).trans ih

theorem every_maintenance_length_progresses (owner : Nat) (start : World) (r : Resident) (key : Token)
    (enabled : access start owner=some (r,.canonical32,key)) (accepted : Epoch.accept start owner=true)
    (n : Nat) : ∃ w next,Walk owner start (List.replicate n false) w ∧
      Retained owner start w ∧ Package.Whole w owner ∧ access w owner=some (next,.canonical32,key) ∧
      next.receipts.length=r.receipts.length+n ∧ w.accounts.cursor key=start.accounts.cursor key+n := by
  obtain ⟨w,walk⟩ := every_word_continues owner start r .canonical32 key enabled (List.replicate n false)
  have retained := maintained_walk_retained owner start w n walk
  obtain ⟨next,live,records,cursor,_⟩ := all_word_registers owner start w r .canonical32 key enabled _ walk
  exact ⟨w,next,walk,retained,Package.every_retained_history_whole_package _ _ _ accepted retained,
    live,by simpa using records,by simpa using cursor⟩

def FixedPackageInvariant (owner : Nat) (identity : ROM × Token × Temporal.Residue × Nat)
    (V : Operational.History renewable owner → Prop) : Prop :=
  (∀ h,V h→Epoch.accept h.1 owner=true ∧ epochIdentity h.1 owner=some identity) ∧
  ∀ h,V h→nativeRows renewable h.1 owner false≠[] ∧
    ∀ v n (edge : (v,n)∈nativeRows renewable h.1 owner false),
      V (Operational.extend h false v n edge)

theorem greatest_fixed_package_filtered_autonomy (owner : Nat)
    (identity : ROM × Token × Temporal.Residue × Nat) :
    FixedPackageInvariant owner identity
      (fun h => Epoch.accept h.1 owner=true ∧ epochIdentity h.1 owner=some identity) ∧
    ∀ V,FixedPackageInvariant owner identity V→∀ h,V h→
      Epoch.accept h.1 owner=true ∧ epochIdentity h.1 owner=some identity := by
  refine ⟨⟨fun _ h => h,?_⟩,fun V h => h.1⟩
  intro h member
  obtain ⟨r,key,enabled,_,_,_⟩ := Epoch.accepted_access _ owner member.1
  refine ⟨native_nonempty _ owner r .canonical32 key enabled renewable false,?_⟩
  intro v n edge
  have path : Retained owner h.1 v := .next (.root h.1) v n edge
  exact ⟨Epoch.accepted_native_append _ owner member.1 v n edge,
    (retained_epoch_identity _ _ _ member.1 path).trans member.2⟩

theorem retained_actual_history (owner : Nat) (start w : World)
    (actual : History renewable 8 .canonical32 start) (history : Retained owner start w) :
    History renewable 8 .canonical32 w := by
  induction history with
  | root => exact actual
  | next past v n edge ih => exact .next ih (.native edge)
  | foreign past other different action v n edge ih => exact .next ih (.native edge)

theorem foreign_step_preserves_full_future (w v : World) (owner other : Nat) (r : Resident)
    (key : Token) (own : access w owner=some (r,.canonical32,key)) (different : owner≠other)
    (action : Bool) (n : Nat) (edge : (v,n)∈nativeRows renewable w other action)
    (word : List Bool) (trace : List (Option Temporal.Observation)) :
    WeightedFuture.law (fun w a => normalizedNative renewable w owner a)
      (fun w => (Temporal.actual w owner).map Temporal.observe) w word trace=
    WeightedFuture.law (fun w a => normalizedNative renewable w owner a)
      (fun w => (Temporal.actual w owner).map Temporal.observe) v word trace := by
  cases foreign : access w other with
  | none => simp [nativeRows,foreign] at edge
  | some data =>
    rcases data with ⟨s,rom,k⟩
    rw [native_rows_from_access _ _ _ _ _ _ foreign action] at edge
    obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
    have world : v=advance renewable w other s rom k action e := (congrArg Prod.fst eq).symm
    have live : access v owner=some (r,.canonical32,key) := by
      rw [world]
      exact foreign_access_after _ _ _ _ _ _ _ _ _ own foreign different action e
    have frame : Temporal.frame w r key=Temporal.frame v r key := by
      simp [Temporal.frame,Temporal.frameROM,(access_facts _ _ _ _ _ own).2,(access_facts _ _ _ _ _ live).2]
    exact (Temporal.actual_full_future_exact _ _ _ _ _ _ _ _ own live).mpr
      (congrArg Temporal.code frame) word trace

end CSTTT.FullNative02
