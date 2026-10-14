import CSTTT.FullNative02.OperationalViability
import CSTTT.FullNative02.AcquiredPackage
import CSTTT.FullNative02.Locality

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 8000000

inductive Retained (owner : Nat) : World → World → Prop where
  | root (w : World) : Retained owner w w
  | next {start w : World} (past : Retained owner start w) (v : World) (n : Nat)
      (edge : (v,n)∈nativeRows renewable w owner false) : Retained owner start v
  | foreign {start w : World} (past : Retained owner start w) (other : Nat)
      (different : owner≠other) (action : Bool) (v : World) (n : Nat)
      (edge : (v,n)∈nativeRows renewable w other action) : Retained owner start v

theorem retained_trans (owner : Nat) (start middle finish : World)
    (first : Retained owner start middle) (second : Retained owner middle finish) :
    Retained owner start finish := by
  induction second with
  | root => exact first
  | next past v n edge ih => exact .next ih v n edge
  | foreign past other different action v n edge ih => exact .foreign ih other different action v n edge

theorem retained_acceptance (owner : Nat) (start w : World) (accepted : Epoch.accept start owner=true)
    (history : Retained owner start w) : Epoch.accept w owner=true := by
  induction history with
  | root => exact accepted
  | next past v n edge ih => exact Epoch.accepted_native_append _ owner ih v n edge
  | foreign past other different action v n edge ih =>
    exact foreign_native_preserves_acceptance _ _ owner other ih different action n edge

theorem retained_nonblocking (owner : Nat) (start w : World) (accepted : Epoch.accept start owner=true)
    (history : Retained owner start w) : nativeRows renewable w owner false≠[] := by
  obtain ⟨r,key,enabled,_,_,_⟩ := Epoch.accepted_access w owner (retained_acceptance _ _ _ accepted history)
  exact native_nonempty w owner r .canonical32 key enabled renewable false

def PackageInvariant (owner : Nat) (V : Operational.History renewable owner → Prop) : Prop :=
  (∀ h,V h→Epoch.accept h.1 owner=true) ∧
  ∀ h,V h→nativeRows renewable h.1 owner false≠[] ∧
    ∀ v n (edge : (v,n)∈nativeRows renewable h.1 owner false),
      V (Operational.extend h false v n edge)

theorem greatest_package_filtered_autonomy (owner : Nat) :
    PackageInvariant owner (fun h => Epoch.accept h.1 owner=true) ∧
    ∀ V,PackageInvariant owner V→∀ h,V h→Epoch.accept h.1 owner=true := by
  refine ⟨⟨fun _ h => h,?_⟩,fun V h => h.1⟩
  intro h accepted
  obtain ⟨r,key,enabled,_,_,_⟩ := Epoch.accepted_access _ owner accepted
  exact ⟨native_nonempty _ owner r .canonical32 key enabled renewable false,
    fun v n edge => Epoch.accepted_native_append _ owner accepted v n edge⟩

/-- Stronger than loop access: every inside physical state has an actually
enabled owned maintenance path, with every intermediate account authenticated. -/
theorem owned_reaches_every_inside (owner : Nat) (w : World) (r : Resident) (key : Token)
    (enabled : access w owner=some (r,.canonical32,key)) (target : State)
    (inside : target.outside=false) :
    ∃ v next,Retained owner w v ∧ access v owner=some (next,.canonical32,key) ∧ next.current=target := by
  by_cases phase : target.phase= !r.current.phase
  · let edge := (target,weight r.current target.u target.v)
    have support : edge∈ROM.canonical32.program.rows r.current false :=
      Viability.maintenance_support _ _ inside phase
    let v := advance renewable w owner r .canonical32 key false edge
    have row : (v,edge.2)∈nativeRows renewable w owner false := by
      rw [native_rows_from_access _ _ _ _ _ _ enabled false]
      exact List.mem_map.mpr ⟨edge,support,rfl⟩
    exact ⟨v,_,.next (.root w) v edge.2 row,
      renewable_access_after _ _ _ _ _ enabled false edge,rfl⟩
  · let middle : State := ⟨false,false,false,false,!r.current.phase⟩
    let e := (middle,weight r.current false false)
    have first : e∈ROM.canonical32.program.rows r.current false :=
      Viability.maintenance_support _ _ rfl rfl
    let mid := advance renewable w owner r .canonical32 key false e
    let next : Resident := {r with
      current := e.1
      version := .version w.events.length
      receipts := r.receipts++[makeReceipt renewable w owner r .canonical32 key false e]}
    have midAccess : access mid owner=some (next,.canonical32,key) :=
      renewable_access_after _ _ _ _ _ enabled false e
    have remaining : target.phase= !next.current.phase := by
      change target.phase= !(!r.current.phase)
      cases hp : r.current.phase <;> cases ht : target.phase <;> simp_all
    let f := (target,weight next.current target.u target.v)
    have second : f∈ROM.canonical32.program.rows next.current false :=
      Viability.maintenance_support _ _ inside remaining
    let v := advance renewable mid owner next .canonical32 key false f
    have firstRow : (mid,e.2)∈nativeRows renewable w owner false := by
      rw [native_rows_from_access _ _ _ _ _ _ enabled false]
      exact List.mem_map.mpr ⟨e,first,rfl⟩
    have secondRow : (v,f.2)∈nativeRows renewable mid owner false := by
      rw [native_rows_from_access _ _ _ _ _ _ midAccess false]
      exact List.mem_map.mpr ⟨f,second,rfl⟩
    exact ⟨v,_,.next (.next (.root w) mid e.2 firstRow) v f.2 secondRow,
      renewable_access_after _ _ _ _ _ midAccess false f,rfl⟩

end CSTTT.FullNative02
