import CSTTT.FullNative02.HistoryLift
import CSTTT.FullNative02.UniversalViability

namespace CSTTT.FullNative02.UniversalPackageAutonomy
set_option autoImplicit false

def core {H : Type} (owner : Nat) (world : H → World)
    (identity : ROM × Token × Temporal.Residue × Nat) (h : H) : Prop :=
  Package.Accept02 (world h) owner=true ∧ epochIdentity (world h) owner=some identity

def Invariant {H : Type} (owner : Nat) (world : H → World)
    (next : UniversalViability.Extension H renewable owner world)
    (identity : ROM × Token × Temporal.Residue × Nat) (V : H → Prop) : Prop :=
  (∀ h,V h→core owner world identity h) ∧
  ∀ h,V h→nativeRows renewable (world h) owner false≠[] ∧
    ∀ v n (edge : (v,n)∈nativeRows renewable (world h) owner false),V (next h false v n edge)

theorem greatest_package_filtered_arbitrary_histories (H : Type) (owner : Nat) (world : H → World)
    (next : UniversalViability.Extension H renewable owner world)
    (projection : ∀ h action v n edge,world (next h action v n edge)=v)
    (identity : ROM × Token × Temporal.Residue × Nat) :
    Invariant owner world next identity (core owner world identity) ∧
    ∀ V,Invariant owner world next identity V→∀ h,V h→core owner world identity h := by
  refine ⟨⟨fun _ h => h,?_⟩,fun V h => h.1⟩
  intro h member
  obtain ⟨r,key,enabled,_,_,_⟩ := Epoch.accepted_access _ owner member.1
  refine ⟨native_nonempty _ owner r .canonical32 key enabled renewable false,?_⟩
  intro v n edge
  unfold core
  rw [projection]
  have step : Retained owner (world h) v := .next (.root _) v n edge
  exact ⟨Epoch.accepted_native_append _ owner member.1 v n edge,
    (retained_epoch_identity _ _ _ member.1 step).trans member.2⟩

end CSTTT.FullNative02.UniversalPackageAutonomy
