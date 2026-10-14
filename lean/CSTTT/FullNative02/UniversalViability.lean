import CSTTT.FullNative02.OperationalViability

namespace CSTTT.FullNative02.UniversalViability
set_option autoImplicit false

/-- Arbitrary history carriers and predicates, including hidden past commands.
The only interface requirement is the exact projection of an extension to the
actual supported successor. No finite observer or predicate descent is assumed. -/
abbrev Extension (H : Type) (supply : Supply) (owner : Nat) (world : H → World) :=
  (h : H) → (action : Bool) → (v : World) → (n : Nat) →
    (v,n)∈nativeRows supply (world h) owner action → H

def pre {H : Type} {supply : Supply} {owner : Nat} (world : H → World)
    (next : Extension H supply owner world) (V : H → Prop) (h : H) : Prop :=
  safe (world h) owner ∧ ∃ action,nativeRows supply (world h) owner action≠[] ∧
    ∀ v n (edge : (v,n)∈nativeRows supply (world h) owner action),V (next h action v n edge)
def Invariant {H : Type} {supply : Supply} {owner : Nat} (world : H → World)
    (next : Extension H supply owner world) (V : H → Prop) : Prop := ∀ h,V h→pre world next V h

theorem greatest_operational_arbitrary_histories (H : Type) (owner : Nat) (world : H → World)
    (next : Extension H renewable owner world)
    (projection : ∀ h action v n edge,world (next h action v n edge)=v) :
    Invariant world next (fun h => operationalCore (world h) owner) ∧
    ∀ V,Invariant world next V→∀ h,V h→operationalCore (world h) owner := by
  refine ⟨?_,?_⟩
  · intro h member
    obtain ⟨r,rom,key,enabled,inside⟩ := member
    refine ⟨operational_core_safe _ _ ⟨r,rom,key,enabled,inside⟩,false,
      native_nonempty _ _ _ _ _ enabled renewable false,?_⟩
    intro v n edge
    rw [projection]
    exact operational_core_response _ _ ⟨r,rom,key,enabled,inside⟩ _ _ edge
  · intro V controlled h member
    obtain ⟨safe,action,nonempty,_⟩ := controlled h member
    exact nonblocking_safe_core renewable _ owner safe action nonempty

theorem absent_arbitrary_histories_empty (H : Type) (owner : Nat) (world : H → World)
    (next : Extension H absent owner world)
    (projection : ∀ h action v n edge,world (next h action v n edge)=v)
    (V : H → Prop) (controlled : Invariant world next V) : ∀ h,¬V h := by
  intro h member
  obtain ⟨_,action,nonempty,all⟩ := controlled h member
  obtain ⟨e,edge⟩ := List.exists_mem_of_ne_nil _ nonempty
  have retained := all e.1 e.2 edge
  obtain ⟨_,second,enabled,_⟩ := controlled _ retained
  rw [projection] at enabled
  rw [Operational.absent_successor_no_rows _ _ _ _ _ edge] at enabled
  contradiction

def UniversalC8 (owner : Nat) : Prop :=
  (∀ (H : Type) (world : H → World) (next : Extension H renewable owner world),
    (∀ h action v n edge,world (next h action v n edge)=v)→
    Invariant world next (fun h => operationalCore (world h) owner) ∧
      ∀ V,Invariant world next V→∀ h,V h→operationalCore (world h) owner) ∧
  (∀ (H : Type) (world : H → World) (next : Extension H absent owner world),
    (∀ h action v n edge,world (next h action v n edge)=v)→
    ∀ V,Invariant world next V→∀ h,¬V h)

theorem universal_c8 (owner : Nat) : UniversalC8 owner :=
  ⟨fun H world next projection => greatest_operational_arbitrary_histories H owner world next projection,
    fun H world next projection V controlled => absent_arbitrary_histories_empty H owner world next projection V controlled⟩

end CSTTT.FullNative02.UniversalViability
