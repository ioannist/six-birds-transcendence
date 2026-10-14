import CSTTT.FullNative02.NativeAccounts

namespace CSTTT.FullNative02.Operational
open FullNative
set_option autoImplicit false

/-- A Type-valued path retains its entire sequence of worlds and actions.
Competitors may inspect this path and need not descend to any finite factor. -/
inductive Path (supply : Supply) (owner : Nat) : World → Type where
  | root (w : World) : Path supply owner w
  | next {w : World} (past : Path supply owner w) (action : Bool) (v : World) (n : Nat)
      (edge : (v,n)∈nativeRows supply w owner action) : Path supply owner v

abbrev History (supply : Supply) (owner : Nat) := (w : World) × Path supply owner w
def extend {supply : Supply} {owner : Nat} (h : History supply owner) (action : Bool)
    (v : World) (n : Nat) (edge : (v,n)∈nativeRows supply h.1 owner action) : History supply owner :=
  ⟨v,.next h.2 action v n edge⟩
def pre {supply : Supply} {owner : Nat} (V : History supply owner → Prop)
    (h : History supply owner) : Prop :=
  safe h.1 owner ∧ ∃ action,nativeRows supply h.1 owner action≠[] ∧
    ∀ v n (edge : (v,n)∈nativeRows supply h.1 owner action),V (extend h action v n edge)
def Invariant {supply : Supply} {owner : Nat} (V : History supply owner → Prop) : Prop :=
  ∀ h,V h→pre V h
def core {supply : Supply} {owner : Nat} (h : History supply owner) : Prop := operationalCore h.1 owner

theorem pre_monotone {supply : Supply} {owner : Nat} (V W : History supply owner → Prop)
    (order : ∀ h,V h→W h) (h : History supply owner) (hp : pre V h) : pre W h := by
  obtain ⟨safe,a,nonempty,successors⟩ := hp
  exact ⟨safe,a,nonempty,fun v n edge => order _ (successors v n edge)⟩

theorem every_invariant_inside_operational_core {supply : Supply} {owner : Nat}
    (V : History supply owner → Prop) (invariant : Invariant V) (h : History supply owner)
    (member : V h) : core h := by
  obtain ⟨safe,a,nonempty,_⟩ := invariant h member
  exact nonblocking_safe_core supply h.1 owner safe a nonempty

theorem operational_core_invariant (owner : Nat) : @Invariant renewable owner core := by
  intro h member
  refine ⟨operational_core_safe h.1 owner member,false,?_,?_⟩
  · obtain ⟨r,rom,key,enabled,_⟩ := member
    exact native_nonempty h.1 owner r rom key enabled renewable false
  · intro v n edge
    exact operational_core_response h.1 owner member v n edge

theorem greatest_operational_c8 (owner : Nat) :
    @Invariant renewable owner core ∧
      ∀ V : History renewable owner → Prop,Invariant V→∀ h,V h→core h :=
  ⟨operational_core_invariant owner,fun V h => every_invariant_inside_operational_core V h⟩

theorem absent_successor_no_rows (w : World) (owner : Nat) (action : Bool)
    (v : World) (n : Nat) (edge : (v,n)∈nativeRows absent w owner action) :
    ∀ next,nativeRows absent v owner next=[] := by
  cases enabled : access w owner with
  | none => simp [nativeRows,enabled] at edge
  | some data =>
    rcases data with ⟨r,rom,key⟩
    rw [native_rows_from_access _ _ _ _ _ _ enabled action] at edge
    obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
    have world : v=advance absent w owner r rom key action e := (congrArg Prod.fst eq).symm
    rw [world]
    intro next
    simp [nativeRows,absent_access_after _ _ _ _ _ enabled]

theorem greatest_absent_c8_empty (owner : Nat) (V : History absent owner → Prop)
    (invariant : Invariant V) : ∀ h,¬V h := by
  intro h member
  obtain ⟨_,a,nonempty,all⟩ := invariant h member
  obtain ⟨edge,he⟩ := List.exists_mem_of_ne_nil _ nonempty
  have accepted := all edge.1 edge.2 he
  obtain ⟨_,next,enabled,_⟩ := invariant _ accepted
  change nativeRows absent edge.1 owner next≠[] at enabled
  rw [absent_successor_no_rows _ _ _ _ _ he next] at enabled
  contradiction

theorem absent_preserves_first_stored_step (w : World) (owner : Nat)
    (h : operationalCore w owner) :
    ∃ v n,(v,n)∈nativeRows absent w owner false ∧ ∀ next,nativeRows absent v owner next=[] := by
  obtain ⟨r,rom,key,enabled,_⟩ := h
  obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ (native_nonempty w owner r rom key enabled absent false)
  exact ⟨e.1,e.2,he,absent_successor_no_rows _ _ _ _ _ he⟩

end CSTTT.FullNative02.Operational
