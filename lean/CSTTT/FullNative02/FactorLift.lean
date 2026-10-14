import CSTTT.FullNative02.WholePackage
import CSTTT.Autonomy.System

namespace CSTTT.FullNative02.FactorLift
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000

abbrev Factor := State × Bool
def lift (owner : Nat) (start : World) (q : Factor) (w : World) : Prop :=
  Retained owner start w ∧ quote w owner=some q
def packageValid (owner : Nat) (start : World) (q : Factor) : Prop :=
  ∀ w,lift owner start q w→Package.Whole w owner
def step (q : Factor) (_ : Unit) (action : Bool) (next : Factor) : Prop :=
  ∃ n,(next,n)∈Viability.fundedRows true q action

theorem quote_enabled (w : World) (owner : Nat) (r : Resident) (rom : ROM) (key : Token)
    (enabled : access w owner=some (r,rom,key)) : quote w owner=some (r.current,true) := by
  simp [quote,(access_facts _ _ _ _ _ enabled).1,(access_facts _ _ _ _ _ enabled).2]

theorem all_descendant_lifts_whole_package (owner : Nat) (start : World)
    (accepted : Package.Accept02 start owner=true) : ∀ q,packageValid owner start q := by
  intro q w lifted
  exact Package.every_retained_history_whole_package owner start w accepted lifted.1

theorem nonempty_every_inside_lift (owner : Nat) (start : World)
    (accepted : Package.Accept02 start owner=true) (q : Factor) (core : Viability.core q=true) :
    ∃ w,lift owner start q w := by
  obtain ⟨r,key,enabled,_,_,_⟩ := Epoch.accepted_access start owner accepted
  have inside : q.1.outside=false ∧ q.2=true := by simpa [Viability.core] using core
  obtain ⟨w,next,history,live,state⟩ := owned_reaches_every_inside owner start r key enabled q.1 inside.1
  refine ⟨w,history,?_⟩
  rw [quote_enabled _ _ _ _ _ live,state]
  exact congrArg some (Prod.ext rfl inside.2.symm)

theorem every_actual_response_covered (owner : Nat) (start w v : World)
    (accepted : Package.Accept02 start owner=true) (q : Factor) (lifted : lift owner start q w)
    (n : Nat) (edge : (v,n)∈nativeRows renewable w owner false) :
    ∃ next,lift owner start next v ∧ (next,n)∈Viability.fundedRows true q false := by
  obtain ⟨r,key,enabled,_,_,_⟩ := Epoch.accepted_access w owner
    (retained_acceptance _ _ _ accepted lifted.1)
  have actual := quote_enabled _ _ _ _ _ enabled
  have same : q=(r.current,true) := Option.some.inj (lifted.2.symm.trans actual)
  rw [same]
  rw [native_rows_from_access _ _ _ _ _ _ enabled false] at edge
  obtain ⟨e,support,eq⟩ := List.mem_map.mp edge
  have world : v=advance renewable w owner r .canonical32 key false e := (congrArg Prod.fst eq).symm
  have weight : n=e.2 := (congrArg Prod.snd eq).symm
  have live := renewable_access_after w owner r .canonical32 key enabled false e
  refine ⟨(e.1,true),⟨?_,?_⟩,?_⟩
  · apply Retained.next lifted.1 v n
    rw [native_rows_from_access _ _ _ _ _ _ enabled false]
    exact List.mem_map.mpr ⟨e,support,eq⟩
  · rw [world,quote_enabled _ _ _ _ _ live]
  · rw [weight]
    exact List.mem_map.mpr ⟨e,support,rfl⟩

/-- EVERY factor response is realized at EVERY actual descendant lift, with
the same weight, rather than only at one selected representative history. -/
theorem every_factor_response_realized (owner : Nat) (start w : World)
    (accepted : Package.Accept02 start owner=true) (q : Factor) (lifted : lift owner start q w)
    (next : Factor) (n : Nat) (edge : (next,n)∈Viability.fundedRows true q false) :
    ∃ v,(v,n)∈nativeRows renewable w owner false ∧ lift owner start next v := by
  obtain ⟨r,key,enabled,_,_,_⟩ := Epoch.accepted_access w owner
    (retained_acceptance _ _ _ accepted lifted.1)
  have actual := quote_enabled _ _ _ _ _ enabled
  have same : q=(r.current,true) := Option.some.inj (lifted.2.symm.trans actual)
  rw [same] at edge
  change (next,n)∈(model.rows r.current false).map (fun e => ((e.1,true),e.2)) at edge
  obtain ⟨e,support,equal⟩ := List.mem_map.mp edge
  have qeq : next=(e.1,true) := (congrArg Prod.fst equal).symm
  have neq : n=e.2 := (congrArg Prod.snd equal).symm
  let v := advance renewable w owner r .canonical32 key false e
  have actualEdge : (v,n)∈nativeRows renewable w owner false := by
    rw [neq,native_rows_from_access _ _ _ _ _ _ enabled false]
    exact List.mem_map.mpr ⟨e,support,rfl⟩
  refine ⟨v,actualEdge,.next lifted.1 v n actualEdge,?_⟩
  rw [qeq,quote_enabled _ _ _ _ _ (renewable_access_after _ _ _ _ _ enabled false e)]

theorem factor_inside_response (q : Factor) (inside : Viability.core q=true) :
    ∃ next,step q () false next ∧ Viability.core next=true := by
  have parts : q.1.outside=false ∧ q.2=true := by simpa [Viability.core] using inside
  let target : State := ⟨false,false,false,false,!q.1.phase⟩
  let n := weight q.1 false false
  have supported : (target,n)∈model.rows q.1 false := Viability.maintenance_support _ _ rfl rfl
  refine ⟨(target,true),⟨n,?_⟩,rfl⟩
  simp only [Viability.fundedRows,parts.2,if_true]
  exact List.mem_map.mpr ⟨(target,n),supported,rfl⟩

def system (owner : Nat) (start : World) : ControlledSystem :=
  { carrier := ⟨⟨owner⟩,Factor,⟨Viability.carrier,Viability.carrier_mem⟩⟩
    Disturbance := Unit
    Action := Bool
    disturbanceEnum := ⟨[()],fun u => by cases u; simp⟩
    actionEnum := ⟨bits,fun b => by cases b <;> simp [bits]⟩
    step := step
    packageValid := packageValid owner start
    actionOwner := fun _ => ⟨owner⟩
    maintenanceResources := fun _ => ((keys start.accounts owner).map fun key => ⟨key.val⟩) ++
      [⟨4⟩,⟨5⟩,⟨6⟩,⟨7⟩] }

def invariantCertificate (owner : Nat) (start : World)
    (accepted : Package.Accept02 start owner=true) (endpoint : Factor)
    (inside : Viability.core endpoint=true) : ControlledInvariantCertificate (system owner start) endpoint :=
  {inside := fun q => Viability.core q=true
   endpointInside := inside
   packageInside := fun q _ => all_descendant_lifts_whole_package owner start accepted q
   targetOwnedResponse := fun q _ h => by
     obtain ⟨next,response,retained⟩ := factor_inside_response q h
     exact ⟨false,next,rfl,response,retained⟩}

end CSTTT.FullNative02.FactorLift
