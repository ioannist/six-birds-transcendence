import CSTTT.FullNative02.ProcessBridge
import CSTTT.FullNative02.UniversalPackageAutonomy

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 32000000
set_option maxRecDepth 8192
set_option synthInstance.maxSize 4096

theorem absent_actual_response_rejects_package (w v : World) (owner : Nat) (action : Bool)
    (n : Nat) (edge : (v,n)∈nativeRows absent w owner action) :
    Epoch.accept v owner=false ∧ ∀ next,nativeRows absent v owner next=[] := by
  refine ⟨?_,Operational.absent_successor_no_rows _ _ _ _ _ edge⟩
  cases enabled : access w owner with
  | none => simp [nativeRows,enabled] at edge
  | some data =>
    rcases data with ⟨r,rom,key⟩
    rw [native_rows_from_access _ _ _ _ _ _ enabled action] at edge
    obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
    have world : v=advance absent w owner r rom key action e := (congrArg Prod.fst eq).symm
    rw [world]
    simp [Epoch.accept,absent_access_after _ _ _ _ _ enabled]

theorem probe_outside (rom : ROM) (s : State) :
    ∀ e∈rom.program.rows s true,e.1.outside=true := by
  cases rom <;> rcases s with ⟨p,u,v,r,c⟩ <;>
    cases p <;> cases u <;> cases v <;> cases r <;> cases c <;> decide +kernel

theorem actual_probe_rejects_package (w v : World) (owner : Nat) (n : Nat)
    (edge : (v,n)∈nativeRows renewable w owner true) : Epoch.accept v owner=false := by
  cases enabled : access w owner with
  | none => simp [nativeRows,enabled] at edge
  | some data =>
    rcases data with ⟨r,rom,key⟩
    rw [native_rows_from_access _ _ _ _ _ _ enabled true] at edge
    obtain ⟨e,supported,eq⟩ := List.mem_map.mp edge
    have world : v=advance renewable w owner r rom key true e := (congrArg Prod.fst eq).symm
    rw [world]
    simp only [Epoch.accept,renewable_access_after _ _ _ _ _ enabled true e]
    simp [(probe_outside rom r.current e supported)]

theorem fusion_and_new_epochs_do_not_inherit_package :
    ∀ e∈fusionRows renewable branchesWorld mainRequest,
      Epoch.accept e.1.world 1=false ∧ Epoch.accept e.1.world 2=false ∧ Epoch.accept e.1.world 3=false ∧
      ∀ ready∈(outputWarmup e.1.world).toList,∀ rows∈(strongerFork ready).toList,
        ∀ out∈rows,Epoch.accept out.1.world 6=false := by decide +kernel

def twinSourceComponent : Node → Bool
  | .birth n => decide (n=0)
  | .event n => decide (1≤n ∧ n≤6)
  | .version n => decide (1≤n ∧ n≤6)
  | _ => false

theorem twin_current_version_not_source_derived : ¬ancestry twinWorld (.birth 0) (.version 13) := by
  have closed : ∀ e∈ledgerEdges twinWorld,
      twinSourceComponent e.1=true→twinSourceComponent e.2=true := by decide +kernel
  have preserved (x y : Node) (path : ancestry twinWorld x y) :
      twinSourceComponent x=true→twinSourceComponent y=true := by
    induction path with
    | one edge => exact closed _ edge
    | extend past edge ih => exact fun h => closed _ edge (ih h)
  intro path
  have impossible := preserved _ _ path rfl
  contradiction

theorem disconnected_twin_accepts_but_has_no_source_ancestry :
    Epoch.accept twinWorld 1=true ∧ ¬SourceOwned twinWorld 1 := by
  refine ⟨by decide +kernel,?_⟩
  rintro ⟨r,key,enabled,path⟩
  have readout : (access twinWorld 1).map (fun data => data.1.version)=some (.version 13) := by decide +kernel
  have version : r.version=.version 13 := by simpa only [enabled,Option.map_some,Option.some.injEq] using readout
  rw [version] at path
  exact twin_current_version_not_source_derived path

end CSTTT.FullNative02
