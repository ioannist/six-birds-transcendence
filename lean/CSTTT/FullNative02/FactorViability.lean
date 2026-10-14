import CSTTT.FullNative02.OperationalViability
import CSTTT.FullNative02.HistoryLift

namespace CSTTT.FullNative02.Viability
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000

abbrev Factor := State × Bool
def funded (rom : ROM) (renew : Bool) (q : Factor) (action : Bool) : List (Factor × Nat) :=
  if q.2 then (rom.program.rows q.1 action).map fun e => ((e.1,renew),e.2) else []
def pre (rom : ROM) (renew : Bool) (V : Factor → Bool) (q : Factor) : Bool :=
  !q.1.outside && bits.any (fun action =>
    let rows := funded rom renew q action
    !rows.isEmpty && rows.all (fun e => V e.1))
def core : Factor → Bool := FullNative.Viability.core

theorem pre_top (rom : ROM) (renew : Bool) (q : Factor) : pre rom renew (fun _ => true) q=core q := by
  cases rom <;> rcases q with ⟨⟨p,u,v,r,c⟩,charge⟩ <;>
    cases p <;> cases u <;> cases v <;> cases r <;> cases c <;> cases charge <;> cases renew <;> decide +kernel
theorem renewable_pre_core (rom : ROM) (q : Factor) : pre rom true core q=core q := by
  cases rom <;> rcases q with ⟨⟨p,u,v,r,c⟩,charge⟩ <;>
    cases p <;> cases u <;> cases v <;> cases r <;> cases c <;> cases charge <;> decide +kernel
theorem absent_pre_core (rom : ROM) (q : Factor) : pre rom false core q=false := by
  cases rom <;> rcases q with ⟨⟨p,u,v,r,c⟩,charge⟩ <;>
    cases p <;> cases u <;> cases v <;> cases r <;> cases c <;> cases charge <;> decide +kernel
theorem sixteen_inside_charged_states : (FullNative.Viability.carrier.filter core).length=16 :=
  FullNative.Viability.actual_core_count

theorem full_actual_factor_projection (renew : Bool) (w : World) (owner : Nat) (r : Resident)
    (rom : ROM) (key : Token) (owned : binding w owner=some (r,rom,key)) (action : Bool) :
    (nativeRows (if renew then renewable else absent) w owner action).map (fun e => (quote e.1 owner,e.2))=
      (funded rom renew (r.current,w.accounts.charge key) action).map (fun e => (some e.1,e.2)) := by
  cases charge : w.accounts.charge key
  · have disabled : access w owner=none := by simp [access,owned,charge]
    simp [nativeRows,disabled,funded,charge]
  · have enabled : access w owner=some (r,rom,key) := by simp [access,owned,charge]
    rw [native_factor_projection renew w owner r rom key enabled action]
    simp only [funded,charge,if_true,List.map_map]
    rfl

def actualPre (renew : Bool) (V : Factor → Bool) (w : World) (owner : Nat) : Bool :=
  match binding w owner with
  | none => false
  | some (r,_,_) => !r.current.outside && bits.any (fun action =>
      let rows := nativeRows (if renew then renewable else absent) w owner action
      !rows.isEmpty && rows.all (fun e => (quote e.1 owner).any V))

theorem actual_predecessor_projection (renew : Bool) (V : Factor → Bool) (w : World) (owner : Nat)
    (r : Resident) (rom : ROM) (key : Token) (owned : binding w owner=some (r,rom,key)) :
    actualPre renew V w owner=pre rom renew V (r.current,w.accounts.charge key) := by
  simp only [actualPre,owned,pre]
  congr 1
  apply congrArg (fun f : Bool → Bool => bits.any f)
  funext action
  have projection := full_actual_factor_projection renew w owner r rom key owned action
  have nonempty := congrArg List.isEmpty projection
  have targets := congrArg (fun rows : List (Option Factor × Nat) => rows.all (fun e => e.1.any V)) projection
  simp only [List.isEmpty_map] at nonempty
  simp only [List.all_map,Function.comp_def,Option.any_some] at targets
  rw [nonempty,targets]

theorem pre_monotone (rom : ROM) (renew : Bool) (V W : Factor → Bool)
    (order : ∀ q,V q=true→W q=true) (q : Factor) (h : pre rom renew V q=true) : pre rom renew W q=true := by
  simp only [pre,Bool.and_eq_true,List.any_eq_true] at h ⊢
  obtain ⟨safe,action,member,nonempty,all⟩ := h
  exact ⟨safe,action,member,nonempty,List.all_eq_true.mpr (fun e he => order e.1 (List.all_eq_true.mp all e he))⟩

theorem cold_original_c8_not_package_filtered :
    operationalCore (initial 8) 0 ∧ Epoch.accept (initial 8) 0=false := by
  have read : access (initial 8) 0=some
      (⟨0,some .canonical32,⟨false,false,false,false,false⟩,.birth 0,.birth 0,0,[],[]⟩,.canonical32,0) := by decide +kernel
  exact ⟨⟨_,_,_,read,rfl⟩,by decide +kernel⟩

theorem greatest_core_projection_realized (q : Factor) :
    (∃ w,History renewable 8 .canonical32 w ∧ operationalCore w 0 ∧ quote w 0=some q) ↔ core q=true := by
  constructor
  · rintro ⟨w,_,member,quoted⟩
    obtain ⟨r,rom,key,enabled,inside⟩ := member
    have same : q=(r.current,true) := Option.some.inj
      (quoted.symm.trans (FactorLift.quote_enabled _ _ _ _ _ enabled))
    rw [same]
    simp [core,FullNative.Viability.core,inside]
  · intro h
    have parts : q.1.outside=false ∧ q.2=true := by simpa [core,FullNative.Viability.core] using h
    have enabled : access (initial 8) 0=some
        (⟨0,some .canonical32,⟨false,false,false,false,false⟩,.birth 0,.birth 0,0,[],[]⟩,.canonical32,0) := by decide +kernel
    obtain ⟨w,next,path,live,state⟩ := owned_reaches_every_inside 0 (initial 8) _ 0 enabled q.1 parts.1
    refine ⟨w,retained_actual_history 0 _ _ (.initial (by decide)) path,
      ⟨next,.canonical32,0,live,by rw [state]; exact parts.1⟩,?_⟩
    rw [FactorLift.quote_enabled _ _ _ _ _ live,state]
    exact congrArg some (Prod.ext rfl parts.2.symm)

end CSTTT.FullNative02.Viability
