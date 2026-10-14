import CSTTT.FullNative02.Withdrawal

namespace CSTTT.FullNative02.Autonomy
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000

def policy (_ : Unit) : Bool := false
def stock (w : World) (key : Token) : Nat := if w.accounts.charge key then 1 else 0

def Progress (owner : Nat) (start : World) : Prop :=
  ∀ w,Retained owner start w→∀ r key,access w owner=some (r,.canonical32,key)→
    ∀ v n,(v,n)∈nativeRows renewable w owner false→∃ next,v.residents owner=some next ∧
      next.receipts.length=r.receipts.length+1 ∧ next.current.phase= !r.current.phase ∧
      v.accounts.cursor key=w.accounts.cursor key+1

def Solvent (owner : Nat) (start : World) : Prop :=
  ∀ w,Retained owner start w→∀ r key,access w owner=some (r,.canonical32,key)→
    ∀ v n,(v,n)∈nativeRows renewable w owner false→
      stock w key=1 ∧ stock v key=stock w key-1+1 ∧
      (v.residents owner).bind (fun r => r.receipts.getLast?.map Receipt.packet)=some (some ())

def OwnedMaintenance (owner : Nat) (start : World) : Prop :=
  ∀ w,Retained owner start w→∀ r key,access w owner=some (r,.canonical32,key)→
    r.installed=some .canonical32 ∧ w.accounts.custody key=.local owner ∧
      ∀ action edge,(makeReceipt renewable w owner r .canonical32 key action edge).issuer=.local owner

def OwnedFuture (owner : Nat) (start : World) : Prop :=
  ∀ w,Retained owner start w→∀ r key,access w owner=some (r,.canonical32,key)→∀ word trace,
    WeightedFuture.law (fun w a => normalizedNative renewable w owner a)
      (fun w => (Temporal.actual w owner).map Temporal.observe) w word trace=
    WeightedFuture.law Temporal.rows (fun r => some (Temporal.observe r))
      (Temporal.frame w r key) word trace

theorem independent_full_history_progress (owner : Nat) (start : World) : Progress owner start := by
  intro w _ r key enabled v n edge
  obtain ⟨next,present,length,phase,cursor,_⟩ := actual_response_progress w owner r .canonical32 key enabled v n edge
  exact ⟨next,present,length,phase,cursor⟩

theorem independent_full_history_solvency (owner : Nat) (start : World) : Solvent owner start := by
  intro w _ r key enabled v n edge
  rw [native_rows_from_access _ _ _ _ _ _ enabled false] at edge
  obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
  have world : v=advance renewable w owner r .canonical32 key false e := (congrArg Prod.fst eq).symm
  rw [world]
  simp [stock,(access_facts _ _ _ _ _ enabled).2,advance,put,paid_charge,
    makeReceipt,renewable,AccountExecution.renewable,List.getLast?_append]

theorem independent_full_history_ownership (owner : Nat) (start : World) : OwnedMaintenance owner start := by
  intro w _ r key enabled
  have facts := binding_facts _ _ _ _ _ (access_facts _ _ _ _ _ enabled).1
  exact ⟨facts.2.1,actual_issuer renewable w owner r .canonical32 key enabled false (r.current,1),
    actual_issuer renewable w owner r .canonical32 key enabled⟩

theorem independent_full_history_future (owner : Nat) (start : World) : OwnedFuture owner start := by
  intro w _ r key enabled
  exact Temporal.actual_all_words w owner r key enabled

/-- Codes 0..3 name the actual token identities. 4..7 name installed code,
local audit, archived birth residue and retained environmental ports. 8..13
name source, bridge, acquisition controller, decoder, scheduler and repair.
These are names in the original finite-certificate interface, not raw resources
or extra energy/custody primitives. -/
def withdrawal (owner : Nat) (start : World) : WithdrawalSpec :=
  { removedResources := [⟨8⟩,⟨9⟩,⟨10⟩,⟨11⟩,⟨12⟩,⟨13⟩]
    retainedResources := (FactorLift.system owner start).maintenanceResources (⟨false,false,false,false,false⟩,true)
    disjoint := by
      intro resource removed retained
      have lower : 8≤resource.code := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at removed
        rcases removed with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      change resource∈((keys start.accounts owner).map fun key => ResourceId.mk key.val)++
        [⟨4⟩,⟨5⟩,⟨6⟩,⟨7⟩] at retained
      rcases List.mem_append.mp retained with token | ownedPart
      · obtain ⟨key,_,eq⟩ := List.mem_map.mp token
        have code := congrArg ResourceId.code eq
        have bound := key.isLt
        simp only at code
        omega
      · simp only [List.mem_cons,List.not_mem_nil,or_false] at ownedPart
        rcases ownedPart with rfl | rfl | rfl | rfl <;> simp at lower
    sourceRemoved := start.residents 0=none ∧ ∀ key,start.accounts.custody key≠.local 0
    bridgeRemoved := (∀ a,start.slots a=none) ∧ ∀ key,start.accounts.custody key≠.external
    migrationControllerRemoved := start.acquisition=false
    externalDecoderRemoved := OwnedFuture owner start
    externalSchedulerRemoved := (∀ d : Unit,policy d=false) ∧ OwnedFuture owner start
    undeclaredRepairRemoved := Solvent owner start }

theorem withdrawal_sound (owner : Nat) (start : World) (removed : Withdrawn start) :
    (withdrawal owner start).sourceRemoved ∧ (withdrawal owner start).bridgeRemoved ∧
    (withdrawal owner start).migrationControllerRemoved ∧ (withdrawal owner start).externalDecoderRemoved ∧
    (withdrawal owner start).externalSchedulerRemoved ∧ (withdrawal owner start).undeclaredRepairRemoved :=
  ⟨⟨removed.1,fun key => (removed.2.2.2 key).2⟩,
    ⟨removed.2.2.1,fun key => (removed.2.2.2 key).1⟩,removed.2.1,
    independent_full_history_future owner start,⟨fun _ => rfl,independent_full_history_future owner start⟩,
    independent_full_history_solvency owner start⟩

def certificate (owner : Nat) (start : World) (accepted : Package.Accept02 start owner=true)
    (endpoint : FactorLift.Factor) (inside : Viability.core endpoint=true) :
    AutonomyCertificate (FactorLift.system owner start) endpoint :=
  {withdrawal := withdrawal owner start
   invariant := FactorLift.invariantCertificate owner start accepted endpoint inside
   antiStall := Progress owner start
   budgetSolventOnInvariant := Solvent owner start
   targetOwnsMaintenance := OwnedMaintenance owner start}

def Realized (owner : Nat) (start : World) : Prop :=
  Withdrawn start ∧ ∃ endpoint,quote start owner=some endpoint ∧ Viability.core endpoint=true ∧
    ∃ cert : AutonomyCertificate (FactorLift.system owner start) endpoint,
      cert.antiStall ∧ cert.budgetSolventOnInvariant ∧ cert.targetOwnsMaintenance ∧
      cert.withdrawal.sourceRemoved ∧ cert.withdrawal.bridgeRemoved ∧ cert.withdrawal.migrationControllerRemoved ∧
      cert.withdrawal.externalDecoderRemoved ∧ cert.withdrawal.externalSchedulerRemoved ∧ cert.withdrawal.undeclaredRepairRemoved ∧
      (∀ q,Viability.core q=true→∃ w,FactorLift.lift owner start q w) ∧
      (∀ q w,FactorLift.lift owner start q w→Package.Whole w owner) ∧
      (∀ q w next n,FactorLift.lift owner start q w→(next,n)∈Viability.fundedRows true q false→
        ∃ v,(v,n)∈nativeRows renewable w owner false ∧ FactorLift.lift owner start next v) ∧
      (∀ q w v n,FactorLift.lift owner start q w→(v,n)∈nativeRows renewable w owner false→
        ∃ next,FactorLift.lift owner start next v ∧ (next,n)∈Viability.fundedRows true q false)

theorem actual_package_preserving_target_autonomy (owner : Nat) (start : World)
    (accepted : Package.Accept02 start owner=true) (removed : Withdrawn start) : Realized owner start := by
  obtain ⟨r,key,enabled,inside,_,_⟩ := Epoch.accepted_access start owner accepted
  have core : Viability.core (r.current,true)=true := by simp [Viability.core,inside]
  refine ⟨removed,(r.current,true),FactorLift.quote_enabled _ _ _ _ _ enabled,core,
    certificate owner start accepted _ core,independent_full_history_progress owner start,
    independent_full_history_solvency owner start,independent_full_history_ownership owner start,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (withdrawal_sound owner start removed).1
  · exact (withdrawal_sound owner start removed).2.1
  · exact (withdrawal_sound owner start removed).2.2.1
  · exact (withdrawal_sound owner start removed).2.2.2.1
  · exact (withdrawal_sound owner start removed).2.2.2.2.1
  · exact (withdrawal_sound owner start removed).2.2.2.2.2
  · exact FactorLift.nonempty_every_inside_lift owner start accepted
  · exact fun q w lifted => FactorLift.all_descendant_lifts_whole_package owner start accepted q w lifted
  · exact fun q w next n lifted edge => FactorLift.every_factor_response_realized owner start w accepted q lifted next n edge
  · exact fun q w v n lifted edge => FactorLift.every_actual_response_covered owner start w v accepted q lifted n edge

end CSTTT.FullNative02.Autonomy
