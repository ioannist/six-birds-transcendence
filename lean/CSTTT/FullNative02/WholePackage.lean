import CSTTT.FullNative02.FullFuture
import CSTTT.FullNative02.Clock
import CSTTT.FullNative02.UniversalViability

namespace CSTTT.FullNative02.Package
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000

def C1 (w : World) (owner : Nat) (r : Resident) : Prop :=
  matrix w owner=Objecthood.P r.current ∧ PhysicalC1 r.current

def C2 (w : World) (owner : Nat) (r : Resident) (key : Token) : Prop :=
  (∀ right,(split w owner r key right,weight r.current false right)∈nativeRows renewable w owner false) ∧
  current (split w owner r key false) owner=current (split w owner r key true) owner ∧
  (Temporal.actual (split w owner r key false) owner).map (fun r => r.context)=
    (Temporal.actual (split w owner r key true) owner).map (fun r => r.context) ∧
  (Temporal.actual (split w owner r key false) owner).map (fun r => classes model r.current)≠
    (Temporal.actual (split w owner r key true) owner).map (fun r => classes model r.current)

def C3 (w : World) (owner : Nat) (r : Resident) (key : Token) : Prop :=
  (TargetTheory.GenericHandoff.ProfileRules.count (profile model)
    (TargetTheory.GenericHandoff.ProfileRules.seed (profile model))=9 ∧
   TargetTheory.GenericHandoff.ProfileRules.count (profile model) (classes model)=16 ∧
   TargetTheory.GenericHandoff.ProfileRules.count (profile model)
    (TargetTheory.GenericHandoff.ProfileRules.second (profile model))=16) ∧
  (∀ n,TargetTheory.GenericHandoff.ProfileRules.iterate (profile model) (1+n)=classFormula) ∧
  ∀ v other s k,access v other=some (s,.canonical32,k)→
    ((∀ word trace,WeightedFuture.law (fun w a => normalizedNative renewable w owner a)
      (fun w => (Temporal.actual w owner).map Temporal.observe) w word trace=
      WeightedFuture.law (fun w a => normalizedNative renewable w other a)
      (fun w => (Temporal.actual w other).map Temporal.observe) v word trace) ↔
     Temporal.code (Temporal.frame w r key)=Temporal.code (Temporal.frame v s k))

def C4 (w : World) (owner : Nat) (r : Resident) (key : Token) : Prop :=
  r.current.outside=false ∧ current w owner=some (0,16,16) ∧
  (∀ v other s k,access v other=some (s,.canonical32,k)→s.current.outside=false→
    current w owner=current v other) ∧
  ¬∃ decode : Option (Nat × Nat × Nat) → Option Nat,
    ∀ right,(Temporal.actual (split w owner r key right) owner).map
      (fun r => classes model r.current)=decode (current (split w owner r key right) owner)

def C5 (w : World) (owner : Nat) (r : Resident) (key : Token) : Prop :=
  Blocks.evidence .canonical32 owner r.receipts=true ∧
  (∃ first rest,(first::rest)∈Blocks.blocks r.receipts ∧
    Blocks.qualifies .canonical32 owner (first::rest)=true ∧
    ∀ measure : State → Rat,measure first.before≠0→
      ¬(∀ receipt∈first::rest,measure receipt.before*Blocks.edge .canonical32 receipt.before receipt.after=
        measure receipt.after*Blocks.edge .canonical32 receipt.after receipt.before)) ∧
  (∀ target : State,target.outside=false→∃ v next,Retained owner w v ∧
    access v owner=some (next,.canonical32,key) ∧ next.current=target)

def ClockAudit (w : World) (owner : Nat) (r : Resident) (key : Token) : Prop :=
  (∀ word,∃ v,Walk owner w word v) ∧
  ∀ word v,Walk owner w word v→∃ next,access v owner=some (next,.canonical32,key) ∧
    next.receipts.length=r.receipts.length+word.length ∧
    v.accounts.cursor key=w.accounts.cursor key+word.length ∧
    next.current.phase=tickAfter word r.current.phase ∧ next.birth=r.birth ∧
    next.birthCursor=r.birthCursor ∧ next.roots=r.roots ∧ next.installed=r.installed ∧ next.owner=r.owner

def C6 (w : World) (owner : Nat) (r : Resident) (key : Token) : Prop :=
  Epoch.valid w owner r .canonical32 key=true ∧ ClockAudit w owner r key ∧
  (∀ v,Retained owner w v→Epoch.accept v owner=true) ∧
  ∀ v n,(v,n)∈nativeRows renewable w owner false→
    ∃ next,v.residents owner=some next ∧ next.receipts.length=r.receipts.length+1 ∧
      next.current.phase= !r.current.phase ∧ v.accounts.cursor key=w.accounts.cursor key+1 ∧
      v.accounts.charge key=true ∧ next.birth=r.birth ∧ next.roots=r.roots ∧
      next.installed=r.installed ∧ v.accounts.custody key=.local owner ∧ 0<n

def C7 (w : World) (owner : Nat) (r : Resident) (key : Token) : Prop :=
  (∀ v other s k,access v other=some (s,.canonical32,k)→∀ right word out,
    emitted w owner (Binding.branch right) word out=emitted v other (Binding.branch right) word out) ∧
  (emitted (split w owner r key false) owner Binding.joint [false] [0]=1/8 ∧
    emitted (split w owner r key true) owner Binding.joint [false] [0]=3/8) ∧
  ∀ v other s k,access v other=some (s,.canonical32,k)→
    Temporal.code (Temporal.frame w r key)=Temporal.code (Temporal.frame v s k)→∀ word out,
      emitted w owner Binding.joint word out=emitted v other Binding.joint word out

def C8 (w : World) (owner : Nat) : Prop :=
  operationalCore w owner ∧ UniversalViability.UniversalC8 owner ∧
  @Operational.Invariant renewable owner Operational.core ∧
  (∀ V : Operational.History renewable owner → Prop,Operational.Invariant V→
    ∀ h,V h→Operational.core h) ∧
  (∀ V : Operational.History absent owner → Prop,Operational.Invariant V→∀ h,¬V h) ∧
  (∀ v,operationalCore v owner→∃ next n,(next,n)∈nativeRows absent v owner false ∧
    ∀ a,nativeRows absent next owner a=[])

/-- Eight theorem projections of one actual access readout; no clause is a raw
constructor input. The independently computed admission predicate is Epoch.accept. -/
structure Certificate (w : World) (owner : Nat) (r : Resident) (key : Token) : Prop where
  c1 : C1 w owner r
  c2 : C2 w owner r key
  c3 : C3 w owner r key
  c4 : C4 w owner r key
  c5 : C5 w owner r key
  c6 : C6 w owner r key
  c7 : C7 w owner r key
  c8 : C8 w owner

def Whole (w : World) (owner : Nat) : Prop :=
  ∃ r key,access w owner=some (r,.canonical32,key) ∧ Certificate w owner r key
abbrev Accept02 := Epoch.accept

theorem whole_package_from_installed_execution (w : World) (owner : Nat)
    (accepted : Accept02 w owner=true) : Whole w owner := by
  obtain ⟨r,key,enabled,inside,audited,evidence⟩ := Epoch.accepted_access w owner accepted
  refine ⟨r,key,enabled,⟨?_,?_,?_,?_,?_,?_,?_,?_⟩⟩
  · exact ⟨matrix_from_installed _ _ _ _ enabled,physical_c1 r.current⟩
  · exact ⟨split_actual _ _ _ _ enabled,split_readouts _ _ _ _ enabled⟩
  · exact ⟨profile_trajectory,stable_profile_forever,
      fun v other s k h => Temporal.actual_full_future_exact _ _ _ _ _ _ _ _ enabled h⟩
  · refine ⟨inside,?_,fun v other s k h hi => current_non_exposure _ _ _ _ _ _ _ _ enabled h inside hi,?_⟩
    · rw [current_from_installed _ _ _ _ enabled,Binding.inside_public _ inside]
    · rintro ⟨decode,law⟩
      have eq := (law false).trans ((congrArg decode (split_readouts _ _ _ _ enabled).1).trans (law true).symm)
      exact (split_readouts _ _ _ _ enabled).2.2 eq
  · refine ⟨evidence,?_,owned_reaches_every_inside owner w r key enabled⟩
    obtain ⟨block,member,qualified⟩ := List.any_eq_true.mp evidence
    cases block with
    | nil => simp [Blocks.qualifies] at qualified
    | cons first rest =>
      exact ⟨first,rest,member,qualified,
        fun measure positive => Blocks.qualifying_block_no_local_balance _ _ _ _ qualified measure positive⟩
  · exact ⟨audited,⟨every_word_continues owner w r .canonical32 key enabled,
      fun word v path => all_word_registers owner w v r .canonical32 key enabled word path⟩,
      fun v path => retained_acceptance owner w v accepted path,
      actual_response_progress w owner r .canonical32 key enabled⟩
  · exact ⟨fun v other s k h => actual_branch_all_words _ _ _ _ _ _ _ _ enabled h,
      actual_split_joint_gap _ _ _ _ enabled,
      fun v other s k h => actual_joint_coherence _ _ _ _ _ _ _ _ enabled h⟩
  · exact ⟨⟨r,.canonical32,key,enabled,inside⟩,UniversalViability.universal_c8 owner,
      (Operational.greatest_operational_c8 owner).1,
      (Operational.greatest_operational_c8 owner).2,Operational.greatest_absent_c8_empty owner,
      fun v h => Operational.absent_preserves_first_stored_step v owner h⟩

theorem every_retained_history_whole_package (owner : Nat) (start w : World)
    (accepted : Accept02 start owner=true) (history : Retained owner start w) : Whole w owner :=
  whole_package_from_installed_execution w owner (retained_acceptance _ _ _ accepted history)

theorem no_independent_clause_input (w : World) (owner : Nat) (r s : Resident) (key k : Token)
    (hr : access w owner=some (r,.canonical32,key))
    (hs : access w owner=some (s,.canonical32,k)) : r=s ∧ key=k := by
  have same := Option.some.inj (hr.symm.trans hs)
  exact ⟨congrArg Prod.fst same,congrArg (fun data => data.2.2) same⟩

end CSTTT.FullNative02.Package
