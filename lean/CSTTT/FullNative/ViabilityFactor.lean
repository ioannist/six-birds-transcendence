import CSTTT.FullNative.DriveClock

/-! The charge factor is a readout of installed/owned native executions. The
history carrier below retains the entire supported path, in addition to every
receipt and account register in its executions. Its invariant predicates are
arbitrary propositions; no descent through the finite readout is assumed. -/
namespace CSTTT.FullNative.Viability
open AccountExecution PhysicalExecution
set_option autoImplicit false
set_option maxHeartbeats 8000000
abbrev VState := State × Bool

def environment (renew : Bool) : Supply := if renew then renewable else absentSupply

def quote (x : Execution) : VState := (x.resident.current,x.accounts.charge x.resident.token)

def Owned (x : Execution) : Prop := x.resident.installed=some model ∧
  x.accounts.allocation x.resident.token=some (.localGenerator x.resident.owner)

def fundedRows (renew : Bool) (q : VState) (a : Bool) : List (VState × Nat) :=
  if q.2 then (rows q.1 a).map fun e => ((e.1,renew),e.2) else []

def carrier : List VState := states.flatMap fun s => bits.map fun c => (s,c)

theorem carrier_exact : carrier.Nodup ∧ carrier.length=64 := by decide +kernel

theorem carrier_mem (q : VState) : q ∈ carrier := by
  apply List.mem_flatMap.mpr
  refine ⟨q.1,state_mem q.1,List.mem_map.mpr ⟨q.2,?_,rfl⟩⟩
  cases q.2 <;> simp [bits]

def pre (renew : Bool) (V : VState → Bool) (q : VState) : Bool :=
  !q.1.outside && bits.any (fun a =>
    let rs := fundedRows renew q a
    !rs.isEmpty && rs.all (fun e => V e.1))

def core (q : VState) : Bool := !q.1.outside && q.2

theorem pre_top (renew : Bool) (q : VState) : pre renew (fun _ => true) q=core q := by
  rcases q with ⟨s,c⟩
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases c <;> cases renew <;> decide +kernel

theorem renewable_pre_core (q : VState) : pre true core q=core q := by
  rcases q with ⟨s,c⟩
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases c <;> decide +kernel

theorem absent_pre_core (q : VState) : pre false core q=false := by
  rcases q with ⟨s,c⟩
  cases s with
  | mk p u v r phase =>
    cases p <;> cases u <;> cases v <;> cases r <;> cases phase <;> cases c <;> decide +kernel

theorem owned_projection (renew : Bool) (x : Execution) (h : Owned x) (a : Bool) :
    (rawRows (environment renew) x a).map (fun e => (quote e.1,e.2))=fundedRows renew (quote x) a := by
  cases hc : x.accounts.charge x.resident.token <;> cases renew <;>
    simp [model,rawRows,environment,renewable,absentSupply,enabled,h.1,h.2,hc,quote,
      fundedRows,List.map_map,advance,transact,debit,put,Function.comp_def]

theorem pre_mono (renew : Bool) (V W : VState → Bool)
    (order : ∀ q, V q=true → W q=true) (q : VState) (h : pre renew V q=true) : pre renew W q=true := by
  simp only [pre,Bool.and_eq_true,List.any_eq_true] at h ⊢
  rcases h with ⟨safe,a,member,nonempty,all⟩
  refine ⟨safe,a,member,nonempty,?_⟩
  exact List.all_eq_true.mpr (fun e he => order e.1 (List.all_eq_true.mp all e he))

def Controlled (renew : Bool) (V : VState → Bool) : Prop :=
  ∀ q, V q=true → pre renew V q=true

theorem controlled_subset_core (renew : Bool) (V : VState → Bool) (h : Controlled renew V)
    (q : VState) (member : V q=true) : core q=true := by
  have retained:=pre_mono renew V (fun _ => true) (fun _ _ => rfl) q (h q member)
  simpa only [pre_top] using retained

theorem core_greatest : Controlled true core ∧
    ∀ V, Controlled true V → ∀ q, V q=true → core q=true := by
  exact ⟨fun q member => (renewable_pre_core q).trans member,
    fun V h q member => controlled_subset_core true V h q member⟩

theorem underfund_greatest_empty (V : VState → Bool) (h : Controlled false V) :
    ∀ q, V q=false := by
  intro q
  cases member : V q
  · rfl
  · have retained:=pre_mono false V core (controlled_subset_core false V h) q (h q member)
    rw [absent_pre_core] at retained
    contradiction

theorem actual_core_count : (carrier.filter core).length=16 := by decide +kernel

def actualPre (renew : Bool) (V : VState → Bool) (x : Execution) : Bool :=
  !x.resident.current.outside && bits.any (fun a =>
    let rs := rawRows (environment renew) x a
    !rs.isEmpty && rs.all (fun e => V (quote e.1)))

theorem actual_pre_projection (renew : Bool) (V : VState → Bool) (x : Execution) (h : Owned x) :
    actualPre renew V x=pre renew V (quote x) := by
  unfold actualPre pre
  change (!x.resident.current.outside && _) = (!x.resident.current.outside && _)
  congr 1
  apply congrArg (fun f : Bool → Bool => bits.any f)
  funext a
  rw [←owned_projection renew x h a]
  simp only [List.isEmpty_map,List.all_map]
  rfl

theorem source_owned_viable : Owned source ∧ core (quote source)=true := by
  exact ⟨⟨rfl,rfl⟩,rfl⟩

theorem credited_targets_owned_viable :
    Owned ⟨Credit.creditedBothWorld.accounts,Credit.creditedFirstLocal⟩ ∧
    Owned ⟨Credit.creditedBothWorld.accounts,Credit.creditedSecondLocal⟩ ∧
    core (quote ⟨Credit.creditedBothWorld.accounts,Credit.creditedFirstLocal⟩)=true ∧
    core (quote ⟨Credit.creditedBothWorld.accounts,Credit.creditedSecondLocal⟩)=true := by
  exact ⟨⟨rfl,rfl⟩,⟨rfl,rfl⟩,rfl,rfl⟩

theorem missing_program_pre (renew : Bool) (V : VState → Bool) (x : Execution)
    (missing : x.resident.installed=none) : actualPre renew V x=false := by
  simp [actualPre,rawRows,missing,bits]

theorem missing_account_pre (renew : Bool) (V : VState → Bool) (x : Execution)
    (missing : x.accounts.allocation x.resident.token=none) : actualPre renew V x=false := by
  simp [actualPre,rawRows,enabled,missing,bits]
  cases x.resident.installed <;> simp

theorem wrong_owner_pre (renew : Bool) (V : VState → Bool) (x : Execution)
    (unowned : x.accounts.allocation x.resident.token ≠ some (.localGenerator x.resident.owner)) :
    actualPre renew V x=false := by
  simp [actualPre,no_owner _ x _ unowned,bits]

theorem empty_charge_pre (renew : Bool) (V : VState → Bool) (x : Execution)
    (empty : x.accounts.charge x.resident.token=false) : actualPre renew V x=false := by
  simp [actualPre,no_charge _ x _ empty,bits]

theorem owned_rows_positive_normalized (renew : Bool) (x : Execution) (owned : Owned x)
    (charged : x.accounts.charge x.resident.token=true) (a : Bool) :
    (∀ e ∈ rawRows (environment renew) x a, 0<e.2) ∧
    (rawRows (environment renew) x a).foldr (fun e acc => e.2+acc) 0=16 := by
  have roweq : rawRows (environment renew) x a=
      (rows x.resident.current a).map (fun e => (advance (environment renew) x a e.1 e.2,e.2)) := by
    simp [rawRows,owned.1,enabled,owned.2,charged,model]
  rw [roweq]
  constructor
  · intro e member
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp member
    exact ((rows_positive_normalized x.resident.current a).1 f hf).1
  · simpa [List.sum,List.foldr_map] using (rows_positive_normalized x.resident.current a).2

theorem owned_advance (renew : Bool) (x : Execution) (h : Owned x)
    (a : Bool) (s : State) (n : Nat) : Owned (advance (environment renew) x a s n) :=
  ⟨h.1,h.2⟩

theorem owned_successor (renew : Bool) (x y : Execution) (h : Owned x)
    (a : Bool) (n : Nat) (edge : (y,n) ∈ rawRows (environment renew) x a) : Owned y := by
  simp only [rawRows,h.1] at edge
  split at edge
  · obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
    have same : advance (environment renew) x a e.1 e.2=y := congrArg Prod.fst eq
    rw [←same]
    exact owned_advance renew x h a e.1 e.2
  · simp at edge

/-- Finite supported paths from any actual installed/owned initial configuration.
The root is explicit; source-only reachability is not silently assumed. -/
inductive Path (renew : Bool) : Execution → Type where
  | root (x : Execution) (owned : Owned x) : Path renew x
  | step {x : Execution} (past : Path renew x) (a : Bool) (y : Execution) (n : Nat)
      (edge : (y,n) ∈ rawRows (environment renew) x a) : Path renew y

abbrev History (renew : Bool) := (x : Execution) × Path renew x

def extend {renew : Bool} (h : History renew) (a : Bool) (y : Execution) (n : Nat)
    (edge : (y,n) ∈ rawRows (environment renew) h.1 a) : History renew :=
  ⟨y,.step h.2 a y n edge⟩

theorem history_owned {renew : Bool} (h : History renew) : Owned h.1 := by
  rcases h with ⟨x,path⟩
  induction path with
  | root x owned => exact owned
  | step past a y n edge ih => exact owned_successor renew _ y ih a n edge

/-- Nonblocking safe controlled predecessor, on the entire supported history.
One action must retain every actual stochastic successor; paths are not selected
or renormalized. Predicates may read any earlier execution or action. -/
def historyPre (renew : Bool) (V : History renew → Prop) (h : History renew) : Prop :=
  h.1.resident.current.outside=false ∧ ∃ a : Bool,
    rawRows (environment renew) h.1 a ≠ [] ∧
    ∀ y n (edge : (y,n) ∈ rawRows (environment renew) h.1 a), V (extend h a y n edge)

def HistoryControlled (renew : Bool) (V : History renew → Prop) : Prop :=
  ∀ h, V h → historyPre renew V h

def historyCore (renew : Bool) (h : History renew) : Prop := core (quote h.1)=true

theorem history_pre_mono (renew : Bool) (V W : History renew → Prop)
    (order : ∀ h, V h → W h) (h : History renew) (retained : historyPre renew V h) :
    historyPre renew W h := by
  obtain ⟨safe,a,nonempty,all⟩ := retained
  exact ⟨safe,a,nonempty,fun y n edge => order _ (all y n edge)⟩

theorem history_pre_projection (renew : Bool) (V : VState → Bool) (h : History renew) :
    historyPre renew (fun k => V (quote k.1)=true) h ↔ pre renew V (quote h.1)=true := by
  rw [←actual_pre_projection renew V h.1 (history_owned h)]
  simp only [historyPre,actualPre,Bool.and_eq_true,List.any_eq_true,List.all_eq_true]
  constructor
  · rintro ⟨safe,a,nonempty,all⟩
    refine ⟨by simpa using safe,a,?_,by simpa using nonempty,?_⟩
    · cases a <;> simp [bits]
    · intro e edge
      exact all e.1 e.2 edge
  · rintro ⟨safe,a,_,nonempty,all⟩
    exact ⟨by simpa using safe,a,by simpa using nonempty,fun y n edge => all (y,n) edge⟩

theorem history_controlled_subset_core (renew : Bool) (V : History renew → Prop)
    (invariant : HistoryControlled renew V) (h : History renew) (member : V h) :
    historyCore renew h := by
  have top := history_pre_mono renew V (fun _ => True) (fun _ _ => True.intro)
    h (invariant h member)
  have finite : pre renew (fun _ => true) (quote h.1)=true :=
    (history_pre_projection renew (fun _ => true) h).mp (by simpa using top)
  simpa only [pre_top] using finite

theorem history_core_invariant : HistoryControlled true (historyCore true) := by
  intro h member
  apply (history_pre_projection true core h).mpr
  exact (renewable_pre_core _).trans member

theorem history_core_greatest : HistoryControlled true (historyCore true) ∧
    ∀ V : History true → Prop, HistoryControlled true V → ∀ h, V h → historyCore true h :=
  ⟨history_core_invariant,fun V inv h mem => history_controlled_subset_core true V inv h mem⟩

theorem history_core_fixed (h : History true) :
    historyPre true (historyCore true) h ↔ historyCore true h := by
  unfold historyCore
  rw [history_pre_projection,renewable_pre_core]

theorem history_underfund_greatest_empty (V : History false → Prop)
    (invariant : HistoryControlled false V) : ∀ h, ¬ V h := by
  intro h member
  have retained := history_pre_mono false V (historyCore false)
    (history_controlled_subset_core false V invariant) h (invariant h member)
  have finite := (history_pre_projection false core h).mp retained
  rw [absent_pre_core] at finite
  contradiction

theorem empty_history_invariant (renew : Bool) :
    HistoryControlled renew (fun _ => False) := fun _ member => member.elim

/-- Membership in some arbitrary history-dependent invariant is exactly the
factor-derived greatest set. This is a greatestness result, not just a bound. -/
theorem history_viable_iff (renew : Bool) (h : History renew) :
    (∃ V : History renew → Prop, HistoryControlled renew V ∧ V h) ↔
      (renew=true ∧ historyCore renew h) := by
  cases renew with
  | false =>
    constructor
    · rintro ⟨V,inv,mem⟩
      exact (history_underfund_greatest_empty V inv h mem).elim
    · rintro ⟨impossible,_⟩
      contradiction
  | true =>
    constructor
    · rintro ⟨V,inv,mem⟩
      exact ⟨rfl,history_controlled_subset_core true V inv h mem⟩
    · rintro ⟨_,mem⟩
      exact ⟨historyCore true,history_core_invariant,mem⟩

/-- Existential projection preserves invariant closure even when the predicate
does not descend to the finite factor. No converse for arbitrary predicates is
asserted: projected successors can have different pasts. -/
def historyImage (renew : Bool) (V : History renew → Prop) (q : VState) : Prop :=
  ∃ h, V h ∧ quote h.1=q

def factorPre (renew : Bool) (V : VState → Prop) (q : VState) : Prop :=
  q.1.outside=false ∧ ∃ a : Bool, fundedRows renew q a ≠ [] ∧
    ∀ t n, (t,n) ∈ fundedRows renew q a → V t

theorem history_pre_image (renew : Bool) (V : History renew → Prop) (h : History renew)
    (retained : historyPre renew V h) : factorPre renew (historyImage renew V) (quote h.1) := by
  obtain ⟨safe,a,nonempty,all⟩ := retained
  refine ⟨safe,a,?_,?_⟩
  · rw [←owned_projection renew h.1 (history_owned h) a]
    simpa using nonempty
  · intro t n edge
    rw [←owned_projection renew h.1 (history_owned h) a] at edge
    obtain ⟨e,member,eq⟩ := List.mem_map.mp edge
    have qt : quote e.1=t := congrArg Prod.fst eq
    exact ⟨extend h a e.1 e.2 member,all e.1 e.2 member,qt⟩

theorem history_invariant_image (renew : Bool) (V : History renew → Prop)
    (invariant : HistoryControlled renew V) :
    ∀ q, historyImage renew V q → factorPre renew (historyImage renew V) q := by
  rintro q ⟨h,member,eq⟩
  rw [←eq]
  exact history_pre_image renew V h (invariant h member)

theorem absent_successor_stops (x y : Execution) (a : Bool) (n : Nat)
    (owned : Owned x) (edge : (y,n) ∈ rawRows absentSupply x a) :
    y.accounts.charge y.resident.token=false ∧
    (∀ b, rawRows absentSupply y b=[]) ∧
    (y.resident.receipts.head?).map Receipt.energy=some none ∧
    y.accounts.portCursor y.resident.token=x.accounts.portCursor x.resident.token+1 := by
  simp only [rawRows,owned.1] at edge
  split at edge
  · obtain ⟨e,_,eq⟩ := List.mem_map.mp edge
    have same : advance absentSupply x a e.1 e.2=y := congrArg Prod.fst eq
    rw [←same]
    exact ⟨missing_energy_depletes _ _,fun b => energy_absence_stops_next x a b e.1 e.2,
      rfl,cursor_after _ _ _⟩
  · simp at edge

theorem history_absent_first_step_and_stop (h : History false) (member : historyCore false h) :
    ∃ a y n, ∃ edge : (y,n) ∈ rawRows absentSupply h.1 a,
      (∀ b, rawRows absentSupply y b=[]) ∧
      ¬ historyCore false (extend h a y n edge) := by
  have top : historyPre false (fun k => (true:Bool)=true) h :=
    (history_pre_projection false (fun _ => true) h).mpr ((pre_top false _).trans member)
  obtain ⟨_,a,nonempty,_⟩ := top
  obtain ⟨e,edge⟩ := List.exists_mem_of_ne_nil _ nonempty
  have stopped := absent_successor_stops h.1 e.1 a e.2 (history_owned h) edge
  refine ⟨a,e.1,e.2,edge,stopped.2.1,?_⟩
  simp [historyCore,extend,core,quote,stopped.1]

/-- Canonical installed/owned initial configurations realize every factor state;
this changes only initial physical state and stored charge, not any primitive. -/
def initialFor (q : VState) : Execution :=
  ⟨{source.accounts with charge := put source.accounts.charge source.resident.token q.2},
    {source.resident with current := q.1}⟩

theorem initial_for_owned (q : VState) : Owned (initialFor q) := ⟨rfl,rfl⟩

theorem initial_for_quote (q : VState) : quote (initialFor q)=q := by
  simp [initialFor,quote,put]

def initialHistory (renew : Bool) (q : VState) : History renew :=
  ⟨initialFor q,.root (initialFor q) (initial_for_owned q)⟩

theorem history_core_projection_exact (q : VState) :
    (∃ h : History true, historyCore true h ∧ quote h.1=q) ↔ core q=true := by
  constructor
  · rintro ⟨h,mem,eq⟩
    rwa [←eq]
  · intro mem
    exact ⟨initialHistory true q,by simpa [historyCore,initialHistory,initial_for_quote] using mem,
      initial_for_quote q⟩

theorem greatest_viability_projection_exact (renew : Bool) (q : VState) :
    (∃ h : History renew, (∃ V : History renew → Prop, HistoryControlled renew V ∧ V h) ∧
      quote h.1=q) ↔ (renew=true ∧ core q=true) := by
  constructor
  · rintro ⟨h,viable,eq⟩
    obtain ⟨funded,mem⟩ := (history_viable_iff renew h).mp viable
    exact ⟨funded,by simpa [historyCore,eq] using mem⟩
  · rintro ⟨funded,mem⟩
    refine ⟨initialHistory renew q,?_,initial_for_quote q⟩
    apply (history_viable_iff renew _).mpr
    exact ⟨funded,by simpa [historyCore,initialHistory,initial_for_quote] using mem⟩

theorem history_underfund_projection_empty (q : VState) :
    ¬ ∃ h : History false, (∃ V : History false → Prop, HistoryControlled false V ∧ V h) ∧
      quote h.1=q := by
  rintro ⟨h,⟨V,inv,mem⟩,_⟩
  exact history_underfund_greatest_empty V inv h mem

def sourceHistory (renew : Bool) : History renew := ⟨source,.root source source_owned_viable.1⟩

def firstTargetHistory (renew : Bool) : History renew :=
  ⟨⟨Credit.creditedBothWorld.accounts,Credit.creditedFirstLocal⟩,
    .root _ credited_targets_owned_viable.1⟩

def secondTargetHistory (renew : Bool) : History renew :=
  ⟨⟨Credit.creditedBothWorld.accounts,Credit.creditedSecondLocal⟩,
    .root _ credited_targets_owned_viable.2.1⟩

theorem source_and_credited_target_history_viability :
    historyCore true (sourceHistory true) ∧ historyCore true (firstTargetHistory true) ∧
    historyCore true (secondTargetHistory true) :=
  ⟨source_owned_viable.2,credited_targets_owned_viable.2.2.1,
    credited_targets_owned_viable.2.2.2⟩

theorem historical_credited_target_viability :
    SnapshotExecution.Historical Credit.creditedBothWorld ∧
    Credit.localCredit Credit.creditedBothWorld 1=some .self ∧
    Credit.localCredit Credit.creditedBothWorld 2=some .self ∧
    historyCore true (firstTargetHistory true) ∧ historyCore true (secondTargetHistory true) :=
  ⟨Credit.credited_both_historical,Credit.same_history_both_credits.1,
    Credit.same_history_both_credits.2.1,source_and_credited_target_history_viability.2⟩

def origin {renew : Bool} {x : Execution} : Path renew x → Execution
  | .root x _ => x
  | .step past _ _ _ _ => origin past

theorem reachable_source_history (x : Execution) (reachable : Reachable renewable x) :
    ∃ h : History true, h.1=x ∧ origin h.2=source := by
  induction reachable with
  | initial => exact ⟨sourceHistory true,rfl,rfl⟩
  | @step x y a n reachable edge ih =>
    obtain ⟨⟨z,path⟩,rfl,root⟩ := ih
    exact ⟨extend ⟨z,path⟩ a y n edge,rfl,root⟩

theorem maintenance_support (s t : State) (inside : t.outside=false)
    (phase : t.phase= !s.phase) : (t,weight s t.u t.v) ∈ rows s false := by
  cases s with
  | mk p u v r clock =>
    cases t with
    | mk q x y j tick =>
      cases p <;> cases u <;> cases v <;> cases r <;> cases clock <;>
        cases q <;> cases x <;> cases y <;> cases j <;> cases tick <;>
        first | contradiction | decide +kernel

theorem renewable_inside_source_reachable (s : State) (inside : s.outside=false) :
    ∃ x, Reachable renewable x ∧ quote x=(s,true) := by
  cases phase : s.phase with
  | true =>
    let n := weight source.resident.current s.u s.v
    have edge : (advance renewable source false s n,n) ∈ rawRows renewable source false := by
      rw [sector_rows source source_sector]
      exact List.mem_map.mpr ⟨(s,n),maintenance_support _ s inside (by simpa [source] using phase),rfl⟩
    exact ⟨advance renewable source false s n,Reachable.step .initial edge,
      by simp [quote,advance,renewable_charge]⟩
  | false =>
    let n := weight replicaLeft.resident.current s.u s.v
    have sector := reachable_sector replicaLeft actual_reachable_fiber.1
    have edge : (advance renewable replicaLeft false s n,n) ∈ rawRows renewable replicaLeft false := by
      rw [sector_rows replicaLeft sector]
      exact List.mem_map.mpr ⟨(s,n),maintenance_support _ s inside
        (by simpa [replicaLeft,advance,FullInterface.replicaLeft] using phase),rfl⟩
    exact ⟨advance renewable replicaLeft false s n,Reachable.step actual_reachable_fiber.1 edge,
      by simp [quote,advance,renewable_charge]⟩

/-- Even requiring actual source-rooted supported paths gives exactly all sixteen
renewable core states. Exactness does not rely on artificial factor roots. -/
theorem source_rooted_greatest_projection_exact (q : VState) :
    (∃ h : History true, origin h.2=source ∧
      (∃ V : History true → Prop, HistoryControlled true V ∧ V h) ∧ quote h.1=q) ↔ core q=true := by
  constructor
  · rintro ⟨h,_,viable,eq⟩
    exact ((greatest_viability_projection_exact true q).mp ⟨h,viable,eq⟩).2
  · intro member
    have parts : (!q.1.outside)=true ∧ q.2=true := by
      simpa only [core,Bool.and_eq_true] using member
    have inside : q.1.outside=false := by simpa using parts.1
    have charged : q.2=true := parts.2
    obtain ⟨x,reachable,eq⟩ := renewable_inside_source_reachable q.1 inside
    obtain ⟨h,tip,root⟩ := reachable_source_history x reachable
    have same : quote h.1=q := by
      rw [tip,eq]
      exact Prod.ext rfl charged.symm
    refine ⟨h,root,(history_viable_iff true h).mpr ⟨rfl,?_⟩,same⟩
    simpa [historyCore,same] using member

end CSTTT.FullNative.Viability
