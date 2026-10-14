import CSTTT.Targets.GenericHandoff.NativeComposition.CoupledKernel

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeCarrierClockPrototype
open RegisterInterpreter
open CoupledNativeKernelPrototype
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

-- The order coordinate, expenditure, and emitted record live in the carrier.
structure Carrier where
  owner : Owner
  factor : Factor
  counter : Nat
  budget : Nat
  record : List Factor
  deriving DecidableEq

def initial (i : Input) (owner : Owner) (s : Factor) : Carrier :=
  ⟨owner,s,0,i.temporal.ledger.initial,[s]⟩

def funded (i : Input) (r : Carrier) : Bool :=
  decide (r.owner=i.temporal.resource.owner ∧ i.temporal.ledger.cost≤r.budget)

def advance (i : Input) (r : Carrier) (action : Bool) (outcome : Factor) : Carrier :=
  {r with
    factor := outcome
    counter := r.counter + i.temporal.ticks r.factor action
    budget := r.budget - i.temporal.ledger.cost +
      (if i.temporal.resource.rechargeAvailable then i.temporal.ledger.recharge else 0)
    record := r.record ++ [outcome]}

def liftedRows (i : Input) (r : Carrier) (action : Bool) : List (Carrier × Nat) :=
  if funded i r then (i.temporal.rows r.factor action).map
    (fun e => (advance i r action e.1,e.2)) else []

def supported (i : Input) (r : Carrier) (action : Bool) (outcome : Factor) : Bool :=
  (i.temporal.rows r.factor action).any (fun e => decide (e.1=outcome ∧ e.2>0))

def step (i : Input) (r : Carrier) (action : Bool) (outcome : Factor) : Option Carrier :=
  if funded i r && supported i r action outcome then some (advance i r action outcome) else none

theorem step_some_exact (i : Input) (r : Carrier) (a : Bool) (o : Factor) (next : Carrier) :
    step i r a o=some next ↔
    (r.owner=i.temporal.resource.owner ∧ i.temporal.ledger.cost≤r.budget) ∧
    (∃ e∈i.temporal.rows r.factor a,e.1=o ∧ e.2>0) ∧ next=advance i r a o := by
  have h : step i r a o=some next ↔ funded i r=true ∧
      supported i r a o=true ∧ next=advance i r a o := by
    unfold step
    generalize funded i r=b
    generalize supported i r a o=c
    cases b <;> cases c <;> simp [Eq.comm]
  rw [h]
  simp only [funded,supported,List.any_eq_true,decide_eq_true_eq]

theorem wrong_owner_step_rejected (i : Input) (r : Carrier) (a : Bool) (o : Factor)
    (wrong : r.owner≠i.temporal.resource.owner) : step i r a o=none := by
  simp [step,funded,wrong]

theorem underbudget_step_rejected (i : Input) (r : Carrier) (a : Bool) (o : Factor)
    (bad : r.budget<i.temporal.ledger.cost) : step i r a o=none := by
  have h : ¬i.temporal.ledger.cost≤r.budget := by omega
  simp [step,funded,h]

theorem unsupported_step_rejected (i : Input) (r : Carrier) (a : Bool) (o : Factor)
    (bad : ∀ e∈i.temporal.rows r.factor a,e.1=o → e.2=0) : step i r a o=none := by
  have h : supported i r a o=false := by
    apply Bool.eq_false_iff.mpr
    intro yes
    obtain ⟨e,he,hpred⟩ := (List.any_eq_true.mp yes)
    have hp := of_decide_eq_true hpred
    have hz := bad e he hp.1
    have hpos := hp.2
    omega
  simp [step,h]

theorem actual_funded (owner : Owner) (r : Carrier) (ho : r.owner=owner) (hb : r.budget=1) :
    funded (input owner) r=true := by
  simp [funded,input,canonicalInput,factorData,ho,hb]

theorem advance_factor (i : Input) (r : Carrier) (a : Bool) (o : Factor) :
    (advance i r a o).factor=o := rfl
theorem advance_owner (i : Input) (r : Carrier) (a : Bool) (o : Factor) :
    (advance i r a o).owner=r.owner := rfl
theorem advance_record (i : Input) (r : Carrier) (a : Bool) (o : Factor) :
    (advance i r a o).record=r.record++[o] := rfl
theorem actual_advance_counter (owner : Owner) (r : Carrier) (a : Bool) (o : Factor) :
    (advance (input owner) r a o).counter=r.counter+1 := rfl
theorem actual_advance_budget (owner : Owner) (r : Carrier) (a : Bool) (o : Factor)
    (hb : r.budget=1) : (advance (input owner) r a o).budget=1 := by
  simp [advance,input,canonicalInput,factorData,hb]

theorem actual_lifted_rows (owner : Owner) (r : Carrier) (a : Bool)
    (ho : r.owner=owner) (hb : r.budget=1) :
    liftedRows (input owner) r a=(rows r.factor a).map
      (fun e => (advance (input owner) r a e.1,e.2)) := by
  simp only [liftedRows,actual_funded owner r ho hb,ite_true,selected_rows]

theorem actual_lifted_total (owner : Owner) (r : Carrier) (a : Bool)
    (ho : r.owner=owner) (hb : r.budget=1) :
    ((liftedRows (input owner) r a).map Prod.snd).sum=8 := by
  rw [actual_lifted_rows owner r a ho hb]
  simpa only [List.map_map,Function.comp_def] using (rows_positive_normalized r.factor a).2

theorem actual_lifted_projection (owner : Owner) (r : Carrier) (a : Bool)
    (ho : r.owner=owner) (hb : r.budget=1) :
    (liftedRows (input owner) r a).map (fun e => (e.1.factor,e.2))=rows r.factor a := by
  rw [actual_lifted_rows owner r a ho hb]
  simp only [List.map_map,Function.comp_def,advance_factor]
  exact List.map_id _

-- No stream is an input: each next outcome is the first actual policy edge.
def maintenanceStep (i : Input) (r : Carrier) : Option Carrier := do
  let edge ← (i.temporal.rows r.factor (i.temporal.policy r.factor)).head?
  step i r (i.temporal.policy r.factor) edge.1

def maintain (i : Input) : Carrier → Nat → Option Carrier
  | r,0 => some r
  | r,n+1 => do
    let next ← maintenanceStep i r
    maintain i next n

def nativeNext (s : Factor) : Factor := if s.1 then s else embed (false,false)
def nativeFirstWeight (s : Factor) : Nat := if s.1 then 8 else diagonalWeight s.2

theorem native_head (s : Factor) :
    (rows s false).head?=some (nativeNext s,nativeFirstWeight s) := by
  rcases s with ⟨p,u,v⟩; cases p <;> cases u <;> cases v <;> rfl

theorem native_first_supported (s : Factor) :
    (rows s false).any (fun e => decide (e.1=nativeNext s ∧ e.2>0))=true := by
  rcases s with ⟨p,u,v⟩; cases p <;> cases u <;> cases v <;> decide +kernel +revert

theorem actual_maintenance_step (owner : Owner) (r : Carrier)
    (ho : r.owner=owner) (hb : r.budget=1) :
    maintenanceStep (input owner) r=some (advance (input owner) r false (nativeNext r.factor)) := by
  simp only [maintenanceStep]
  change ((rows r.factor false).head?).bind (fun e => step (input owner) r false e.1)=_
  rw [native_head]
  simp only [Option.bind_some,step,actual_funded owner r ho hb]
  change (if true && (rows r.factor false).any _ then _ else _)=_
  rw [native_first_supported r.factor]
  rfl

def after (owner : Owner) : Carrier → Nat → Carrier
  | r,0 => r
  | r,n+1 => after owner (advance (input owner) r false (nativeNext r.factor)) n

theorem after_owner (owner : Owner) (r : Carrier) (n : Nat) :
    (after owner r n).owner=r.owner := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih => rw [after,ih,advance_owner]

theorem after_budget (owner : Owner) (r : Carrier) (n : Nat) (hb : r.budget=1) :
    (after owner r n).budget=1 := by
  induction n generalizing r with
  | zero => exact hb
  | succ n ih => exact ih _ (actual_advance_budget owner r false _ hb)

theorem after_counter (owner : Owner) (r : Carrier) (n : Nat) :
    (after owner r n).counter=r.counter+n := by
  induction n generalizing r with
  | zero => simp [after]
  | succ n ih => rw [after,ih,actual_advance_counter]; omega

theorem after_record_length (owner : Owner) (r : Carrier) (n : Nat) :
    (after owner r n).record.length=r.record.length+n := by
  induction n generalizing r with
  | zero => simp [after]
  | succ n ih => rw [after,ih,advance_record,List.length_append]; simp; omega

theorem actual_maintain_exact (owner : Owner) (r : Carrier) (n : Nat)
    (ho : r.owner=owner) (hb : r.budget=1) :
    maintain (input owner) r n=some (after owner r n) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    simp only [maintain,actual_maintenance_step owner r ho hb,after]
    exact ih _ (by rw [advance_owner,ho]) (actual_advance_budget owner r false _ hb)

theorem native_next_inside (s : Factor) (hs : s.1=false) : (nativeNext s).1=false := by
  simp [nativeNext,hs,embed]

theorem after_inside (owner : Owner) (r : Carrier) (n : Nat) (hs : r.factor.1=false) :
    (after owner r n).factor.1=false := by
  induction n generalizing r with
  | zero => exact hs
  | succ n ih => exact ih _ (native_next_inside r.factor hs)

theorem unbounded_funded_carrier (owner : Owner) (s : Kernel) (n : Nat) :
    ∃ final,maintain (input owner) (initial (input owner) owner (embed s)) n=some final ∧
      final.owner=owner ∧ final.factor.1=false ∧ final.counter=n ∧ final.budget=1 ∧
      final.record.length=n+1 := by
  refine ⟨after owner (initial (input owner) owner (embed s)) n,
    actual_maintain_exact owner _ n rfl rfl,after_owner owner _ n,after_inside owner _ n rfl,?_,
    after_budget owner _ n rfl,?_⟩
  · simpa [initial] using after_counter owner (initial (input owner) owner (embed s)) n
  · simpa [initial,Nat.add_comm] using after_record_length owner (initial (input owner) owner (embed s)) n

-- The lift keeps the entire law, rather than merely a chosen legal trajectory.
def liftedMass (i : Input) (observe : Factor → Nat) (r : Carrier)
    (word : List Bool) (outputs : List Nat) : Nat :=
  NativeObservedFutureRulesPrototype.mass (liftedRows i) (fun r => observe r.factor) r word outputs

theorem lifted_future_exact (owner : Owner) (observe : Factor → Nat) (r : Carrier)
    (word : List Bool) (outputs : List Nat) (ho : r.owner=owner) (hb : r.budget=1) :
    liftedMass (input owner) observe r word outputs=
      outputMass (input owner) observe r.factor word outputs := by
  induction word generalizing r outputs with
  | nil => cases outputs <;> rfl
  | cons a rest ih =>
    cases outputs with
    | nil => rfl
    | cons obs tail =>
      simp only [liftedMass,NativeObservedFutureRulesPrototype.mass,outputMass,
        actual_lifted_rows owner r a ho hb,List.foldr_map]
      apply congrArg (fun f => (rows r.factor a).foldr f 0)
      funext edge acc
      have hx := ih (advance (input owner) r a edge.1) tail
        (by rw [advance_owner,ho]) (actual_advance_budget owner r a edge.1 hb)
      simp only [liftedMass] at hx
      simp only [advance_factor,hx]

-- The arrow is the actual native probability-cycle audit with housed provenance.
def ownArrow (i : Input) (owner : Owner) : Prop :=
  i.temporal.resource.owner=owner ∧ forward i≠reverse i

def ClockClosed (i : Input) (owner : Owner) : Prop :=
  ownArrow i owner ∧ i.temporal.ledger.cost>0 ∧ i.temporal.ledger.initial>0 ∧
  i.temporal.resource.rechargeAvailable=true ∧
  (∀ s a,i.temporal.ticks s a>0) ∧
  ∀ r,r.owner=owner → r.budget=i.temporal.ledger.initial → ∀ n,
    ∃ final,maintain i r n=some final ∧ final.owner=owner ∧
      final.budget=i.temporal.ledger.initial ∧ final.counter=r.counter+n ∧
      final.record.length=r.record.length+n

theorem actual_clock_closed (owner : Owner) : ClockClosed (input owner) owner := by
  refine ⟨⟨rfl,(actual_cycle_directionality owner).2.2⟩,Nat.zero_lt_one,Nat.zero_lt_one,rfl,?_,?_⟩
  · intro s a; exact Nat.zero_lt_one
  · intro r ho hb n
    change r.budget=1 at hb
    exact ⟨after owner r n,actual_maintain_exact owner r n ho hb,
      (after_owner owner r n).trans ho,after_budget owner r n hb,
      after_counter owner r n,after_record_length owner r n⟩

theorem flat_own_arrow_false (owner : Owner) : ¬ownArrow (flatten (input owner)) owner := by
  intro h
  apply h.2
  exact flat_cycle_collapses (input owner)

theorem flat_clock_false (owner : Owner) : ¬ClockClosed (flatten (input owner)) owner :=
  fun h => flat_own_arrow_false owner h.1

def zeroTicks (i : Input) : Input :=
  {i with temporal:={i.temporal with ticks:=fun _ _ => 0}}

theorem zero_tick_clock_false (i : Input) (owner : Owner) : ¬ClockClosed (zeroTicks i) owner := by
  intro h
  have bad := h.2.2.2.2.1 (false,false,false) false
  change 0>0 at bad
  omega

noncomputable def clockBit (owner : Owner) (i : Input) : Bool := by
  classical
  exact decide (ClockClosed i owner)

theorem actual_clock_bit (owner : Owner) : clockBit owner (input owner)=true := by
  classical
  exact decide_eq_true (actual_clock_closed owner)
theorem flat_clock_bit (owner : Owner) : clockBit owner (flatten (input owner))=false := by
  classical
  exact decide_eq_false (flat_clock_false owner)
theorem zero_tick_clock_bit (owner : Owner) (i : Input) : clockBit owner (zeroTicks i)=false := by
  classical
  exact decide_eq_false (zero_tick_clock_false i owner)

theorem clock_readout_true_exact (owner cell : Owner) (copy : Bool)
    (a : Assignment Owner MemoryValue) : readout (clockBit owner) cell copy a=some true ↔
      ∃ pair,a cell=some pair ∧ ClockClosed (MemoryFrames.selectInput copy pair) owner := by
  classical
  rw [readout_some_exact]
  simp [clockBit]

theorem clock_readout_false_exact (owner cell : Owner) (copy : Bool)
    (a : Assignment Owner MemoryValue) : readout (clockBit owner) cell copy a=some false ↔
      ∃ pair,a cell=some pair ∧ ¬ClockClosed (MemoryFrames.selectInput copy pair) owner := by
  classical
  rw [readout_some_exact]
  simp [clockBit]

theorem concrete_clock_readouts (owner : Owner) :
    readout (clockBit owner) owner false assignment=some true ∧
    readout (clockBit owner) owner false flatAssignment=some false ∧
    readout (clockBit owner) owner true flatAssignment=some true := by
  simp [readout,selected,assignment,flatAssignment,
    MemoryFrames.selectInput,actual_clock_bit,flat_clock_bit]

-- Prefix-compatible construction gives a single unbounded accepted carrier run.
theorem after_add (owner : Owner) (r : Carrier) (m n : Nat) :
    after owner r (m+n)=after owner (after owner r m) n := by
  induction m generalizing r with
  | zero => simp [after]
  | succ m ih => simp only [Nat.succ_add,after,ih]

theorem after_succ (owner : Owner) (r : Carrier) (n : Nat) :
    after owner r (n+1)=advance (input owner) (after owner r n) false
      (nativeNext (after owner r n).factor) := by
  rw [after_add]
  rfl

theorem coherent_unbounded_run (owner : Owner) (r : Carrier)
    (ho : r.owner=owner) (hb : r.budget=1) (n : Nat) :
    maintenanceStep (input owner) (after owner r n)=some (after owner r (n+1)) ∧
      (after owner r n).counter<(after owner r (n+1)).counter ∧
      (after owner r (n+1)).record=(after owner r n).record++
        [(after owner r (n+1)).factor] := by
  refine ⟨?_,?_,?_⟩
  · rw [after_succ]
    exact actual_maintenance_step owner _ ((after_owner owner r n).trans ho)
      (after_budget owner r n hb)
  · rw [after_counter,after_counter]; omega
  · rw [after_succ,advance_record,advance_factor]

theorem distinct_carrier_ticks (owner : Owner) (r : Carrier) (m n : Nat)
    (different : m≠n) : after owner r m≠after owner r n := by
  intro equal
  have h := congrArg Carrier.counter equal
  rw [after_counter,after_counter] at h
  omega

-- Flattening keeps the entire executable clock, while its native arrow is gone.
theorem flat_head (s : Factor) :
    (flatRows s false).head?=some (nativeNext s,if s.1 then 8 else 2) := by
  rcases s with ⟨p,u,v⟩; cases p <;> cases u <;> cases v <;> rfl

theorem flat_first_supported (s : Factor) :
    (flatRows s false).any (fun e => decide (e.1=nativeNext s ∧ e.2>0))=true := by
  rcases s with ⟨p,u,v⟩; cases p <;> cases u <;> cases v <;> decide +kernel

theorem flat_advance_same (i : Input) (r : Carrier) (a : Bool) (o : Factor) :
    advance (flatten i) r a o=advance i r a o := rfl

theorem flat_maintenance_step (owner : Owner) (r : Carrier)
    (ho : r.owner=owner) (hb : r.budget=1) :
    maintenanceStep (flatten (input owner)) r=
      some (advance (input owner) r false (nativeNext r.factor)) := by
  simp only [maintenanceStep]
  change ((flatRows r.factor false).head?).bind
    (fun e => step (flatten (input owner)) r false e.1)=_
  rw [flat_head]
  simp only [Option.bind_some,step]
  have hf : funded (flatten (input owner)) r=true := actual_funded owner r ho hb
  rw [hf]
  change (if true && (flatRows r.factor false).any _ then _ else _)=_
  rw [flat_first_supported r.factor]
  rfl

theorem flat_maintain_same (owner : Owner) (r : Carrier) (n : Nat)
    (ho : r.owner=owner) (hb : r.budget=1) :
    maintain (flatten (input owner)) r n=maintain (input owner) r n := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    simp only [maintain,flat_maintenance_step owner r ho hb,
      actual_maintenance_step owner r ho hb]
    exact ih _ (by rw [advance_owner,ho]) (actual_advance_budget owner r false _ hb)

theorem ticks_do_not_supply_own_arrow (owner : Owner) (r : Carrier) (n : Nat)
    (ho : r.owner=owner) (hb : r.budget=1) :
    maintain (flatten (input owner)) r n=some (after owner r n) ∧
    (after owner r n).counter=r.counter+n ∧
    ¬ClockClosed (flatten (input owner)) owner :=
  ⟨(flat_maintain_same owner r n ho hb).trans (actual_maintain_exact owner r n ho hb),
    after_counter owner r n,flat_clock_false owner⟩

-- Actual recharge-off execution spends its last unit and cannot execute twice.
theorem unfunded_maintenance_step (owner : Owner) (r : Carrier)
    (ho : r.owner=owner) (hb : r.budget=1) :
    maintenanceStep (unfunded (input owner)) r=
      some (advance (unfunded (input owner)) r false (nativeNext r.factor)) := by
  simp only [maintenanceStep]
  change ((rows r.factor false).head?).bind
    (fun e => step (unfunded (input owner)) r false e.1)=_
  rw [native_head]
  simp only [Option.bind_some,step]
  have hf : funded (unfunded (input owner)) r=true := actual_funded owner r ho hb
  rw [hf]
  change (if true && (rows r.factor false).any _ then _ else _)=_
  rw [native_first_supported r.factor]
  rfl

theorem unfunded_advance_budget (owner : Owner) (r : Carrier) (a : Bool) (o : Factor)
    (hb : r.budget=1) : (advance (unfunded (input owner)) r a o).budget=0 := by
  simp [advance,unfunded,input,canonicalInput,factorData,hb]

theorem unfunded_zero_budget_step (owner : Owner) (r : Carrier) (hb : r.budget=0) :
    maintenanceStep (unfunded (input owner)) r=none := by
  unfold maintenanceStep
  cases hh : ((unfunded (input owner)).temporal.rows r.factor
      ((unfunded (input owner)).temporal.policy r.factor)).head? with
  | none => rfl
  | some e =>
    apply underbudget_step_rejected
    simp [unfunded,input,canonicalInput,factorData,hb]

theorem unfunded_two_steps_reject (owner : Owner) (r : Carrier)
    (ho : r.owner=owner) (hb : r.budget=1) :
    maintain (unfunded (input owner)) r 2=none := by
  simp only [maintain,unfunded_maintenance_step owner r ho hb]
  change (maintenanceStep (unfunded (input owner))
    (advance (unfunded (input owner)) r false (nativeNext r.factor))).bind (fun next => some next)=none
  rw [unfunded_zero_budget_step owner _ (unfunded_advance_budget owner r false _ hb)]
  rfl

theorem unfunded_clock_false (owner : Owner) : ¬ClockClosed (unfunded (input owner)) owner := by
  intro h
  have bad := h.2.2.2.1
  change false=true at bad
  contradiction

theorem unfunded_clock_bit (owner : Owner) : clockBit owner (unfunded (input owner))=false := by
  classical
  exact decide_eq_false (unfunded_clock_false owner)

def absentRows (i : Input) : Input :=
  {i with temporal:={i.temporal with rows:=fun _ _ => []}}

theorem absent_maintenance_rejected (i : Input) (r : Carrier) :
    maintenanceStep (absentRows i) r=none := rfl

theorem absent_one_step_rejected (i : Input) (r : Carrier) :
    maintain (absentRows i) r 1=none := rfl

theorem absent_clock_false (i : Input) (owner : Owner) : ¬ClockClosed (absentRows i) owner := by
  intro h
  have arrow := h.1.2
  apply arrow
  simp [forward,reverse,P,absentRows]

theorem absent_clock_bit (i : Input) (owner : Owner) : clockBit owner (absentRows i)=false := by
  classical
  exact decide_eq_false (absent_clock_false i owner)

-- A publicly observed tick/budget does not expose the hidden Factor future.
def publicTuple (i : Input) (r : Carrier) : List Nat :=
  [r.counter,r.budget]++factorCurrent i r.factor

def publicHistory (decode : List Nat → Nat) : Nat → Nat → List Nat
  | _,0 => []
  | counter,n+1 => decode [counter+1,1,0,1,1]::publicHistory decode (counter+1) n

theorem public_history_length (decode : List Nat → Nat) (counter n : Nat) :
    (publicHistory decode counter n).length=n := by
  induction n generalizing counter with
  | zero => rfl
  | succ n ih => simp [publicHistory,ih]

theorem next_public_tuple (owner : Owner) (r : Carrier) (a : Bool) (o : Factor)
    (hb : r.budget=1) :
    publicTuple (input owner) (advance (input owner) r a o)=[r.counter+1,1,0,1,1] := by
  simp only [publicTuple,actual_advance_counter,actual_advance_budget owner r a o hb,
    factor_current_constant]
  rfl

theorem lifted_public_history_exact (owner : Owner) (decode : List Nat → Nat)
    (r : Carrier) (word : List Bool) (outputs : List Nat)
    (ho : r.owner=owner) (hb : r.budget=1) :
    NativeObservedFutureRulesPrototype.mass (liftedRows (input owner))
      (fun r => decode (publicTuple (input owner) r)) r word outputs=
      if outputs=publicHistory decode r.counter word.length then 8^word.length else 0 := by
  induction word generalizing r outputs with
  | nil => cases outputs <;> simp [NativeObservedFutureRulesPrototype.mass,publicHistory]
  | cons a rest ih =>
    cases outputs with
    | nil => simp [NativeObservedFutureRulesPrototype.mass,publicHistory]
    | cons obs tail =>
      simp only [NativeObservedFutureRulesPrototype.mass,actual_lifted_rows owner r a ho hb,
        List.foldr_map]
      have hx (edge : Factor × Nat) :
          NativeObservedFutureRulesPrototype.mass (liftedRows (input owner))
            (fun r => decode (publicTuple (input owner) r))
            (advance (input owner) r a edge.1) rest tail=
          if tail=publicHistory decode (r.counter+1) rest.length then 8^rest.length else 0 := by
        rw [ih _ tail (by rw [advance_owner,ho]) (actual_advance_budget owner r a edge.1 hb)]
        rw [actual_advance_counter]
      simp only [next_public_tuple owner r a _ hb,hx]
      by_cases first : decode [r.counter+1,1,0,1,1]=obs
      · subst obs
        simp only [ite_true,NativeObservedFutureRulesPrototype.weighted_fold_constant,
          (rows_positive_normalized r.factor a).2]
        by_cases same : tail=publicHistory decode (r.counter+1) rest.length
        · simp [same,publicHistory,Nat.pow_succ,Nat.mul_comm]
        · simp [same,publicHistory]
      · simp [first,publicHistory,Ne.symm first,NativeObservedFutureRulesPrototype.foldr_no_emissions]

theorem lifted_public_history_equal (owner : Owner) (decode : List Nat → Nat)
    (r s : Carrier) (word : List Bool) (outputs : List Nat)
    (hr : r.owner=owner) (hs : s.owner=owner) (br : r.budget=1) (bs : s.budget=1)
    (same : r.counter=s.counter) :
    NativeObservedFutureRulesPrototype.mass (liftedRows (input owner))
      (fun r => decode (publicTuple (input owner) r)) r word outputs=
    NativeObservedFutureRulesPrototype.mass (liftedRows (input owner))
      (fun r => decode (publicTuple (input owner) r)) s word outputs := by
  rw [lifted_public_history_exact owner decode r word outputs hr br,
    lifted_public_history_exact owner decode s word outputs hs bs,same]

theorem lifted_branch_all_future (owner : Owner) (right : Bool) (s t : Kernel)
    (word : List Bool) (outputs : List Nat) :
    liftedMass (input owner) (branchObserve right) (initial (input owner) owner (embed s)) word outputs=
    liftedMass (input owner) (branchObserve right) (initial (input owner) owner (embed t)) word outputs := by
  rw [lifted_future_exact owner _ _ word outputs rfl rfl,
    lifted_future_exact owner _ _ word outputs rfl rfl]
  exact branch_all_future_equal owner right s t word outputs

theorem lifted_paired_strict (owner : Owner) :
    liftedMass (input owner) pairedObserve
      (initial (input owner) owner (embed (false,false))) [false] [0]=1 ∧
    liftedMass (input owner) pairedObserve
      (initial (input owner) owner (embed (false,true))) [false] [0]=3 := by
  rw [lifted_future_exact owner _ _ [false] [0] rfl rfl,
    lifted_future_exact owner _ _ [false] [0] rfl rfl]
  exact actual_paired_strict owner

theorem same_native_carrier_return (owner : Owner) :
    ClockClosed (input owner) owner ∧
    (∀ s n,∃ final,maintain (input owner) (initial (input owner) owner (embed s)) n=some final ∧
      final.owner=owner ∧ final.factor.1=false ∧ final.counter=n ∧ final.budget=1 ∧
      final.record.length=n+1) ∧
    (∀ observe r word outputs,r.owner=owner → r.budget=1 →
      liftedMass (input owner) observe r word outputs=outputMass (input owner) observe r.factor word outputs) ∧
    (∀ s t right word outputs,
      liftedMass (input owner) (branchObserve right) (initial (input owner) owner (embed s)) word outputs=
      liftedMass (input owner) (branchObserve right) (initial (input owner) owner (embed t)) word outputs) :=
  ⟨actual_clock_closed owner,unbounded_funded_carrier owner,lifted_future_exact owner,
    fun s t right => lifted_branch_all_future owner right s t⟩

-- Every accepted native outcome advances the carried clock, not only the head route.
theorem every_accepted_native_step (owner : Owner) (r : Carrier) (a : Bool)
    (o : Factor) (next : Carrier) (ho : r.owner=owner) (hb : r.budget=1)
    (accepted : step (input owner) r a o=some next) :
    next.owner=owner ∧ next.factor=o ∧ next.budget=1 ∧
    next.counter=r.counter+1 ∧ next.record=r.record++[o] ∧
    ∃ edge∈rows r.factor a,edge.1=o ∧ edge.2>0 := by
  obtain ⟨_,support,equal⟩ := (step_some_exact (input owner) r a o next).mp accepted
  subst next
  exact ⟨ho,rfl,actual_advance_budget owner r a o hb,rfl,rfl,support⟩

theorem every_safe_native_outcome_inside (s : Factor) (e : Factor × Nat)
    (inside : s.1=false) (supported : e∈rows s false) : e.1.1=false := by
  simp [rows,inside] at supported
  rcases supported with h | h | h | h <;> subst e <;> rfl

theorem zero_advance_counter (i : Input) (r : Carrier) (a : Bool) (o : Factor) :
    (advance (zeroTicks i) r a o).counter=r.counter := by simp [advance,zeroTicks]

theorem zero_maintenance_step (owner : Owner) (r : Carrier)
    (ho : r.owner=owner) (hb : r.budget=1) :
    maintenanceStep (zeroTicks (input owner)) r=
      some (advance (zeroTicks (input owner)) r false (nativeNext r.factor)) := by
  simp only [maintenanceStep]
  change ((rows r.factor false).head?).bind
    (fun e => step (zeroTicks (input owner)) r false e.1)=_
  rw [native_head]
  simp only [Option.bind_some,step]
  have hf : funded (zeroTicks (input owner)) r=true := actual_funded owner r ho hb
  rw [hf]
  change (if true && (rows r.factor false).any _ then _ else _)=_
  rw [native_first_supported r.factor]
  rfl

theorem zero_advance_budget (owner : Owner) (r : Carrier) (a : Bool) (o : Factor)
    (hb : r.budget=1) : (advance (zeroTicks (input owner)) r a o).budget=1 :=
  actual_advance_budget owner r a o hb

theorem funded_movement_without_tick (owner : Owner) (r : Carrier) (n : Nat)
    (ho : r.owner=owner) (hb : r.budget=1) :
    ∃ final,maintain (zeroTicks (input owner)) r n=some final ∧ final.owner=owner ∧
      final.budget=1 ∧ final.counter=r.counter ∧ final.record.length=r.record.length+n := by
  induction n generalizing r with
  | zero => exact ⟨r,rfl,ho,hb,rfl,by omega⟩
  | succ n ih =>
    obtain ⟨final,exec,own,budget,counter,len⟩ :=
      ih (advance (zeroTicks (input owner)) r false (nativeNext r.factor))
        (by rw [advance_owner,ho]) (zero_advance_budget owner r false _ hb)
    refine ⟨final,?_,own,budget,?_,?_⟩
    · simpa only [maintain,zero_maintenance_step owner r ho hb] using exec
    · simpa only [zero_advance_counter] using counter
    · rw [advance_record,List.length_append,List.length_singleton] at len
      omega

theorem zero_tick_not_funded_clock (owner : Owner) (r : Carrier) (n : Nat)
    (ho : r.owner=owner) (hb : r.budget=1) :
    (∃ final,maintain (zeroTicks (input owner)) r n=some final ∧ final.owner=owner ∧
      final.budget=1 ∧ final.counter=r.counter ∧ final.record.length=r.record.length+n) ∧
    ¬ClockClosed (zeroTicks (input owner)) owner :=
  ⟨funded_movement_without_tick owner r n ho hb,zero_tick_clock_false (input owner) owner⟩

def zeroTickAssignment : Assignment Owner MemoryValue :=
  fun owner => some (zeroTicks (input owner),input owner)

theorem concrete_zero_tick_readouts (owner : Owner) :
    readout (clockBit owner) owner false zeroTickAssignment=some false ∧
    readout (clockBit owner) owner true zeroTickAssignment=some true := by
  simp [readout,selected,zeroTickAssignment,MemoryFrames.selectInput,
    zero_tick_clock_bit,actual_clock_bit]

-- The original declared public tuple remains opaque at every carried tick.
theorem native_public_history_all_ticks (owner : Owner) (decode : List Nat → Nat)
    (r : Carrier) (word : List Bool) (outputs : List Nat)
    (ho : r.owner=owner) (hb : r.budget=1) :
    liftedMass (input owner) (fun s => decode (factorCurrent (input owner) s)) r word outputs=
      if outputs=List.replicate word.length (decode [0,1,1]) then 8^word.length else 0 := by
  rw [lifted_future_exact owner _ r word outputs ho hb]
  exact full_public_history_exact owner decode r.factor word outputs

theorem native_public_all_carrier_states (owner : Owner) (decode : List Nat → Nat)
    (r s : Carrier) (word : List Bool) (outputs : List Nat)
    (hr : r.owner=owner) (hs : s.owner=owner) (br : r.budget=1) (bs : s.budget=1) :
    liftedMass (input owner) (fun s => decode (factorCurrent (input owner) s)) r word outputs=
    liftedMass (input owner) (fun s => decode (factorCurrent (input owner) s)) s word outputs := by
  rw [native_public_history_all_ticks owner decode r word outputs hr br,
    native_public_history_all_ticks owner decode s word outputs hs bs]

-- Added clock exposure genuinely enlarges the interface: equal-phase coverage
-- above is not an unrestricted privacy claim for the expanded tuple.
theorem public_clock_exposure_separates_ticks (owner : Owner) :
    NativeObservedFutureRulesPrototype.mass (liftedRows (input owner))
      (fun r => (publicTuple (input owner) r).head!)
      (initial (input owner) owner (embed (false,false))) [false] [1]=8 ∧
    NativeObservedFutureRulesPrototype.mass (liftedRows (input owner))
      (fun r => (publicTuple (input owner) r).head!)
      (after owner (initial (input owner) owner (embed (false,false))) 1) [false] [1]=0 := by
  constructor
  · rw [lifted_public_history_exact owner (fun xs => xs.head!) _ [false] [1] rfl rfl]
    simp [publicHistory,initial,List.head!]
  · rw [lifted_public_history_exact owner (fun xs => xs.head!) _ [false] [1]
      (after_owner owner _ 1) (after_budget owner _ 1 rfl),after_counter]
    simp [publicHistory,initial,List.head!]

def Maintained (owner : Owner) (r : Carrier) : Prop :=
  r.owner=owner ∧ r.budget=1 ∧ r.factor.1=false

theorem initial_maintained (owner : Owner) (s : Kernel) :
    Maintained owner (initial (input owner) owner (embed s)) := ⟨rfl,rfl,rfl⟩

theorem every_maintenance_edge_preserves_carrier (owner : Owner) (r : Carrier)
    (hr : Maintained owner r) (edge : Carrier × Nat)
    (he : edge∈liftedRows (input owner) r false) :
    edge.2>0 ∧ Maintained owner edge.1 ∧ edge.1.counter=r.counter+1 ∧
      edge.1.record=r.record++[edge.1.factor] ∧
      step (input owner) r false edge.1.factor=some edge.1 := by
  rw [actual_lifted_rows owner r false hr.1 hr.2.1] at he
  obtain ⟨raw,member,equal⟩ := List.mem_map.mp he
  subst edge
  have pos := ((rows_positive_normalized r.factor false).1 raw member).1
  have inside := every_safe_native_outcome_inside r.factor raw hr.2.2 member
  refine ⟨pos,⟨hr.1,actual_advance_budget owner r false raw.1 hr.2.1,inside⟩,rfl,rfl,?_⟩
  apply (step_some_exact (input owner) r false raw.1 _).mpr
  exact ⟨⟨hr.1,by simpa only [hr.2.1] using Nat.le_refl 1⟩,⟨raw,member,rfl,pos⟩,rfl⟩

theorem maintained_carrier_has_actual_successor (owner : Owner) (r : Carrier)
    (hr : Maintained owner r) :
    ∃ next,maintenanceStep (input owner) r=some next ∧ Maintained owner next ∧
      next.counter=r.counter+1 ∧ next.record=r.record++[next.factor] := by
  refine ⟨advance (input owner) r false (nativeNext r.factor),
    actual_maintenance_step owner r hr.1 hr.2.1,
    ⟨hr.1,actual_advance_budget owner r false _ hr.2.1,native_next_inside r.factor hr.2.2⟩,rfl,rfl⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeCarrierClockPrototype

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeCarrierClockPrototype
open RegisterInterpreter CoupledNativeKernelPrototype
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

-- Positive-budget repair: every owned carrier admitted by funded is covered.
theorem positive_budget_funded (owner : Owner) (r : Carrier)
    (ho : r.owner=owner) (hb : 1≤r.budget) : funded (input owner) r=true := by
  simp only [funded,input,canonicalInput,factorData,ho,decide_eq_true_eq]
  exact ⟨True.intro,hb⟩

theorem positive_budget_preserved (owner : Owner) (r : Carrier) (a : Bool) (o : Factor)
    (hb : 1≤r.budget) : (advance (input owner) r a o).budget=r.budget := by
  change r.budget-1+1=r.budget
  omega

theorem positive_budget_lifted_rows (owner : Owner) (r : Carrier) (a : Bool)
    (ho : r.owner=owner) (hb : 1≤r.budget) :
    liftedRows (input owner) r a=(rows r.factor a).map
      (fun e => (advance (input owner) r a e.1,e.2)) := by
  simp only [liftedRows,positive_budget_funded owner r ho hb,ite_true,selected_rows]

theorem positive_budget_lifted_total (owner : Owner) (r : Carrier) (a : Bool)
    (ho : r.owner=owner) (hb : 1≤r.budget) :
    ((liftedRows (input owner) r a).map Prod.snd).sum=8 := by
  rw [positive_budget_lifted_rows owner r a ho hb]
  simpa only [List.map_map,Function.comp_def] using (rows_positive_normalized r.factor a).2

theorem positive_budget_lifted_projection (owner : Owner) (r : Carrier) (a : Bool)
    (ho : r.owner=owner) (hb : 1≤r.budget) :
    (liftedRows (input owner) r a).map (fun e => (e.1.factor,e.2))=rows r.factor a := by
  rw [positive_budget_lifted_rows owner r a ho hb]
  simp only [List.map_map,Function.comp_def,advance_factor]
  exact List.map_id _

theorem positive_budget_maintenance_step (owner : Owner) (r : Carrier)
    (ho : r.owner=owner) (hb : 1≤r.budget) :
    maintenanceStep (input owner) r=some (advance (input owner) r false (nativeNext r.factor)) := by
  simp only [maintenanceStep]
  change ((rows r.factor false).head?).bind (fun e => step (input owner) r false e.1)=_
  rw [native_head]
  simp only [Option.bind_some,step,positive_budget_funded owner r ho hb]
  change (if true && (rows r.factor false).any _ then _ else _)=_
  rw [native_first_supported r.factor]
  rfl

theorem positive_budget_after (owner : Owner) (r : Carrier) (n : Nat) (hb : 1≤r.budget) :
    (after owner r n).budget=r.budget := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [after,ih _ (by rw [positive_budget_preserved owner r false _ hb]; exact hb),
      positive_budget_preserved owner r false _ hb]

theorem positive_budget_maintain_exact (owner : Owner) (r : Carrier) (n : Nat)
    (ho : r.owner=owner) (hb : 1≤r.budget) :
    maintain (input owner) r n=some (after owner r n) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    simp only [maintain,positive_budget_maintenance_step owner r ho hb,after]
    exact ih _ (by rw [advance_owner,ho])
      (by rw [positive_budget_preserved owner r false _ hb]; exact hb)

theorem positive_budget_coherent_run (owner : Owner) (r : Carrier) (n : Nat)
    (ho : r.owner=owner) (hb : 1≤r.budget) :
    maintenanceStep (input owner) (after owner r n)=some (after owner r (n+1)) ∧
      (after owner r n).budget=r.budget ∧
      (after owner r n).counter<(after owner r (n+1)).counter ∧
      (after owner r (n+1)).record=(after owner r n).record++
        [(after owner r (n+1)).factor] := by
  refine ⟨?_,positive_budget_after owner r n hb,?_,?_⟩
  · rw [after_succ]
    exact positive_budget_maintenance_step owner _ ((after_owner owner r n).trans ho)
      (by rw [positive_budget_after owner r n hb]; exact hb)
  · rw [after_counter,after_counter]; omega
  · rw [after_succ,advance_record,advance_factor]

theorem positive_budget_future_exact (owner : Owner) (observe : Factor → Nat) (r : Carrier)
    (word : List Bool) (outputs : List Nat) (ho : r.owner=owner) (hb : 1≤r.budget) :
    liftedMass (input owner) observe r word outputs=
      outputMass (input owner) observe r.factor word outputs := by
  induction word generalizing r outputs with
  | nil => cases outputs <;> rfl
  | cons a rest ih =>
    cases outputs with
    | nil => rfl
    | cons obs tail =>
      simp only [liftedMass,NativeObservedFutureRulesPrototype.mass,outputMass,
        positive_budget_lifted_rows owner r a ho hb,List.foldr_map]
      apply congrArg (fun f => (rows r.factor a).foldr f 0)
      funext edge acc
      have hx := ih (advance (input owner) r a edge.1) tail
        (by rw [advance_owner,ho])
        (by rw [positive_budget_preserved owner r a edge.1 hb]; exact hb)
      simp only [liftedMass] at hx
      simp only [advance_factor,hx]

theorem positive_budget_native_public_history (owner : Owner) (decode : List Nat → Nat)
    (r : Carrier) (word : List Bool) (outputs : List Nat)
    (ho : r.owner=owner) (hb : 1≤r.budget) :
    liftedMass (input owner) (fun s => decode (factorCurrent (input owner) s)) r word outputs=
      if outputs=List.replicate word.length (decode [0,1,1]) then 8^word.length else 0 := by
  rw [positive_budget_future_exact owner _ r word outputs ho hb]
  exact full_public_history_exact owner decode r.factor word outputs

theorem positive_budget_native_public_all (owner : Owner) (decode : List Nat → Nat)
    (r s : Carrier) (word : List Bool) (outputs : List Nat)
    (hr : r.owner=owner) (hs : s.owner=owner) (br : 1≤r.budget) (bs : 1≤s.budget) :
    liftedMass (input owner) (fun s => decode (factorCurrent (input owner) s)) r word outputs=
    liftedMass (input owner) (fun s => decode (factorCurrent (input owner) s)) s word outputs := by
  rw [positive_budget_native_public_history owner decode r word outputs hr br,
    positive_budget_native_public_history owner decode s word outputs hs bs]

def budgetHistory (decode : List Nat → Nat) (budget : Nat) : Nat → Nat → List Nat
  | _,0 => []
  | counter,n+1 => decode [counter+1,budget,0,1,1]::budgetHistory decode budget (counter+1) n

theorem positive_budget_next_public_tuple (owner : Owner) (r : Carrier) (a : Bool) (o : Factor)
    (hb : 1≤r.budget) :
    publicTuple (input owner) (advance (input owner) r a o)=[r.counter+1,r.budget,0,1,1] := by
  simp only [publicTuple,actual_advance_counter,positive_budget_preserved owner r a o hb,
    factor_current_constant]
  rfl

theorem positive_budget_public_history_exact (owner : Owner) (decode : List Nat → Nat)
    (r : Carrier) (word : List Bool) (outputs : List Nat)
    (ho : r.owner=owner) (hb : 1≤r.budget) :
    NativeObservedFutureRulesPrototype.mass (liftedRows (input owner))
      (fun r => decode (publicTuple (input owner) r)) r word outputs=
      if outputs=budgetHistory decode r.budget r.counter word.length then 8^word.length else 0 := by
  induction word generalizing r outputs with
  | nil => cases outputs <;> simp [NativeObservedFutureRulesPrototype.mass,budgetHistory]
  | cons a rest ih =>
    cases outputs with
    | nil => simp [NativeObservedFutureRulesPrototype.mass,budgetHistory]
    | cons obs tail =>
      simp only [NativeObservedFutureRulesPrototype.mass,positive_budget_lifted_rows owner r a ho hb,
        List.foldr_map]
      have hx (edge : Factor × Nat) :
          NativeObservedFutureRulesPrototype.mass (liftedRows (input owner))
            (fun r => decode (publicTuple (input owner) r))
            (advance (input owner) r a edge.1) rest tail=
          if tail=budgetHistory decode r.budget (r.counter+1) rest.length then 8^rest.length else 0 := by
        rw [ih _ tail (by rw [advance_owner,ho])
          (by rw [positive_budget_preserved owner r a edge.1 hb]; exact hb)]
        rw [actual_advance_counter,positive_budget_preserved owner r a edge.1 hb]
      simp only [positive_budget_next_public_tuple owner r a _ hb,hx]
      by_cases first : decode [r.counter+1,r.budget,0,1,1]=obs
      · subst obs
        simp only [ite_true,NativeObservedFutureRulesPrototype.weighted_fold_constant,
          (rows_positive_normalized r.factor a).2]
        by_cases same : tail=budgetHistory decode r.budget (r.counter+1) rest.length
        · simp [same,budgetHistory,Nat.pow_succ,Nat.mul_comm]
        · simp [same,budgetHistory]
      · simp [first,budgetHistory,Ne.symm first,NativeObservedFutureRulesPrototype.foldr_no_emissions]

theorem positive_budget_public_history_equal (owner : Owner) (decode : List Nat → Nat)
    (r s : Carrier) (word : List Bool) (outputs : List Nat)
    (hr : r.owner=owner) (hs : s.owner=owner) (br : 1≤r.budget) (bs : 1≤s.budget)
    (clock : r.counter=s.counter) (budget : r.budget=s.budget) :
    NativeObservedFutureRulesPrototype.mass (liftedRows (input owner))
      (fun r => decode (publicTuple (input owner) r)) r word outputs=
    NativeObservedFutureRulesPrototype.mass (liftedRows (input owner))
      (fun r => decode (publicTuple (input owner) r)) s word outputs := by
  rw [positive_budget_public_history_exact owner decode r word outputs hr br,
    positive_budget_public_history_exact owner decode s word outputs hs bs,clock,budget]

def PositiveMaintained (owner : Owner) (r : Carrier) : Prop :=
  r.owner=owner ∧ 1≤r.budget ∧ r.factor.1=false

theorem all_positive_maintenance_edges (owner : Owner) (r : Carrier)
    (hr : PositiveMaintained owner r) (edge : Carrier × Nat)
    (he : edge∈liftedRows (input owner) r false) :
    edge.2>0 ∧ PositiveMaintained owner edge.1 ∧ edge.1.budget=r.budget ∧
      edge.1.counter=r.counter+1 ∧ edge.1.record=r.record++[edge.1.factor] ∧
      step (input owner) r false edge.1.factor=some edge.1 := by
  rw [positive_budget_lifted_rows owner r false hr.1 hr.2.1] at he
  obtain ⟨raw,member,equal⟩ := List.mem_map.mp he
  subst edge
  have pos := ((rows_positive_normalized r.factor false).1 raw member).1
  have inside := every_safe_native_outcome_inside r.factor raw hr.2.2 member
  have hb := positive_budget_preserved owner r false raw.1 hr.2.1
  refine ⟨pos,⟨hr.1,by rw [hb]; exact hr.2.1,inside⟩,hb,rfl,rfl,?_⟩
  apply (step_some_exact (input owner) r false raw.1 _).mpr
  exact ⟨⟨hr.1,hr.2.1⟩,⟨raw,member,rfl,pos⟩,rfl⟩

theorem every_funded_native_step (owner : Owner) (r : Carrier) (a : Bool)
    (o : Factor) (next : Carrier) (ho : r.owner=owner) (hb : 1≤r.budget)
    (accepted : step (input owner) r a o=some next) :
    next.owner=owner ∧ next.factor=o ∧ next.budget=r.budget ∧
    next.counter=r.counter+1 ∧ next.record=r.record++[o] ∧
    ∃ edge∈rows r.factor a,edge.1=o ∧ edge.2>0 := by
  obtain ⟨_,support,equal⟩ := (step_some_exact (input owner) r a o next).mp accepted
  subst next
  exact ⟨ho,rfl,positive_budget_preserved owner r a o hb,rfl,rfl,support⟩

theorem positive_budget_unbounded_return (owner : Owner) (r : Carrier) (n : Nat)
    (ho : r.owner=owner) (hb : 1≤r.budget) :
    maintain (input owner) r n=some (after owner r n) ∧
    (after owner r n).owner=owner ∧ (after owner r n).budget=r.budget ∧
    (after owner r n).counter=r.counter+n ∧
    (after owner r n).record.length=r.record.length+n :=
  ⟨positive_budget_maintain_exact owner r n ho hb,(after_owner owner r n).trans ho,
    positive_budget_after owner r n hb,after_counter owner r n,after_record_length owner r n⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeCarrierClockPrototype
