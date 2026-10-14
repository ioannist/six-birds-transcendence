import CSTTT.Targets.GenericHandoff.NativeComposition.CarrierClock

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeGeneratorCreditPrototype
open RegisterInterpreter CoupledNativeKernelPrototype NativeCarrierClockPrototype
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

inductive Credit where
  | self | other | neutral
  deriving DecidableEq, Repr

-- The unsupported dual-asymmetry case is absent, rather than self-credit.
def classify (sf sb ofwd ob : Rat) : Option Credit :=
  if sf ≠ sb then (if ofwd ≠ ob then none else some .self)
  else if ofwd ≠ ob then some .other else some .neutral

theorem dual_asymmetry_rejected (sf sb ofwd ob : Rat)
    (hs : sf ≠ sb) (ho : ofwd ≠ ob) : classify sf sb ofwd ob = none := by
  simp [classify,hs,ho]

-- Generator ownership is an additional declared RAW input. It is not deduced
-- from the resource-account owner and is never a supplied credit verdict.
def nativeCredit (owner : Owner) (issuer : Option Owner) (i : Input) : Option Credit :=
  issuer.bind fun origin =>
    if origin = owner then classify (forward i) (reverse i) 0 0
    else classify 0 0 (forward i) (reverse i)

theorem native_missing_issuer (owner : Owner) (i : Input) :
    nativeCredit owner none i = none := rfl

theorem native_credit_self_exact (owner : Owner) (issuer : Option Owner) (i : Input) :
    nativeCredit owner issuer i = some .self ↔
      issuer = some owner ∧ forward i ≠ reverse i := by
  cases issuer with
  | none => simp [nativeCredit]
  | some origin =>
    by_cases same : origin = owner
    · subst origin; simp [nativeCredit,classify]
    · by_cases equal : forward i = reverse i <;> simp [nativeCredit,classify,same,equal]

theorem native_credit_other_exact (owner : Owner) (issuer : Option Owner) (i : Input) :
    nativeCredit owner issuer i = some .other ↔
      ∃ origin,issuer = some origin ∧ origin ≠ owner ∧ forward i ≠ reverse i := by
  cases issuer with
  | none => simp [nativeCredit]
  | some origin =>
    by_cases same : origin = owner
    · subst origin
      by_cases equal : forward i = reverse i <;> simp [nativeCredit,classify,equal]
    · simp [nativeCredit,classify,same]

theorem native_credit_neutral_exact (owner : Owner) (issuer : Option Owner) (i : Input) :
    nativeCredit owner issuer i = some .neutral ↔
      issuer.isSome = true ∧ forward i = reverse i := by
  cases issuer with
  | none => simp [nativeCredit]
  | some origin =>
    by_cases same : origin = owner <;> simp [nativeCredit,classify,same]

theorem native_credit_none_exact (owner : Owner) (issuer : Option Owner) (i : Input) :
    nativeCredit owner issuer i = none ↔ issuer = none := by
  cases issuer with
  | none => simp [nativeCredit]
  | some origin =>
    by_cases same : origin = owner <;>
      by_cases equal : forward i = reverse i <;> simp [nativeCredit,classify,same,equal]

theorem actual_native_self_credit (owner : Owner) :
    nativeCredit owner (some owner) (input owner) = some .self :=
  (native_credit_self_exact owner _ _).mpr ⟨rfl,(actual_cycle_directionality owner).2.2⟩

theorem actual_native_other_credit (owner : Owner) :
    nativeCredit owner (some (swapOwner owner)) (input owner) = some .other := by
  apply (native_credit_other_exact owner _ _).mpr
  exact ⟨swapOwner owner,rfl,by cases owner <;> decide,(actual_cycle_directionality owner).2.2⟩

theorem flat_native_neutral_credit (owner : Owner) :
    nativeCredit owner (some owner) (flatten (input owner)) = some .neutral := by
  cases owner <;> decide +kernel

inductive Tri where
  | a | b | c
  deriving DecidableEq, Repr
def triStates : List Tri := [.a,.b,.c]
abbrev LiftState := Tri × Tri
def liftStates : List LiftState :=
  triStates.flatMap fun x => triStates.map fun phase => (x,phase)

-- Reversible lazy swaps; phase b activates (b,c), all other phases (a,b).
def phaseKernel (p : Rat) : Tri → Tri → Tri → Rat
  | .b,.a,.a => 1
  | .b,.b,.b | .b,.c,.c => 1-p
  | .b,.b,.c | .b,.c,.b => p
  | .a,.c,.c | .c,.c,.c => 1
  | .a,.a,.a | .a,.b,.b | .c,.a,.a | .c,.b,.b => 1-p
  | .a,.a,.b | .a,.b,.a | .c,.a,.b | .c,.b,.a => p
  | _,_,_ => 0

def clockChannel (s t : LiftState) : Rat := if s.1 = t.1 then 1/6 else 0
def contentChannel (p : Rat) (s t : LiftState) : Rat :=
  if s.2 = t.2 then phaseKernel p s.2 s.1 t.1 / 2 else 0
def liftP (p : Rat) (s t : LiftState) : Rat :=
  clockChannel s t + contentChannel p s t

theorem phase_kernel_symmetric (p : Rat) (phase x y : Tri) :
    phaseKernel p phase x y = phaseKernel p phase y x := by
  cases phase <;> cases x <;> cases y <;> rfl

theorem clock_channel_symmetric (s t : LiftState) : clockChannel s t = clockChannel t s := by
  simp only [clockChannel,eq_comm]

theorem content_channel_symmetric (p : Rat) (s t : LiftState) :
    contentChannel p s t = contentChannel p t s := by
  rcases s with ⟨x,phase⟩; rcases t with ⟨y,next⟩
  by_cases same : phase = next
  · subst next; simp only [contentChannel,ite_true]
    rw [phase_kernel_symmetric]
  · simp [contentChannel,same,Ne.symm same]

theorem lifted_decomposition (p : Rat) (s t : LiftState) :
    liftP p s t = clockChannel s t + contentChannel p s t := rfl

theorem lifted_symmetric (p : Rat) (s t : LiftState) : liftP p s t = liftP p t s := by
  simp only [liftP,clock_channel_symmetric s t,content_channel_symmetric p s t]

-- Exact integer/rational arithmetic for both source and native-derived biases.
def bias (i : Input) : Rat := P i (false,false) (false,true)
theorem actual_bias (owner : Owner) : bias (input owner) = 3/8 := by
  cases owner <;> decide +kernel

theorem source_lift_normalized (s : LiftState) :
    (liftStates.map (liftP (2/3) s)).sum = 1 := by
  rcases s with ⟨x,phase⟩; cases x <;> cases phase <;> decide +kernel
theorem source_lift_nonnegative (s t : LiftState) :
    0 ≤ clockChannel s t ∧ 0 ≤ contentChannel (2/3) s t ∧ 0 ≤ liftP (2/3) s t := by
  rcases s with ⟨x,phase⟩; rcases t with ⟨y,next⟩
  cases x <;> cases phase <;> cases y <;> cases next <;> decide +kernel
theorem native_lift_normalized (owner : Owner) (s : LiftState) :
    (liftStates.map (liftP (bias (input owner)) s)).sum = 1 := by
  rw [actual_bias]
  rcases s with ⟨x,phase⟩; cases x <;> cases phase <;> decide +kernel
theorem native_lift_nonnegative (owner : Owner) (s t : LiftState) :
    0 ≤ clockChannel s t ∧ 0 ≤ contentChannel (bias (input owner)) s t ∧
      0 ≤ liftP (bias (input owner)) s t := by
  rw [actual_bias]
  rcases s with ⟨x,phase⟩; rcases t with ⟨y,next⟩
  cases x <;> cases phase <;> cases y <;> cases next <;> decide +kernel

-- All finite paths, not a supplied cycle value or a finite-length test bound.
def edgeProduct {S : Type} (w : S → S → Rat) : List (S × S) → Rat
  | [] => 1
  | e::rest => w e.1 e.2 * edgeProduct w rest
def reversedEdges {S : Type} (edges : List (S × S)) : List (S × S) :=
  edges.reverse.map Prod.swap

theorem edge_product_append {S : Type} (w : S → S → Rat) (a b : List (S × S)) :
    edgeProduct w (a++b) = edgeProduct w a * edgeProduct w b := by
  induction a with
  | nil => simp [edgeProduct]
  | cons e rest ih => simp [edgeProduct,ih,Rat.mul_assoc]

theorem edge_product_reverse {S : Type} (w : S → S → Rat) (a : List (S × S)) :
    edgeProduct w a.reverse = edgeProduct w a := by
  induction a with
  | nil => rfl
  | cons e rest ih => simp [edgeProduct,List.reverse_cons,edge_product_append,ih,Rat.mul_comm]

theorem symmetric_all_path_products {S : Type} (w : S → S → Rat)
    (symmetric : ∀ s t,w s t = w t s) (edges : List (S × S)) :
    edgeProduct w edges = edgeProduct w (reversedEdges edges) := by
  unfold reversedEdges
  rw [List.map_reverse,edge_product_reverse]
  induction edges with
  | nil => rfl
  | cons e rest ih =>
    simp only [List.map_cons,edgeProduct,Prod.swap]
    rw [← symmetric,ih]

theorem internalized_all_path_products (p : Rat) (edges : List (LiftState × LiftState)) :
    edgeProduct clockChannel edges = edgeProduct clockChannel (reversedEdges edges) ∧
    edgeProduct (contentChannel p) edges = edgeProduct (contentChannel p) (reversedEdges edges) ∧
    edgeProduct (liftP p) edges = edgeProduct (liftP p) (reversedEdges edges) :=
  ⟨symmetric_all_path_products _ clock_channel_symmetric edges,
    symmetric_all_path_products _ (content_channel_symmetric p) edges,
    symmetric_all_path_products _ (lifted_symmetric p) edges⟩

-- Content/self and clock/other routing is declared before evaluating products.
def internalizedCredit (p : Rat) (edges : List (LiftState × LiftState)) : Option Credit :=
  classify (edgeProduct (contentChannel p) edges)
    (edgeProduct (contentChannel p) (reversedEdges edges))
    (edgeProduct clockChannel edges) (edgeProduct clockChannel (reversedEdges edges))

theorem internalized_credit_neutral_all_paths (p : Rat) (edges : List (LiftState × LiftState)) :
    internalizedCredit p edges = some .neutral := by
  have h := internalized_all_path_products p edges
  simp [internalizedCredit,classify,h.1,h.2.1]

def liftedCycle : List (LiftState × LiftState) :=
  [((.a,.a),(.b,.a)),((.b,.a),(.b,.c)),((.b,.c),(.a,.c)),((.a,.c),(.a,.a))]
theorem source_lift_cycle_exact :
    edgeProduct (liftP (2/3)) liftedCycle = 1/324 ∧
    edgeProduct (liftP (2/3)) (reversedEdges liftedCycle) = 1/324 ∧
    edgeProduct (contentChannel (2/3)) liftedCycle = 0 ∧
    edgeProduct clockChannel liftedCycle = 0 := by decide +kernel
theorem native_lift_cycle_exact (owner : Owner) :
    edgeProduct (liftP (bias (input owner))) liftedCycle = 1/1024 ∧
    edgeProduct (liftP (bias (input owner))) (reversedEdges liftedCycle) = 1/1024 := by
  rw [actual_bias]; decide +kernel

def scheduledP (p : Rat) (s t : Tri) : Rat :=
  (triStates.map fun mid => phaseKernel p .a s mid * phaseKernel p .b mid t).sum
def scheduleCycle : List (Tri × Tri) := [(.a,.b),(.b,.c),(.c,.a)]
-- This composed generator is scheduler-owned, even though its ingredients
-- are reversible. It has a real apparent arrow which is computed, not denied.
def scheduledCredit (p : Rat) : Option Credit :=
  classify 0 0 (edgeProduct (scheduledP p) scheduleCycle)
    (edgeProduct (scheduledP p) (reversedEdges scheduleCycle))

theorem source_scheduled_cycle_exact :
    edgeProduct (scheduledP (2/3)) scheduleCycle = 0 ∧
    edgeProduct (scheduledP (2/3)) (reversedEdges scheduleCycle) = 16/81 ∧
    scheduledCredit (2/3) = some .other := by decide +kernel
theorem native_scheduled_cycle_exact (owner : Owner) :
    edgeProduct (scheduledP (bias (input owner))) scheduleCycle = 0 ∧
    edgeProduct (scheduledP (bias (input owner))) (reversedEdges scheduleCycle) = 81/4096 ∧
    scheduledCredit (bias (input owner)) = some .other := by
  rw [actual_bias]; decide +kernel

def AuthoredClock (owner : Owner) (issuer : Option Owner) (i : Input) : Prop :=
  ClockClosed i owner ∧ nativeCredit owner issuer i = some .self
noncomputable def authoredClockBit (owner : Owner) (issuer : Option Owner) (i : Input) : Bool := by
  classical
  exact decide (AuthoredClock owner issuer i)

theorem authored_clock_actual (owner : Owner) :
    AuthoredClock owner (some owner) (input owner) :=
  ⟨actual_clock_closed owner,actual_native_self_credit owner⟩
theorem authored_clock_issuer_control (owner : Owner) :
    ClockClosed (input owner) owner ∧
    ¬ AuthoredClock owner (some (swapOwner owner)) (input owner) := by
  refine ⟨actual_clock_closed owner,?_⟩
  intro h
  have credited := h.2
  rw [actual_native_other_credit] at credited
  cases credited

theorem authored_clock_missing_control (owner : Owner) (i : Input) :
    ¬ AuthoredClock owner none i := by
  intro h; cases h.2

theorem authored_clock_actual_bit (owner : Owner) :
    authoredClockBit owner (some owner) (input owner) = true := by
  classical
  exact decide_eq_true (authored_clock_actual owner)
theorem authored_clock_other_bit (owner : Owner) :
    authoredClockBit owner (some (swapOwner owner)) (input owner) = false := by
  classical
  exact decide_eq_false (authored_clock_issuer_control owner).2

-- Missing issuer and missing consumed carrier both reject the actual readout.
noncomputable def authoredReadout (owner : Owner) (issuer : Option Owner)
    (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) : Option Bool :=
  issuer.bind fun _ => readout (authoredClockBit owner issuer) cell copy a

theorem authored_readout_true_exact (owner : Owner) (issuer : Option Owner)
    (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) :
    authoredReadout owner issuer cell copy a = some true ↔
      ∃ origin pair,issuer = some origin ∧ a cell = some pair ∧
        AuthoredClock owner issuer (MemoryFrames.selectInput copy pair) := by
  classical
  cases issuer with
  | none => simp [authoredReadout]
  | some origin => simp [authoredReadout,readout_some_exact,authoredClockBit]

theorem authored_readout_false_exact (owner : Owner) (issuer : Option Owner)
    (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) :
    authoredReadout owner issuer cell copy a = some false ↔
      ∃ origin pair,issuer = some origin ∧ a cell = some pair ∧
        ¬ AuthoredClock owner issuer (MemoryFrames.selectInput copy pair) := by
  classical
  cases issuer with
  | none => simp [authoredReadout]
  | some origin => simp [authoredReadout,readout_some_exact,authoredClockBit]

theorem authored_readout_none_exact (owner : Owner) (issuer : Option Owner)
    (cell : Owner) (copy : Bool) (a : Assignment Owner MemoryValue) :
    authoredReadout owner issuer cell copy a = none ↔ issuer = none ∨ a cell = none := by
  cases issuer <;> simp [authoredReadout,readout_none_exact]

theorem authored_copied_source_exact (owner : Owner) (issuer : Option Owner)
    (cell : Owner) (a : Assignment Owner MemoryValue) :
    authoredReadout owner issuer (swapOwner cell) true (memoryImage a) =
      authoredReadout owner issuer cell false a := by
  cases issuer with
  | none => rfl
  | some origin => exact copied_source_readout_exact _ a cell

theorem native_authored_audit_panel (owner : Owner) :
    nativeCredit owner (some owner) (input owner) = some .self ∧
    scheduledCredit (bias (input owner)) = some .other ∧
    (∀ edges, internalizedCredit (bias (input owner)) edges = some .neutral) ∧
    AuthoredClock owner (some owner) (input owner) :=
  ⟨actual_native_self_credit owner,(native_scheduled_cycle_exact owner).2.2,
    internalized_credit_neutral_all_paths _,authored_clock_actual owner⟩

theorem authored_positive_budget_return (owner : Owner)
    (r : NativeCarrierClockPrototype.Carrier) (n : Nat)
    (ho : r.owner = owner) (hb : 1 ≤ r.budget) :
    AuthoredClock owner (some owner) (input owner) ∧
    scheduledCredit (bias (input owner)) = some .other ∧
    (∀ edges,internalizedCredit (bias (input owner)) edges = some .neutral) ∧
    maintain (input owner) r n = some (after owner r n) ∧
    (after owner r n).owner = owner ∧ (after owner r n).budget = r.budget ∧
    (after owner r n).counter = r.counter+n ∧
    (after owner r n).record.length = r.record.length+n :=
  ⟨authored_clock_actual owner,(native_scheduled_cycle_exact owner).2.2,
    internalized_credit_neutral_all_paths _,positive_budget_unbounded_return owner r n ho hb⟩

theorem authored_other_readout_control (owner : Owner) :
    authoredReadout owner (some (swapOwner owner)) owner false assignment = some false := by
  simp only [authoredReadout,Option.bind_some,readout,selected,assignment,
    Option.map_some,MemoryFrames.selectInput]
  exact congrArg some (authored_clock_other_bit owner)

theorem authored_missing_readout_control (owner cell : Owner) (copy : Bool)
    (a : Assignment Owner MemoryValue) : authoredReadout owner none cell copy a = none := rfl

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeGeneratorCreditPrototype
