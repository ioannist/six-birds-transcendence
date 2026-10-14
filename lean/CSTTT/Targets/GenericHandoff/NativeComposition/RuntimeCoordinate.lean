import CSTTT.Targets.GenericHandoff.NativeComposition.GeneratorCredit

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeRuntimeCoordinatePrototype
open RegisterInterpreter CoupledNativeKernelPrototype NativeCarrierClockPrototype
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

structure Coordinate where
  owner : Owner
  factor : Factor
  counter : Nat
  budget : Nat
  deriving DecidableEq

def coordinate (r : NativeCarrierClockPrototype.Carrier) : Coordinate :=
  ⟨r.owner,r.factor,r.counter,r.budget⟩
def representative (q : Coordinate) : NativeCarrierClockPrototype.Carrier :=
  ⟨q.owner,q.factor,q.counter,q.budget,[]⟩
def coordinateAdvance (i : Input) (q : Coordinate) (a : Bool) (o : Factor) : Coordinate :=
  coordinate (advance i (representative q) a o)
def coordinateFunded (i : Input) (q : Coordinate) : Bool := funded i (representative q)
def coordinateRows (i : Input) (q : Coordinate) (a : Bool) : List (Coordinate × Nat) :=
  if coordinateFunded i q then
    (i.temporal.rows q.factor a).map fun edge => (coordinateAdvance i q a edge.1,edge.2)
  else []

theorem coordinate_representative (q : Coordinate) : coordinate (representative q) = q := by
  cases q; rfl
theorem coordinate_advance_exact (i : Input) (r : NativeCarrierClockPrototype.Carrier)
    (a : Bool) (o : Factor) :
    coordinate (advance i r a o) = coordinateAdvance i (coordinate r) a o := rfl
theorem coordinate_funded_exact (i : Input) (r : NativeCarrierClockPrototype.Carrier) :
    funded i r = coordinateFunded i (coordinate r) := rfl

theorem coordinate_rows_exact (i : Input) (r : NativeCarrierClockPrototype.Carrier) (a : Bool) :
    (liftedRows i r a).map (fun edge => (coordinate edge.1,edge.2)) =
      coordinateRows i (coordinate r) a := by
  unfold liftedRows coordinateRows
  rw [coordinate_funded_exact]
  by_cases h : coordinateFunded i (coordinate r)
  · simp only [h,ite_true,List.map_map]
    rfl
  · simp [h]

theorem coordinate_mass_exact (i : Input) (observe : Coordinate → Nat)
    (r : NativeCarrierClockPrototype.Carrier) (word : List Bool) (outputs : List Nat) :
    NativeObservedFutureRulesPrototype.mass (liftedRows i) (fun r => observe (coordinate r)) r word outputs =
      NativeObservedFutureRulesPrototype.mass (coordinateRows i) observe (coordinate r) word outputs := by
  induction word generalizing r outputs with
  | nil => cases outputs <;> rfl
  | cons a rest ih =>
    cases outputs with
    | nil => rfl
    | cons obs tail =>
      simp only [NativeObservedFutureRulesPrototype.mass]
      rw [← coordinate_rows_exact i r a,List.foldr_map]
      simp only [ih]

theorem coordinate_equality_future (i : Input) (r s : NativeCarrierClockPrototype.Carrier)
    (same : coordinate r = coordinate s) (observe : Coordinate → Nat)
    (word : List Bool) (outputs : List Nat) :
    NativeObservedFutureRulesPrototype.mass (liftedRows i) (fun r => observe (coordinate r)) r word outputs =
      NativeObservedFutureRulesPrototype.mass (liftedRows i) (fun r => observe (coordinate r)) s word outputs := by
  rw [coordinate_mass_exact,coordinate_mass_exact,same]

theorem coordinate_eq_exact (r s : NativeCarrierClockPrototype.Carrier) :
    coordinate r = coordinate s ↔
      r.owner = s.owner ∧ r.factor = s.factor ∧ r.counter = s.counter ∧ r.budget = s.budget := by
  cases r; cases s; simp [coordinate]

def probeCoordinate (owner : Owner) (r : NativeCarrierClockPrototype.Carrier) : Coordinate :=
  coordinate (advance (input owner) r true (outside r.factor.2))
theorem actual_probe_row (owner : Owner) (r : NativeCarrierClockPrototype.Carrier)
    (ho : r.owner = owner) (hb : 1 ≤ r.budget) (hi : r.factor.1 = false) :
    liftedRows (input owner) r true = [(advance (input owner) r true (outside r.factor.2),8)] := by
  rw [positive_budget_lifted_rows owner r true ho hb]
  simp [rows,hi]
theorem actual_coordinate_probe_row (owner : Owner) (r : NativeCarrierClockPrototype.Carrier)
    (ho : r.owner = owner) (hb : 1 ≤ r.budget) (hi : r.factor.1 = false) :
    coordinateRows (input owner) (coordinate r) true = [(probeCoordinate owner r,8)] := by
  rw [← coordinate_rows_exact,actual_probe_row owner r ho hb hi]
  rfl

theorem actual_probe_mass (owner : Owner) (r : NativeCarrierClockPrototype.Carrier)
    (ho : r.owner = owner) (hb : 1 ≤ r.budget) (hi : r.factor.1 = false)
    (observe : Coordinate → Nat) (obs : Nat) :
    NativeObservedFutureRulesPrototype.mass (liftedRows (input owner))
      (fun r => observe (coordinate r)) r [true] [obs] =
        if observe (probeCoordinate owner r) = obs then 8 else 0 := by
  simp only [NativeObservedFutureRulesPrototype.mass,actual_probe_row owner r ho hb hi,
    List.foldr_cons,List.foldr_nil,probeCoordinate]
  simp

theorem probe_coordinate_injective (owner : Owner) (r s : NativeCarrierClockPrototype.Carrier)
    (hr : r.owner = owner) (hs : s.owner = owner)
    (br : 1 ≤ r.budget) (bs : 1 ≤ s.budget)
    (ir : r.factor.1 = false) (is : s.factor.1 = false) :
    probeCoordinate owner r = probeCoordinate owner s ↔ coordinate r = coordinate s := by
  constructor
  · intro same
    have factor : r.factor.2 = s.factor.2 := congrArg (fun q => q.factor.2) same
    have counter : r.counter+1 = s.counter+1 := congrArg Coordinate.counter same
    have budget : r.budget = s.budget := by
      have b := congrArg Coordinate.budget same
      simpa only [probeCoordinate,coordinate,
        positive_budget_preserved owner r true _ br,positive_budget_preserved owner s true _ bs] using b
    apply (coordinate_eq_exact r s).mpr
    refine ⟨hr.trans hs.symm,?_,by omega,budget⟩
    exact Prod.ext (ir.trans is.symm) factor
  · intro same
    obtain ⟨_,factor,_,_⟩ := (coordinate_eq_exact r s).mp same
    simp only [probeCoordinate,coordinate_advance_exact,factor,same]

-- Internal self-lens is distinct from the declared external exposure tuple.
def selfLens (r : NativeCarrierClockPrototype.Carrier) : Nat × Nat := (r.counter,r.budget)
def firstProfile (i : Input) (r : NativeCarrierClockPrototype.Carrier) :=
  (selfLens r,coordinateRows i (coordinate r) true)

theorem first_profile_exact (owner : Owner) (r s : NativeCarrierClockPrototype.Carrier)
    (hr : r.owner = owner) (hs : s.owner = owner)
    (br : 1 ≤ r.budget) (bs : 1 ≤ s.budget)
    (ir : r.factor.1 = false) (is : s.factor.1 = false) :
    firstProfile (input owner) r = firstProfile (input owner) s ↔ coordinate r = coordinate s := by
  constructor
  · intro same
    have h := congrArg Prod.snd same
    simp only [firstProfile,actual_coordinate_probe_row owner r hr br ir,
      actual_coordinate_probe_row owner s hs bs is,List.cons.injEq] at h
    exact (probe_coordinate_injective owner r s hr hs br bs ir is).mp (congrArg Prod.fst h.1)
  · intro same
    have h := (coordinate_eq_exact r s).mp same
    simp only [firstProfile,selfLens,h.2.2.1,h.2.2.2,same]

def fullFutureEquivalent (i : Input) (r s : NativeCarrierClockPrototype.Carrier) : Prop :=
  ∀ (observe : Coordinate → Nat) (word : List Bool) (outputs : List Nat),
    NativeObservedFutureRulesPrototype.mass (liftedRows i) (fun r => observe (coordinate r)) r word outputs =
      NativeObservedFutureRulesPrototype.mass (liftedRows i) (fun r => observe (coordinate r)) s word outputs

theorem full_runtime_future_exact (owner : Owner) (r s : NativeCarrierClockPrototype.Carrier)
    (hr : r.owner = owner) (hs : s.owner = owner)
    (br : 1 ≤ r.budget) (bs : 1 ≤ s.budget)
    (ir : r.factor.1 = false) (is : s.factor.1 = false) :
    fullFutureEquivalent (input owner) r s ↔ coordinate r = coordinate s := by
  constructor
  · intro laws
    by_cases same : probeCoordinate owner r = probeCoordinate owner s
    · exact (probe_coordinate_injective owner r s hr hs br bs ir is).mp same
    · let observe : Coordinate → Nat := fun q => if q = probeCoordinate owner r then 1 else 0
      have h := laws observe [true] [1]
      rw [actual_probe_mass owner r hr br ir,actual_probe_mass owner s hs bs is] at h
      simp [observe,Ne.symm same] at h
  · intro same observe word outputs
    exact coordinate_equality_future _ r s same observe word outputs

theorem predictive_profile_full_future (owner : Owner) (r s : NativeCarrierClockPrototype.Carrier)
    (hr : r.owner = owner) (hs : s.owner = owner)
    (br : 1 ≤ r.budget) (bs : 1 ≤ s.budget)
    (ir : r.factor.1 = false) (is : s.factor.1 = false) :
    firstProfile (input owner) r = firstProfile (input owner) s ↔
      fullFutureEquivalent (input owner) r s := by
  rw [first_profile_exact owner r s hr hs br bs ir is,full_runtime_future_exact owner r s hr hs br bs ir is]

-- Recursive successor profile computed through the actual descended rows.
def secondProfile (i : Input) (r : NativeCarrierClockPrototype.Carrier) :=
  (firstProfile i r,
    (coordinateRows i (coordinate r) false).map fun edge =>
      (firstProfile i (representative edge.1),edge.2),
    (coordinateRows i (coordinate r) true).map fun edge =>
      (firstProfile i (representative edge.1),edge.2))

theorem recursive_profile_stable (owner : Owner) (r s : NativeCarrierClockPrototype.Carrier)
    (hr : r.owner = owner) (hs : s.owner = owner)
    (br : 1 ≤ r.budget) (bs : 1 ≤ s.budget)
    (ir : r.factor.1 = false) (is : s.factor.1 = false) :
    secondProfile (input owner) r = secondProfile (input owner) s ↔
      firstProfile (input owner) r = firstProfile (input owner) s := by
  constructor
  · intro same; exact congrArg Prod.fst same
  · intro same
    have co := (first_profile_exact owner r s hr hs br bs ir is).mp same
    simp only [secondProfile,same,co]

-- Actual recursive signatures retain both action rows and their successor
-- signatures; the complete profile is computed rather than supplied.
inductive ProfileTree where
  | seed (lens : Nat × Nat)
  | refine (previous : ProfileTree)
      (safe probe : List (Coordinate × Nat × ProfileTree))

def treeProfile (i : Input) : Nat → NativeCarrierClockPrototype.Carrier → ProfileTree
  | 0,r => .seed (selfLens r)
  | n+1,r => .refine (treeProfile i n r)
      ((coordinateRows i (coordinate r) false).map fun e =>
        (e.1,e.2,treeProfile i n (representative e.1)))
      ((coordinateRows i (coordinate r) true).map fun e =>
        (e.1,e.2,treeProfile i n (representative e.1)))

def treeProbeRows : ProfileTree → List (Coordinate × Nat)
  | .seed _ => []
  | .refine _ _ probe => probe.map fun e => (e.1,e.2.1)

theorem tree_profile_probe_rows (i : Input) (n : Nat) (r : NativeCarrierClockPrototype.Carrier) :
    treeProbeRows (treeProfile i (n+1) r) = coordinateRows i (coordinate r) true := by
  simp [treeProfile,treeProbeRows,List.map_map,Function.comp_def]

theorem tree_coordinate_dependence (i : Input) (n : Nat)
    (r s : NativeCarrierClockPrototype.Carrier) (same : coordinate r = coordinate s) :
    treeProfile i n r = treeProfile i n s := by
  induction n generalizing r s with
  | zero =>
    have h := (coordinate_eq_exact r s).mp same
    simp only [treeProfile,selfLens,h.2.2.1,h.2.2.2]
  | succ n ih =>
    simp only [treeProfile,ih r s same,same]

theorem tree_terminal_exact (owner : Owner) (n : Nat) (r s : NativeCarrierClockPrototype.Carrier)
    (hr : r.owner = owner) (hs : s.owner = owner)
    (br : 1 ≤ r.budget) (bs : 1 ≤ s.budget)
    (ir : r.factor.1 = false) (is : s.factor.1 = false) :
    treeProfile (input owner) (n+1) r = treeProfile (input owner) (n+1) s ↔
      coordinate r = coordinate s := by
  constructor
  · intro same
    have rows := congrArg treeProbeRows same
    rw [tree_profile_probe_rows,tree_profile_probe_rows,
      actual_coordinate_probe_row owner r hr br ir,actual_coordinate_probe_row owner s hs bs is] at rows
    have probe := congrArg (fun row => row.head?) rows
    have pair : (probeCoordinate owner r,8) = (probeCoordinate owner s,8) := Option.some.inj probe
    exact (probe_coordinate_injective owner r s hr hs br bs ir is).mp (congrArg Prod.fst pair)
  · intro same; exact tree_coordinate_dependence _ (n+1) r s same

theorem runtime_profile_stable_forever (owner : Owner) (n : Nat) (r s : NativeCarrierClockPrototype.Carrier)
    (hr : r.owner = owner) (hs : s.owner = owner)
    (br : 1 ≤ r.budget) (bs : 1 ≤ s.budget)
    (ir : r.factor.1 = false) (is : s.factor.1 = false) :
    treeProfile (input owner) (n+1) r = treeProfile (input owner) (n+1) s ↔
      fullFutureEquivalent (input owner) r s := by
  rw [tree_terminal_exact owner n r s hr hs br bs ir is,
    full_runtime_future_exact owner r s hr hs br bs ir is]

theorem stored_record_quotient (i : Input) (r : NativeCarrierClockPrototype.Carrier)
    (record : List Factor) (observe : Coordinate → Nat) (word : List Bool) (outputs : List Nat) :
    NativeObservedFutureRulesPrototype.mass (liftedRows i) (fun r => observe (coordinate r))
      {r with record := record} word outputs =
    NativeObservedFutureRulesPrototype.mass (liftedRows i) (fun r => observe (coordinate r)) r word outputs :=
  coordinate_equality_future i {r with record := record} r rfl observe word outputs

theorem different_clock_is_predictively_different (owner : Owner) (r s : NativeCarrierClockPrototype.Carrier)
    (hr : r.owner = owner) (hs : s.owner = owner)
    (br : 1 ≤ r.budget) (bs : 1 ≤ s.budget)
    (ir : r.factor.1 = false) (is : s.factor.1 = false) (different : r.counter ≠ s.counter) :
    ¬ fullFutureEquivalent (input owner) r s := by
  intro same
  have co := (full_runtime_future_exact owner r s hr hs br bs ir is).mp same
  exact different (congrArg Coordinate.counter co)

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeRuntimeCoordinatePrototype
