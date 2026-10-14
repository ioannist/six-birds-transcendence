import CSTTT.FullNative02.Runtime

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 8000000

/-- Indices retain the identity of each row entry, even if an installed ROM
ever has coincident outcomes. They are computed by zipIdx, not request data. -/
structure Edge where
  state : State
  weight : Nat
  index : Nat
  deriving DecidableEq, Repr

def edges (rom : ROM) (s : State) (a : Bool) : List Edge :=
  (rom.program.rows s a).zipIdx.map fun e => ⟨e.1.1,e.1.2,e.2⟩

abbrev Pair := Edge × Edge
def meeting (rom : ROM) (s t : State) (a b : Bool) : List Pair :=
  (edges rom s a).flatMap fun l =>
    ((edges rom t b).filter fun r => decide (l.state=r.state)).map fun r => (l,r)

def pairWeight (p : Pair) : Nat := p.1.weight*p.2.weight
def meetingMass (rom : ROM) (s t : State) (a b : Bool) : Nat :=
  ((meeting rom s t a b).map pairWeight).sum
def pairProbability (rom : ROM) (s t : State) (a b : Bool) (p : Pair) : Rat :=
  (pairWeight p : Rat)/(meetingMass rom s t a b : Rat)

theorem edge_support (rom : ROM) (s : State) (a : Bool) (e : Edge)
    (h : e∈edges rom s a) : (e.state,e.weight)∈rom.program.rows s a ∧ 0<e.weight := by
  obtain ⟨entry,hm,he⟩ := List.mem_map.mp h
  have hw := List.mem_of_getElem? (List.mk_mem_zipIdx_iff_getElem?.mp hm)
  cases he
  exact ⟨hw,(rom_rows_positive_normalized rom s a).1 _ hw⟩

theorem edge_identity (rom : ROM) (s : State) (a : Bool) (e : Edge)
    (h : e∈edges rom s a) : (rom.program.rows s a)[e.index]?=some (e.state,e.weight) := by
  obtain ⟨entry,hm,he⟩ := List.mem_map.mp h
  cases he
  exact List.mk_mem_zipIdx_iff_getElem?.mp hm

theorem meeting_support (rom : ROM) (s t : State) (a b : Bool) (p : Pair)
    (h : p∈meeting rom s t a b) :
    p.1∈edges rom s a ∧ p.2∈edges rom t b ∧ p.1.state=p.2.state := by
  obtain ⟨l,hl,hm⟩ := List.mem_flatMap.mp h
  obtain ⟨r,hr,he⟩ := List.mem_map.mp hm
  cases he
  exact ⟨hl,(List.mem_filter.mp hr).1,of_decide_eq_true (List.mem_filter.mp hr).2⟩

theorem meeting_weight_positive (rom : ROM) (s t : State) (a b : Bool) (p : Pair)
    (h : p∈meeting rom s t a b) : 0<pairWeight p := by
  have hs := meeting_support rom s t a b p h
  exact Nat.mul_pos (edge_support rom s a p.1 hs.1).2 (edge_support rom t b p.2 hs.2.1).2

theorem divided_mass (weights : List Nat) (denominator : Nat) :
    (weights.map (fun (n : Nat) => (n : Rat)/(denominator : Rat))).sum =
    ((weights.sum : Nat) : Rat)/(denominator : Rat) := by
  induction weights with
  | nil => simp [Rat.div_def,Rat.zero_mul]
  | cons n rest ih =>
    rw [List.map_cons,List.sum_cons,ih,List.sum_cons]
    simp only [Rat.natCast_add,Rat.div_def,Rat.add_mul]

theorem meeting_normalized (rom : ROM) (s t : State) (a b : Bool)
    (h : meetingMass rom s t a b≠0) :
    ((meeting rom s t a b).map (pairProbability rom s t a b)).sum=1 := by
  have hc : (meetingMass rom s t a b : Rat)≠0 := by
    intro hz
    exact h (Rat.natCast_eq_zero_iff.mp hz)
  have hs := divided_mass ((meeting rom s t a b).map pairWeight) (meetingMass rom s t a b)
  have total : ((meeting rom s t a b).map (pairProbability rom s t a b)).sum =
      (meetingMass rom s t a b : Rat)/(meetingMass rom s t a b : Rat) := by
    simpa only [List.map_map,Function.comp_def,pairProbability,meetingMass] using hs
  rw [total,Rat.div_def]
  exact Rat.mul_inv_cancel _ hc

theorem supported_probability_positive (rom : ROM) (s t : State) (a b : Bool)
    (p : Pair) (member : p∈meeting rom s t a b) (positive : 0<meetingMass rom s t a b) :
    0<pairProbability rom s t a b p := by
  rw [pairProbability,Rat.div_def]
  exact Rat.mul_pos (Rat.natCast_pos.mpr (meeting_weight_positive rom s t a b p member))
    (Rat.inv_pos.mpr (Rat.natCast_pos.mpr positive))

/-- Empty is ALL-outcome incompatibility, not the failure of a selected pair. -/
theorem zero_meeting_has_no_pair (rom : ROM) (s t : State) (a b : Bool)
    (h : meetingMass rom s t a b=0) : meeting rom s t a b=[] := by
  cases hm : meeting rom s t a b with
  | nil => rfl
  | cons p rest =>
    have hp := meeting_weight_positive rom s t a b p (by simp [hm])
    have hz := h
    simp only [meetingMass,hm,List.map_cons,List.sum_cons] at hz
    omega

def phaseState (phase : Bool) : State := ⟨false,false,false,false,phase⟩

theorem phase_opposed_empty (rom : ROM) :
    meeting rom (phaseState false) (phaseState true) false false=[] := by
  cases rom <;> decide +kernel

theorem maintenance_probe_empty (rom : ROM) (phase : Bool) :
    meeting rom (phaseState phase) (phaseState phase) false true=[] := by
  cases rom <;> cases phase <;> decide +kernel

theorem maintained_meeting_positive (rom : ROM) :
    0<meetingMass rom (phaseState false) (phaseState false) false false := by
  cases rom <;> decide +kernel

end CSTTT.FullNative02
