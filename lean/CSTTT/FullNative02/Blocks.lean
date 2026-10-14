import CSTTT.FullNative02.WarmupSupport

namespace CSTTT.FullNative02.Blocks
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

/-- The current immutable generator supplies both products. Receipt weights
are audited separately; they cannot supply a replacement reverse generator. -/
def edge (rom : ROM) (s t : State) : Rat :=
  ((rationalRows rom.program s false).map fun e => if e.1=t then e.2 else 0).sum

def forward {S R : Type} (weight : S → S → Rat) (before after : R → S) (rs : List R) : Rat :=
  (rs.map fun r => weight (before r) (after r)).foldr (·*·) 1

def backward {S R : Type} (weight : S → S → Rat) (before after : R → S) (rs : List R) : Rat :=
  (rs.map fun r => weight (after r) (before r)).foldr (·*·) 1

def directional {S R : Type} (weight : S → S → Rat) (before after : R → S) (rs : List R) : Bool :=
  decide (forward weight before after rs≠0 ∧ backward weight before after rs≠0 ∧
    forward weight before after rs≠backward weight before after rs)

theorem symmetric_products {S R : Type} (weight : S → S → Rat) (before after : R → S)
    (symmetry : ∀ s t, weight s t=weight t s) (rs : List R) :
    forward weight before after rs=backward weight before after rs := by
  unfold forward backward
  congr 1
  apply List.map_congr_left
  intro r _
  exact symmetry _ _

theorem symmetric_block_rejected {S R : Type} (weight : S → S → Rat) (before after : R → S)
    (symmetry : ∀ s t, weight s t=weight t s) (rs : List R) :
    directional weight before after rs=false := by
  simp [directional,symmetric_products weight before after symmetry rs]

def consecutive : List Receipt → Bool
  | [] => true
  | [_] => true
  | r::s::rest => decide (r.after=s.before) && consecutive (s::rest)

theorem detailed_balance_chain (weight : State → State → Rat) (measure : State → Rat)
    (balance : ∀ s t, measure s*weight s t=measure t*weight t s)
    (r : Receipt) (rest : List Receipt) (chain : consecutive (r::rest)=true) :
    measure r.before*forward weight Receipt.before Receipt.after (r::rest)=
      measure ((r::rest).getLast (by simp)).after*backward weight Receipt.before Receipt.after (r::rest) := by
  induction rest generalizing r with
  | nil => simpa [forward,backward,Rat.mul_one] using balance r.before r.after
  | cons s tail ih =>
    have pieces : decide (r.after=s.before)=true ∧ consecutive (s::tail)=true := by
      simpa only [consecutive,Bool.and_eq_true] using chain
    have adjacent : r.after=s.before := of_decide_eq_true pieces.1
    have remaining := pieces.2
    have transported := ih s remaining
    change measure r.before*(weight r.before r.after*forward weight Receipt.before Receipt.after (s::tail))=
      measure ((r::s::tail).getLast (by simp)).after*
        (weight r.after r.before*backward weight Receipt.before Receipt.after (s::tail))
    rw [←adjacent] at transported
    rw [←Rat.mul_assoc,balance,Rat.mul_assoc,
      Rat.mul_comm (weight r.after r.before),←Rat.mul_assoc,transported,Rat.mul_assoc,
      Rat.mul_comm (backward weight Receipt.before Receipt.after (s::tail))]
    rfl

theorem local_balance_chain (weight : State → State → Rat) (measure : State → Rat)
    (r : Receipt) (rest : List Receipt) (chain : consecutive (r::rest)=true)
    (balance : ∀ receipt∈r::rest,
      measure receipt.before*weight receipt.before receipt.after=
      measure receipt.after*weight receipt.after receipt.before) :
    measure r.before*forward weight Receipt.before Receipt.after (r::rest)=
      measure ((r::rest).getLast (by simp)).after*backward weight Receipt.before Receipt.after (r::rest) := by
  induction rest generalizing r with
  | nil => simpa [forward,backward,Rat.mul_one] using balance r (by simp)
  | cons s tail ih =>
    have pieces : decide (r.after=s.before)=true ∧ consecutive (s::tail)=true := by
      simpa only [consecutive,Bool.and_eq_true] using chain
    have adjacent : r.after=s.before := of_decide_eq_true pieces.1
    have transported := ih s pieces.2 (fun receipt member => balance receipt (List.mem_cons_of_mem _ member))
    change measure r.before*(weight r.before r.after*forward weight Receipt.before Receipt.after (s::tail))=
      measure ((r::s::tail).getLast (by simp)).after*
        (weight r.after r.before*backward weight Receipt.before Receipt.after (s::tail))
    rw [←adjacent] at transported
    rw [←Rat.mul_assoc,balance r (by simp),Rat.mul_assoc,
      Rat.mul_comm (weight r.after r.before),←Rat.mul_assoc,transported,Rat.mul_assoc,
      Rat.mul_comm (backward weight Receipt.before Receipt.after (s::tail))]
    rfl


def qualifies (rom : ROM) (owner : Nat) (rs : List Receipt) : Bool :=
  !rs.isEmpty && consecutive rs &&
    decide (rs.head?.map Receipt.before=rs.getLast?.map Receipt.after) &&
    rs.all (fun r => decide (r.owner=owner ∧ r.issuer=.local owner ∧ r.rom=rom ∧
      r.action=false ∧ (r.after,r.weight)∈rom.program.rows r.before false) && r.packet.isSome) &&
    directional (edge rom) Receipt.before Receipt.after rs

/-- Unequal products on an actual closed block obstruct detailed balance of
the immutable generator. This is a process law, not only a historical tag. -/
theorem qualifying_block_no_positive_detailed_balance (rom : ROM) (owner : Nat)
    (rs : List Receipt) (qualified : qualifies rom owner rs=true) :
    ¬∃ measure : State → Rat, (∀ s,measure s≠0) ∧
      ∀ s t,measure s*edge rom s t=measure t*edge rom t s := by
  intro reversible
  obtain ⟨measure,positive,balance⟩ := reversible
  cases rs with
  | nil => simp [qualifies] at qualified
  | cons r rest =>
    have pieces := qualified
    simp only [qualifies,List.isEmpty_cons,Bool.not_false,Bool.true_and,
      Bool.and_eq_true,decide_eq_true_eq,and_assoc] at pieces
    obtain ⟨chain,closed,_,products⟩ := pieces
    have loop : r.before=((r::rest).getLast (by simp)).after := by
      simpa only [List.head?_cons,List.getLast?_eq_some_getLast (l:=r::rest) (by simp),Option.map_some,
        Option.some.injEq] using closed
    have telescoped := detailed_balance_chain (edge rom) measure balance r rest chain
    rw [←loop] at telescoped
    have equal := congrArg (fun v => (measure r.before)⁻¹*v) telescoped
    simp only [←Rat.mul_assoc,Rat.inv_mul_cancel _ (positive _),Rat.one_mul] at equal
    simp [directional,equal] at products

/-- ALL contiguous blocks, including the empty candidate (which is rejected).
There is no preferred cycle length, supplied witness or sticky credit field. -/
def blocks (rs : List Receipt) : List (List Receipt) :=
  (List.range (rs.length+1)).flatMap fun start =>
    (List.range (rs.length-start+1)).map fun count => (rs.drop start).take count

def evidence (rom : ROM) (owner : Nat) (rs : List Receipt) : Bool :=
  (blocks rs).any (qualifies rom owner)

theorem qualifying_block_no_local_balance (rom : ROM) (owner : Nat) (r : Receipt)
    (rest : List Receipt) (qualified : qualifies rom owner (r::rest)=true)
    (measure : State → Rat) (positive : measure r.before≠0) :
    ¬(∀ receipt∈r::rest,measure receipt.before*edge rom receipt.before receipt.after=
      measure receipt.after*edge rom receipt.after receipt.before) := by
  intro balance
  have pieces := qualified
  simp only [qualifies,List.isEmpty_cons,Bool.not_false,Bool.true_and,
    Bool.and_eq_true,decide_eq_true_eq,and_assoc] at pieces
  obtain ⟨chain,closed,_,products⟩ := pieces
  have loop : r.before=((r::rest).getLast (by simp)).after := by
    simpa only [List.head?_cons,List.getLast?_eq_some_getLast (l:=r::rest) (by simp),
      Option.map_some,Option.some.injEq] using closed
  have telescoped := local_balance_chain (edge rom) measure r rest chain balance
  rw [←loop] at telescoped
  have equal := congrArg (fun v => (measure r.before)⁻¹*v) telescoped
  simp only [←Rat.mul_assoc,Rat.inv_mul_cancel _ positive,Rat.one_mul] at equal
  simp [directional,equal] at products

theorem evidence_no_positive_detailed_balance (rom : ROM) (owner : Nat)
    (rs : List Receipt) (h : evidence rom owner rs=true) :
    ¬∃ measure : State → Rat, (∀ s,measure s≠0) ∧
      ∀ s t,measure s*edge rom s t=measure t*edge rom t s := by
  obtain ⟨block,_,qualifying⟩ := List.any_eq_true.mp h
  exact qualifying_block_no_positive_detailed_balance rom owner block qualifying

theorem qualifying_block_current_generator (rom : ROM) (owner : Nat) (rs : List Receipt)
    (h : qualifies rom owner rs=true) :
    ¬(∀ s t, edge rom s t=edge rom t s) := by
  intro symmetry
  have rejected := symmetric_block_rejected (edge rom) Receipt.before Receipt.after symmetry rs
  simp [qualifies,rejected] at h

theorem evidence_current_generator (rom : ROM) (owner : Nat) (rs : List Receipt)
    (h : evidence rom owner rs=true) : ¬(∀ s t, edge rom s t=edge rom t s) := by
  obtain ⟨block,_,qualifying⟩ := List.any_eq_true.mp h
  exact qualifying_block_current_generator rom owner block qualifying

theorem empty_epoch_rejected (rom : ROM) (owner : Nat) : evidence rom owner []=false := by
  simp [evidence,blocks,qualifies,List.range]

theorem append_keeps_evidence (rom : ROM) (owner : Nat) (rs tail : List Receipt)
    (h : evidence rom owner rs=true) : evidence rom owner (rs++tail)=true := by
  obtain ⟨block,member,qualified⟩ := List.any_eq_true.mp h
  obtain ⟨start,hs,selected⟩ := List.mem_flatMap.mp member
  obtain ⟨count,hc,eq⟩ := List.mem_map.mp selected
  have startBound := List.mem_range.mp hs
  have countBound := List.mem_range.mp hc
  have inside : start+count≤rs.length := by omega
  have equalBlock : ((rs++tail).drop start).take count=(rs.drop start).take count := by
    rw [List.drop_append_of_le_length (by omega),List.take_append_of_le_length]
    simp only [List.length_drop]
    omega
  apply List.any_eq_true.mpr
  refine ⟨block,?_,qualified⟩
  apply List.mem_flatMap.mpr
  refine ⟨start,List.mem_range.mpr (by simp only [List.length_append]; omega),?_⟩
  apply List.mem_map.mpr
  refine ⟨count,List.mem_range.mpr (by simp only [List.length_append]; omega),?_⟩
  exact equalBlock.trans eq

end CSTTT.FullNative02.Blocks
