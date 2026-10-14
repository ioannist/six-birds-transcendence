import CSTTT.POS04.Assembly
import CSTTT.Package.FiniteGluing

/-!
TTN-08 designed cyclic `ClauseSpec` gluing control. POS-04's eight L8-grade
clause predicates are side conditions; its positive `PackagePass` is unchanged.
The 160 L5 coordinates enumerate `(tag,state,clause)` slots but have no
assignment value or assignment-sensitive acceptance function. `PackagePass`
checks model data, not a supplied local `GlobalAssignment`. Thus this theorem
does not prove a local/global obstruction under POS-04's own acceptance
semantics. A compatible running-intersection cover glues by TTH-01. The
declared control adds
a shared diagonal coordinate to nonconsecutive C1 and C5 slots of an
otherwise ordinary eight-clause cycle. All edge values come from the first
state of POS-04's raw hidden pair; C5's diagonal comes from its second state.
No acceptance or failure verdict is stored. The diagonal violates running
intersection, so edge compatibility does not force global agreement.
-- FOLLOW-UP: introduce assignment-indexed C1–C8 checks over raw local values
-- and prove their equivalence to the POS-04 package predicates before claiming
-- an actual POS-04 eight-clause gluing obstruction.
-/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit
abbrev CycleNode := Fin 8

inductive CycleCoord where
  | edge (index : Fin 8) | diagonal
  deriving DecidableEq, Repr

private def cycleNodeEnum : CSTTT.FiniteEnum CycleNode :=
  ⟨List.finRange 8, by intro n; exact List.mem_finRange n⟩
private def cycleCoordEnum : CSTTT.FiniteEnum CycleCoord :=
  ⟨(List.finRange 8).map CycleCoord.edge ++ [.diagonal], by
    intro c
    cases c with
    | edge k => simp [List.mem_append, List.mem_map, List.mem_finRange]
    | diagonal => simp⟩
private def cycleStateEnum : CSTTT.FiniteEnum KState :=
  ⟨kernel, by intro s; cases s <;> simp [kernel]⟩

abbrev cycleAlphabet : CSTTT.PackageAlphabet :=
  { Coord := CycleCoord, Value := KState,
    coordEnum := cycleCoordEnum, valueEnum := cycleStateEnum }

/-- Exactly the eight typed clause slots represented in POS-04. -/
def cycleClause : CycleNode → CSTTT.ClauseId
  | 0 => .c1Objecthood
  | 1 => .c2StrictPromotion
  | 2 => .c3ReflexiveSelfCoordinate
  | 3 => .c4InterfaceNonexposure
  | 4 => .c5ActionCredit
  | 5 => .c6TemporalClosure
  | 6 => .c7BindingRecombination
  | _ => .c8ViabilityRepair

theorem cycle_clause_coverage (id : CSTTT.ClauseId) :
    ∃ n : CycleNode, cycleClause n = id := by
  cases id with
  | c1Objecthood => exact ⟨0,rfl⟩
  | c2StrictPromotion => exact ⟨1,rfl⟩
  | c3ReflexiveSelfCoordinate => exact ⟨2,rfl⟩
  | c4InterfaceNonexposure => exact ⟨3,rfl⟩
  | c5ActionCredit => exact ⟨4,rfl⟩
  | c6TemporalClosure => exact ⟨5,rfl⟩
  | c7BindingRecombination => exact ⟨6,rfl⟩
  | c8ViabilityRepair => exact ⟨7,rfl⟩

/-- The edge coordinate indexed by k is shared by k and its successor. -/
def cycleScope (n : CycleNode) : List CycleCoord :=
  [.edge n, .edge ⟨(n.val + 7) % 8, by omega⟩] ++
    (if n = 0 || n = 4 then [.diagonal] else [])

abbrev cycleAdjacent (n m : CycleNode) : Prop :=
  (n.val + 1) % 8 = m.val ∨ (m.val + 1) % 8 = n.val

/-- The sole non-default value is derived from the second raw hidden state. -/
def cycleValue (n : CycleNode) (c : CycleCoord) : KState :=
  if n = 4 && c = .diagonal then hiddenPair.2 else hiddenPair.1

def cycleLocal (n : CycleNode) : CSTTT.GlobalAssignment cycleAlphabet :=
  fun c => if (cycleScope n).contains c then some (cycleValue n c) else none

/-- These are the computed predicates used by `PackagePass`, but they do not
inspect a `GlobalAssignment`. They serve only as POS-04 pass side conditions.
C4–C7 retain their declared surrogate ceilings. -/
def cyclePOS04ClausePass : CycleNode → Prop
  | 0 => C1FactorPass .target
  | 1 => C2Pass .position .target
  | 2 => C3Pass .positive .position .target
  | 3 => C4Surrogate .positive .target
  | 4 => C5Surrogate .positive .target
  | 5 => C6Pass .positive .target
  | 6 => C7Pass .positive .target
  | _ => C8Pass .funded .target

/-- This is a *designed* assignment-sensitive `ClauseSpec`: its equality rule
is new to the cyclic control, while `cyclePOS04ClausePass` is a side condition
independent of the supplied assignment. The gate requires each scoped
coordinate to be present. The generic `essentialResources` list is unused by
this gluing check; C8 resource and ledger requirements are checked only by
the POS-04 side condition `C8Pass`. -/
def cycleSpec (n : CycleNode) : CSTTT.ClauseSpec (cycleClause n) cycleAlphabet :=
  { scope := cycleScope n
    accepts := fun a => cyclePOS04ClausePass n ∧
      ∀ c, c ∈ cycleScope n → a c = some (cycleValue n c)
    hardGate := fun a => ∀ c, c ∈ cycleScope n → a c ≠ none
    essentialResources := [] }

def cycleWitness (n : CycleNode) (h : cyclePOS04ClausePass n) :
    CSTTT.ClauseWitness (cycleClause n) cycleAlphabet (cycleSpec n) := by
  refine ⟨cycleLocal n, ⟨h, ?_⟩, ?_⟩
  · intro c hc
    simp [cycleLocal, hc]
  · intro c hc
    simp [cycleLocal, hc]

/-- The positive eight-clause package supplies every POS-04 side condition. -/
theorem cycle_all_clause_pass : ∀ n : CycleNode, cyclePOS04ClausePass n := by
  intro n
  have h := package_funded_each_tag .target
  rcases h with ⟨_, hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8⟩
  have allcases : ∀ n : CycleNode,
      n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨
      n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by decide
  have cases := allcases n
  rcases cases with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7
  · simpa [h0, cyclePOS04ClausePass] using hc1
  · simpa [h1, cyclePOS04ClausePass] using hc2
  · simpa [h2, cyclePOS04ClausePass] using hc3
  · simpa [h3, cyclePOS04ClausePass] using hc4
  · simpa [h4, cyclePOS04ClausePass] using hc5
  · simpa [h5, cyclePOS04ClausePass] using hc6
  · simpa [h6, cyclePOS04ClausePass] using hc7
  · simpa [h7, cyclePOS04ClausePass] using hc8

theorem cycle_all_local_witnesses :
    ∀ n : CycleNode,
      Nonempty (CSTTT.ClauseWitness (cycleClause n) cycleAlphabet (cycleSpec n)) := by
  intro n
  exact ⟨cycleWitness n (cycle_all_clause_pass n)⟩

/-- All eight differently typed *designed* witnesses inhabit the generic
`ClauseBundle` shape. They are not POS-04's 160 coordinate assignments. -/
abbrev CycleClauseBundle := CSTTT.ClauseBundle cycleAlphabet
  (cycleSpec 0) (cycleSpec 1) (cycleSpec 2) (cycleSpec 3)
  (cycleSpec 4) (cycleSpec 5) (cycleSpec 6) (cycleSpec 7)

def cycleClauseBundle : CycleClauseBundle :=
  { w1 := cycleWitness 0 (cycle_all_clause_pass 0)
    w2 := cycleWitness 1 (cycle_all_clause_pass 1)
    w3 := cycleWitness 2 (cycle_all_clause_pass 2)
    w4 := cycleWitness 3 (cycle_all_clause_pass 3)
    w5 := cycleWitness 4 (cycle_all_clause_pass 4)
    w6 := cycleWitness 5 (cycle_all_clause_pass 5)
    w7 := cycleWitness 6 (cycle_all_clause_pass 6)
    w8 := cycleWitness 7 (cycle_all_clause_pass 7) }

theorem cycle_bundle_nonempty : Nonempty CycleClauseBundle :=
  ⟨cycleClauseBundle⟩

/-- The designed equality rule detects an incorrect diagonal value. -/
def cycleWrongC1 : CSTTT.GlobalAssignment cycleAlphabet :=
  fun c => if c = .diagonal then some hiddenPair.2 else cycleLocal 0 c

theorem cycle_wrong_c1_rejected :
    ¬ (cycleSpec 0).accepts cycleWrongC1 := by
  intro h
  have hv := h.2 .diagonal (by decide)
  have hneq : cycleWrongC1 .diagonal ≠ some (cycleValue 0 .diagonal) := by
    decide
  exact hneq hv

/-- Compatibility on every cycle edge, with real shared edge coordinates. -/
def CycleEdgeCompatible : Prop :=
  ((List.finRange 8).all fun n =>
    (List.finRange 8).all fun m =>
      cycleCoordEnum.elems.all fun c =>
        if decide (cycleAdjacent n m ∧
            c ∈ cycleScope n ∧ c ∈ cycleScope m) then
          decide (cycleLocal n c = cycleLocal m c)
        else true) = true

theorem cycle_edge_compatible : CycleEdgeCompatible := by
  simp only [CycleEdgeCompatible]
  decide

theorem cycle_edge_compatible_universal :
    ∀ n m : CycleNode, cycleAdjacent n m →
      ∀ c : CycleCoord, c ∈ cycleScope n → c ∈ cycleScope m →
        cycleLocal n c = cycleLocal m c := by
  intro n m hadj c hn hm
  have hall := List.all_eq_true.mp cycle_edge_compatible
  have hn' := List.all_eq_true.mp (hall n (List.mem_finRange n))
  have hm' := List.all_eq_true.mp (hn' m (List.mem_finRange m))
  have hc := hm' c (cycleCoordEnum.complete c)
  simp [hadj, hn, hm] at hc
  simpa only [decide_eq_true_eq] using hc

theorem cycle_each_edge_has_overlap :
    ∀ n : CycleNode,
      CycleCoord.edge n ∈ cycleScope n ∧
      CycleCoord.edge n ∈ cycleScope ⟨(n.val + 1) % 8, by omega⟩ := by decide

/-- This is the restriction field of IntegratedPackageWitness generalized
from RootedJoinTree to the declared cyclic cover. -/
def CycleGlobalRestriction (g : CSTTT.GlobalAssignment cycleAlphabet) : Prop :=
  ∀ n : CycleNode, ∀ c : CycleCoord,
    c ∈ cycleScope n → g c = cycleLocal n c

theorem cycle_no_global_restriction :
    ¬ ∃ g : CSTTT.GlobalAssignment cycleAlphabet,
      CycleGlobalRestriction g := by
  rintro ⟨g, hg⟩
  have h0 := hg 0 .diagonal (by decide)
  have h4 := hg 4 .diagonal (by decide)
  have hneq : cycleLocal 0 .diagonal ≠ cycleLocal 4 .diagonal := by
    simp [cycleLocal, cycleScope, cycleValue, hiddenPair]
  exact hneq (h0.symm.trans h4)

/-- The diagonal appears only at C1 and C5, which are not neighbors. -/
theorem cycle_diagonal_not_adjacent :
    ¬ cycleAdjacent (0 : CycleNode) 4 ∧
    (∀ n : CycleNode, CycleCoord.diagonal ∈ cycleScope n →
      n = 0 ∨ n = 4) := by
  simp only [cycleAdjacent, cycleScope]
  decide

/-- TTH-01 rules out an obstruction with these premises on any rooted
running-intersection cover. The cyclic control fails that cover premise. -/
theorem acyclic_compatible_witnesses_glue
    {Index Coord Value : Type}
    (tree : CSTTT.PackageTheory.RootedJoinTree Index Coord)
    (localAssignment : Index → Coord → Value)
    (accepted hardGate : Index → Prop)
    (edgeCompatible :
      ∀ i j : Index, ∀ c : Coord,
        tree.adjacent i j → tree.scope i c → tree.scope j c →
          localAssignment i c = localAssignment j c)
    (allAccepted : ∀ i : Index, accepted i)
    (allHardGates : ∀ i : Index, hardGate i) :
    Nonempty (CSTTT.PackageTheory.IntegratedPackageWitness
      tree localAssignment accepted hardGate) := by
  exact ⟨CSTTT.PackageTheory.acyclicLocalWitnessGluing
    tree localAssignment accepted hardGate edgeCompatible
    allAccepted allHardGates⟩

/-- TTN-08 at the designed-control ceiling: a positive POS-04 package supplies
side conditions, and the cyclic `ClauseSpec` witnesses cannot glue. This does
not establish failure of POS-04's own clause acceptance on local assignments. -/
theorem ttn08_designed_cyclic_control :
    PackagePass .funded .target ∧
    Nonempty CycleClauseBundle ∧
    (∀ n : CycleNode,
      Nonempty (CSTTT.ClauseWitness (cycleClause n) cycleAlphabet (cycleSpec n))) ∧
    (∀ n m : CycleNode, cycleAdjacent n m →
      ∀ c : CycleCoord, c ∈ cycleScope n → c ∈ cycleScope m →
        cycleLocal n c = cycleLocal m c) ∧
    (∀ n : CycleNode,
      CycleCoord.edge n ∈ cycleScope n ∧
      CycleCoord.edge n ∈ cycleScope ⟨(n.val + 1) % 8, by omega⟩) ∧
    ¬ ∃ g : CSTTT.GlobalAssignment cycleAlphabet,
      CycleGlobalRestriction g := by
  exact ⟨package_funded_each_tag .target, cycle_bundle_nonempty,
    cycle_all_local_witnesses,
    cycle_edge_compatible_universal, cycle_each_edge_has_overlap,
    cycle_no_global_restriction⟩

end CSTTT.POS04
