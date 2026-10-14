import CSTTT.Package.Clauses

namespace CSTTT.PackageTheory

/-- A path that stays inside the clauses carrying one coordinate.  Adjacency is
    supplied independently of all package-success or handoff predicates. -/
inductive ScopedReach
    {Index Coord : Type}
    (adjacent : Index → Index → Prop)
    (scope : Index → Coord → Prop)
    (coord : Coord) : Index → Index → Prop where
  | refl (i : Index) (present : scope i coord) : ScopedReach adjacent scope coord i i
  | step {i j k : Index}
      (presentAtI : scope i coord)
      (presentAtJ : scope j coord)
      (edge : adjacent i j)
      (tail : ScopedReach adjacent scope coord j k) :
      ScopedReach adjacent scope coord i k

/-- A rooted parent presentation.  The rank-decrease field makes parent cycles
    impossible; every nonroot has exactly one parent because `parent` is a
    function and `everyNonrootHasParent` is total away from the root. -/
structure RootedJoinTree (Index Coord : Type) where
  root : Index
  parent : Index → Option Index
  rootHasNoParent : parent root = none
  everyNonrootHasParent : ∀ i : Index, i ≠ root → ∃ p : Index, parent i = some p
  rank : Index → Nat
  parentDecreases : ∀ i p : Index, parent i = some p → rank p < rank i
  scope : Index → Coord → Prop
  covers : ∀ c : Coord, ∃ i : Index, scope i c
  runningIntersection :
    ∀ i j : Index, ∀ c : Coord, scope i c → scope j c →
      ScopedReach
        (fun a b => parent a = some b ∨ parent b = some a)
        scope c i j

namespace RootedJoinTree

variable {Index Coord : Type}

/-- Undirected adjacency induced by the independently declared rooted parent map. -/
def adjacent (tree : RootedJoinTree Index Coord) (i j : Index) : Prop :=
  tree.parent i = some j ∨ tree.parent j = some i

end RootedJoinTree

/-- Edge compatibility propagates along a running-intersection path. -/
theorem localEqualityAlongScopedReach
    {Index Coord Value : Type}
    {adjacent : Index → Index → Prop}
    {scope : Index → Coord → Prop}
    {localAssignment : Index → Coord → Value}
    (edgeCompatible :
      ∀ i j : Index, ∀ c : Coord,
        adjacent i j → scope i c → scope j c → localAssignment i c = localAssignment j c)
    {c : Coord} {i j : Index}
    (path : ScopedReach adjacent scope c i j) :
    localAssignment i c = localAssignment j c := by
  induction path with
  | refl _ _ => rfl
  | step presentAtI presentAtJ edge tail ih =>
      exact Eq.trans (edgeCompatible _ _ _ edge presentAtI presentAtJ) ih

/-- Canonical global assignment: choose one local carrier for each covered coordinate. -/
noncomputable def gluedAssignment
    {Index Coord Value : Type}
    (tree : RootedJoinTree Index Coord)
    (localAssignment : Index → Coord → Value) : Coord → Value :=
  fun c => localAssignment (Classical.choose (tree.covers c)) c

/-- The chosen global assignment restricts to every local assignment. -/
theorem gluedAssignmentAgrees
    {Index Coord Value : Type}
    (tree : RootedJoinTree Index Coord)
    (localAssignment : Index → Coord → Value)
    (edgeCompatible :
      ∀ i j : Index, ∀ c : Coord,
        tree.adjacent i j → tree.scope i c → tree.scope j c →
          localAssignment i c = localAssignment j c)
    (i : Index) (c : Coord) (present : tree.scope i c) :
    gluedAssignment tree localAssignment c = localAssignment i c := by
  classical
  unfold gluedAssignment
  apply localEqualityAlongScopedReach edgeCompatible
  exact tree.runningIntersection
    (Classical.choose (tree.covers c)) i c
    (Classical.choose_spec (tree.covers c)) present

/-- A global package witness keeps local acceptance and hard gates as separate fields. -/
structure IntegratedPackageWitness
    {Index Coord Value : Type}
    (tree : RootedJoinTree Index Coord)
    (localAssignment : Index → Coord → Value)
    (accepted hardGate : Index → Prop) where
  global : Coord → Value
  restricts : ∀ i : Index, ∀ c : Coord, tree.scope i c → global c = localAssignment i c
  everyLocalAccepted : ∀ i : Index, accepted i
  everyHardGatePassed : ∀ i : Index, hardGate i

/-- TTH-01 / PTH-01.  A rooted acyclic running-intersection cover plus
    edge-compatible local assignments yields one global assignment whose
    restrictions recover every local witness. -/
noncomputable def acyclicLocalWitnessGluing
    {Index Coord Value : Type}
    (tree : RootedJoinTree Index Coord)
    (localAssignment : Index → Coord → Value)
    (accepted hardGate : Index → Prop)
    (edgeCompatible :
      ∀ i j : Index, ∀ c : Coord,
        tree.adjacent i j → tree.scope i c → tree.scope j c →
          localAssignment i c = localAssignment j c)
    (allAccepted : ∀ i : Index, accepted i)
    (allHardGates : ∀ i : Index, hardGate i) :
    IntegratedPackageWitness tree localAssignment accepted hardGate := by
  classical
  refine
    { global := gluedAssignment tree localAssignment
      restricts := ?_
      everyLocalAccepted := allAccepted
      everyHardGatePassed := allHardGates }
  intro i c present
  exact gluedAssignmentAgrees tree localAssignment edgeCompatible i c present

/-- Heterogeneous stage evidence is typed before target assembly.  It carries
    source and target vocabularies, total coordinate maps, and pointwise value
    preservation, but contains no lineage or autonomy field. -/
structure StagedHeterogeneousEvidence
    {Index SourceCoord TargetCoord SourceValue TargetValue : Type}
    (targetTree : RootedJoinTree Index TargetCoord) where
  sourceScope : Index → SourceCoord → Prop
  sourceLocal : Index → SourceCoord → SourceValue
  targetLocal : Index → TargetCoord → TargetValue
  mapCoord : Index → SourceCoord → TargetCoord
  mapValue : Index → SourceValue → TargetValue
  targetAccepted : Index → Prop
  targetHardGate : Index → Prop
  separatelyTyped : Prop
  separatelyTypedPass : separatelyTyped
  hardGatesNeverAveraged : Prop
  hardGatesNeverAveragedPass : hardGatesNeverAveraged
  everySourceCoordinateMapped :
    ∀ i : Index, ∀ c : SourceCoord,
      sourceScope i c → targetTree.scope i (mapCoord i c)
  everyTargetCoordinateMapped :
    ∀ i : Index, ∀ c : TargetCoord,
      targetTree.scope i c →
        ∃ source : SourceCoord, sourceScope i source ∧ mapCoord i source = c
  mappedValuesAgree :
    ∀ i : Index, ∀ c : SourceCoord,
      sourceScope i c →
        targetLocal i (mapCoord i c) = mapValue i (sourceLocal i c)
  everyTargetAccepted : ∀ i : Index, targetAccepted i
  everyTargetHardGatePassed : ∀ i : Index, targetHardGate i

/-- TTH-02 / PTH-02. Typed stagewise preservation and target-local gluing
    assemble a target package without invoking any later verdict predicate. -/
theorem stagedHeterogeneousPackageAssembly
    {Index SourceCoord TargetCoord SourceValue TargetValue : Type}
    (targetTree : RootedJoinTree Index TargetCoord)
    (stage :
      StagedHeterogeneousEvidence
        (SourceCoord := SourceCoord)
        (SourceValue := SourceValue)
        (TargetValue := TargetValue)
        targetTree)
    (edgeCompatible :
      ∀ i j : Index, ∀ c : TargetCoord,
        targetTree.adjacent i j →
        targetTree.scope i c → targetTree.scope j c →
        stage.targetLocal i c = stage.targetLocal j c) :
    stage.separatelyTyped ∧ stage.hardGatesNeverAveraged ∧
      Nonempty (IntegratedPackageWitness
        targetTree stage.targetLocal stage.targetAccepted stage.targetHardGate) := by
  refine ⟨stage.separatelyTypedPass, stage.hardGatesNeverAveragedPass, ?_⟩
  exact ⟨acyclicLocalWitnessGluing
    targetTree stage.targetLocal stage.targetAccepted stage.targetHardGate
    edgeCompatible stage.everyTargetAccepted stage.everyTargetHardGatePassed⟩

end CSTTT.PackageTheory
