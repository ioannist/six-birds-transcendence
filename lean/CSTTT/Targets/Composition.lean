import CSTTT.Targets.FiniteTemporalFIACH
import CSTTT.Corridor.Composition

namespace CSTTT.TargetTheory

/-- Finite summary of the independently audited lanes needed for episode composition. -/
structure FullHandoffData (Package Signature : Type) where
  source : CarrierId
  target : CarrierId
  sourcePackage : Package
  targetPackage : Package
  entry : Signature
  exit : Signature
  routeStatus : RouteStatus
  targetOwner : CarrierId
  realized : Prop
  lineage : Prop
  autonomous : Prop

/-- Proof fields for one full structural handoff summary. -/
structure FullHandoffCertificate
    {Package Signature : Type}
    (d : FullHandoffData Package Signature) where
  distinct : d.source ≠ d.target
  targetOwned : d.targetOwner = d.target
  realized : d.realized
  lineage : d.lineage
  autonomous : d.autonomous

/-- The exact intermediate package, temporal frontier, route residue, and owner must agree. -/
def FullHandoffCompatible
    {Package Signature : Type}
    (left right : FullHandoffData Package Signature) : Prop :=
  left.target = right.source ∧
  left.targetPackage = right.sourcePackage ∧
  left.exit = right.entry ∧
  left.targetOwner = right.source ∧
  (left.routeStatus = .flat ∧ right.routeStatus = .flat ∨
   left.routeStatus ≠ .unresolved ∧ right.routeStatus ≠ .unresolved)

/-- Route status is flat only when both component handoffs are independently flat. -/
def composeRouteStatus (left right : RouteStatus) : RouteStatus :=
  if left = .flat ∧ right = .flat then .flat else .routeIndexed

/-- Composition retains the first source, final target, shared lane proofs, and final autonomy. -/
def composeFullHandoffData
    {Package Signature : Type}
    (left right : FullHandoffData Package Signature) : FullHandoffData Package Signature where
  source := left.source
  target := right.target
  sourcePackage := left.sourcePackage
  targetPackage := right.targetPackage
  entry := left.entry
  exit := right.exit
  routeStatus := composeRouteStatus left.routeStatus right.routeStatus
  targetOwner := right.targetOwner
  realized := left.realized ∧ right.realized
  lineage := left.lineage ∧ right.lineage
  autonomous := right.autonomous

/-- TTH-07 / PTH-06: full Temporal-FIACH summaries compose under the exact interface. -/
theorem fullTemporalHandoffComposition
    {Package Signature : Type}
    {left right : FullHandoffData Package Signature}
    (leftCert : FullHandoffCertificate left)
    (rightCert : FullHandoffCertificate right)
    (interface : FullHandoffCompatible left right)
    (endpointsDistinct : left.source ≠ right.target) :
    Nonempty (FullHandoffCertificate (composeFullHandoffData left right)) := by
  exact ⟨{
    distinct := endpointsDistinct
    targetOwned := rightCert.targetOwned
    realized := ⟨leftCert.realized, rightCert.realized⟩
    lineage := ⟨leftCert.lineage, rightCert.lineage⟩
    autonomous := rightCert.autonomous
  }⟩

/-- The composition theorem does not infer one lane from another. -/
theorem composedHandoffPreservesIndependentLanes
    {Package Signature : Type}
    {left right : FullHandoffData Package Signature}
    (cert : FullHandoffCertificate (composeFullHandoffData left right)) :
    (left.realized ∧ right.realized) ∧
    (left.lineage ∧ right.lineage) ∧
    right.autonomous := by
  exact ⟨cert.realized, cert.lineage, cert.autonomous⟩

/-- A route-indexed component prevents an automatic flat composite. -/
theorem routeIndexedComponentPreventsAutomaticFlatness
    (left right : RouteStatus)
    (h : left ≠ .flat ∨ right ≠ .flat) :
    composeRouteStatus left right = .routeIndexed := by
  have hnot : ¬ (left = .flat ∧ right = .flat) := by
    intro bothFlat
    exact h.elim
      (fun leftNotFlat => leftNotFlat bothFlat.1)
      (fun rightNotFlat => rightNotFlat bothFlat.2)
  simp [composeRouteStatus, hnot]

end CSTTT.TargetTheory
