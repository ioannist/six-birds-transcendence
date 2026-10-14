import CSTTT.Core.Finite

namespace CSTTT

inductive OperationalEdgeKind where
  | sourceToRecord
  | recordToTarget
  | liveDependency
  | guardedFission
  | guardedFusion
  deriving DecidableEq, Repr

structure OperationalEdge (Node : Type) where
  source : Node
  target : Node
  kind : OperationalEdgeKind

/-- The fallback seed is operational provenance, not a successorship verdict. -/
structure OperationalSeed (Node : Type) where
  edges : List (OperationalEdge Node)
  seed : Node → Node → Prop
  edgeSound : ∀ e : OperationalEdge Node, e ∈ edges → seed e.source e.target

structure AncestryClosure (Node : Type) where
  seed : Node → Node → Prop
  gamma : (Node → Node → Prop) → Node → Node → Prop
  monotone :
    ∀ r s : Node → Node → Prop,
      (∀ x y, r x y → s x y) →
      ∀ x y, gamma r x y → gamma s x y
  noExNihilo : Prop

/-- The fallback result is relation-valued structural successorship only. -/
structure IAPSCertificate
    (Node PackageCert AutonomyCert : Type)
    (packageValid : PackageCert → Prop)
    (autonomyValid : AutonomyCert → Prop) where
  source : Node
  target : Node
  ancestry : Node → Node → Prop
  ancestryEvidence : ancestry source target
  packageCertificate : PackageCert
  packageEvidence : packageValid packageCertificate
  autonomyCertificate : AutonomyCert
  autonomyEvidence : autonomyValid autonomyCertificate

end CSTTT
