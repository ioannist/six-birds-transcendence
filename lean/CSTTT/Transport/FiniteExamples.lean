import CSTTT.Transport.FiniteTemporalTransport
import CSTTT.Transport.RecordArrow
import CSTTT.Transport.RouteDiscipline

namespace CSTTT.TransportExamples

inductive SourceBit where | zero | one deriving DecidableEq, Repr
inductive TargetBit where | low | high deriving DecidableEq, Repr

def sourceEnum : FiniteEnum SourceBit :=
  { elems := [.zero, .one]
    complete := by intro x; cases x <;> simp }

def targetEnum : FiniteEnum TargetBit :=
  { elems := [.low, .high]
    complete := by intro x; cases x <;> simp }

def sourceAlphabet : TemporalAlphabet :=
  {
    predictiveType := SourceBit
    orderType := SourceBit
    tickType := SourceBit
    progressType := SourceBit
    recordType := SourceBit
    routeType := SourceBit
    maintenanceType := SourceBit
    predictiveEnum := sourceEnum
    orderEnum := sourceEnum
    tickEnum := sourceEnum
    progressEnum := sourceEnum
    recordEnum := sourceEnum
    routeEnum := sourceEnum
    maintenanceEnum := sourceEnum
  }

def targetAlphabet : TemporalAlphabet :=
  {
    predictiveType := TargetBit
    orderType := TargetBit
    tickType := TargetBit
    progressType := TargetBit
    recordType := TargetBit
    routeType := TargetBit
    maintenanceType := TargetBit
    predictiveEnum := targetEnum
    orderEnum := targetEnum
    tickEnum := targetEnum
    progressEnum := targetEnum
    recordEnum := targetEnum
    routeEnum := targetEnum
    maintenanceEnum := targetEnum
  }

def mapBit : SourceBit → TargetBit
  | .zero => .low
  | .one => .high

def exampleClock : ClockTranslation sourceAlphabet targetAlphabet :=
  {
    mapPredictive := mapBit
    mapOrder := mapBit
    mapTick := mapBit
    mapProgress := mapBit
    mapRecord := mapBit
    mapRoute := mapBit
    mapMaintenance := mapBit
    successorCompatible := True
    progressCompatible := True
    recordMonotone := True
  }

def sourceSignature : TemporalSignature sourceAlphabet :=
  {
    predictiveNow := { predictiveClass := .zero, routeResidue := .zero, futureSufficient := True }
    orderState := .zero
    tickPhase := .zero
    progressState := .zero
    arrowRecord := .zero
    maintenanceState := .zero
    owner := ⟨17⟩
  }

def targetSignature : TemporalSignature targetAlphabet :=
  {
    predictiveNow := { predictiveClass := .low, routeResidue := .low, futureSufficient := True }
    orderState := .low
    tickPhase := .low
    progressState := .low
    arrowRecord := .low
    maintenanceState := .low
    owner := ⟨101⟩
  }

theorem exactHeterogeneousSignatureAgreement :
    TransportTheory.TemporalSignatureAgreement
      exampleClock ⟨101⟩ sourceSignature targetSignature := by
  exact {
    predictiveClass := rfl
    routeResidue := rfl
    futureSufficiency := rfl
    orderState := rfl
    tickPhase := rfl
    progressState := rfl
    arrowRecord := rfl
    maintenanceState := rfl
    targetOwnership := rfl
  }

inductive ExampleRoute where | left | right deriving DecidableEq, Repr

def exampleCurrent : ExampleRoute → Nat := fun _ => 0

def exampleFuture : ExampleRoute → Nat
  | .left => 0
  | .right => 1

theorem exampleNoCurrentOnlyPredictor :
    ¬ ∃ predictor : Nat → Nat,
      predictor (exampleCurrent .left) = exampleFuture .left ∧
      predictor (exampleCurrent .right) = exampleFuture .right := by
  exact RouteTheory.noCurrentOnlyPredictor
    exampleCurrent exampleFuture .left .right rfl (by decide)

inductive DiamondRoute where | left | right deriving DecidableEq, Repr
inductive DiamondEndpoint where | joined deriving DecidableEq, Repr
inductive DiamondNormal where | normal deriving DecidableEq, Repr

def diamondCertificate : RouteTheory.NormalizationCertificate
    DiamondRoute Unit DiamondNormal DiamondEndpoint :=
  {
    boundary := fun _ => ()
    normalize := fun _ => .normal
    canonicalNormal := fun _ => .normal
    endpoint := fun _ => .joined
    endpointOfNormal := fun _ => .joined
    normalizeByBoundary := by intro r; cases r <;> rfl
    endpointFactors := by intro r; cases r <;> rfl
  }

theorem exampleConfluentEndpoints :
    diamondCertificate.endpoint .left = diamondCertificate.endpoint .right := by
  exact RouteTheory.routeIndependentEndpointUnderNormalization
    diamondCertificate .left .right rfl

end CSTTT.TransportExamples
