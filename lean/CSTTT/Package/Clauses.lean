import CSTTT.Core.Carrier
import CSTTT.Temporal.Closure

namespace CSTTT

inductive ClauseId where
  | c1Objecthood
  | c2StrictPromotion
  | c3ReflexiveSelfCoordinate
  | c4InterfaceNonexposure
  | c5ActionCredit
  | c6TemporalClosure
  | c7BindingRecombination
  | c8ViabilityRepair
  deriving DecidableEq, Repr

namespace ClauseId

def all : List ClauseId :=
  [c1Objecthood, c2StrictPromotion, c3ReflexiveSelfCoordinate,
   c4InterfaceNonexposure, c5ActionCredit, c6TemporalClosure,
   c7BindingRecombination, c8ViabilityRepair]

end ClauseId

structure PackageAlphabet where
  Coord : Type
  Value : Type
  coordEnum : FiniteEnum Coord
  valueEnum : FiniteEnum Value

abbrev GlobalAssignment (a : PackageAlphabet) := a.Coord → Option a.Value

/-- Each clause is declared independently of package success and lineage. -/
structure ClauseSpec (id : ClauseId) (a : PackageAlphabet) where
  scope : List a.Coord
  accepts : GlobalAssignment a → Prop
  hardGate : GlobalAssignment a → Prop
  essentialResources : List ResourceId

structure ClauseWitness (id : ClauseId) (a : PackageAlphabet) (spec : ClauseSpec id a) where
  assignment : GlobalAssignment a
  accepted : spec.accepts assignment
  gatePassed : spec.hardGate assignment

/-- Exactly one independently typed witness slot is present for each C-shaped clause. -/
structure ClauseBundle (a : PackageAlphabet)
    (c1 : ClauseSpec .c1Objecthood a)
    (c2 : ClauseSpec .c2StrictPromotion a)
    (c3 : ClauseSpec .c3ReflexiveSelfCoordinate a)
    (c4 : ClauseSpec .c4InterfaceNonexposure a)
    (c5 : ClauseSpec .c5ActionCredit a)
    (c6 : ClauseSpec .c6TemporalClosure a)
    (c7 : ClauseSpec .c7BindingRecombination a)
    (c8 : ClauseSpec .c8ViabilityRepair a) where
  w1 : ClauseWitness .c1Objecthood a c1
  w2 : ClauseWitness .c2StrictPromotion a c2
  w3 : ClauseWitness .c3ReflexiveSelfCoordinate a c3
  w4 : ClauseWitness .c4InterfaceNonexposure a c4
  w5 : ClauseWitness .c5ActionCredit a c5
  w6 : ClauseWitness .c6TemporalClosure a c6
  w7 : ClauseWitness .c7BindingRecombination a c7
  w8 : ClauseWitness .c8ViabilityRepair a c8

end CSTTT
