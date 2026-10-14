import CSTTT.Targets.GenericHandoff.StrategyGame
import CSTTT.Targets.GenericHandoff.ViableSet

/-! Sound, potentially incomplete finite constructor for the hybrid game kernel.

This is a theorem about a proved lift, not a theorem that arbitrary recipes
have one. All relevant run contexts are quantified in the lifting obligations.
Only actions selected by a safe response are required safe. No decision
completeness, omitted-context irrelevance, POS-04 equivalence, or RawHandoff
assembly is claimed here. The eventual raw adapter must construct the projection
and interpret all semantic arguments from the shared assignment. -/
namespace CSTTT.TargetTheory.GenericHandoff.GameFiniteConstructor
open StrategyGame
variable {X Run Disturbance Action Outcome : Type} [DecidableEq X]

/-- Each obligation must be proved against the actual interpreted rows/updater.
The finite operator and semantic predicates are mathematical interface arguments
of this engine, not separately supplied candidates at the raw model boundary. -/
structure LiftWitness
    (rows : Rows Run Disturbance Action Outcome)
    (update : Updater Run Disturbance Action Outcome)
    (entries : Run → Prop) (withdrawal : Prop)
    (package resourceClosed : Run → Prop)
    (responseLegal : Run → Disturbance → Action → Prop)
    (transitionLaw : Run → Disturbance → Action → Outcome → Prop)
    (carrier : List X) (retain : List X → X → Bool) where
  context : Run → Prop
  projection : Run → X
  withdrawn : withdrawal
  entriesNonempty : ∃ r, entries r
  entryContext : ∀ r, entries r → context r
  entryFactor : ∀ r, entries r → projection r ∈ ViableSet.greatest carrier retain
  packageLift : ∀ S, ViableSet.Viable retain S →
    ∀ r, context r → projection r ∈ S → package r
  resourceLift : ∀ S, ViableSet.Viable retain S →
    ∀ r, context r → projection r ∈ S → resourceClosed r
  responseLift : ∀ S, ViableSet.Viable retain S →
    ∀ r, context r → projection r ∈ S → ∀ d,
      ∃ a, responseLegal r d a ∧ Normalized rows r d a ∧
        ∀ o, PositiveSupport rows r d a o →
          context (update r d a o) ∧ projection (update r d a o) ∈ S ∧
          transitionLaw r d a o

/-- Defined pullback of the computed greatest set and the auxiliary run-law
invariant. No arbitrary safe factor set is supplied. -/
def liftedInside
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    {carrier : List X} {retain : List X → X → Bool}
    (lift : LiftWitness rows update entries withdrawal package resourceClosed responseLegal
      transitionLaw carrier retain) (r : Run) : Prop :=
  lift.context r ∧ lift.projection r ∈ ViableSet.greatest carrier retain

/-- The construction consumes genuine greatest-set viability and the lift laws.
In particular, projected membership alone is insufficient. -/
def certificate
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    {carrier : List X} {retain : List X → X → Bool}
    (covered : ∀ x, x ∈ carrier) (monotone : ViableSet.Monotone retain)
    (lift : LiftWitness rows update entries withdrawal package resourceClosed responseLegal
      transitionLaw carrier retain) :
    InvariantCertificate rows update entries withdrawal package resourceClosed responseLegal transitionLaw where
  inside := liftedInside lift
  withdrawn := lift.withdrawn
  entriesNonempty := lift.entriesNonempty
  entriesInside r hr := ⟨lift.entryContext r hr,lift.entryFactor r hr⟩
  packageInside r hr := lift.packageLift _ (ViableSet.greatest_viable carrier covered retain monotone) r hr.1 hr.2
  resourcesInside r hr := lift.resourceLift _ (ViableSet.greatest_viable carrier covered retain monotone) r hr.1 hr.2
  response r hr d := by
    obtain ⟨a,ha,hn,hs⟩ := lift.responseLift _
      (ViableSet.greatest_viable carrier covered retain monotone) r hr.1 hr.2 d
    exact ⟨a,ha,hn,fun o ho => ⟨⟨(hs o ho).1,(hs o ho).2.1⟩,(hs o ho).2.2⟩⟩

theorem finite_lift_game_soundness
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    {carrier : List X} {retain : List X → X → Bool}
    (covered : ∀ x, x ∈ carrier) (monotone : ViableSet.Monotone retain)
    (lift : LiftWitness rows update entries withdrawal package resourceClosed responseLegal
      transitionLaw carrier retain) :
    GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw :=
  invariant_game_soundness rows update entries withdrawal package resourceClosed responseLegal
    transitionLaw (certificate covered monotone lift)

/-- The same induction proves full context coverage along generated plays.
The result does not discard counters, ledger or tape dependence. -/
theorem finite_lift_play_context
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    {carrier : List X} {retain : List X → X → Bool}
    (covered : ∀ x, x ∈ carrier) (monotone : ViableSet.Monotone retain)
    (lift : LiftWitness rows update entries withdrawal package resourceClosed responseLegal
      transitionLaw carrier retain)
    {entry r : Run} {past : List Run} (he : entries entry)
    (hp : Play rows update (causalStrategy rows update entries withdrawal package resourceClosed
      responseLegal transitionLaw (certificate covered monotone lift)) entry (r :: past)) :
    lift.context r ∧ lift.projection r ∈ ViableSet.greatest carrier retain :=
  every_play_inside rows update entries withdrawal package resourceClosed responseLegal transitionLaw
    (certificate covered monotone lift) he hp r past rfl

end CSTTT.TargetTheory.GenericHandoff.GameFiniteConstructor
