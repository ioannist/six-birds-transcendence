import CSTTT.Targets.GenericHandoff.GameInvariantCompleteness
import CSTTT.Autonomy.FiniteAutonomy

/-! G6d-5b internal finite-carrier projection engine. The game is on the full
run space; the frozen TTH-05 Carrier requires a FiniteEnum. This engine DOES
NOT assume a finite-context lift. Every projection obligation below ranges
over all relevant runs, responses and actual positive-support successors.

Component interpretations are mathematical engine parameters, as in
StrategyGame and GameFiniteConstructor. The eventual RawHandoff binding must
DEFINE them from its shared assigned primitives, rather than expose this
interpretation-parametric engine as the final raw-data certificate theorem.
The auxiliary inside predicate is constructed from the game's reachable-play
invariant, never supplied as a finite safety verdict or autonomy proof.
-/
namespace CSTTT.TargetTheory.GenericHandoff.GameAutonomyTransport
open StrategyGame CSTTT.AutonomyTheory

/-- Frozen finite component interpretation, WITHOUT a chosen endpoint or safe
set. These are constructed below from an actual entry and the game invariant. -/
structure FactorData where
  sys : ControlledSystem
  withdrawal : WithdrawalSpec
  resourceOwner : ResourceId → CarrierId
  antiStall : sys.carrier.State → sys.Disturbance → sys.Action → sys.carrier.State → Prop
  budgetSolvent : sys.carrier.State → sys.Disturbance → sys.Action → sys.carrier.State → Prop
  boundaryFixedBeforeEvaluation : Prop
  disturbanceClassFixedBeforeEvaluation : Prop

variable {Run Outcome : Type}

/-- Not an omitted-context assumption: each equation/implication must be
proved by the raw-model instance. Full support is preserved before projecting
to TTH-05's existential response. The action/disturbance domains stay identical. -/
structure ProjectionLaws (factor : FactorData)
    (rows : Rows Run factor.sys.Disturbance factor.sys.Action Outcome)
    (update : Updater Run factor.sys.Disturbance factor.sys.Action Outcome)
    (withdrawal : Prop) (package resourceClosed : Run → Prop)
    (responseLegal : Run → factor.sys.Disturbance → factor.sys.Action → Prop)
    (transitionLaw : Run → factor.sys.Disturbance → factor.sys.Action → Outcome → Prop)
    (projection : Run → factor.sys.carrier.State) : Prop where
  sourceRemoved : withdrawal → factor.withdrawal.sourceRemoved
  bridgeRemoved : withdrawal → factor.withdrawal.bridgeRemoved
  migrationControllerRemoved : withdrawal → factor.withdrawal.migrationControllerRemoved
  externalDecoderRemoved : withdrawal → factor.withdrawal.externalDecoderRemoved
  externalSchedulerRemoved : withdrawal → factor.withdrawal.externalSchedulerRemoved
  undeclaredRepairRemoved : withdrawal → factor.withdrawal.undeclaredRepairRemoved
  boundaryFixed : withdrawal → factor.boundaryFixedBeforeEvaluation
  disturbanceClassFixed : withdrawal → factor.disturbanceClassFixedBeforeEvaluation
  packageProjection : ∀ r, package r → factor.sys.packageValid (projection r)
  resourceProjection : ∀ r, resourceClosed r → ∀ res ∈ factor.sys.maintenanceResources (projection r),
    res ∈ factor.withdrawal.retainedResources
  retainedOwnership : withdrawal → ∀ res ∈ factor.withdrawal.retainedResources,
    factor.resourceOwner res = factor.sys.carrier.id
  actionOwnership : ∀ r d a, resourceClosed r → responseLegal r d a →
    factor.sys.actionOwner a = factor.sys.carrier.id
  stepProjection : ∀ r d a o, responseLegal r d a → PositiveSupport rows r d a o →
    factor.sys.step (projection r) d a (projection (update r d a o))
  antiStallProjection : ∀ r d a o, transitionLaw r d a o →
    factor.antiStall (projection r) d a (projection (update r d a o))
  solvencyProjection : ∀ r d a o, transitionLaw r d a o →
    factor.budgetSolvent (projection r) d a (projection (update r d a o))

/-- Exact data for the actual entry's factor; inside is the image of the
certified run invariant, not a supplied safe subset. -/
def projectedData (factor : FactorData)
    {rows : Rows Run factor.sys.Disturbance factor.sys.Action Outcome}
    {update : Updater Run factor.sys.Disturbance factor.sys.Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop} {package resourceClosed : Run → Prop}
    {responseLegal : Run → factor.sys.Disturbance → factor.sys.Action → Prop}
    {transitionLaw : Run → factor.sys.Disturbance → factor.sys.Action → Outcome → Prop}
    (cert : InvariantCertificate rows update entries withdrawal package resourceClosed responseLegal transitionLaw)
    (projection : Run → factor.sys.carrier.State) (entry : Run) : ExactAutonomyData where
  sys := factor.sys
  endpoint := projection entry
  withdrawal := factor.withdrawal
  inside := fun s => ∃ r, cert.inside r ∧ projection r = s
  resourceOwner := factor.resourceOwner
  antiStall := factor.antiStall
  budgetSolvent := factor.budgetSolvent
  boundaryFixedBeforeEvaluation := factor.boundaryFixedBeforeEvaluation
  disturbanceClassFixedBeforeEvaluation := factor.disturbanceClassFixedBeforeEvaluation

/-- Construct every existing TTH-05 field from game invariance and the checked
projection laws. Normalization supplies a real positive-support successor. -/
def projectedCertificate (factor : FactorData)
    {rows : Rows Run factor.sys.Disturbance factor.sys.Action Outcome}
    {update : Updater Run factor.sys.Disturbance factor.sys.Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop} {package resourceClosed : Run → Prop}
    {responseLegal : Run → factor.sys.Disturbance → factor.sys.Action → Prop}
    {transitionLaw : Run → factor.sys.Disturbance → factor.sys.Action → Outcome → Prop}
    (cert : InvariantCertificate rows update entries withdrawal package resourceClosed responseLegal transitionLaw)
    (projection : Run → factor.sys.carrier.State)
    (laws : ProjectionLaws factor rows update withdrawal package resourceClosed responseLegal transitionLaw projection)
    (entry : Run) (he : entries entry) : ExactAutonomyCertificate (projectedData factor cert projection entry) where
  sourceRemoved := laws.sourceRemoved cert.withdrawn
  bridgeRemoved := laws.bridgeRemoved cert.withdrawn
  migrationControllerRemoved := laws.migrationControllerRemoved cert.withdrawn
  externalDecoderRemoved := laws.externalDecoderRemoved cert.withdrawn
  externalSchedulerRemoved := laws.externalSchedulerRemoved cert.withdrawn
  undeclaredRepairRemoved := laws.undeclaredRepairRemoved cert.withdrawn
  boundaryFixed := laws.boundaryFixed cert.withdrawn
  disturbanceClassFixed := laws.disturbanceClassFixed cert.withdrawn
  endpointInside := ⟨entry,cert.entriesInside entry he,rfl⟩
  packageInside := by
    rintro s ⟨r,hr,hp⟩
    rw [← hp]
    exact laws.packageProjection r (cert.packageInside r hr)
  resourceClosed := by
    rintro s ⟨r,hr,hp⟩ res hres
    rw [← hp] at hres
    exact laws.resourceProjection r (cert.resourcesInside r hr) res hres
  retainedResourcesTargetOwned := laws.retainedOwnership cert.withdrawn
  response := by
    rintro s d ⟨r,hr,hproj⟩
    obtain ⟨act,hlegal,hnormal,hnext⟩ := cert.response r hr d
    obtain ⟨o,ho⟩ := hnormal.2.2
    have ht := hnext o ho
    refine ⟨act,projection (update r d act o),
      laws.actionOwnership r d act (cert.resourcesInside r hr) hlegal,?_,
      ⟨update r d act o,ht.1,rfl⟩,?_,?_⟩
    all_goals rw [← hproj]
    · exact laws.stepProjection r d act o hlegal ho
    · exact laws.antiStallProjection r d act o ht.2
    · exact laws.solvencyProjection r d act o ht.2

/-- The projection preserves EVERY actual branch of the chosen response.
TTH-05's existential response is a consequence of this stronger support law. -/
theorem projected_response_all_support (factor : FactorData)
    {rows : Rows Run factor.sys.Disturbance factor.sys.Action Outcome}
    {update : Updater Run factor.sys.Disturbance factor.sys.Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop} {package resourceClosed : Run → Prop}
    {responseLegal : Run → factor.sys.Disturbance → factor.sys.Action → Prop}
    {transitionLaw : Run → factor.sys.Disturbance → factor.sys.Action → Outcome → Prop}
    (cert : InvariantCertificate rows update entries withdrawal package resourceClosed responseLegal transitionLaw)
    (projection : Run → factor.sys.carrier.State)
    (laws : ProjectionLaws factor rows update withdrawal package resourceClosed responseLegal transitionLaw projection)
    (r : Run) (hr : cert.inside r) (disturbance : factor.sys.Disturbance) :
    ∃ action, factor.sys.actionOwner action = factor.sys.carrier.id ∧ Normalized rows r disturbance action ∧
      ∀ o, PositiveSupport rows r disturbance action o →
        cert.inside (update r disturbance action o) ∧
        factor.sys.step (projection r) disturbance action (projection (update r disturbance action o)) ∧
        factor.antiStall (projection r) disturbance action (projection (update r disturbance action o)) ∧
        factor.budgetSolvent (projection r) disturbance action (projection (update r disturbance action o)) := by
  obtain ⟨action,hlegal,hnormal,hnext⟩ := cert.response r hr disturbance
  refine ⟨action,laws.actionOwnership r disturbance action (cert.resourcesInside r hr) hlegal,hnormal,?_⟩
  intro o ho
  have ht := hnext o ho
  exact ⟨ht.1,laws.stepProjection r disturbance action o hlegal ho,
    laws.antiStallProjection r disturbance action o ht.2,laws.solvencyProjection r disturbance action o ht.2⟩

/-- The GAME READOUT, not a stored autonomy certificate, supplies the actual
reachable-play invariant. One invariant works for EVERY genuine entry. -/
theorem game_each_entry_exact (factor : FactorData)
    {rows : Rows Run factor.sys.Disturbance factor.sys.Action Outcome}
    {update : Updater Run factor.sys.Disturbance factor.sys.Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop} {package resourceClosed : Run → Prop}
    {responseLegal : Run → factor.sys.Disturbance → factor.sys.Action → Prop}
    {transitionLaw : Run → factor.sys.Disturbance → factor.sys.Action → Outcome → Prop}
    (projection : Run → factor.sys.carrier.State)
    (laws : ProjectionLaws factor rows update withdrawal package resourceClosed responseLegal transitionLaw projection)
    (game : GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw) :
    ∃ cert : InvariantCertificate rows update entries withdrawal package resourceClosed responseLegal transitionLaw,
      ∀ entry, entries entry → Nonempty (ExactAutonomyCertificate (projectedData factor cert projection entry)) := by
  obtain ⟨cert⟩ := game_invariant_completeness game
  exact ⟨cert,fun entry he => ⟨projectedCertificate factor cert projection laws entry he⟩⟩

/-- Every finite disturbance word is answered on the declared factor carrier.
This is TTH-05's conclusion, derived using its existing generic theorem. -/
theorem game_each_entry_finite_words (factor : FactorData)
    {rows : Rows Run factor.sys.Disturbance factor.sys.Action Outcome}
    {update : Updater Run factor.sys.Disturbance factor.sys.Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop} {package resourceClosed : Run → Prop}
    {responseLegal : Run → factor.sys.Disturbance → factor.sys.Action → Prop}
    {transitionLaw : Run → factor.sys.Disturbance → factor.sys.Action → Outcome → Prop}
    (projection : Run → factor.sys.carrier.State)
    (laws : ProjectionLaws factor rows update withdrawal package resourceClosed responseLegal transitionLaw projection)
    (game : GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw) :
    ∃ cert : InvariantCertificate rows update entries withdrawal package resourceClosed responseLegal transitionLaw,
      ∀ entry, entries entry → ∀ word : List factor.sys.Disturbance,
        ∃ y, ControlledRun (projectedData factor cert projection entry) (projection entry) word y ∧ factor.sys.packageValid y := by
  obtain ⟨cert,hc⟩ := game_each_entry_exact factor projection laws game
  refine ⟨cert,?_⟩
  intro entry he word
  obtain ⟨exactCert⟩ := hc entry he
  exact postWithdrawalFiniteHorizonInvariance exactCert word

end CSTTT.TargetTheory.GenericHandoff.GameAutonomyTransport
