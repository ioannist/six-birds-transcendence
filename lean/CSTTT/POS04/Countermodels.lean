import CSTTT.POS04.Assembly
import CSTTT.Transport.RouteDiscipline

/-!
Finite POS-04 boundary witnesses for TTN-02, 04, 06, 09, 13, and 14.
These use the raw-data predicates of L5–L8. Their scope is the declared
POS-04 finite interface: C4 and C7 remain surrogates, and a pointed T1
factor is not a physical consciousness model. See
`audit/N1_countermodel_plan.md` for the exact-statement mappings and gaps.
-/

namespace CSTTT.POS04

open CSTTT.Objecthood.T1Audit

/-- A finite T1 system with a selected present state. Both instances below
have the same canonical action table; only their designated state differs.
The hidden readout is the computed predictive M partition. -/
structure PointedFactor where
  tag : Tag
  present : KState

def pointedPublic (x : PointedFactor) := c4Current .positive x.tag x.present
def pointedHidden (x : PointedFactor) := rawM x.tag x.present

/-- TTN-02, at the finite predictive-interface ceiling. This does not
establish a difference in a full P05 consciousness predicate. -/
theorem ttn02_public_shadow :
    ∃ a b : PointedFactor,
      a.tag = .target ∧ b.tag = .target ∧
      pointedPublic a = pointedPublic b ∧
      pointedHidden a ≠ pointedHidden b ∧
      C4Collision .positive .target := by
  refine ⟨⟨.target,.p1w0⟩, ⟨.target,.p1w1⟩,
    rfl, rfl, ?_, ?_, c4_collision_each_tag .target⟩
  · decide
  · decide

def routeCurrent (r : RouteId) : Option KState := routeTargetEndpoint r
def routeFuture (r : RouteId) : Option Nat := routeFutureOutput .positive r
def routeResidue (r : RouteId) := routeRegister r

theorem pos04_route_current_collision :
    routeCurrent .a = routeCurrent .b ∧
    routeFuture .a ≠ routeFuture .b ∧
    routeResidue .a ≠ routeResidue .b := by decide

theorem pos04_route_code_future_sufficient :
    CSTTT.RouteTheory.FutureSufficientEncoding
      (fun r => (routeCurrent r, routeResidue r)) routeFuture := by
  intro r s h
  cases r <;> cases s <;> simp_all [routeCurrent, routeFuture, routeResidue,
    routeRegister, routeOf, routes, sourceHistory]

/-- TTN-04 on the concrete two-route domain: the current-only obstruction
and the licensed memory repair. The future is the declared funded route
readout, not an arbitrary label. -/
theorem ttn04_current_collision_memory :
    (¬ ∃ predictor : Option KState → Option Nat,
      predictor (routeCurrent .a) = routeFuture .a ∧
      predictor (routeCurrent .b) = routeFuture .b) ∧
    CSTTT.RouteTheory.MemoryRepairs routeCurrent routeFuture routeResidue := by
  have h := pos04_route_current_collision
  refine ⟨CSTTT.RouteTheory.noCurrentOnlyPredictor
    routeCurrent routeFuture .a .b h.1 h.2.1, ?_⟩
  have license := CSTTT.RouteTheory.memoryOrFlatness
    routeCurrent routeFuture routeResidue pos04_route_code_future_sufficient
  cases license with
  | inl flat => exact False.elim (h.2.1 (flat .a .b h.1))
  | inr memory => exact memory

/-- TTN-06: the funded target has its computed package and remains viable
after source withdrawal, while withdrawing its essential target recharge
collapses the greatest viable set and destroys autonomy. -/
theorem ttn06_withdrawn_essential_resource :
    ∃ fundedVariant broken : C8Variant,
      PackagePass fundedVariant .target ∧
      c8Greatest fundedVariant .target = kernel ∧
      TargetAutonomy fundedVariant c8WithdrawnReceiver ∧
      c8Greatest broken .target = [] ∧
      ¬ TargetAutonomy broken c8WithdrawnReceiver := by
  exact ⟨.funded,.negUnderfund,package_funded_each_tag .target,
    c8_funded_greatest_is_kernel .target,
    target_only_autonomy_positive,neg_c8_underfund_empty,
    neg_autonomy_withdraw_fails⟩

/-- TTN-09: both ends of the declared stage chain remain realized and the
raw exit event is unchanged, but mix1 is absent. Endpoint equivalence here
is the two routes' computed T1 endpoint class, not an active receiver output
through the broken corridor. -/
theorem ttn09_gap_resume :
    ∃ v : CorridorVariant,
      Stage.sourceLive ∈ corridorRealized v ∧
      Stage.targetExit ∈ corridorRealized v ∧
      Stage.mix1 ∉ corridorRealized v ∧
      corridorStrict v = true ∧
      (sourceHistory .repA).getLast? = some .p1w0 ∧
      routeTargetEndpoint .a = some .p1w0 ∧
      routeTargetEndpoint .a = routeTargetEndpoint .b ∧
      rawM .source .p1w0 = rawM .target .p1w0 ∧
      corridorNoGap v = false ∧ ¬ CorridorPass v := by
  refine ⟨.gap, by decide, by decide, by decide, by decide,
    by decide, by decide,
    by decide, by decide, neg_corridor_gap_no_gap_false,
    neg_corridor_gap_fails⟩

/-- A nonidentity phase re-encoding on the fixed target carrier. This
re-encoding is not a source→target change of carrier. -/
def sameCarrierReencode : KState → KState
  | .p0w0 => .p0w1
  | .p0w1 => .p0w0
  | s => s

theorem same_carrier_reencode_nonidentity :
    sameCarrierReencode .p0w0 ≠ .p0w0 := by decide

theorem same_carrier_reencode_involution (s : KState) :
    sameCarrierReencode (sameCarrierReencode s) = s := by
  cases s <;> rfl

/-- The real distinct-carrier field of the generic Temporal-FIACH type
rules out a certificate whose two carrier identifiers are the same. -/
theorem no_same_carrier_fiach
    {PackageCert CorridorCert AutonomyCert : Type}
    (packageValid : PackageCert → Prop)
    (corridorValid : CorridorCert → Prop)
    (autonomyValid : AutonomyCert → Prop)
    (packageTarget : PackageCert → CarrierId)
    (corridorSource corridorTarget : CorridorCert → CarrierId)
    (autonomyTarget : AutonomyCert → CarrierId)
    (carrier : CarrierId) :
    ¬ ∃ cert : CSTTT.TemporalFIACHCertificate
      PackageCert CorridorCert AutonomyCert packageValid corridorValid
      autonomyValid packageTarget corridorSource corridorTarget autonomyTarget,
      cert.source = carrier ∧ cert.target = carrier := by
  rintro ⟨cert, hs, ht⟩
  exact cert.distinct (hs.trans ht.symm)

/-- TTN-13, using the nonidentity raw phase swap and the actual certificate
distinctness requirement, rather than a stipulated transport predicate. -/
theorem ttn13_same_carrier_boundary :
    sameCarrierReencode .p0w0 ≠ .p0w0 ∧
    (∀ s : KState, sameCarrierReencode (sameCarrierReencode s) = s) ∧
    (∀ {PackageCert CorridorCert AutonomyCert : Type}
      (packageValid : PackageCert → Prop)
      (corridorValid : CorridorCert → Prop)
      (autonomyValid : AutonomyCert → Prop)
      (packageTarget : PackageCert → CarrierId)
      (corridorSource corridorTarget : CorridorCert → CarrierId)
      (autonomyTarget : AutonomyCert → CarrierId),
      ¬ ∃ cert : CSTTT.TemporalFIACHCertificate
        PackageCert CorridorCert AutonomyCert packageValid corridorValid
        autonomyValid packageTarget corridorSource corridorTarget autonomyTarget,
        cert.source = tagCarrierId .target ∧
        cert.target = tagCarrierId .target) := by
  refine ⟨same_carrier_reencode_nonidentity,
    same_carrier_reencode_involution, ?_⟩
  intro PackageCert CorridorCert AutonomyCert pv cv av pt cs ct autonomyEndpoint
  exact no_same_carrier_fiach pv cv av pt cs ct autonomyEndpoint (tagCarrierId .target)

/-- TTN-14 at the finite C7-surrogate ceiling: both structures have the
same complete ordered branch records. Changing the target joint coupling
changes its recombination relation and defeats the staged equation. -/
theorem ttn14_marginals_do_not_fix_recombination :
    ∃ v : C7Variant,
      C7Pass .positive .source ∧
      C7LocallyConsistent v .target ∧
      c7Branchwise .positive .source .crossed =
        c7Branchwise v .target .crossed ∧
      c7JointDistribution .positive .source .crossed ≠
        c7JointDistribution v .target .crossed ∧
      ¬ C7Strict v .target ∧ ¬ C7Transport v := by
  refine ⟨.negTransport,c7_each_tag .source,
    neg_c7_transport_locally_consistent, by decide, by decide,
    neg_c7_transport_loses_target_refinement,
    neg_c7_transport_breaks_staged_equation⟩

end CSTTT.POS04
