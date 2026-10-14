import CSTTT.Targets.Composition
import CSTTT.Transport.RouteDiscipline

namespace CSTTT.TargetTheory

/-- Contextual route completion keeps the endpoint package fixed while changing only route status. -/
structure RouteCompletionData (Package : Type) where
  endpointPackage : Package
  inputStatus : RouteStatus
  outputStatus : RouteStatus
  routeMemoryRetained : Prop
  flatnessCertified : Prop
  commonNormalForm : Prop
  zeroClockHolonomy : Prop

/-- Licensed route completion has exactly the memory-or-flatness alternatives. -/
structure RouteCompletionCertificate
    {Package : Type}
    (d : RouteCompletionData Package) where
  licensed : d.routeMemoryRetained ∨
    (d.flatnessCertified ∧ d.commonNormalForm ∧ d.zeroClockHolonomy)
  outputCorrect :
    (d.routeMemoryRetained → d.outputStatus = .routeIndexed) ∧
    (d.flatnessCertified ∧ d.commonNormalForm ∧ d.zeroClockHolonomy → d.outputStatus = .flat)

/-- Route memory cannot be erased unless flatness, normalization, and clock compatibility are all certified. -/
theorem noUnlicensedRouteMemoryErasure
    {Package : Type}
    {d : RouteCompletionData Package}
    (cert : RouteCompletionCertificate d)
    (noMemory : ¬ d.routeMemoryRetained) :
    d.flatnessCertified ∧ d.commonNormalForm ∧ d.zeroClockHolonomy := by
  exact cert.licensed.resolve_left noMemory

/-- A holonomic handoff remains route-indexed when route memory is retained. -/
theorem retainedRouteMemoryYieldsIndexedStatus
    {Package : Type}
    {d : RouteCompletionData Package}
    (cert : RouteCompletionCertificate d)
    (memory : d.routeMemoryRetained) :
    d.outputStatus = .routeIndexed := by
  exact cert.outputCorrect.1 memory

/-- A separately certified common normal form licenses the flat strengthening. -/
theorem certifiedNormalizationYieldsFlatStatus
    {Package : Type}
    {d : RouteCompletionData Package}
    (cert : RouteCompletionCertificate d)
    (flat : d.flatnessCertified)
    (normal : d.commonNormalForm)
    (clock : d.zeroClockHolonomy) :
    d.outputStatus = .flat := by
  exact cert.outputCorrect.2 ⟨flat, normal, clock⟩

end CSTTT.TargetTheory
