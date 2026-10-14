import CSTTT.Transport.TemporalBridge

namespace CSTTT.RouteTheory

/-- An encoding is future-sufficient when equal codes force equal future
signatures on the declared route class. -/
def FutureSufficientEncoding
    {Route Code Future : Type}
    (encode : Route → Code)
    (future : Route → Future) : Prop :=
  ∀ r₁ r₂, encode r₁ = encode r₂ → future r₁ = future r₂


/-- A current-only predictor cannot realize two different futures at one current
code.  This is the elementary finite obstruction used by the route-memory toy. -/
theorem noCurrentOnlyPredictor
    {Route Current Future : Type}
    (current : Route → Current)
    (future : Route → Future)
    (r₁ r₂ : Route)
    (hsame : current r₁ = current r₂)
    (hdifferent : future r₁ ≠ future r₂) :
    ¬ ∃ predictor : Current → Future,
      predictor (current r₁) = future r₁ ∧
      predictor (current r₂) = future r₂ := by
  intro h
  rcases h with ⟨predictor, h₁, h₂⟩
  apply hdifferent
  calc
    future r₁ = predictor (current r₁) := h₁.symm
    _ = predictor (current r₂) := congrArg predictor hsame
    _ = future r₂ := h₂

/-- Current flatness: the current class already fixes the future signature. -/
def FlatAt
    {Route Current Future : Type}
    (current : Route → Current)
    (future : Route → Future) : Prop :=
  ∀ r₁ r₂, current r₁ = current r₂ → future r₁ = future r₂

/-- Route memory repairs every current collision that remains future-distinct. -/
def MemoryRepairs
    {Route Current Future Residue : Type}
    (current : Route → Current)
    (future : Route → Future)
    (residue : Route → Residue) : Prop :=
  ∀ r₁ r₂, current r₁ = current r₂ → future r₁ ≠ future r₂ →
    residue r₁ ≠ residue r₂

/-- TTN-04. If current plus route residue is future-sufficient, then either the
current representation is already flat or route residue separates every
current-equal future-distinct pair. -/
theorem memoryOrFlatness
    {Route Current Future Residue : Type}
    (current : Route → Current)
    (future : Route → Future)
    (residue : Route → Residue)
    (hsufficient : FutureSufficientEncoding (fun r => (current r, residue r)) future) :
    FlatAt current future ∨ MemoryRepairs current future residue := by
  classical
  by_cases hflat : FlatAt current future
  · exact Or.inl hflat
  · apply Or.inr
    intro r₁ r₂ hcurrent hfuture
    intro hresidue
    apply hfuture
    apply hsufficient r₁ r₂
    exact Prod.ext hcurrent hresidue

/-- A canonical global now is a function of boundary data alone. -/
def CanonicalGlobalNow
    {Route Boundary Now : Type}
    (boundary : Route → Boundary)
    (localNow : Route → Now) : Prop :=
  ∃ globalNow : Boundary → Now, ∀ r, globalNow (boundary r) = localNow r

/-- TTN-05. Two same-boundary routes with distinct local-now values obstruct a
single boundary-indexed global now. -/
theorem noCanonicalGlobalNowOfTranslationHolonomy
    {Route Boundary Now : Type}
    (boundary : Route → Boundary)
    (localNow : Route → Now)
    (r₁ r₂ : Route)
    (hsame : boundary r₁ = boundary r₂)
    (hdifferent : localNow r₁ ≠ localNow r₂) :
    ¬ CanonicalGlobalNow boundary localNow := by
  intro hglobal
  rcases hglobal with ⟨globalNow, hfactor⟩
  apply hdifferent
  calc
    localNow r₁ = globalNow (boundary r₁) := (hfactor r₁).symm
    _ = globalNow (boundary r₂) := congrArg globalNow hsame
    _ = localNow r₂ := hfactor r₂

/-- Short named form of the global-now factorization obstruction. -/
theorem noGlobalNowFactorization
    {Route Boundary Now : Type}
    (boundary : Route → Boundary)
    (localNow : Route → Now)
    (r₁ r₂ : Route)
    (hsame : boundary r₁ = boundary r₂)
    (hdifferent : localNow r₁ ≠ localNow r₂) :
    ¬ CanonicalGlobalNow boundary localNow := by
  exact noCanonicalGlobalNowOfTranslationHolonomy
    boundary localNow r₁ r₂ hsame hdifferent

/-- Explicit normalization data used to purchase route independence. -/
structure NormalizationCertificate
    (Route Boundary Normal Endpoint : Type) where
  boundary : Route → Boundary
  normalize : Route → Normal
  canonicalNormal : Boundary → Normal
  endpoint : Route → Endpoint
  endpointOfNormal : Normal → Endpoint
  normalizeByBoundary : ∀ r, normalize r = canonicalNormal (boundary r)
  endpointFactors : ∀ r, endpoint r = endpointOfNormal (normalize r)

/-- TTH-09. When every route normalizes to the canonical normal form of its
boundary and endpoints factor through that normal form, equal boundaries have
equal temporal endpoints. -/
theorem routeIndependentEndpointUnderNormalization
    {Route Boundary Normal Endpoint : Type}
    (c : NormalizationCertificate Route Boundary Normal Endpoint)
    (r₁ r₂ : Route)
    (hsame : c.boundary r₁ = c.boundary r₂) :
    c.endpoint r₁ = c.endpoint r₂ := by
  calc
    c.endpoint r₁ = c.endpointOfNormal (c.normalize r₁) := c.endpointFactors r₁
    _ = c.endpointOfNormal (c.canonicalNormal (c.boundary r₁)) :=
      congrArg c.endpointOfNormal (c.normalizeByBoundary r₁)
    _ = c.endpointOfNormal (c.canonicalNormal (c.boundary r₂)) :=
      congrArg (fun b => c.endpointOfNormal (c.canonicalNormal b)) hsame
    _ = c.endpointOfNormal (c.normalize r₂) :=
      congrArg c.endpointOfNormal (c.normalizeByBoundary r₂).symm
    _ = c.endpoint r₂ := (c.endpointFactors r₂).symm

/-- Direct and factored transports agree when they share one certified
boundary normal form. -/
theorem directFactoredAgreementUnderNormalization
    {Route Boundary Normal Endpoint : Type}
    (c : NormalizationCertificate Route Boundary Normal Endpoint)
    (direct factored : Route)
    (hsame : c.boundary direct = c.boundary factored) :
    c.endpoint direct = c.endpoint factored := by
  exact routeIndependentEndpointUnderNormalization c direct factored hsame

end CSTTT.RouteTheory
