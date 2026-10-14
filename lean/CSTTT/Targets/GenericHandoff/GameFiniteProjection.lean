import CSTTT.Targets.GenericHandoff.GameInvariantCompleteness

/-! Generic converse for a VERIFIED run-to-factor projection. The retention
law is proof evidence on the interpreted game/finite operator, not an assertion
that omitted context is irrelevant. Each raw-model adapter must prove it for
all runs and all comparison sets. Unrestricted recipes need not have such a
law. This pairs with GameFiniteConstructor.LiftWitness without adding a finite
context premise to RawHandoff. -/
namespace CSTTT.TargetTheory.GenericHandoff.GameFiniteProjection
open StrategyGame
variable {X Run Disturbance Action Outcome : Type} [DecidableEq X]

/-- Obligations of an exact factor interpretation. A target response is checked
only when selected; all of its actual positive branches are quantified. -/
structure Laws
    (rows : Rows Run Disturbance Action Outcome)
    (update : Updater Run Disturbance Action Outcome)
    (package resourceClosed : Run → Prop)
    (responseLegal : Run → Disturbance → Action → Prop)
    (transitionLaw : Run → Disturbance → Action → Outcome → Prop)
    (retain : List X → X → Bool) (projection : Run → X) : Prop where
  retention : ∀ S r, package r → resourceClosed r →
    (∀ d, ∃ a, responseLegal r d a ∧ Normalized rows r d a ∧
      ∀ o, PositiveSupport rows r d a o →
        projection (update r d a o) ∈ S ∧ transitionLaw r d a o) →
    retain S (projection r) = true

noncomputable def projected
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    (carrier : List X) (projection : Run → X)
    (cert : InvariantCertificate rows update entries withdrawal package resourceClosed responseLegal transitionLaw) : List X :=
  by
    classical
    exact carrier.filter fun s => decide (∃ r, cert.inside r ∧ projection r = s)

omit [DecidableEq X] in
theorem projected_membership
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    (carrier : List X) (covered : ∀ x, x ∈ carrier) (projection : Run → X)
    (cert : InvariantCertificate rows update entries withdrawal package resourceClosed responseLegal transitionLaw)
    (s : X) : s ∈ projected carrier projection cert ↔ ∃ r, cert.inside r ∧ projection r = s := by
  classical
  simp [projected,covered s]

omit [DecidableEq X] in
theorem projected_viable
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    (carrier : List X) (covered : ∀ x, x ∈ carrier)
    (retain : List X → X → Bool) (projection : Run → X)
    (laws : Laws rows update package resourceClosed responseLegal transitionLaw retain projection)
    (cert : InvariantCertificate rows update entries withdrawal package resourceClosed responseLegal transitionLaw) :
    ViableSet.Viable retain (projected carrier projection cert) := by
  intro s hs
  obtain ⟨r,hr,hproj⟩ := (projected_membership carrier covered projection cert s).mp hs
  rw [← hproj]
  apply laws.retention _ r (cert.packageInside r hr) (cert.resourcesInside r hr)
  intro d
  obtain ⟨a,ha,hn,hnext⟩ := cert.response r hr d
  exact ⟨a,ha,hn,fun o ho => ⟨(projected_membership carrier covered projection cert _).mpr
    ⟨update r d a o,(hnext o ho).1,rfl⟩,(hnext o ho).2⟩⟩

theorem entries_in_greatest
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    (carrier : List X) (covered : ∀ x, x ∈ carrier)
    (retain : List X → X → Bool) (hm : ViableSet.Monotone retain) (projection : Run → X)
    (laws : Laws rows update package resourceClosed responseLegal transitionLaw retain projection)
    (game : GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw) :
    ∀ r, entries r → projection r ∈ ViableSet.greatest carrier retain := by
  obtain ⟨cert⟩ := game_invariant_completeness game
  have hv := projected_viable carrier covered retain projection laws cert
  have hi := ViableSet.greatest_contains_viable carrier covered retain hm _ hv
  intro r hr
  exact hi ((projected_membership carrier covered projection cert _).mpr ⟨r,cert.entriesInside r hr,rfl⟩)

end CSTTT.TargetTheory.GenericHandoff.GameFiniteProjection
