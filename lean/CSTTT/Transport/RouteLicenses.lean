import CSTTT.Core.Finite

/-! G3c, frozen audit/G3_route_spec.md:22–102. Raw event paths, actions,
rewrites, completion paths and clock translations determine all readouts.
Flatness is the stronger adopted G3a license, not an endpoint-coincidence test.
The generic clock table is a forward/backward translation pair; its inverse
and action-coherence equations are checked by the flat license. Z/2 clocks
in the finite instances instantiate this representation exactly. -/
namespace CSTTT.RouteLicenses

structure EventData (Vertex State : Type) where
  entry : Vertex
  exit : Vertex
  available : Bool
  action : State → State
  clockForward : State → State
  clockBackward : State → State
structure BoundaryData (Vertex State : Type) where
  entry : Vertex
  exit : Vertex
  initial : State
structure Completion (Route : Type) where
  left : Route
  right : Route
  join : Route
  leftPath : List Route
  rightPath : List Route
  deriving DecidableEq
structure RawSystem (Route Event Boundary Vertex State : Type) where
  path : Route → List Event
  boundary : Route → Boundary
  events : Event → EventData Vertex State
  boundaries : Boundary → BoundaryData Vertex State
  rewrites : List (Route × Route)
  rank : Route → Nat
  critical : List (Route × Route)
  completions : List (Completion Route)
structure Domain (Route Boundary : Type) where
  boundary : Boundary
  routes : List Route

variable {R E B V S : Type} [DecidableEq B]

def execWord (m : RawSystem R E B V S) : List E → S → S
  | [], x => x
  | e :: es, x => execWord m es ((m.events e).action x)
def endpoint (m : RawSystem R E B V S) (r : R) : S :=
  execWord m (m.path r) (m.boundaries (m.boundary r)).initial
def clockWord (m : RawSystem R E B V S) : List E → S → S
  | [], x => x
  | e :: es, x => clockWord m es ((m.events e).clockForward x)
def inverseClockWord (m : RawSystem R E B V S) : List E → S → S
  | [], x => x
  | e :: es, x => (m.events e).clockBackward (inverseClockWord m es x)

def vertexPath (m : RawSystem R E B V S) : List E → V → V → Prop
  | [], a, b => a = b
  | e :: es, a, b => (m.events e).entry = a ∧ vertexPath m es (m.events e).exit b
structure Admissible (m : RawSystem R E B V S) (r : R) : Prop where
  available : ∀ e ∈ m.path r, (m.events e).available = true
  vertices : vertexPath m (m.path r) (m.boundaries (m.boundary r)).entry (m.boundaries (m.boundary r)).exit
structure DomainCheck (m : RawSystem R E B V S) (d : Domain R B) : Prop where
  distinct : ∃ r ∈ d.routes, ∃ s ∈ d.routes, m.path r ≠ m.path s
  noDuplicates : (d.routes.map m.path).Nodup
  admissible : ∀ r ∈ d.routes, Admissible m r
  boundary : ∀ r ∈ d.routes, m.boundary r = d.boundary
  closed : ∀ r ∈ d.routes, ∀ s, (r,s) ∈ m.rewrites → s ∈ d.routes

def rewrite (m : RawSystem R E B V S) (d : Domain R B) (r s : R) : Prop :=
  r ∈ d.routes ∧ s ∈ d.routes ∧ (r,s) ∈ m.rewrites
inductive Reach (edge : R → R → Prop) : R → R → Prop where
  | refl (r) : Reach edge r r
  | step {r s t} : edge r s → Reach edge s t → Reach edge r t

def terminal (d : Domain R B) (edge : R → R → Prop) (r : R) : Prop :=
  ∀ s ∈ d.routes, ¬ edge r s
/-- Singleton terminal images shared across the declared boundary; no normal
form/normalizer is a raw or candidate argument. -/
def SharedNormal (d : Domain R B) (edge : R → R → Prop) : Prop :=
  ∃ n ∈ d.routes, terminal d edge n ∧
    ∀ r ∈ d.routes, Reach edge r n ∧
      ∀ z ∈ d.routes, Reach edge r z → terminal d edge z → z = n

def RewriteBoundary (m : RawSystem R E B V S) (d : Domain R B) : Prop :=
  ∀ r ∈ d.routes, ∀ s, (r,s) ∈ m.rewrites → s ∈ d.routes ∧ m.boundary r = m.boundary s
def RewriteActions (m : RawSystem R E B V S) (d : Domain R B) : Prop :=
  ∀ r ∈ d.routes, ∀ s, (r,s) ∈ m.rewrites → ∀ x, execWord m (m.path r) x = execWord m (m.path s) x
structure NormalizationLicense (m : RawSystem R E B V S) (d : Domain R B) : Prop where
  domain : DomainCheck m d
  boundary : RewriteBoundary m d
  decreasing : ∀ r ∈ d.routes, ∀ s, (r,s) ∈ m.rewrites → m.rank s < m.rank r
  actions : RewriteActions m d
  normal : SharedNormal d (rewrite m d)
structure ConfluenceLicense (m : RawSystem R E B V S) (d : Domain R B) : Prop where
  domain : DomainCheck m d
  boundary : RewriteBoundary m d
  actions : RewriteActions m d
  joinable : ∀ r ∈ d.routes, ∀ s ∈ d.routes,
    ∃ j ∈ d.routes, Reach (rewrite m d) r j ∧ Reach (rewrite m d) s j

def criticalPairs (m : RawSystem R E B V S) (d : Domain R B) :=
  m.critical.filter fun p => decide (m.boundary p.1 = d.boundary ∨ m.boundary p.2 = d.boundary)
def completionRows (m : RawSystem R E B V S) (d : Domain R B) :=
  m.completions.filter fun c => decide (m.boundary c.left = d.boundary ∨ m.boundary c.right = d.boundary)
def rewritePath (m : RawSystem R E B V S) (d : Domain R B) : List R → R → R → Prop
  | [], _, _ => False
  | [a], r, s => a = r ∧ a = s ∧ a ∈ d.routes
  | a :: b :: tail, r, s => a = r ∧ rewrite m d a b ∧ rewritePath m d (b :: tail) b s

def CompletionValid (m : RawSystem R E B V S) (d : Domain R B) (c : Completion R) : Prop :=
  (c.left,c.right) ∈ criticalPairs m d ∧ c.join ∈ d.routes ∧
  rewritePath m d c.leftPath c.left c.join ∧ rewritePath m d c.rightPath c.right c.join

def move (m : RawSystem R E B V S) (d : Domain R B) (r s : R) : Prop :=
  ∃ c ∈ completionRows m d, (c.left = r ∧ c.right = s) ∨ (c.left = s ∧ c.right = r)
def reduction (m : RawSystem R E B V S) (d : Domain R B) (r s : R) : Prop :=
  ∃ c ∈ completionRows m d, (r = c.left ∨ r = c.right) ∧ s = c.join ∧ r ≠ s
/-- Check local raw action equations along every supplied completion path. -/
def CompletionActions (m : RawSystem R E B V S) (d : Domain R B) : Prop :=
  ∀ c ∈ completionRows m d, ∀ path ∈ [c.leftPath,c.rightPath],
    ∀ p ∈ path.zip path.tail, ∀ x, execWord m (m.path p.1) x = execWord m (m.path p.2) x
structure FlatLicense (m : RawSystem R E B V S) (d : Domain R B) : Prop where
  domain : DomainCheck m d
  clockActions : ∀ e, (m.events e).available = true → ∀ x, (m.events e).action x = (m.events e).clockForward x
  clockInverse : ∀ e, (m.events e).available = true → ∀ x,
    (m.events e).clockForward ((m.events e).clockBackward x) = x ∧
    (m.events e).clockBackward ((m.events e).clockForward x) = x
  nonempty : (criticalPairs m d).length > 0
  pairs : ∀ p ∈ criticalPairs m d, p.1 ∈ d.routes ∧ p.2 ∈ d.routes ∧
    m.boundary p.1 = d.boundary ∧ m.boundary p.2 = d.boundary ∧ m.path p.1 ≠ m.path p.2
  covers : ∀ r ∈ d.routes, ∃ p ∈ criticalPairs m d, r = p.1 ∨ r = p.2
  completed : ∀ p ∈ criticalPairs m d, ∃ c ∈ completionRows m d, c.left = p.1 ∧ c.right = p.2
  valid : ∀ c ∈ completionRows m d, CompletionValid m d c
  connected : ∀ r ∈ d.routes, ∀ s ∈ d.routes, Reach (move m d) r s
  decreasing : ∀ r s, reduction m d r s → m.rank s < m.rank r
  normal : SharedNormal d (reduction m d)
  actions : CompletionActions m d
  zero : ∀ c ∈ completionRows m d, ∀ x,
    inverseClockWord m (m.path c.right) (clockWord m (m.path c.left) x) = x

def RouteLicense (m : RawSystem R E B V S) (d : Domain R B) : Prop :=
  NormalizationLicense m d ∨ FlatLicense m d ∨ ConfluenceLicense m d

omit [DecidableEq B] in
theorem reach_execution {m : RawSystem R E B V S} {d : Domain R B}
    (h : RewriteActions m d) {r s} (hr : Reach (rewrite m d) r s) (x : S) :
    execWord m (m.path r) x = execWord m (m.path s) x := by
  induction hr with
  | refl => rfl
  | step he _ ih => exact (h _ he.1 _ he.2.2 x).trans ih

omit [DecidableEq B] in
theorem normalization_sufficient (m : RawSystem R E B V S) (d : Domain R B)
    (h : NormalizationLicense m d) (r s : R) (hr : r ∈ d.routes) (hs : s ∈ d.routes) :
    endpoint m r = endpoint m s := by
  obtain ⟨n,_,_,hn⟩ := h.normal
  have he : ∀ x, execWord m (m.path r) x = execWord m (m.path s) x := fun x =>
    (reach_execution h.actions (hn r hr).1 x).trans (reach_execution h.actions (hn s hs).1 x).symm
  unfold endpoint
  rw [h.domain.boundary r hr,h.domain.boundary s hs]
  exact he _

omit [DecidableEq B] in
theorem confluence_sufficient (m : RawSystem R E B V S) (d : Domain R B)
    (h : ConfluenceLicense m d) (r s : R) (hr : r ∈ d.routes) (hs : s ∈ d.routes) :
    endpoint m r = endpoint m s := by
  obtain ⟨j,_,hj,hk⟩ := h.joinable r hr s hs
  unfold endpoint
  rw [h.domain.boundary r hr,h.domain.boundary s hs]
  exact (reach_execution h.actions hj _).trans (reach_execution h.actions hk _).symm

theorem action_clock_word {m : RawSystem R E B V S} {d} (h : FlatLicense m d)
    (word : List E) (ha : ∀ e ∈ word, (m.events e).available = true) (x : S) :
    execWord m word x = clockWord m word x := by
  induction word generalizing x with
  | nil => rfl
  | cons e es ih =>
    simp only [execWord,clockWord]
    rw [h.clockActions e (ha e (by simp)) x]
    exact ih (fun e he => ha e (by simp [he])) _

theorem clock_inverse_word {m : RawSystem R E B V S} {d} (h : FlatLicense m d)
    (word : List E) (ha : ∀ e ∈ word, (m.events e).available = true) (x : S) :
    clockWord m word (inverseClockWord m word x) = x := by
  induction word generalizing x with
  | nil => rfl
  | cons e es ih =>
    simp only [clockWord,inverseClockWord]
    rw [(h.clockInverse e (ha e (by simp)) _).1]
    exact ih (fun e he => ha e (by simp [he])) x

theorem completed_execution {m : RawSystem R E B V S} {d} (h : FlatLicense m d)
    (c : Completion R) (hc : c ∈ completionRows m d) (x : S) :
    execWord m (m.path c.left) x = execWord m (m.path c.right) x := by
  have hp := h.pairs _ (h.valid c hc).1
  have ha := (h.domain.admissible _ hp.1).available
  have hb := (h.domain.admissible _ hp.2.1).available
  rw [action_clock_word h _ ha x,action_clock_word h _ hb x]
  have hz := congrArg (clockWord m (m.path c.right)) (h.zero c hc x)
  rw [clock_inverse_word h _ hb _] at hz
  exact hz

theorem flatness_sufficient (m : RawSystem R E B V S) (d : Domain R B)
    (h : FlatLicense m d) (r s : R) (hr : r ∈ d.routes) (hs : s ∈ d.routes) :
    endpoint m r = endpoint m s := by
  have hm : ∀ u v, move m d u v → ∀ x, execWord m (m.path u) x = execWord m (m.path v) x := by
    intro u v ⟨c,hc,he⟩ x
    rcases he with ⟨hl,hr⟩ | ⟨hl,hr⟩
    · subst u; subst v; exact completed_execution h c hc x
    · subst v; subst u; exact (completed_execution h c hc x).symm
  have he := h.connected r hr s hs
  have hf : ∀ u v, Reach (move m d) u v → ∀ x, execWord m (m.path u) x = execWord m (m.path v) x := by
    intro u v hh x
    induction hh with
    | refl => rfl
    | step ht _ ih => exact (hm _ _ ht x).trans ih
  unfold endpoint
  rw [h.domain.boundary r hr,h.domain.boundary s hs]
  exact hf r s he _

theorem domain_rejection_excludes_licenses {m : RawSystem R E B V S} {d : Domain R B}
    (h : ¬ DomainCheck m d) : ¬ RouteLicense m d := by
  rintro (hl | hl | hl)
  · exact h hl.domain
  · exact h hl.domain
  · exact h hl.domain

theorem routeIndependentEndpoint_generic (m : RawSystem R E B V S) (d : Domain R B)
    (r s : R) (hr : r ∈ d.routes) (hs : s ∈ d.routes) (h : RouteLicense m d) :
    endpoint m r = endpoint m s := by
  rcases h with h | h | h
  · exact normalization_sufficient m d h r s hr hs
  · exact flatness_sufficient m d h r s hr hs
  · exact confluence_sufficient m d h r s hr hs
end CSTTT.RouteLicenses
