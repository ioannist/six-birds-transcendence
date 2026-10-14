import CSTTT.Corridor.Composition

/-! TTH-04: finite raw overlap legs, not summary propositions.
Source semantics: cst-tt/docs/TEMPORAL_CORRIDOR_SEMANTICS.md:5–17 and
CORRIDOR_COMPOSITION_THEOREM.md:5–18. Readout recipes are raw numerical,
append, and ownership equations checked at EVERY successive stage. Route
status is conservative: retaining a nonempty executed residue licenses indexed
comparison; no flatness assertion is made without a separate completion audit. -/
namespace CSTTT.CorridorTheory.AtomicChain

structure Frontier where
  predictive : Nat
  order : Nat
  tick : Nat
  progress : Nat
  record : Nat
  residue : List String
  maintenance : String
  owner : Nat
  deriving DecidableEq, Repr, Inhabited

structure RawStage where
  support : List Nat
  realized : Bool
  frontier : Frontier
  deriving DecidableEq, Repr, Inhabited

structure RawEvent where
  id : String
  owner : Nat
  stage : Nat
  deriving DecidableEq, Repr, Inhabited

structure RawDependency where
  parent : String
  child : String
  deriving DecidableEq, Repr

/-- Independently recorded local update recipes; no derived verdict fields. -/
structure ReadoutUpdate where
  predictiveAdvance : Nat
  orderAdvance : Nat
  tickAdvance : Nat
  progressAdvance : Nat
  recordAdvance : Nat
  appendResidue : List String
  nextMaintenance : String
  nextOwner : Nat
  deriving DecidableEq, Repr

structure Projection where
  predictive : Nat
  tick : Nat
  record : Nat
  deriving DecidableEq, Repr, Inhabited

def addProjection (a b : Projection) : Projection :=
  ⟨a.predictive+b.predictive,a.tick+b.tick,a.record+b.record⟩

def project (s : RawStage) : Projection :=
  ⟨s.frontier.predictive,s.frontier.tick,s.frontier.record⟩

inductive InterventionMode where | additive | mixedSupport
  deriving DecidableEq, Repr

structure FiniteAtomicLeg where
  interventionMode : InterventionMode := .additive
  source : Nat
  target : Nat
  stages : List RawStage
  events : List RawEvent
  dependencies : List RawDependency
  updates : List ReadoutUpdate
  base : Projection
  sourceContribution : Projection
  targetContribution : Projection
  sourceAudit : String
  targetAudit : String
  laterAudit : String
  deriving DecidableEq, Repr

def entry (l : FiniteAtomicLeg) : RawStage := l.stages.headD default
def exit (l : FiniteAtomicLeg) : RawStage := l.stages.getLastD default

def eventAt (l : FiniteAtomicLeg) (id : String) : Option RawEvent :=
  l.events.find? (fun e => e.id == id)

def dependencyCheck (l : FiniteAtomicLeg) (d : RawDependency) : Bool :=
  match eventAt l d.parent, eventAt l d.child with
  | some a, some b => decide (a.stage < b.stage)
  | _, _ => false

def auditCheck (l : FiniteAtomicLeg) : Bool :=
  match eventAt l l.sourceAudit, eventAt l l.targetAudit, eventAt l l.laterAudit with
  | some s, some t, some e =>
    decide (s.owner = l.source ∧ t.owner = l.target ∧ s.stage = t.stage ∧
      s.stage < e.stage ∧ e.stage + 1 = l.stages.length ∧
      l.source ∈ (l.stages[s.stage]?.getD default).support ∧
      l.target ∈ (l.stages[t.stage]?.getD default).support) &&
    l.dependencies.contains ⟨s.id,e.id⟩ && l.dependencies.contains ⟨t.id,e.id⟩
  | _, _, _ => false

def readoutStep (a b : RawStage) (u : ReadoutUpdate) : Bool :=
  decide (b.frontier.predictive = a.frontier.predictive + u.predictiveAdvance ∧
    u.orderAdvance > 0 ∧ b.frontier.order = a.frontier.order + u.orderAdvance ∧
    u.tickAdvance > 0 ∧ b.frontier.tick = a.frontier.tick + u.tickAdvance ∧
    u.progressAdvance > 0 ∧ b.frontier.progress = a.frontier.progress + u.progressAdvance ∧
    u.recordAdvance > 0 ∧ b.frontier.record = a.frontier.record + u.recordAdvance ∧
    b.frontier.residue = a.frontier.residue ++ u.appendResidue ∧
    u.appendResidue ≠ [] ∧ b.frontier.maintenance = u.nextMaintenance ∧
    u.nextMaintenance ≠ "" ∧ b.frontier.owner = u.nextOwner ∧
    b.frontier.owner ∈ b.support)

/-- Strictness follows from the checked positive increments, not from a
strictness label or a proof field. -/
theorem readout_step_strict (a b : RawStage) (u : ReadoutUpdate)
    (h : readoutStep a b u = true) :
    a.frontier.order < b.frontier.order ∧ a.frontier.tick < b.frontier.tick ∧
    a.frontier.progress < b.frontier.progress ∧ a.frontier.record < b.frontier.record := by
  simp only [readoutStep, decide_eq_true_eq] at h
  rcases h with ⟨_,ho,heo,ht,het,hp,hep,hr,her,_⟩
  omega

def readoutCheck (l : FiniteAtomicLeg) : Bool :=
  decide (l.updates.length + 1 = l.stages.length) &&
  ((l.stages.zip (l.stages.drop 1)).zip l.updates).all
    (fun pair => readoutStep pair.1.1 pair.1.2 pair.2)

/-- Enumerate complete supported event paths, one event at each stage.
The comparison domain is these raw paths, never a list of supplied route labels. -/
def pathsAt (l : FiniteAtomicLeg) : Nat → List (List RawEvent)
  | 0 => (l.events.filter (fun e => e.stage == 0)).map (fun e => [e])
  | n+1 => (pathsAt l n).flatMap fun path =>
      (l.events.filter (fun e => e.stage == n+1 &&
        l.dependencies.contains ⟨(path.getLastD default).id,e.id⟩)).map
        (fun e => path ++ [e])

def routeExecutions (l : FiniteAtomicLeg) : List (List RawEvent) :=
  pathsAt l (l.stages.length - 1)

inductive ComputedRouteStatus where | unavailable | routeIndexed
  deriving DecidableEq, Repr

/-- Execute the raw append recipes; compare to the actual exit register.
This is route-indexed discipline, NOT a claim that growing residue proves
nonflat holonomy. Empty execution/comparison domains cannot certify a status. -/
def routeStatusOf (l : FiniteAtomicLeg) : ComputedRouteStatus :=
  if !(routeExecutions l).isEmpty && !l.dependencies.isEmpty && l.dependencies.all (dependencyCheck l) &&
      !l.updates.isEmpty && !(entry l).frontier.residue.isEmpty &&
      decide (l.updates.foldl (fun r u => r ++ u.appendResidue)
        (entry l).frontier.residue = (exit l).frontier.residue) &&
      readoutCheck l then .routeIndexed else .unavailable

def fullProjection (l : FiniteAtomicLeg) : Projection :=
  addProjection (addProjection l.base l.sourceContribution) l.targetContribution

/-- Both modes execute removal on raw inputs. Additive mode uses the frozen
COR projection rule; mixed-support mode uses POS-04's Boolean conjunction rule.
Neither mode accepts a stored nonredundancy verdict. -/
def mixedCount (l : FiniteAtomicLeg) (remove : Option Nat) : Nat :=
  (l.stages.filter fun s =>
    let support := s.support.filter (fun c => some c != remove)
    s.realized && decide (l.source ∈ support ∧ l.target ∈ support)).length

def interventionCheck (l : FiniteAtomicLeg) : Bool :=
  (match l.interventionMode with
  | .additive => decide (l.base = project (entry l) ∧ fullProjection l = project (exit l) ∧
      fullProjection l ≠ addProjection l.base l.targetContribution ∧
      fullProjection l ≠ addProjection l.base l.sourceContribution)
  | .mixedSupport => decide (mixedCount l none > 0 ∧
      mixedCount l (some l.source) = 0 ∧ mixedCount l (some l.target) = 0)) &&
  auditCheck l

def AtomicLegCheck (l : FiniteAtomicLeg) : Bool :=
  decide (l.source ≠ l.target ∧ l.stages.length ≥ 3 ∧
    (entry l).support = [l.source] ∧ (exit l).support = [l.target] ∧
    (entry l).frontier.owner = l.source ∧ (exit l).frontier.owner = l.target) &&
  l.stages.all (fun s => s.realized && !s.support.isEmpty &&
    decide (s.frontier.owner ∈ s.support ∧ s.frontier.maintenance ≠ "")) &&
  l.stages.any (fun s => decide (l.source ∈ s.support ∧ l.target ∈ s.support)) &&
  (!l.events.isEmpty && decide ((l.events.map (·.id)).eraseDups.length = l.events.length)) &&
  l.events.all (fun e => decide (e.stage < l.stages.length ∧
    e.owner ∈ (l.stages[e.stage]?.getD default).support)) &&
  !l.dependencies.isEmpty && l.dependencies.all (dependencyCheck l) &&
  readoutCheck l && interventionCheck l &&
  decide (routeStatusOf l = .routeIndexed)

def AtomicLegPass (l : FiniteAtomicLeg) : Prop := AtomicLegCheck l = true

/-- Exact shared carrier, complete frontier (including all eight components),
residue and owner. The redundant explicit equations expose the row's interfaces. -/
def AdjacentFrontierCheck (a b : FiniteAtomicLeg) : Bool :=
  decide (a.target = b.source ∧ exit a = entry b ∧
    (exit a).frontier.residue = (entry b).frontier.residue ∧
    (exit a).frontier.owner = (entry b).frontier.owner)

def chainCheck : List FiniteAtomicLeg → Bool
  | [] => true
  | a :: [] => AtomicLegCheck a
  | a :: b :: rest => AtomicLegCheck a && AdjacentFrontierCheck a b && chainCheck (b::rest)

def chainStages : List FiniteAtomicLeg → List RawStage
  | [] => []
  | a :: rest => a.stages ++ (chainStages rest).drop 1

/-- Unscoped projection for comparison with frozen model JSON. The generic
graph below retains leg-scoped IDs; this view is not used as a name-resolution
gate when unrelated legs reuse a local event name. -/
def chainEventsFrom : Nat → List FiniteAtomicLeg → List RawEvent
  | _, [] => []
  | offset, a::rest =>
      a.events.map (fun e => {e with stage := e.stage + offset}) ++
        chainEventsFrom (offset + (a.stages.length - 1)) rest

def chainEvents (legs : List FiniteAtomicLeg) : List RawEvent :=
  (chainEventsFrom 0 legs).eraseDups

def chainDependencies (legs : List FiniteAtomicLeg) : List RawDependency :=
  (legs.flatMap (·.dependencies)).eraseDups

/-- The generic event graph uses leg-scoped IDs, so unrelated events with
identical local names cannot collide. Shared STAGES are merged; event vertices
need not have the same local name to represent that exact temporal frontier. -/
structure ScopedEvent where
  leg : Nat
  localId : String
  owner : Nat
  stage : Nat
  deriving DecidableEq, Repr

structure ScopedDependency where
  leg : Nat
  parent : String
  child : String
  deriving DecidableEq, Repr

def scopedEventsFrom : Nat → Nat → List FiniteAtomicLeg → List ScopedEvent
  | _, _, [] => []
  | k, offset, a::rest =>
      a.events.map (fun e => ⟨k,e.id,e.owner,e.stage+offset⟩) ++
        scopedEventsFrom (k+1) (offset + (a.stages.length-1)) rest

def scopedDependenciesFrom : Nat → List FiniteAtomicLeg → List ScopedDependency
  | _, [] => []
  | k, a::rest => a.dependencies.map (fun d => ⟨k,d.parent,d.child⟩) ++
      scopedDependenciesFrom (k+1) rest

def constructedEvents := scopedEventsFrom 0 0
def constructedDependencies := scopedDependenciesFrom 0

/-- Explicit inductive derivation, rather than a supplied corridor summary. -/
inductive ChainDerivation : List FiniteAtomicLeg → Prop
  | single (a) : AtomicLegPass a → ChainDerivation [a]
  | prepend (a b rest) : AtomicLegPass a → AdjacentFrontierCheck a b = true →
      ChainDerivation (b::rest) → ChainDerivation (a::b::rest)

def CorridorPass (legs : List FiniteAtomicLeg) : Prop :=
  legs ≠ [] ∧ chainCheck legs = true ∧
  (legs.head?.map (·.source)) ≠ (legs.getLast?.map (·.target))

def chainReadoutEdges (legs : List FiniteAtomicLeg) :
    List ((RawStage × RawStage) × ReadoutUpdate) :=
  legs.flatMap fun l => (l.stages.zip (l.stages.drop 1)).zip l.updates


/-- Every derived data object is a definition, never an argument or a field.
The witness carries ONLY proofs about those computed objects. -/
structure StrictCorridorWitness (legs : List FiniteAtomicLeg) : Prop where
  pass : CorridorPass legs
  derivation : ChainDerivation legs
  readoutLaws : ∀ l ∈ legs, readoutCheck l = true
  realized : ∀ s ∈ chainStages legs, s.realized = true
  strictSteps : ∀ edge ∈ chainReadoutEdges legs,
    edge.1.1.frontier.order < edge.1.2.frontier.order ∧
    edge.1.1.frontier.tick < edge.1.2.frontier.tick ∧
    edge.1.1.frontier.progress < edge.1.2.frontier.progress ∧
    edge.1.1.frontier.record < edge.1.2.frontier.record

 theorem chain_derivation (legs : List FiniteAtomicLeg) (hne : legs ≠ [])
    (h : chainCheck legs = true) : ChainDerivation legs := by
  induction legs with
  | nil => contradiction
  | cons a rest ih =>
    cases rest with
    | nil => exact .single a h
    | cons b tail =>
      simp only [chainCheck, Bool.and_eq_true] at h
      exact .prepend a b tail h.1.1 h.1.2 (ih (by simp) h.2)

 theorem chain_each_pass (legs : List FiniteAtomicLeg) (h : chainCheck legs = true) :
    ∀ l ∈ legs, AtomicLegPass l := by
  induction legs with
  | nil => simp
  | cons a rest ih =>
    cases rest with
    | nil => simpa [chainCheck, AtomicLegPass] using h
    | cons b tail =>
      simp only [chainCheck, Bool.and_eq_true] at h
      intro l hl
      simp only [List.mem_cons] at hl
      rcases hl with rfl | hl
      · exact h.1.1
      · exact ih h.2 l (by simpa only [List.mem_cons] using hl)

 theorem atomic_readout_laws (l) (h : AtomicLegPass l) : readoutCheck l = true := by
  simp only [AtomicLegPass, AtomicLegCheck, Bool.and_eq_true] at h
  exact h.1.1.2

 theorem atomic_realized (l) (h : AtomicLegPass l) :
    ∀ s ∈ l.stages, s.realized = true := by
  simp only [AtomicLegPass, AtomicLegCheck, Bool.and_eq_true] at h
  have hs := h.1.1.1.1.1.1.1.1.2
  intro s hm
  have := List.all_eq_true.mp hs s hm
  simp only [Bool.and_eq_true] at this
  exact this.1.1

 theorem chain_realized (legs) (h : chainCheck legs = true) :
    ∀ s ∈ chainStages legs, s.realized = true := by
  induction legs with
  | nil => simp [chainStages]
  | cons a rest ih =>
    have ha : AtomicLegPass a := chain_each_pass _ h a (by simp)
    have ht : chainCheck rest = true := by
      cases rest with
      | nil => rfl
      | cons b tail =>
        simp only [chainCheck, Bool.and_eq_true] at h
        exact h.2
    intro s hs
    simp only [chainStages, List.mem_append] at hs
    rcases hs with hs | hs
    · exact atomic_realized a ha s hs
    · exact ih ht s (List.mem_of_mem_drop hs)

/-- The boundary comparison is computed by traversing to the last leg. -/
def boundaryCheck : List FiniteAtomicLeg → List FiniteAtomicLeg → Bool
  | [], _ => false
  | [_], [] => false
  | [a], b::_ => AdjacentFrontierCheck a b
  | _::b::rest, right => boundaryCheck (b::rest) right

theorem derivation_check {legs} (h : ChainDerivation legs) : chainCheck legs = true := by
  induction h with
  | single a ha => exact ha
  | prepend a b rest ha hj _ ih =>
    simp only [chainCheck, Bool.and_eq_true]
    exact ⟨⟨ha,hj⟩,ih⟩

theorem derivation_append {left right} (hl : ChainDerivation left)
    (hr : ChainDerivation right) (hj : boundaryCheck left right = true) :
    ChainDerivation (left ++ right) := by
  induction hl with
  | single a ha =>
    cases hr with
    | single b hb => exact .prepend a b [] ha hj (.single b hb)
    | prepend b c rest hb hbc ht =>
      exact .prepend a b (c::rest) ha hj (.prepend b c rest hb hbc ht)
  | prepend a b rest ha hab ht ih =>
    exact .prepend a b (rest ++ right) ha hab (ih hj)

/-- Each realized advancing pair in the constructed trace has its own recipe.
At joins there is ONE identical boundary stage, not a zero-length extra edge. -/
theorem chain_readout_steps (legs) (h : CorridorPass legs) :
    ∀ edge ∈ chainReadoutEdges legs,
      readoutStep edge.1.1 edge.1.2 edge.2 = true := by
  intro edge he
  simp only [chainReadoutEdges, List.mem_flatMap] at he
  obtain ⟨l,hl,he⟩ := he
  have hc := atomic_readout_laws l (chain_each_pass _ h.2.1 l hl)
  simp only [readoutCheck, Bool.and_eq_true] at hc
  exact List.all_eq_true.mp hc.2 edge he

/-- Generic TTH-04. Induction constructs the atomic derivation for any nonempty
chain; every update law is checked throughout the chain, including exact joins. -/
theorem strictTemporalCorridorComposition_generic (legs : List FiniteAtomicLeg)
    (h : CorridorPass legs) : StrictCorridorWitness legs := by
  exact ⟨h, chain_derivation legs h.1 h.2.1,
    fun l hl => atomic_readout_laws l (chain_each_pass _ h.2.1 l hl),
    chain_realized legs h.2.1,
    fun edge he => readout_step_strict _ _ _ (chain_readout_steps legs h edge he)⟩

/-- Binary form of the accepted G0 contract. The raw lists are appended,
interfaces recomputed, and the atomic derivation is built by induction. -/
theorem append_corridor (left right : List FiniteAtomicLeg)
    (hl : CorridorPass left) (hr : CorridorPass right)
    (hj : boundaryCheck left right = true)
    (hd : ((left ++ right).head?.map (·.source)) ≠
      ((left ++ right).getLast?.map (·.target))) :
    StrictCorridorWitness (left ++ right) := by
  have d := derivation_append (chain_derivation _ hl.1 hl.2.1)
    (chain_derivation _ hr.1 hr.2.1) hj
  apply strictTemporalCorridorComposition_generic
  exact ⟨by intro he; exact hl.1 (List.append_eq_nil_iff.mp he).1,
    derivation_check d, hd⟩

end CSTTT.CorridorTheory.AtomicChain
