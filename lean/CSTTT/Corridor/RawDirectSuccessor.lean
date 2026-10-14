import CSTTT.Corridor.AtomicChain

/-! Raw direct-successor foundation, classification (b).
The receiver instruction stays fixed under source removal and token consumption.
Generation, complete payload, provenance, adjacency and ownership checks are
computed from raw inputs. Every partial source assignment is covered.
Positive controls are separately declared before evaluation; this foundation
alone does not establish incomparability or promote any TTD row. -/
namespace CSTTT.CorridorTheory.RawDirectSuccessor
open CSTTT.CorridorTheory.AtomicChain

abbrev EventId := String

inductive Provenance where | live | detached | archive | store
  deriving DecidableEq
inductive Kind where | liveTemporal | copy | replay | storage
  deriving DecidableEq
structure Token where
  id : Nat
  used : Bool
structure SourceEvent where
  stage : Nat
  payload : Option Frontier
  token : Option Token
  present : Bool
  provenance : Provenance
structure Edge where
  parent : EventId
  child : EventId
  kind : Kind
  deriving DecidableEq
structure Raw where
  sourceEvent : EventId
  targetEvent : EventId
  edges : List Edge
  receiver : ReadoutUpdate
abbrev Assignment := EventId → Option SourceEvent
structure Capsule where
  input : SourceEvent
  payload : Frontier
  token : Token
structure Delivered where
  parent : EventId
  child : EventId
  kind : Kind
  sourcePayload : Frontier
  frontier : Frontier
  stage : Nat
  consumedToken : Token

def incoming (raw : Raw) := raw.edges.filter (fun e => e.child==raw.targetEvent)
def decode (a : Assignment) (parent : EventId) : Option Capsule := do
  let input ← a parent
  let payload ← input.payload
  let token ← input.token
  pure ⟨input,payload,token⟩
def Ready (a : Assignment) (parent : EventId) : Prop :=
  ∃ input payload token, a parent=some input ∧ input.payload=some payload ∧ input.token=some token
theorem decode_ready_iff (a : Assignment) (parent : EventId) : (decode a parent).isSome=true ↔ Ready a parent := by
  cases ha : a parent with
  | none => simp [decode,Ready,ha]
  | some input =>
    cases hp : input.payload <;> cases ht : input.token <;> simp [decode,Ready,ha,hp,ht]

theorem decoded_fields (a : Assignment) (parent : EventId) (c : Capsule)
    (h : decode a parent=some c) :
    a parent=some c.input ∧ c.input.payload=some c.payload ∧ c.input.token=some c.token := by
  cases hi : a parent with
  | none => simp [decode,hi] at h
  | some input =>
    cases hp : input.payload with
    | none => simp [decode,hi,hp] at h
    | some payload =>
      cases ht : input.token with
      | none => simp [decode,hi,hp,ht] at h
      | some token =>
        simp [decode,hi,hp,ht] at h
        cases h
        exact ⟨rfl,hp,ht⟩

def advance (u : ReadoutUpdate) (s : Frontier) : Frontier :=
  ⟨s.predictive+u.predictiveAdvance,s.order+u.orderAdvance,s.tick+u.tickAdvance,
    s.progress+u.progressAdvance,s.record+u.recordAdvance,s.residue++u.appendResidue,u.nextMaintenance,u.nextOwner⟩
def deliver (raw : Raw) (edge : Edge) (capsule : Capsule) : Delivered :=
  ⟨edge.parent,edge.child,edge.kind,capsule.payload,advance raw.receiver capsule.payload,
    capsule.input.stage+1,{capsule.token with used := true}⟩
def emit (raw : Raw) (a : Assignment) (edge : Edge) : Option Delivered := do
  let capsule ← decode a edge.parent
  if capsule.input.present && !capsule.token.used then
    pure (deliver raw edge capsule)
  else none
def generated (raw : Raw) (a : Assignment) : List Delivered :=
  (incoming raw).filterMap (emit raw a)
def deleteSource (raw : Raw) (a : Assignment) : Assignment :=
  fun event => if event=raw.sourceEvent then none else a event
def consumeSource (raw : Raw) (a : Assignment) : Assignment :=
  fun event => if event=raw.sourceEvent then
    (a event).map (fun input => {input with token := input.token.map (fun token => {token with used := true})})
    else a event

theorem missing_emit (raw : Raw) (a : Assignment) (edge : Edge) (h : a edge.parent=none) :
    emit raw a edge=none := by simp [emit,decode,h]
theorem necessary_source_generation (raw : Raw) (a : Assignment) (edge : Edge)
    (unique : incoming raw=[edge]) (parent : edge.parent=raw.sourceEvent) :
    generated raw (deleteSource raw a)=[] := by
  unfold generated
  rw [unique]
  have hm : deleteSource raw a edge.parent=none := by simp [deleteSource,parent]
  simp [missing_emit raw _ edge hm]
theorem consumed_source_emit (raw : Raw) (a : Assignment) (edge : Edge)
    (parent : edge.parent=raw.sourceEvent) : emit raw (consumeSource raw a) edge=none := by
  cases ha : a raw.sourceEvent with
  | none => apply missing_emit; simp [consumeSource,parent,ha]
  | some input =>
    simp only [emit,decode,consumeSource,parent,ite_true,ha,Option.map_some,Option.bind_some]
    cases hp : input.payload <;> cases ht : input.token <;> simp [hp,ht]
theorem single_use_generation (raw : Raw) (a : Assignment) (edge : Edge)
    (unique : incoming raw=[edge]) (parent : edge.parent=raw.sourceEvent) :
    generated raw (consumeSource raw a)=[] := by
  unfold generated
  rw [unique]
  simp [consumed_source_emit raw a edge parent]

def EmissionReady (a : Assignment) (parent : EventId) : Prop :=
  ∃ capsule, decode a parent=some capsule ∧
    capsule.input.present=true ∧ capsule.token.used=false

theorem emit_ready_iff (raw : Raw) (a : Assignment) (edge : Edge) :
    (emit raw a edge).isSome=true ↔ EmissionReady a edge.parent := by
  cases hd : decode a edge.parent with
  | none => simp [emit,EmissionReady,hd]
  | some capsule =>
    cases hp : capsule.input.present <;> cases ht : capsule.token.used <;>
      simp [emit,EmissionReady,hd,hp,ht]

theorem emission_exact (raw : Raw) (a : Assignment) (edge : Edge) (d : Delivered) :
    emit raw a edge=some d ↔
    ∃ capsule, decode a edge.parent=some capsule ∧
      capsule.input.present=true ∧ capsule.token.used=false ∧
      d=deliver raw edge capsule := by
  cases hd : decode a edge.parent with
  | none => simp [emit,hd]
  | some capsule =>
    cases hp : capsule.input.present <;> cases ht : capsule.token.used <;>
      simp [emit,hd,hp,ht]
    exact eq_comm

theorem missing_payload_emit (raw : Raw) (a : Assignment) (edge : Edge)
    (input : SourceEvent) (hi : a edge.parent=some input) (hp : input.payload=none) :
    emit raw a edge=none := by simp [emit,decode,hi,hp]

theorem missing_token_emit (raw : Raw) (a : Assignment) (edge : Edge)
    (input : SourceEvent) (hi : a edge.parent=some input) (ht : input.token=none) :
    emit raw a edge=none := by
  cases hp : input.payload <;> simp [emit,decode,hi,hp,ht]

theorem source_token_reuse_rejected (raw : Raw) (a : Assignment) (edge : Edge)
    (input : SourceEvent) (token : Token) (hi : a edge.parent=some input)
    (ht : input.token=some token) (hu : token.used=true) :
    emit raw a edge=none := by
  cases hp : input.payload <;> simp [emit,decode,hi,hp,ht,hu]

theorem empty_incoming_no_generation (raw : Raw) (a : Assignment)
    (h : incoming raw=[]) : generated raw a=[] := by simp [generated,h]

theorem complete_payload_and_consumption (raw : Raw) (a : Assignment)
    (edge : Edge) (d : Delivered) (h : emit raw a edge=some d) :
    ∃ capsule, decode a edge.parent=some capsule ∧
      d.sourcePayload=capsule.payload ∧
      d.frontier=advance raw.receiver capsule.payload ∧
      d.stage=capsule.input.stage+1 ∧
      d.consumedToken.id=capsule.token.id ∧ d.consumedToken.used=true := by
  obtain ⟨capsule,hc,_,_,rfl⟩ := (emission_exact raw a edge d).mp h
  exact ⟨capsule,hc,rfl,rfl,rfl,rfl,rfl⟩

structure Boundary where
  sourceCarrier : Nat
  targetCarrier : Nat
  source : RawStage
  target : RawStage
  sourceStage : Nat
  targetStage : Nat

/-- Finite raw equalities and the existing full-frontier update checker.
No certificate verdict is stored in these observations. -/
def Geometry (raw : Raw) (b : Boundary) (edge : Edge) (c : Capsule) : Prop :=
  b.sourceCarrier ≠ b.targetCarrier ∧
  edge.parent=raw.sourceEvent ∧ edge.child=raw.targetEvent ∧
  edge.kind=.liveTemporal ∧ c.input.provenance=.live ∧
  b.source.realized=true ∧ b.target.realized=true ∧
  b.source.support=[b.sourceCarrier] ∧ b.target.support=[b.targetCarrier] ∧
  b.source.frontier.owner=b.sourceCarrier ∧ b.target.frontier.owner=b.targetCarrier ∧
  c.payload=b.source.frontier ∧
  c.input.stage+1=b.targetStage ∧
  b.target.frontier=advance raw.receiver c.payload ∧
  readoutStep b.source b.target raw.receiver=true ∧ c.input.stage=b.sourceStage ∧
  raw.sourceEvent≠raw.targetEvent
instance geometryDecidable (raw : Raw) (b : Boundary) (edge : Edge) (c : Capsule) :
    Decidable (Geometry raw b edge c) := inferInstanceAs (Decidable (_ ∧ _))

def directCheck (raw : Raw) (b : Boundary) (a : Assignment) : Bool :=
  match incoming raw with
  | [edge] => match decode a edge.parent with
    | some c => c.input.present && !c.token.used && decide (Geometry raw b edge c)
    | none => false
  | _ => false

def ImmediateDirect (raw : Raw) (b : Boundary) (a : Assignment) : Prop :=
  directCheck raw b a=true

theorem direct_readout_iff (raw : Raw) (b : Boundary) (a : Assignment) :
    ImmediateDirect raw b a ↔
    ∃ edge c, incoming raw=[edge] ∧ decode a edge.parent=some c ∧
      c.input.present=true ∧ c.token.used=false ∧ Geometry raw b edge c := by
  cases hi : incoming raw with
  | nil => simp [ImmediateDirect,directCheck,hi]
  | cons edge rest =>
    cases rest with
    | nil =>
      cases hd : decode a edge.parent with
      | none => simp [ImmediateDirect,directCheck,hi,hd]
      | some c =>
        cases hp : c.input.present <;> cases ht : c.token.used <;>
          simp [ImmediateDirect,directCheck,hi,hd,hp,ht]
    | cons e es => simp [ImmediateDirect,directCheck,hi]

theorem direct_constructive_generation (raw : Raw) (b : Boundary) (a : Assignment)
    (h : ImmediateDirect raw b a) :
    ∃ edge c, incoming raw=[edge] ∧ Geometry raw b edge c ∧
      generated raw a=[deliver raw edge c] ∧
      generated raw (deleteSource raw a)=[] ∧
      generated raw (consumeSource raw a)=[] := by
  obtain ⟨edge,c,hi,hd,hp,ht,hg⟩ := (direct_readout_iff raw b a).mp h
  have parent : edge.parent=raw.sourceEvent := hg.2.1
  have emitted : emit raw a edge=some (deliver raw edge c) := by
    simp [emit,hd,hp,ht]
  refine ⟨edge,c,hi,hg,?_,necessary_source_generation raw a edge hi parent,
    single_use_generation raw a edge hi parent⟩
  simp [generated,hi,emitted]

theorem no_generated_target_not_direct (raw : Raw) (b : Boundary) (a : Assignment)
    (h : generated raw a=[]) : ¬ ImmediateDirect raw b a := by
  intro hd
  obtain ⟨edge,c,_,_,he,_⟩ := direct_constructive_generation raw b a hd
  rw [h] at he
  cases he

theorem source_removed_not_direct (raw : Raw) (b : Boundary) (a : Assignment)
    (h : ImmediateDirect raw b a) :
    ¬ ImmediateDirect raw b (deleteSource raw a) := by
  obtain ⟨_,_,_,_,_,he,_⟩ := direct_constructive_generation raw b a h
  exact no_generated_target_not_direct raw b _ he

theorem token_consumed_not_direct (raw : Raw) (b : Boundary) (a : Assignment)
    (h : ImmediateDirect raw b a) :
    ¬ ImmediateDirect raw b (consumeSource raw a) := by
  obtain ⟨_,_,_,_,_,_,he⟩ := direct_constructive_generation raw b a h
  exact no_generated_target_not_direct raw b _ he

/-- Consume the token identity throughout the actual input state; aliases
cannot regain a consumed token by selecting another event cell. -/
def consumeToken (key : Nat) (a : Assignment) : Assignment := fun event =>
  (a event).map fun input => {input with token := input.token.map fun token =>
    if token.id=key then {token with used := true} else token}

theorem consumed_token_alias_emit (raw : Raw) (a : Assignment) (edge : Edge)
    (input : SourceEvent) (token : Token) (key : Nat)
    (hi : a edge.parent=some input) (ht : input.token=some token) (hk : token.id=key) :
    emit raw (consumeToken key a) edge=none := by
  cases hp : input.payload <;> simp [emit,decode,consumeToken,hi,ht,hk,hp]

/-- The state update is executed alongside successful delivery. -/
def fire (raw : Raw) (a : Assignment) : Option (Delivered × Assignment) :=
  match generated raw a with
  | [d] => some (d,consumeToken d.consumedToken.id a)
  | _ => none

theorem actual_fire_single_use (raw : Raw) (b : Boundary) (a : Assignment)
    (h : ImmediateDirect raw b a) :
    ∃ d next, fire raw a=some (d,next) ∧
      generated raw next=[] ∧ fire raw next=none ∧ ¬ ImmediateDirect raw b next := by
  obtain ⟨edge',c',hi,hd,hpresent,hunused,_⟩ := (direct_readout_iff raw b a).mp h
  obtain ⟨ha,hp,htoken⟩ := decoded_fields a edge'.parent c' hd
  have hg' : generated raw a=[deliver raw edge' c'] := by
    have emitted : emit raw a edge'=some (deliver raw edge' c') := by
      simp [emit,hd,hpresent,hunused]
    simp [generated,hi,emitted]
  have empty : generated raw (consumeToken c'.token.id a)=[] := by
    simp [generated,hi,consumed_token_alias_emit raw a edge' c'.input c'.token c'.token.id ha htoken rfl]
  refine ⟨deliver raw edge' c',consumeToken c'.token.id a,?_,empty,?_,
    no_generated_target_not_direct raw b _ empty⟩
  · simp [fire,hg',deliver]
  · simp [fire,empty]

/-- Positive raw provenance observations, independent of the direct verdict. -/
def Pattern (raw : Raw) (a : Assignment) (kind : Kind) (provenance : Provenance) : Prop :=
  ∃ edge, edge∈incoming raw ∧
    (edge.kind=kind ∨ ∃ input, a edge.parent=some input ∧ input.provenance=provenance)

def DetachedCopy (raw : Raw) (a : Assignment) : Prop := Pattern raw a .copy .detached
def ArchivalReplay (raw : Raw) (a : Assignment) : Prop := Pattern raw a .replay .archive
def StorageMediated (raw : Raw) (a : Assignment) : Prop := Pattern raw a .storage .store
def TemporalGap (b : Boundary) : Prop :=
  b.source.realized=false ∨ b.target.realized=false ∨ b.sourceStage+1≠b.targetStage

theorem direct_excludes_pattern (raw : Raw) (b : Boundary) (a : Assignment)
    (kind : Kind) (provenance : Provenance)
    (hk : kind≠.liveTemporal) (hp : provenance≠.live)
    (h : ImmediateDirect raw b a) : ¬ Pattern raw a kind provenance := by
  obtain ⟨edge,c,hi,hd,_,_,hg⟩ := (direct_readout_iff raw b a).mp h
  intro pattern
  obtain ⟨other,member,hbad⟩ := pattern
  have sameEdge : other=edge := by simpa [hi] using member
  subst other
  rcases hbad with hkind | hprovenance
  · exact hk (hkind.symm.trans hg.2.2.2.1)
  · obtain ⟨input,hai,hpi⟩ := hprovenance
    have sameInput : c.input=input := Option.some.inj ((decoded_fields a edge.parent c hd).1.symm.trans hai)
    subst input
    exact hp (hpi.symm.trans hg.2.2.2.2.1)

theorem direct_excludes_gap (raw : Raw) (b : Boundary) (a : Assignment)
    (h : ImmediateDirect raw b a) : ¬ TemporalGap b := by
  obtain ⟨_,c,_,_,_,_,hg⟩ := (direct_readout_iff raw b a).mp h
  intro gap
  rcases hg with ⟨_,_,_,_,_,hs,ht,_,_,_,_,_,hstage,_,_,hsourceStage,_⟩
  rcases gap with hSource | hTarget | hStage
  · simp [hs] at hSource
  · simp [ht] at hTarget
  · apply hStage
    rw [← hsourceStage]
    exact hstage

theorem actual_direct_exclusions (raw : Raw) (b : Boundary) (a : Assignment)
    (h : ImmediateDirect raw b a) :
    ¬ DetachedCopy raw a ∧ ¬ ArchivalReplay raw a ∧
    ¬ StorageMediated raw a ∧ ¬ TemporalGap b := by
  exact ⟨direct_excludes_pattern raw b a .copy .detached (by decide) (by decide) h,
    direct_excludes_pattern raw b a .replay .archive (by decide) (by decide) h,
    direct_excludes_pattern raw b a .storage .store (by decide) (by decide) h,
    direct_excludes_gap raw b a h⟩

/-- Full structural binding implies agreement for every hash function.
No injectivity or collision-resistance assumption about a checksum is used. -/
theorem complete_payload_hash_binding {Digest : Type} (hash : Frontier → Digest)
    (raw : Raw) (b : Boundary) (a : Assignment) (h : ImmediateDirect raw b a) :
    ∀ d∈generated raw a, d.sourcePayload=b.source.frontier ∧
      d.frontier=b.target.frontier ∧ hash d.frontier=hash b.target.frontier := by
  obtain ⟨edge,c,hi,hd,hp,ht,hg⟩ := (direct_readout_iff raw b a).mp h
  rcases hg with ⟨_,_,_,_,_,_,_,_,_,_,_,hpayload,_,htarget,_⟩
  have emitted : emit raw a edge=some (deliver raw edge c) := by simp [emit,hd,hp,ht]
  intro d member
  simp [generated,hi,emitted] at member
  subst d
  exact ⟨hpayload,htarget.symm,congrArg hash htarget.symm⟩

theorem direct_strict_temporal_steps (raw : Raw) (b : Boundary) (a : Assignment)
    (h : ImmediateDirect raw b a) :
    b.source.frontier.order < b.target.frontier.order ∧
    b.source.frontier.tick < b.target.frontier.tick ∧
    b.source.frontier.progress < b.target.frontier.progress ∧
    b.source.frontier.record < b.target.frontier.record := by
  obtain ⟨_,c,_,_,_,_,hg⟩ := (direct_readout_iff raw b a).mp h
  rcases hg with ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hstep,_⟩
  exact readout_step_strict b.source b.target raw.receiver hstep

structure DataEdge where
  parent : EventId
  child : EventId
  payload : Frontier
  deriving DecidableEq

/-- Nonempty directed paths in a separately declared raw data-channel graph.
Payload carriage is literal full-frontier equality at every edge. -/
inductive DataPath (graph : List DataEdge) (payload : Frontier) : EventId → EventId → Prop where
  | one (edge : DataEdge) (member : edge∈graph) (carried : edge.payload=payload) :
      DataPath graph payload edge.parent edge.child
  | extend (source middle target : EventId) (pathToMiddle : DataPath graph payload source middle)
      (edge : DataEdge) (member : edge∈graph) (carried : edge.payload=payload)
      (parent : edge.parent=middle) (child : edge.child=target) :
      DataPath graph payload source target

theorem singleton_data_path (source target : EventId) (payload : Frontier) :
    DataPath [⟨source,target,payload⟩] payload source target :=
  .one ⟨source,target,payload⟩ (by simp) rfl

/-- One raw episode domain supplies both typed readouts. The generator uses
the actual dependency graph, actual selected event/stage observations and
actual recipe at the selected source stage. Missing fields reject. -/
structure ControlModel where
  episode : FiniteAtomicLeg
  input : Assignment
  dependencyKind : EventId → EventId → Kind
  dataGraph : List DataEdge

def directProjection (m : ControlModel) : Option (Raw × Boundary) := do
  let source ← eventAt m.episode m.episode.sourceAudit
  let target ← eventAt m.episode m.episode.targetAudit
  let sourceStage ← m.episode.stages[source.stage]?
  let targetStage ← m.episode.stages[target.stage]?
  let receiver ← m.episode.updates[source.stage]?
  if source.owner=m.episode.source ∧ target.owner=m.episode.target ∧
      (m.episode.events.map RawEvent.id).Nodup ∧
      m.episode.dependencies.all (dependencyCheck m.episode)=true then
    pure (⟨source.id,target.id,m.episode.dependencies.map
      (fun e => ⟨e.parent,e.child,m.dependencyKind e.parent e.child⟩),receiver⟩,
      ⟨m.episode.source,m.episode.target,sourceStage,targetStage,source.stage,target.stage⟩)
  else none

def DirectMode (m : ControlModel) : Prop :=
  ∃ raw b, directProjection m=some (raw,b) ∧ ImmediateDirect raw b m.input
def OverlapMode (m : ControlModel) : Prop := AtomicLegPass m.episode
def DataReachable (m : ControlModel) : Prop :=
  ∃ input payload, m.input m.episode.sourceAudit=some input ∧ input.payload=some payload ∧
    DataPath m.dataGraph payload m.episode.sourceAudit m.episode.targetAudit

theorem missing_projection_not_direct (m : ControlModel)
    (h : directProjection m=none) : ¬ DirectMode m := by
  simp [DirectMode,h]

/-- Adding a data graph holds the complete event episode and generator fixed.
Any direct episode can coexist with positively witnessed data reachability. -/
def withDataChannel (m : ControlModel) (payload : Frontier) : ControlModel :=
  {m with dataGraph := [⟨m.episode.sourceAudit,m.episode.targetAudit,payload⟩]}

theorem coexistence_generic (m : ControlModel) (payload : Frontier)
    (h : DirectMode m)
    (source : ∃ input, m.input m.episode.sourceAudit=some input ∧ input.payload=some payload) :
    DirectMode (withDataChannel m payload) ∧ DataReachable (withDataChannel m payload) := by
  refine ⟨h,?_⟩
  obtain ⟨input,hi,hp⟩ := source
  exact ⟨input,payload,hi,hp,singleton_data_path _ _ payload⟩

theorem direct_projection_source_id (m : ControlModel) (raw : Raw) (b : Boundary)
    (h : directProjection m=some (raw,b)) : raw.sourceEvent=m.episode.sourceAudit := by
  unfold directProjection at h
  cases hs : eventAt m.episode m.episode.sourceAudit <;> simp [hs] at h
  rename_i source
  cases ht : eventAt m.episode m.episode.targetAudit <;> simp [ht] at h
  rename_i target
  cases hss : m.episode.stages[source.stage]? <;> simp [hss] at h
  rename_i sourceStage
  cases hts : m.episode.stages[target.stage]? <;> simp [hts] at h
  rename_i targetStage
  cases hu : m.episode.updates[source.stage]? <;> simp [hu] at h
  rename_i receiver
  obtain ⟨_,hr,_⟩ := h
  cases hr
  have found := List.find?_some hs
  simpa using found

theorem direct_source_payload (m : ControlModel) (h : DirectMode m) :
    ∃ input payload, m.input m.episode.sourceAudit=some input ∧ input.payload=some payload := by
  obtain ⟨raw,b,hproj,hread⟩ := h
  obtain ⟨edge,c,_,hd,_,_,hg⟩ := (direct_readout_iff raw b m.input).mp hread
  obtain ⟨hi,hp,_⟩ := decoded_fields m.input edge.parent c hd
  rw [hg.2.1,direct_projection_source_id m raw b hproj] at hi
  exact ⟨c.input,c.payload,hi,hp⟩

theorem direct_coexists_with_data (m : ControlModel) (h : DirectMode m) :
    ∃ payload, DirectMode (withDataChannel m payload) ∧ DataReachable (withDataChannel m payload) := by
  obtain ⟨input,payload,hi,hp⟩ := direct_source_payload m h
  exact ⟨payload,coexistence_generic m payload h ⟨input,hi,hp⟩⟩

inductive GeneralizedLeg where
  | overlap (episode : FiniteAtomicLeg)
  | direct (raw : Raw) (boundary : Boundary) (input : Assignment)

abbrev Signature := Nat × Frontier
def legEntry : GeneralizedLeg → Signature
  | .overlap episode => (episode.source,(entry episode).frontier)
  | .direct _ boundary _ => (boundary.sourceCarrier,boundary.source.frontier)
def legExit : GeneralizedLeg → Signature
  | .overlap episode => (episode.target,(exit episode).frontier)
  | .direct _ boundary _ => (boundary.targetCarrier,boundary.target.frontier)
def legCheck : GeneralizedLeg → Bool
  | .overlap episode => AtomicLegCheck episode
  | .direct raw boundary input => directCheck raw boundary input

/-- Boundary-indexed typed concatenation; it never produces an atomic edge. -/
inductive GeneralizedPath : Signature → Signature → Type where
  | one (leg : GeneralizedLeg) (checked : legCheck leg=true) :
      GeneralizedPath (legEntry leg) (legExit leg)
  | append {a b c : Signature}
      (left : GeneralizedPath a b) (right : GeneralizedPath b c) : GeneralizedPath a c

theorem generalized_path_composition {a b c : Signature}
    (left : GeneralizedPath a b) (right : GeneralizedPath b c) :
    Nonempty (GeneralizedPath a c) := ⟨.append left right⟩

def pathLegs {a b : Signature} : GeneralizedPath a b → List GeneralizedLeg
  | .one leg _ => [leg]
  | .append left right => pathLegs left ++ pathLegs right

theorem path_nonempty {a b : Signature} (path : GeneralizedPath a b) :
    pathLegs path≠[] := by
  induction path with
  | one leg checked => simp [pathLegs]
  | append left right hl hr => simp [pathLegs,hl]

theorem every_path_leg_checked {a b : Signature} (path : GeneralizedPath a b) :
    ∀ leg∈pathLegs path, legCheck leg=true := by
  induction path with
  | one leg checked => simpa [pathLegs] using checked
  | append left right hl hr =>
    intro leg member
    simp only [pathLegs,List.mem_append] at member
    rcases member with hleft | hright
    · exact hl leg hleft
    · exact hr leg hright

def GeneralizedMode (m : ControlModel) : Prop :=
  ∃ source target : Frontier,
    Nonempty (GeneralizedPath (m.episode.source,source) (m.episode.target,target))

theorem overlap_embedding (m : ControlModel) (h : OverlapMode m) : GeneralizedMode m := by
  exact ⟨(entry m.episode).frontier,(exit m.episode).frontier,
    ⟨.one (.overlap m.episode) h⟩⟩

theorem direct_projection_endpoints (m : ControlModel) (raw : Raw) (b : Boundary)
    (h : directProjection m=some (raw,b)) :
    b.sourceCarrier=m.episode.source ∧ b.targetCarrier=m.episode.target := by
  unfold directProjection at h
  cases hs : eventAt m.episode m.episode.sourceAudit <;> simp [hs] at h
  rename_i source
  cases ht : eventAt m.episode m.episode.targetAudit <;> simp [ht] at h
  rename_i target
  cases hss : m.episode.stages[source.stage]? <;> simp [hss] at h
  rename_i sourceStage
  cases hts : m.episode.stages[target.stage]? <;> simp [hts] at h
  rename_i targetStage
  cases hu : m.episode.updates[source.stage]? <;> simp [hu] at h
  rename_i receiver
  obtain ⟨_,_,hb⟩ := h
  cases hb
  exact ⟨rfl,rfl⟩

theorem direct_embedding (m : ControlModel) (h : DirectMode m) : GeneralizedMode m := by
  obtain ⟨raw,b,hp,hd⟩ := h
  obtain ⟨hs,ht⟩ := direct_projection_endpoints m raw b hp
  refine ⟨b.source.frontier,b.target.frontier,?_⟩
  have path := GeneralizedPath.one (.direct raw b m.input) hd
  change GeneralizedPath (b.sourceCarrier,b.source.frontier) (b.targetCarrier,b.target.frontier) at path
  rw [hs,ht] at path
  exact ⟨path⟩

end CSTTT.CorridorTheory.RawDirectSuccessor
