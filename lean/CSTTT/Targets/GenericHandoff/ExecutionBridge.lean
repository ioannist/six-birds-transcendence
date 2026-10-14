import CSTTT.Targets.GenericHandoff.ExecutionSnapshotTransport

/-! G6d-4b typed execution transport. Two separately typed register programs
read ONE immutable assignment. Their histories, initial states, snapshots,
weights, successors, code and eight-field observations are interpreted here.
The register translation is a raw instruction family, not a supplied state
map. Its laws are checked on the whole actual source future closure.

This is the execution part of the G1c adapter. Factor-table, record-edge and
retained-route comparison laws must additionally be extracted at the enclosing
lineage boundary; this module does not rename this part StrictTemporalLineage.
-/
namespace CSTTT.TargetTheory.GenericHandoff.ExecutionBridge
open RegisterInterpreter CSTTT.TransportTheory

structure Raw (Cell : Type) (Value : Cell → Type) (S T : Type)
    (SV : S → Type) (TV : T → Type)
    (D A O P Q Residue Maintenance Stage Id History RouteId : Type) where
  source : ExecutionFrontier.Raw Cell Value S SV D A O P Residue Maintenance Stage Id History RouteId
  target : ExecutionFrontier.Raw Cell Value T TV D A O Q Residue Maintenance Stage Id History RouteId
  translation : (k : T) → Expr Cell Value S SV Unit (TV k)
  maps : SnapshotRawMaps P Q Residue Maintenance

variable {Cell S T D A O P Q Residue Maintenance Stage Id History RouteId : Type}
    {Value : Cell → Type} {SV : S → Type} {TV : T → Type}

abbrev TranslationReady
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) := ∀ k, Complete (raw.translation k).dependencies a

noncomputable def translate
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : TranslationReady raw a) (x : Registers S SV) : Registers T TV :=
  fun k => RegisterFuture.read (raw.translation k) a (h k) x

theorem translate_equation
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (h : TranslationReady raw a) (x : Registers S SV) (k : T) :
    (raw.translation k).eval a x () = some (translate raw a h x k) :=
  RegisterFuture.read_eq _ _ _ _

variable [DecidableEq O] [DecidableEq Stage] [DecidableEq P] [DecidableEq Q]
    [DecidableEq Residue] [DecidableEq Maintenance]

/-- All laws are equations on the decoded instructions. Every supported
successor, including nonrepresentative branches, is covered. Observation
coherence is closure-wide, not just at the four audited snapshots. -/
structure Laws
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a) : Prop where
  audit : raw.target.audit = raw.source.audit
  outcomes : raw.target.acquisition.execution.outcomes = raw.source.acquisition.execution.outcomes
  words : raw.target.acquisition.histories.read a = raw.source.acquisition.histories.read a
  initial : ∀ hist, translate raw a hm (ExecutionFrontier.initial raw.source a hs hist) =
    ExecutionFrontier.initial raw.target a ht hist
  rows : ∀ x, ExecutionFrontier.Closure raw.source a hs x → ∀ da o,
    RegisterFuture.weight (ExecutionFrontier.temporal raw.target) a ht.2
      (translate raw a hm x) da o =
    RegisterFuture.weight (ExecutionFrontier.temporal raw.source) a hs.2 x da o
  successor : ∀ x, ExecutionFrontier.Closure raw.source a hs x →
    ∀ d ∈ raw.source.acquisition.execution.disturbances,
    ∀ act ∈ raw.source.acquisition.execution.actions,
    ∀ o ∈ raw.source.acquisition.execution.outcomes,
      translate raw a hm (AcquisitionExecution.update raw.source.acquisition a hs.1 x d act o) =
      AcquisitionExecution.update raw.target.acquisition a ht.1 (translate raw a hm x) d act o
  observation : ∀ x, ExecutionFrontier.Closure raw.source a hs x →
    mapSnapshotReadout raw.maps (RegisterFuture.observation (ExecutionFrontier.temporal raw.source) a hs.2 x) =
      RegisterFuture.observation (ExecutionFrontier.temporal raw.target) a ht.2 (translate raw a hm x)

def Valid
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) : Prop :=
  ExecutionFrontier.Valid raw.source a ∧ ExecutionFrontier.Valid raw.target a ∧
    ∃ hm : TranslationReady raw a, ∀ hs ht, Laws raw a hs ht hm

omit [DecidableEq Stage] [DecidableEq P] [DecidableEq Q] [DecidableEq Residue] [DecidableEq Maintenance] in
/-- Induction over the actual supported word. The terminal run is constructed
by the updater. No equality of predictive representatives substitutes for it. -/
theorem fold_commutes
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a)
    (hl : Laws raw a hs ht hm) (x : Registers S SV)
    (word : List (D × A × O)) (hx : ExecutionFrontier.Closure raw.source a hs x)
    (hp : ExecutionFrontier.PrefixCheck raw.source a hs x word) :
    translate raw a hm (AcquisitionExecution.foldHistory raw.source.acquisition a hs.1 x word) =
      AcquisitionExecution.foldHistory raw.target.acquisition a ht.1 (translate raw a hm x) word := by
  induction word generalizing x with
  | nil => rfl
  | cons e rest ih =>
    rcases e with ⟨d,act,o⟩
    have hn : ExecutionFrontier.Closure raw.source a hs
        (AcquisitionExecution.update raw.source.acquisition a hs.1 x d act o) := by
      have h := FutureClosure.step hx (d,act) o hp.2.2.1
      simpa only [RegisterFuture.dynamics,ExecutionFrontier.updater_shared] using h
    simp only [AcquisitionExecution.foldHistory]
    rw [ih _ hn hp.2.2.2.2.2,hl.successor x hx d hp.1 act hp.2.1 o hp.2.2.1]

omit [DecidableEq Stage] [DecidableEq P] [DecidableEq Q] [DecidableEq Residue] [DecidableEq Maintenance] in
theorem snapshot_commutes
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a)
    (hl : Laws raw a hs ht hm) (ha : ExecutionFrontier.AuditCheck raw.source a hs)
    (i : History × Nat) (hi : i ∈ raw.source.audit) :
    translate raw a hm (ExecutionFrontier.snapshot raw.source a hs i) =
      ExecutionFrontier.snapshot raw.target a ht i := by
  have hw : ExecutionFrontier.historyPrefix raw.target a i = ExecutionFrontier.historyPrefix raw.source a i := by
    simp only [ExecutionFrontier.historyPrefix,hl.words]
  obtain ⟨histories,hh,hchecks,_⟩ := ha.2
  have hc := (hchecks i hi).2.2
  unfold ExecutionFrontier.snapshot
  rw [hw,← hl.initial]
  apply fold_commutes raw a hs ht hm hl
  · exact FutureClosure.root _ (List.mem_map.mpr ⟨i,hi,rfl⟩)
  · exact hc

omit [DecidableEq Stage] [DecidableEq P] [DecidableEq Q] [DecidableEq Residue] [DecidableEq Maintenance] in
/-- Snapshot map equations are derived from the actual instruction fold and
closure-wide observation law, rather than supplied as a candidate display. -/
theorem snapshot_map_check
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a)
    (hl : Laws raw a hs ht hm) (ha : ExecutionFrontier.AuditCheck raw.source a hs) :
    SnapshotMapCheck raw.source.audit (ExecutionFrontier.observation raw.source a hs)
      (ExecutionFrontier.observation raw.target a ht) raw.maps := by
  intro i hi
  have hc := (ExecutionFrontier.snapshot_execution raw.source a hs ha i hi).2
  have hmapped := hl.observation _ hc
  rw [snapshot_commutes raw a hs ht hm hl ha i hi] at hmapped
  exact hmapped

/-- All eight frozen fields transport exactly. Both full-future propositions
come from their own defined interpreter and all-word induction. Different
register namespaces and raw action rows are permitted, subject to the laws. -/
theorem frozen_transport
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hv : Valid raw a) :
    ∃ hs : ExecutionFrontier.Ready raw.source a, ∃ ht : ExecutionFrontier.Ready raw.target a,
      ∃ _hm : TranslationReady raw a,
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal raw.source) a hs.2) ∧
      FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal raw.target) a ht.2) ∧
      ∃ hc : SnapshotMapCheck raw.source.audit (ExecutionFrontier.observation raw.source a hs)
          (ExecutionFrontier.observation raw.target a ht) raw.maps,
        ∀ i : Audited raw.source.audit,
          transportFrozenSnapshot raw.source.audit (ExecutionFrontier.observation raw.source a hs)
            (ExecutionFrontier.observation raw.target a ht) raw.maps hc
            (ExecutionFrontier.frozen raw.source a hs i) =
          frozenSnapshot (RegisterFuture.future (ExecutionFrontier.temporal raw.target) a ht.2)
            raw.source.audit (ExecutionFrontier.observation raw.target a ht) i := by
  obtain ⟨hs,ha,_,_,_,hb,_,_⟩ := hv.1
  obtain ⟨ht,_,hft,_,_,_⟩ := ExecutionFrontier.soundness raw.target a hv.2.1
  obtain ⟨hm,hl⟩ := hv.2.2
  have hsource := FutureLumping.all_words _ hb
  have hc := snapshot_map_check raw a hs ht hm (hl hs ht) ha
  refine ⟨hs,ht,hm,?_,hft,hc,?_⟩
  · exact hsource
  · intro i
    have he := frozen_snapshot_transport (RegisterFuture.future (ExecutionFrontier.temporal raw.source) a hs.2)
      raw.source.audit _ _ raw.maps hc i
    change transportFrozenSnapshot _ _ _ _ _ (frozenSnapshot _ _ _ _) = _
    rw [he]
    -- Both sides are true, but each is independently proved by its own bisimulation.
    have hp' : FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal raw.source) a hs.2) =
        FullFutureSufficient (RegisterFuture.future (ExecutionFrontier.temporal raw.target) a ht.2) :=
      propext ⟨fun _ => hft,fun _ => hsource⟩
    simp only [frozenSnapshot,hp',eq_self]

/-- Representative independence is derived from the executed snapshot map.
The histories and full runs may differ; only their source predictive readout
is required to agree. No representative-independent verdict is a raw field. -/
theorem representative_independence
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hv : Valid raw a)
    (hs : ExecutionFrontier.Ready raw.source a) (ht : ExecutionFrontier.Ready raw.target a)
    (i j : Audited raw.source.audit)
    (same : (ExecutionFrontier.observation raw.source a hs i.val).predictive =
      (ExecutionFrontier.observation raw.source a hs j.val).predictive) :
    (ExecutionFrontier.observation raw.target a ht i.val).predictive =
      (ExecutionFrontier.observation raw.target a ht j.val).predictive := by
  obtain ⟨hs',ha,rest⟩ := hv.1
  obtain ⟨hm,hl⟩ := hv.2.2
  have hc := snapshot_map_check raw a hs ht hm (hl hs ht) ha
  have hi := congrArg TemporalSnapshotReadout.predictive (hc i.val i.property)
  have hj := congrArg TemporalSnapshotReadout.predictive (hc j.val j.property)
  exact hi.symm.trans ((congrArg raw.maps.predictive same).trans hj)

/-- A direct rejection of the executed bridge result when an atomic input is
missing. Readiness is not assumed together with the incompatible missing cell. -/
theorem missing_atomic_rejected
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hm : raw.source.acquisition.events.read a = none) : ¬ Valid raw a :=
  fun hv => ExecutionFrontier.missing_atomic_view raw.source a hm hv.1

theorem missing_translation_rejected
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (k : Cell) (r : T)
    (hk : k ∈ (raw.translation r).dependencies) (hm : a k = none) : ¬ Valid raw a := by
  rintro ⟨_,_,ht,hchecks⟩
  have hp := ht r k hk
  rw [hm] at hp
  contradiction

/-- Guard against a wrong transition at ANY computed closure state. -/
theorem successor_mismatch_rejected
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a)
    (x : Registers S SV) (hx : ExecutionFrontier.Closure raw.source a hs x)
    (d : D) (hd : d ∈ raw.source.acquisition.execution.disturbances)
    (act : A) (ha : act ∈ raw.source.acquisition.execution.actions)
    (o : O) (ho : o ∈ raw.source.acquisition.execution.outcomes)
    (bad : translate raw a hm (AcquisitionExecution.update raw.source.acquisition a hs.1 x d act o) ≠
      AcquisitionExecution.update raw.target.acquisition a ht.1 (translate raw a hm x) d act o) : ¬ Valid raw a := by
  rintro ⟨_,_,hm',hl⟩
  exact bad ((hl hs ht).successor x hx d hd act ha o ho)

/-- Per-field whole-closure guard, including a cap that agrees at audit roots. -/
theorem readout_mismatch_rejected
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a)
    (x : Registers S SV) (hx : ExecutionFrontier.Closure raw.source a hs x)
    (bad : mapSnapshotReadout raw.maps
      (RegisterFuture.observation (ExecutionFrontier.temporal raw.source) a hs.2 x) ≠
      RegisterFuture.observation (ExecutionFrontier.temporal raw.target) a ht.2 (translate raw a hm x)) :
    ¬ Valid raw a := by
  rintro ⟨_,_,hm',hl⟩
  exact bad ((hl hs ht).observation x hx)

/-- One field mismatch anywhere in the full source closure denies the bridge.
Instantiating read with each of the eight record projections gives the complete
field family; it includes caps agreeing at every audit-root value. -/
theorem field_mismatch_rejected {X : Type}
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a)
    (x : Registers S SV) (hx : ExecutionFrontier.Closure raw.source a hs x)
    (read : TemporalSnapshotReadout Q Residue Maintenance → X)
    (bad : read (mapSnapshotReadout raw.maps
        (RegisterFuture.observation (ExecutionFrontier.temporal raw.source) a hs.2 x)) ≠
      read (RegisterFuture.observation (ExecutionFrontier.temporal raw.target) a ht.2 (translate raw a hm x))) :
    ¬ Valid raw a :=
  readout_mismatch_rejected raw a hs ht hm x hx (fun he => bad (congrArg read he))

/-- A wrong branch weight cannot be hidden by coherent audit-root displays. -/
theorem weight_mismatch_rejected
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a)
    (x : Registers S SV) (hx : ExecutionFrontier.Closure raw.source a hs x)
    (da : D × A) (o : O)
    (bad : RegisterFuture.weight (ExecutionFrontier.temporal raw.target) a ht.2
        (translate raw a hm x) da o ≠
      RegisterFuture.weight (ExecutionFrontier.temporal raw.source) a hs.2 x da o) : ¬ Valid raw a := by
  rintro ⟨_,_,hm',hl⟩
  exact bad ((hl hs ht).rows x hx da o)

theorem word_mismatch_rejected
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value)
    (bad : raw.target.acquisition.histories.read a ≠ raw.source.acquisition.histories.read a) : ¬ Valid raw a := by
  rintro ⟨hs,ht,hm,hl⟩
  exact bad ((hl hs.choose ht.choose).words)

theorem initial_mismatch_rejected
    (raw : Raw Cell Value S T SV TV D A O P Q Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hs : ExecutionFrontier.Ready raw.source a)
    (ht : ExecutionFrontier.Ready raw.target a) (hm : TranslationReady raw a) (hist : History)
    (bad : translate raw a hm (ExecutionFrontier.initial raw.source a hs hist) ≠
      ExecutionFrontier.initial raw.target a ht hist) : ¬ Valid raw a := by
  rintro ⟨_,_,hm',hl⟩
  exact bad ((hl hs ht).initial hist)

/-- Algebraic identity specialization; this does not claim a carrier change.
It is also an adapter regression for arbitrary partial assignments. -/
def identityRaw
    (frame : ExecutionFrontier.Raw Cell Value S SV D A O P Residue Maintenance Stage Id History RouteId) :
    Raw Cell Value S S SV SV D A O P P Residue Maintenance Stage Id History RouteId :=
  ⟨frame,frame,fun k => .register k,⟨id,id,id,id,id,id,id,id⟩⟩

omit [DecidableEq O] [DecidableEq Stage] [DecidableEq P] [DecidableEq Q]
    [DecidableEq Residue] [DecidableEq Maintenance] in
theorem identity_translate
    (frame : ExecutionFrontier.Raw Cell Value S SV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) (hm : TranslationReady (identityRaw frame) a) (x : Registers S SV) :
    translate (identityRaw frame) a hm x = x := by
  funext k
  exact Option.some.inj ((translate_equation (identityRaw frame) a hm x k).symm)

omit [DecidableEq Q] in
theorem identity_valid_iff
    (frame : ExecutionFrontier.Raw Cell Value S SV D A O P Residue Maintenance Stage Id History RouteId)
    (a : Assignment Cell Value) : Valid (identityRaw frame) a ↔ ExecutionFrontier.Valid frame a := by
  constructor
  · exact fun h => h.1
  · intro hv
    have hm : TranslationReady (identityRaw frame) a := by
      intro k j hj; simp [identityRaw,Expr.dependencies] at hj
    refine ⟨hv,hv,hm,?_⟩
    intro hs ht
    constructor
    · rfl
    · rfl
    · rfl
    · intro hist; rw [identity_translate]; rfl
    · intro x hx da o; rw [identity_translate]; rfl
    · intro x hx d hd act ha o ho; rw [identity_translate,identity_translate]; rfl
    · intro x hx; rw [identity_translate]; rfl

end CSTTT.TargetTheory.GenericHandoff.ExecutionBridge
