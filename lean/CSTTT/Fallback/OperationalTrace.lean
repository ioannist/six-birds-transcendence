import CSTTT.Core.Finite

namespace CSTTT.FallbackTheory.OperationalTrace
variable {S T : Type}
-- Class (b): typed source, captured record, or target; no ancestry/verdict slot.
inductive Content (S T : Type) where
  | source (payload : S)
  | record (origin capturedAt : Nat) (payload : S)
  | target (payload : T)
-- Class (b): derived execution store; edges are interpreter outputs.
structure Store (S T : Type) where
  read : Nat → Option (Content S T)
  active : Nat → Bool
  edges : List (Nat × Nat)
  clock : Nat
  captured : Nat → Option (Nat × Nat × S)
-- Class (b): raw commands, without ancestry or acceptance predicates.
inductive Command (T : Type) where
  | snapshot (source record : Nat)
  | erase (source : Nat)
  | gap (duration : Nat)
  | activate (record target : Nat)
  | independent (target : Nat) (payload : T)
-- Class (b): exact event-slot write; operations check freshness.
def put (read : Nat → Option (Content S T)) (key : Nat) (value : Content S T) : Nat → Option (Content S T) :=
  fun k => if k=key then some value else read k
-- Class (b): actual active switch, separate from retained event contents.
def switch (active : Nat → Bool) (key : Nat) (value : Bool) : Nat → Bool :=
  fun k => if k=key then value else active k
-- Class (b): initialize only a raw source; no supplied record or graph edge.
def initial (source : Nat) (payload : S) : Store S T :=
  ⟨fun k => if k=source then some (.source payload) else none,fun k => decide (k=source),[],0,fun _ => none⟩
-- Class (b): read actual source/record and decode; missing, wrong-kind and occupied inputs reject.
def step (decoder : Option (S → T)) (maxAge : Nat) (store : Store S T) : Command T → Option (Store S T)
  | .snapshot source record => do
      let .source payload ← store.read source | none
      if store.active source && (store.read record).isNone then
        some ⟨put store.read record (.record source (store.clock+1) payload),switch store.active record false,
          (source,record)::store.edges,store.clock+1,
          fun k => if k=record then some (source,store.clock+1,payload) else store.captured k⟩
      else none
  | .erase source => do
      let .source _ ← store.read source | none
      if store.active source then some {store with active := switch store.active source false,clock := store.clock+1}
      else none
  | .gap duration => some {store with clock := store.clock+duration}
  | .activate record target => do
      let .record _ created payload ← store.read record | none
      let decode ← decoder
      if decide (created ≤ store.clock) && decide (store.clock-created ≤ maxAge) && (store.read target).isNone then
        some ⟨put store.read target (.target (decode payload)),switch store.active target true,
          (record,target)::store.edges,store.clock+1,store.captured⟩
      else none
  | .independent target payload =>
      if (store.read target).isNone then
        some ⟨put store.read target (.target payload),switch store.active target true,store.edges,store.clock+1,store.captured⟩
      else none
-- Class (b): complete actual execution propagates any failed command.
def run (decoder : Option (S → T)) (maxAge : Nat) : Store S T → List (Command T) → Option (Store S T)
  | store,[] => some store
  | store,command::rest => (step decoder maxAge store command).bind (fun next => run decoder maxAge next rest)
-- Class (b): positive-length paths use only actually emitted operational edges.
inductive Path (edges : List (Nat × Nat)) : Nat → Nat → Prop where
  | one {x y : Nat} (member : (x,y)∈edges) : Path edges x y
  | extend {x y z : Nat} (previous : Path edges x y) (member : (y,z)∈edges) : Path edges x z
-- Class (b): actual path closure is least among all edge-containing transitive relations.
theorem path_least (edges : List (Nat × Nat)) (r : Nat → Nat → Prop)
    (seeds : ∀ x y, (x,y)∈edges → r x y)
    (closed : ∀ x y z, r x y → r y z → r x z) : ∀ x y, Path edges x y → r x y := by
  intro x y path
  induction path with
  | one member => exact seeds _ _ member
  | extend previous member ih => exact closed _ _ _ ih (seeds _ _ member)
-- Class (b): every nonseed consequence requires a related predecessor and actual edge.
theorem path_no_ex_nihilo (edges : List (Nat × Nat)) (x y : Nat) (path : Path edges x y) :
    (x,y)∈edges ∨ ∃ predecessor, Path edges x predecessor ∧ (predecessor,y)∈edges := by
  cases path with
  | one member => exact Or.inl member
  | extend previous member => exact Or.inr ⟨_,previous,member⟩
-- Class (b): actual lack of incoming edges directly excludes operational ancestry.
theorem no_incoming_excludes (edges : List (Nat × Nat)) (twin : Nat)
    (missing : ∀ predecessor, (predecessor,twin)∉edges) : ∀ source, ¬ Path edges source twin := by
  intro source path
  rcases path_no_ex_nihilo edges source twin path with member|⟨predecessor,_,member⟩
  · exact missing source member
  · exact missing predecessor member
-- Class (b): declared generic destructive program with an independent, equal-payload target.
def destructiveWithTwin (source record target twin duration : Nat) (twinPayload : T) : List (Command T) :=
  [.snapshot source record,.erase source,.gap duration,.activate record target,.independent twin twinPayload]
end CSTTT.FallbackTheory.OperationalTrace

namespace CSTTT.FallbackTheory.OperationalTrace
variable {S T : Type}
-- Class (b): optional raw source input; a missing source rejects before execution.
def execute (decoder : Option (S → T)) (maxAge source : Nat) (rawSource : Option S)
    (commands : List (Command T)) : Option (Store S T) :=
  rawSource.bind (fun payload => run decoder maxAge (initial source payload) commands)
-- Class (b): absence of consumed raw source is direct None for every other input.
theorem missing_source_rejects (decoder : Option (S → T)) (maxAge source : Nat)
    (commands : List (Command T)) : execute decoder maxAge source none commands=none := rfl
-- Class (b): activation with a missing raw decoder rejects, regardless of all other inputs.
theorem missing_decoder_rejects (maxAge : Nat) (store : Store S T) (record target : Nat) :
    step none maxAge store (.activate record target)=none := by
  simp only [step]
  cases h : store.read record with
  | none => rfl
  | some value => cases value <;> rfl
-- Class (b): missing consumed record rejects on every partial decoder assignment.
theorem missing_record_rejects (decoder : Option (S → T)) (maxAge : Nat)
    (store : Store S T) (record target : Nat) (missing : store.read record=none) :
    step decoder maxAge store (.activate record target)=none := by simp [step,missing]
-- Class (b): an actual source token cannot masquerade as the required typed record.
theorem wrong_kind_rejects (decoder : Option (S → T)) (maxAge : Nat)
    (store : Store S T) (record target : Nat) (payload : S)
    (wrong : store.read record=some (.source payload)) :
    step decoder maxAge store (.activate record target)=none := by simp [step,wrong]
-- Class (b): actual record age beyond the declared bound directly rejects the readout.
theorem stale_record_rejects (decoder : Option (S → T)) (maxAge : Nat)
    (store : Store S T) (record target origin created : Nat) (payload : S)
    (read : store.read record=some (.record origin created payload))
    (stale : maxAge < store.clock-created) :
    step decoder maxAge store (.activate record target)=none := by
  cases decoder with
  | none => exact missing_decoder_rejects _ _ _ _
  | some decode => simp [step,read,show ¬ store.clock-created ≤ maxAge by omega,
      show ¬ store.clock ≤ maxAge+created by omega]
-- Class (b): future-dated records reject, including in Nat's truncated-subtraction regime.
theorem future_record_rejects (decoder : Option (S → T)) (maxAge : Nat)
    (store : Store S T) (record target origin created : Nat) (payload : S)
    (read : store.read record=some (.record origin created payload))
    (future : store.clock < created) :
    step decoder maxAge store (.activate record target)=none := by
  cases decoder with
  | none => exact missing_decoder_rejects _ _ _ _
  | some decode => simp [step,read,show ¬ created ≤ store.clock by omega]
end CSTTT.FallbackTheory.OperationalTrace

namespace CSTTT.FallbackTheory.OperationalTrace
variable {S T : Type}
-- Class (b): exact snapshot result calculated from the initial raw source contents.
def captured (source record : Nat) (payload : S) : Store S T :=
  let start : Store S T := initial source payload
  ⟨put start.read record (.record source 1 payload),switch start.active record false,[(source,record)],1,
    fun k => if k=record then some (source,1,payload) else none⟩
-- Class (b): actual source activity disappears while the captured event record persists.
def erased (source record : Nat) (payload : S) : Store S T :=
  let snapshot : Store S T := captured source record payload
  {snapshot with active := switch snapshot.active source false,clock := 2}
-- Class (b): explicit dormancy changes the event clock, without constructing a target or ancestry.
def dormant (source record duration : Nat) (payload : S) : Store S T :=
  {erased source record payload with clock := 2+duration}
-- Class (b): exact activation writes the decoder output of the ACTUAL captured payload.
def activated (source record target duration : Nat) (decode : S → T) (payload : S) : Store S T :=
  let waited := dormant source record duration payload
  ⟨put waited.read target (.target (decode payload)),switch waited.active target true,
    [(record,target),(source,record)],2+duration+1,waited.captured⟩
-- Class (b): same target payload/active status is written independently; no provenance edge is added.
def withTwin (source record target twin duration : Nat) (decode : S → T) (payload : S) : Store S T :=
  let derived := activated source record target duration decode payload
  ⟨put derived.read twin (.target (decode payload)),switch derived.active twin true,derived.edges,derived.clock+1,derived.captured⟩
-- Class (b): full actual execution derives this store, for EVERY payload/decoder/duration and distinct address set.
theorem actual_destructive_with_twin (source record target twin duration maxAge : Nat) (decode : S → T) (payload : S)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin)
    (age : 2+duration-1 ≤ maxAge) :
    run (some decode) maxAge (initial source payload) (destructiveWithTwin source record target twin duration (decode payload))=
      some (withTwin source record target twin duration decode payload) := by
  simp [run,step,destructiveWithTwin,initial,withTwin,activated,dormant,erased,captured,put,switch,
    age, show 2+duration ≤ maxAge+1 by omega, show 1 ≤ 2+duration by omega,
    sr,st,sw,rt,rw,tw,Ne.symm sr,Ne.symm st,Ne.symm sw,Ne.symm rt,Ne.symm rw,Ne.symm tw]
-- Class (b): before activation, the source is inactive and no target exists, while the actual record retains the source payload.
theorem actual_gap_state (source record target duration : Nat) (payload : S)
    (sr : source≠record) (st : source≠target) (rt : record≠target) :
    (dormant source record duration payload : Store S T).active source=false ∧
    (dormant source record duration payload : Store S T).read target=none ∧
    (dormant source record duration payload : Store S T).read record=some (.record source 1 payload) := by
  simp [dormant,erased,captured,initial,put,switch,sr,st,rt,Ne.symm sr,Ne.symm st,Ne.symm rt]
-- Class (b): reconstruction and independent twin have exactly equal actual target payloads/active status.
theorem actual_target_readouts_equal (source record target twin duration : Nat) (decode : S → T) (payload : S)
    (tw : target≠twin) :
    (withTwin source record target twin duration decode payload).read target=some (.target (decode payload)) ∧
    (withTwin source record target twin duration decode payload).read twin=some (.target (decode payload)) ∧
    (withTwin source record target twin duration decode payload).active target=true ∧
    (withTwin source record target twin duration decode payload).active twin=true := by
  simp [withTwin,activated,put,switch,tw]
-- Class (b): actual source-record-target ancestry is generated by the two emitted edges.
theorem reconstruction_path (source record target twin duration : Nat) (decode : S → T) (payload : S) :
    Path (withTwin source record target twin duration decode payload).edges source target :=
  .extend (y := record) (.one (by simp [withTwin,activated])) (by simp [withTwin,activated])
-- Class (b): the structurally equal independently created twin has no actual incoming edge and is ancestry-excluded.
theorem independent_twin_excluded (source record target twin duration : Nat) (decode : S → T) (payload : S)
    (rw : record≠twin) (tw : target≠twin) :
    ¬ Path (withTwin source record target twin duration decode payload).edges source twin := by
  apply no_incoming_excludes
  intro predecessor
  simp [withTwin,activated,Ne.symm rw,Ne.symm tw]
-- Class (b): provenance discrimination is invariant under the explicitly declared gap duration, without relying on endpoint equality.
theorem gap_preserves_emitted_graph (source record target twin firstDuration secondDuration : Nat)
    (decode : S → T) (payload : S) :
    (withTwin source record target twin firstDuration decode payload).edges=
      (withTwin source record target twin secondDuration decode payload).edges := rfl
end CSTTT.FallbackTheory.OperationalTrace

namespace CSTTT.FallbackTheory.OperationalTrace
variable {S T : Type}
-- Class (b): independent raw target initialization never calls the decoder or reads a source/record.
theorem independent_ignores_decoder (first second : Option (S → T)) (maxAge : Nat) (store : Store S T) (target : Nat) (rawPayload : T) :
    step first maxAge store (.independent target rawPayload)=step second maxAge store (.independent target rawPayload) := rfl
-- Class (b): complete actual-run return, rather than an assertion about an unexecuted display store.
theorem actual_run_separates (source record target twin duration maxAge : Nat) (decode : S → T) (payload : S)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1 ≤ maxAge) (finished : Store S T)
    (executed : run (some decode) maxAge (initial source payload)
      (destructiveWithTwin source record target twin duration (decode payload))=some finished) :
    finished.read target=finished.read twin ∧ finished.active source=false ∧
    Path finished.edges source target ∧ ¬ Path finished.edges source twin := by
  have equal := Option.some.inj ((actual_destructive_with_twin source record target twin duration maxAge decode payload sr st sw rt rw tw age).symm.trans executed)
  rw [← equal]
  have observed := actual_target_readouts_equal source record target twin duration decode payload tw
  refine ⟨observed.1.trans observed.2.1.symm,?_,reconstruction_path source record target twin duration decode payload,
    independent_twin_excluded source record target twin duration decode payload rw tw⟩
  simp [withTwin,activated,dormant,erased,switch,st,sw]
end CSTTT.FallbackTheory.OperationalTrace

namespace CSTTT.FallbackTheory.OperationalTrace
variable {S T : Type}
-- Class (b): expected independent write uses a separate raw target payload.
def withRawTwin (source record target twin duration : Nat) (decode : S → T) (payload : S)
    (rawTwin : T) : Store S T :=
  let derived := activated source record target duration decode payload
  ⟨put derived.read twin (.target rawTwin),switch derived.active twin true,derived.edges,derived.clock+1,derived.captured⟩
-- Class (b): actual optional-source/decoder execution derives the target and unrelated raw twin.
theorem actual_raw_program (source record target twin duration maxAge : Nat) (decode : S → T)
    (payload : S) (rawTwin : T) (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1 ≤ maxAge) :
    execute (some decode) maxAge source (some payload)
      (destructiveWithTwin source record target twin duration rawTwin)=
      some (withRawTwin source record target twin duration decode payload rawTwin) := by
  simp [execute,run,step,destructiveWithTwin,initial,withRawTwin,activated,dormant,erased,captured,put,switch,
    show 2+duration ≤ maxAge+1 by omega,show 1 ≤ 2+duration by omega,
    sr,st,sw,rt,rw,tw,Ne.symm sr,Ne.symm st,Ne.symm sw,Ne.symm rt,Ne.symm rw,Ne.symm tw]
-- Class (b): overlong dormancy rejects the COMPLETE executed program before target activation.
theorem stale_program_rejects (source record target twin duration maxAge : Nat) (decode : S → T)
    (payload : S) (rawTwin : T) (sr : source≠record) (stale : maxAge < 2+duration-1) :
    execute (some decode) maxAge source (some payload)
      (destructiveWithTwin source record target twin duration rawTwin)=none := by
  simp [execute,run,step,destructiveWithTwin,initial,put,switch,sr,Ne.symm sr,
    show ¬ 2+duration ≤ maxAge+1 by omega]
-- Class (b): missing decoder rejects the actual destructive program; no replacement decoder is supplied.
theorem missing_decoder_program_rejects (source record target twin duration maxAge : Nat)
    (payload : S) (rawTwin : T) (sr : source≠record) :
    execute none maxAge source (some payload)
      (destructiveWithTwin source record target twin duration rawTwin)=none := by
  simp [execute,run,step,destructiveWithTwin,initial,put,switch,sr,Ne.symm sr]
-- Class (b): actual activation presence iff the consumed typed record, decoder, time checks and fresh output all hold.
theorem activation_present_iff (decoder : Option (S → T)) (maxAge : Nat) (store : Store S T)
    (record target : Nat) :
    (step decoder maxAge store (.activate record target)).isSome=true ↔
      ∃ origin created payload decode, store.read record=some (.record origin created payload) ∧
        decoder=some decode ∧ created≤store.clock ∧ store.clock-created≤maxAge ∧ store.read target=none := by
  cases read : store.read record with
  | none => simp [step,read]
  | some content =>
    cases content with
    | source payload => simp [step,read]
    | target payload => simp [step,read]
    | record origin created payload =>
      cases decoder with
      | none => simp [step,read]
      | some decode =>
        simp [step,read]
        constructor
        · intro h
          exact ⟨origin,created,⟨rfl,rfl⟩,h.1.1,h.1.2,h.2⟩
        · rintro ⟨otherOrigin,otherCreated,⟨rfl,rfl⟩,h1,h2,h3⟩
          exact ⟨⟨h1,h2⟩,h3⟩
-- Class (b): independent raw construction consumes no decoder and adds no operational edge.
theorem independent_present_without_decoder (maxAge : Nat) (store : Store S T) (target : Nat)
    (rawTwin : T) (fresh : store.read target=none) :
    step none maxAge store (.independent target rawTwin)=
      some ⟨put store.read target (.target rawTwin),switch store.active target true,store.edges,store.clock+1,store.captured⟩ := by
  simp [step,fresh]
-- Class (b): an independently supplied raw twin remains ancestry-excluded regardless of its payload.
theorem raw_twin_excluded (source record target twin duration : Nat) (decode : S → T)
    (payload : S) (rawTwin : T) (rw : record≠twin) (tw : target≠twin) :
    ¬ Path (withRawTwin source record target twin duration decode payload rawTwin).edges source twin := by
  apply no_incoming_excludes
  intro predecessor
  simp [withRawTwin,activated,Ne.symm rw,Ne.symm tw]
end CSTTT.FallbackTheory.OperationalTrace

namespace CSTTT.FallbackTheory.SourceCheckedTrace
open CSTTT.FallbackTheory.OperationalTrace
variable {S T : Type} [DecidableEq S]
-- Class (b): verify the captured payload against the retained immutable source event before activation.
def checkedStep (decoder : Option (S → T)) (maxAge : Nat) (store : Store S T) : Command T → Option (Store S T)
  | .activate record target => do
      let .record origin created payload ← store.read record | none
      let .source original ← store.read origin | none
      if payload=original then do
        let (journalOrigin,journalTime,journalPayload) ← store.captured record
        if origin=journalOrigin ∧ created=journalTime ∧ payload=journalPayload then
          step decoder maxAge store (.activate record target)
        else none
      else none
  | command => step decoder maxAge store command
-- Class (b): actual source-checked execution propagates any missing or forged record rejection.
def checkedRun (decoder : Option (S → T)) (maxAge : Nat) : Store S T → List (Command T) → Option (Store S T)
  | store,[] => some store
  | store,command::rest => (checkedStep decoder maxAge store command).bind (fun next => checkedRun decoder maxAge next rest)
-- Class (b): source initialization still consumes only raw optional payload, with no supplied record or graph.
def checkedExecute (decoder : Option (S → T)) (maxAge source : Nat) (rawSource : Option S)
    (commands : List (Command T)) : Option (Store S T) :=
  rawSource.bind (fun payload => checkedRun decoder maxAge (initial source payload) commands)
-- Class (b): absence of the actual immutable origin source event directly rejects activation.
theorem missing_origin_rejects (decoder : Option (S → T)) (maxAge : Nat) (store : Store S T)
    (record target origin created : Nat) (payload : S)
    (read : store.read record=some (.record origin created payload)) (missing : store.read origin=none) :
    checkedStep decoder maxAge store (.activate record target)=none := by simp [checkedStep,read,missing]
-- Class (b): mismatching actual record/source payloads directly reject, even with unchanged ancestry edges.
theorem forged_payload_rejects (decoder : Option (S → T)) (maxAge : Nat) (store : Store S T)
    (record target origin created : Nat) (recordPayload sourcePayload : S)
    (read : store.read record=some (.record origin created recordPayload))
    (sourceRead : store.read origin=some (.source sourcePayload)) (different : recordPayload≠sourcePayload) :
    checkedStep decoder maxAge store (.activate record target)=none := by
  simp [checkedStep,read,sourceRead,different]
-- Class (b): all base time/decoder/freshness failures remain direct rejection in the source-checked interpreter.
theorem base_failure_rejects (decoder : Option (S → T)) (maxAge : Nat) (store : Store S T)
    (record target : Nat) (failed : step decoder maxAge store (.activate record target)=none) :
    checkedStep decoder maxAge store (.activate record target)=none := by
  simp only [checkedStep]
  cases read : store.read record with
  | none => rfl
  | some value =>
    cases value with
    | source p => rfl
    | target p => rfl
    | record origin stamp payload =>
      cases sourceRead : store.read origin with
      | none => simp [read,sourceRead]
      | some value =>
        cases value with
        | record o s p => simp [read,sourceRead]
        | target p => simp [read,sourceRead]
        | source original => simp [read,sourceRead,failed]
-- Class (b): source-checked interpreter executes the declared program on actual initial inputs, for arbitrary raw twin payload.
theorem actual_checked_program (source record target twin duration maxAge : Nat) (decode : S → T)
    (payload : S) (rawTwin : T) (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1 ≤ maxAge) :
    checkedExecute (some decode) maxAge source (some payload)
      (destructiveWithTwin source record target twin duration rawTwin)=
      some (withRawTwin source record target twin duration decode payload rawTwin) := by
  simp [checkedExecute,checkedRun,checkedStep,step,destructiveWithTwin,initial,withRawTwin,activated,dormant,erased,captured,put,switch,
    show 2+duration ≤ maxAge+1 by omega,show 1 ≤ 2+duration by omega,
    sr,st,sw,rt,rw,tw,Ne.symm sr,Ne.symm st,Ne.symm sw,Ne.symm rt,Ne.symm rw,Ne.symm tw]
-- Class (b): adversarial raw record overwrite retains old origin/stamp/edges, rather than supplying a failed verdict.
def alterRecord (store : Store S T) (record : Nat) (rawReplacement : S) : Option (Store S T) := do
  let .record origin created _ ← store.read record | none
  some {store with read := put store.read record (.record origin created rawReplacement)}
-- Class (b): the actual raw alteration of a computed dormant record yields a defined altered store.
theorem actual_record_alteration (source record duration : Nat) (payload replacement : S) :
    alterRecord (dormant source record duration payload : Store S T) record replacement=
      some {(dormant source record duration payload : Store S T) with read := put (dormant source record duration payload : Store S T).read record (.record source 1 replacement)} := by
  simp [alterRecord,dormant,erased,captured,put]
-- Class (b): actual forged dormant record rejects while its preexisting operational graph is retained.
theorem altered_record_rejects (source record target duration maxAge : Nat) (payload replacement : S)
    (decoder : Option (S → T)) (sr : source≠record) (different : replacement≠payload) :
    (alterRecord (dormant source record duration payload : Store S T) record replacement).bind
      (fun altered => checkedStep decoder maxAge altered (.activate record target))=none := by
  rw [actual_record_alteration]
  simp [checkedStep,dormant,erased,captured,initial,put,sr,different]
end CSTTT.FallbackTheory.SourceCheckedTrace

namespace CSTTT.FallbackTheory.SourceCheckedTrace
open CSTTT.FallbackTheory.OperationalTrace
variable {S T : Type} [DecidableEq S]
-- Class (b): exact source/journal agreement makes checked activation equal the original time/decoder-checked operation.
theorem journal_checked_step_eq (decoder : Option (S → T)) (maxAge : Nat) (store : Store S T)
    (record target origin created : Nat) (payload original : S)
    (read : store.read record=some (.record origin created payload))
    (sourceRead : store.read origin=some (.source original))
    (journal : store.captured record=some (origin,created,payload)) (same : payload=original) :
    checkedStep decoder maxAge store (.activate record target)=step decoder maxAge store (.activate record target) := by
  simp [checkedStep,read,sourceRead,journal,same]
-- Class (b): raw journal mismatch directly rejects the checked activation readout.
theorem journal_mismatch_rejects (decoder : Option (S → T)) (maxAge : Nat) (store : Store S T)
    (record target origin created journalOrigin journalTime : Nat) (payload original journalPayload : S)
    (read : store.read record=some (.record origin created payload))
    (sourceRead : store.read origin=some (.source original))
    (journal : store.captured record=some (journalOrigin,journalTime,journalPayload))
    (different : ¬ (origin=journalOrigin ∧ created=journalTime ∧ payload=journalPayload)) :
    checkedStep decoder maxAge store (.activate record target)=none := by
  simp [checkedStep,read,sourceRead,journal,different]
-- Class (b): declared adversarial record replacement changes only raw record fields, retaining the computed journal/edges.
def replaceRecord (store : Store S T) (record rawOrigin rawTime : Nat) (rawPayload : S) : Option (Store S T) := do
  let .record _ _ _ ← store.read record | none
  some {store with read := put store.read record (.record rawOrigin rawTime rawPayload)}
-- Class (b): the complete actual prefix constructs the dormant store and its journal for every partial decoder.
theorem actual_checked_prefix (decoder : Option (S → T)) (maxAge source record duration : Nat)
    (payload : S) (sr : source≠record) :
    checkedRun decoder maxAge (initial source payload) [.snapshot source record,.erase source,.gap duration]=
      some (dormant source record duration payload) := by
  simp [checkedRun,checkedStep,step,initial,dormant,erased,captured,put,switch,sr,Ne.symm sr]
-- Class (b): actual source snapshot journal is derived from execution rather than supplied as an authentication verdict.
theorem actual_snapshot_journal (source record duration : Nat) (payload : S) :
    (dormant source record duration payload : Store S T).captured record=some (source,1,payload) := by
  simp [dormant,erased,captured]
-- Class (b): restamping the actual dormant record cannot rejuvenate it against its original execution journal.
theorem actual_retiming_rejects (decoder : Option (S → T)) (maxAge source record target duration newTime : Nat)
    (payload : S) (sr : source≠record) (changed : newTime≠1) :
    (checkedRun decoder maxAge (initial source payload) [.snapshot source record,.erase source,.gap duration]).bind
      (fun dormantStore => (replaceRecord dormantStore record source newTime payload).bind
        (fun altered => checkedStep decoder maxAge altered (.activate record target)))=none := by
  rw [actual_checked_prefix decoder maxAge source record duration payload sr]
  simp [replaceRecord,checkedStep,dormant,erased,captured,initial,put,sr,changed]
-- Class (b): checked activation presence iff all actual source/journal agreements and the complete underlying operation hold.
theorem checked_activation_present_iff (decoder : Option (S → T)) (maxAge : Nat) (store : Store S T)
    (record target : Nat) :
    (checkedStep decoder maxAge store (.activate record target)).isSome=true ↔
      ∃ origin created payload original, store.read record=some (.record origin created payload) ∧
        store.read origin=some (.source original) ∧ store.captured record=some (origin,created,payload) ∧
        payload=original ∧ (step decoder maxAge store (.activate record target)).isSome=true := by
  constructor
  · intro present
    cases read : store.read record with
    | none => simp [checkedStep,read] at present
    | some content =>
      cases content with
      | source p => simp [checkedStep,read] at present
      | target p => simp [checkedStep,read] at present
      | record origin created payload =>
        cases sourceRead : store.read origin with
        | none => simp [checkedStep,read,sourceRead] at present
        | some content =>
          cases content with
          | record o t p => simp [checkedStep,read,sourceRead] at present
          | target p => simp [checkedStep,read,sourceRead] at present
          | source original =>
            cases journal : store.captured record with
            | none => simp [checkedStep,read,sourceRead,journal] at present
            | some entry =>
              rcases entry with ⟨journalOrigin,journalTime,journalPayload⟩
              by_cases same : payload=original
              · by_cases agree : origin=journalOrigin ∧ created=journalTime ∧ payload=journalPayload
                · have journalExact : store.captured record=some (origin,created,payload) := by
                    rw [agree.1,agree.2.1,agree.2.2]
                    exact journal
                  rw [journal_checked_step_eq decoder maxAge store record target origin created payload original
                    read sourceRead journalExact same] at present
                  exact ⟨origin,created,payload,original,rfl,sourceRead,
                    (by simpa only [journal] using journalExact),same,present⟩
                · rw [journal_mismatch_rejects decoder maxAge store record target origin created journalOrigin journalTime
                    payload original journalPayload read sourceRead journal agree] at present
                  simp at present
              · rw [forged_payload_rejects decoder maxAge store record target origin created payload original
                  read sourceRead same] at present
                simp at present
  · rintro ⟨origin,created,payload,original,read,sourceRead,journal,same,base⟩
    rw [journal_checked_step_eq decoder maxAge store record target origin created payload original read sourceRead journal same]
    exact base
end CSTTT.FallbackTheory.SourceCheckedTrace
