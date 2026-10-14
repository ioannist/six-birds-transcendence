import CSTTT.Fallback.PredictiveBridge
import CSTTT.Fallback.OperationalTrace

namespace CSTTT.FallbackTheory.OperationalPredictiveReturn
open CSTTT.TransportTheory
open CSTTT.FallbackTheory.RawPredictiveQuotient
open CSTTT.FallbackTheory.OperationalTrace
open CSTTT.FallbackTheory.SourceCheckedTrace
variable {H S T E R SC TC RR M : Type} [DecidableEq S]
-- Class (b): the actual executed target readout preserves every raw predictive query.
theorem actual_predictive_return (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (source record target twin duration maxAge : Nat) (payload : S) (rawTwin : T)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1≤maxAge)
    (finished : Store S T) (executed : checkedExecute (some b.mapState) maxAge source (some payload)
      (destructiveWithTwin source record target twin duration rawTwin)=some finished) :
    ∃ decoded, finished.read target=some (.target decoded) ∧
      ∀ query, targetFuture b decoded query=sourceFuture b payload query := by
  have eq := Option.some.inj ((actual_checked_program source record target twin duration maxAge
    b.mapState payload rawTwin sr st sw rt rw tw age).symm.trans executed)
  rw [← eq]
  refine ⟨b.mapState payload,?_,actual_future_transport b laws payload⟩
  simp [withRawTwin,activated,put,tw]
-- Class (b): complete execution separates equal raw endpoint payloads by actual operational ancestry.
theorem actual_equal_twin_separation (b : RawBridge H S T E R SC TC RR M)
    (source record target twin duration maxAge : Nat) (payload : S) (rawTwin : T)
    (equalPayload : rawTwin=b.mapState payload)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1≤maxAge)
    (finished : Store S T) (executed : checkedExecute (some b.mapState) maxAge source (some payload)
      (destructiveWithTwin source record target twin duration rawTwin)=some finished) :
    finished.read target=finished.read twin ∧ finished.active target=true ∧ finished.active twin=true ∧
      finished.active source=false ∧ Path finished.edges source target ∧ ¬ Path finished.edges source twin := by
  have eq := Option.some.inj ((actual_checked_program source record target twin duration maxAge
    b.mapState payload rawTwin sr st sw rt rw tw age).symm.trans executed)
  rw [← eq]
  have excluded := raw_twin_excluded source record target twin duration b.mapState payload rawTwin rw tw
  refine ⟨?_,?_,?_,?_,?_,excluded⟩
  · simp [withRawTwin,activated,put,tw,equalPayload]
  · simp [withRawTwin,activated,switch,tw]
  · simp [withRawTwin,switch]
  · simp [withRawTwin,activated,dormant,erased,switch,st,sw]
  · exact .extend (y := record) (.one (by simp [withRawTwin,activated])) (by simp [withRawTwin,activated])
-- Class (b): successful execution is constructed, rather than assuming a populated store or completed trace.
theorem actual_return_exists (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (source record target twin duration maxAge : Nat) (payload : S) (rawTwin : T)
    (equalPayload : rawTwin=b.mapState payload)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1≤maxAge) :
    ∃ finished, checkedExecute (some b.mapState) maxAge source (some payload)
        (destructiveWithTwin source record target twin duration rawTwin)=some finished ∧
      (∃ decoded, finished.read target=some (.target decoded) ∧
        ∀ query, targetFuture b decoded query=sourceFuture b payload query) ∧
      finished.read target=finished.read twin ∧ finished.active target=true ∧ finished.active twin=true ∧
      finished.active source=false ∧ Path finished.edges source target ∧ ¬ Path finished.edges source twin := by
  let finished := withRawTwin source record target twin duration b.mapState payload rawTwin
  have executed := actual_checked_program source record target twin duration maxAge b.mapState payload rawTwin sr st sw rt rw tw age
  exact ⟨finished,executed,actual_predictive_return b laws source record target twin duration maxAge payload rawTwin
    sr st sw rt rw tw age finished executed,actual_equal_twin_separation b source record target twin duration maxAge
    payload rawTwin equalPayload sr st sw rt rw tw age finished executed⟩
-- Class (b): actual source event is historical evidence after erasure, while no active source token remains.
theorem actual_source_erased (b : RawBridge H S T E R SC TC RR M)
    (source record target twin duration maxAge : Nat) (payload : S) (rawTwin : T)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1≤maxAge)
    (finished : Store S T) (executed : checkedExecute (some b.mapState) maxAge source (some payload)
      (destructiveWithTwin source record target twin duration rawTwin)=some finished) :
    finished.active source=false ∧ finished.read source=some (.source payload) ∧
      finished.read record=some (.record source 1 payload) := by
  have eq := Option.some.inj ((actual_checked_program source record target twin duration maxAge
    b.mapState payload rawTwin sr st sw rt rw tw age).symm.trans executed)
  rw [← eq]
  simp [withRawTwin,activated,dormant,erased,captured,initial,put,switch,sr,st,sw,rw,rt]
end CSTTT.FallbackTheory.OperationalPredictiveReturn

namespace CSTTT.FallbackTheory.OperationalSeed
open CSTTT.TransportTheory
open CSTTT.FallbackTheory.RawPredictiveQuotient
open CSTTT.FallbackTheory.OperationalTrace
open CSTTT.FallbackTheory.SourceCheckedTrace
variable {H S T E R SC TC RR M : Type} [DecidableEq S]
-- Class (b): source/target data and graph are read ONLY from an actually computed complete execution.
def seedReadout (decoder : Option (S → T)) (maxAge source target : Nat) (rawSource : Option S)
    (commands : List (Command T)) : Option (S × T × List (Nat × Nat)) := do
  let finished ← checkedExecute decoder maxAge source rawSource commands
  let .source original ← finished.read source | none
  let .target decoded ← finished.read target | none
  some (original,decoded,finished.edges)
-- Class (b): exact finite-probe admissible operational seed; no ancestry, successorship or package verdict enters it.
def Seed (b : RawBridge H S T E R SC TC RR M) (decoder : Option (S → T))
    (maxAge source target : Nat) (rawSource : Option S) (commands : List (Command T)) : Prop :=
  ∃ original decoded edges, seedReadout decoder maxAge source target rawSource commands=some (original,decoded,edges) ∧
    Path edges source target ∧ sourceSignature b (classQueries b) original=targetSignature b (classQueries b) decoded
-- Class (b): missing consumed source yields no seed on every partial decoder/program assignment.
theorem missing_source_seed_rejected (b : RawBridge H S T E R SC TC RR M) (decoder : Option (S → T))
    (maxAge source target : Nat) (commands : List (Command T)) :
    ¬ Seed b decoder maxAge source target none commands := by simp [Seed,seedReadout,checkedExecute]
-- Class (b): actual full-program rejection refutes the computed seed directly.
theorem failed_execution_seed_rejected (b : RawBridge H S T E R SC TC RR M) (decoder : Option (S → T))
    (maxAge source target : Nat) (rawSource : Option S) (commands : List (Command T))
    (failed : checkedExecute decoder maxAge source rawSource commands=none) :
    ¬ Seed b decoder maxAge source target rawSource commands := by simp [Seed,seedReadout,failed]
-- Class (b): complete finite probe family exactly characterizes cross-carrier all-query prediction under raw laws/coverage.
theorem finite_cross_exact (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (sourceComplete : ∀ x, x∈b.sourceStates) (targetComplete : ∀ y, y∈b.targetStates)
    (bisim : SourceActionBisim b) (original : S) (decoded : T) :
    sourceSignature b (classQueries b) original=targetSignature b (classQueries b) decoded ↔
      ∀ query, sourceFuture b original query=targetFuture b decoded query := by
  obtain ⟨preimage,_,rfl⟩ := target_covered_preimage b laws decoded (targetComplete decoded)
  rw [actual_finite_signature b laws]
  constructor
  · intro equal query
    rw [actual_future_transport b laws]
    exact (finite_full_iff b sourceComplete bisim original preimage).mp equal query
  · intro equal
    apply (finite_full_iff b sourceComplete bisim original preimage).mpr
    intro query
    rw [← actual_future_transport b laws preimage query]
    exact equal query
-- Class (b): this seed returns actual source-target readouts, path and every predictive query, rather than only a score.
theorem seed_predictive_sound (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (sourceComplete : ∀ x, x∈b.sourceStates) (targetComplete : ∀ y, y∈b.targetStates)
    (bisim : SourceActionBisim b) (decoder : Option (S → T)) (maxAge source target : Nat)
    (rawSource : Option S) (commands : List (Command T))
    (seed : Seed b decoder maxAge source target rawSource commands) :
    ∃ original decoded edges, seedReadout decoder maxAge source target rawSource commands=some (original,decoded,edges) ∧
      Path edges source target ∧ ∀ query, sourceFuture b original query=targetFuture b decoded query := by
  obtain ⟨original,decoded,edges,read,path,pred⟩ := seed
  exact ⟨original,decoded,edges,read,path,(finite_cross_exact b laws sourceComplete targetComplete bisim original decoded).mp pred⟩
-- Class (b): the actual source-checked destructive program constructs an admissible seed under actual raw map laws.
theorem actual_seed_constructed (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (source record target twin duration maxAge : Nat) (payload : S) (rawTwin : T)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1≤maxAge) :
    Seed b (some b.mapState) maxAge source target (some payload)
      (destructiveWithTwin source record target twin duration rawTwin) := by
  have executed := actual_checked_program source record target twin duration maxAge b.mapState payload rawTwin sr st sw rt rw tw age
  refine ⟨payload,b.mapState payload,[(record,target),(source,record)],?_,?_,(actual_finite_signature b laws _ payload).symm⟩
  · unfold seedReadout
    rw [executed]
    simp [withRawTwin,activated,dormant,erased,captured,initial,put,sr,st,sw,tw]
  · exact .extend (y := record) (.one (by simp)) (by simp)
-- Class (b): the actual independently initialized twin cannot satisfy this seed, even when its predictive signature matches.
theorem actual_twin_seed_excluded (b : RawBridge H S T E R SC TC RR M)
    (source record target twin duration maxAge : Nat) (payload : S) (rawTwin : T)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1≤maxAge) :
    ¬ Seed b (some b.mapState) maxAge source twin (some payload)
      (destructiveWithTwin source record target twin duration rawTwin) := by
  have executed := actual_checked_program source record target twin duration maxAge b.mapState payload rawTwin sr st sw rt rw tw age
  intro seed
  obtain ⟨original,decoded,edges,read,path,_⟩ := seed
  unfold seedReadout at read
  rw [executed] at read
  simp [withRawTwin,activated,dormant,erased,captured,initial,put,sr,st,sw] at read
  rcases read with ⟨rfl,rfl,rfl⟩
  exact raw_twin_excluded source record target twin duration b.mapState payload rawTwin rw tw path
end CSTTT.FallbackTheory.OperationalSeed

namespace CSTTT.FallbackTheory.SharedOperationalSeed
open CSTTT.TransportTheory
open CSTTT.FallbackTheory.RawPredictiveQuotient
open CSTTT.FallbackTheory.OperationalTrace
open CSTTT.FallbackTheory.SourceCheckedTrace
variable {H S T E R SC TC RR M : Type} [DecidableEq S]
-- Class (b): shared primitive execution inputs, without store, edges, snapshots, ancestry or final verdict fields.
structure RawInputs (S T : Type) where
  initialSource : Nat
  rawSource : Option S
  decoder : Option (S → T)
  maxAge : Nat
  commands : List (Command T)
-- Class (b): one shared actual store is computed before any source-target pair is queried.
def computedStore (inputs : RawInputs S T) : Option (Store S T) :=
  checkedExecute inputs.decoder inputs.maxAge inputs.initialSource inputs.rawSource inputs.commands
-- Class (b): source/target/graph readout from that SAME computed store, for arbitrary requested pair addresses.
def readAt (inputs : RawInputs S T) (source target : Nat) : Option (S × T × List (Nat × Nat)) := do
  let finished ← computedStore inputs
  let .source original ← finished.read source | none
  let .target decoded ← finished.read target | none
  some (original,decoded,finished.edges)
-- Class (b): shared operational/predictive seed; changing the queried pair does not reinitialize execution.
def Seed (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T) (source target : Nat) : Prop :=
  ∃ original decoded edges, readAt inputs source target=some (original,decoded,edges) ∧
    Path edges source target ∧ sourceSignature b (classQueries b) original=targetSignature b (classQueries b) decoded
-- Class (b): the earlier single-root formulation is exactly the shared readout at the fixed initialization root.
theorem root_seed_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T) (target : Nat) :
    Seed b inputs inputs.initialSource target ↔
      CSTTT.FallbackTheory.OperationalSeed.Seed b inputs.decoder inputs.maxAge inputs.initialSource target
        inputs.rawSource inputs.commands := Iff.rfl
-- Class (b): any actually failed shared execution directly excludes EVERY queried pair.
theorem failed_store_excludes_all (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (failed : computedStore inputs=none) : ∀ source target, ¬ Seed b inputs source target := by
  intro source target
  simp [Seed,readAt,failed]
-- Class (b): missing consumed raw source excludes every seed on every partial assignment of other primitive fields.
theorem missing_source_excludes_all (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (missing : inputs.rawSource=none) : ∀ source target, ¬ Seed b inputs source target := by
  apply failed_store_excludes_all b inputs
  simp [computedStore,checkedExecute,missing]
-- Class (b): every shared seed supplies actual computed readouts/path and every predictive query under raw completeness laws.
theorem shared_seed_sound (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (sourceComplete : ∀ x, x∈b.sourceStates) (targetComplete : ∀ y, y∈b.targetStates)
    (bisim : SourceActionBisim b) (inputs : RawInputs S T) (source target : Nat)
    (seed : Seed b inputs source target) :
    ∃ original decoded edges, readAt inputs source target=some (original,decoded,edges) ∧
      Path edges source target ∧ ∀ query, sourceFuture b original query=targetFuture b decoded query := by
  obtain ⟨original,decoded,edges,read,path,pred⟩ := seed
  exact ⟨original,decoded,edges,read,path,
    (CSTTT.FallbackTheory.OperationalSeed.finite_cross_exact b laws sourceComplete targetComplete bisim original decoded).mp pred⟩
-- Class (b): actual absent incoming edges exclude every requested source at the shared completed store.
theorem disconnected_target_excludes_all (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (finished : Store S T) (executed : computedStore inputs=some finished) (target : Nat)
    (noIncoming : ∀ predecessor, (predecessor,target)∉finished.edges) : ∀ source, ¬ Seed b inputs source target := by
  intro source seed
  obtain ⟨original,decoded,edges,read,path,_⟩ := seed
  unfold readAt at read
  rw [executed] at read
  cases sourceRead : finished.read source with
  | none => simp [sourceRead] at read
  | some content =>
    cases content with
    | record o t p => simp [sourceRead] at read
    | target p => simp [sourceRead] at read
    | source payload =>
      cases targetRead : finished.read target with
      | none => simp [sourceRead,targetRead] at read
      | some content =>
        cases content with
        | record o t p => simp [sourceRead,targetRead] at read
        | source p => simp [sourceRead,targetRead] at read
        | target payload =>
          simp [sourceRead,targetRead] at read
          rcases read with ⟨rfl,rfl,rfl⟩
          exact no_incoming_excludes finished.edges target noIncoming source path
end CSTTT.FallbackTheory.SharedOperationalSeed
