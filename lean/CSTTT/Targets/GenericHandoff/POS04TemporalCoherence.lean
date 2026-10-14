import CSTTT.Targets.GenericHandoff.TemporalRuntimeCoherence
import CSTTT.Targets.GenericHandoff.POS04TemporalRuntime
import CSTTT.Targets.GenericHandoff.POS04DispatcherEquivalence

/-! Exact temporal clause/runtime coherence for arbitrary partial POS-04
assignments, on both tags and ALL register contexts. The only representation
change is the proved injective predictive alphabet and owner relabeling. The
runtime executes the actual assigned rows and updater, including every ambient
branch; it does not select predictive-class representatives. This closes the
temporal component binding, not the resource/acquisition RawHandoff assembly. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04TemporalCoherence
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TransportTheory RegisterInterpreter
open POS04RegisterDynamics

abbrev Predictive := TemporalFactorRules.Predictive Ambient

def readouts (tag : Tag) : RegisterFuture.Readouts Cell Value Register RegisterValue
    Predictive (List KState × List EventId) Bool :=
  ⟨.map POS04TemporalFactor.predictionImage (predictiveExpression tag),
   .register Register.counter,.register Register.ticks,.register Register.counter,
   writerExpression tag,recordExpression tag,.register Register.residue,.register Register.funded,
   .map (fun (r : ResourceData) => tagCarrierId r.owner) (.cell (Cell.resources tag))⟩

def runtime (tag : Tag) : RegisterFuture.Raw Cell Value Register RegisterValue
    LaneDisturbance Action Ambient Predictive (List KState × List EventId) Bool :=
  ⟨ambientStates,actions,[.nominal],2,POS04RegisterFuture.enabledRow tag,program tag,readouts tag⟩

def projection : E Unit (TemporalFactorRules.Run Ambient KState EventId) :=
  .map (fun (p : Ambient × Nat × Nat × (List KState × List EventId) × Bool) =>
    ⟨p.1,p.2.1,p.2.2.1,p.2.2.2.1,p.2.2.2.2⟩)
    (.pair (.register Register.factor) (.pair (.register Register.counter)
      (.pair (.register Register.ticks) (.pair (.register Register.residue) (.register Register.funded)))))

def raw (tag : Tag) : TemporalRuntimeCoherence.Raw Cell Value Register RegisterValue
    KState Action Ambient HistoryId RouteId CSTTT.POS04.Stage EventId Tag LaneDisturbance :=
  ⟨POS04TemporalFactor.schema tag,POS04TemporalFactor.bindings tag,runtime tag,projection,tagCarrierId⟩

theorem dependencies_complete (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (clauseScope tag .c6) a) : Complete (temporalDependencies tag) a := by
  intro k hk
  apply hc k
  simp [temporalDependencies,coreDependencies] at hk
  rcases hk with hk | hk | hk | hk | hk | hk | hk | hk | hk <;>
    subst k <;> cases tag <;> decide

theorem runtime_ready (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) : RegisterFuture.RawReady (runtime tag) a :=
  POS04RegisterFuture.ready a tag hc

theorem ready (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (clauseScope tag .c6) a) : TemporalRuntimeCoherence.Ready (raw tag) a :=
  ⟨⟨_,POS04TemporalFactor.decoded_complete a tag hc⟩,
   runtime_ready a tag (dependencies_complete a tag hc),by simp [raw,projection,Expr.dependencies,Complete]⟩

theorem data_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : TemporalRuntimeCoherence.Ready (raw tag) a) :
    TemporalRuntimeCoherence.data (raw tag) a h = POS04TemporalFactor.raw (runInputs6 a tag) tag := by
  have hc := (POS04TemporalFactor.decoded_complete_iff a tag).mp h.1
  exact Option.some.inj ((TemporalRuntimeCoherence.decoded_data (raw tag) a h).symm.trans
    (POS04TemporalFactor.decoded_complete a tag hc))

theorem project_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : TemporalRuntimeCoherence.Ready (raw tag) a) (x : Registers Register RegisterValue) :
    TemporalRuntimeCoherence.project (raw tag) a h x =
      POS04TemporalFactor.encodeRun (decodeRun x) := by
  apply Option.some.inj
  exact (RegisterFuture.read_eq projection a h.2.2 x).symm.trans (by rfl)

private theorem read_value (e : E Unit X) (a : CSTTT.POS04.Assigned.Assignment)
    (h : Complete e.dependencies a) (x : Registers Register RegisterValue) (v : X)
    (hv : e.eval a x () = some v) : RegisterFuture.read e a h x = v :=
  Option.some.inj ((RegisterFuture.read_eq e a h x).symm.trans hv)

theorem observation_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (hc : Complete (temporalDependencies tag) a) (x : Run6) :
    RegisterFuture.observation (runtime tag) a (runtime_ready a tag hc) (encode x) =
      TemporalRuntimeCoherence.observationImage tagCarrierId
        (POS04TemporalFactor.observationImage (observation6 (runInputs6 a tag) tag x)) := by
  have ownerEval : (readouts tag).owner.eval a (encode x) () =
      some (tagCarrierId (runInputs6 a tag).resource.owner) := by
    have hr := cell_value (hc (.resources tag) (by simp [temporalDependencies]))
    simp only [readouts,Expr.eval]
    rw [hr]
    cases tag <;> rfl
  have predictiveEval : (readouts tag).predictive.eval a (encode x) () =
      some (POS04TemporalFactor.predictionImage (predictive6 (runInputs6 a tag) x.factor)) := by
    simp only [readouts,Expr.eval,predictive_eval a tag hc x,Option.map_some]
  change (Expr.map POS04TemporalFactor.predictionImage (predictiveExpression tag) : E Unit Predictive).eval a (encode x) () = _ at predictiveEval
  change (Expr.map (fun (r : ResourceData) => tagCarrierId r.owner) (.cell (Cell.resources tag)) : E Unit CarrierId).eval a (encode x) () = _ at ownerEval
  unfold RegisterFuture.observation
  simp only [runtime,readouts]
  rw [read_value _ _ _ _ _ predictiveEval,
      read_value _ _ _ _ _ (show (Expr.register Register.counter : E Unit Nat).eval a (encode x) () = some x.counter from rfl),
      read_value _ _ _ _ _ (show (Expr.register Register.ticks : E Unit Nat).eval a (encode x) () = some x.ticks from rfl),
      read_value _ _ _ _ _ (record_eval a tag hc x),
      read_value _ _ _ _ _ (show (Expr.register Register.residue : E Unit (List KState × List EventId)).eval a (encode x) () = some x.residue from rfl),
      read_value _ _ _ _ _ (show (Expr.register Register.funded : E Unit Bool).eval a (encode x) () = some x.funded from rfl),
      read_value _ _ _ _ _ ownerEval]
  rfl

set_option maxRecDepth 4096

/-- No acceptance hypothesis: all runtime equations hold whenever the actual
inputs are present, even for a complete but rejected clause assignment. -/
theorem laws (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : TemporalRuntimeCoherence.Ready (raw tag) a) : TemporalRuntimeCoherence.Laws (raw tag) a h := by
  have hc := (POS04TemporalFactor.decoded_complete_iff a tag).mp h.1
  have ht := dependencies_complete a tag hc
  refine ⟨fun _ _ he => tag_carrier_id_injective _ _ he,rfl,?_,?_,?_,?_,?_,?_⟩
  · intro x da
    rw [data_eq,project_eq]
    have he := POS04RegisterFuture.row_eq a tag ht (decodeRun x) da.1 da.2
    simp only [encode_decode] at he
    rw [show RegisterFuture.row (raw tag).runtime a h.2.1 x da =
      RegisterFuture.row (POS04RegisterFuture.raw tag) a (POS04RegisterFuture.ready a tag ht) x da from rfl,he]
    simp only [raw,TemporalFactorRules.actualRows,actualRows6,POS04TemporalFactor.row_eq]
    rfl
  · intro x da o
    rw [project_eq,data_eq,project_eq]
    have hn := POS04RegisterFuture.next_eq a tag ht (decodeRun x) da.1 da.2 o
    simp only [encode_decode] at hn
    rw [show RegisterFuture.next (raw tag).runtime a h.2.1 x da o =
      RegisterFuture.next (POS04RegisterFuture.raw tag) a (POS04RegisterFuture.ready a tag ht) x da o from rfl,hn]
    simp only [decode_encode]
    exact (POS04TemporalFactor.updater_eq a tag (decodeRun x) da.2 o).symm
  · intro x
    rw [data_eq,project_eq]
    have ho := observation_eq a tag ht (decodeRun x)
    simp only [encode_decode] at ho
    rw [show RegisterFuture.observation (raw tag).runtime a h.2.1 x =
      RegisterFuture.observation (runtime tag) a (runtime_ready a tag ht) x from rfl,ho]
    change _ = TemporalRuntimeCoherence.observationImage tagCarrierId
      (TemporalFactorRules.observe (POS04TemporalFactor.schema tag) (POS04TemporalFactor.raw (runInputs6 a tag) tag) 2 (POS04TemporalFactor.encodeRun (decodeRun x)))
    rw [POS04TemporalFactor.observation_eq]
    rfl
  · intro x
    rw [project_eq]
    rfl
  · intro x
    rw [data_eq,project_eq]
    change (writerExpression tag).eval a x () = some (TemporalFactorRules.writer
      (POS04TemporalFactor.schema tag) (POS04TemporalFactor.raw (runInputs6 a tag) tag) (decodeRun x).residue)
    simpa only [encode_decode,POS04TemporalFactor.writer_eq] using writer_eval a tag ht (decodeRun x)
  · intro p _
    refine ⟨encode (POS04TemporalFactor.decodeRun p),?_⟩
    rw [project_eq]
    simp only [decode_encode,POS04TemporalFactor.encode_decode]

/-- Exact biconditional for arbitrary PARTIAL assignments, not only canonical
truth. In particular no missing cell is repaired by a decoder default. -/
theorem valid_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    TemporalRuntimeCoherence.Valid (raw tag) a ↔ C6Accept a tag := by
  constructor
  · intro hv
    exact (POS04TemporalFactor.generic_c6_iff a tag).mp
      (TemporalRuntimeCoherence.valid_clause (raw tag) a hv)
  · intro ha
    let h := ready a tag ha.1.1.1
    refine ⟨h,?_,laws a tag h⟩
    obtain ⟨d,hd,haccept⟩ := (POS04TemporalFactor.generic_c6_iff a tag).mpr ha
    have he := Option.some.inj (hd.symm.trans (TemporalRuntimeCoherence.decoded_data (raw tag) a h))
    exact he ▸ haccept

theorem dispatcher_rule (tag : Tag) :
    (POS04Dispatcher.package tag).rule .c6 = TemporalRuntimeCoherence.rule (raw tag) := rfl

theorem canonical_valid (tag : Tag) : TemporalRuntimeCoherence.Valid (raw tag) canonical :=
  (valid_iff canonical tag).mpr (canonical_accept6 tag)

theorem accepted_all_words (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (ha : C6Accept a tag) :
    ∃ h : TemporalRuntimeCoherence.Ready (raw tag) a,
      FullFutureSufficient (RegisterFuture.future (runtime tag) a h.2.1) :=
  TemporalRuntimeCoherence.soundness (raw tag) a ((valid_iff a tag).mpr ha)

theorem per_tag_controls :
    (TemporalRuntimeCoherence.Valid (raw .source) canonical ∧
      TemporalRuntimeCoherence.Valid (raw .target) canonical) ∧
    (TemporalRuntimeCoherence.Valid (raw .source) (futureBreak6 canonical) ∧
      ¬ TemporalRuntimeCoherence.Valid (raw .target) (futureBreak6 canonical)) ∧
    (TemporalRuntimeCoherence.Valid (raw .source) (recordBreak6 canonical) ∧
      ¬ TemporalRuntimeCoherence.Valid (raw .target) (recordBreak6 canonical)) ∧
    (¬ TemporalRuntimeCoherence.Valid (raw .source) (missingMix6 canonical) ∧
      ¬ TemporalRuntimeCoherence.Valid (raw .target) (missingMix6 canonical)) := by
  simp only [valid_iff]
  exact c6_m3b_per_tag_outcomes

theorem missing_cell_guard (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (k : Cell) (hk : k ∈ clauseScope tag .c6) :
    ¬ TemporalRuntimeCoherence.Valid (raw tag) (CSTTT.POS04.Assigned.put a k none) :=
  TemporalRuntimeCoherence.missing_clause_input (raw tag) _ k
    ((POS04TemporalFactor.scope_membership tag k).mpr hk) (by simp)

theorem zero_ledger_guard (tag : Tag) :
    ¬ TemporalRuntimeCoherence.Valid (raw tag) (zeroLedger6 canonical) :=
  fun h => c6_zero_ledger_rejected tag ((valid_iff _ _).mp h)

/-- Proposed interpreter changes leave the decoded clause primitives, their
schema and projection untouched. They are guards, not new model declarations. -/
def proposal (tag : Tag) (r : RegisterFuture.Raw Cell Value Register RegisterValue
    LaneDisturbance Action Ambient Predictive (List KState × List EventId) Bool) :=
  {raw tag with runtime := r}

theorem proposal_ready (tag : Tag) (r : RegisterFuture.Raw Cell Value Register RegisterValue
    LaneDisturbance Action Ambient Predictive (List KState × List EventId) Bool) :
    TemporalRuntimeCoherence.Ready (proposal tag r) canonical :=
  ⟨⟨_,POS04TemporalFactor.decoded_canonical tag⟩,
   ⟨canonical_complete _,fun _ => canonical_complete _,canonical_complete _⟩,canonical_complete _⟩

theorem proposal_data (tag : Tag) (r : RegisterFuture.Raw Cell Value Register RegisterValue
    LaneDisturbance Action Ambient Predictive (List KState × List EventId) Bool)
    (h : TemporalRuntimeCoherence.Ready (proposal tag r) canonical) :
    TemporalRuntimeCoherence.data (proposal tag r) canonical h =
      POS04TemporalFactor.raw (runInputs6 canonical tag) tag :=
  Option.some.inj ((TemporalRuntimeCoherence.decoded_data _ _ h).symm.trans
    (POS04TemporalFactor.decoded_canonical tag))

theorem proposal_project (tag : Tag) (r : RegisterFuture.Raw Cell Value Register RegisterValue
    LaneDisturbance Action Ambient Predictive (List KState × List EventId) Bool)
    (h : TemporalRuntimeCoherence.Ready (proposal tag r) canonical)
    (x : Registers Register RegisterValue) :
    TemporalRuntimeCoherence.project (proposal tag r) canonical h x =
      POS04TemporalFactor.encodeRun (decodeRun x) :=
  Option.some.inj ((RegisterFuture.read_eq projection canonical h.2.2 x).symm.trans (by rfl))

def emptyRows (tag : Tag) := {runtime tag with row := .literal []}
def stationary (tag : Tag) :=
  {runtime tag with program := fun r => .register r}
def cappedProgress (tag : Tag) :=
  {runtime tag with readouts := {readouts tag with
    progress := .map (fun n : Nat => min n 2) (.register Register.counter)}}

theorem empty_rows_rejected (tag : Tag) :
    ¬ TemporalRuntimeCoherence.Valid (proposal tag (emptyRows tag)) canonical := by
  let h := proposal_ready tag (emptyRows tag)
  let x := encode (initial6 canonical tag .p0w0 .a)
  apply TemporalRuntimeCoherence.row_guard _ _ h x (.nominal,.stay)
  rw [proposal_data,proposal_project]
  have he : RegisterFuture.row (proposal tag (emptyRows tag)).runtime canonical h.2.1 x
      (.nominal,.stay) = [] :=
    Option.some.inj ((RegisterFuture.row_eq _ _ _ _ _).symm.trans (by rfl))
  rw [he]
  cases tag <;> decide

theorem stationary_rejected (tag : Tag) :
    ¬ TemporalRuntimeCoherence.Valid (proposal tag (stationary tag)) canonical := by
  let h := proposal_ready tag (stationary tag)
  let x := encode (initial6 canonical tag .p0w0 .a)
  apply TemporalRuntimeCoherence.successor_guard _ _ h x (.nominal,.stay) (.inK .p0w0)
  rw [proposal_project,proposal_project,proposal_data]
  have hn : RegisterFuture.next (proposal tag (stationary tag)).runtime canonical h.2.1 x
      (.nominal,.stay) (.inK .p0w0) = x := by
    funext k
    exact Option.some.inj ((checked_execute_eq _ _ _ _ _ k).symm.trans (by rfl))
  rw [hn]
  intro he
  have hc := congrArg TemporalFactorRules.Run.counter he
  change (0 : Nat) = 1 at hc
  contradiction

theorem capped_progress_rejected (tag : Tag) :
    ¬ TemporalRuntimeCoherence.Valid (proposal tag (cappedProgress tag)) canonical := by
  let h := proposal_ready tag (cappedProgress tag)
  let x := encode (show Run6 from ⟨.inK .p0w0,3,3,([],[]),true⟩)
  apply TemporalRuntimeCoherence.observation_field_guard _ _ h x TemporalSnapshotReadout.progress
  rw [proposal_data,proposal_project]
  change RegisterFuture.read
    (show E Unit Nat from .map (fun n : Nat => min n 2) (.register Register.counter))
    canonical (canonical_complete _) x ≠ _
  rw [read_value _ _ _ _ (2 : Nat) (by rfl)]
  change (2 : Nat) ≠ 3
  decide

end CSTTT.TargetTheory.GenericHandoff.POS04TemporalCoherence
