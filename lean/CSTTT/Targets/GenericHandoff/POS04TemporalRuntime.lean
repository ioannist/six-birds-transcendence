import CSTTT.Targets.GenericHandoff.POS04TemporalEquivalence
import CSTTT.Targets.GenericHandoff.POS04RegisterReadoutLaws
import CSTTT.Targets.GenericHandoff.TemporalFactorClosure

/-! Exact runtime binding of the dispatched C6 schema. The equations quantify
over arbitrary partial assignments and ALL actual run contexts and successors.
The readout embedding is injective; the actual action-row branches and their
weights are unchanged. Acceptance additionally rejects every missing input.
This is a proved family simulation, not a generic irrelevance assumption. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04TemporalFactor
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit CSTTT.TransportTheory

def encodeRun (x : Run6) : TemporalFactorRules.Run Ambient KState EventId :=
  ⟨x.factor,x.counter,x.ticks,x.residue,x.funded⟩
def decodeRun (x : TemporalFactorRules.Run Ambient KState EventId) : Run6 :=
  ⟨x.factor,x.counter,x.ticks,x.residue,x.funded⟩
@[simp] theorem decode_encode (x : Run6) : decodeRun (encodeRun x) = x := by cases x <;> rfl
@[simp] theorem encode_decode (x : TemporalFactorRules.Run Ambient KState EventId) : encodeRun (decodeRun x) = x := by cases x <;> rfl

def observationImage (x : C6Observation) : TemporalFactorRules.Observation Ambient KState EventId Tag :=
  ⟨predictionImage x.predictive,x.eventOrder,x.tickPhase,x.cumulativeProgress,x.endogenousRecordCount,
    x.routeResidue,x.maintenanceState,x.owner⟩
def codeImage (x : C6Code) : TemporalFactorRules.Code Ambient KState EventId Tag :=
  ⟨predictionImage x.predictive,x.eventCount,x.tickPhase,x.routeResidue,x.maintenance,x.owner⟩

theorem observationImage_injective : Function.Injective observationImage := by
  intro x y he
  have hp : x.predictive = y.predictive := predictionImage_injective (congrArg TemporalFactorRules.Observation.predictive he)
  have hn := congrArg TemporalFactorRules.Observation.order he
  have ht := congrArg TemporalFactorRules.Observation.tickPhase he
  have hg := congrArg TemporalFactorRules.Observation.progress he
  have hr := congrArg TemporalFactorRules.Observation.record he
  have hs := congrArg TemporalFactorRules.Observation.residue he
  have hm := congrArg TemporalFactorRules.Observation.maintenance he
  have ho := congrArg TemporalFactorRules.Observation.owner he
  cases x; cases y; simp_all [observationImage]

theorem register_tuple_eq (d : RunInputs6) (t : Tag) (r : RouteId) :
    TemporalFactorRules.registerTuple (raw d t) r = routeTuple d.base r := by
  simp only [TemporalFactorRules.registerTuple,route_eq,routeTuple]
  cases he : d.base.routes.find? (fun x => x.id == r) <;> rfl

theorem writer_eq (d : RunInputs6) (t : Tag) (res : List KState × List EventId) :
    TemporalFactorRules.writer (schema t) (raw d t) res = writer6 d t res := by
  unfold TemporalFactorRules.writer
  change (routeIds.find? (fun r => decide (TemporalFactorRules.registerTuple (raw d t) r = some res))).any (d.base.writers t) = _
  simp only [register_tuple_eq,routeIds,List.find?_cons,List.find?_nil,writer6]
  by_cases ha : routeTuple d.base .a = some res <;> by_cases hb : routeTuple d.base .b = some res <;> simp [ha,hb]

theorem code_eq (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (x : Run6) :
    TemporalFactorRules.code (schema t) (raw (runInputs6 a t) t) 2 (encodeRun x) =
      codeImage ((actualFuture6 a t).code x) := by
  simp only [TemporalFactorRules.code,encodeRun,codeImage,actualFuture6,code6]
  rw [prediction_eq]
  rfl

theorem observation_eq (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (x : Run6) :
    TemporalFactorRules.observe (schema t) (raw (runInputs6 a t) t) 2 (encodeRun x) =
      observationImage ((actualFuture6 a t).observe x) := by
  simp only [TemporalFactorRules.observe,encodeRun,observationImage,actualFuture6,observation6]
  rw [prediction_eq,writer_eq]
  rfl

theorem updater_eq (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (x : Run6) (act : Action) (o : Ambient) :
    TemporalFactorRules.update (schema t) (raw (runInputs6 a t) t) (encodeRun x) act o =
      encodeRun ((actualFuture6 a t).next x act o) := by
  simp only [TemporalFactorRules.update,encodeRun,delta_eq,actualFuture6,actualUpdate6]
  rfl

theorem weight_eq (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (x : Run6) (act : Action) (o : Ambient) :
    TemporalFactorRules.weight (schema t) (raw (runInputs6 a t) t) (encodeRun x) act o =
      (actualFuture6 a t).weight x act o := by
  unfold TemporalFactorRules.weight
  have he : TemporalFactorRules.actualRows (schema t) (raw (runInputs6 a t) t) (encodeRun x) act =
      actualRows6 (runInputs6 a t) x act := by
    simp only [TemporalFactorRules.actualRows,actualRows6,row_eq]
    rfl
  rw [he]
  rfl

/-- Probability equality on every finite word, not a bounded horizon. -/
theorem word_law (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (x : Run6)
    (word : List Action) (trace : List C6Observation) :
    fullFuture (TemporalFactorRules.future (schema t) (raw (runInputs6 a t) t) 2)
      (encodeRun x) word (trace.map observationImage) = fullFuture (actualFuture6 a t) x word trace := by
  have h := FutureReindex.mapped_word_law (actualFuture6 a t)
    (TemporalFactorRules.future (schema t) (raw (runInputs6 a t) t) 2) decodeRun id observationImage
    (fun _ _ he => observationImage_injective he) rfl
    (fun y => by simpa only [encode_decode] using observation_eq a t (decodeRun y))
    (fun y act o => by simpa only [encode_decode] using weight_eq a t (decodeRun y) act o)
    (fun y act o => by
      have hn := congrArg decodeRun (updater_eq a t (decodeRun y) act o)
      simpa only [encode_decode,decode_encode] using hn)
    (encodeRun x) word trace
  simpa only [decode_encode,List.map_id] using h

/-- Dispatched acceptance entails the full actual-support word law. -/
theorem accepted_all_words (a : CSTTT.POS04.Assigned.Assignment) (t : Tag)
    (h : TemporalFactorCells.Accept (schema t) (bindings t) a) :
    FullFutureSufficient (actualFuture6 a t) := by
  obtain ⟨d,hd,ha⟩ := h
  have hc := (decoded_complete_iff a t).mp ⟨d,hd⟩
  have he := Option.some.inj (hd.symm.trans (decoded_complete a t hc))
  subst d
  have hf := TemporalFactorRules.all_words (schema t) (raw (runInputs6 a t) t) 2 ha
  intro x y hcode word trace
  have hencoded : (TemporalFactorRules.future (schema t) (raw (runInputs6 a t) t) 2).code (encodeRun x) =
      (TemporalFactorRules.future (schema t) (raw (runInputs6 a t) t) 2).code (encodeRun y) := by
    change TemporalFactorRules.code _ _ _ _ = TemporalFactorRules.code _ _ _ _
    rw [code_eq,code_eq,hcode]
  have hp := hf (encodeRun x) (encodeRun y) hencoded word (trace.map observationImage)
  simpa only [word_law] using hp

/-- The register interpreter's closure laws are proved from the SAME assigned
cells; readiness and all eleven field recipes are checked on its whole closure. -/
theorem accepted_register_laws (a : CSTTT.POS04.Assigned.Assignment) (t : Tag)
    (h : TemporalFactorCells.Accept (schema t) (bindings t) a) :
    RegisterFuture.ReadoutLawGate (POS04RegisterFuture.raw t) (POS04RegisterReadoutLaws.recipes t)
      a (POS04RegisterFuture.ready a t (POS04RegisterFuture.accepted_complete ((generic_c6_iff a t).mp h)))
      (POS04RegisterReadoutLaws.roots a t) :=
  POS04RegisterReadoutLaws.readout_gate ((generic_c6_iff a t).mp h)

/-- Uniform one-field guard: the altered expression alone leaves dynamics,
weights, and closure fixed. The independently evaluated raw recipe detects it.
An intrinsically constant lawful owner is not required to vary. -/
theorem constant_readout_guard (a : CSTTT.POS04.Assigned.Assignment) (t : Tag)
    (h : TemporalFactorCells.Accept (schema t) (bindings t) a)
    (x : RegisterInterpreter.Registers POS04RegisterDynamics.Register POS04RegisterDynamics.RegisterValue)
    (hx : RegisterFuture.Closure (POS04RegisterFuture.raw t) a
      (POS04RegisterFuture.ready a t (POS04RegisterFuture.accepted_complete ((generic_c6_iff a t).mp h)))
      (POS04RegisterReadoutLaws.roots a t) x)
    (act : Action) (o : Ambient) (f : RegisterFuture.Field)
    (expected wrong : RegisterFuture.FieldValue CSTTT.POS04.PredictiveNow (List KState × List EventId) Bool f)
    (rhs : (POS04RegisterReadoutLaws.recipes t f).eval a x (.nominal,act,o) = some expected)
    (hne : wrong ≠ expected)
    (hnew : RegisterFuture.RawReady (RegisterFuture.replaceReadout (POS04RegisterFuture.raw t) f (.literal wrong)) a) :
    ¬ RegisterFuture.ReadoutLawGate (RegisterFuture.replaceReadout (POS04RegisterFuture.raw t) f (.literal wrong))
      (POS04RegisterReadoutLaws.recipes t) a hnew (POS04RegisterReadoutLaws.roots a t) := by
  apply RegisterFuture.constant_field_guard (POS04RegisterFuture.raw t) (POS04RegisterReadoutLaws.recipes t)
    a (POS04RegisterFuture.ready a t (POS04RegisterFuture.accepted_complete ((generic_c6_iff a t).mp h)))
    (POS04RegisterReadoutLaws.roots a t) x hx .nominal (by change ComputedFIACH.LaneDisturbance.nominal ∈ [ComputedFIACH.LaneDisturbance.nominal]; decide) act
    (by change act ∈ actions; cases act <;> decide) o
    (by change o ∈ ambientStates; cases o with
        | inK k => cases k <;> decide
        | p2w0 => decide
        | p5w1 => decide) f expected wrong rhs hne hnew

theorem capped_progress_guard (t : Tag) :
    ¬ RegisterFuture.ReadoutLawGate (POS04RegisterReadoutLaws.cappedProgress t)
      (POS04RegisterReadoutLaws.recipes t) canonical (POS04RegisterReadoutLaws.capped_ready t)
      (POS04RegisterReadoutLaws.roots canonical t) := POS04RegisterReadoutLaws.capped_progress_rejected t

/-- Both tags and passing side effects are preserved exactly, including the
realized-stage sensitivity guard. -/
theorem per_tag_controls :
    (TemporalFactorCells.Accept (schema .source) (bindings .source) canonical ∧
      TemporalFactorCells.Accept (schema .target) (bindings .target) canonical) ∧
    (TemporalFactorCells.Accept (schema .source) (bindings .source) (futureBreak6 canonical) ∧
      ¬ TemporalFactorCells.Accept (schema .target) (bindings .target) (futureBreak6 canonical)) ∧
    (TemporalFactorCells.Accept (schema .source) (bindings .source) (recordBreak6 canonical) ∧
      ¬ TemporalFactorCells.Accept (schema .target) (bindings .target) (recordBreak6 canonical)) ∧
    (¬ TemporalFactorCells.Accept (schema .source) (bindings .source) (missingMix6 canonical) ∧
      ¬ TemporalFactorCells.Accept (schema .target) (bindings .target) (missingMix6 canonical)) := by
  simp only [generic_c6_iff]
  exact c6_m3b_per_tag_outcomes

theorem zero_ledger_guard (t : Tag) :
    ¬ TemporalFactorCells.Accept (schema t) (bindings t) (zeroLedger6 canonical) :=
  fun h => c6_zero_ledger_rejected t ((generic_c6_iff _ _).mp h)

end CSTTT.TargetTheory.GenericHandoff.POS04TemporalFactor
