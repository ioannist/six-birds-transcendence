import CSTTT.Targets.GenericHandoff.JointRules
import CSTTT.Targets.GenericHandoff.POS04Exposure

/-! Exact partial-assignment C7 adapter, at the recombination-surrogate grade.
All event, history, receiver and pairing views use the existing shared cells.
The distribution is declared coupling data, not endogenous T1 coupling. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04Joint
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

abbrev JSchema := JointRules.Schema KState Action Ambient AssemblageId HistoryId
  (Fin 2) (Fin 2) AssemblageId JointObservable CSTTT.POS04.Stage EventId
abbrev JRaw := JointRules.Raw KState Action Ambient AssemblageId HistoryId
  (Fin 2) (Fin 2) AssemblageId JointObservable CSTTT.POS04.Stage EventId

def schema : JSchema :=
  ⟨kernel,actions,ambientStates,historyIds,List.finRange 2,List.finRange 2,assemblageIds,
    (.diagonal,.crossed),.jointPairing,coupling,2,.exit,
    (fun o => match o with | .inK s => some s | _ => none),4,
    (fun s t => pNum (index s) (index t))⟩
def jointImage (j : JointData) : JointRules.Tables AssemblageId HistoryId (Fin 2) (Fin 2)
    AssemblageId JointObservable := ⟨fun _ => j.left,fun _ => j.right,j.coupling,j.reassembly,j.observables⟩
def eventImage (e : CSTTT.POS04.Event) : JointRules.Event CSTTT.POS04.Stage EventId :=
  ⟨e.id,e.fromStage,e.toStage,e.atomic,e.sourceSupport,e.targetSupport⟩
def receiverImage (r : CSTTT.POS04.Receiver) : JointRules.Receiver :=
  ⟨r.sourcePresent,r.targetReceiverFunded,r.funded,r.mixedEventRequired⟩
def raw (d : ExtraInputs) : JRaw :=
  ⟨jointImage d.joint,d.base.rows,d.base.policy,d.histories,
    (fun s t => d.base.publishedP (index s) (index t)),d.events.map eventImage,d.realized,receiverImage d.receiver⟩

theorem weight_eq (d : ExtraInputs) (s t : KState) :
    JointRules.weight schema (raw d) s t = rowWeight (d.base.rows s (d.base.policy s)) t := by
  rw [POS04ObjecthoodQuotient.rowWeight_sum]
  unfold JointRules.weight
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  cases e.1 <;> simp [schema]

theorem supported_eq (d : ExtraInputs) (h : HistoryId) :
    JointRules.supported schema (raw d) h = historySupported d h := by
  have hw : (fun e : KState × KState => decide (JointRules.weight schema (raw d) e.1 e.2 > 0)) =
    fun e => decide (rowWeight (d.base.rows e.1 (d.base.policy e.1)) e.2 > 0) := by
    funext e; rw [weight_eq]
  unfold JointRules.supported historySupported pathSupported
  change (!(d.histories h).isEmpty && ((d.histories h).zip ((d.histories h).drop 1)).all _) = _
  rw [hw]

theorem count_eq (d : ExtraInputs) (id : AssemblageId) (l r : HistoryId) :
    JointRules.pairCount (raw d) id l r = pairCount7 d id l r := by
  unfold JointRules.pairCount pairCount7
  apply congrArg List.length
  apply congrArg (fun f => (d.joint.coupling id).filter f)
  funext p
  change (decide (_ = _) && decide (_ = _)) = (_ == _ && _ == _)
  simp only [Bool.beq_eq_decide_eq]
  rfl

theorem pairing_eq (d : ExtraInputs) (id : AssemblageId) (l r : HistoryId) :
    JointRules.pairing (raw d) id l r = pairing7 d id l r := by
  simp only [JointRules.pairing,pairing7,count_eq]; rfl

theorem branchwise_eq (d : ExtraInputs) (id : AssemblageId) :
    JointRules.branchwise schema (raw d) id = branchwise7 d id := rfl

theorem distribution_eq (d : ExtraInputs) (id : AssemblageId) :
    JointRules.distribution schema (raw d) id = distribution7 d id := by
  unfold JointRules.distribution distribution7
  simp only [count_eq]; rfl

theorem display_eq (d : ExtraInputs) (id : AssemblageId) :
    JointRules.display schema (raw d) id = display7 d id := by
  unfold JointRules.display display7
  rw [distribution_eq]; rfl

theorem mixed_eq (d : ExtraInputs) : JointRules.mixed schema (raw d) = mixed7 d := by
  change ((d.events.map eventImage).any _) = _
  rw [List.any_map]
  unfold mixed7
  apply congrArg (fun f => d.events.any f)
  funext e
  cases he : e.id <;> simp [schema,raw,eventImage,he,bne,Bool.beq_eq_decide_eq]

theorem active_eq (d : ExtraInputs) : JointRules.active schema (raw d) = active7 d := by
  unfold JointRules.active
  rw [mixed_eq]
  rfl

theorem receiver_eq (d : ExtraInputs) (id : AssemblageId) :
    JointRules.receiverDisplay schema (raw d) id = receiverDisplay7 d id := by
  unfold JointRules.receiverDisplay
  rw [mixed_eq,active_eq,display_eq]
  rfl

theorem strict_iff (d : ExtraInputs) : JointRules.Strict schema (raw d) ↔ Strict7 d := by
  unfold JointRules.Strict JointRules.recombination
  simp only [branchwise_eq,display_eq]
  
  rfl

theorem local_iff (d : ExtraInputs) : JointRules.Local schema (raw d) ↔ Local7 d := Iff.rfl

theorem histories_iff (d : ExtraInputs) : JointRules.Histories schema (raw d) ↔ Histories7 d := by
  unfold JointRules.Histories
  simp only [supported_eq]
  rfl

theorem operational_iff (d : ExtraInputs) : JointRules.Operational schema (raw d) ↔ Operational7 d := by
  unfold JointRules.Operational
  rw [mixed_eq,active_eq,receiver_eq,receiver_eq]
  have hw : ∀ s t, JointRules.weight schema (raw d) s t = rowWeight (d.base.rows s (d.base.policy s)) t := weight_eq d
  simp only [hw]
  rfl

theorem rule_iff (d : ExtraInputs) : JointRules.Rule schema (raw d) ↔ C7Rule d := by
  unfold JointRules.Rule
  rw [local_iff,histories_iff,strict_iff,operational_iff]
  rfl

theorem domain_checked : JointRules.DomainCheck schema := by
  refine ⟨by decide,(by intro s; cases s <;> decide),by decide,
    (by intro a; cases a <;> decide),by decide,?_,by decide,
    (by intro h; cases h <;> decide),by decide,?_,by decide,?_,by decide,
    (by intro id; cases id <;> decide)⟩
  · intro o; cases o with
    | inK s => cases s <;> decide
    | p2w0 => decide
    | p5w1 => decide
  · exact List.mem_finRange
  · exact List.mem_finRange

theorem published_iff (d : ExtraInputs) : (raw d).publishedP = schema.canonicalP ↔ d.base.publishedP = pNum := by
  constructor
  · intro h
    funext i j
    have he := congrFun (congrFun h (stateAt i)) (stateAt j)
    simpa only [raw,schema,index_stateAt] using he
  · intro h
    simp only [raw,schema,h]

theorem gate_iff (d : ExtraInputs) : JointRules.Gate schema (raw d) ↔
    RowsValid d.base ∧ d.base.publishedP = pNum ∧ (historyIds.map d.histories).Nodup := by
  unfold JointRules.Gate
  rw [and_iff_right domain_checked,published_iff]
  change ((0 < (2 : Nat)) ∧ RowsValid d.base ∧ d.base.publishedP = pNum ∧ _) ↔ _
  simp [schema,raw]

def bindings (tag : Tag) : JointRules.Bindings Cell Value KState Action Ambient AssemblageId HistoryId
    (Fin 2) (Fin 2) AssemblageId JointObservable CSTTT.POS04.Stage EventId :=
  ⟨⟨.joint tag,jointImage⟩,⟨.rows tag,id⟩,⟨.policy,id⟩,⟨.histories,id⟩,
    ⟨.publishedP,fun p s t => p (index s) (index t)⟩,
    ⟨.eventTable,fun es => es.map eventImage⟩,⟨.realized,id⟩,⟨.receiverInput,receiverImage⟩⟩

theorem scope_eq (tag : Tag) : (bindings tag).scope = clauseScope tag .c7 := rfl

set_option maxRecDepth 16000 in
set_option maxHeartbeats 16000000 in
open Classical in
theorem decoded_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    JointRules.decoded (bindings tag) a =
      if CSTTT.POS04.Assigned.Complete (clauseScope tag .c7) a then
        some (raw (extraInputs a tag)) else none := by
  cases hj : a (.joint tag) <;> cases hr : a (.rows tag) <;> cases hp : a .policy <;>
    cases hh : a .histories <;> cases hP : a .publishedP <;> cases he : a .eventTable <;>
    cases hre : a .realized <;> cases hrc : a .receiverInput <;>
    simp [JointRules.decoded,bindings,CellView.read,raw,extraInputs,inputs,
      CSTTT.POS04.Assigned.Complete,clauseScope,hj,hr,hp,hh,hP,he,hre,hrc]

theorem raw_scoped (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    raw (extraInputs a tag) = raw (clauseExtra a tag .c7) := by cases tag <;> rfl

theorem generic_c7_gate_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    JointRules.AssignedGate schema (bindings tag) a ↔ C7Gate a tag := by
  unfold JointRules.AssignedGate C7Gate Ready
  rw [decoded_eq,raw_scoped]
  by_cases h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c7) a <;>
    simp [h,gate_iff,clauseExtra,extraInputs,clauseInputs]

theorem generic_c7_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    JointRules.AssignedAccept schema (bindings tag) a ↔ C7Accept a tag := by
  unfold JointRules.AssignedAccept C7Accept C7Gate Ready
  rw [decoded_eq,raw_scoped]
  by_cases h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c7) a <;>
    simp [h,JointRules.SurrogateAccept,gate_iff,rule_iff,clauseExtra,extraInputs,clauseInputs]

def AssignedTransport (a : CSTTT.POS04.Assigned.Assignment) : Prop :=
  JointRules.AssignedGate schema (bindings .source) a ∧
  JointRules.AssignedGate schema (bindings .target) a ∧
  JointRules.Transport schema schema (raw (clauseExtra a .source .c7))
    (raw (clauseExtra a .target .c7)) id

theorem generic_transport_iff (a : CSTTT.POS04.Assigned.Assignment) :
    AssignedTransport a ↔ CSTTT.POS04.Assigned.C7Transport a := by
  unfold AssignedTransport CSTTT.POS04.Assigned.C7Transport JointRules.Transport
  rw [generic_c7_gate_iff,generic_c7_gate_iff]
  simp only [branchwise_eq,distribution_eq]
  simp [branchwise7,raw,jointImage,schema]

theorem canonical_accept (tag : Tag) : JointRules.AssignedAccept schema (bindings tag) canonical :=
  (generic_c7_iff canonical tag).mpr (canonical_c457 tag).2.2

theorem canonical_transport : AssignedTransport canonical :=
  (generic_transport_iff canonical).mpr canonical_staged57.2

theorem controls_equivalence (v : C7Variant) (tag : Tag) :
    JointRules.AssignedAccept schema (bindings tag) (controls7 v) ↔ C7Pass v tag :=
  (generic_c7_iff _ _).trans (c7_controls_equivalence v tag)

theorem controls_transport_equivalence (v : C7Variant) :
    AssignedTransport (controls7 v) ↔ CSTTT.POS04.C7Transport v :=
  (generic_transport_iff _).trans (c7_transport_equivalence v)

theorem aggregate_control (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (aggregate7 canonical) :=
  fun h => neg_c7_aggregate_outcomes tag ((generic_c7_iff _ _).mp h)

theorem uncoupled_control (tag : Tag) :
    JointRules.Local schema (raw (clauseExtra (uncoupled7 canonical) tag .c7)) ∧
    ¬ JointRules.AssignedAccept schema (bindings tag) (uncoupled7 canonical) :=
  ⟨(local_iff _).mpr (neg_c7_uncoupled_outcomes tag).1,
   fun h => (neg_c7_uncoupled_outcomes tag).2 ((generic_c7_iff _ _).mp h)⟩

theorem transport_control :
    JointRules.AssignedAccept schema (bindings .source) (transportBreak7 canonical) ∧
    JointRules.Local schema (raw (clauseExtra (transportBreak7 canonical) .target .c7)) ∧
    ¬ JointRules.AssignedAccept schema (bindings .target) (transportBreak7 canonical) ∧
    ¬ AssignedTransport (transportBreak7 canonical) :=
  ⟨(generic_c7_iff _ _).mpr neg_c7_transport_outcomes.1,
   (local_iff _).mpr neg_c7_transport_outcomes.2.1,
   fun h => neg_c7_transport_outcomes.2.2.1 ((generic_c7_iff _ _).mp h),
   fun h => neg_c7_transport_outcomes.2.2.2 ((generic_transport_iff _).mp h)⟩

theorem exact_probabilities (tag : Tag) :
    JointRules.pairing (raw (clauseExtra canonical tag .c7)) .diagonal .repA .classB = 1/2 ∧
    JointRules.pairing (raw (clauseExtra canonical tag .c7)) .crossed .repA .split = 1/2 := by
  simp only [pairing_eq]
  exact assigned_exact_joint_probabilities tag

theorem missing_rejected (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c7) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (put a k none) :=
  fun h => c7_missing_rejected a tag k hk ((generic_c7_iff _ _).mp h)

theorem histories_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (emptyHistories canonical) :=
  fun h => c7_histories_guard tag ((generic_c7_iff _ _).mp h)

theorem events_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (emptyEvents canonical) :=
  fun h => c7_events_guard tag ((generic_c7_iff _ _).mp h)

theorem realization_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (noRealization canonical) :=
  fun h => c7_realization_guard tag ((generic_c7_iff _ _).mp h)

theorem source_presence_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (sourceWithdrawn canonical) :=
  fun h => c7_source_presence_guard tag ((generic_c7_iff _ _).mp h)

theorem receiver_funding_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (unfundedReceiver canonical) :=
  fun h => c7_receiver_funding_guard tag ((generic_c7_iff _ _).mp h)

theorem target_funding_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (unfundedTargetReceiver canonical) :=
  fun h => c7_target_funding_guard tag ((generic_c7_iff _ _).mp h)

theorem left_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (flatLeft canonical tag) :=
  fun h => c7_left_guard tag ((generic_c7_iff _ _).mp h)

theorem right_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (flatRight canonical tag) :=
  fun h => c7_right_guard tag ((generic_c7_iff _ _).mp h)

theorem coupling_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (flatCoupling canonical tag) :=
  fun h => c7_coupling_guard tag ((generic_c7_iff _ _).mp h)

theorem observable_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (noJointObservable canonical tag) :=
  fun h => c7_observable_guard tag ((generic_c7_iff _ _).mp h)

theorem reassembly_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (flatReassembly canonical tag) :=
  fun h => c7_reassembly_guard tag ((generic_c7_iff _ _).mp h)

theorem distinct_histories_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (duplicateHistories canonical) :=
  fun h => c7_duplicate_history_guard tag ((generic_c7_iff _ _).mp h)

theorem rows_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (noRows canonical tag) := by
  intro h
  have hc := ((generic_c7_iff _ _).mp h).2.2.1 .repA (by decide)
  have hn : historySupported (clauseExtra (noRows canonical tag) tag .c7) .repA = false := by
    cases tag <;> decide +kernel
  rw [hn] at hc
  contradiction

theorem policy_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (stayPolicy canonical) := by
  intro h
  have hc := ((generic_c7_iff _ _).mp h).2.2.1 .repA (by decide)
  have hn : historySupported (clauseExtra (stayPolicy canonical) tag .c7) .repA = false := by
    cases tag <;> decide +kernel
  rw [hn] at hc
  contradiction

theorem publishedP_guard (tag : Tag) :
    ¬ JointRules.AssignedAccept schema (bindings tag) (zeroP canonical) := by
  intro h
  have he := congrFun (congrFun ((generic_c7_iff _ _).mp h).1.2.1 (index .p1w0)) (index .p2w1)
  have hn : (clauseExtra (zeroP canonical) tag .c7).base.publishedP (index .p1w0) (index .p2w1) ≠
      pNum (index .p1w0) (index .p2w1) := by
    cases tag <;> decide +kernel
  exact hn he

end CSTTT.TargetTheory.GenericHandoff.POS04Joint
