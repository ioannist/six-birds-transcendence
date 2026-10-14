import CSTTT.Targets.GenericHandoff.ExposureRules
import CSTTT.Targets.GenericHandoff.POS04ObjecthoodProtocol
import CSTTT.POS04.Assigned.C457Guards

/-! Exact arbitrary-partial-assignment adapter for the C4 surrogate. The
positive exposure theorem expressly documents failure of full HIDD. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04Exposure
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

def schema : ExposureRules.Schema KState Action Ambient HistoryId :=
  ⟨POS04ProfileRules.clauseSchema,.split⟩
def instruction : CurrentChannel → ExposureRules.Channel
  | .publicPosition => .position | .deadlineAvailability => .availability | .canonicalM => .predictive

def raw (d : ExtraInputs) : ExposureRules.Raw KState Action Ambient HistoryId :=
  ⟨d.base.rows,d.base.positions,d.base.hazards,d.channels.map instruction,
    d.base.policy,d.histories,d.base.publishedM⟩

theorem predictive_eq (d : ExtraInputs) : ExposureRules.predictive schema (raw d) = predictive d.base := rfl

theorem channel_eq (d : ExtraInputs) (c : CurrentChannel) (s : KState) :
    ExposureRules.channel schema (raw d) (instruction c) s = currentChannel d c s := by cases c <;> rfl

theorem current_eq (d : ExtraInputs) : ExposureRules.current schema (raw d) = current d := by
  funext s
  change ((d.channels.map instruction).map fun c => ExposureRules.channel schema (raw d) c s) = _
  rw [List.map_map]
  apply List.map_congr_left
  intro c hc
  exact channel_eq d c s

theorem weight_eq (d : ExtraInputs) (s t : KState) :
    ExposureRules.weight schema (raw d) s t = rowWeight (d.base.rows s (d.base.policy s)) t := by
  rw [POS04ObjecthoodQuotient.rowWeight_sum]
  unfold ExposureRules.weight
  apply congrArg List.sum
  apply List.map_congr_left
  intro e he
  cases e.1 <;> simp [schema,POS04ProfileRules.clauseSchema,POS04ProfileRules.schema]

theorem collision_iff (d : ExtraInputs) : ExposureRules.Collision schema (raw d) ↔ Collision4 d := by
  unfold ExposureRules.Collision
  rw [current_eq,predictive_eq]
  rfl

theorem connector_iff (d : ExtraInputs) : ExposureRules.Connector schema (raw d) ↔ Connector4 d := by
  have hw : (fun e : KState × KState => decide (ExposureRules.weight schema (raw d) e.1 e.2 > 0)) =
      fun e => decide (rowWeight (d.base.rows e.1 (d.base.policy e.1)) e.2 > 0) := by
    funext e; rw [weight_eq]
  unfold ExposureRules.Connector
  rw [collision_iff,hw]
  rfl

theorem exposed_iff (d : ExtraInputs) : ExposureRules.Exposed schema (raw d) ↔ Exposed4 d := by
  constructor
  · rintro ⟨c,hc,hn,hf⟩
    change c ∈ d.channels.map instruction at hc
    obtain ⟨c0,h0,he⟩ := List.mem_map.mp hc
    subst c
    refine ⟨c0,h0,?_,?_⟩
    · simpa only [channel_eq] using hn
    · simpa only [channel_eq,predictive_eq] using hf
  · rintro ⟨c,hc,hn,hf⟩
    refine ⟨instruction c,List.mem_map.mpr ⟨c,hc,rfl⟩,?_,?_⟩
    · simpa only [channel_eq] using hn
    · simpa only [channel_eq,predictive_eq] using hf

theorem gate_iff (d : ExtraInputs) : ExposureRules.Gate schema (raw d) ↔
    RowsValid d.base ∧ MLinked d.base ∧ (connector d).head? = some hiddenPair.1 ∧
      (connector d).getLast? = some hiddenPair.2 ∧ (connector d).length ≥ 2 := by
  unfold ExposureRules.Gate
  rw [and_iff_right (show ProfileRules.DomainCheck schema.base from POS04ProfileRules.domain_checked)]
  rfl

def bindings (tag : Tag) : ExposureRules.Bindings Cell Value KState Action Ambient HistoryId :=
  ⟨⟨.rows tag,id⟩,⟨.positions,id⟩,⟨.hazards,id⟩,
    ⟨.channels,fun cs => cs.map instruction⟩,⟨.policy,id⟩,⟨.histories,id⟩,⟨.publishedM,id⟩⟩

theorem scope_eq (tag : Tag) : (bindings tag).scope = clauseScope tag .c4 := rfl

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
open Classical in
theorem decoded_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ExposureRules.decoded (bindings tag) a =
      if CSTTT.POS04.Assigned.Complete (clauseScope tag .c4) a then
        some (raw (extraInputs a tag)) else none := by
  cases hr : a (.rows tag) <;> cases hp : a .positions <;> cases hh : a .hazards <;>
    cases hc : a .channels <;> cases hpol : a .policy <;> cases hhist : a .histories <;>
    cases hm : a .publishedM <;>
    simp [ExposureRules.decoded,bindings,CellView.read,raw,extraInputs,inputs,
      CSTTT.POS04.Assigned.Complete,clauseScope,commonScope,hr,hp,hh,hc,hpol,hhist,hm]

theorem raw_scoped (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    raw (extraInputs a tag) = raw (clauseExtra a tag .c4) := by cases tag <;> rfl

theorem generic_c4_gate_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ExposureRules.AssignedGate schema (bindings tag) a ↔ C4Gate a tag := by
  unfold ExposureRules.AssignedGate C4Gate Ready
  rw [decoded_eq,raw_scoped]
  by_cases h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c4) a <;>
    simp [h,gate_iff,clauseExtra,extraInputs,clauseInputs]

theorem generic_c4_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ExposureRules.AssignedAccept schema (bindings tag) a ↔ C4Accept a tag := by
  unfold ExposureRules.AssignedAccept C4Accept C4Gate Ready
  rw [decoded_eq,raw_scoped]
  by_cases h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c4) a <;>
    simp [h,ExposureRules.SurrogateAccept,gate_iff,collision_iff,connector_iff,exposed_iff,
      clauseExtra,extraInputs,clauseInputs]

theorem canonical_accept (tag : Tag) : ExposureRules.AssignedAccept schema (bindings tag) canonical :=
  (generic_c4_iff _ _).mpr (canonical_c457 tag).1

theorem canonical_full_HIDD_fails (tag : Tag) :
    ¬ ExposureRules.FullNonExposure schema (raw (clauseExtra canonical tag .c4)) := by
  unfold ExposureRules.FullNonExposure
  rw [exposed_iff]
  exact assigned_full_HIDD_nonexposure_fails tag

theorem expose_control (tag : Tag) :
    ¬ ExposureRules.AssignedAccept schema (bindings tag) (expose4 canonical) :=
  fun h => neg_c4_expose_outcome tag ((generic_c4_iff _ _).mp h)

theorem missing_rejected (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c4) :
    ¬ ExposureRules.AssignedGate schema (bindings tag) (CSTTT.POS04.Assigned.put a k none) ∧
    ¬ ExposureRules.AssignedAccept schema (bindings tag) (CSTTT.POS04.Assigned.put a k none) := by
  apply ExposureRules.missing_rejected _ _ _ k
  · simpa only [scope_eq] using hk
  · simp

theorem histories_guard (tag : Tag) :
    ¬ ExposureRules.AssignedAccept schema (bindings tag) (emptyHistories canonical) :=
  fun h => c4_histories_guard tag ((generic_c4_iff _ _).mp h)

theorem channels_guard (tag : Tag) :
    ¬ ExposureRules.AssignedAccept schema (bindings tag) (emptyChannels canonical) :=
  fun h => c4_channels_guard tag ((generic_c4_iff _ _).mp h)

private theorem collapse_guard (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (s t : KState)
    (hq : predictive (clauseExtra a tag .c4).base s = predictive (clauseExtra a tag .c4).base t)
    (hn : mClass (index s) ≠ mClass (index t)) :
    ¬ ExposureRules.AssignedAccept schema (bindings tag) a := by
  intro h
  have hl := ((generic_c4_iff _ _).mp h).1.2.1
  have he := (hl.2 s t).mp hq
  rw [hl.1] at he
  exact hn he

theorem rows_guard (tag : Tag) :
    ¬ ExposureRules.AssignedAccept schema (bindings tag) (noRows canonical tag) := by
  apply collapse_guard _ tag .p1w0 .p1w1
  · cases tag <;> rfl
  · decide

theorem positions_guard (tag : Tag) :
    ¬ ExposureRules.AssignedAccept schema (bindings tag) (flatPositions canonical) := by
  apply collapse_guard _ tag .p2w1 .p5w0
  · cases tag <;> rfl
  · decide

theorem hazards_guard (tag : Tag) :
    ¬ ExposureRules.AssignedAccept schema (bindings tag) (noHazards canonical) := by
  apply collapse_guard _ tag .p1w0 .p1w1
  · cases tag <;> rfl
  · decide

theorem classes_guard (tag : Tag) :
    ¬ ExposureRules.AssignedAccept schema (bindings tag) (flatM canonical) := by
  intro h
  have hl := ((generic_c4_iff _ _).mp h).1.2.1.1
  have he := congrFun hl .p1w0
  have hn : mClass (index KState.p1w0) ≠ 0 := by decide
  cases tag <;> change (0 : Nat) = mClass (index KState.p1w0) at he <;> exact hn he.symm

theorem policy_guard (tag : Tag) :
    ¬ ExposureRules.AssignedAccept schema (bindings tag) (stayPolicy canonical) := by
  intro h
  have hc := ((generic_c4_iff _ _).mp h).2.2.1.1
  have hn : ((connector (clauseExtra (stayPolicy canonical) tag .c4)).zip
      ((connector (clauseExtra (stayPolicy canonical) tag .c4)).drop 1)).all (fun e =>
      decide (rowWeight ((clauseExtra (stayPolicy canonical) tag .c4).base.rows e.1
        ((clauseExtra (stayPolicy canonical) tag .c4).base.policy e.1)) e.2 > 0)) = false := by
    cases tag <;> decide +kernel
  rw [hn] at hc
  contradiction

end CSTTT.TargetTheory.GenericHandoff.POS04Exposure
