import CSTTT.Targets.GenericHandoff.POS04OperationalGame
namespace CSTTT.TargetTheory.GenericHandoff.POS04OperationalGame
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH

/-- Withdrawal changes recharge availability, not acquired route provenance. -/
theorem acquisition_projections (m : RawLaneModel) :
    (inputs m).routes = (arrivalInputs m).base.routes ∧
    (inputs m).histories = (arrivalInputs m).base.histories ∧
    (inputs m).writers = (arrivalInputs m).base.writers := ⟨rfl,rfl,rfl⟩

theorem acquisition_tuple (m : RawLaneModel) (id : RouteId) :
    tuple (inputs m) id = routeTuple (arrivalInputs m).base id := by
  simp only [tuple,routeTuple,(acquisition_projections m).1,(acquisition_projections m).2.1]

theorem acquisition_writer (m : RawLaneModel) (residue : List KState × List EventId) :
    writer (inputs m) residue = writer6 (arrivalInputs m) .target residue := by
  simp only [writer,writer6,acquisition_tuple,(acquisition_projections m).2.2]

theorem protocol_resources (m : RawLaneModel) (h : Protocol m) :
    available8 (inputs m).viability .target = true ∧ Ledger8 (inputs m).viability ∧
    ticks6 (runInputs6 (withdrawnAssignment m) .target) = true ∧
    writers6 (runInputs6 (withdrawnAssignment m) .target) .target = true := by
  have ha := h.2.2.1
  simp only [advancementCheck,Bool.and_eq_true] at ha
  exact ⟨by rw [viability_eq]; exact ha.1.1.1.1,
    by rw [viability_eq]; exact of_decide_eq_true ha.1.1.1.2,ha.1.1.2,ha.1.2⟩

theorem protocol_tick (m : RawLaneModel) (h : Protocol m) (s : KState) (a : Action)
    (hn : ((inputs m).viability.rows s a).isEmpty = false) : (inputs m).ticks s a = 1 := by
  have ht := (protocol_resources m h).2.2.1
  have hs := List.all_eq_true.mp ht s (by cases s <;> decide)
  have ha := List.all_eq_true.mp hs a (by cases a <;> decide)
  have he : (runInputs6 (withdrawnAssignment m) .target).base.base.rows = (inputs m).viability.rows := rfl
  rw [he,hn] at ha
  simpa only [Bool.false_or,decide_eq_true_eq,← (operational_projections m).1] using ha

theorem protocol_writer (m : RawLaneModel) (h : Protocol m) (id : RouteId)
    (residue : List KState × List EventId) (ht : tuple (inputs m) id = some residue) :
    writer (inputs m) residue = true := by
  have hw := (protocol_resources m h).2.2.2
  have ha : (inputs m).writers .target .a = true := by
    rw [(operational_projections m).2.2.2]
    exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp hw).2 .a (by decide)
  have hb : (inputs m).writers .target .b = true := by
    rw [(operational_projections m).2.2.2]
    exact List.all_eq_true.mp (Bool.and_eq_true_iff.mp hw).2 .b (by decide)
  cases id <;> simp [writer,ht,ha,hb]

/-- Disassembly of an actual entry, not a chosen/reset receiver state. -/
theorem entry_execution (m : RawLaneModel) (e : WithdrawalEntry) (he : e ∈ entries m) :
    ∃ id ∈ routeIds, ∃ hist path raw,
      phase2Check m id = true ∧ routeTuple (arrivalInputs m).base id = some (hist,path) ∧
      raw ∈ (arrivalInputs m).base.base.rows (hist.getLastD .p0w0)
        ((arrivalInputs m).base.base.policy (hist.getLastD .p0w0)) ∧
      e = ⟨raw.1,raw.2,(hist,path),1,(arrivalInputs m).ticks (hist.getLastD .p0w0)
        ((arrivalInputs m).base.base.policy (hist.getLastD .p0w0))⟩ := by
  obtain ⟨id,hi,he⟩ := List.mem_flatMap.mp he
  unfold phase2Entries at he
  split at he
  · rename_i hc
    cases ht : routeTuple (arrivalInputs m).base id with
    | none => simp [ht] at he
    | some residue =>
      simp only [ht] at he
      obtain ⟨raw,hr,heq⟩ := List.mem_map.mp he
      exact ⟨id,hi,residue.1,residue.2,raw,hc,ht,hr,heq.symm⟩
  · simp at he

theorem entry_facts (m : RawLaneModel) (h : Protocol m) (e : WithdrawalEntry)
    (he : e ∈ entries m) :
    e.numerator > 0 ∧ e.register.1.isEmpty = false ∧ e.register.2.isEmpty = false ∧
    writer (inputs m) e.register = true ∧ (arrivalInputs m).base.receiver.funded = true := by
  obtain ⟨id,_,hist,path,raw,hc,ht,hr,rfl⟩ := entry_execution m e he
  have hf : active7 (arrivalInputs m).base = true ∧
      path6 (arrivalInputs m) id = true ∧
      (((arrivalInputs m).base.base.rows (hist.getLastD .p0w0)
        ((arrivalInputs m).base.base.policy (hist.getLastD .p0w0))).all
        (fun e => decide (e.2 > 0 ∧ e.1 ∈ ambientStates))) = true := by
    unfold phase2Check at hc
    split at hc
    · simp at hc
    · simp only [ht] at hc
      split at hc <;> try contradiction
      split at hc <;> try contradiction
      all_goals simp only [Bool.and_eq_true] at hc
      all_goals first
        | exact False.elim (Bool.noConfusion hc.2)
        | exact ⟨hc.1.1.1,hc.1.1.2,hc.2.2⟩
  have hp := List.all_eq_true.mp hf.2.2 raw hr
  have hn := hf.2.1
  simp only [path6,ht,Bool.and_eq_true] at hn
  exact ⟨(of_decide_eq_true hp).1,by simpa using hn.1.1.1.1,
    by simpa using hn.1.1.2,protocol_writer m h id (hist,path) (by rw [acquisition_tuple]; exact ht),
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf.1).1).2⟩

/-- Legacy advancement is precisely this small operational expression. Its
unused full-C6 decoder fields cannot affect the gate on partial assignments. -/
theorem advancement_operational_eq (m : RawLaneModel) :
    advancementCheck m =
      (available8 (inputs m).viability .target && decide (Ledger8 (inputs m).viability) &&
        (kernel.all fun s => actions.all fun a =>
          ((inputs m).viability.rows s a).isEmpty || decide ((inputs m).ticks s a = 1)) &&
        (!routeIds.isEmpty && routeIds.all ((inputs m).writers .target)) &&
        !(inputs m).routes.isEmpty) := by
  simp only [advancementCheck,ticks6,writers6,viability_eq,
    (operational_projections m).1,(operational_projections m).2.2.1,(operational_projections m).2.2.2]
  rfl

/-- Completeness and the actual run resource law bind every response row to
assigned C6's ACTUAL support, even with unused predictive cells missing. -/
theorem rows_actual_of_resource (m : RawLaneModel) (hp : Protocol m) (r : Run)
    (hr : ResourceClosed m r) (d : Disturbance) (a : Action) :
    rows m r d a = actualRows6 (runInputs6 (withdrawnAssignment m) .target) r a := by
  have hl := hr.2.1
  have hr' : (runInputs6 (withdrawnAssignment m) .target).resource.rechargeAvailable = true := hl.1
  have hc : (runInputs6 (withdrawnAssignment m) .target).ledger.initialBudget = 1 := hl.2.1
  have hcost : (runInputs6 (withdrawnAssignment m) .target).ledger.actionCost = 1 := hl.2.2.1
  have he : enabled6 (runInputs6 (withdrawnAssignment m) .target) r = true := by
    simp only [enabled6,budget6,hr.2.2.1,hr',hc,hcost]
    rfl
  simp only [rows,if_pos (protocol_complete m hp),actualRows6,he,if_true]
  congr 1
  cases r.factor <;> rfl

theorem record_actual_observer (m : RawLaneModel) (r : Run) :
    record m r = (observation6 (runInputs6 (withdrawnAssignment m) .target) .target r).endogenousRecordCount := by
  simp only [record,observation6,writer_eq]

end CSTTT.TargetTheory.GenericHandoff.POS04OperationalGame
