import CSTTT.POS04.Assigned.C6Acceptance
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.TransportTheory

/-- Exact declared interventions; no code or projection rule is altered. -/
def futureBreak6 (a : Assignment) := mapCell a (.ticks .target) (fun ts s act =>
  if s = .p0w1 ∧ act = .stay then 2 else ts s act)
def recordBreak6 (a : Assignment) := mapCell a .writers (fun ws tag route =>
  if tag = .target ∧ route = .b then false else ws tag route)
def missingMix6 (a : Assignment) := mapCell a .realized (fun ss => ss.filter (· != .mix1))
def controls6 (v : C6Variant) : Assignment := match v with
  | .positive => canonical
  | .negFuture => futureBreak6 canonical
  | .negRecord => recordBreak6 canonical
  | .missingMix1 => missingMix6 canonical

/-- Exact adapter equations for the changed raw cells; untouched primitive
families retain canonical values. These are not stored predicate outcomes. -/
theorem controls6_ticks (v : C6Variant) (tag : Tag) (s : KState) (act : Action) :
    (runInputs6 (controls6 v) tag).ticks s act = c6Tick v tag s act := by
  cases v <;> cases tag <;> cases s <;> cases act <;> rfl
theorem controls6_writers (v : C6Variant) (tag : Tag) (route : RouteId) :
    (runInputs6 (controls6 v) tag).base.writers tag route = c6Writer v tag route := by
  cases v <;> cases tag <;> cases route <;> rfl
theorem controls6_realized (v : C6Variant) (tag : Tag) :
    (runInputs6 (controls6 v) tag).base.realized = c6Realized v := by
  cases v <;> cases tag <;> rfl

theorem controls6_rows (v : C6Variant) (tag : Tag) (s : KState) (act : Action) :
    (runInputs6 (controls6 v) tag).base.base.rows s act = actionRow tag s act := by
  cases v <;> cases tag <;> rfl
theorem controls6_predictive (v : C6Variant) (tag : Tag) (s : Ambient) :
    predictive6 (runInputs6 (controls6 v) tag) s = predictiveNow tag s := by
  cases v <;> cases tag <;> exact canonical_predictive6 _ _
theorem controls6_mass (v : C6Variant) (tag : Tag) (s : Ambient) (act : Action) (o : OutcomeClass) :
    mass6 (runInputs6 (controls6 v) tag) s act (legacyOutcome6 tag o) = classMass tag s act o := by
  cases v <;> cases tag <;> exact canonical_mass6 _ _ _ _

theorem controls6_ready (v : C6Variant) (tag : Tag) : Ready (controls6 v) tag .c6 := by
  constructor
  · cases v with
    | positive => exact canonical_complete _
    | negFuture => exact mapCell_complete _ _ (canonical_complete _)
    | negRecord => exact mapCell_complete _ _ (canonical_complete _)
    | missingMix1 => exact mapCell_complete _ _ (canonical_complete _)
  · cases v <;> cases tag <;> exact legacy_rows_valid .positive .positive .position .source

theorem controls6_reference (v : C6Variant) (tag : Tag) : Reference6 (runInputs6 (controls6 v) tag) := by
  cases v <;> cases tag <;> exact canonical_reference6 _

theorem controls6_conservation (v : C6Variant) (tag : Tag) : LedgerConservation6 (controls6 v) tag := by
  cases v <;> cases tag <;> rfl

theorem controls6_coarser (v : C6Variant) (tag : Tag) : Coarser6 (controls6 v) tag := by
  cases v <;> cases tag <;> unfold Coarser6 <;> decide

theorem controls6_trace_equivalence (v : C6Variant) (tag : Tag) :
    Trace6 (runInputs6 (controls6 v) tag) tag ↔ C6Trace v tag := by
  cases v <;> cases tag <;> unfold Trace6 C6Trace <;> decide

theorem controls6_finite_bisim (tag : Tag) :
    FiniteBisim6 (runInputs6 (recordBreak6 canonical) tag) := by
  cases tag <;> unfold FiniteBisim6 <;> decide

theorem controls6_source_pass (v : C6Variant) (h : v ≠ .missingMix1) : C6Accept (controls6 v) .source := by
  refine ⟨⟨controls6_ready _ _,controls6_reference _ _,?_,controls6_conservation _ _,?_,?_⟩,?_,controls6_coarser _ _⟩
  · cases v <;> unfold Trace6 <;> first | decide | contradiction
  · cases v <;> rfl
  · cases v <;> unfold UnitFunding6 <;> decide
  · cases v <;> unfold FiniteBisim6 <;> first | decide | contradiction

theorem neg_c6_future_assigned : ¬ C6Accept (futureBreak6 canonical) .target := by
  intro h
  have ht := h.1.2.2.1.2.2.2.1
  change ticks6 (runInputs6 (futureBreak6 canonical) .target) = true at ht
  have hf : ticks6 (runInputs6 (futureBreak6 canonical) .target) = false := by decide
  rw [hf] at ht
  contradiction

theorem neg_c6_record_assigned : ¬ C6Accept (recordBreak6 canonical) .target := by
  intro h
  have ht := h.1.2.2.1.2.2.2.2.1
  change writers6 (runInputs6 (recordBreak6 canonical) .target) .target = true at ht
  have hf : writers6 (runInputs6 (recordBreak6 canonical) .target) .target = false := by decide
  rw [hf] at ht
  contradiction

theorem missing_realized6_assigned (tag : Tag) : ¬ C6Accept (missingMix6 canonical) tag := by
  intro h
  have ht := h.1.2.2.1.2.2.2.2.2.1
  have hf : paths6 (runInputs6 (missingMix6 canonical) tag) = false := by cases tag <;> decide
  rw [hf] at ht
  contradiction

/-- Full future sufficiency still holds under record-writer removal; trace
acceptance fails honestly because the assigned target writer is unavailable. -/
theorem neg_record6_all_words (tag : Tag) : FullFutureSufficient (future6 (recordBreak6 canonical) tag) :=
  assigned6_all_words _ tag (controls6_finite_bisim tag)

/-- M3b package C6 is evaluated per tag. Legacy negative C6Pass quantifies
across BOTH tags: its source negFuture result differs for that reason. Only
canonical C6Pass equivalence is asserted; no negative quantifier is weakened. -/
theorem c6_m3b_per_tag_outcomes :
    (C6Accept canonical .source ∧ C6Accept canonical .target) ∧
    (C6Accept (futureBreak6 canonical) .source ∧ ¬ C6Accept (futureBreak6 canonical) .target) ∧
    (C6Accept (recordBreak6 canonical) .source ∧ ¬ C6Accept (recordBreak6 canonical) .target) ∧
    (¬ C6Accept (missingMix6 canonical) .source ∧ ¬ C6Accept (missingMix6 canonical) .target) :=
  ⟨⟨canonical_accept6 _,canonical_accept6 _⟩,
   ⟨controls6_source_pass .negFuture (by decide),neg_c6_future_assigned⟩,
   ⟨controls6_source_pass .negRecord (by decide),neg_c6_record_assigned⟩,
   ⟨missing_realized6_assigned _,missing_realized6_assigned _⟩⟩

end CSTTT.POS04.Assigned
