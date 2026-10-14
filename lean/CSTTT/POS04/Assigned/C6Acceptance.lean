import CSTTT.POS04.Assigned.C6Sufficiency

/-! G2b-3b. Assignment-indexed C6 surrogate; M3_model_spec.md:22,30–33.
Every object is decoded/defined. The finite row/delta check entails bisimulation
on ALL runs, not only audit roots. Budget conservation is mandatory for the
constant-budget lift. No source-presence requirement is added to package C6. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit CSTTT.TransportTheory

/-- Lookups fail closed; a missing reference cannot use `eventOf`'s default. -/
def event6 (d : RunInputs6) (id : EventId) := d.base.events.find? (fun e => decide (e.id = id))
def strictEvent6 (d : RunInputs6) (e : Event) : Bool :=
  e.atomic && e.strictStep && decide (e.fromStage ∈ d.base.realized) &&
  decide (e.toStage ∈ d.base.realized) &&
  decide (stages.idxOf e.toStage = stages.idxOf e.fromStage + 1)
def path6 (d : RunInputs6) (id : RouteId) : Bool :=
  match routeTuple d.base id with
  | none => false
  | some (hist,path) =>
    !hist.isEmpty && pathSupported d.base hist && !path.isEmpty &&
    path.all (fun id => (event6 d id).any (strictEvent6 d)) &&
    (path.zip (path.drop 1)).all (fun pair =>
      match event6 d pair.1,event6 d pair.2 with
      | some e,some f => decide (e.toStage = f.fromStage)
      | _,_ => false)
def paths6 (d : RunInputs6) : Bool :=
  decide (d.base.realized = stages) && !routeIds.isEmpty &&
  routeIds.all (path6 d) &&
  eventIds.all (fun id => d.base.routes.any (fun route => decide (id ∈ route.eventPath))) &&
  eventIds.all (fun id => (event6 d id).any (strictEvent6 d))
def ticks6 (d : RunInputs6) := kernel.all fun s => actions.all fun a =>
  (d.base.base.rows s a).isEmpty || decide (d.ticks s a = 1)
def writers6 (d : RunInputs6) (tag : Tag) :=
  !routeIds.isEmpty && routeIds.all (d.base.writers tag)
def Trace6 (d : RunInputs6) (tag : Tag) : Prop :=
  d.base.receiver.funded = true ∧ d.resource.rechargeAvailable = true ∧
  d.ledger.initialBudget ≥ d.ledger.actionCost ∧
  ticks6 d = true ∧ writers6 d tag = true ∧ paths6 d = true ∧ d.resource.owner = tag
/-- References and imported tables are comparisons; the quotient and future
weights are still computed from the assignment's action rows and hazards. -/
def Reference6 (d : RunInputs6) : Prop :=
  MLinked d.base.base ∧
  ∀ s t : KState, rowWeight (d.base.base.rows s (d.base.base.policy s)) t =
    d.base.base.publishedP (index s) (index t)
def Coarser6 (a : Assignment) (tag : Tag) : Prop :=
  (future6 a tag).code (initial6 a tag .p0w0 .a) =
    (future6 a tag).code (initial6 a tag .p0w1 .a) ∧
  initial6 a tag .p0w0 .a ≠ initial6 a tag .p0w1 .a

/-- M3_model_spec.md:32: one indivisible price token, one returned token,
one initial token. Conservation alone does not imply positive maintenance. -/
def UnitFunding6 (d : RunInputs6) : Prop :=
  d.ledger.initialBudget = 1 ∧ d.ledger.actionCost = 1 ∧
  d.ledger.rechargePerAction = 1 ∧ budget6 d > 0 ∧ budgetAfter6 d > 0

def C6Gate (a : Assignment) (tag : Tag) : Prop :=
  Ready a tag .c6 ∧ Reference6 (runInputs6 a tag) ∧
  Trace6 (runInputs6 a tag) tag ∧ LedgerConservation6 a tag ∧
  (runInputs6 a tag).interface = futureInterface ∧ UnitFunding6 (runInputs6 a tag)
/-- Acceptance checks the finite bisimulation equations, not a supplied
future-sufficiency proposition. Readout/update laws are definition theorems. -/
def C6Accept (a : Assignment) (tag : Tag) : Prop :=
  C6Gate a tag ∧ FiniteBisim6 (runInputs6 a tag) ∧ Coarser6 a tag

theorem c6_accept_sufficient {a : Assignment} {tag : Tag} (h : C6Accept a tag) :
    FullFutureSufficient (future6 a tag) := assigned6_all_words a tag h.2.1

theorem c6_accept_closure_laws {a : Assignment} {tag : Tag} (_h : C6Accept a tag) :
    ClosureReadoutLaws6 a tag := closure_readout_laws6 a tag

/-- All registered raw residues have available writers, even if two route
references resolve to the same tuple (the priority lookup remains honest). -/
theorem accepted_writer6 {a : Assignment} {tag : Tag} (h : C6Accept a tag)
    (r : RouteId) (residue : List KState × List EventId)
    (hr : routeTuple (runInputs6 a tag).base r = some residue) :
    writer6 (runInputs6 a tag) tag residue = true := by
  have hw := h.1.2.2.1.2.2.2.2.1
  simp only [writers6,Bool.and_eq_true] at hw
  have ha : (runInputs6 a tag).base.writers tag .a = true :=
    List.all_eq_true.mp hw.2 .a (by decide)
  have hb : (runInputs6 a tag).base.writers tag .b = true :=
    List.all_eq_true.mp hw.2 .b (by decide)
  cases r <;> simp [writer6,hr,ha,hb]

/-- Positivity and available writers persist on the entire computed closure.
The root and step facts are derived, not supplied maintenance evidence. -/
theorem c6_accept_funded_writer {a : Assignment} {tag : Tag} (h : C6Accept a tag)
    (x : Run6) (hx : Closure6 a tag x) :
    x.funded = true ∧ writer6 (runInputs6 a tag) tag x.residue = true := by
  have hpos := h.1.2.2.2.2.2.2.2.2.2
  induction hx with
  | root x hm =>
    change x ∈ routeIds.flatMap (fun r => match routeTuple (runInputs6 a tag).base r with
      | none => []
      | some residue => kernel.map (fun s =>
        (⟨.inK s,0,0,residue,(runInputs6 a tag).base.receiver.funded⟩ : Run6))) at hm
    obtain ⟨r,_,hr⟩ := List.mem_flatMap.mp hm
    cases he : routeTuple (runInputs6 a tag).base r with
    | none => simp [he] at hr
    | some residue =>
      simp only [he] at hr
      obtain ⟨s,_,hs⟩ := List.mem_map.mp hr
      subst x
      exact ⟨h.1.2.2.1.1,accepted_writer6 h r residue he⟩
  | step hx act o ho ih =>
    change (update6 (runInputs6 a tag) _ act o).funded = true ∧ _
    refine ⟨?_,ih.2⟩
    simp only [update6,ih.1,decide_eq_true hpos,Bool.true_and]

/-- Every update on the audited execution closure retains strictly positive
conserved funding and increments the endogenous record. This is stronger
than its restriction to nonzero-probability supported steps. -/
theorem c6_accept_record_advancement {a : Assignment} {tag : Tag} (h : C6Accept a tag)
    (x : Run6) (hx : Closure6 a tag x) (act : Action) (o : PredictiveNow) :
    budgetAfter6 (runInputs6 a tag) = budget6 (runInputs6 a tag) ∧
    budgetAfter6 (runInputs6 a tag) > 0 ∧
    (update6 (runInputs6 a tag) x act o).funded = true ∧
    (observation6 (runInputs6 a tag) tag (update6 (runInputs6 a tag) x act o)).endogenousRecordCount =
      (observation6 (runInputs6 a tag) tag x).endogenousRecordCount + 1 := by
  have hf := c6_accept_funded_writer h x hx
  have hp := h.1.2.2.2.2.2.2.2.2.2
  refine ⟨h.1.2.2.2.1,hp,?_,?_⟩
  · simp only [update6,hf.1,decide_eq_true hp,Bool.true_and]
  · simp only [observation6,update6,hf.1,hf.2,decide_eq_true hp,Bool.true_and,if_true]


theorem c6_gate_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c6) a b) : C6Gate a tag ↔ C6Gate b tag := by
  unfold C6Gate LedgerConservation6
  rw [ready_locality h,run_inputs6_locality h]
theorem c6_accept_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c6) a b) : C6Accept a tag ↔ C6Accept b tag := by
  unfold C6Accept Coarser6 initial6
  rw [c6_gate_locality h,run_inputs6_locality h,future6_locality h]

theorem canonical_trace6 (tag : Tag) : Trace6 (runInputs6 canonical tag) tag := by
  cases tag <;> unfold Trace6 <;> decide

theorem canonical_reference6 (tag : Tag) : Reference6 (runInputs6 canonical tag) := by
  constructor
  · rw [canonical_run_inputs6]
    cases tag <;> exact legacy_M_link .positive .positive .position _
  · intro s t
    cases tag <;> cases s <;> cases t <;> decide

theorem canonical_gate6 (tag : Tag) : C6Gate canonical tag := by
  exact ⟨canonical_ready tag .c6,canonical_reference6 tag,canonical_trace6 tag,
    canonical_ledger_conservation6 tag,(by cases tag <;> rfl),
    (by cases tag <;> unfold UnitFunding6 <;> decide)⟩

theorem canonical_accept6 (tag : Tag) : C6Accept canonical tag :=
  ⟨canonical_gate6 tag,canonical_finite_bisim6 tag,
    (canonical_merged_roots6 tag).2.2.1,(canonical_merged_roots6 tag).2.2.2⟩

/-- Canonical truth equivalence, backed by the exact all-state/word-law links
in C6Sufficiency, not a closure-only replacement for the legacy quantifier. -/
theorem canonical_c6_equivalence (tag : Tag) : C6Accept canonical tag ↔ C6Pass .positive tag := by
  constructor
  · intro _; exact c6_each_tag tag
  · intro _; exact canonical_accept6 tag

end CSTTT.POS04.Assigned
