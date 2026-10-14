import CSTTT.Targets.GenericHandoff.FactorTransport
import CSTTT.Targets.GenericHandoff.POS04TemporalEquivalence
import CSTTT.Targets.ComputedFIACH.AssignmentBridge

/-! Exact factor extraction from arbitrary partial POS-04 assignments. The
Option decoder rejects absence before the old helper defaults are accessible.
At a complete assignment all extracted rows/classes/coordinates/clock/resource
values equal the existing assignment-owned bridge, not just its baseline. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04FactorTransport
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH CSTTT.TransportTheory

abbrev Data := FactorTransport.Data KState Action Ambient Tag

def data (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) : Data :=
  let d := runInputs6 a t
  ⟨d.base.base.rows,d.base.base.positions,d.base.base.hazards,d.base.base.policy,d.ticks,
    ⟨d.resource.owner,d.resource.rechargeAvailable⟩,
    ⟨d.ledger.initialBudget,d.ledger.actionCost,d.ledger.rechargePerAction⟩⟩

def view (t : Tag) : StaticView Cell Value Data :=
  ⟨.map (fun p : ((KState → Action → List (Ambient × Nat)) × (KState → Nat)) ×
      (((Ambient → Bool) × (KState → Action)) × ((KState → Action → Nat) × (ResourceData × CSTTT.POS04.Ledger))) =>
    ⟨p.1.1,p.1.2,p.2.1.1,p.2.1.2,p.2.2.1,
      ⟨p.2.2.2.1.owner,p.2.2.2.1.rechargeAvailable⟩,
      ⟨p.2.2.2.2.initialBudget,p.2.2.2.2.actionCost,p.2.2.2.2.rechargePerAction⟩⟩)
    (.pair (.pair (.cell (Cell.rows t)) (.cell Cell.positions))
      (.pair (.pair (.cell Cell.hazards) (.cell Cell.policy))
        (.pair (.cell (Cell.ticks t)) (.pair (.cell (Cell.resources t)) (.cell Cell.maintenance)))))⟩

def decoded (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) : Option Data := (view t).read a

theorem dependencies (t : Tag) : (view t).dependencies =
    [.rows t,.positions,.hazards,.policy,.ticks t,.resources t,.maintenance] := rfl

theorem decoded_equation (a : CSTTT.POS04.Assigned.Assignment) (t : Tag)
    (h : Complete (view t).dependencies a) : decoded a t = some (data a t) := by
  have h1 := POS04RegisterDynamics.cell_value (h (.rows t) (by simp [dependencies]))
  have h2 := POS04RegisterDynamics.cell_value (h .positions (by simp [dependencies]))
  have h3 := POS04RegisterDynamics.cell_value (h .hazards (by simp [dependencies]))
  have h4 := POS04RegisterDynamics.cell_value (h .policy (by simp [dependencies]))
  have h5 := POS04RegisterDynamics.cell_value (h (.ticks t) (by simp [dependencies]))
  have h6 := POS04RegisterDynamics.cell_value (h (.resources t) (by simp [dependencies]))
  have h7 := POS04RegisterDynamics.cell_value (h .maintenance (by simp [dependencies]))
  simp only [decoded,StaticView.read,view,RegisterInterpreter.Expr.eval]
  rw [h1,h2,h3,h4,h5,h6,h7]
  cases t <;> rfl

theorem decoded_iff (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) :
    (∃ d, decoded a t = some d) ↔ Complete (view t).dependencies a := by
  constructor
  · rintro ⟨d,hd⟩ k hk
    cases hm : a k with
    | some v => rfl
    | none =>
      have hn := (view t).missing a k hk hm
      change decoded a t = none at hn
      rw [hn] at hd
      contradiction
  · intro h; exact ⟨_,decoded_equation a t h⟩

theorem missing_rejected (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (k : Cell)
    (hk : k ∈ (view t).dependencies) (hm : a k = none) : decoded a t = none :=
  (view t).missing a k hk hm

private theorem row_sum (xs : List (Ambient × Nat)) (u : KState) (n : Nat) :
    (xs.filter fun e => e.1 == Ambient.inK u).foldl (fun n e => n+e.2) n =
      n + (xs.map fun e => if e.1 = Ambient.inK u then e.2 else 0).sum := by
  induction xs generalizing n with
  | nil => simp
  | cons e es ih =>
    by_cases he : e.1 = .inK u
    · simp [he,ih,Nat.add_assoc]
    · simp [he,ih]

theorem weight_equation (a : CSTTT.POS04.Assigned.Assignment) (t : Tag)
    (s u : KState) (act : Action) :
    FactorTransport.actionWeight (POS04TemporalFactor.schema t)
      (data a t) s act u =
        rowWeight ((runInputs6 a t).base.base.rows s act) u := by
  rw [rowWeight,row_sum]
  simp only [Nat.zero_add,FactorTransport.actionWeight,data]
  congr 1
  apply List.map_congr_left
  intro e _
  have he : POS04ProfileRules.schema.destination e.1 = some u ↔ e.1 = .inK u := by
    cases e.1 <;> simp [POS04ProfileRules.schema]
  simp only [POS04TemporalFactor.schema,POS04ProfileRules.clauseSchema,he]

theorem class_equation (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (s : KState) :
    FactorTransport.classOf (POS04TemporalFactor.schema t)
      (data a t) s =
        predictive (runInputs6 a t).base.base s := rfl

theorem policy_equation (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (s u : KState) :
    FactorTransport.canonicalWeight (POS04TemporalFactor.schema t)
      (data a t) s u = assignedFactorStep a t s u := by
  exact weight_equation a t s u ((runInputs6 a t).base.base.policy s)

theorem raw_action_equation (m : RawLaneModel) (t : Tag) (s u : KState) (i : Nat) :
    (match actions[i]? with
    | none => 0
    | some act => FactorTransport.actionWeight (POS04TemporalFactor.schema t)
      (data (image m.assignment) t) s act u) =
      assignedActionStep (image m.assignment) t s i u := by
  unfold assignedActionStep
  cases hi : actions[i]? with
  | none => rfl
  | some act => exact weight_equation _ _ _ _ _

/-- Six readout projections share the same decoded primitives. No free
coordinate/class/tick/maintenance/owner candidates are accepted. -/
theorem bridge_readout_equations (m : RawLaneModel) (t : Tag) (s : KState) :
    let d := data (image m.assignment) t
    FactorTransport.classOf (POS04TemporalFactor.schema t) d s =
      (if t = .source then (assignmentRawBridge m).sourceClass s else (assignmentRawBridge m).targetClass s) ∧
    d.positions s = (if t = .source then (assignmentRawBridge m).sourceCoord s else (assignmentRawBridge m).targetCoord s) ∧
    d.ticks s (d.policy s) = (if t = .source then (assignmentRawBridge m).sourceTick s else (assignmentRawBridge m).targetTick s) ∧
    FactorTransport.maintained (POS04TemporalFactor.schema t) d = (if t = .source then (assignmentRawBridge m).sourceMaintenance s else (assignmentRawBridge m).targetMaintenance s) ∧
    tagCarrierId d.resource.owner = (if t = .source then (assignmentRawBridge m).sourceOwner s else (assignmentRawBridge m).targetOwner s) := by
  cases t
  all_goals refine ⟨rfl,rfl,rfl,?_,rfl⟩
  all_goals rfl

/-- The declared typed tag bijection copies factor coordinates, while resource
ownership is translated to the target carrier. These are raw map instructions,
not candidates for any derived predictive or future value. -/
def maps : FactorTransport.Maps KState KState Action Action Tag :=
  ⟨id,id,id,id,id,fun _ => .target⟩

theorem canonical_equations : FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source)
    (data canonical .target) maps := by
  constructor
  · rfl
  · intro s; rfl
  · intro s; rfl
  · intro s; rfl
  · intro s act u
    rw [weight_equation,weight_equation]
    rfl
  · intro s; rfl
  · rfl
  · rfl
  · intro s u he; exact he
  · rfl

theorem erased_target_rows_rejected : ¬ FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source)
    {(data canonical .target) with rows := fun _ _ => []} maps := by
  apply FactorTransport.action_mismatch_rejected _ _ _ _ _ .p1w0 .p2w1 (canonicalAction .p1w0)
  decide +kernel

theorem collapsed_predictive_map_rejected : ¬ FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source)
    (data canonical .target)
    {maps with predictive := fun _ => (0,[])} := by
  apply FactorTransport.class_collapse_rejected _ _ _ _ _ .p1w0 .p1w1 rfl
  decide +kernel

/-- Exact equations for the bridge's finite factor projection, separate from
its event/history/run laws. Both directions quantify over arbitrary partial
assignments; the acceptance decoder separately requires completeness. -/
def FactorFields (m : RawLaneModel) : Prop :=
  let b := assignmentRawBridge m
  (∀ s, b.targetCoord s = b.sourceCoord s ∧ b.targetClass s = b.sourceClass s ∧
    b.targetTick s = b.sourceTick s ∧ b.targetMaintenance s = b.sourceMaintenance s ∧
    b.targetOwner s = b.targetId) ∧ FiniteActionMap m

def FactorEquations (m : RawLaneModel) : Prop := FactorTransport.Equations
  (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
  (data (image m.assignment) .source)
  (data (image m.assignment) .target) maps

theorem factor_equations_iff (m : RawLaneModel) : FactorEquations m ↔ FactorFields m := by
  constructor
  · intro h
    constructor
    · intro s
      refine ⟨h.coordinate s,h.predictive s,h.tick s,h.maintenance,?_⟩
      exact congrArg tagCarrierId h.owner
    · intro s u act
      have he := h.action s act u
      simpa only [maps,weight_equation,id_eq] using he
  · rintro ⟨h,ha⟩
    constructor
    · rfl
    · intro s; exact (h s).1
    · intro s; exact (h s).2.1
    · intro s; rfl
    · intro s act u
      simpa only [maps,weight_equation,id_eq] using ha s u act
    · intro s; exact (h s).2.2.1
    · exact (h .p0w0).2.2.2.1
    · have he := (h .p0w0).2.2.2.2
      change tagCarrierId (runInputs6 (image m.assignment) .target).resource.owner = tagCarrierId .target at he
      change (runInputs6 (image m.assignment) .target).resource.owner = .target
      cases ho : (runInputs6 (image m.assignment) .target).resource.owner
      · rw [ho] at he
        exact False.elim ((by decide : tagCarrierId .source ≠ tagCarrierId .target) he)
      · rfl
    · intro s u he; exact he
    · rfl

def binding : FactorTransport.Binding Cell Value KState KState Action Action Ambient Ambient
    HistoryId RouteId CSTTT.POS04.Stage EventId Tag :=
  ⟨view .source,view .target,⟨.literal maps⟩⟩

theorem pass_iff (m : RawLaneModel) :
    FactorTransport.Pass (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
      binding (image m.assignment) ↔
    Complete (view .source).dependencies (image m.assignment) ∧
      Complete (view .target).dependencies (image m.assignment) ∧ FactorFields m := by
  constructor
  · rintro ⟨ds,dt,mp,hs,ht,hm,hp⟩
    have hcs := (decoded_iff _ .source).mp ⟨ds,hs⟩
    have hct := (decoded_iff _ .target).mp ⟨dt,ht⟩
    have es := Option.some.inj ((decoded_equation _ .source hcs).symm.trans hs)
    have et := Option.some.inj ((decoded_equation _ .target hct).symm.trans ht)
    have em : maps = mp := Option.some.inj hm
    cases es
    cases et
    cases em
    exact ⟨hcs,hct,(factor_equations_iff m).mp hp⟩
  · rintro ⟨hcs,hct,hp⟩
    exact ⟨_,_,maps,decoded_equation _ .source hcs,decoded_equation _ .target hct,rfl,
      (factor_equations_iff m).mpr hp⟩

theorem positive : FactorTransport.Pass (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    binding canonical :=
  ⟨_,_,maps,decoded_equation _ .source (canonical_complete _),
    decoded_equation _ .target (canonical_complete _),rfl,canonical_equations⟩

/-- The finite-factor view does not accidentally depend on the unused
interface declaration. Its contents are neither a probability nor a readout. -/
theorem interface_not_consumed (t : Tag) : Cell.interface ∉ (view t).dependencies := by
  cases t <;> decide

theorem linked_M (a : CSTTT.POS04.Assigned.Assignment) (t : Tag) (h : C2Gate a t) (s u : KState) :
    FactorTransport.classOf (POS04TemporalFactor.schema t) (data a t) s =
      FactorTransport.classOf (POS04TemporalFactor.schema t) (data a t) u ↔
    mClass (index s) = mClass (index u) := by
  have hp : FactorTransport.classOf (POS04TemporalFactor.schema t) (data a t) =
      predictive (clauseInputs a t .c2) := by cases t <;> rfl
  rw [hp]
  have he := h.2.2 s u
  rw [h.2.1] at he
  exact he

theorem canonical_M_link (t : Tag) (s u : KState) :
    FactorTransport.classOf (POS04TemporalFactor.schema t) (data canonical t) s =
      FactorTransport.classOf (POS04TemporalFactor.schema t) (data canonical t) u ↔
    mClass (index s) = mClass (index u) := linked_M _ t (canonical_c123 t).2.1.1 s u

/-- Each guard changes just the named raw field or typed map. Zero means
field erasure; it is not a fitted model parameter. -/
theorem coordinate_erasure_guard : ¬ FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source) {(data canonical .target) with positions := fun _ => 0} maps := by
  apply FactorTransport.coordinate_mismatch_rejected _ _ _ _ _ .p1w0
  decide +kernel

theorem tick_erasure_guard : ¬ FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source) {(data canonical .target) with ticks := fun _ _ => 0} maps := by
  apply FactorTransport.tick_mismatch_rejected _ _ _ _ _ .p1w0
  decide +kernel

theorem policy_erasure_guard : ¬ FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source) {(data canonical .target) with policy := fun _ => .stay} maps := by
  apply FactorTransport.policy_mismatch_rejected _ _ _ _ _ .p1w0
  decide +kernel

theorem resource_erasure_guard : ¬ FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source) {(data canonical .target) with resource := ⟨.target,false⟩} maps := by
  apply FactorTransport.maintenance_mismatch_rejected _ _ _ _ _
  decide +kernel

theorem ledger_erasure_guard : ¬ FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source) {(data canonical .target) with ledger := ⟨0,0,0⟩} maps := by
  apply FactorTransport.maintenance_mismatch_rejected _ _ _ _ _
  decide +kernel

theorem owner_relabel_guard : ¬ FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source) {(data canonical .target) with resource := ⟨.source,true⟩} maps := by
  apply FactorTransport.owner_mismatch_rejected _ _ _ _ _
  decide +kernel

theorem collapsed_state_map_guard : ¬ FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source) (data canonical .target) {maps with state := fun _ => .p0w0} := by
  apply FactorTransport.states_mismatch_rejected _ _ _ _ _
  decide +kernel

theorem collapsed_action_map_guard : ¬ FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source) (data canonical .target) {maps with action := fun _ => .stay} := by
  apply FactorTransport.action_mismatch_rejected _ _ _ _ _ .p1w0 .p2w1 (canonicalAction .p1w0)
  decide +kernel

theorem hazard_erasure_guard : ¬ FactorTransport.Equations
    (POS04TemporalFactor.schema .source) (POS04TemporalFactor.schema .target)
    (data canonical .source) {(data canonical .target) with hazards := fun _ => false} maps := by
  apply FactorTransport.predictive_mismatch_rejected _ _ _ _ _ .p1w0
  decide +kernel

end CSTTT.TargetTheory.GenericHandoff.POS04FactorTransport
