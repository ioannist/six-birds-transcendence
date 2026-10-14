import CSTTT.Targets.ComputedFIACH.Models

/-! G6_lane_spec.md:213–285; G6b CR1 phase-2 execution. Arrival activation
and realization are checked BEFORE withdrawing recharge. Every positive support
entry is retained, including exits (which fail endpoint-inside); no lucky branch
or reset to the receiver factor is allowed. Counter one is the declared one-step
probe-local counter, as in G6b's `routes`, not the corridor event ordinal. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

structure WithdrawalEntry where
  factor : Ambient
  numerator : Nat
  register : List KState × List EventId
  counter : Nat
  ticks : Nat
  deriving DecidableEq, Repr

def arrivalInputs (m : RawLaneModel) := runInputs6 (image m.assignment) .target

/-- Exact execution dependencies in the staged namespace. Source rows
validate acquisition histories; target rows govern the funded response. -/
def phase2Dependencies : List Cell :=
  [.rows .source,.rows .target,.policy,.ticks .target,.resources .target,
   .maintenance,.histories,.eventTable,.realized,.receiverInput,.routeTable,.writers]

def phase2Complete (m : RawLaneModel) : Bool :=
  decide (Complete phase2Dependencies (image m.assignment))

def phase2Check (m : RawLaneModel) (r : RouteId) : Bool :=
  if !phase2Complete m then false else
  let d := arrivalInputs m
  match routeTuple d.base r with
  | none => false
  | some (hist,path) =>
    let factor := hist.getLastD .p0w0
    let row := d.base.base.rows factor (d.base.base.policy factor)
    active7 d.base && path6 d r &&
      pathSupported (clauseExtra (image m.assignment) .source .c6) hist &&
      match path.head?,path.getLast? with
      | some first,some last =>
        match event6 d first,event6 d last with
        | some start,some finish =>
          decide (start.fromStage = .sourceLive ∧ finish.toStage = .targetExit) &&
          finish.targetSupport && !finish.sourceSupport &&
          available8 (clause8 (image m.assignment) .target) .target &&
          d.base.writers .target r && !row.isEmpty &&
          decide ((row.map Prod.snd).sum = 4) &&
          row.all (fun e => decide (e.2 > 0 ∧ e.1 ∈ ambientStates))
        | _,_ => false
      | _,_ => false

def phase2Entries (m : RawLaneModel) (r : RouteId) : List WithdrawalEntry :=
  let d := arrivalInputs m
  if phase2Check m r then
    match routeTuple d.base r with
    | none => []
    | some residue =>
      let factor := residue.1.getLastD .p0w0
      let action := d.base.base.policy factor
      (d.base.base.rows factor action).map fun e =>
        ⟨e.1,e.2,residue,1,d.ticks factor action⟩
  else []
def entries (m : RawLaneModel) := routeIds.flatMap (phase2Entries m)
def entryInside (S : List KState) (e : WithdrawalEntry) : Bool :=
  !e.register.1.isEmpty && !e.register.2.isEmpty && e.numerator > 0 &&
  match e.factor with | .inK s => decide (s ∈ S) | _ => false

def autonomyInputs : List Cell :=
  clauseScope .target .c8 ++ [.ticks .target,.writers,.histories,.routeTable,
    .receiverInput,.eventTable,.realized]

def sharedAutonomyCheck (m : RawLaneModel) (S : List KState) : Bool :=
  decide (Complete autonomyInputs (image m.assignment)) && withdrawalCheck m &&
  advancementCheck m && decide (PUnchanged8 (withdrawnInputs m)) &&
  !S.isEmpty && routeIds.all (phase2Check m) && !(entries m).isEmpty &&
  (entries m).all (entryInside S) &&
  S.all (fun s => actions.any (responseCheck m S s .nominal))

def fullAutonomyCheck (m : RawLaneModel) : Bool :=
  sharedAutonomyCheck m (greatestF m) &&
    (greatestF m).all (packageAtCheck m)
def operationalAutonomyCheck (m : RawLaneModel) : Bool :=
  sharedAutonomyCheck m (greatestO m)
def AF (m : RawLaneModel) : Prop := fullAutonomyCheck m = true
def AO (m : RawLaneModel) : Prop := operationalAutonomyCheck m = true

/-- Generic dependence, with computed nonempty invariant. The full package
Inside readout does NOT supply the separate P proof in certificate assembly. -/
theorem fullAutonomy_implies_package (m : RawLaneModel) (h : AF m) : PackageLane m.assignment := by
  simp only [AF,fullAutonomyCheck,Bool.and_eq_true] at h
  have hshared := h.1
  simp only [sharedAutonomyCheck,Bool.and_eq_true] at hshared
  have hn : greatestF m ≠ [] := by
    intro he
    rw [he] at hshared
    simp at hshared
  exact full_invariant_implies_package m hn

theorem phase2_unavailable_no_entries (m : RawLaneModel)
    (h : ∀ r ∈ routeIds, phase2Check m r = false) : entries m = [] := by
  unfold entries
  apply List.flatMap_eq_nil_iff.mpr
  intro r hr
  simp [phase2Entries,h r hr]

theorem empty_entries_reject_F (m : RawLaneModel) (h : entries m = []) : ¬ AF m := by
  simp [AF,fullAutonomyCheck,sharedAutonomyCheck,h]
theorem empty_entries_reject_O (m : RawLaneModel) (h : entries m = []) : ¬ AO m := by
  simp [AO,operationalAutonomyCheck,sharedAutonomyCheck,h]
theorem no_source_rejects_phase2 (m : RawLaneModel)
    (h : (arrivalInputs m).base.receiver.sourcePresent = false) (r : RouteId) :
    phase2Check m r = false := by
  unfold phase2Check
  split
  · rfl
  · dsimp only
    split
    · rfl
    · simp [active7,h]

/-- One guard covers every consumed primitive, before decoder defaults. -/
theorem phase2_missing_staged_cell (m : RawLaneModel) (k : Cell)
    (hk : k ∈ phase2Dependencies) (hmissing : image m.assignment k = none)
    (r : RouteId) : phase2Check m r = false := by
  have hc : phase2Complete m = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    have hh : Complete phase2Dependencies (image m.assignment) := of_decide_eq_true h
    have hs := hh k hk
    rw [hmissing] at hs
    contradiction
  simp [phase2Check,hc]

theorem image_delete_cell (a : Assignment) (k : Cell) :
    image (put a (swapCell k) none) k = none := by
  simp [image,exchangeAssignment]

theorem phase2_missing_dependency (m : RawLaneModel) (k : Cell)
    (hk : k ∈ phase2Dependencies) (r : RouteId) :
    phase2Check {m with assignment := put m.assignment (swapCell k) none} r = false :=
  phase2_missing_staged_cell _ k hk (image_delete_cell _ _) r

theorem phase2_missing_dependency_no_entries (m : RawLaneModel) (k : Cell)
    (hk : k ∈ phase2Dependencies) :
    entries {m with assignment := put m.assignment (swapCell k) none} = [] := by
  apply phase2_unavailable_no_entries
  intro r _
  exact phase2_missing_dependency m k hk r

theorem phase2_missing_dependency_reject_F (m : RawLaneModel) (k : Cell)
    (hk : k ∈ phase2Dependencies) :
    ¬ AF {m with assignment := put m.assignment (swapCell k) none} :=
  empty_entries_reject_F _ (phase2_missing_dependency_no_entries m k hk)
theorem phase2_missing_dependency_reject_O (m : RawLaneModel) (k : Cell)
    (hk : k ∈ phase2Dependencies) :
    ¬ AO {m with assignment := put m.assignment (swapCell k) none} :=
  empty_entries_reject_O _ (phase2_missing_dependency_no_entries m k hk)

/-- The original target-row deletion removes staged SOURCE rows. -/
theorem missing_target_rows_reject_O :
    ¬ AO {baseline with assignment := put canonical (.rows .target) none} :=
  phase2_missing_dependency_reject_O baseline (.rows .source) (by decide)
theorem missing_receiver_reject_phase2 (r : RouteId) :
    phase2Check {baseline with assignment := put canonical .receiverInput none} r = false :=
  phase2_missing_dependency baseline .receiverInput (by decide) r
end CSTTT.TargetTheory.ComputedFIACH
