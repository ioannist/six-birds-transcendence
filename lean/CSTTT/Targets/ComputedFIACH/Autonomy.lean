import CSTTT.Targets.ComputedFIACH.PackageImage

/-! G6_lane_spec.md:147–300. A raw withdrawal rule over one immutable
assignment. The environment alphabet is nominal, NOT the action alphabet.
This module constructs the package-filtered greatest set for every assignment;
it does not yet constitute the full G6 certificate/lineage adapter. -/
namespace CSTTT.TargetTheory.ComputedFIACH
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

inductive LaneDisturbance where | nominal deriving DecidableEq, Repr
inductive RemovedRole where
  | source | migrationBridge | migrationController | externalDecoder
  | externalScheduler | undeclaredRepair
  deriving DecidableEq, Repr
inductive RetainedResource where | targetRecharge deriving DecidableEq, Repr

def removedRoles : List RemovedRole :=
  [.source,.migrationBridge,.migrationController,.externalDecoder,.externalScheduler,.undeclaredRepair]

/-- All fields are raw inputs. No safe set, entry, observation, code, or
acceptance verdict is supplied. The fixed G6 staging/cover is defined above. -/
structure RawLaneModel where
  assignment : Assignment
  retained : List RetainedResource
  removed : List RemovedRole
  sourcePresentAfterWithdrawal : Bool

def withdrawnAssignment (m : RawLaneModel) : Assignment :=
  mapCell (image m.assignment) (.resources .target) fun r =>
    {r with rechargeAvailable := r.rechargeAvailable && m.retained.contains .targetRecharge}
def withdrawnInputs (m : RawLaneModel) := clause8 (withdrawnAssignment m) .target

def withdrawalCheck (m : RawLaneModel) : Bool :=
  removedRoles.all m.removed.contains && m.removed.all removedRoles.contains &&
    !m.sourcePresentAfterWithdrawal

/-- Run recipes come from assigned C6. Every tick/writer is checked on its
actual raw route/action domain; no finite counter replaces the unbounded run. -/
def advancementCheck (m : RawLaneModel) : Bool :=
  let d := runInputs6 (withdrawnAssignment m) .target
  available8 (withdrawnInputs m) .target && decide (Ledger8 (withdrawnInputs m)) &&
    ticks6 d && writers6 d .target && !d.base.routes.isEmpty

/-- The original 160 logical coordinates are views, not new acceptance cells.
Their dependency completeness is checked through each actual clause scope. -/
def stateViewsCheck (a : Assignment) (_x : KState) : Bool :=
  clauses.all fun c => decide (Complete (clauseScope .target c) a)

def packageAtCheck (m : RawLaneModel) (x : KState) : Bool :=
  packageLaneCheck m.assignment && packageCheck (withdrawnAssignment m) .target &&
    stateViewsCheck (withdrawnAssignment m) x && advancementCheck m

/-- The response reads the same raw four-unit row, not a lucky successor.
Nominal disturbance has identity effects. Every positive support entry must
stay inside S; the owner/resource/unit-ledger/writer gates are independent of S. -/
def responseCheck (m : RawLaneModel) (S : List KState) (x : KState)
    (_disturbance : LaneDisturbance) (a : Action) : Bool :=
  withdrawalCheck m && advancementCheck m &&
    rowClosed8 (withdrawnInputs m) x a S

def retainF (m : RawLaneModel) (S : List KState) (x : KState) : Bool :=
  packageAtCheck m x && actions.any (responseCheck m S x .nominal)
def pruneF (m : RawLaneModel) (S : List KState) := S.filter (retainF m S)
def ViableF (m : RawLaneModel) (S : List KState) : Prop :=
  ∀ x ∈ S, retainF m S x = true

def greatestF (m : RawLaneModel) : List KState :=
  kernel.filter fun x => candidates8.any fun S =>
    decide (x ∈ S) && S.all (retainF m S)

def greatestO (m : RawLaneModel) := greatest8 (withdrawnInputs m) .target

theorem response_mono (m : RawLaneModel) {A B : List KState} (hAB : A ⊆ B)
    (x : KState) (d : LaneDisturbance) (a : Action)
    (h : responseCheck m A x d a = true) : responseCheck m B x d a = true := by
  simp only [responseCheck,Bool.and_eq_true] at h ⊢
  exact ⟨h.1,row_closed8_mono _ _ _ hAB h.2⟩
theorem retainF_mono (m : RawLaneModel) {A B : List KState} (hAB : A ⊆ B)
    (x : KState) (h : retainF m A x = true) : retainF m B x = true := by
  simp only [retainF,Bool.and_eq_true,List.any_eq_true] at h ⊢
  obtain ⟨a,ha,hr⟩ := h.2
  exact ⟨h.1,a,ha,response_mono m hAB x .nominal a hr⟩
theorem pruneF_mono (m : RawLaneModel) {A B : List KState} (hAB : A ⊆ B) :
    pruneF m A ⊆ pruneF m B := by
  intro x hx
  obtain ⟨hx,hr⟩ := List.mem_filter.mp hx
  exact List.mem_filter.mpr ⟨hAB hx,retainF_mono m hAB x hr⟩

theorem member_greatestF (m : RawLaneModel) (x : KState) :
    x ∈ greatestF m ↔ ∃ S ∈ candidates8, x ∈ S ∧ ViableF m S := by
  have hk : x ∈ kernel := by cases x <;> decide
  simp [greatestF,hk,List.mem_filter,List.any_eq_true,List.all_eq_true,ViableF]

theorem greatestF_contains_viable (m : RawLaneModel) (S : List KState)
    (h : ViableF m S) : S ⊆ greatestF m := by
  let normalized := kernel.filter (fun x => decide (x ∈ S))
  have he : ∀ x, x ∈ normalized ↔ x ∈ S := by
    intro x
    have hk : x ∈ kernel := by cases x <;> decide
    simp [normalized,hk]
  have hv : ViableF m normalized := by
    intro x hx
    exact retainF_mono m (fun _ ht => (he _).mpr ht) x (h x ((he x).mp hx))
  intro x hx
  exact (member_greatestF m x).mpr
    ⟨normalized,filter_mem_subsets8 _ kernel,(he x).mpr hx,hv⟩

theorem greatestF_viable (m : RawLaneModel) : ViableF m (greatestF m) := by
  intro x hx
  obtain ⟨S,_,hxS,hv⟩ := (member_greatestF m x).mp hx
  exact retainF_mono m (greatestF_contains_viable m S hv) x (hv x hxS)

theorem greatestF_fixed (m : RawLaneModel) : pruneF m (greatestF m) = greatestF m :=
  List.filter_eq_self.mpr (greatestF_viable m)

theorem greatestF_packageInside (m : RawLaneModel) (x : KState)
    (hx : x ∈ greatestF m) : packageAtCheck m x = true := by
  have hv := greatestF_viable m x hx
  exact (Bool.and_eq_true_iff.mp hv).1

theorem greatestF_all_support_responses (m : RawLaneModel) (x : KState)
    (hx : x ∈ greatestF m) (d : LaneDisturbance) :
    ∃ a ∈ actions, responseCheck m (greatestF m) x d a = true := by
  cases d
  exact List.any_eq_true.mp (Bool.and_eq_true_iff.mp (greatestF_viable m x hx)).2

theorem greatestF_missing_package_empty (m : RawLaneModel)
    (hp : packageLaneCheck m.assignment = false) : greatestF m = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have h := greatestF_packageInside m x hx
  simp [packageAtCheck,hp] at h

/-- Package-filtered viability supplies the actual assigned C6 acceptance,
so its unbounded closure-wide advancement theorem remains available. This is
not a claim about withdrawal entries (the entry adapter is a separate gate). -/
theorem greatestF_c6_advancement (m : RawLaneModel) (s : KState)
    (hs : s ∈ greatestF m) (x : Run6)
    (hx : Closure6 (withdrawnAssignment m) .target x) (a : Action) (o : CSTTT.POS04.PredictiveNow) :
    budgetAfter6 (runInputs6 (withdrawnAssignment m) .target) =
      budget6 (runInputs6 (withdrawnAssignment m) .target) ∧
    budgetAfter6 (runInputs6 (withdrawnAssignment m) .target) > 0 ∧
    (update6 (runInputs6 (withdrawnAssignment m) .target) x a o).funded = true ∧
    (observation6 (runInputs6 (withdrawnAssignment m) .target) .target
      (update6 (runInputs6 (withdrawnAssignment m) .target) x a o)).endogenousRecordCount =
      (observation6 (runInputs6 (withdrawnAssignment m) .target) .target x).endogenousRecordCount + 1 := by
  have hp := greatestF_packageInside m s hs
  simp only [packageAtCheck,Bool.and_eq_true] at hp
  have hpackage := (package_check_iff _ _).mp hp.1.1.2
  exact c6_accept_record_advancement (hpackage .c6) x hx a o

/-- The implication uses a real member of the computed invariant, not empty
universal packageInside. This is the invariant part of AF→P; the full AF
entry/withdrawal certificate is implemented separately. -/
theorem full_invariant_implies_package (m : RawLaneModel)
    (h : greatestF m ≠ []) : PackageLane m.assignment := by
  cases hs : greatestF m with
  | nil => exact False.elim (h hs)
  | cons x xs =>
    have hp := greatestF_packageInside m x (by simp [hs])
    exact ((Bool.and_eq_true_iff.mp ((Bool.and_eq_true_iff.mp ((Bool.and_eq_true_iff.mp hp).1)).1)).1)
end CSTTT.TargetTheory.ComputedFIACH
