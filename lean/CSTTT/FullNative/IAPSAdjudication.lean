import CSTTT.FullNative.SharedAttribution
import CSTTT.Autonomy.System

/-! G29: an explicit structural successor, and rejection of the original
package-preserving autonomy lane on G27's actual whole-package readout.
Validity below is computed execution availability, not a supplied lane tuple.
The primitive request selects one of the two residents of the same final World.
No historical source-memory package is substituted for SharedPackage.Accept. -/
namespace CSTTT.FullNative.IAPSAdjudication
open AccountExecution PhysicalExecution SnapshotExecution SharedPackage OriginalPackage
set_option autoImplicit false
set_option maxHeartbeats 8000000
set_option maxRecDepth 8192

abbrev Cert := Bool
def Valid (right : Cert) : Prop := (execution (targetRaw right)).isSome=true
def PredictiveAncestry (right : Cert) : Prop :=
  SharedAttribution.ancestry 0 (TemporalTransport.branchOwner right).val ∧
  (targetExecution right).resident.installed=TemporalTransport.sourceAtCopy.resident.installed ∧
  (targetExecution right).resident.rootedRoute=([TemporalTransport.anchor.state],[TemporalTransport.anchor.receipt]) ∧
  (TemporalTransport.writtenSnapshot right).map (fun s => s.receipt)=
    TemporalTransport.sourceAtCopy.resident.receipts.head? ∧
  (∀ word trace,
    WeightedFuture.law (normalizedRows renewable)
      (fun x => FullInterface.observe (TemporalTransport.shiftRun TemporalTransport.anchor (frame x)))
      (TemporalTransport.targetAtCopy right) word trace=
    WeightedFuture.law FullInterface.rows FullInterface.observe
      (TemporalTransport.rebase (TemporalTransport.targetAtCopy right).resident.owner
        (TemporalTransport.targetAtCopy right).resident.rootedRoute (frame TemporalTransport.sourceAtCopy)) word trace) ∧
  (∀ word trace,
    WeightedFuture.law (normalizedRows renewable)
      (fun x => FullInterface.observe (TemporalTransport.shiftRun TemporalTransport.anchor (frame x)))
      (targetExecution right) word trace=
    WeightedFuture.law FullInterface.rows FullInterface.observe
      (TemporalTransport.shiftRun TemporalTransport.anchor (frame (targetExecution right))) word trace)

def PackageRealized (right : Cert) : Prop := Accept (targetRaw right)

/-- Deliberately named RESOURCE continuation: full-clock progress, greatest
actual-history viability and simultaneous funded withdrawn sibling paths.
It does not assert that every future receipt audit still closes a cycle. -/
def ResourceContinuation (right : Cert) : Prop :=
  ClockAudit (targetExecution right) ∧
  (∃ h : Viability.History true, execution (targetRaw right)=some h.1 ∧
    ∃ V : Viability.History true → Prop, Viability.HistoryControlled true V ∧ V h) ∧
  ∀ word, ∃ w, JointContinuation (targetRaw right).world word w ∧
    Historical w ∧ Siblings w ∧ w.carriers 0=none ∧ w.bridge=none

/-- The original autonomy lane must retain the ACTUAL package. This necessary
controlled-closure condition even permits a favorable outcome, making its
refutation stronger than rejection of one fixed policy or one adverse path. -/
def PackageAutonomous (right : Cert) : Prop :=
  ∃ V : Raw → Prop, V (targetRaw right) ∧ (∀ p, V p → Accept p) ∧
    ∀ p, V p → ∃ a q n, (q,n)∈nativeRows renewable p.world p.owner a ∧ V ⟨q,p.owner⟩

theorem valid_each_request (right : Cert) : Valid right := by
  simp only [Valid,target_read,Option.isSome_some]

theorem predictive_ancestry_from_raw (right : Cert) : PredictiveAncestry right := by
  have ancestors := SharedAttribution.source_to_both_targets
  have ancestor : SharedAttribution.ancestry 0 (TemporalTransport.branchOwner right).val := by
    cases right
    · exact ancestors.1
    · exact ancestors.2
  have provenance := SharedAttribution.edge_provenance right
  refine ⟨ancestor,provenance.1,provenance.2.2.1,provenance.2.1,
    TemporalTransport.actual_transported_future right,?_⟩
  intro word trace
  rw [TemporalTransport.actual_frame_law
    (fun r => FullInterface.observe (TemporalTransport.shiftRun TemporalTransport.anchor r))
    _ (actual_ready.2 right).1,TemporalTransport.shifted_future_law]

theorem resource_continuation_from_raw (right : Cert) : ResourceContinuation right := by
  have cert := computed_certificate (targetExecution right) (actual_ready.2 right)
  refine ⟨cert.c6.2.1,accepted_history_viable _ (source_and_both_targets.2 right),?_⟩
  intro word
  obtain ⟨w,path,historical,siblings⟩ := Credit.credited_joint_future word
  have controls := SharedAttribution.all_joint_paths_have_no_merger word w path
  cases right <;> exact ⟨w,path,historical,siblings,controls.2.2.1,controls.2.2.2⟩

theorem all_checkpoint_lanes_from_shared_raw (right : Cert) :
    PredictiveAncestry right ∧ PackageRealized right ∧ ResourceContinuation right :=
  ⟨predictive_ancestry_from_raw right,source_and_both_targets.2 right,resource_continuation_from_raw right⟩

/-- Exact original SCHEMA instantiated with an explicitly DIFFERENT final
predicate. This theorem is the disclosed successor, not original autonomy. -/
theorem checkpoint_resource_successor :
    CSTTT.Prospects.IntegratedTemporalIAPS Cert Valid PredictiveAncestry PackageRealized ResourceContinuation :=
  fun right _ => all_checkpoint_lanes_from_shared_raw right

theorem no_independent_package_lanes (right : Cert) (c : Clause) :
    clause (targetRaw right) c := (all_eight_from_same_raw c).2 right

theorem endpoint_receipt_ends (right : Cert) :
    (targetExecution right).resident.receipts≠[] ∧
    ((targetExecution right).resident.receipts.getLast?.map Receipt.before)=some FullInterface.rootState ∧
    (targetExecution right).resident.current.phase=false := by
  cases right <;> decide +kernel

theorem last_kept (rs : List Receipt) (r : Receipt) (present : rs≠[]) :
    (r::rs).getLast?=rs.getLast? := by
  cases rs with
  | nil => contradiction
  | cons s tail => simp

theorem target_step_credit_rejected (right : Cert) (a : Bool) (y : Execution) (n : Nat)
    (edge : (y,n)∈rawRows renewable (targetExecution right) a) : credit y=.rejected := by
  have sector := (actual_ready.2 right).1
  have tick := (Credit.actual_clock_step _ _ sector a n edge).2.2.1
  rw [sector_rows _ sector a] at edge
  obtain ⟨entry,member,equal⟩ := List.mem_map.mp edge
  have eq : y=advance renewable (targetExecution right) a entry.1 entry.2 :=
    (congrArg Prod.fst equal).symm
  subst y
  have phase : entry.1.phase=true := by
    simpa only [advance,(endpoint_receipt_ends right).2.2,Bool.not_false] using tick
  have unequal : some entry.1≠some FullInterface.rootState := by
    intro same
    have eq := congrArg State.phase (Option.some.inj same)
    rw [phase] at eq
    contradiction
  have closed : Credit.closedReceipts
      (issued renewable (targetExecution right) a entry.1 entry.2 ::
        (targetExecution right).resident.receipts)=false := by
    simp only [Credit.closedReceipts,List.isEmpty_cons,Bool.not_false,List.head?_cons,Option.map_some,
      last_kept _ _ (endpoint_receipt_ends right).1,(endpoint_receipt_ends right).2.1]
    simp only [issued,unequal,decide_false,Bool.and_false]
  simp only [credit,advance,sector.1,Option.some.injEq]
  simp [Credit.receiptCredit,Credit.validReceipts,closed]

theorem target_step_c5_rejected (right : Cert) (a : Bool) (y : Execution) (n : Nat)
    (edge : (y,n)∈rawRows renewable (targetExecution right) a) : ¬C5 y := by
  intro claimed
  have credit := claimed.1
  rw [target_step_credit_rejected right a y n edge] at credit
  contradiction

theorem every_native_successor_rejects_package (right : Cert) (a : Bool) (w : World) (n : Nat)
    (edge : (w,n)∈nativeRows renewable (targetRaw right).world (targetRaw right).owner a) :
    ¬Accept ⟨w,(targetRaw right).owner⟩ := by
  have projection := world_rows_project _ _ (target_read right) (actual_ready.2 right).1 a
  have observed : (execution ⟨w,(targetRaw right).owner⟩,n)∈
      (nativeRows renewable (targetRaw right).world (targetRaw right).owner a).map
        (fun e => (execution ⟨e.1,(targetRaw right).owner⟩,e.2)) :=
    List.mem_map.mpr ⟨(w,n),edge,rfl⟩
  rw [projection] at observed
  obtain ⟨entry,native,equal⟩ := List.mem_map.mp observed
  have read : execution ⟨w,(targetRaw right).owner⟩=some entry.1 :=
    (congrArg Prod.fst equal).symm
  have reject := target_step_credit_rejected right a entry.1 entry.2 native
  apply (raw_gate_rejected _ _ read ?_).1
  intro ready
  have self := ready.2.2
  rw [reject] at self
  contradiction

theorem original_package_autonomy_refuted (right : Cert) : ¬PackageAutonomous right := by
  rintro ⟨V,initial,accepted,closed⟩
  obtain ⟨a,w,n,edge,inside⟩ := closed _ initial
  exact every_native_successor_rejects_package right a w n edge (accepted _ inside)

/-- Direct bridge to the ORIGINAL controlled-invariant certificate. Any
presentation that really reads this endpoint/package and native step relation
is rejected. The proof does not assume finite histories or weaken a package
field to viability. Stronger ownership/solvency/anti-stall fields cannot repair
failure of these necessary fields. No such presentation is supplied as data. -/
theorem no_faithful_original_invariant (right : Cert) (sys : CSTTT.ControlledSystem)
    (decode : sys.carrier.State → Raw) (endpoint : sys.carrier.State)
    (atEndpoint : decode endpoint=targetRaw right)
    (packageSound : ∀ x, sys.packageValid x → Accept (decode x))
    (disturbance : sys.Disturbance)
    (stepSound : ∀ x y d a, sys.step x d a y →
      ∃ action w n, (w,n)∈nativeRows renewable (decode x).world (decode x).owner action ∧
        decode y=⟨w,(decode x).owner⟩) :
    ¬Nonempty (CSTTT.ControlledInvariantCertificate sys endpoint) := by
  rintro ⟨cert⟩
  obtain ⟨a,y,_,step,inside⟩ := cert.targetOwnedResponse endpoint disturbance cert.endpointInside
  obtain ⟨action,w,n,edge,read⟩ := stepSound endpoint y disturbance a step
  rw [atEndpoint] at edge read
  have accepted := packageSound y (cert.packageInside y inside)
  rw [read] at accepted
  exact every_native_successor_rejects_package right action w n edge accepted

theorem no_faithful_original_autonomy (right : Cert) (sys : CSTTT.ControlledSystem)
    (decode : sys.carrier.State → Raw) (endpoint : sys.carrier.State)
    (atEndpoint : decode endpoint=targetRaw right)
    (packageSound : ∀ x, sys.packageValid x → Accept (decode x))
    (disturbance : sys.Disturbance)
    (stepSound : ∀ x y d a, sys.step x d a y →
      ∃ action w n, (w,n)∈nativeRows renewable (decode x).world (decode x).owner action ∧
        decode y=⟨w,(decode x).owner⟩) :
    ¬Nonempty (CSTTT.AutonomyCertificate sys endpoint) := by
  rintro ⟨cert⟩
  exact no_faithful_original_invariant right sys decode endpoint atEndpoint packageSound
    disturbance stepSound ⟨cert.invariant⟩

theorem original_iaps_schema_refuted :
    ¬CSTTT.Prospects.IntegratedTemporalIAPS Cert Valid PredictiveAncestry PackageRealized PackageAutonomous := by
  intro claimed
  exact original_package_autonomy_refuted false (claimed false (valid_each_request false)).2.2

/-- The stronger honest assembled return: the G27 audited package, rooted
fission and all-word funded joint histories without merger, and BOTH targets'
checkpoint/resource lanes together with the original-autonomy negatives.
There are no independently supplied clause or lane inputs. -/
theorem adjudicated_shared_raw_package :
    OriginalPackage.AuditedAssembly ∧
    (SharedAttribution.ancestry 0 1 ∧ SharedAttribution.ancestry 0 2) ∧
    (∀ word, ∃ w, JointContinuation (targetRaw false).world word w ∧
      Historical w ∧ Siblings w ∧ ¬SharedAttribution.FusionRealized w) ∧
    (∀ right : Cert, Valid right ∧ PredictiveAncestry right ∧
      PackageRealized right ∧ ResourceContinuation right ∧ ¬PackageAutonomous right) := by
  refine ⟨OriginalPackage.audited_shared_raw_successor,SharedAttribution.source_to_both_targets,?_,?_⟩
  · intro word
    obtain ⟨w,path,history,siblings⟩ := Credit.credited_joint_future word
    exact ⟨w,path,history,siblings,SharedAttribution.siblings_are_not_fusion w siblings⟩
  · intro right
    exact ⟨valid_each_request right,predictive_ancestry_from_raw right,
      source_and_both_targets.2 right,resource_continuation_from_raw right,
      original_package_autonomy_refuted right⟩

theorem actual_iaps_countertrace :
    PredictiveAncestry false ∧ PackageRealized false ∧ ResourceContinuation false ∧
    (PublicShadow.after.world,weight PublicShadow.beforeExecution.resident.current false false)∈
      nativeRows renewable PublicShadow.before.world PublicShadow.before.owner false ∧
    ¬Accept PublicShadow.after ∧ ClockAudit PublicShadow.afterExecution ∧
    (frame PublicShadow.beforeExecution).context.order=6 ∧
    (frame PublicShadow.afterExecution).context.order=7 ∧
    (PublicShadow.afterExecution.resident.receipts.head?).map Receipt.serial=some 25 :=
  ⟨predictive_ancestry_from_raw false,source_and_both_targets.2 false,
    resource_continuation_from_raw false,PublicShadow.actual_step,PublicShadow.after_package_rejected,
    PublicShadow.funded_clock_survives,PublicShadow.actual_countertrace.1,
    PublicShadow.actual_countertrace.2.1,PublicShadow.actual_countertrace.2.2.2.2.1⟩

end CSTTT.FullNative.IAPSAdjudication
