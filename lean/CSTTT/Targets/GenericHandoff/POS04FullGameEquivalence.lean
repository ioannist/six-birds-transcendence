import CSTTT.Targets.GenericHandoff.POS04OperationalEquivalence

/-! Exact F interpretation on the POS-04 assignment interface. Same assigned
package at acquisition and after withdrawal; the actual current factor is checked.
Ledger, record, tick and register context is checked by the shared operational
interpreter, on every actual support branch. This is a family specialization,
not a claim that unrestricted run recipes have a finite-context projection. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04FullGame
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH
open POS04OperationalGame
set_option maxRecDepth 4096

/-- Assigned primitives and the actual factor, not an arrival-only verdict. -/
def PackageAt (m : RawLaneModel) (r : Run) : Prop :=
  PackageLane m.assignment ∧ ∃ s, r.factor = .inK s ∧ packageAtCheck m s = true
abbrev Certificate (m : RawLaneModel) :=
  StrategyGame.InvariantCertificate (rows m) (update m) (Entries m) (Protocol m)
    (PackageAt m) (ResourceClosed m) (Legal m) (StepLaw m)
def Autonomy (m : RawLaneModel) : Prop :=
  StrategyGame.GameReadout (rows m) (update m) (Entries m) (Protocol m)
    (PackageAt m) (ResourceClosed m) (Legal m) (StepLaw m)

theorem soundness (m : RawLaneModel) (h : Certificate m) : Autonomy m :=
  StrategyGame.invariant_game_soundness _ _ _ _ _ _ _ _ h

theorem full_implies_arrival (m : RawLaneModel) (h : Autonomy m) : PackageLane m.assignment :=
  StrategyGame.game_same_package_implies_arrival h

theorem af_parts (m : RawLaneModel) (h : AF m) :
    Protocol m ∧ greatestF m ≠ [] ∧ entries m ≠ [] ∧
    (∀ e ∈ entries m, entryInside (greatestF m) e = true) := by
  have h := (Bool.and_eq_true_iff.mp h).1
  simp only [sharedAutonomyCheck,Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc,hw⟩,ha⟩,hp⟩,hs⟩,hr⟩,he⟩,hi⟩,_⟩ := h
  exact ⟨⟨of_decide_eq_true hc,hw,ha,of_decide_eq_true hp,hr⟩,
    List.isEmpty_eq_false_iff.mp (by simpa using hs),
    List.isEmpty_eq_false_iff.mp (by simpa using he),List.all_eq_true.mp hi⟩

def certificateOfAF (m : RawLaneModel) (h : AF m) : Certificate m where
  inside r := r.funded = true ∧ writer (inputs m) r.residue = true ∧
    ∃ s, r.factor = .inK s ∧ s ∈ greatestF m
  withdrawn := (af_parts m h).1
  entriesNonempty := by
    obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil (entries m) (af_parts m h).2.2.1
    exact ⟨entryRun m e,e,he,rfl⟩
  entriesInside r hr := by
    obtain ⟨e,he,rfl⟩ := hr
    have hf := entry_facts m (af_parts m h).1 e he
    have hi := (af_parts m h).2.2.2 e he
    simp only [entryInside,Bool.and_eq_true] at hi
    cases hs : e.factor with
    | inK s => exact ⟨hf.2.2.2.2,hf.2.2.2.1,s,hs,of_decide_eq_true (by simpa [hs] using hi.2)⟩
    | p2w0 => simp [hs] at hi
    | p5w1 => simp [hs] at hi
  packageInside r hr := by
    obtain ⟨s,hs,hm⟩ := hr.2.2
    exact ⟨fullAutonomy_implies_package m h,s,hs,greatestF_packageInside m s hm⟩
  resourcesInside r hr :=
    ⟨(protocol_resources m (af_parts m h).1).1,(protocol_resources m (af_parts m h).1).2.1,hr.1,hr.2.1⟩
  response r hr d := by
    obtain ⟨s,hs,hmem⟩ := hr.2.2
    obtain ⟨a,ha,hresp⟩ := greatestF_all_support_responses m s hmem d
    have hrow := (Bool.and_eq_true_iff.mp hresp).2
    rw [← viability_eq] at hrow
    have hres : ResourceClosed m r :=
      ⟨(protocol_resources m (af_parts m h).1).1,(protocol_resources m (af_parts m h).1).2.1,hr.1,hr.2.1⟩
    refine ⟨a,⟨ha,s,hs,row_closed8_mono _ _ _ (fun x _ => by cases x <;> decide) hrow⟩,
      row_normalized m (af_parts m h).1 r s hs d a (greatestF m) hrow,?_⟩
    intro o ho
    obtain ⟨w,hw,_⟩ := ho
    simp only [rows,if_pos (protocol_complete m (af_parts m h).1),rawRow,hs] at hw
    obtain ⟨e,he,heq⟩ := List.mem_map.mp hw
    obtain ⟨_,y,hy,hymem⟩ := (closed_fields _ _ _ _ hrow).2.2 e he
    have heo : e.1 = o := congrArg Prod.fst heq
    have ho' : o = .inK y := heo.symm.trans hy
    have hp := step_preserves m (af_parts m h).1 r hres s hs d a
      (List.isEmpty_eq_false_iff.mpr (closed_fields _ _ _ _ hrow).1) o
    exact ⟨⟨hp.1.2.2.1,hp.1.2.2.2,y,ho',hymem⟩,hp.2⟩

theorem af_implies_game (m : RawLaneModel) (h : AF m) : Autonomy m :=
  soundness m (certificateOfAF m h)

theorem certificate_implies_af (m : RawLaneModel) (cert : Certificate m) : AF m := by
  classical
  let S := kernel.filter fun s => decide (∃ r, cert.inside r ∧ r.factor = .inK s)
  have hS : ∀ s, s ∈ S ↔ ∃ r, cert.inside r ∧ r.factor = .inK s := by
    intro s
    have hk : s ∈ kernel := by cases s <;> decide
    simp [S,hk]
  have hv : ViableF m S := by
    intro s hs
    obtain ⟨r,hr,hfactor⟩ := (hS s).mp hs
    obtain ⟨a,ha,_hn,hnext⟩ := cert.response r hr .nominal
    obtain ⟨haActions,t,ht,hkernel⟩ := ha
    have heq : t = s := by injection (ht.symm.trans hfactor)
    subst t
    have hf := closed_fields _ _ _ _ hkernel
    have hrow : rowClosed8 (inputs m).viability s a S = true := by
      simp only [rowClosed8,Bool.and_eq_true,List.all_eq_true]
      refine ⟨⟨by simpa using List.isEmpty_eq_false_iff.mpr hf.1,
        decide_eq_true hf.2.1⟩,?_⟩
      intro e he
      obtain ⟨hp,y,hy,_⟩ := hf.2.2 e he
      have hsupport := raw_support m cert.withdrawn r s hfactor .nominal a e he hp
      have hinside := (hnext e.1 hsupport).1
      have hmem : y ∈ S := (hS y).mpr ⟨update m r .nominal a e.1,hinside,hy⟩
      simp [hy,hp,hmem]
    obtain ⟨_,t,ht,hpackage⟩ := cert.packageInside r hr
    have heq : t = s := by injection (ht.symm.trans hfactor)
    subst t
    simp only [retainF,Bool.and_eq_true,List.any_eq_true]
    exact ⟨hpackage,a,haActions,by
      simp only [responseCheck,cert.withdrawn.2.1,cert.withdrawn.2.2.1,Bool.true_and]
      rw [viability_eq] at hrow
      exact hrow⟩
  have hg : S ⊆ greatestF m := greatestF_contains_viable m S hv
  have entryMem : ∀ e ∈ entries m, ∃ s, e.factor = .inK s ∧ s ∈ greatestF m := by
    intro e he
    have hentry : Entries m (entryRun m e) := ⟨e,he,rfl⟩
    have hi := cert.entriesInside _ hentry
    obtain ⟨_,s,hs,_⟩ := cert.packageInside _ hi
    exact ⟨s,hs,hg ((hS s).mpr ⟨entryRun m e,hi,hs⟩)⟩
  have heNonempty : entries m ≠ [] := by
    obtain ⟨r,e,he,_⟩ := cert.entriesNonempty
    intro hn
    rw [hn] at he
    contradiction
  have hgNonempty : greatestF m ≠ [] := by
    obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ heNonempty
    obtain ⟨s,_,hs⟩ := entryMem e he
    intro hn
    rw [hn] at hs
    contradiction
  have hentries : (entries m).all (entryInside (greatestF m)) = true := by
    apply List.all_eq_true.mpr
    intro e he
    obtain ⟨s,hs,hmem⟩ := entryMem e he
    have hf := entry_facts m cert.withdrawn e he
    simp [entryInside,hf.2.1,hf.2.2.1,hf.1,hs,hmem]
  have hresponses : (greatestF m).all (fun s => actions.any (responseCheck m (greatestF m) s .nominal)) = true := by
    apply List.all_eq_true.mpr
    intro s hs
    obtain ⟨a,ha,hr⟩ := greatestF_all_support_responses m s hs .nominal
    exact List.any_eq_true.mpr ⟨a,ha,hr⟩
  simp only [AF,fullAutonomyCheck,sharedAutonomyCheck,Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨decide_eq_true cert.withdrawn.1,cert.withdrawn.2.1⟩,
    cert.withdrawn.2.2.1⟩,decide_eq_true cert.withdrawn.2.2.2.1⟩,
    by simpa using List.isEmpty_eq_false_iff.mpr hgNonempty⟩,cert.withdrawn.2.2.2.2⟩,
    by simpa using List.isEmpty_eq_false_iff.mpr heNonempty⟩,hentries⟩,hresponses⟩,
    List.all_eq_true.mpr (greatestF_packageInside m)⟩

theorem game_iff_af (m : RawLaneModel) : Autonomy m ↔ AF m := by
  constructor
  · intro h
    obtain ⟨cert⟩ := StrategyGame.game_invariant_completeness h
    exact certificate_implies_af m cert
  · exact af_implies_game m

end CSTTT.TargetTheory.GenericHandoff.POS04FullGame
