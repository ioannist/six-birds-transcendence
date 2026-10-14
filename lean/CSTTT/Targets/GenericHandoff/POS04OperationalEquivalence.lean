import CSTTT.Targets.GenericHandoff.POS04OperationalProtocol
import CSTTT.Targets.GenericHandoff.ScaledRows

/-! Arbitrary-partial-assignment Version O equivalence. The strategy semantics
are independent of the finite algorithm. Forward construction uses the greatest
viable factor set; the converse projects a strategy's actual reachable-run
invariant, proves that projection viable, and then invokes greatest containment.
This is a proved context lift on this interface, not an assumed generic lift. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04OperationalGame
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open CSTTT.TargetTheory.ComputedFIACH
set_option maxRecDepth 4096

 theorem ao_parts (m : RawLaneModel) (h : AO m) :
    Protocol m ∧ greatestO m ≠ [] ∧ entries m ≠ [] ∧
    (∀ e ∈ entries m, entryInside (greatestO m) e = true) := by
  simp only [AO,operationalAutonomyCheck,sharedAutonomyCheck,Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc,hw⟩,ha⟩,hp⟩,hs⟩,hr⟩,he⟩,hi⟩,_⟩ := h
  exact ⟨⟨of_decide_eq_true hc,hw,ha,of_decide_eq_true hp,hr⟩,
    List.isEmpty_eq_false_iff.mp (by simpa using hs),
    List.isEmpty_eq_false_iff.mp (by simpa using he),List.all_eq_true.mp hi⟩

theorem closed_fields (d : ViabilityInputs) (s : KState) (a : Action) (S : List KState)
    (h : rowClosed8 d s a S = true) :
    d.rows s a ≠ [] ∧ (d.rows s a |>.map Prod.snd).sum = 4 ∧
    ∀ e ∈ d.rows s a, e.2 > 0 ∧ ∃ y, e.1 = .inK y ∧ y ∈ S := by
  simp only [rowClosed8,Bool.and_eq_true] at h
  refine ⟨List.isEmpty_eq_false_iff.mp (by simpa using h.1.1),of_decide_eq_true h.1.2,?_⟩
  intro e he
  have hp := List.all_eq_true.mp h.2 e he
  rcases e with ⟨o,n⟩
  cases o with
  | inK y => exact ⟨of_decide_eq_true (Bool.and_eq_true_iff.mp hp).1,y,rfl,
      of_decide_eq_true (Bool.and_eq_true_iff.mp hp).2⟩
  | p2w0 => simp at hp
  | p5w1 => simp at hp

theorem row_normalized (m : RawLaneModel) (h : Protocol m) (r : Run) (s : KState)
    (hs : r.factor = .inK s) (d : Disturbance) (a : Action) (S : List KState)
    (hr : rowClosed8 (inputs m).viability s a S = true) :
    StrategyGame.Normalized (rows m) r d a := by
  have hf := closed_fields _ _ _ _ hr
  have hn := ScaledRows.normalized 4 ((inputs m).viability.rows s a) (by decide)
    hf.1 hf.2.1 (fun e he => (hf.2.2 e he).1)
  simp only [StrategyGame.Normalized,StrategyGame.PositiveSupport,rows,if_pos (protocol_complete m h),rawRow,hs]
  exact ⟨hn.1,hn.2.1,by obtain ⟨o,w,hm,hp⟩ := hn.2.2; exact ⟨o,w,hm,hp⟩⟩

theorem raw_support (m : RawLaneModel) (h : Protocol m) (r : Run) (s : KState)
    (hs : r.factor = .inK s) (d : Disturbance) (a : Action) (e : Ambient × Nat)
    (he : e ∈ (inputs m).viability.rows s a) (hp : e.2 > 0) :
    StrategyGame.PositiveSupport (rows m) r d a e.1 := by
  refine ⟨(e.2 : Rat)/4,?_,ScaledRows.positive 4 e.2 (by decide) hp⟩
  simp only [rows,if_pos (protocol_complete m h),rawRow,hs]
  exact List.mem_map.mpr ⟨e,he,rfl⟩

theorem step_preserves (m : RawLaneModel) (h : Protocol m) (r : Run) (hr : ResourceClosed m r)
    (s : KState) (hs : r.factor = .inK s) (d : Disturbance) (a : Action)
    (hn : ((inputs m).viability.rows s a).isEmpty = false) (o : Ambient) :
    ResourceClosed m (update m r d a o) ∧ StepLaw m r d a o := by
  have hl := hr.2.1
  have hfund : (update m r d a o).funded = true := by
    simp only [update,hl.2.1,hl.2.2.1,hl.2.2.2.1,hr.2.2.1]
    rfl
  have ht : tick (inputs m) r.factor a = 1 := by
    simp only [tick,hs]
    exact protocol_tick m h s a hn
  have ho : (inputs m).viability.resource.owner = .target :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp hr.1).2
  refine ⟨⟨hr.1,hl,hfund,hr.2.2.2⟩,hfund,rfl,?_,?_,rfl,ho⟩
  · simp only [update,ht]
  · have hw : (update m r d a o).residue = r.residue := rfl
    simp only [record,hfund,hr.2.2.1,hr.2.2.2,hw,Bool.true_and,if_true]
    rfl

/-- Every actual raw branch is preserved, for arbitrary assigned tables. -/
def certificateOfAO (m : RawLaneModel) (h : AO m) : Certificate m where
  inside r := r.funded = true ∧ writer (inputs m) r.residue = true ∧
    ∃ s, r.factor = .inK s ∧ s ∈ greatestO m
  withdrawn := (ao_parts m h).1
  entriesNonempty := by
    obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil (entries m) (ao_parts m h).2.2.1
    exact ⟨entryRun m e,e,he,rfl⟩
  entriesInside r hr := by
    obtain ⟨e,he,rfl⟩ := hr
    have hf := entry_facts m (ao_parts m h).1 e he
    have hi := (ao_parts m h).2.2.2 e he
    simp only [entryInside,Bool.and_eq_true] at hi
    cases hs : e.factor with
    | inK s => exact ⟨hf.2.2.2.2,hf.2.2.2.1,s,hs,of_decide_eq_true (by simpa [hs] using hi.2)⟩
    | p2w0 => simp [hs] at hi
    | p5w1 => simp [hs] at hi
  packageInside r hr := by obtain ⟨s,hs,_⟩ := hr.2.2; exact ⟨s,hs⟩
  resourcesInside r hr :=
    ⟨(protocol_resources m (ao_parts m h).1).1,(protocol_resources m (ao_parts m h).1).2.1,hr.1,hr.2.1⟩
  response r hr d := by
    obtain ⟨s,hs,hmem⟩ := hr.2.2
    have hv := greatest8_viable (withdrawnInputs m) .target s hmem
    obtain ⟨a,ha,hrow⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp hv).2
    rw [← viability_eq] at hrow
    have hres : ResourceClosed m r :=
      ⟨(protocol_resources m (ao_parts m h).1).1,(protocol_resources m (ao_parts m h).1).2.1,hr.1,hr.2.1⟩
    refine ⟨a,⟨ha,s,hs,row_closed8_mono _ _ _ (fun x _ => by cases x <;> decide) hrow⟩,
      row_normalized m (ao_parts m h).1 r s hs d a (greatestO m) hrow,?_⟩
    intro o ho
    obtain ⟨w,hw,_⟩ := ho
    simp only [rows,if_pos (protocol_complete m (ao_parts m h).1),rawRow,hs] at hw
    obtain ⟨e,he,heq⟩ := List.mem_map.mp hw
    obtain ⟨_,y,hy,hymem⟩ := (closed_fields _ _ _ _ hrow).2.2 e he
    have heo : e.1 = o := congrArg Prod.fst heq
    have ho' : o = .inK y := heo.symm.trans hy
    have hp := step_preserves m (ao_parts m h).1 r hres s hs d a
      (List.isEmpty_eq_false_iff.mpr (closed_fields _ _ _ _ hrow).1) o
    exact ⟨⟨hp.1.2.2.1,hp.1.2.2.2,y,ho',hymem⟩,hp.2⟩

theorem ao_implies_game (m : RawLaneModel) (h : AO m) : Autonomy m :=
  soundness m (certificateOfAO m h)

/-- The projection is formed from the actual strategy invariant. Classical
existence is auxiliary proof evidence, never a caller-supplied safe-set verdict. -/
theorem certificate_implies_ao (m : RawLaneModel) (cert : Certificate m) : AO m := by
  classical
  let S := kernel.filter fun s => decide (∃ r, cert.inside r ∧ r.factor = .inK s)
  have hS : ∀ s, s ∈ S ↔ ∃ r, cert.inside r ∧ r.factor = .inK s := by
    intro s
    have hk : s ∈ kernel := by cases s <;> decide
    simp [S,hk]
  have hv : Viable8 (withdrawnInputs m) .target S := by
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
    have hav := (cert.resourcesInside r hr).1
    rw [viability_eq] at hav hrow
    exact Bool.and_eq_true_iff.mpr ⟨hav,List.any_eq_true.mpr ⟨a,haActions,hrow⟩⟩
  have hg : S ⊆ greatestO m := greatest8_contains_viable _ _ S hv
  have entryMem : ∀ e ∈ entries m, ∃ s, e.factor = .inK s ∧ s ∈ greatestO m := by
    intro e he
    have hentry : Entries m (entryRun m e) := ⟨e,he,rfl⟩
    have hi := cert.entriesInside _ hentry
    obtain ⟨s,hs⟩ := cert.packageInside _ hi
    exact ⟨s,hs,hg ((hS s).mpr ⟨entryRun m e,hi,hs⟩)⟩
  have heNonempty : entries m ≠ [] := by
    obtain ⟨r,e,he,_⟩ := cert.entriesNonempty
    intro hn
    rw [hn] at he
    contradiction
  have hgNonempty : greatestO m ≠ [] := by
    obtain ⟨e,he⟩ := List.exists_mem_of_ne_nil _ heNonempty
    obtain ⟨s,_,hs⟩ := entryMem e he
    intro hn
    rw [hn] at hs
    contradiction
  have hentries : (entries m).all (entryInside (greatestO m)) = true := by
    apply List.all_eq_true.mpr
    intro e he
    obtain ⟨s,hs,hmem⟩ := entryMem e he
    have hf := entry_facts m cert.withdrawn e he
    simp [entryInside,hf.2.1,hf.2.2.1,hf.1,hs,hmem]
  have hresponses : (greatestO m).all (fun s => actions.any (responseCheck m (greatestO m) s .nominal)) = true := by
    apply List.all_eq_true.mpr
    intro s hs
    have hv' := greatest8_viable (withdrawnInputs m) .target s hs
    obtain ⟨a,ha,hrow⟩ := List.any_eq_true.mp (Bool.and_eq_true_iff.mp hv').2
    exact List.any_eq_true.mpr ⟨a,ha,by
      simp only [responseCheck,cert.withdrawn.2.1,cert.withdrawn.2.2.1,Bool.true_and]
      exact hrow⟩
  simp only [AO,operationalAutonomyCheck,sharedAutonomyCheck,Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨decide_eq_true cert.withdrawn.1,cert.withdrawn.2.1⟩,
    cert.withdrawn.2.2.1⟩,decide_eq_true cert.withdrawn.2.2.2.1⟩,
    by simpa using List.isEmpty_eq_false_iff.mpr hgNonempty⟩,cert.withdrawn.2.2.2.2⟩,
    by simpa using List.isEmpty_eq_false_iff.mpr heNonempty⟩,hentries⟩,hresponses⟩

theorem game_iff_ao (m : RawLaneModel) : Autonomy m ↔ AO m := by
  constructor
  · intro h
    obtain ⟨cert⟩ := StrategyGame.game_invariant_completeness h
    exact certificate_implies_ao m cert
  · exact ao_implies_game m

end CSTTT.TargetTheory.GenericHandoff.POS04OperationalGame
