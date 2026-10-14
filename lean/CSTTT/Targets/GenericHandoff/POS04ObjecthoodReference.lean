import CSTTT.Targets.GenericHandoff.ObjecthoodProtocol
import CSTTT.Targets.GenericHandoff.POS04ObjecthoodProtocol

/-! Exact arbitrary-partial POS-04 specialization of the generic C1 protocol
checker. It uses the already kernel-checked T1 reference data and verifier,
not a second acceptance implementation or a stored uniqueness claim. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodReference
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open POS04ObjecthoodQuotient POS04ObjecthoodTrace

def reference : ObjecthoodProtocol.Reference KState :=
  let d := raw (inputs canonical .source)
  ⟨c1Tau,c1Epsilon,c1RetentionThreshold,d.publishedP,d.publishedC,d.publishedU,c1ColumnRepresentatives⟩

private theorem equal_scaled {n m : Nat} (scale : Rat) (hs : scale ≠ 0)
    (h : (n : Rat)/scale = (m : Rat)/scale) : n = m := by
  have he := congrArg (fun x : Rat => x * scale) h
  simp only [Rat.div_mul_cancel hs] at he
  exact Rat.natCast_inj.mp he

theorem matches_iff (d : Inputs) : ObjecthoodProtocol.Matches reference (raw d) ↔
    T1Anchors d ∧ d.prototypes = c1ColumnRepresentatives := by
  constructor
  · rintro ⟨ht,he,hr,hp,hc,hu,hpro⟩
    refine ⟨⟨?_,?_,?_,?_⟩,hpro⟩
    · cases hd : d.audit
      simp only [reference,raw,hd] at ht he hr
      cases ht; cases he; cases hr
      rfl
    · funext i j
      have hx := congrFun (congrFun hp (stateAt i)) (stateAt j)
      change (d.publishedP (index (stateAt i)) (index (stateAt j)) : Rat)/4 =
        (pNum (index (stateAt i)) (index (stateAt j)) : Rat)/4 at hx
      simpa only [index_stateAt] using equal_scaled 4 (by decide) hx
    · funext i j
      have hx := congrFun (congrFun hc (stateAt i)) j.val
      change (if h : j.val < 7 then (d.publishedC (index (stateAt i)) ⟨j.val,h⟩ : Rat) else 0) =
        (if h : j.val < 7 then (cIndicator (index (stateAt i)) ⟨j.val,h⟩ : Rat) else 0) at hx
      simpa only [dif_pos j.isLt,index_stateAt,Rat.natCast_inj] using hx
    · funext i j
      have hx := congrFun (congrFun hu i.val) (stateAt j)
      change (if h : i.val < 7 then (d.publishedU ⟨i.val,h⟩ (index (stateAt j)) : Rat)/2 else 0) =
        (if h : i.val < 7 then (uPrototypeNum ⟨i.val,h⟩ (index (stateAt j)) : Rat)/2 else 0) at hx
      simp only [dif_pos i.isLt,index_stateAt] at hx
      exact equal_scaled 2 (by decide) hx
  · rintro ⟨⟨ha,hp,hc,hu⟩,hproto⟩
    refine ⟨?_,?_,?_,?_,?_,?_,hproto⟩
    · change d.audit.tau = c1Tau; rw [ha]
    · change d.audit.epsilon = c1Epsilon; rw [ha]
    · change d.audit.retention = c1RetentionThreshold; rw [ha]
    · change (fun s t => (d.publishedP (index s) (index t) : Rat)/4) = _; rw [hp]; rfl
    · change (fun s k => if h : k < 7 then (d.publishedC (index s) ⟨k,h⟩ : Rat) else 0) = _; rw [hc]; rfl
    · change (fun k s => if h : k < 7 then (d.publishedU ⟨k,h⟩ (index s) : Rat)/2 else 0) = _; rw [hu]; rfl

/-- The generic action-support check already entails POS-04's row checks.
This is the additional converse needed for EXACT acceptance equivalence. -/
theorem rows_valid_from_support (d : Inputs) (h : ObjecthoodRules.SupportCheck (raw d)) : RowsValid d := by
  simp only [RowsValid,List.all_eq_true,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,decide_eq_true_eq]
  intro s hs a ha
  constructor
  · intro e he
    refine ⟨h.2.2.1 s a e he,?_⟩
    cases e.1 with
    | inK k => cases k <;> decide
    | p2w0 => decide
    | p5w1 => decide
  · rw [POS04ObjecthoodProtocol.sum_weights]
    exact h.2.2.2 s a

def Accept (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) : Prop :=
  ObjecthoodProtocol.Accept POS04ProfileRules.schema reference (POS04ObjecthoodCells.bindings tag) a

theorem generic_c1_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) : Accept a tag ↔ C1Accept a tag := by
  rw [← POS04ObjecthoodProtocol.generic_c1_iff]
  constructor
  · rintro ⟨d,hd,ha,hm⟩
    have old : ObjecthoodCells.Accept POS04ProfileRules.schema (POS04ObjecthoodCells.bindings tag) a := ⟨d,hd,ha⟩
    have hp := (POS04ObjecthoodCells.accept_decode_iff a tag).mp old
    have hd' := POS04ObjecthoodCells.decoded_complete a tag hp.1
    have he := Option.some.inj (hd.symm.trans hd')
    subst d
    have hm := (matches_iff _).mp hm
    exact ⟨old,hm.1,rows_valid_from_support _ ha.1.2.2.2.1,hm.2⟩
  · rintro ⟨old,ha,hv,hproto⟩
    have hp := (POS04ObjecthoodCells.accept_decode_iff a tag).mp old
    exact ⟨_,POS04ObjecthoodCells.decoded_complete a tag hp.1,hp.2,(matches_iff _).mpr ⟨ha,hproto⟩⟩

theorem canonical_accept (tag : Tag) : Accept canonical tag :=
  (generic_c1_iff _ _).mpr (canonical_c123 tag).1

theorem deleted_C_rejected (tag : Tag) :
    ¬ Accept (CSTTT.POS04.Assigned.put canonical .publishedC none) tag := by
  apply ObjecthoodProtocol.missing_rejected _ _ _ _ .publishedC
  · simp [POS04ObjecthoodCells.bindings,ObjecthoodCells.Bindings.scope]
  · simp

end CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodReference
