import CSTTT.Targets.GenericHandoff.POS04ObjecthoodInstance

/-! The POS-04 protocol is checked explicitly. This specialization is separate
from the polymorphic C1 rule, which admits other protocols and comparison data.
No acceptance or uniqueness verdict is a primitive. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodProtocol
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit
open POS04ObjecthoodQuotient POS04ObjecthoodTrace

/-- First-occurrence prototype order is raw data, not a class-label verdict. -/
theorem prototypes_eq (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    d.prototypes = c1ColumnRepresentatives := by
  rcases hr with ⟨hi,hl,hc,_,_,_,_,_,_⟩
  simp only [List.all_eq_true,beq_iff_eq] at hc
  apply List.ext_getElem
  · simpa using hl
  · intro n hn hm
    have hk : n < 7 := by simpa [hl] using hn
    have h := hc ⟨n,hk⟩ (by simp)
    rw [hi,ha.2.2.1] at h
    have hf : ((List.finRange 10).filter fun i => cIndicator i ⟨n,hk⟩ == 1).head? =
        some (index (c1ColumnRepresentatives.getD n .p0w0)) := by
      have all : ∀ k : J,
          ((List.finRange 10).filter fun i => cIndicator i k == 1).head? =
            some (index (c1ColumnRepresentatives.getD k.val .p0w0)) := by decide
      exact all ⟨n,hk⟩
    rw [hf] at h
    have he := POS04ObjecthoodTrace.index_injective _ _ |>.mp (Option.some.inj h)
    simpa [List.getD,hn,hm] using he.symm

theorem assigned_kernel (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.KernelCheck (raw d) := by
  have hc := (POS04ObjecthoodInstance.canonical_raw_gate .source).1
  have hc1 := (canonical_c123 .source).1.1
  have hp := POS04ObjecthoodOperator.P_matrix d ha hr
  have hp0 := POS04ObjecthoodOperator.P_matrix
    (clauseInputs canonical .source .c1) hc1.2.1 hc1.2.2
  unfold ObjecthoodRules.KernelCheck at hc ⊢
  rw [hp] 
  rw [hp0] at hc
  simpa only [raw,POS04ProfileRules.raw,POS04ProfileRules.schema,ha.1] using hc

theorem assigned_quotient (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d) :
    ObjecthoodRules.QuotientCheck (raw d) := by
  have he := prototypes_eq d ha hr
  change (classOrder d).Nodup ∧ (∀ s : KState, s ∈ kernel) ∧
    (∀ p ∈ d.prototypes, p ∈ kernel) ∧
    (∀ s, predictive d s ∈ classOrder d) ∧ _
  refine ⟨hr.2.2.2.1,(by intro s; cases s <;> decide),?_,?_,?_⟩
  · intro p hp; cases p <;> decide
  · intro s
    have hc := hr.2.2.2.2.1
    simp only [List.all_eq_true,decide_eq_true_eq] at hc
    exact hc s (by cases s <;> decide)
  · intro k p hp
    change d.prototypes[k.val]? = some p at hp
    change (kernel.filter fun s => decide (predictive d s = predictive d p)).head? = some p
    have hf : (kernel.filter fun s => decide (predictive d s = predictive d p)) =
        kernel.filter fun s => decide (mClass (index s) = mClass (index p)) := by
      apply List.filter_congr
      intro s hs
      exact Bool.eq_iff_iff.mpr (by simp only [decide_eq_true_eq]; exact predictive_partition d ha hr s p)
    rw [hf]
    rw [he] at hp
    have all : ∀ n : Fin 7, ∀ p : KState, c1ColumnRepresentatives[n.val]? = some p →
      (kernel.filter fun s => decide (mClass (index s) = mClass (index p))).head? = some p := by
        intro n p; cases p <;> decide +revert
    exact all ⟨k.val,by simpa [raw,he] using k.isLt⟩ p hp

theorem sum_weights (row : List (Ambient × Nat)) :
    row.foldl (fun n e => n + e.2) 0 = (row.map Prod.snd).sum := by
  have gen (n : Nat) : row.foldl (fun n e => n + e.2) n = n + (row.map Prod.snd).sum := by
    induction row generalizing n with
    | nil => simp
    | cons e es ih => simp only [List.foldl_cons,List.map_cons,List.sum_cons]; rw [ih]; omega
  simpa only [Nat.zero_add] using gen 0

theorem assigned_support (d : Inputs) (hv : RowsValid d) :
    ObjecthoodRules.SupportCheck (raw d) := by
  simp only [RowsValid,List.all_eq_true,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq,
    decide_eq_true_eq] at hv
  change actions.Nodup ∧ (∀ a : Action, a ∈ actions) ∧
    (∀ s a e, e ∈ d.rows s a → 0 < e.2) ∧
    (∀ s a, (d.rows s a |>.map Prod.snd).sum = 0 ∨
      (d.rows s a |>.map Prod.snd).sum = 4)
  refine ⟨by decide,(by intro a; cases a <;> decide),?_,?_⟩
  · intro s a e he
    exact (hv s (by cases s <;> decide) a (by cases a <;> decide)).1 e he |>.1
  · intro s a
    have h := (hv s (by cases s <;> decide) a (by cases a <;> decide)).2
    simpa only [sum_weights,raw] using h

theorem assigned_gate (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (hv : RowsValid d) : ObjecthoodRules.Gate (raw d) :=
  ⟨assigned_kernel d ha hr,assigned_quotient d ha hr,rational_reconstruction d ha hr,
    assigned_support d hv,assigned_trace_check d ha hr⟩

theorem assigned_accept (d : Inputs) (ha : T1Anchors d) (hr : TablesReconstructed d)
    (hv : RowsValid d) : ObjecthoodRules.Accept (raw d) := by
  refine ⟨assigned_gate d ha hr hv,assigned_nonuniform d ha hr,?_,assigned_TV d ha hr,
    assigned_zero_defect d ha hr,assigned_eps_defect d ha hr⟩
  rw [assigned_core_mass d ha hr]
  change (77/80 : Rat) ≥ d.audit.retention
  rw [ha.1]
  decide +kernel

/-- Fixed protocol, raw outcome well-formedness and exact column ordering.
No computed reconstruction, fixed-point, or acceptance conclusion is stored. -/
def Protocol (d : Inputs) : Prop :=
  T1Anchors d ∧ RowsValid d ∧ d.prototypes = c1ColumnRepresentatives

private theorem unscale {n m : Nat} {scale : Rat} (hs : scale ≠ 0)
    (h : (n : Rat) / scale = (m : Rat) / scale) : n = m := by
  have he := congrArg (fun x : Rat => x * scale) h
  simp only [Rat.div_mul_cancel hs] at he
  exact Rat.natCast_inj.mp he

private theorem columns (d : Inputs) (hlen : d.prototypes.length = 7)
    (hr : ObjecthoodRules.Reconstruction (raw d)) (i : I) (k : J) :
    rawC d i k = d.publishedC i k := by
  have h := hr.2.1 (stateAt i) ⟨k.val,by simp only [raw,hlen]; exact k.isLt⟩
  rw [C_readout d hlen] at h
  change (rawC d (index (stateAt i)) k : Rat) =
    (if h : k.val < 7 then (d.publishedC (index (stateAt i)) ⟨k.val,h⟩ : Rat) else 0) at h
  simpa only [index_stateAt,dif_pos k.isLt,Rat.natCast_inj] using h

private theorem column_partition (d : Inputs) (hlen : d.prototypes.length = 7)
    (hcov : ∀ s, predictive d s ∈ classOrder d) (s t : KState) :
    predictive d s = predictive d t ↔ ∀ k : J, rawC d (index s) k = rawC d (index t) k := by
  constructor
  · intro h k
    simp only [rawC,stateAt_index]
    rw [h]
  · intro h
    obtain ⟨n,hn,hv⟩ := List.getElem_of_mem (hcov s)
    let k : J := ⟨n,by simpa [classOrder,hlen] using hn⟩
    have hd : (classOrder d).getD k.val (0,[]) = predictive d s := by
      simp [List.getD,List.getElem?_eq_getElem hn,hv,k]
    have hs : rawC d (index s) k = 1 := by simp only [rawC,stateAt_index]; rw [hd]; simp
    have ht : rawC d (index t) k = 1 := (h k).symm.trans hs
    simp only [rawC,stateAt_index,hd] at ht
    by_cases he : predictive d t = predictive d s
    · exact he.symm
    · simp [he] at ht

private theorem partition_from_reconstruction (d : Inputs) (ha : T1Anchors d)
    (hlen : d.prototypes.length = 7) (hq : ObjecthoodRules.QuotientCheck (raw d))
    (hr : ObjecthoodRules.Reconstruction (raw d)) (s t : KState) :
    predictive d s = predictive d t ↔ mClass (index s) = mClass (index t) := by
  rw [column_partition d hlen hq.2.2.2.1]
  simp only [columns d hlen hr,ha.2.2.1]
  exact imported_columns_iff s t

private theorem small_fibers (d : Inputs) (ha : T1Anchors d)
    (hlen : d.prototypes.length = 7) (hq : ObjecthoodRules.QuotientCheck (raw d))
    (hr : ObjecthoodRules.Reconstruction (raw d)) (s : KState) :
    fiberSize d s = 1 ∨ fiberSize d s = 2 := by
  have hf : fiberSize d s = classSize (index s) := by
    unfold fiberSize
    have he : (kernel.filter fun t => predictive d s == predictive d t) =
        kernel.filter fun t => decide (mClass (index t) = mClass (index s)) := by
      apply List.filter_congr
      intro t ht
      exact Bool.eq_iff_iff.mpr (by simpa only [beq_iff_eq,decide_eq_true_eq] using
        (eq_comm.trans (partition_from_reconstruction d ha hlen hq hr t s)))
    rw [he]
    cases s <;> decide
  rw [hf]
  exact m_fibers_nonempty_and_small (index s)

private theorem U_from_reconstruction (d : Inputs) (ha : T1Anchors d)
    (hlen : d.prototypes.length = 7) (hq : ObjecthoodRules.QuotientCheck (raw d))
    (hr : ObjecthoodRules.Reconstruction (raw d)) (k : J) (s : KState) :
    ObjecthoodRules.U (raw d) k.val s = (rawU d k (index s) : Rat) / 2 := by
  have hn : k.val < d.prototypes.length := by rw [hlen]; exact k.isLt
  have hd : (classOrder d).getD k.val (0,[]) = predictive d d.prototypes[k.val] := by
    simp [classOrder,List.getD,hn]
  unfold ObjecthoodRules.U
  rw [show (raw d).prototypes = d.prototypes from rfl,class_readout,
    List.getElem?_eq_getElem hn]
  simp only [rawU,stateAt_index,hd]
  by_cases he : predictive d s = predictive d d.prototypes[k.val]
  · simp only [he,if_true,generic_fiber_length]
    have hf : fiberSize d d.prototypes[k.val] = fiberSize d s := by unfold fiberSize; rw [he]
    rw [hf]
    rcases small_fibers d ha hlen hq hr s with h | h <;> rw [h] <;> decide +kernel
  · simp only [he,if_false]
    decide +kernel

/-- Converse reconstruction: the actual rational equations force the legacy
scaled-integer equations. No legacy acceptance predicate is assumed here. -/
theorem reconstructed_from_generic (d : Inputs) (hp : Protocol d)
    (hg : ObjecthoodRules.Gate (raw d)) : TablesReconstructed d := by
  rcases hp with ⟨ha,hv,hproto⟩
  have hlen : d.prototypes.length = 7 := by rw [hproto]; rfl
  have hq := hg.2.1
  have hr := hg.2.2.1
  have hc := columns d hlen hr
  have hu : ∀ k : J, ∀ j : I, rawU d k j = d.publishedU k j := by
    intro k j
    have h := hr.2.2 ⟨k.val,by simp only [raw,hlen]; exact k.isLt⟩ (stateAt j)
    rw [U_from_reconstruction d ha hlen hq hr] at h
    change (rawU d k (index (stateAt j)) : Rat) / 2 =
      (if h : k.val < 7 then (d.publishedU ⟨k.val,h⟩ (index (stateAt j)) : Rat) / 2 else 0) at h
    simp only [index_stateAt,dif_pos k.isLt] at h
    exact unscale (by decide) h
  refine ⟨by decide,hlen,?_,hq.1,?_,?_,?_,?_,?_⟩
  · rw [ha.2.2.1,hproto]
    decide
  · simp only [List.all_eq_true,decide_eq_true_eq]
    intro s hs
    exact hq.2.2.2.1 s
  · intro s t
    have h := hr.1 s t
    rw [P_readout] at h
    exact unscale (by decide) h
  · simp only [List.all_eq_true,beq_iff_eq]
    exact fun i hi k hk => hc i k
  · simp only [List.all_eq_true,beq_iff_eq]
    exact fun k hk j hj => hu k j
  · intro i j
    unfold sum7
    simp only [hc,hu]

/-- Checked specialization. Missing cells cannot pass the polymorphic decoder;
protocol checking only constrains raw parameters, references, and column order. -/
def Accept (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) : Prop :=
  ObjecthoodCells.Accept POS04ProfileRules.schema (POS04ObjecthoodCells.bindings tag) a ∧
    Protocol (clauseInputs a tag .c1)

theorem generic_c1_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    Accept a tag ↔ C1Accept a tag := by
  rw [c1_accept_iff_gate]
  constructor
  · rintro ⟨hc,hp⟩
    have hd := (POS04ObjecthoodCells.accept_decode_iff a tag).mp hc
    exact ⟨⟨hd.1,hp.2.1⟩,hp.1,reconstructed_from_generic _ hp hd.2.1⟩
  · intro hg
    have hd := clauseInputs a tag .c1
    exact ⟨(POS04ObjecthoodCells.accept_decode_iff a tag).mpr
      ⟨hg.1.1,assigned_accept _ hg.2.1 hg.2.2 hg.1.2⟩,
      hg.2.1,hg.1.2,prototypes_eq _ hg.2.1 hg.2.2⟩

theorem acceptance_locality {a b : CSTTT.POS04.Assigned.Assignment} {tag : Tag}
    (h : CSTTT.POS04.Assigned.Agrees (clauseScope tag .c1) a b) :
    Accept a tag ↔ Accept b tag := by
  rw [generic_c1_iff,generic_c1_iff]
  exact c1_acceptance_locality h

theorem missing_rejected (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c1) :
    ¬ Accept (CSTTT.POS04.Assigned.put a k none) tag := fun h =>
  (POS04ObjecthoodCells.missing_rejected a tag k hk).2 h.1

theorem changed_protocol_rejected (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : (clauseInputs a tag .c1).audit ≠ ⟨c1Tau,c1Epsilon,c1RetentionThreshold⟩) :
    ¬ Accept a tag := fun ha => h ha.2.1.1

theorem changed_column_order_rejected (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : (clauseInputs a tag .c1).prototypes ≠ c1ColumnRepresentatives) :
    ¬ Accept a tag := fun ha => h ha.2.2.2

theorem invalid_outcome_reference_rejected (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag)
    (h : ¬ RowsValid (clauseInputs a tag .c1)) : ¬ Accept a tag := fun ha => h ha.2.2.1

theorem canonical_accept (tag : Tag) : Accept canonical tag :=
  (generic_c1_iff _ _).mpr (canonical_c123 tag).1

theorem table_control (tag : Tag) :
    if tag = .target then ¬ Accept (negC1Table canonical) tag
    else Accept (negC1Table canonical) tag := by
  have h := (neg_c1_table_outcomes tag).1
  by_cases ht : tag = .target
  · simp only [ht,if_true] at h ⊢
    exact fun ha => h ((generic_c1_iff _ _).mp ha)
  · simp only [ht,if_false] at h ⊢
    exact (generic_c1_iff _ _).mpr h

theorem profile_control (tag : Tag) :
    if tag = .target then ¬ Accept (negC3Profile canonical) tag
    else Accept (negC3Profile canonical) tag := by
  have h := (neg_c3_profile_outcomes tag).1
  by_cases ht : tag = .target
  · simp only [ht,if_true] at h ⊢
    exact fun ha => h ((generic_c1_iff _ _).mp ha)
  · simp only [ht,if_false] at h ⊢
    exact (generic_c1_iff _ _).mpr h

theorem lower_control (tag : Tag) : Accept (negC2Split canonical) tag :=
  (generic_c1_iff _ _).mpr (neg_c2_split_outcomes tag).1

/-- All consumed primitive families retain the assigned C1 sensitivity guards.
Each edit is to actual data; equivalence applies also to incomplete assignments. -/
theorem field_guards (tag : Tag) :
    ¬ Accept (noRows canonical tag) tag ∧
    ¬ Accept (flatPositions canonical) tag ∧
    ¬ Accept (noHazards canonical) tag ∧
    ¬ Accept (stayPolicy canonical) tag ∧
    ¬ Accept (repeatedPrototypes canonical) tag ∧
    ¬ Accept (zeroP canonical) tag ∧
    ¬ Accept (zeroC canonical) tag ∧
    ¬ Accept (zeroU canonical) tag ∧
    ¬ Accept (wrongTau canonical) tag ∧
    ¬ Accept (wrongEpsilon canonical) tag ∧
    ¬ Accept (wrongRetention canonical) tag := by
  simp only [generic_c1_iff]
  exact ⟨c1_rows_guard tag,c1_positions_guard tag,c1_hazards_guard tag,
    c1_policy_guard tag,c1_prototypes_guard tag,c1_P_guard tag,c1_C_guard tag,
    c1_U_guard tag,c1_tau_guard tag,c1_epsilon_guard tag,c1_retention_guard tag⟩

end CSTTT.TargetTheory.GenericHandoff.POS04ObjecthoodProtocol
