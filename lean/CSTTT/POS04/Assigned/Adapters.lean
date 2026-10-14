import CSTTT.POS04.Assigned.C123

namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit

/-- Replace precisely one raw action row; no other cell or row is touched. -/
def editRow (a : Assignment) (tag : Tag) (s : KState) (act : Action)
    (row : List (Ambient × Nat)) : Assignment :=
  put a (.rows tag) ((a (.rows tag)).map fun rows =>
    fun t b => if t = s ∧ b = act then row else rows t b)

/-- Frozen POS-04 interventions, JSON `NEG-C1-TABLE`, `NEG-C3-PROFILE`,
`NEG-C2-SPLIT`. These are raw assignment transformations, not verdict selectors. -/
def negC1Table (a : Assignment) : Assignment :=
  editRow a .target .p2w1 .stay [(.inK .p1w0,2),(.inK .p1w1,2)]
def negC3Profile (a : Assignment) : Assignment :=
  editRow a .target .p1w0 .cw [(.inK .p5w0,4)]
def negC2Split (a : Assignment) : Assignment :=
  put (put a (.lower .source) (some .stateLabel)) (.lower .target) (some .stateLabel)

/-- Compatibility adapter: variant names apply the declared raw edits. The
acceptance algorithms never see the names. -/
def controls (v : C1TableVariant) (p : ProfileVariant) (l : LowerRule) : Assignment :=
  let a := match p with | .positive => canonical | .negC3Profile => negC3Profile canonical
  let a := match v with | .positive => a | .negTable => negC1Table a
  match l with | .position => a | .stateLabel => negC2Split a

def legacyInputs (v : C1TableVariant) (p : ProfileVariant) (l : LowerRule)
    (tag : Tag) : Inputs :=
  ⟨c1ActionRow v p tag,publicPosition,isLethalHazard,l,canonicalAction,
   c1ColumnRepresentatives,pNum,cIndicator,uPrototypeNum,
   fun s => mClass (index s),⟨c1Tau,c1Epsilon,c1RetentionThreshold⟩⟩

/-- Exact raw-table adapter, including unchanged cells. -/
theorem controls_rows (v : C1TableVariant) (p : ProfileVariant) (l : LowerRule)
    (tag : Tag) : controls v p l (.rows tag) = some (c1ActionRow v p tag) := by
  cases v <;> cases p <;> cases l <;> cases tag <;>
    apply congrArg some <;> funext s a <;> cases s <;> cases a <;> rfl

theorem controls_complete (v : C1TableVariant) (p : ProfileVariant)
    (l : LowerRule) (scope : List Cell) : Complete scope (controls v p l) := by
  intro k hk
  clear hk
  cases v <;> cases p <;> cases l <;> cases k <;> try rfl
  all_goals rename_i tag; cases tag <;> rfl

theorem decoded_c1 (v : C1TableVariant) (p : ProfileVariant)
    (l : LowerRule) (tag : Tag) :
    clauseInputs (controls v p l) tag .c1 = legacyInputs v p .position tag := by
  unfold clauseInputs inputs
  rw [show decode (clauseScope tag .c1) (controls v p l) (.rows tag) =
    some (c1ActionRow v p tag) by
      simp only [decode]; rw [if_pos (shared_rows tag).1]; exact controls_rows v p l tag]
  cases v <;> cases p <;> cases l <;> cases tag <;> rfl

theorem decoded_c23 (p : ProfileVariant) (l : LowerRule) (tag : Tag) :
    clauseInputs (controls .positive p l) tag .c2 = legacyInputs .positive p l tag ∧
    clauseInputs (controls .positive p l) tag .c3 = legacyInputs .positive p l tag := by
  have h2 : clauseInputs (controls .positive p l) tag .c2 =
      legacyInputs .positive p l tag := by
    unfold clauseInputs inputs
    rw [show decode (clauseScope tag .c2) (controls .positive p l) (.rows tag) =
      some (c1ActionRow .positive p tag) by
        simp only [decode]; rw [if_pos (shared_rows tag).2.1]; exact controls_rows _ _ _ _]
    cases p <;> cases l <;> cases tag <;> rfl
  exact ⟨h2,h2⟩

theorem legacy_anchors (v : C1TableVariant) (p : ProfileVariant)
    (l : LowerRule) (tag : Tag) : T1Anchors (legacyInputs v p l tag) :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem legacy_M_link (v : C1TableVariant) (p : ProfileVariant)
    (l : LowerRule) (tag : Tag) : MLinked (legacyInputs v p l tag) := by
  refine ⟨rfl,?_⟩
  intro s t
  cases v <;> cases p <;> cases l <;> cases tag <;> cases s <;> cases t <;> decide

theorem legacy_tables_equivalence (v : C1TableVariant) (p : ProfileVariant)
    (tag : Tag) : TablesReconstructed (legacyInputs v p .position tag) ↔
    C1TablesReconstructed v p tag := by
  simp only [TablesReconstructed,C1TablesReconstructed,legacyInputs,
    classOrder,predictive,rawC,rawU,fiberSize,c1RawM,c1RawClassOrder,
    c1RawC,c1RawUNum,c1RawClassSize,C1ColumnOrderMatches,taggedPNum,
    declared_cu_is_t1]
  rfl

theorem legacy_rows_valid (v : C1TableVariant) (p : ProfileVariant)
    (l : LowerRule) (tag : Tag) : RowsValid (legacyInputs v p l tag) := by
  unfold RowsValid
  cases v <;> cases p <;> cases l <;> cases tag <;> decide

theorem controls_ready_c1 (v : C1TableVariant) (p : ProfileVariant)
    (l : LowerRule) (tag : Tag) : Ready (controls v p l) tag .c1 := by
  refine ⟨controls_complete _ _ _ _,?_⟩
  rw [decoded_c1]
  exact legacy_rows_valid _ _ _ _

theorem controls_ready_c23 (p : ProfileVariant) (l : LowerRule) (tag : Tag) :
    Ready (controls .positive p l) tag .c2 ∧ Ready (controls .positive p l) tag .c3 := by
  have h2 : Ready (controls .positive p l) tag .c2 := by
    refine ⟨controls_complete _ _ _ _,?_⟩
    rw [(decoded_c23 p l tag).1]
    exact legacy_rows_valid _ _ _ _
  exact ⟨h2,h2⟩

/-- Every named adapter has exactly the old C1 outcome, including universal
uniqueness when accepted. The proof transports the audit, never decides it. -/
theorem c1_controls_equivalence (v : C1TableVariant) (p : ProfileVariant)
    (l : LowerRule) (tag : Tag) :
    C1Accept (controls v p l) tag ↔ C1FactorPass tag v p := by
  rw [c1_accept_iff_gate]
  unfold C1Gate
  rw [decoded_c1]
  have hcomplete := controls_ready_c1 v p l tag
  have hanchor := legacy_anchors v p .position tag
  rw [and_iff_right hcomplete, and_iff_right hanchor, legacy_tables_equivalence]
  constructor
  · intro hr
    have ha : C1FactorPass tag := c1_factor_pass tag
    exact ⟨hr,ha.2⟩
  · exact And.left

theorem c1_canonical_equivalence (tag : Tag) :
    C1Accept canonical tag ↔ C1FactorPass tag :=
  c1_controls_equivalence .positive .positive .position tag

theorem legacy_seed (p : ProfileVariant) (l : LowerRule) (tag : Tag) :
    seed (legacyInputs .positive p l tag) = profile0 l := by
  cases l <;> rfl

theorem legacy_first (p : ProfileVariant) (l : LowerRule) (tag : Tag) :
    first (legacyInputs .positive p l tag) = profile1 p l tag := by
  unfold first
  rw [legacy_seed]
  rfl

theorem legacy_second (p : ProfileVariant) (l : LowerRule) (tag : Tag) :
    second (legacyInputs .positive p l tag) = profile2 p l tag := by
  unfold second
  rw [legacy_first]
  rfl

theorem c3_rule_equivalence (p : ProfileVariant) (l : LowerRule) (tag : Tag) :
    C3Rule (legacyInputs .positive p l tag) ↔ C3Pass p l tag := by
  unfold C3Rule
  rw [legacy_seed,legacy_first,legacy_second]
  rfl

theorem c3_controls_equivalence (p : ProfileVariant) (l : LowerRule) (tag : Tag) :
    C3Accept (controls .positive p l) tag ↔ C3Pass p l tag := by
  unfold C3Accept C3Gate
  rw [(decoded_c23 p l tag).2]
  have hc := (controls_ready_c23 p l tag).2
  have hm := legacy_M_link .positive p l tag
  rw [and_iff_right (And.intro hc hm)]
  exact c3_rule_equivalence p l tag

theorem c2_rule_equivalence (p : ProfileVariant) (l : LowerRule) (tag : Tag) :
    C2Rule (legacyInputs .positive p l tag) ↔ C2Pass l tag := by
  unfold C2Rule C2Pass C2Defect
  cases p <;> cases l <;> cases tag <;> decide

theorem c2_controls_equivalence (p : ProfileVariant) (l : LowerRule) (tag : Tag) :
    C2Accept (controls .positive p l) tag ↔ C2Pass l tag := by
  unfold C2Accept C2Gate
  rw [(decoded_c23 p l tag).1]
  have hc := (controls_ready_c23 p l tag).1
  have hm := legacy_M_link .positive p l tag
  rw [and_iff_right (And.intro hc hm)]
  exact c2_rule_equivalence p l tag

theorem c2_canonical_equivalence (tag : Tag) :
    C2Accept canonical tag ↔ C2Pass (positiveLowerRule tag) tag := by
  have h := c2_controls_equivalence .positive .position tag
  cases tag <;> exact h

theorem c3_canonical_equivalence (tag : Tag) :
    C3Accept canonical tag ↔ C3Pass .positive (positiveLowerRule tag) tag := by
  have h := c3_controls_equivalence .positive .position tag
  cases tag <;> exact h

theorem canonical_c123 (tag : Tag) :
    C1Accept canonical tag ∧ C2Accept canonical tag ∧ C3Accept canonical tag :=
  ⟨(c1_canonical_equivalence tag).mpr (c1_factor_pass tag),
   (c2_canonical_equivalence tag).mpr (c2_split_each_tag tag),
   (c3_canonical_equivalence tag).mpr (c3_each_tag tag)⟩

/-- Computed M from assigned action support/hazards is linked pairwise to
T1's imported partition on the canonical assignment. -/
theorem assigned_M_iff_imported (tag : Tag) (s t : KState) :
    (predictive (clauseInputs canonical tag .c3) s =
      predictive (clauseInputs canonical tag .c3) t) ↔
    taggedMClass tag s = taggedMClass tag t := by
  change (predictive (clauseInputs (controls .positive .positive .position) tag .c3) s =
    predictive (clauseInputs (controls .positive .positive .position) tag .c3) t) ↔ _
  rw [(decoded_c23 .positive .position tag).2]
  exact rawM_iff_imported_M tag s t

theorem decoded_c23_for (v : C1TableVariant) (p : ProfileVariant)
    (l : LowerRule) (tag : Tag) :
    clauseInputs (controls v p l) tag .c2 = legacyInputs v p l tag ∧
    clauseInputs (controls v p l) tag .c3 = legacyInputs v p l tag := by
  have h2 : clauseInputs (controls v p l) tag .c2 = legacyInputs v p l tag := by
    unfold clauseInputs inputs
    rw [show decode (clauseScope tag .c2) (controls v p l) (.rows tag) =
      some (c1ActionRow v p tag) by
        simp only [decode]; rw [if_pos (shared_rows tag).2.1]; exact controls_rows _ _ _ _]
    cases v <;> cases p <;> cases l <;> cases tag <;> rfl
  exact ⟨h2,h2⟩

theorem legacy_predictive_unchanged (v : C1TableVariant) (p : ProfileVariant)
    (l : LowerRule) (tag : Tag) : predictive (legacyInputs v p l tag) = rawM tag := by
  funext s
  cases v <;> cases p <;> cases l <;> cases tag <;> cases s <;> decide

/-- All three declared edits use one raw assignment, so their cross-clause
outcomes are checked rather than selected independently. -/
theorem neg_c1_table_outcomes (tag : Tag) :
    (if tag = .target then ¬ C1Accept (negC1Table canonical) tag
      else C1Accept (negC1Table canonical) tag) ∧
    C2Accept (negC1Table canonical) tag ∧ C3Accept (negC1Table canonical) tag := by
  have h1 : (if tag = .target then ¬ C1Accept (controls .negTable .positive .position) tag
      else C1Accept (controls .negTable .positive .position) tag) := by
    cases tag
    · exact (c1_controls_equivalence .negTable .positive .position .source).mpr
        (c1_factor_pass .source)
    · intro h
      exact neg_c1_table_breaks_P ((c1_controls_equivalence _ _ _ _).mp h).1
  have hm := legacy_M_link .negTable .positive .position tag
  have hd := decoded_c23_for .negTable .positive .position tag
  have h2 : C2Accept (controls .negTable .positive .position) tag := by
    refine ⟨⟨⟨controls_complete _ _ _ _,?_⟩,?_⟩,?_⟩
    · rw [hd.1]; exact legacy_rows_valid _ _ _ _
    · rw [hd.1]; exact hm
    · rw [hd.1]
      cases tag <;> unfold C2Rule <;> decide
  have h3 : C3Accept (controls .negTable .positive .position) tag := by
    refine ⟨⟨⟨controls_complete _ _ _ _,?_⟩,?_⟩,?_⟩
    · rw [hd.2]; exact legacy_rows_valid _ _ _ _
    · rw [hd.2]; exact hm
    · rw [hd.2]
      unfold C3Rule samePartition
      refine ⟨?_,?_,?_,?_,?_⟩
      · cases tag <;> decide
      · cases tag <;> decide
      · cases tag <;> decide
      · intro s t; cases tag <;> cases s <;> cases t <;> decide
      · intro s t; cases tag <;> cases s <;> cases t <;> decide
  exact ⟨h1,h2,h3⟩

theorem neg_c2_split_outcomes (tag : Tag) :
    C1Accept (negC2Split canonical) tag ∧
    ¬ C2Accept (negC2Split canonical) tag ∧
    ¬ C3Accept (negC2Split canonical) tag := by
  refine ⟨(c1_controls_equivalence .positive .positive .stateLabel tag).mpr
    (c1_factor_pass tag),?_,?_⟩
  · intro h
    have hd := (c2_controls_equivalence .positive .stateLabel tag).mp h
    exact neg_c2_split_no_defect tag ⟨.p1w0,.p1w1,hd⟩
  · intro h
    exact c3_state_label_lower_fails tag
      ((c3_controls_equivalence .positive .stateLabel tag).mp h)

/-- The failed C3 prediction stays failed: C3 and C2 pass, while target C1
rejects the changed canonical P row. Source is unchanged. -/
theorem neg_c3_profile_outcomes (tag : Tag) :
    (if tag = .target then ¬ C1Accept (negC3Profile canonical) tag
      else C1Accept (negC3Profile canonical) tag) ∧
    C2Accept (negC3Profile canonical) tag ∧ C3Accept (negC3Profile canonical) tag := by
  refine ⟨?_,?_,?_⟩
  · cases tag
    · exact (c1_controls_equivalence .positive .negC3Profile .position .source).mpr
        (c1_factor_pass .source)
    · intro h
      exact neg_c3_profile_breaks_c1_P ((c1_controls_equivalence .positive .negC3Profile .position .target).mp h).1
  · apply (c2_controls_equivalence .negC3Profile .position tag).mpr
    exact c2_split_each_tag tag
  · apply (c3_controls_equivalence .negC3Profile .position tag).mpr
    cases tag
    · exact c3_each_tag .source
    · exact neg_c3_profile_still_holds

theorem editRow_other_cell (a : Assignment) (tag : Tag) (s : KState)
    (act : Action) (row : List (Ambient × Nat)) (k : Cell) (hk : k ≠ .rows tag) :
    editRow a tag s act row k = a k := by
  exact put_other a (.rows tag) k _ hk

theorem editRow_other_row (a : Assignment) (tag : Tag) (s t : KState)
    (act b : Action) (row : List (Ambient × Nat)) (h : ¬ (t = s ∧ b = act)) :
    ((editRow a tag s act row (.rows tag)).map fun rows => rows t b) =
      ((a (.rows tag)).map fun rows => rows t b) := by
  simp [editRow,Option.map_map,Function.comp_def,h]

end CSTTT.POS04.Assigned
