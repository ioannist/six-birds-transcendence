import CSTTT.Targets.GenericHandoff.ProfileRules
import CSTTT.POS04.Assigned.Adapters
import CSTTT.POS04.Assigned.Guards

/-! Exact C2/C3 raw-algorithm specialization. Row validity and M reconstruction are checked by the generic raw rules.
C1 reconstruction is still a separate unfinished extraction. Equivalences quantify over every partial assignment. -/
namespace CSTTT.TargetTheory.GenericHandoff.POS04ProfileRules
open CSTTT.POS04 CSTTT.POS04.Assigned CSTTT.Objecthood.T1Audit

def schema : ProfileRules.Schema KState Action Ambient :=
  ⟨kernel,actions,(fun o => match o with | .inK s => some s | _ => none),
   (fun o => match o with | .p2w0 => 10 | .p5w1 => 11 | .inK _ => 0),
   List.range 12,(.p1w0,.p1w1),(6,7,7),1⟩

def raw (d : Inputs) : ProfileRules.Raw KState Action Ambient :=
  ⟨schema.states,schema.actions,d.rows,d.positions,d.hazards,schema.destination,
   schema.externalBlock,decide (d.lower = .stateLabel),schema.blocks,
   schema.split,schema.trajectory,schema.depth⟩

theorem predictive_eq (d : Inputs) : ProfileRules.predictive (raw d) = predictive d := rfl
theorem lower_eq (d : Inputs) : ProfileRules.lower (raw d) = lower d := by
  funext s
  cases h : d.lower <;> simp [ProfileRules.lower,raw,lower,h]
theorem seed_eq (d : Inputs) : ProfileRules.seed (raw d) = seed d := by
  funext s
  cases h : d.lower
  · simp [ProfileRules.seed,raw,schema,seed,h]
  · simp only [ProfileRules.seed,raw,schema,h,decide_true,if_true,seed]
    cases s <;> decide

theorem block_eq (d : Inputs) (c : KState → Nat) (o : Ambient) :
    ProfileRules.block (raw d) c o = blockOf c o := by cases o <;> rfl
theorem mass_eq (d : Inputs) (c : KState → Nat) (s : KState) (a : Action) (b : Nat) :
    ProfileRules.mass (raw d) c s a b = mass d c s a b := by
  simp only [ProfileRules.mass,mass,raw]
  congr 1
  funext n e
  change (if ProfileRules.block (raw d) c e.1 = b then n + e.2 else n) = _
  simp only [block_eq]
theorem signature_eq (d : Inputs) (c : KState → Nat) :
    ProfileRules.signature (raw d) c = signature d c := by
  funext s
  simp only [ProfileRules.signature,raw,schema,signature]
  congr 1
  apply List.map_congr_left
  intro a ha
  apply List.map_congr_left
  intro b hb
  exact mass_eq d c s a b

theorem step_eq (d : Inputs) (c : KState → Nat) : ProfileRules.step (raw d) c = step d c := by
  unfold ProfileRules.step
  rw [signature_eq]
  rfl
theorem first_eq (d : Inputs) : ProfileRules.first (raw d) = first d := by
  change ProfileRules.step (raw d) (ProfileRules.seed (raw d)) = _
  rw [seed_eq,step_eq]
  rfl
theorem second_eq (d : Inputs) : ProfileRules.second (raw d) = second d := by
  unfold ProfileRules.second
  rw [first_eq,step_eq]
  rfl
theorem promotion_iff (d : Inputs) : ProfileRules.Promotion (raw d) ↔ C2Rule d := by
  unfold ProfileRules.Promotion
  rw [lower_eq,predictive_eq]
  rfl
theorem profile_iff (d : Inputs) : ProfileRules.RecursiveProfile (raw d) ↔ C3Rule d := by
  unfold ProfileRules.RecursiveProfile ProfileRules.count
  rw [seed_eq,first_eq,second_eq,predictive_eq]
  rfl

def bindings (tag : Tag) : ProfileRules.Bindings Cell Value KState Action Ambient :=
  ⟨⟨.rows tag,id⟩,⟨.positions,id⟩,⟨.hazards,id⟩,
    ⟨.lower tag,fun (l : LowerRule) => decide (l = .stateLabel)⟩⟩

theorem decoded_complete_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ProfileRules.decoded schema (bindings tag) a = some (raw (inputs a tag)) ↔
      CSTTT.TargetTheory.GenericHandoff.Complete (bindings tag).scope a := by
  cases hr : a (.rows tag) <;> cases hp : a .positions <;>
    cases hh : a .hazards <;> cases hl : a (.lower tag) <;>
    simp [ProfileRules.decoded,bindings,CellView.read,raw,inputs,hr,hp,hh,hl,
      CSTTT.TargetTheory.GenericHandoff.Complete,ProfileRules.Bindings.scope]

theorem bindings_in_clause (tag : Tag) (c : Clause) (hc : c = .c2 ∨ c = .c3) :
    ∀ k ∈ (bindings tag).scope, k ∈ clauseScope tag c := by
  rcases hc with rfl | rfl <;> cases tag <;> decide

theorem decoded_clause (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (c : Clause)
    (hc : c = .c2 ∨ c = .c3) (h : CSTTT.POS04.Assigned.Complete (clauseScope tag c) a) :
    ProfileRules.decoded schema (bindings tag) (CSTTT.POS04.Assigned.decode (clauseScope tag c) a) =
      some (raw (clauseInputs a tag c)) := by
  apply (decoded_complete_iff _ _).mpr
  intro k hk
  have hm := bindings_in_clause tag c hc k hk
  simpa [CSTTT.POS04.Assigned.decode,hm] using h k hm

def clauseSchema : ProfileRules.ClauseSchema KState Action Ambient :=
  ⟨schema,ambientStates,4,fun s => mClass (index s)⟩
def clauseBindings (tag : Tag) : ProfileRules.ClauseBindings Cell Value KState Action Ambient :=
  ⟨bindings tag,⟨.publishedM,id⟩⟩

theorem clause_scope_eq (tag : Tag) (c : Clause) (hc : c = .c2 ∨ c = .c3) :
    (clauseBindings tag).scope = clauseScope tag c := by
  rcases hc with rfl | rfl <;> rfl

open Classical in
theorem clause_decode_eq (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (c : Clause)
    (hc : c = .c2 ∨ c = .c3) :
    ProfileRules.decodedClause clauseSchema (clauseBindings tag) a =
      if CSTTT.POS04.Assigned.Complete (clauseScope tag c) a then
        some (raw (inputs a tag),(inputs a tag).publishedM) else none := by
  rcases hc with rfl | rfl
  all_goals
    cases hr : a (.rows tag) <;> cases hp : a .positions <;>
      cases hh : a .hazards <;> cases hl : a (.lower tag) <;> cases hm : a .publishedM <;>
      simp [ProfileRules.decodedClause,ProfileRules.decoded,clauseSchema,clauseBindings,
        bindings,CellView.read,raw,inputs,hr,hp,hh,hl,hm,
        CSTTT.POS04.Assigned.Complete,clauseScope,commonScope]

theorem raw_scoped (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (c : Clause)
    (hc : c = .c2 ∨ c = .c3) : raw (inputs a tag) = raw (clauseInputs a tag c) := by
  rcases hc with rfl | rfl <;> cases tag <;> rfl
 theorem labels_scoped (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) (c : Clause)
    (hc : c = .c2 ∨ c = .c3) :
    (inputs a tag).publishedM = (clauseInputs a tag c).publishedM := by
  rcases hc with rfl | rfl <;> cases tag <;> rfl

theorem rows_valid_iff (d : Inputs) : ProfileRules.RowsValid clauseSchema (raw d) ↔ RowsValid d := Iff.rfl
theorem linked_iff (d : Inputs) :
    ProfileRules.Linked clauseSchema (raw d) d.publishedM ↔ MLinked d := Iff.rfl

theorem domain_checked : ProfileRules.DomainCheck clauseSchema := by
  refine ⟨by decide,by decide,by decide,?_,?_,?_⟩
  · intro s; cases s <;> decide
  · intro a; cases a <;> decide
  · intro o; cases o with
    | inK s => cases s <;> decide
    | p2w0 => decide
    | p5w1 => decide

theorem generic_c2_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ProfileRules.C2Accept clauseSchema (clauseBindings tag) a ↔ C2Accept a tag := by
  simp only [ProfileRules.C2Accept,domain_checked,true_and]
  rw [clause_decode_eq a tag .c2 (Or.inl rfl),
    raw_scoped a tag .c2 (Or.inl rfl),labels_scoped a tag .c2 (Or.inl rfl)]
  by_cases h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c2) a
  · simp only [if_pos h,Option.some.injEq,Prod.mk.injEq]
    constructor
    · rintro ⟨d,labels,⟨rfl,rfl⟩,hr,hm,hp⟩
      exact ⟨⟨⟨h,(rows_valid_iff _).mp hr⟩,(linked_iff _).mp hm⟩,(promotion_iff _).mp hp⟩
    · intro hp
      exact ⟨_,_,⟨rfl,rfl⟩,(rows_valid_iff _).mpr hp.1.1.2,
        (linked_iff _).mpr hp.1.2,(promotion_iff _).mpr hp.2⟩
  · simp [h,C2Accept,C2Gate,Ready]

theorem generic_c3_iff (a : CSTTT.POS04.Assigned.Assignment) (tag : Tag) :
    ProfileRules.C3Accept clauseSchema (clauseBindings tag) a ↔ C3Accept a tag := by
  simp only [ProfileRules.C3Accept,domain_checked,true_and]
  rw [clause_decode_eq a tag .c3 (Or.inr rfl),
    raw_scoped a tag .c3 (Or.inr rfl),labels_scoped a tag .c3 (Or.inr rfl)]
  by_cases h : CSTTT.POS04.Assigned.Complete (clauseScope tag .c3) a
  · simp only [if_pos h,Option.some.injEq,Prod.mk.injEq]
    constructor
    · rintro ⟨d,labels,⟨rfl,rfl⟩,hr,hm,hp⟩
      exact ⟨⟨⟨h,(rows_valid_iff _).mp hr⟩,(linked_iff _).mp hm⟩,(profile_iff _).mp hp⟩
    · intro hp
      exact ⟨_,_,⟨rfl,rfl⟩,(rows_valid_iff _).mpr hp.1.1.2,
        (linked_iff _).mpr hp.1.2,(profile_iff _).mpr hp.2⟩
  · simp [h,C3Accept,C3Gate,Ready]


theorem generic_canonical (tag : Tag) :
    ProfileRules.C2Accept clauseSchema (clauseBindings tag) canonical ∧
    ProfileRules.C3Accept clauseSchema (clauseBindings tag) canonical :=
  ⟨(generic_c2_iff _ _).mpr (canonical_c123 tag).2.1,
   (generic_c3_iff _ _).mpr (canonical_c123 tag).2.2⟩

theorem generic_table_control (tag : Tag) :
    ProfileRules.C2Accept clauseSchema (clauseBindings tag) (negC1Table canonical) ∧
    ProfileRules.C3Accept clauseSchema (clauseBindings tag) (negC1Table canonical) :=
  ⟨(generic_c2_iff _ _).mpr (neg_c1_table_outcomes tag).2.1,
   (generic_c3_iff _ _).mpr (neg_c1_table_outcomes tag).2.2⟩
theorem generic_exposed_control (tag : Tag) :
    ¬ ProfileRules.C2Accept clauseSchema (clauseBindings tag) (negC2Split canonical) ∧
    ¬ ProfileRules.C3Accept clauseSchema (clauseBindings tag) (negC2Split canonical) :=
  ⟨fun h => (neg_c2_split_outcomes tag).2.1 ((generic_c2_iff _ _).mp h),
   fun h => (neg_c2_split_outcomes tag).2.2 ((generic_c3_iff _ _).mp h)⟩
theorem generic_profile_control (tag : Tag) :
    ProfileRules.C2Accept clauseSchema (clauseBindings tag) (negC3Profile canonical) ∧
    ProfileRules.C3Accept clauseSchema (clauseBindings tag) (negC3Profile canonical) :=
  ⟨(generic_c2_iff _ _).mpr (neg_c3_profile_outcomes tag).2.1,
   (generic_c3_iff _ _).mpr (neg_c3_profile_outcomes tag).2.2⟩

theorem rows_guard (tag : Tag) :
    ¬ ProfileRules.C2Accept clauseSchema (clauseBindings tag) (noRows canonical tag) ∧
    ¬ ProfileRules.C3Accept clauseSchema (clauseBindings tag) (noRows canonical tag) :=
  ⟨fun h => c2_rows_guard tag ((generic_c2_iff _ _).mp h),
   fun h => c3_rows_guard tag ((generic_c3_iff _ _).mp h)⟩
theorem positions_guard (tag : Tag) :
    ¬ ProfileRules.C2Accept clauseSchema (clauseBindings tag) (flatPositions canonical) ∧
    ¬ ProfileRules.C3Accept clauseSchema (clauseBindings tag) (flatPositions canonical) :=
  ⟨fun h => c2_positions_guard tag ((generic_c2_iff _ _).mp h),
   fun h => c3_positions_guard tag ((generic_c3_iff _ _).mp h)⟩
theorem hazards_guard (tag : Tag) :
    ¬ ProfileRules.C2Accept clauseSchema (clauseBindings tag) (noHazards canonical) ∧
    ¬ ProfileRules.C3Accept clauseSchema (clauseBindings tag) (noHazards canonical) :=
  ⟨fun h => c2_hazards_guard tag ((generic_c2_iff _ _).mp h),
   fun h => c3_hazards_guard tag ((generic_c3_iff _ _).mp h)⟩
theorem classes_guard (tag : Tag) :
    ¬ ProfileRules.C2Accept clauseSchema (clauseBindings tag) (flatM canonical) ∧
    ¬ ProfileRules.C3Accept clauseSchema (clauseBindings tag) (flatM canonical) :=
  ⟨fun h => c2_M_guard tag ((generic_c2_iff _ _).mp h),
   fun h => c3_M_guard tag ((generic_c3_iff _ _).mp h)⟩
theorem canonical_genuine_stabilization (tag : Tag) :
    ProfileRules.StableProfile (raw (clauseInputs canonical tag .c3)) := by
  refine ⟨(profile_iff _).mpr (canonical_c123 tag).2.2.2,?_,?_,?_⟩
  · funext s; cases tag <;> cases s <;> decide
  · apply (ProfileRules.block_coverage_iff _ _).mp
    cases tag <;> decide +kernel
  · apply (ProfileRules.block_coverage_iff _ _).mp
    cases tag <;> decide +kernel

end CSTTT.TargetTheory.GenericHandoff.POS04ProfileRules
