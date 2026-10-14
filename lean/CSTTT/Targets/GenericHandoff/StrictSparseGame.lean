import CSTTT.Targets.GenericHandoff.GameInvariantCompleteness

/-! TTH-06, (b) format-qualified autonomy (manager resolution of 068899e).
Every LISTED weight of the selected response must be positive. This is a
representation-sensitive legality condition, not a stronger stochastic safety
claim. Neither duplicate freedom nor ordering is imposed. Plays and successor
safety still quantify over exactly the positive support. The committed
`StrategyGame.GameReadout` is retained as the support-only readout. -/
namespace CSTTT.TargetTheory.GenericHandoff.StrictSparseGame
open StrategyGame
variable {Run D A O : Type}

def StrictSparse (row : List (O × Rat)) : Prop := ∀ e ∈ row, 0 < e.2

def Legal (rows : Rows Run D A O) (legal : Run → D → A → Prop)
    (r : Run) (d : D) (a : A) : Prop := legal r d a ∧ StrictSparse (rows r d a)

abbrev SupportOnlyReadout := @StrategyGame.GameReadout

def Readout (rows : Rows Run D A O) (update : Updater Run D A O)
    (entries : Run → Prop) (withdrawal : Prop) (package resources : Run → Prop)
    (legal : Run → D → A → Prop) (step : Run → D → A → O → Prop) : Prop :=
  GameReadout rows update entries withdrawal package resources (Legal rows legal) step

abbrev Certificate (rows : Rows Run D A O) (update : Updater Run D A O)
    (entries : Run → Prop) (withdrawal : Prop) (package resources : Run → Prop)
    (legal : Run → D → A → Prop) (step : Run → D → A → O → Prop) :=
  InvariantCertificate rows update entries withdrawal package resources (Legal rows legal) step

/-- Selected responses alone are checked, throughout the actual strategy plays. -/
theorem selected_sparse {rows : Rows Run D A O} {update : Updater Run D A O}
    {entries : Run → Prop} {withdrawal : Prop} {package resources : Run → Prop}
    {legal : Run → D → A → Prop} {step : Run → D → A → O → Prop}
    (h : Readout rows update entries withdrawal package resources legal step) :
    ∃ strategy, ∀ entry, entries entry → ∀ r past,
      Play rows update strategy entry (r::past) → ∀ d,
        StrictSparse (rows r d (strategy (r::past) d)) := by
  obtain ⟨_,_,strategy,hs⟩ := h
  exact ⟨strategy,fun entry he r past hp d => ((hs entry he r past hp).2.2 d).1.2⟩

theorem implies_support_only {rows : Rows Run D A O} {update : Updater Run D A O}
    {entries : Run → Prop} {withdrawal : Prop} {package resources : Run → Prop}
    {legal : Run → D → A → Prop} {step : Run → D → A → O → Prop}
    (h : Readout rows update entries withdrawal package resources legal step) :
    SupportOnlyReadout rows update entries withdrawal package resources legal step := by
  obtain ⟨hw,he,strategy,hs⟩ := h
  refine ⟨hw,he,strategy,?_⟩
  intro entry hin r past hp
  have hh := hs entry hin r past hp
  exact ⟨hh.1,hh.2.1,fun d => ⟨(hh.2.2 d).1.1,(hh.2.2 d).2⟩⟩

theorem soundness {rows : Rows Run D A O} {update : Updater Run D A O}
    {entries : Run → Prop} {withdrawal : Prop} {package resources : Run → Prop}
    {legal : Run → D → A → Prop} {step : Run → D → A → O → Prop}
    (cert : Certificate rows update entries withdrawal package resources legal step) :
    Readout rows update entries withdrawal package resources legal step :=
  invariant_game_soundness _ _ _ _ _ _ _ _ cert

theorem invariant_iff {rows : Rows Run D A O} {update : Updater Run D A O}
    {entries : Run → Prop} {withdrawal : Prop} {package resources : Run → Prop}
    {legal : Run → D → A → Prop} {step : Run → D → A → O → Prop} :
    Readout rows update entries withdrawal package resources legal step ↔
      Nonempty (Certificate rows update entries withdrawal package resources legal step) :=
  game_iff_run_invariant

theorem zero_entry_rejected (row : List (O × Rat)) (o : O) (h : (o,0) ∈ row) :
    ¬ StrictSparse row := fun hs => Rat.lt_irrefl (hs (o,0) h)

theorem empty_not_normalized (r : Run) (d : D) (a : A) :
    ¬ Normalized (fun (_ : Run) (_ : D) (_ : A) => ([] : List (O × Rat))) r d a := by
  rintro ⟨_,_,o,w,hw,_⟩
  exact List.not_mem_nil hw

theorem append_iff (xs ys : List (O × Rat)) :
    StrictSparse (xs ++ ys) ↔ StrictSparse xs ∧ StrictSparse ys := by
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_append_left _ he),
      fun e he => h e (List.mem_append_right _ he)⟩
  · rintro ⟨hx,hy⟩ e he
    exact (List.mem_append.mp he).elim (hx e) (hy e)

theorem duplicate_positive (xs : List (O × Rat)) (e : O × Rat) (he : 0 < e.2) :
    StrictSparse (xs ++ [e,e]) ↔ StrictSparse xs := by
  rw [append_iff]
  simp only [StrictSparse,List.mem_cons,List.not_mem_nil,or_false]
  constructor
  · exact And.left
  · intro h
    exact ⟨h,fun x hx => by rcases hx with rfl | rfl <;> exact he⟩

theorem perm_iff {xs ys : List (O × Rat)} (h : xs.Perm ys) :
    StrictSparse xs ↔ StrictSparse ys := by
  unfold StrictSparse
  simp only [h.mem_iff]

/-- No selected action can use a null entry, even when the outcome is inside
an otherwise safe invariant. The support-only semantics is NOT changed. -/
theorem null_at_entry_no_game {rows : Rows Run D A O} {update : Updater Run D A O}
    {entries : Run → Prop} {withdrawal : Prop} {package resources : Run → Prop}
    {legal : Run → D → A → Prop} {step : Run → D → A → O → Prop}
    (entry : Run) (he : entries entry) (d : D)
    (null : ∀ a, ∃ o, (o,0) ∈ rows entry d a) :
    ¬ Readout rows update entries withdrawal package resources legal step := by
  rintro ⟨_,_,strategy,hs⟩
  obtain ⟨o,ho⟩ := null (strategy [entry] d)
  exact zero_entry_rejected _ o ho (((hs entry he entry [] Play.initial).2.2 d).1.2)

end CSTTT.TargetTheory.GenericHandoff.StrictSparseGame
