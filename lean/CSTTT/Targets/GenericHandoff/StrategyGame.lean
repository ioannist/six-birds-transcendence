import Lean

/-! Hybrid autonomy: semantic strategy/induction engine.

This is the interpretation-parametric game kernel, not a RawHandoff assembler.
Its relations must be instantiated by the defined raw package, withdrawal,
resource, ownership and ledger interpreters. They are not independent candidate
arguments at that boundary. The rows and updater here can depend on the entire
unbounded run context. No finite-context or Markov projection is assumed.

The auxiliary invariant is a proof witness. It stores neither an autonomy
verdict nor a proof of the game readout. Soundness constructs a causal strategy
and inducts on its plays, checking every positive-support successor of the
selected action, without quantifying over unselected actions. -/
namespace CSTTT.TargetTheory.GenericHandoff.StrategyGame

variable {Run Disturbance Action Outcome : Type}

abbrev Rows (Run Disturbance Action Outcome : Type) :=
  Run → Disturbance → Action → List (Outcome × Rat)
abbrev Updater (Run Disturbance Action Outcome : Type) :=
  Run → Disturbance → Action → Outcome → Run
abbrev Strategy (Run Disturbance Action : Type) := List Run → Disturbance → Action

def PositiveSupport (rows : Rows Run Disturbance Action Outcome)
    (r : Run) (d : Disturbance) (a : Action) (o : Outcome) : Prop :=
  ∃ weight, (o,weight) ∈ rows r d a ∧ 0 < weight

def Normalized (rows : Rows Run Disturbance Action Outcome)
    (r : Run) (d : Disturbance) (a : Action) : Prop :=
  (∀ e ∈ rows r d a, 0 ≤ e.2) ∧
  ((rows r d a).map Prod.snd).sum = 1 ∧
  ∃ o, PositiveSupport rows r d a o

/-- Histories contain the current run first. Actions see the past history and
current disturbance, never a future disturbance or the chosen successor. -/
inductive Play (rows : Rows Run Disturbance Action Outcome)
    (update : Updater Run Disturbance Action Outcome)
    (strategy : Strategy Run Disturbance Action) (entry : Run) : List Run → Prop where
  | initial : Play rows update strategy entry [entry]
  | step {r : Run} {past : List Run}
      (earlier : Play rows update strategy entry (r :: past))
      (d : Disturbance) (o : Outcome)
      (supported : PositiveSupport rows r d (strategy (r :: past) d) o) :
      Play rows update strategy entry
        (update r d (strategy (r :: past) d) o :: r :: past)

/-- These are component semantics, NOT certificate fields. At the raw boundary
all five predicates are defined by the shared assignment and actual execution.
`responseLegal` includes ownership, resources and raw withdrawal availability;
`transitionLaw` includes actual-update solvency and advancement. -/
def GameReadout (rows : Rows Run Disturbance Action Outcome)
    (update : Updater Run Disturbance Action Outcome)
    (entries : Run → Prop) (withdrawal : Prop)
    (package resourceClosed : Run → Prop)
    (responseLegal : Run → Disturbance → Action → Prop)
    (transitionLaw : Run → Disturbance → Action → Outcome → Prop) : Prop :=
  withdrawal ∧ (∃ r, entries r) ∧
  ∃ strategy : Strategy Run Disturbance Action,
    ∀ entry, entries entry → ∀ r past,
      Play rows update strategy entry (r :: past) →
      package r ∧ resourceClosed r ∧
      ∀ d, responseLegal r d (strategy (r :: past) d) ∧
        Normalized rows r d (strategy (r :: past) d) ∧
        ∀ o, PositiveSupport rows r d (strategy (r :: past) d) o →
          transitionLaw r d (strategy (r :: past) d) o

/-- Proof-bearing validity. Each field is evidence on the component semantics.
The invariant is auxiliary; dynamics, entries and readouts are not fields. -/
structure InvariantCertificate
    (rows : Rows Run Disturbance Action Outcome)
    (update : Updater Run Disturbance Action Outcome)
    (entries : Run → Prop) (withdrawal : Prop)
    (package resourceClosed : Run → Prop)
    (responseLegal : Run → Disturbance → Action → Prop)
    (transitionLaw : Run → Disturbance → Action → Outcome → Prop) where
  inside : Run → Prop
  withdrawn : withdrawal
  entriesNonempty : ∃ r, entries r
  entriesInside : ∀ r, entries r → inside r
  packageInside : ∀ r, inside r → package r
  resourcesInside : ∀ r, inside r → resourceClosed r
  response : ∀ r, inside r → ∀ d,
    ∃ a, responseLegal r d a ∧ Normalized rows r d a ∧
      ∀ o, PositiveSupport rows r d a o →
        inside (update r d a o) ∧ transitionLaw r d a o

section Soundness
variable (rows : Rows Run Disturbance Action Outcome)
    (update : Updater Run Disturbance Action Outcome)
    (entries : Run → Prop) (withdrawal : Prop)
    (package resourceClosed : Run → Prop)
    (responseLegal : Run → Disturbance → Action → Prop)
    (transitionLaw : Run → Disturbance → Action → Outcome → Prop)
    (cert : InvariantCertificate rows update entries withdrawal package resourceClosed
      responseLegal transitionLaw)

/-- A total proof-level selector on invariant runs. Outside the invariant it
uses an action already obtained from a genuine entry, not a semantic default. -/
noncomputable def selected : Run → Disturbance → Action := by
  classical
  let entry := Classical.choose cert.entriesNonempty
  have entryInside := cert.entriesInside entry (Classical.choose_spec cert.entriesNonempty)
  exact fun r d => if h : cert.inside r then Classical.choose (cert.response r h d)
    else Classical.choose (cert.response entry entryInside d)

theorem selected_spec (r : Run) (hr : cert.inside r) (d : Disturbance) :
    responseLegal r d (selected rows update entries withdrawal package resourceClosed
      responseLegal transitionLaw cert r d) ∧
    Normalized rows r d (selected rows update entries withdrawal package resourceClosed
      responseLegal transitionLaw cert r d) ∧
    ∀ o, PositiveSupport rows r d (selected rows update entries withdrawal package resourceClosed
      responseLegal transitionLaw cert r d) o →
      cert.inside (update r d (selected rows update entries withdrawal package resourceClosed
        responseLegal transitionLaw cert r d) o) ∧
      transitionLaw r d (selected rows update entries withdrawal package resourceClosed
        responseLegal transitionLaw cert r d) o := by
  classical
  simpa only [selected,dif_pos hr] using Classical.choose_spec (cert.response r hr d)

/-- Markov in the full run context, hence causal as a history strategy.
No finite-factor Markov claim is made. -/
noncomputable def causalStrategy : Strategy Run Disturbance Action :=
  fun history d => match history with
    | r :: _ => selected rows update entries withdrawal package resourceClosed
        responseLegal transitionLaw cert r d
    | [] => selected rows update entries withdrawal package resourceClosed
        responseLegal transitionLaw cert (Classical.choose cert.entriesNonempty) d

theorem every_play_inside {entry : Run} (he : entries entry)
    {history : List Run}
    (hp : Play rows update (causalStrategy rows update entries withdrawal package resourceClosed
      responseLegal transitionLaw cert) entry history) :
    ∀ r past, history = r :: past → cert.inside r := by
  induction hp with
  | initial =>
    intro r past h
    cases h
    exact cert.entriesInside entry he
  | @step r past earlier d o supported ih =>
    intro next rest h
    cases h
    have hr := ih r past rfl
    exact ((selected_spec rows update entries withdrawal package resourceClosed
      responseLegal transitionLaw cert r hr d).2.2 o supported).1

include cert in
/-- Game soundness is derived by play induction, not read from the witness. -/
theorem invariant_game_soundness :
    GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw := by
  refine ⟨cert.withdrawn,cert.entriesNonempty,
    causalStrategy rows update entries withdrawal package resourceClosed responseLegal transitionLaw cert,?_⟩
  intro entry he r past hp
  have hr := every_play_inside rows update entries withdrawal package resourceClosed
    responseLegal transitionLaw cert he hp r past rfl
  refine ⟨cert.packageInside r hr,cert.resourcesInside r hr,?_⟩
  intro d
  have hs := selected_spec rows update entries withdrawal package resourceClosed
    responseLegal transitionLaw cert r hr d
  exact ⟨hs.1,hs.2.1,fun o ho => (hs.2.2 o ho).2⟩
end Soundness

/-- Full autonomy entails the package at every genuine entry. The eventual
F adapter defines `package` to include the same coherent arrival P, so this
lemma derives AF→P rather than assuming a stored implication. -/
theorem game_entry_package
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    (h : GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw)
    (entry : Run) (he : entries entry) : package entry := by
  obtain ⟨_,_,strategy,hs⟩ := h
  exact (hs entry he entry [] Play.initial).1

/-- Execution records only actions chosen by the causal strategy. All support
branches are permitted; existence is separate from their universal safety. -/
inductive WordExecution (rows : Rows Run Disturbance Action Outcome)
    (update : Updater Run Disturbance Action Outcome)
    (strategy : Strategy Run Disturbance Action) :
    List Run → List Disturbance → List Run → Prop where
  | nil (history : List Run) : WordExecution rows update strategy history [] history
  | step {r : Run} {past final : List Run} {d : Disturbance} {rest : List Disturbance}
      (o : Outcome) (supported : PositiveSupport rows r d (strategy (r :: past) d) o)
      (tail : WordExecution rows update strategy
        (update r d (strategy (r :: past) d) o :: r :: past) rest final) :
      WordExecution rows update strategy (r :: past) (d :: rest) final

theorem strategy_answers_word
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {strategy : Strategy Run Disturbance Action} {entry : Run}
    (total : ∀ r past, Play rows update strategy entry (r :: past) →
      ∀ d, ∃ o, PositiveSupport rows r d (strategy (r :: past) d) o)
    (r : Run) (past : List Run) (hp : Play rows update strategy entry (r :: past))
    (word : List Disturbance) :
    ∃ final, WordExecution rows update strategy (r :: past) word final ∧
      Play rows update strategy entry final := by
  induction word generalizing r past with
  | nil => exact ⟨r :: past,WordExecution.nil _,hp⟩
  | cons d rest ih =>
    obtain ⟨o,ho⟩ := total r past hp d
    have nextPlay := Play.step hp d o ho
    obtain ⟨final,exec,hf⟩ := ih _ (r :: past) nextPlay
    exact ⟨final,WordExecution.step o ho exec,hf⟩

theorem game_answers_every_word
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    (h : GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw) :
    ∃ strategy, ∀ entry, entries entry → ∀ word : List Disturbance,
      ∃ final, WordExecution rows update strategy [entry] word final ∧
        Play rows update strategy entry final := by
  obtain ⟨_,_,strategy,hs⟩ := h
  refine ⟨strategy,?_⟩
  intro entry he word
  apply strategy_answers_word (entry := entry) _ entry [] Play.initial word
  intro r past hp d
  exact (hs entry he r past hp).2.2 d |>.2.1.2.2

/-- F's same-package consequence at an actual entry. The arrival proposition
is a component interpretation, not an extra field of the invariant witness. -/
theorem game_same_package_implies_arrival
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal arrival : Prop}
    {packageContext resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    (h : GameReadout rows update entries withdrawal (fun r => arrival ∧ packageContext r)
      resourceClosed responseLegal transitionLaw) : arrival := by
  obtain ⟨entry,he⟩ := h.2.1
  exact (game_entry_package h entry he).1

theorem no_entries_no_game
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    (empty : ∀ r, ¬ entries r) :
    ¬ GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw := by
  rintro ⟨_,⟨r,hr⟩,_⟩
  exact empty r hr

/-- Applies in particular when withdrawal removes a required resource or all
responses to one admitted disturbance are insolvent/unowned. -/
theorem missing_response_no_game
    {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}
    (entry : Run) (he : entries entry) (d : Disturbance)
    (missing : ∀ a, ¬ responseLegal entry d a) :
    ¬ GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw := by
  rintro ⟨_,_,strategy,hs⟩
  exact missing (strategy [entry] d) ((hs entry he entry [] Play.initial).2.2 d).1

/-- Changing rows/updaters of unselected actions cannot change generated
plays. This does not assert that those other actions are safe. -/
theorem play_selected_congruence
    {rows₁ rows₂ : Rows Run Disturbance Action Outcome}
    {update₁ update₂ : Updater Run Disturbance Action Outcome}
    (strategy : Strategy Run Disturbance Action)
    (hrows : ∀ r past d, rows₁ r d (strategy (r :: past) d) = rows₂ r d (strategy (r :: past) d))
    (hupdate : ∀ r past d o, update₁ r d (strategy (r :: past) d) o =
      update₂ r d (strategy (r :: past) d) o)
    {entry : Run} {history : List Run}
    (hp : Play rows₁ update₁ strategy entry history) : Play rows₂ update₂ strategy entry history := by
  induction hp with
  | initial => exact Play.initial
  | @step r past earlier d o supported ih =>
    have hs : PositiveSupport rows₂ r d (strategy (r :: past) d) o := by
      simpa only [PositiveSupport,← hrows r past d] using supported
    rw [hupdate r past d o]
    exact Play.step ih d o hs

section Guards
variable {rows : Rows Run Disturbance Action Outcome}
    {update : Updater Run Disturbance Action Outcome}
    {entries : Run → Prop} {withdrawal : Prop}
    {package resourceClosed : Run → Prop}
    {responseLegal : Run → Disturbance → Action → Prop}
    {transitionLaw : Run → Disturbance → Action → Outcome → Prop}

theorem invalid_withdrawal_no_game (invalid : ¬ withdrawal) :
    ¬ GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw :=
  fun h => invalid h.1

theorem entry_package_failure_no_game (entry : Run) (he : entries entry)
    (failed : ¬ package entry) :
    ¬ GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw :=
  fun h => failed (game_entry_package h entry he)

theorem entry_resource_failure_no_game (entry : Run) (he : entries entry)
    (failed : ¬ resourceClosed entry) :
    ¬ GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw := by
  rintro ⟨_,_,strategy,hs⟩
  exact failed (hs entry he entry [] Play.initial).2.1

/-- One bad positive branch of each possible response defeats autonomy;
this is not an obligation to make all available actions safe. -/
theorem unavoidable_bad_branch_no_game (entry : Run) (he : entries entry) (d : Disturbance)
    (bad : ∀ a, ∃ o, PositiveSupport rows entry d a o ∧ ¬ transitionLaw entry d a o) :
    ¬ GameReadout rows update entries withdrawal package resourceClosed responseLegal transitionLaw := by
  rintro ⟨_,_,strategy,hs⟩
  obtain ⟨o,ho,hn⟩ := bad (strategy [entry] d)
  exact hn (((hs entry he entry [] Play.initial).2.2 d).2.2 o ho)
end Guards

end CSTTT.TargetTheory.GenericHandoff.StrategyGame
