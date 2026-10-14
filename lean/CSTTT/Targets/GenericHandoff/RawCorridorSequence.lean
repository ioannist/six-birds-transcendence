import CSTTT.Targets.GenericHandoff.AcquisitionCorridor

/-! Heterogeneous raw acquisition requests compose as their actual interpreted
leg chain. Seams are decoded complete-frontier comparisons; outer distinctness
is a separate raw carrier check. No composite corridor result is a premise. -/
namespace CSTTT.TargetTheory.GenericHandoff.RawCorridorSequence
open RegisterInterpreter CSTTT.CorridorTheory.AtomicChain

structure Request (Cell : Type) (Value : Cell → Type) where
  Register : Type
  registerValue : Register → Type
  Disturbance : Type
  Action : Type
  Outcome : Type
  Stage : Type
  Id : Type
  History : Type
  Route : Type
  stageEq : DecidableEq Stage
  raw : AcquisitionCorridor.Raw Cell Value Register registerValue Disturbance Action Outcome Stage Id History Route
  route : Route

variable {Cell : Type} {Value : Cell → Type}

def source (q : Request Cell Value) : Nat := q.raw.schema.source.code
def target (q : Request Cell Value) : Nat := q.raw.schema.target.code
def leg (q : Request Cell Value) (a : Assignment Cell Value) : Option FiniteAtomicLeg :=
  letI := q.stageEq
  (AcquisitionCorridor.read q.raw a).map (fun v => AcquisitionCorridor.leg q.raw v q.route)
def Parent (q : Request Cell Value) (a : Assignment Cell Value) : Prop :=
  letI := q.stageEq
  AcquisitionCorridor.Pass q.raw a ∧ q.route ∈ q.raw.schema.routes

def chain (a : Assignment Cell Value) : List (Request Cell Value) → Option (List FiniteAtomicLeg)
  | [] => some []
  | q :: rest => do
    let here ← leg q a
    let tail ← chain a rest
    pure (here :: tail)

def seam (a : Assignment Cell Value) (left right : Request Cell Value) : Option Bool := do
  let l ← leg left a
  let r ← leg right a
  pure (AdjacentFrontierCheck l r)
def seams (a : Assignment Cell Value) : List (Request Cell Value) → Option Bool
  | [] | [_] => some true
  | left :: right :: rest => do
    let here ← seam a left right
    let tail ← seams a (right :: rest)
    pure (here && tail)

def OuterDistinct (qs : List (Request Cell Value)) : Prop :=
  (qs.head?.map source) ≠ (qs.getLast?.map target)
def Checked (a : Assignment Cell Value) (qs : List (Request Cell Value)) : Prop :=
  qs ≠ [] ∧ (∀ q ∈ qs, Parent q a) ∧ seams a qs = some true ∧ OuterDistinct qs
def Readout (a : Assignment Cell Value) (qs : List (Request Cell Value)) : Prop :=
  ∃ ls, chain a qs = some ls ∧ StrictCorridorWitness ls

theorem leg_source (q : Request Cell Value) (a : Assignment Cell Value) (l : FiniteAtomicLeg)
    (h : leg q a = some l) : l.source = source q := by
  letI := q.stageEq
  unfold leg at h
  cases hv : AcquisitionCorridor.read q.raw a with
  | none => simp [hv] at h
  | some v =>
    have he : AcquisitionCorridor.leg q.raw v q.route = l := by simpa [hv] using h
    exact he ▸ rfl
theorem leg_target (q : Request Cell Value) (a : Assignment Cell Value) (l : FiniteAtomicLeg)
    (h : leg q a = some l) : l.target = target q := by
  letI := q.stageEq
  unfold leg at h
  cases hv : AcquisitionCorridor.read q.raw a with
  | none => simp [hv] at h
  | some v =>
    have he : AcquisitionCorridor.leg q.raw v q.route = l := by simpa [hv] using h
    exact he ▸ rfl

theorem parent_constructs (q : Request Cell Value) (a : Assignment Cell Value) (h : Parent q a) :
    ∃ l, leg q a = some l ∧ AtomicLegPass l := by
  letI := q.stageEq
  obtain ⟨⟨_,v,hv,hc⟩,hr⟩ := h
  exact ⟨AcquisitionCorridor.leg q.raw v q.route,
    by simp [leg,hv],(hc.2.2.2.2.2.2 q.route hr).2.2.2.2.2⟩

theorem chain_constructs (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (h : ∀ q ∈ qs, Parent q a) : ∃ ls, chain a qs = some ls := by
  induction qs with
  | nil => exact ⟨[],rfl⟩
  | cons q rest ih =>
    obtain ⟨l,hl,_⟩ := parent_constructs q a (h q (by simp))
    obtain ⟨ls,hs⟩ := ih (fun r hr => h r (by simp [hr]))
    exact ⟨l::ls,by simp [chain,hl,hs]⟩

theorem chain_cons (a : Assignment Cell Value) (q : Request Cell Value)
    (qs : List (Request Cell Value)) (ls : List FiniteAtomicLeg) (h : chain a (q::qs) = some ls) :
    ∃ l rest, leg q a = some l ∧ chain a qs = some rest ∧ ls = l::rest := by
  cases hl : leg q a with
  | none => simp [chain,hl] at h
  | some l =>
    cases hs : chain a qs with
    | none => simp [chain,hl,hs] at h
    | some rest => exact ⟨l,rest,rfl,rfl,by simpa [chain,hl,hs] using h.symm⟩

theorem chain_length (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (ls : List FiniteAtomicLeg) (h : chain a qs = some ls) : ls.length = qs.length := by
  induction qs generalizing ls with
  | nil =>
    have he : ls = [] := by simpa [chain] using h.symm
    simp [he]
  | cons q rest ih =>
    obtain ⟨l,tail,_,ht,rfl⟩ := chain_cons a q rest ls h
    simp [ih tail ht]

theorem chain_sources (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (ls : List FiniteAtomicLeg) (h : chain a qs = some ls) :
    ls.map (·.source) = qs.map source := by
  induction qs generalizing ls with
  | nil =>
    have he : ls = [] := by simpa [chain] using h.symm
    simp [he]
  | cons q rest ih =>
    obtain ⟨l,tail,hl,ht,rfl⟩ := chain_cons a q rest ls h
    simp [leg_source q a l hl,ih tail ht]
theorem chain_targets (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (ls : List FiniteAtomicLeg) (h : chain a qs = some ls) :
    ls.map (·.target) = qs.map target := by
  induction qs generalizing ls with
  | nil =>
    have he : ls = [] := by simpa [chain] using h.symm
    simp [he]
  | cons q rest ih =>
    obtain ⟨l,tail,hl,ht,rfl⟩ := chain_cons a q rest ls h
    simp [leg_target q a l hl,ih tail ht]

theorem chain_check (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (ls : List FiniteAtomicLeg) (h : chain a qs = some ls)
    (hp : ∀ q ∈ qs, Parent q a) (hj : seams a qs = some true) : chainCheck ls = true := by
  induction qs generalizing ls with
  | nil =>
    have he : ls = [] := by simpa [chain] using h.symm
    simp [he,chainCheck]
  | cons q rest ih =>
    obtain ⟨l,tail,hl,ht,rfl⟩ := chain_cons a q rest ls h
    obtain ⟨other,ho,hpass⟩ := parent_constructs q a (hp q (by simp))
    have eq : other = l := Option.some.inj (ho.symm.trans hl)
    subst other
    cases rest with
    | nil =>
      have he : tail = [] := by simpa [chain] using ht.symm
      subst tail
      exact hpass
    | cons r rest =>
      obtain ⟨next,last,hn,hr,rfl⟩ := chain_cons a r rest tail ht
      have hd : AdjacentFrontierCheck l next = true ∧ seams a (r::rest) = some true := by
        cases hs : seams a (r::rest) with
        | none => simp [seams,seam,hl,hn,hs] at hj
        | some b =>
          have he : (AdjacentFrontierCheck l next && b) = true := by simpa [seams,seam,hl,hn,hs] using hj
          have he' : AdjacentFrontierCheck l next = true ∧ b = true := by
            simpa only [Bool.and_eq_true] using he
          exact ⟨he'.1,congrArg some he'.2⟩
      simp only [chainCheck,Bool.and_eq_true]
      exact ⟨⟨hpass,hd.1⟩,ih (next::last) ht (fun x hx => hp x (by simp [hx])) hd.2⟩

theorem outer_distinct (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (ls : List FiniteAtomicLeg) (h : chain a qs = some ls) (hd : OuterDistinct qs) :
    (ls.head?.map (·.source)) ≠ (ls.getLast?.map (·.target)) := by
  have hs := chain_sources a qs ls h
  have ht := chain_targets a qs ls h
  have hs' := congrArg List.head? hs
  have ht' := congrArg List.getLast? ht
  simp only [List.head?_map] at hs'
  simp only [List.getLast?_map] at ht'
  intro he
  exact hd (hs'.symm.trans (he.trans ht'))

theorem constructs (a : Assignment Cell Value) (qs : List (Request Cell Value)) (h : Checked a qs) : Readout a qs := by
  obtain ⟨ls,hl⟩ := chain_constructs a qs h.2.1
  refine ⟨ls,hl,strictTemporalCorridorComposition_generic ls ⟨?_,chain_check a qs ls hl h.2.1 h.2.2.1,outer_distinct a qs ls hl h.2.2.2⟩⟩
  intro he
  have hn := chain_length a qs ls hl
  rw [he] at hn
  exact h.1 (List.length_eq_zero_iff.mp hn.symm)

theorem chain_append (a : Assignment Cell Value) (left right : List (Request Cell Value)) :
    chain a (left++right) = (chain a left).bind (fun l => (chain a right).map (fun r => l++r)) := by
  induction left with
  | nil => simp [chain]
  | cons q rest ih =>
    simp only [List.cons_append,chain,ih]
    cases leg q a <;> cases chain a rest <;> cases chain a right <;> rfl

theorem missing_head (a : Assignment Cell Value) (q : Request Cell Value) (rest : List (Request Cell Value))
    (hm : leg q a = none) : ¬ Readout a (q::rest) := by
  rintro ⟨ls,h,_⟩
  simp [chain,hm] at h

theorem chain_none_at (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (q : Request Cell Value) (hq : q ∈ qs) (hm : leg q a = none) : chain a qs = none := by
  induction qs with
  | nil => simp at hq
  | cons r rest ih =>
    rcases List.mem_cons.mp hq with he | ht
    · subst r; simp [chain,hm]
    · simp [chain,ih ht]

theorem missing_at (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (q : Request Cell Value) (hq : q ∈ qs) (hm : leg q a = none) : ¬ Readout a qs := by
  rintro ⟨ls,he,_⟩
  rw [chain_none_at a qs q hq hm] at he
  contradiction

theorem readout_outer_distinct (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (h : Readout a qs) : OuterDistinct qs := by
  obtain ⟨ls,he,hw⟩ := h
  have hs := congrArg List.head? (chain_sources a qs ls he)
  have ht := congrArg List.getLast? (chain_targets a qs ls he)
  simp only [List.head?_map] at hs
  simp only [List.getLast?_map] at ht
  intro hd
  exact hw.pass.2.2 (hs.trans (hd.trans ht.symm))

theorem equal_outer_no_readout (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (h : ¬ OuterDistinct qs) : ¬ Readout a qs := fun hr => h (readout_outer_distinct a qs hr)

theorem bad_first_seam_no_readout (a : Assignment Cell Value) (q r : Request Cell Value)
    (rest : List (Request Cell Value)) (l m : FiniteAtomicLeg)
    (hl : leg q a = some l) (hm : leg r a = some m)
    (bad : AdjacentFrontierCheck l m = false) : ¬ Readout a (q::r::rest) := by
  rintro ⟨ls,he,hw⟩
  obtain ⟨first,tail,hf,ht,rfl⟩ := chain_cons a q (r::rest) ls he
  obtain ⟨second,last,hs,_,rfl⟩ := chain_cons a r rest tail ht
  have eqf := Option.some.inj (hf.symm.trans hl)
  have eqs := Option.some.inj (hs.symm.trans hm)
  subst first; subst second
  have hc := hw.pass.2.1
  simp [chainCheck,bad] at hc

theorem empty_no_readout (a : Assignment Cell Value) : ¬ Readout a [] := by
  rintro ⟨ls,he,hw⟩
  have hs : ls = [] := by simpa [chain] using he.symm
  exact hw.pass.1 hs

theorem chain_member (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (ls : List FiniteAtomicLeg) (h : chain a qs = some ls)
    (q : Request Cell Value) (hq : q ∈ qs) (l : FiniteAtomicLeg) (hl : leg q a = some l) : l ∈ ls := by
  induction qs generalizing ls with
  | nil => simp at hq
  | cons r rest ih =>
    obtain ⟨first,tail,hf,ht,rfl⟩ := chain_cons a r rest ls h
    rcases List.mem_cons.mp hq with he | hr
    · subst r
      have eq := Option.some.inj (hf.symm.trans hl)
      subst first; simp
    · exact List.mem_cons_of_mem _ (ih tail ht hr)

theorem bad_leg_no_readout (a : Assignment Cell Value) (qs : List (Request Cell Value))
    (q : Request Cell Value) (hq : q ∈ qs) (l : FiniteAtomicLeg) (hl : leg q a = some l)
    (bad : ¬ AtomicLegPass l) : ¬ Readout a qs := by
  rintro ⟨ls,he,hw⟩
  exact bad (chain_each_pass ls hw.pass.2.1 l (chain_member a qs ls he q hq l hl))

end CSTTT.TargetTheory.GenericHandoff.RawCorridorSequence
