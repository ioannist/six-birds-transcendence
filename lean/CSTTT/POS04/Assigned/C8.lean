import CSTTT.POS04.Assigned.C457Guards

/-! G2b-2: M3_model_spec.md:24,32. Funded viability from assigned raw data.
The greatest set is the union of all viable subsets of K, computed by finite
subset enumeration. No ten-round stabilization assumption on arbitrary rows. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit
structure ViabilityInputs where
  rows : KState → Action → List (Ambient × Nat)
  policy : KState → Action
  resource : ResourceData
  budget : Ledger

def viabilityInputs (d : Assignment) (tag : Tag) : ViabilityInputs :=
  ⟨(d (.rows tag)).getD (canonicalValue (.rows tag)),
   (d .policy).getD (canonicalValue .policy),
   (d (.resources tag)).getD (canonicalValue (.resources tag)),
   (d .maintenance).getD (canonicalValue .maintenance)⟩
def clause8 (a : Assignment) (tag : Tag) := viabilityInputs (decode (clauseScope tag .c8) a) tag

def available8 (d : ViabilityInputs) (tag : Tag) : Bool :=
  d.resource.rechargeAvailable && decide (d.budget.initialBudget ≥ d.budget.actionCost) &&
  decide (d.budget.initialBudget - d.budget.actionCost + d.budget.rechargePerAction > 0) &&
  decide (d.resource.owner = tag)
def rowClosed8 (d : ViabilityInputs) (s : KState) (a : Action) (S : List KState) : Bool :=
  let row := d.rows s a
  !row.isEmpty && decide ((row.map Prod.snd).sum = 4) &&
  row.all (fun e => e.2 > 0 && match e.1 with
    | .inK t => decide (t ∈ S)
    | .p2w0 | .p5w1 => false)
def retain8 (d : ViabilityInputs) (tag : Tag) (S : List KState) (s : KState) :=
  available8 d tag && actions.any (fun a => rowClosed8 d s a S)
def prune8 (d : ViabilityInputs) (tag : Tag) (S : List KState) := S.filter (retain8 d tag S)
def Viable8 (d : ViabilityInputs) (tag : Tag) (S : List KState) : Prop :=
  ∀ s ∈ S, retain8 d tag S s = true

def subsets8 : List KState → List (List KState)
  | [] => [[]]
  | s :: rest => subsets8 rest ++ (subsets8 rest).map (s :: ·)
def candidates8 := subsets8 kernel
def viableTest8 (d : ViabilityInputs) (tag : Tag) (S : List KState) := S.all (retain8 d tag S)
def greatest8 (d : ViabilityInputs) (tag : Tag) :=
  kernel.filter fun s => candidates8.any fun S => decide (s ∈ S) && viableTest8 d tag S

theorem row_closed8_mono (d : ViabilityInputs) (s : KState) (a : Action)
    {A B : List KState} (hAB : A ⊆ B) (h : rowClosed8 d s a A = true) :
    rowClosed8 d s a B = true := by
  simp only [rowClosed8, Bool.and_eq_true, List.all_eq_true] at h ⊢
  refine ⟨h.1, ?_⟩
  intro e he
  have hp := h.2 e he
  rcases e with ⟨dest,w⟩
  cases dest with
  | inK t =>
    simp only [decide_eq_true_eq] at hp ⊢
    exact ⟨hp.1,hAB hp.2⟩
  | p2w0 => simp at hp
  | p5w1 => simp at hp

theorem retain8_mono (d : ViabilityInputs) (tag : Tag) {A B : List KState}
    (hAB : A ⊆ B) {s : KState} (h : retain8 d tag A s = true) : retain8 d tag B s = true := by
  simp only [retain8, Bool.and_eq_true, List.any_eq_true] at h ⊢
  obtain ⟨a,ha,hrow⟩ := h.2
  exact ⟨h.1,a,ha,row_closed8_mono d s a hAB hrow⟩
theorem prune8_mono (d : ViabilityInputs) (tag : Tag) {A B : List KState}
    (hAB : A ⊆ B) : prune8 d tag A ⊆ prune8 d tag B := by
  intro s hs
  have h := List.mem_filter.mp hs
  exact List.mem_filter.mpr ⟨hAB h.1,retain8_mono d tag hAB h.2⟩

theorem filter_mem_subsets8 (p : KState → Bool) (xs : List KState) : xs.filter p ∈ subsets8 xs := by
  induction xs with
  | nil => simp [subsets8]
  | cons x xs ih => cases h : p x <;> simp [h,subsets8,ih]

theorem viable_test8_iff (d : ViabilityInputs) (tag : Tag) (S : List KState) :
    viableTest8 d tag S = true ↔ Viable8 d tag S := by simp [viableTest8,Viable8,List.all_eq_true]

theorem member_greatest8 (d : ViabilityInputs) (tag : Tag) (s : KState) :
    s ∈ greatest8 d tag ↔ ∃ S ∈ candidates8, s ∈ S ∧ Viable8 d tag S := by
  have hk : s ∈ kernel := by cases s <;> decide
  simp [greatest8,List.mem_filter,hk,List.any_eq_true,Bool.and_eq_true,viable_test8_iff]

theorem greatest8_contains_viable (d : ViabilityInputs) (tag : Tag)
    (S : List KState) (h : Viable8 d tag S) : S ⊆ greatest8 d tag := by
  let normalized := kernel.filter (fun s => decide (s ∈ S))
  have he : ∀ s, s ∈ normalized ↔ s ∈ S := by
    intro s
    have hk : s ∈ kernel := by cases s <;> decide
    simp [normalized,hk]
  have hv : Viable8 d tag normalized := by
    intro s hs
    exact retain8_mono d tag (fun _ ht => (he _).mpr ht) (h s ((he s).mp hs))
  intro s hs
  exact (member_greatest8 d tag s).mpr
    ⟨normalized,filter_mem_subsets8 _ kernel,(he s).mpr hs,hv⟩

theorem greatest8_viable (d : ViabilityInputs) (tag : Tag) : Viable8 d tag (greatest8 d tag) := by
  intro s hs
  obtain ⟨S,_,hsS,hv⟩ := (member_greatest8 d tag s).mp hs
  exact retain8_mono d tag (greatest8_contains_viable d tag S hv) (hv s hsS)
theorem greatest8_fixed (d : ViabilityInputs) (tag : Tag) :
    prune8 d tag (greatest8 d tag) = greatest8 d tag := List.filter_eq_self.mpr (greatest8_viable d tag)
theorem unavailable8_empty (d : ViabilityInputs) (tag : Tag)
    (h : available8 d tag = false) : greatest8 d tag = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro s hs
  have hv := greatest8_viable d tag s hs
  simp [retain8,h] at hv

def Ledger8 (d : ViabilityInputs) : Prop :=
  d.resource.rechargeAvailable = true ∧ d.budget.initialBudget = 1 ∧
  d.budget.actionCost = 1 ∧ d.budget.rechargePerAction = 1 ∧
  d.budget.initialBudget - d.budget.actionCost + d.budget.rechargePerAction = d.budget.initialBudget
def PUnchanged8 (d : ViabilityInputs) : Prop :=
  ∀ s ∈ kernel, ∀ t ∈ kernel, rowWeight (d.rows s (d.policy s)) t = pNum (index s) (index t)
def C8Gate (a : Assignment) (tag : Tag) : Prop := Ready a tag .c8
def C8Accept (a : Assignment) (tag : Tag) : Prop :=
  C8Gate a tag ∧ greatest8 (clause8 a tag) tag ≠ [] ∧ available8 (clause8 a tag) tag = true ∧
  Ledger8 (clause8 a tag) ∧ PUnchanged8 (clause8 a tag)

theorem clause8_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c8) a b) : clause8 a tag = clause8 b tag := by
  unfold clause8
  rw [decoder_locality h]
theorem c8_gate_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c8) a b) : C8Gate a tag ↔ C8Gate b tag := ready_locality h
theorem c8_accept_locality {a b : Assignment} {tag : Tag}
    (h : Agrees (clauseScope tag .c8) a b) : C8Accept a tag ↔ C8Accept b tag := by
  simp only [C8Accept,clause8_locality h,c8_gate_locality h]
end CSTTT.POS04.Assigned
