import CSTTT.Transport.RouteLicenses

/-! G3c transcriptions of audit/proposed_models/TTH09-ROUTES.model.json,
/models/0 and /models/1; definitions from audit/G3_route_spec.md:105–138.
Source-order Fin indices label raw routes/events, not predictive verdicts.
The evaluated export is compared to every operative raw table by the checker. -/
namespace CSTTT.RouteLicenses.Models
open CSTTT.RouteLicenses

inductive BitAction where | identity | toggle deriving DecidableEq, Repr
def BitAction.apply : BitAction → Bool → Bool | .identity,x => x | .toggle,x => !x
def translate (increment x : Bool) : Bool := if increment then !x else x

/-- /shared_domains/actions and clock_group: exact bit action and Z/2 clock. -/
def bitEvent {n : Nat} (entry exit : Fin n) (action : BitAction) (clock : Bool) : EventData (Fin n) Bool :=
  ⟨entry,exit,true,action.apply,translate clock,translate clock⟩
/-- /models/0/events, routes, boundaries, rewrites, ranks, critical_pairs, completions. -/
def negAction (e : Fin 3) : BitAction := if e = 2 then .toggle else .identity
def negClock (e : Fin 3) : Bool := decide (e = 2)
def necessity : RawSystem (Fin 3) (Fin 3) (Fin 1) (Fin 2) Bool :=
  ⟨(fun r => [r]),(fun _ => 0),(fun e => bitEvent 0 1 (negAction e) (negClock e)),
    (fun _ => ⟨0,1,false⟩),[],(fun _ => 0),[(0,1),(0,2),(1,2)],[]⟩
def necessityDomain : Domain (Fin 3) (Fin 1) := ⟨0,[0,1,2]⟩

/-- /models/1 source order: a0,n0,a1,n1 and e_a0,e_n0,e_a1,e_n1. -/
def positiveBoundary (r : Fin 4) : Fin 2 := ⟨r.val / 2,by omega⟩
def posAction (e : Fin 4) : BitAction := if e.val < 2 then .identity else .toggle
def posClock (e : Fin 4) : Bool := decide (2 ≤ e.val)
def positive : RawSystem (Fin 4) (Fin 4) (Fin 2) (Fin 3) Bool :=
  ⟨(fun r => [r]),positiveBoundary,
    (fun e => bitEvent 0 (if e.val < 2 then 1 else 2) (posAction e) (posClock e)),
    (fun b => ⟨0,(if b = 0 then 1 else 2),false⟩),
    [(0,1),(2,3)],(fun r => if r.val % 2 = 0 then 1 else 0),[(0,1),(2,3)],
    [⟨0,1,1,[0,1],[1]⟩,⟨2,3,3,[2,3],[3]⟩]⟩
def aliasRoute (b : Fin 2) : Fin 4 := if b = 0 then 0 else 2
def normalRoute (b : Fin 2) : Fin 4 := if b = 0 then 1 else 3
def positiveDomain (b : Fin 2) : Domain (Fin 4) (Fin 2) := ⟨b,[aliasRoute b,normalRoute b]⟩

macro "raw_check" : tactic => `(tactic|
  (first | (simp [vertexPath,rewrite,terminal,RewriteActions,RewriteBoundary,CompletionValid,
    rewritePath,CompletionActions,completionRows,criticalPairs,reduction,positive,
    positiveDomain,aliasRoute,normalRoute,bitEvent,positiveBoundary,posAction,posClock,
    translate,BitAction.apply,execWord,clockWord,inverseClockWord,necessity,negAction,negClock,
    necessityDomain] <;> decide +revert) | decide +revert))

theorem necessity_domain : DomainCheck necessity necessityDomain := by
  constructor
  · exact ⟨0,by decide,1,by decide,by decide⟩
  · decide
  · intro r _; constructor <;> raw_check
  · decide
  · decide

theorem necessity_equal : endpoint necessity 0 = endpoint necessity 1 := rfl
theorem necessity_nonzero_holonomy :
    inverseClockWord necessity (necessity.path 2) (clockWord necessity (necessity.path 0) false) ≠ false := by decide

theorem necessity_separation : endpoint necessity 0 ≠ endpoint necessity 2 := by decide

theorem necessity_reach_identity {r s : Fin 3} (h : Reach (rewrite necessity necessityDomain) r s) : r = s := by
  induction h with
  | refl => rfl
  | step he _ _ => simp [rewrite,necessity] at he

theorem necessity_no_normalization : ¬ NormalizationLicense necessity necessityDomain := by
  intro h
  obtain ⟨n,_,_,hn⟩ := h.normal
  have h0 := necessity_reach_identity (hn 0 (by decide)).1
  have h1 := necessity_reach_identity (hn 1 (by decide)).1
  have he : (0 : Fin 3) = 1 := h0.trans h1.symm
  contradiction

theorem necessity_no_confluence : ¬ ConfluenceLicense necessity necessityDomain := by
  intro h
  obtain ⟨j,_,ha,hb⟩ := h.joinable 0 (by decide) 1 (by decide)
  have he : (0 : Fin 3) = 1 := (necessity_reach_identity ha).trans (necessity_reach_identity hb).symm
  contradiction

theorem necessity_no_flatness : ¬ FlatLicense necessity necessityDomain := by
  intro h
  have hp : ((0,1) : Fin 3 × Fin 3) ∈ criticalPairs necessity necessityDomain := by decide
  obtain ⟨c,hc,_⟩ := h.completed _ hp
  simp [completionRows,necessity] at hc

theorem endpoint_coincidence_does_not_license :
    DomainCheck necessity necessityDomain ∧ endpoint necessity 0 = endpoint necessity 1 ∧
    ¬ RouteLicense necessity necessityDomain := by
  refine ⟨necessity_domain,necessity_equal,?_⟩
  rintro (h | h | h)
  · exact necessity_no_normalization h
  · exact necessity_no_flatness h
  · exact necessity_no_confluence h

/-- Formal failure of the converse, on its fixed nonempty raw-path domain. -/
theorem literal_necessity_false : ¬ (∀ r ∈ necessityDomain.routes, ∀ s ∈ necessityDomain.routes,
    endpoint necessity r = endpoint necessity s → RouteLicense necessity necessityDomain) := by
  intro h
  exact endpoint_coincidence_does_not_license.2.2 (h 0 (by decide) 1 (by decide) necessity_equal)

theorem positive_domain (b : Fin 2) : DomainCheck positive (positiveDomain b) := by
  constructor
  · exact ⟨aliasRoute b,by simp [positiveDomain],normalRoute b,by simp [positiveDomain],by raw_check⟩
  · raw_check
  · intro r hr; constructor <;> raw_check
  · raw_check
  · raw_check

theorem positive_rewrite_edge (b : Fin 2) : rewrite positive (positiveDomain b) (aliasRoute b) (normalRoute b) := by
  raw_check

theorem positive_reach (b : Fin 2) (r : Fin 4) (hr : r ∈ (positiveDomain b).routes) :
    Reach (rewrite positive (positiveDomain b)) r (normalRoute b) := by
  simp [positiveDomain] at hr
  rcases hr with rfl | rfl
  · exact .step (positive_rewrite_edge b) (.refl _)
  · exact .refl _

theorem positive_normal_terminal (b : Fin 2) : terminal (positiveDomain b) (rewrite positive (positiveDomain b)) (normalRoute b) := by
  raw_check

theorem positive_terminal_unique (b : Fin 2) (z : Fin 4) (hz : z ∈ (positiveDomain b).routes)
    (ht : terminal (positiveDomain b) (rewrite positive (positiveDomain b)) z) : z = normalRoute b := by
  simp [positiveDomain] at hz
  rcases hz with rfl | rfl
  · exact False.elim (ht _ (by simp [positiveDomain]) (positive_rewrite_edge b))
  · rfl

theorem positive_normalization (b : Fin 2) : NormalizationLicense positive (positiveDomain b) := by
  constructor
  · exact positive_domain b
  · raw_check
  · raw_check
  · raw_check
  · exact ⟨normalRoute b,by simp [positiveDomain],positive_normal_terminal b,
      fun r hr => ⟨positive_reach b r hr,fun z hz _ ht => positive_terminal_unique b z hz ht⟩⟩

theorem positive_confluence (b : Fin 2) : ConfluenceLicense positive (positiveDomain b) := by
  constructor
  · exact positive_domain b
  · raw_check
  · raw_check
  · intro r hr s hs
    exact ⟨normalRoute b,by simp [positiveDomain],positive_reach b r hr,positive_reach b s hs⟩

theorem positive_move_edge (b : Fin 2) : move positive (positiveDomain b) (aliasRoute b) (normalRoute b) := by
  unfold move
  refine ⟨if b = 0 then ⟨0,1,1,[0,1],[1]⟩ else ⟨2,3,3,[2,3],[3]⟩,?_,?_⟩ <;> raw_check

theorem positive_reduction_edge (b : Fin 2) : reduction positive (positiveDomain b) (aliasRoute b) (normalRoute b) := by
  unfold reduction
  refine ⟨if b = 0 then ⟨0,1,1,[0,1],[1]⟩ else ⟨2,3,3,[2,3],[3]⟩,?_,?_⟩ <;> raw_check

theorem positive_flatness (b : Fin 2) : FlatLicense positive (positiveDomain b) := by
  constructor
  · exact positive_domain b
  · decide
  · decide
  · raw_check
  · raw_check
  · intro r hr
    refine ⟨(aliasRoute b,normalRoute b),?_,?_⟩
    · raw_check
    · simpa [positiveDomain] using hr
  · intro p hp
    refine ⟨if b = 0 then ⟨0,1,1,[0,1],[1]⟩ else ⟨2,3,3,[2,3],[3]⟩,?_,?_⟩ <;> raw_check
  · raw_check
  · intro r hr s hs
    have ha : r = aliasRoute b ∨ r = normalRoute b := by simpa [positiveDomain] using hr
    have hb : s = aliasRoute b ∨ s = normalRoute b := by simpa [positiveDomain] using hs
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact .refl _
    · exact .step (positive_move_edge b) (.refl _)
    · apply Reach.step ?_ (.refl _)
      obtain ⟨c,hc,he⟩ := positive_move_edge b
      exact ⟨c,hc,he.elim Or.inr Or.inl⟩
    · exact .refl _
  · raw_check
  · refine ⟨normalRoute b,by simp [positiveDomain],?_,?_⟩
    · raw_check
    · intro r hr
      have ha : r = aliasRoute b ∨ r = normalRoute b := by simpa [positiveDomain] using hr
      constructor
      · rcases ha with rfl | rfl
        · exact .step (positive_reduction_edge b) (.refl _)
        · exact .refl _
      · intro z hz _ ht
        have hz' : z = aliasRoute b ∨ z = normalRoute b := by simpa [positiveDomain] using hz
        rcases hz' with rfl | rfl
        · exact False.elim (ht _ (by simp [positiveDomain]) (positive_reduction_edge b))
        · rfl
  · raw_check
  · raw_check

theorem positive_nonconstant : endpoint positive 1 ≠ endpoint positive 3 := by decide
theorem positive_functions_nonconstant (r : Fin 4) : execWord positive (positive.path r) false ≠ execWord positive (positive.path r) true := by
  raw_check
end CSTTT.RouteLicenses.Models
