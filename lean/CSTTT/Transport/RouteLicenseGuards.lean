import CSTTT.Transport.RouteLicenseModels

/-! G3c field-sensitivity guards. Each variant changes one raw field family;
none changes a stored verdict. Clock forward/backward maps are independently
checked raw inverse tables in the generic representation. These are method
guards, not revisions to the frozen route models. -/
namespace CSTTT.RouteLicenses.Models

def duplicatePath := { positive with path := fun r => if r = 0 then [1] else positive.path r }
def unavailableEvent := { positive with events := fun e =>
  if e = 0 then { positive.events e with available := false } else positive.events e }
def wrongEventEntry := { positive with events := fun e =>
  if e = 0 then { positive.events e with entry := 1 } else positive.events e }
def wrongEventExit := { positive with events := fun e =>
  if e = 0 then { positive.events e with exit := 0 } else positive.events e }
def wrongBoundaryEntry := { positive with boundaries := fun b =>
  if b = 0 then { positive.boundaries b with entry := 1 } else positive.boundaries b }
def wrongBoundaryExit := { positive with boundaries := fun b =>
  if b = 0 then { positive.boundaries b with exit := 0 } else positive.boundaries b }
def changedInitial := { positive with boundaries := fun b =>
  if b = 1 then { positive.boundaries b with initial := true } else positive.boundaries b }
def wrongRouteBoundary := { positive with boundary := fun r => if r = 0 then 1 else positive.boundary r }
def wrongDomain : Domain (Fin 4) (Fin 2) := ⟨1,[0,1]⟩
def repeatedDomain : Domain (Fin 4) (Fin 2) := ⟨0,[0,0]⟩
def changedAction := { positive with events := fun e =>
  if e = 0 then { positive.events e with action := BitAction.toggle.apply } else positive.events e }
def brokenForward := { positive with events := fun e =>
  if e = 0 then { positive.events e with clockForward := fun _ => false } else positive.events e }
def brokenBackward := { positive with events := fun e =>
  if e = 0 then { positive.events e with clockBackward := fun _ => false } else positive.events e }
def changedClock := { positive with events := fun e =>
  if e = 0 then { positive.events e with clockForward := (translate true), clockBackward := (translate true) } else positive.events e }
def noRewrites := { positive with rewrites := [] }
def flatRanks := { positive with rank := fun _ => 0 }
def noCritical := { positive with critical := [] }
def repeatedCritical := { positive with critical := [(0,0),(2,3)] }
def noCompletions := { positive with completions := [] }
def wrongCompletionLeft := { positive with completions := [⟨1,1,1,[0,1],[1]⟩,⟨2,3,3,[2,3],[3]⟩] }
def wrongCompletionRight := { positive with completions := [⟨0,0,1,[0,1],[1]⟩,⟨2,3,3,[2,3],[3]⟩] }
def wrongCompletionJoin := { positive with completions := [⟨0,1,0,[0,1],[1]⟩,⟨2,3,3,[2,3],[3]⟩] }
def noLeftPath := { positive with completions := [⟨0,1,1,[],[1]⟩,⟨2,3,3,[2,3],[3]⟩] }
def noRightPath := { positive with completions := [⟨0,1,1,[0,1],[]⟩,⟨2,3,3,[2,3],[3]⟩] }

theorem path_distinctness_guard : ¬ DomainCheck duplicatePath (positiveDomain 0) := by
  intro h
  obtain ⟨r,hr,s,hs,he⟩ := h.distinct
  have eq : ∀ r ∈ (positiveDomain 0).routes, ∀ s ∈ (positiveDomain 0).routes,
      duplicatePath.path r = duplicatePath.path s := by decide
  exact he (eq r hr s hs)
theorem critical_path_guard : ¬ FlatLicense duplicatePath (positiveDomain 0) := by
  intro h
  have hp := h.pairs (0,1) (by decide)
  exact hp.2.2.2.2 rfl

theorem availability_guard : ¬ DomainCheck unavailableEvent (positiveDomain 0) := by
  intro h
  have he := (h.admissible 0 (by decide)).available 0 (by decide)
  contradiction

theorem event_entry_guard : ¬ DomainCheck wrongEventEntry (positiveDomain 0) := by
  intro h
  have he := (h.admissible 0 (by decide)).vertices
  have hn : ¬ vertexPath wrongEventEntry [0] 0 1 := by simp [vertexPath,wrongEventEntry,positive,bitEvent]
  exact hn he

theorem event_exit_guard : ¬ DomainCheck wrongEventExit (positiveDomain 0) := by
  intro h
  have he := (h.admissible 0 (by decide)).vertices
  have hn : ¬ vertexPath wrongEventExit [0] 0 1 := by simp [vertexPath,wrongEventExit,positive,bitEvent]
  exact hn he

theorem boundary_entry_guard : ¬ DomainCheck wrongBoundaryEntry (positiveDomain 0) := by
  intro h
  have he := (h.admissible 0 (by decide)).vertices
  have hn : ¬ vertexPath wrongBoundaryEntry [0] 1 1 := by simp [vertexPath,wrongBoundaryEntry,positive,bitEvent]
  exact hn he

theorem boundary_exit_guard : ¬ DomainCheck wrongBoundaryExit (positiveDomain 0) := by
  intro h
  have he := (h.admissible 0 (by decide)).vertices
  have hn : ¬ vertexPath wrongBoundaryExit [0] 0 0 := by simp [vertexPath,wrongBoundaryExit,positive,bitEvent]
  exact hn he

/-- The initial state is a lawful raw input, not a derived candidate and not
fixed by a license. Changing it can destroy the declared nonconstant readout. -/
theorem initial_readout_guard : ¬ (endpoint changedInitial 1 ≠ endpoint changedInitial 3) := by decide

theorem route_boundary_guard : ¬ DomainCheck wrongRouteBoundary (positiveDomain 0) := by
  intro h
  have he := h.boundary 0 (by decide)
  contradiction

theorem domain_boundary_guard : ¬ DomainCheck positive wrongDomain := by
  intro h
  have he := h.boundary 0 (by decide)
  contradiction

theorem domain_routes_guard : ¬ DomainCheck positive repeatedDomain := by
  intro h
  have he := h.noDuplicates
  have hn : ¬ (repeatedDomain.routes.map positive.path).Nodup := by decide
  exact hn he

theorem action_guard : ¬ NormalizationLicense changedAction (positiveDomain 0) := by
  intro h
  have he := h.actions 0 (by decide) 1 (by decide) false
  contradiction

theorem forward_clock_guard : ¬ FlatLicense brokenForward (positiveDomain 0) := by
  intro h
  have he := h.clockActions 0 rfl true
  contradiction

theorem backward_clock_guard : ¬ FlatLicense brokenBackward (positiveDomain 0) := by
  intro h
  have he := (h.clockInverse 0 rfl true).1
  contradiction

theorem holonomy_guard : ¬ FlatLicense changedClock (positiveDomain 0) := by
  intro h
  have he := h.zero ⟨0,1,1,[0,1],[1]⟩ (by decide) false
  contradiction

theorem rank_guard : ¬ NormalizationLicense flatRanks (positiveDomain 0) := by
  intro h
  have he := h.decreasing 0 (by decide) 1 (by decide)
  change (0 : Nat) < 0 at he
  omega

theorem completion_rank_guard : ¬ FlatLicense flatRanks (positiveDomain 0) := by
  intro h
  have he := h.decreasing 0 1 (by
    refine ⟨⟨0,1,1,[0,1],[1]⟩,by decide,Or.inl rfl,rfl,by decide⟩)
  change (0 : Nat) < 0 at he
  omega

theorem empty_rewrite_reach {r s : Fin 4} (h : Reach (rewrite noRewrites (positiveDomain 0)) r s) : r = s := by
  induction h with
  | refl => rfl
  | step he _ _ => simp [rewrite,noRewrites] at he

theorem rewrite_guard : ¬ ConfluenceLicense noRewrites (positiveDomain 0) := by
  intro h
  obtain ⟨j,_,hr,hs⟩ := h.joinable 0 (by decide) 1 (by decide)
  have he : (0 : Fin 4) = 1 := (empty_rewrite_reach hr).trans (empty_rewrite_reach hs).symm
  contradiction

theorem critical_nonempty_guard : ¬ FlatLicense noCritical (positiveDomain 0) := by
  intro h
  have he := h.nonempty
  change (0 : Nat) > 0 at he
  omega

theorem critical_distinct_guard : ¬ FlatLicense repeatedCritical (positiveDomain 0) := by
  intro h
  have he := h.pairs (0,0) (by decide)
  exact he.2.2.2.2 rfl

theorem completion_guard : ¬ FlatLicense noCompletions (positiveDomain 0) := by
  intro h
  obtain ⟨c,hc,_⟩ := h.completed (0,1) (by decide)
  simp [completionRows,noCompletions] at hc

theorem completion_left_guard : ¬ FlatLicense wrongCompletionLeft (positiveDomain 0) := by
  intro h
  have he := (h.valid ⟨1,1,1,[0,1],[1]⟩ (by decide)).1
  have hn : (1,1) ∉ criticalPairs wrongCompletionLeft (positiveDomain 0) := by decide
  exact hn he

theorem completion_right_guard : ¬ FlatLicense wrongCompletionRight (positiveDomain 0) := by
  intro h
  have he := (h.valid ⟨0,0,1,[0,1],[1]⟩ (by decide)).1
  have hn : (0,0) ∉ criticalPairs wrongCompletionRight (positiveDomain 0) := by decide
  exact hn he

theorem completion_join_guard : ¬ FlatLicense wrongCompletionJoin (positiveDomain 0) := by
  intro h
  have he := (h.valid ⟨0,1,0,[0,1],[1]⟩ (by decide)).2.2.1
  have hn : ¬ rewritePath wrongCompletionJoin (positiveDomain 0) [0,1] 0 0 := by
    simp [rewritePath,rewrite,wrongCompletionJoin,positiveDomain,aliasRoute,normalRoute]
  exact hn he

theorem left_completion_path_guard : ¬ FlatLicense noLeftPath (positiveDomain 0) := by
  intro h
  exact (h.valid ⟨0,1,1,[],[1]⟩ (by decide)).2.2.1

theorem right_completion_path_guard : ¬ FlatLicense noRightPath (positiveDomain 0) := by
  intro h
  exact (h.valid ⟨0,1,1,[0,1],[]⟩ (by decide)).2.2.2
end CSTTT.RouteLicenses.Models
