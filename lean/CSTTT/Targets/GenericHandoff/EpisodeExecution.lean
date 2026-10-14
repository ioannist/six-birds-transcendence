import CSTTT.Targets.GenericHandoff.SupportedAcquisitionSequence

/-! The source terminal is interpreted before reception. It is distinct from
the post-reception arrival even when reception preserves physical time. -/
namespace CSTTT.TargetTheory.GenericHandoff.EpisodeExecution
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence
variable {Cell R D A O Stage Id H Route : Type} {Value : Cell → Type} {RV : R → Type}
  [DecidableEq D] [DecidableEq A] [DecidableEq O]

noncomputable def sourceTerminal (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : Route) : Option (Registers R RV) := do
  let routes ← raw.routes.read a
  let histories ← raw.histories.read a
  supportedFold raw a h (initial raw a h (routes rid).history) (histories (routes rid).history)

/-- Exact all-partial decomposition. Reception operates on the executed
source terminal, with the raw route selector retained. -/
theorem arrival_from_source_terminal (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : Route) :
    firstArrival raw a h rid = (do
      let routes ← raw.routes.read a
      let terminal ← sourceTerminal raw a h rid
      pure (receive raw a h terminal (routes rid).history rid)) := by
  cases hr : raw.routes.read a <;> cases hh : raw.histories.read a <;>
    simp [firstArrival,fromStart,sourceTerminal,hr,hh]

theorem entry_from_source_terminal (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : Route) (o : O) :
    firstEntry raw a h rid o=postExit raw a h rid o (do
      let routes ← raw.routes.read a
      let terminal ← sourceTerminal raw a h rid
      pure (receive raw a h terminal (routes rid).history rid)) := by
  rw [firstEntry,arrival_from_source_terminal]

theorem terminal_execution (raw : Raw Cell Value R RV D A O Stage Id H Route)
    (a : Assignment Cell Value) (h : Ready raw a) (rid : Route)
    (routes : Route → AcquisitionExecution.Route H Id) (histories : H → List (D × A × O))
    (hr : raw.routes.read a=some routes) (hh : raw.histories.read a=some histories)
    (terminal : Registers R RV) (he : sourceTerminal raw a h rid=some terminal) :
    HistoryExecution raw a h (initial raw a h (routes rid).history) (histories (routes rid).history) terminal := by
  apply (fold_some_iff raw a h _ terminal _).mp
  simpa [sourceTerminal,hr,hh] using he

end CSTTT.TargetTheory.GenericHandoff.EpisodeExecution
