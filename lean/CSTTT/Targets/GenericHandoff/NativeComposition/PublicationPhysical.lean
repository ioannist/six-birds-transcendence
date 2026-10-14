import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationNominal

/-! Event prefixes are constructed AFTER the corresponding interpreted source
fold and exit succeed. Reception preserves the prefix and changes owner at the
same physical time. The full stored route is not used as the terminal prefix. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationPhysical
open RegisterInterpreter AcquisitionExecution SupportedAcquisitionSequence ModeExecution PublicationReplay

def terminalRun (cell : Owner) (h : Factor) :=
  PublicationExecution.snapshot h (copies cell) (start cell+(jump cell-1)) (swapOwner cell)
def arrivalRun (cell : Owner) (h : Factor) :=
  PublicationExecution.snapshot h (2*copies cell) (start cell+(jump cell-1)) cell
def entryRun (cell : Owner) (h : Factor) :=
  PublicationExecution.snapshot h (2*copies cell) (start cell+jump cell) cell

theorem source_terminal (cell : Owner) (h : Factor) :
    EpisodeExecution.sourceTerminal (raw cell) PublicationResources.assignment (PublicationReplay.ready cell) h=
      some (terminalRun cell h) := by
  cases cell
  · have hr := PublicationExecution.native_routes false true 2 2 1 PublicationExecution.nativeAssignment rfl
    have hh : PublicationExecution.secondAcquisition.histories.read PublicationExecution.nativeAssignment=some
      (fun h => [((),false,h),((),false,h),((),false,h)]) := rfl
    change EpisodeExecution.sourceTerminal PublicationExecution.secondAcquisition PublicationExecution.nativeAssignment
      (PublicationReplay.ready false) h=some (PublicationExecution.snapshot h 4 5 true)
    simp only [EpisodeExecution.sourceTerminal,hr,hh,bind,Option.bind_some,PublicationExecution.second_initializer,
      supportedFold,PublicationExecution.snapshot_check false true 2 2 1 PublicationExecution.nativeAssignment rfl,
      ite_true,PublicationExecution.snapshot_step false true 2 2 1 PublicationExecution.nativeAssignment (PublicationReplay.ready false) rfl]
  · have hr := PublicationExecution.native_routes true false 0 1 0 PublicationExecution.nativeAssignment rfl
    have hh : PublicationExecution.firstAcquisition.histories.read PublicationExecution.nativeAssignment=some
      (fun h => [((),false,h)]) := rfl
    change EpisodeExecution.sourceTerminal PublicationExecution.firstAcquisition PublicationExecution.nativeAssignment
      (PublicationReplay.ready true) h=some (PublicationExecution.snapshot h 2 1 false)
    simp only [EpisodeExecution.sourceTerminal,hr,hh,bind,Option.bind_some,PublicationExecution.first_initializer,
      supportedFold,PublicationExecution.snapshot_check true false 0 1 0 PublicationExecution.nativeAssignment rfl,
      ite_true,PublicationExecution.snapshot_step true false 0 1 0 PublicationExecution.nativeAssignment (PublicationReplay.ready true) rfl]

theorem receive_terminal (cell : Owner) (h : Factor) :
    receive (raw cell) PublicationResources.assignment (PublicationReplay.ready cell) (terminalRun cell h) h h=arrivalRun cell h := by
  have he := acquisition_receive cell (swapOwner cell) (start cell) (stride cell) PublicationExecution.nativeAssignment
    (PublicationReplay.ready cell) (PublicationExecution.episodePair (round cell))
    (PublicationExecution.assigned_pair cell) (terminalRun cell h) h h
  cases cell <;> exact he
theorem actual_arrival (cell : Owner) (h : Factor) :
    firstArrival (raw cell) PublicationResources.assignment (PublicationReplay.ready cell) h=some (arrivalRun cell h) := by
  cases cell
  · exact PublicationExecution.second_arrival (PublicationReplay.ready false) h
  · exact PublicationExecution.first_arrival (PublicationReplay.ready true) h
theorem actual_entry (cell : Owner) (h : Factor) :
    firstEntry (raw cell) PublicationResources.assignment (PublicationReplay.ready cell) h h=some (entryRun cell h) := by
  cases cell
  · exact PublicationExecution.second_entry (PublicationReplay.ready false) h
  · exact PublicationExecution.first_entry (PublicationReplay.ready true) h

noncomputable def sourcePrefix (cell : Owner) (h : Factor) : Option (ModeExecution.Registers × List Bool) := do
  let routes ← (raw cell).routes.read PublicationResources.assignment
  let first ← (routes h).path.head?
  let terminal ← EpisodeExecution.sourceTerminal (raw cell) PublicationResources.assignment (PublicationReplay.ready cell) h
  pure (terminal,[first])
noncomputable def arrivalPrefix (cell : Owner) (h : Factor) : Option (ModeExecution.Registers × List Bool) := do
  let routes ← (raw cell).routes.read PublicationResources.assignment
  let p ← sourcePrefix cell h
  pure (receive (raw cell) PublicationResources.assignment (PublicationReplay.ready cell) p.1 (routes h).history h,p.2)
noncomputable def exitPrefix (cell : Owner) (h : Factor) : Option (ModeExecution.Registers × List Bool) := do
  let routes ← (raw cell).routes.read PublicationResources.assignment
  let last ← (routes h).path.getLast?
  let p ← arrivalPrefix cell h
  let exited ← postExit (raw cell) PublicationResources.assignment (PublicationReplay.ready cell) h h (some p.1)
  pure (exited,p.2++[last])

theorem route_reader (cell : Owner) : (raw cell).routes.read PublicationResources.assignment=some (fun h => ⟨h,[false,true]⟩) :=
  PublicationExecution.native_routes cell (swapOwner cell) (start cell) (stride cell) (round cell)
    PublicationExecution.nativeAssignment (PublicationExecution.assigned_pair cell)
theorem source_prefix (cell : Owner) (h : Factor) : sourcePrefix cell h=some (terminalRun cell h,[false]) := by
  simp [sourcePrefix,route_reader,source_terminal]
theorem arrival_prefix (cell : Owner) (h : Factor) : arrivalPrefix cell h=some (arrivalRun cell h,[false]) := by
  simp [arrivalPrefix,route_reader,source_prefix,receive_terminal]
theorem exit_prefix (cell : Owner) (h : Factor) : exitPrefix cell h=some (entryRun cell h,[false,true]) := by
  have he := actual_entry cell h
  rw [firstEntry,actual_arrival] at he
  simpa [exitPrefix,route_reader,arrival_prefix,he] using congrArg (fun z => z.map (fun x => (x,[false,true]))) he
theorem terminal_prefix_is_not_full_recipe (cell : Owner) (h : Factor) :
    (sourcePrefix cell h).map Prod.snd≠((raw cell).routes.read PublicationResources.assignment).map (fun rs => (rs h).path) := by
  rw [source_prefix,route_reader]
  change (some [false] : Option (List Bool))≠some [false,true]
  decide +kernel

def ownerExpr (cell : Owner) : Expr Owner MemoryValue Unit (fun _ => ModeExecution.State) Unit CarrierId :=
  .map (fun p : FactorData × ModeExecution.State => names cell p.1.resource.owner) (context cell (swapOwner cell))
theorem owner_evaluation (cell : Owner) (a : Assignment Owner MemoryValue) (p : Input × Input)
    (hp : a cell=some p) (x : ModeExecution.Registers) :
    (ownerExpr cell).eval a x ()=some (names cell
      (if (x ()).2=cell then p.1.temporal.resource.owner else p.2.temporal.resource.owner)) := by
  simp only [ownerExpr,Expr.eval,context_evaluation cell (swapOwner cell) a p hp x,
    swap_owner_involution,Option.map_some]
  split <;> rfl
theorem actual_owners (cell : Owner) (h : Factor) :
    (ownerExpr cell).eval PublicationResources.assignment (terminalRun cell h) ()=some (names cell (swapOwner cell)) ∧
    (ownerExpr cell).eval PublicationResources.assignment (arrivalRun cell h) ()=some (names cell cell) ∧
    (ownerExpr cell).eval PublicationResources.assignment (entryRun cell h) ()=some (names cell cell) := by
  simp only [owner_evaluation cell PublicationResources.assignment (PublicationExecution.episodePair (round cell))
    (PublicationExecution.assigned_pair cell)]
  cases cell <;> exact ⟨rfl,rfl,rfl⟩
theorem physical_durations (cell : Owner) (h : Factor) :
    (acquisitionEvents (start cell) (stride cell) (PublicationExecution.episodePair (round cell)) false).orderAdvance=
      (terminalRun cell h ()).1.counter-start cell ∧
    (acquisitionEvents (start cell) (stride cell) (PublicationExecution.episodePair (round cell)) true).orderAdvance=
      (entryRun cell h ()).1.counter-(arrivalRun cell h ()).1.counter := by
  cases cell <;> exact ⟨rfl,rfl⟩
theorem receive_preserves_time (cell : Owner) (h : Factor) :
    (terminalRun cell h ()).1.counter=(arrivalRun cell h ()).1.counter ∧
    (terminalRun cell h ()).1.ticks=(arrivalRun cell h ()).1.ticks := ⟨rfl,rfl⟩
theorem source_and_target_modes (cell : Owner) (h : Factor) :
    (PublicationResources.runtime cell).sourcePresent.eval PublicationResources.assignment (terminalRun cell h) ()=some true ∧
    (PublicationResources.runtime cell).sourcePresent.eval PublicationResources.assignment (arrivalRun cell h) ()=some false ∧
    (PublicationResources.runtime cell).sourcePresent.eval PublicationResources.assignment (entryRun cell h) ()=some false := by
  cases cell <;> exact ⟨rfl,rfl,rfl⟩

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationPhysical
