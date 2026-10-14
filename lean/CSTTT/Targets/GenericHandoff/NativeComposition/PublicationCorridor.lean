import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationSequence
import CSTTT.Corridor.AtomicChain

/-! The corridor projection uses absolute physical ticks and an accumulated
executed-event log. Full incoming past is transported separately by the actual
receiver and whole-future map; it is not replaced by this event-log projection.
All frontiers read the actual runtime. No leg or verdict is primitive input. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationCorridor
open RegisterInterpreter RegisterInitialization AcquisitionExecution SupportedAcquisitionSequence
open CSTTT.CorridorTheory.AtomicChain ModeExecution PublicationReplay

def predictiveCode : Frame.Predictive → Nat
  | .inl (n,channels) => 2*n+(if [true] ∈ channels then 1 else 0)
  | .inr s => 4+labels s

def frontier (cell : Owner) (a : Assignment Owner MemoryValue) (x : ModeExecution.Registers)
    (log : List String) : Option Frontier := do
  let d ← (activeData cell (swapOwner cell)).eval a x ()
  let owner ← (PublicationPhysical.ownerExpr cell).eval a x ()
  let order ← (PublicationResources.runtime cell).order.eval a x ()
  let ticks ← (PublicationResources.runtime cell).ticks.eval a x ()
  let progress ← (PublicationResources.runtime cell).progress.eval a x ()
  let record ← (PublicationResources.runtime cell).record.eval a x ()
  pure ⟨predictiveCode (TemporalFactorRules.prediction (factorSchema (swapOwner cell)) d (x ()).1.factor),
    order,ticks,progress,record,log,if (x ()).1.funded then "funded" else "",owner.code⟩

def eventName (cell : Owner) (id : Bool) :=
  (if cell then "first-" else "second-")++(if id then "exit" else "source")
def seedName (s : Factor) := "past-"++toString (bit s.1)++toString (bit s.2.1)++toString (bit s.2.2)

def stage (realized : List Stage) (s : Stage) (x : ModeExecution.Registers)
    (support : List Nat) (f : Frontier) : RawStage :=
  ⟨support,decide (s ∈ realized) && (x ()).1.funded,f⟩

def construct (cell : Owner) (p : Input × Input)
    (begin terminal exited : ModeExecution.Registers) (first last : Bool)
    (f0 f1 f2 : Frontier) : FiniteAtomicLeg :=
  let cfg := PublicationReplay.schema cell
  let events := acquisitionEvents (start cell) (stride cell) p
  let source := cfg.source.code
  let target := cfg.target.code
  let mixed := (if (events first).sourceSupport then [source] else [])++
    (if (events first).targetSupport then [target] else [])
  let final := (if (events last).sourceSupport then [source] else [])++
    (if (events last).targetSupport then [target] else [])
  let label1 := eventName cell first
  let label2 := eventName cell last
  { interventionMode := .mixedSupport
    source := source, target := target
    stages := [stage p.2.temporal.realized 0 begin [source] f0,
      stage p.2.temporal.realized 1 terminal mixed f1,
      stage p.2.temporal.realized 2 exited final f2]
    events := [⟨"entry",source,0⟩]++
      (if (events first).sourceSupport then [⟨label1++"-source",source,1⟩] else [])++
      (if (events first).targetSupport then [⟨label1++"-target",target,1⟩] else [])++
      (if (events last).sourceSupport then [⟨label2++"-source",source,2⟩] else [])++
      (if (events last).targetSupport then [⟨label2++"-target",target,2⟩] else [])
    dependencies := [⟨"entry",label1++"-source"⟩,⟨"entry",label1++"-target"⟩,
      ⟨label1++"-source",label2++"-target"⟩,⟨label1++"-target",label2++"-target"⟩]
    updates := [⟨0,(events first).orderAdvance,(events first).orderAdvance,
      (events first).orderAdvance,(events first).orderAdvance,[label1],f1.maintenance,f1.owner⟩,
      ⟨0,(events last).orderAdvance,(events last).orderAdvance,
      (events last).orderAdvance,(events last).orderAdvance,[label2],f2.maintenance,f2.owner⟩]
    base := default, sourceContribution := default, targetContribution := default
    sourceAudit := label1++"-source", targetAudit := label1++"-target", laterAudit := label2++"-target" }

def eventGuard (cell : Owner) (p : Input × Input) (first last : Bool) : Bool :=
  let es := acquisitionEvents (start cell) (stride cell) p
  (es first).atomic && (es first).strictStep && (es last).atomic && (es last).strictStep

def recipeGuard (cell : Owner) (p : Input × Input) (path : List Bool) : Bool :=
  let es := acquisitionEvents (start cell) (stride cell) p
  decide (path=[false,true] ∧ (es false).fromStage=0 ∧ (es false).toStage=1 ∧
    (es true).fromStage=1 ∧ (es true).toStage=2)

/-- The only readiness branch comes from the consumed cell. Guarded folds and
exit compute all three states before any corridor leg can be returned. -/
noncomputable def episode (cell : Owner) (a : Assignment Owner MemoryValue)
    (h : Factor) (seed : List String) : Option FiniteAtomicLeg :=
  if ha : (a cell).isSome=true then do
    let p ← a cell
    if p.1.receiver.sourcePresent && p.1.receiver.targetFunded && p.1.receiver.funded then
      let ready := acquisition_ready cell (swapOwner cell) (start cell) (stride cell) a ha
      let routes ← (raw cell).routes.read a
      if recipeGuard cell p (routes h).path then
        let first ← (routes h).path.head?
        let last ← (routes h).path.getLast?
        if eventGuard cell p first last then
          let initial := AcquisitionExecution.initial (raw cell) a ready (routes h).history
          let terminal ← EpisodeExecution.sourceTerminal (raw cell) a ready h
          let arrived := AcquisitionExecution.receive (raw cell) a ready terminal (routes h).history h
          let exited ← postExit (raw cell) a ready h h (some arrived)
          let f0 ← frontier cell a initial seed
          let f1 ← frontier cell a terminal (seed++[eventName cell first])
          let f2 ← frontier cell a exited (seed++[eventName cell first,eventName cell last])
          pure (construct cell p initial terminal exited first last f0 f1 f2)
        else none
      else none
    else none
  else none

theorem missing_episode (cell : Owner) (a : Assignment Owner MemoryValue) (hm : a cell=none)
    (h : Factor) (seed : List String) : episode cell a h seed=none := by simp [episode,hm]
theorem inactive_episode (cell : Owner) (a : Assignment Owner MemoryValue) (p : Input × Input)
    (hp : a cell=some p) (hn : p.1.receiver.sourcePresent=false) (h : Factor) (seed : List String) :
    episode cell a h seed=none := by simp [episode,hp,hn]

def startRun (cell : Owner) (h : Factor) :=
  PublicationExecution.snapshot h (copies cell) (start cell) (swapOwner cell)
def snapshotFrontier (cell : Owner) (h : Factor) (time : Nat) (owner : Owner) (log : List String) : Frontier :=
  ⟨labels h,time,time,time,time,log,"funded",(names cell owner).code⟩

theorem snapshot_frontier (cell target : Owner) (h : Factor) (time : Nat) (log : List String) :
    frontier cell PublicationResources.assignment
      (PublicationExecution.snapshot h (if target then 2*copies cell else copies cell) time
        (if target then cell else swapOwner cell)) log=
      some (snapshotFrontier cell h time (if target then cell else swapOwner cell) log) := by
  cases cell <;> cases target
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl

def canonicalLeg (cell : Owner) (h : Factor) (seed : List String) : FiniteAtomicLeg :=
  construct cell (PublicationExecution.episodePair (round cell)) (startRun cell h)
    (PublicationPhysical.terminalRun cell h) (PublicationPhysical.entryRun cell h) false true
    (snapshotFrontier cell h (start cell) (swapOwner cell) seed)
    (snapshotFrontier cell h (start cell+(jump cell-1)) (swapOwner cell) (seed++[eventName cell false]))
    (snapshotFrontier cell h (start cell+jump cell) cell (seed++[eventName cell false,eventName cell true]))

theorem actual_initial (cell : Owner) (h : Factor) :
    initial (raw cell) PublicationResources.assignment (PublicationReplay.ready cell) h=startRun cell h := by
  cases cell
  · exact PublicationExecution.second_initializer (PublicationReplay.ready false) h
  · exact PublicationExecution.first_initializer (PublicationReplay.ready true) h

theorem actual_post_exit (cell : Owner) (h : Factor) :
    postExit (raw cell) PublicationResources.assignment (PublicationReplay.ready cell) h h
      (some (PublicationPhysical.arrivalRun cell h))=some (PublicationPhysical.entryRun cell h) := by
  have he := PublicationPhysical.actual_entry cell h
  simpa only [firstEntry,PublicationPhysical.actual_arrival] using he

theorem actual_episode (cell : Owner) (h : Factor) (seed : List String) :
    episode cell PublicationResources.assignment h seed=some (canonicalLeg cell h seed) := by
  have hp : PublicationResources.assignment cell=some (PublicationExecution.episodePair (round cell)) :=
    PublicationExecution.assigned_pair cell
  have ha : (PublicationResources.assignment cell).isSome=true := by rw [hp]; rfl
  have hr := PublicationPhysical.route_reader cell
  have hrecv : ((PublicationExecution.episodePair (round cell)).1.receiver.sourcePresent &&
      (PublicationExecution.episodePair (round cell)).1.receiver.targetFunded &&
      (PublicationExecution.episodePair (round cell)).1.receiver.funded)=true := by cases cell <;> rfl
  unfold episode
  rw [dif_pos ha]
  simp only [hp,bind,Option.bind_some,hrecv,ite_true,hr]
  have hrecipe : recipeGuard cell (PublicationExecution.episodePair (round cell)) [false,true]=true := by
    cases cell <;> rfl
  rw [hrecipe]
  simp only [ite_true]
  simp only [List.head?_cons,List.getLast?_cons,List.getLast?_nil,Option.getD_none,Option.getD_some,Option.bind_some]
  have hg : eventGuard cell (PublicationExecution.episodePair (round cell)) false true=true := by
    cases cell <;> rfl
  rw [hg]
  simp only [ite_true]
  rw [actual_initial,PublicationPhysical.source_terminal]
  simp only [Option.bind_some,PublicationPhysical.receive_terminal,actual_post_exit,Option.bind_some]
  have f0 := snapshot_frontier cell false h (start cell) seed
  have f1 := snapshot_frontier cell false h (start cell+(jump cell-1)) (seed++[eventName cell false])
  have f2 := snapshot_frontier cell true h (start cell+jump cell) (seed++[eventName cell false,eventName cell true])
  simp only [Bool.false_eq_true,ite_false,ite_true] at f0 f1 f2
  simp only [startRun,PublicationPhysical.terminalRun,PublicationPhysical.entryRun] at f0 f1 f2 ⊢
  simp only [f0,f1,f2,bind,pure,Option.bind_some]
  rfl


def initialSeed (a : Assignment Owner MemoryValue) (h : Factor) : Option (List String) :=
  ((ModeExecution.initializer true false 0 ()).eval a noRegisters h).map
    (fun x => x.1.residue.1.map seedName)

/-- The entire computed middle state, including incoming past and funding,
is compared against the independently interpreted next initializer. -/
noncomputable def middle (a : Assignment Owner MemoryValue) (h : Factor) : Option Bool :=
  if ha : (a true).isSome=true then do
    let actual ← firstEntry (raw true) a (acquisition_ready true false 0 1 a ha) h h
    let next ← (ModeExecution.initializer false true 2 ()).eval a noRegisters h
    pure (decide (actual ()=next))
  else none
noncomputable def chain (a : Assignment Owner MemoryValue) (h : Factor) : Option (List FiniteAtomicLeg) := do
  let seam ← middle a h
  if seam then
    let seed ← initialSeed a h
    let left ← episode true a h seed
    let right ← episode false a h (exit left).frontier.residue
    pure [left,right]
  else none

def seed (h : Factor) := [seedName h,seedName h]
def left (h : Factor) := canonicalLeg true h (seed h)
def right (h : Factor) := canonicalLeg false h ((exit (left h)).frontier.residue)

theorem actual_seed (h : Factor) : initialSeed PublicationResources.assignment h=some (seed h) := by
  rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
theorem actual_middle (h : Factor) : middle PublicationResources.assignment h=some true := by
  unfold middle
  rw [dif_pos (show (PublicationResources.assignment true).isSome=true from rfl),PublicationPhysical.actual_entry]
  have hi : (ModeExecution.initializer false true 2 ()).eval PublicationResources.assignment noRegisters h=
      some (PublicationExecution.snapshot h 4 2 true ()) := by
    rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
  simp [hi,PublicationPhysical.entryRun,jump,start,copies]
theorem actual_chain (h : Factor) : chain PublicationResources.assignment h=some [left h,right h] := by
  simp [chain,actual_middle,actual_seed,actual_episode,left,right]

theorem first_leg_pass (h : Factor) : AtomicLegPass (left h) := by
  unfold AtomicLegPass
  rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> decide +kernel
theorem second_leg_pass (h : Factor) : AtomicLegPass (right h) := by
  unfold AtomicLegPass
  rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> decide +kernel
theorem full_frontier_seam (h : Factor) : AdjacentFrontierCheck (left h) (right h)=true := by
  rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> decide +kernel
theorem carrier_chain (h : Factor) :
    (left h).source=17 ∧ (left h).target=55 ∧ (right h).source=55 ∧ (right h).target=101 :=
  ⟨rfl,rfl,rfl,rfl⟩
theorem strict_corridor (h : Factor) : StrictCorridorWitness [left h,right h] := by
  apply strictTemporalCorridorComposition_generic
  refine ⟨by simp,?_,?_⟩
  · have hl : AtomicLegCheck (left h)=true := first_leg_pass h
    have hr : AtomicLegCheck (right h)=true := second_leg_pass h
    simp only [chainCheck,hl,hr,full_frontier_seam,Bool.and_self]
  · change (some 17 : Option Nat)≠some 101
    decide +kernel

def Readout (a : Assignment Owner MemoryValue) (h : Factor) : Prop :=
  ∃ legs, chain a h=some legs ∧ StrictCorridorWitness legs
theorem actual_readout (h : Factor) : Readout PublicationResources.assignment h :=
  ⟨[left h,right h],actual_chain h,strict_corridor h⟩

theorem missing_first (a : Assignment Owner MemoryValue) (hm : a true=none) (h : Factor) :
    ¬ Readout a h := by
  rintro ⟨legs,he,_⟩
  simp [chain,middle,hm] at he
theorem missing_second (a : Assignment Owner MemoryValue) (hm : a false=none) (h : Factor) :
    ¬ Readout a h := by
  rintro ⟨legs,he,_⟩
  have hi : (ModeExecution.initializer false true 2 ()).eval a noRegisters h=none := by
    simp [ModeExecution.initializer,Expr.eval,hm]
  have hs : middle a h=none := by
    unfold middle
    split
    · cases firstEntry (raw true) a _ h h <;> simp [hi]
    · rfl
  simp [chain,hs] at he


theorem cut_episode (cell : Owner) (a : Assignment Owner MemoryValue) (h : Factor) (seed : List String) :
    episode cell (PublicationReceiver.cutAt cell a) h seed=none := by
  cases hp : a cell with
  | none => apply missing_episode; simp [PublicationReceiver.cutAt,hp]
  | some p =>
    apply inactive_episode cell _ (PublicationReceiver.cutSource p)
    · simp [PublicationReceiver.cutAt,hp]
    · rfl

theorem failed_first_episode (a : Assignment Owner MemoryValue) (h : Factor)
    (hf : ∀ seed, episode true a h seed=none) : ¬ Readout a h := by
  rintro ⟨legs,he,_⟩
  cases hs : middle a h with
  | none => simp [chain,hs] at he
  | some b => cases b <;> simp [chain,hs,hf] at he

theorem failed_second_episode (a : Assignment Owner MemoryValue) (h : Factor)
    (hf : ∀ seed, episode false a h seed=none) : ¬ Readout a h := by
  rintro ⟨legs,he,_⟩
  cases hs : middle a h with
  | none => simp [chain,hs] at he
  | some b => cases b <;> simp [chain,hs,hf] at he

theorem cut_readout (cell : Owner) (a : Assignment Owner MemoryValue) (h : Factor) :
    ¬ Readout (PublicationReceiver.cutAt cell a) h := by
  cases cell
  · exact failed_second_episode _ h (fun seed => cut_episode false a h seed)
  · exact failed_first_episode _ h (fun seed => cut_episode true a h seed)

theorem physical_clocks (h : Factor) :
    (left h).stages.map (fun s => s.frontier.order)=[0,1,2] ∧
    (right h).stages.map (fun s => s.frontier.order)=[2,5,6] ∧
    (left h).stages.map (fun s => s.frontier.owner)=[17,17,55] ∧
    (right h).stages.map (fun s => s.frontier.owner)=[55,55,101] := ⟨rfl,rfl,rfl,rfl⟩

theorem executed_residue (h : Factor) :
    (left h).stages.map (fun s => s.frontier.residue)=
      [seed h,seed h++[eventName true false],seed h++[eventName true false,eventName true true]] ∧
    (exit (right h)).frontier.residue=
      seed h++[eventName true false,eventName true true,eventName false false,eventName false true] := by
  constructor
  · rfl
  · simp [right,left,canonicalLeg,construct,exit,stage,snapshotFrontier,List.append_assoc]

theorem computed_route_status (h : Factor) :
    routeStatusOf (left h)=.routeIndexed ∧ routeStatusOf (right h)=.routeIndexed := by
  rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> decide +kernel


theorem predictive_code_faithful (cell : Owner) (s t : Factor) :
    predictiveCode (TemporalFactorRules.prediction (factorSchema (swapOwner cell))
        (PublicationExecution.episodePair (round cell)).2.temporal s)=
      predictiveCode (TemporalFactorRules.prediction (factorSchema (swapOwner cell))
        (PublicationExecution.episodePair (round cell)).2.temporal t) ↔
    TemporalFactorRules.prediction (factorSchema (swapOwner cell))
        (PublicationExecution.episodePair (round cell)).2.temporal s=
      TemporalFactorRules.prediction (factorSchema (swapOwner cell))
        (PublicationExecution.episodePair (round cell)).2.temporal t := by
  cases cell
  all_goals rcases s with ⟨p,v,j⟩; rcases t with ⟨q,w,k⟩
  all_goals cases p <;> cases v <;> cases j <;> cases q <;> cases w <;> cases k <;> decide +kernel


theorem disabled_event_episode (cell : Owner) (a : Assignment Owner MemoryValue) (p : Input × Input)
    (hp : a cell=some p) (hg : ∀ first last, eventGuard cell p first last=false)
    (h : Factor) (seed : List String) : episode cell a h seed=none := by
  have ha : (a cell).isSome=true := by rw [hp]; rfl
  unfold episode
  rw [dif_pos ha]
  simp only [hp,bind,Option.bind_some]
  split
  · cases hr : (raw cell).routes.read a with
    | none => simp
    | some routes =>
      simp only [Option.bind_some]
      split
      · cases hf : (routes h).path.head? with
        | none => simp
        | some first =>
          simp only [Option.bind_some]
          cases hl : (routes h).path.getLast? with
          | none => simp
          | some last => simp [hg]
      · rfl
  · rfl

theorem disabled_events_no_readout (cell : Owner) (a : Assignment Owner MemoryValue)
    (p : Input × Input) (hp : a cell=some p)
    (hg : ∀ first last, eventGuard cell p first last=false) (h : Factor) : ¬ Readout a h := by
  cases cell
  · exact failed_second_episode a h (fun seed => disabled_event_episode false a p hp hg h seed)
  · exact failed_first_episode a h (fun seed => disabled_event_episode true a p hp hg h seed)

theorem guard_requires_flags (cell : Owner) (p : Input × Input) (first last : Bool)
    (hg : eventGuard cell p first last=true) :
    (acquisitionEvents (start cell) (stride cell) p first).atomic=true ∧
    (acquisitionEvents (start cell) (stride cell) p first).strictStep=true ∧
    (acquisitionEvents (start cell) (stride cell) p last).atomic=true ∧
    (acquisitionEvents (start cell) (stride cell) p last).strictStep=true := by
  simpa only [eventGuard,Bool.and_eq_true,and_assoc] using hg


def eraseEvent (atomic : Bool) (e : TemporalFactorRules.Event Stage Bool) : TemporalFactorRules.Event Stage Bool :=
  if atomic then {e with atomic := false} else {e with strictStep := false}
def eraseFlag (atomic : Bool) (p : Input × Input) : Input × Input :=
  (p.1,{p.2 with temporal := {p.2.temporal with events := p.2.temporal.events.map (eraseEvent atomic)}})

theorem erased_flag (atomic cell : Bool) (p : Input × Input) (id : Bool) :
    (if atomic then (acquisitionEvents (start cell) (stride cell) (eraseFlag atomic p) id).atomic
      else (acquisitionEvents (start cell) (stride cell) (eraseFlag atomic p) id).strictStep)=false := by
  unfold acquisitionEvents
  cases he : TemporalFactorRules.event (eraseFlag atomic p).2.temporal id with
  | none => cases atomic <;> rfl
  | some e =>
    have hm : e ∈ (eraseFlag atomic p).2.temporal.events := List.mem_of_find?_eq_some he
    change e ∈ p.2.temporal.events.map (eraseEvent atomic) at hm
    obtain ⟨original,_,rfl⟩ := List.mem_map.mp hm
    cases atomic <;> rfl

theorem erased_guard (atomic cell : Bool) (p : Input × Input) (first last : Bool) :
    eventGuard cell (eraseFlag atomic p) first last=false := by
  have he := erased_flag atomic cell p first
  cases atomic <;> simp only [Bool.false_eq_true,ite_false,ite_true] at he
  · simp [eventGuard,he]
  · simp [eventGuard,he]

def eraseFlagAt (atomic cell : Bool) (a : Assignment Owner MemoryValue) : Assignment Owner MemoryValue :=
  fun o => if o=cell then (a o).map (eraseFlag atomic) else a o

theorem erased_flag_no_readout (atomic cell : Bool) (a : Assignment Owner MemoryValue) (h : Factor) :
    ¬ Readout (eraseFlagAt atomic cell a) h := by
  cases hp : a cell with
  | none =>
    have hm : eraseFlagAt atomic cell a cell=none := by simp [eraseFlagAt,hp]
    cases cell
    · exact missing_second _ hm h
    · exact missing_first _ hm h
  | some p =>
    apply disabled_events_no_readout cell _ (eraseFlag atomic p)
    · simp [eraseFlagAt,hp]
    · exact erased_guard atomic cell p


end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationCorridor
