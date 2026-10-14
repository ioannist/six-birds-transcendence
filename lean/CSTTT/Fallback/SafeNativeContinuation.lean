import CSTTT.Fallback.NativeReceiptExecution

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeSafeClosurePrototype
open RegisterInterpreter NativeReceiptExtensionPrototype NativeTwoHopReceiptPrototype
open NativeAcquiredWithdrawalPrototype (ContinuationLaw)
set_option autoImplicit false

-- Class (b): commands select the already established constant safe controller.
-- This predicate restricts proposed raw actions, not their computed success.
def SafeCommand : Command → Prop
  | .advance _ _ action _ => action=false
  | .fission _ _ _ => True
def SafeCommands (commands : List Command) : Prop := ∀ command∈commands, SafeCommand command
-- Every live, actually present register must retain its own continuation laws.
-- This is an induction predicate, never an input to the raw interpreter.
def LiveLaw (affected : Owner) (world : World) : Prop :=
  ∀ address state, world.active address=true → world.read address=some state →
    (state ()).2=false ∧ ContinuationLaw affected false state

-- Rebase on ANY genuinely executed prefix; constancy makes the strategy agree.
theorem safe_play_append
    (rows : StrategyGame.Rows ModeExecution.Registers Unit Bool Factor)
    (update : StrategyGame.Updater ModeExecution.Registers Unit Bool Factor)
    (entry next : ModeExecution.Registers) (prior later : List ModeExecution.Registers)
    (prefixPlay : StrategyGame.Play rows update PublicationResources.safeController entry (next::prior))
    (laterPlay : StrategyGame.Play rows update PublicationResources.safeController next later) :
    StrategyGame.Play rows update PublicationResources.safeController entry (later++prior) := by
  induction laterPlay with
  | initial => exact prefixPlay
  | @step state past earlier disturbance outcome supported ih =>
    change StrategyGame.Play rows update PublicationResources.safeController entry
      (update state disturbance false outcome :: state :: (past++prior))
    exact StrategyGame.Play.step ih disturbance outcome supported

theorem continuation_at_play (affected : Owner) (entry state : ModeExecution.Registers)
    (law : ContinuationLaw affected false entry) (past : List ModeExecution.Registers)
    (played : StrategyGame.Play
      (ResourceRuntime.rows (PublicationResources.runtime false) (NativePackageBundle.nativeInputs (withdrawnCurrent affected)))
      (ResourceRuntime.update (PublicationResources.runtime false) (NativePackageBundle.nativeInputs (withdrawnCurrent affected))
        (withdrawnReady affected)) PublicationResources.safeController entry (state::past)) :
    ContinuationLaw affected false state := by
  intro later history play
  exact law later (history++past) (safe_play_append _ _ entry state past (later::history) played play)

theorem continuation_after_supported_update (affected : Owner) (state : ModeExecution.Registers)
    (law : ContinuationLaw affected false state) (outcome : Factor)
    (support : StrategyGame.PositiveSupport (ResourceRuntime.rows (PublicationResources.runtime false)
      (NativePackageBundle.nativeInputs (withdrawnCurrent affected))) state () false outcome) :
    ContinuationLaw affected false
      (ResourceRuntime.update (PublicationResources.runtime false) (NativePackageBundle.nativeInputs (withdrawnCurrent affected))
        (withdrawnReady affected) state () false outcome) := by
  apply continuation_at_play affected state _ law [state]
  exact StrategyGame.Play.step StrategyGame.Play.initial () outcome support

theorem actual_updater_mode (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (state : ModeExecution.Registers) (action : Bool) (outcome : Factor) :
    (ResourceRuntime.update (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current) ready state () action outcome ()).2
      =(state ()).2 := by
  have present := (PublicationResources.ready_iff false _).mp ready
  cases assigned : current false with
  | none => simp [NativePackageBundle.nativeInputs,assigned] at present
  | some pair =>
    have input : NativePackageBundle.nativeInputs current false=some (pair.1.native,pair.2.native) := by
      simp [NativePackageBundle.nativeInputs,assigned]
    have evaluation := ModeExecution.mode_update_evaluation false true (NativePackageBundle.nativeInputs current)
      (pair.1.native,pair.2.native) input state () action outcome
    have execution := checked_execute_eq (PublicationResources.runtime false).execution.program
      (NativePackageBundle.nativeInputs current) ready.2.1 state ((),action,outcome) ()
    change (ModeExecution.updateExpr false true).eval (NativePackageBundle.nativeInputs current) state ((),action,outcome) =
      some (ResourceRuntime.update (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current) ready state () action outcome ()) at execution
    rw [evaluation] at execution
    exact (congrArg Prod.snd (Option.some.inj execution)).symm

theorem canonical_live_law (affected : Owner) (history : Factor) : LiveLaw affected (canonicalWorld history) := by
  intro address state active read
  have addressEq : address=4 := by simpa [canonicalWorld] using active
  subst address
  have stateEq : state=(canonicalReceipt false history).entry := (Option.some.inj read).symm
  subst state
  exact ⟨rfl,(canonical_final_continuation affected history).2⟩

theorem safe_step_live_law (affected : Owner) (world finished : World) (command : Command)
    (live : LiveLaw affected world) (safe : SafeCommand command)
    (accepted : step (withdrawnCurrent affected) (withdrawnReady affected) world command=some finished) :
    LiveLaw affected finished := by
  cases command with
  | advance parent target action outcome =>
    have actionEq : action=false := safe
    subst action
    obtain ⟨state,row,read,actual,mode,active,fresh,supported,rfl⟩ := (advance_some_exact _ _ _ _ _ _ _ _).mp accepted
    have law := (live parent state active read).2
    have positive : StrategyGame.PositiveSupport (ResourceRuntime.rows (PublicationResources.runtime false)
        (NativePackageBundle.nativeInputs (withdrawnCurrent affected))) state () false outcome := by
      simpa [StrategyGame.PositiveSupport,ResourceRuntime.rows,actual] using supported
    have nextLaw := continuation_after_supported_update affected state law outcome positive
    intro address next activeNext readNext
    by_cases equal : address=target
    · subst address
      have stateEq := Option.some.inj (by simpa [advanced,NativeReceiptExtensionPrototype.put] using readNext)
      subst next
      exact ⟨(actual_updater_mode _ _ _ _ _).trans mode,nextLaw⟩
    · exact live address next (by simpa [advanced,equal] using activeNext) (by simpa [advanced,NativeReceiptExtensionPrototype.put,equal] using readNext)
  | fission parent left right =>
    obtain ⟨state,read,mode,active,freshL,freshR,distinct,rfl⟩ := (fission_some_exact _ _ _ _ _ _ _).mp accepted
    have law := live parent state active read
    intro address next activeNext readNext
    by_cases copied : address=left ∨ address=right
    · have stateEq := Option.some.inj (by simpa [split,copied] using readNext)
      subst next
      exact law
    · exact live address next (by simpa [split,copied] using activeNext) (by simpa [split,copied] using readNext)

theorem safe_run_live_law (affected : Owner) (commands : List Command) (world finished : World)
    (live : LiveLaw affected world) (safe : SafeCommands commands)
    (accepted : run (withdrawnCurrent affected) (withdrawnReady affected) world commands=some finished) :
    LiveLaw affected finished := by
  induction commands generalizing world with
  | nil =>
    have equal : world=finished := Option.some.inj accepted
    subst finished
    exact live
  | cons command rest ih =>
    cases first : step (withdrawnCurrent affected) (withdrawnReady affected) world command with
    | none => simp [run,first] at accepted
    | some next =>
      apply ih next (safe_step_live_law affected world next command live (safe command (by simp)) first)
        (fun c member => safe c (by simp [member]))
      simpa [run,first] using accepted

theorem canonical_safe_continuation (affected : Owner) (history : Factor) (commands : List Command) (finished : World)
    (safe : SafeCommands commands)
    (accepted : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history commands=some finished) : LiveLaw affected finished := by
  apply safe_run_live_law affected commands (canonicalWorld history) finished (canonical_live_law affected history) safe
  simpa [extend,canonical_from_actual] using accepted

-- The original whole historical qualified package is returned at the actual live state.
theorem canonical_live_package (affected : Owner) (history : Factor) (commands : List Command) (finished : World)
    (safe : SafeCommands commands)
    (accepted : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history commands=some finished)
    (address : Nat) (state : ModeExecution.Registers) (active : finished.active address=true) (read : finished.read address=some state) :
    PostWithdrawalQualifiedPrototype.qualifiedPackageAt (withdrawnCurrent affected) false state ∧
      ContinuationLaw affected false state := by
  have law := (canonical_safe_continuation affected history commands finished safe accepted address state active read).2
  exact ⟨(law state [] StrategyGame.Play.initial).1,law⟩

theorem safe_advance_whole_law (affected : Owner) (world finished : World) (parent target : Nat) (outcome : Factor)
    (live : LiveLaw affected world)
    (accepted : step (withdrawnCurrent affected) (withdrawnReady affected) world (.advance parent target false outcome)=some finished) :
    ∃ state,world.read parent=some state ∧
      finished.read target=some (ResourceRuntime.update (PublicationResources.runtime false)
        (NativePackageBundle.nativeInputs (withdrawnCurrent affected)) (withdrawnReady affected) state () false outcome) ∧
      ResourceRuntime.StepLaw (PublicationResources.cfg false) (PublicationResources.runtime false)
        (NativePackageBundle.nativeInputs (withdrawnCurrent affected)) (withdrawnReady affected) state () false outcome := by
  obtain ⟨state,row,read,actual,mode,active,fresh,supported,rfl⟩ := (advance_some_exact _ _ _ _ _ _ _ _).mp accepted
  have positive : StrategyGame.PositiveSupport (ResourceRuntime.rows (PublicationResources.runtime false)
      (NativePackageBundle.nativeInputs (withdrawnCurrent affected))) state () false outcome := by
    simpa [StrategyGame.PositiveSupport,ResourceRuntime.rows,actual] using supported
  have laws := (live parent state active read).2 state [] StrategyGame.Play.initial
  exact ⟨state,read,by simp [advanced,NativeReceiptExtensionPrototype.put],(laws.2.2 ()).2.2 outcome positive⟩

-- A positive outcome is constructed from normalization at ANY actual live state.
theorem live_supported_advance (affected : Owner) (world : World) (live : LiveLaw affected world)
    (parent target : Nat) (state : ModeExecution.Registers)
    (active : world.active parent=true) (read : world.read parent=some state) (fresh : world.read target=none) :
    ∃ outcome finished,step (withdrawnCurrent affected) (withdrawnReady affected) world (.advance parent target false outcome)=some finished ∧
      LiveLaw affected finished ∧ ContinuationLaw affected false
        (ResourceRuntime.update (PublicationResources.runtime false) (NativePackageBundle.nativeInputs (withdrawnCurrent affected))
          (withdrawnReady affected) state () false outcome) := by
  have laws := live parent state active read
  obtain ⟨outcome,positive⟩ := ((laws.2 state [] StrategyGame.Play.initial).2.2 ()).2.1.2.2
  obtain ⟨row,actual,supported⟩ := positive_row_present (withdrawnCurrent affected) state false outcome positive
  let finished := advanced world parent target (ResourceRuntime.update (PublicationResources.runtime false)
    (NativePackageBundle.nativeInputs (withdrawnCurrent affected)) (withdrawnReady affected) state () false outcome)
  have accepted : step (withdrawnCurrent affected) (withdrawnReady affected) world (.advance parent target false outcome)=some finished :=
    (advance_some_exact _ _ _ _ _ _ _ _).mpr ⟨state,row,read,actual,laws.1,active,fresh,supported,rfl⟩
  exact ⟨outcome,finished,accepted,safe_step_live_law affected world finished (.advance parent target false outcome) live rfl accepted,
    continuation_after_supported_update affected state laws.2 outcome positive⟩

-- Activity inherits a closed property only through genuinely accepted edges.
theorem step_active_closed (affected : Owner) (world finished : World) (command : Command)
    (relation : Nat → Prop) (old : ∀ address,world.active address=true → relation address)
    (closed : ∀ parent target,(parent,target)∈commandEdges command → relation parent → relation target)
    (accepted : step (withdrawnCurrent affected) (withdrawnReady affected) world command=some finished) :
    ∀ address,finished.active address=true → relation address := by
  cases command with
  | advance parent target action outcome =>
    obtain ⟨state,row,read,actual,mode,active,fresh,supported,rfl⟩ := (advance_some_exact _ _ _ _ _ _ _ _).mp accepted
    intro address current
    by_cases equal : address=target
    · subst address
      exact closed parent target (by simp [commandEdges]) (old parent active)
    · exact old address (by simpa [advanced,equal] using current)
  | fission parent left right =>
    obtain ⟨state,read,mode,active,freshL,freshR,distinct,rfl⟩ := (fission_some_exact _ _ _ _ _ _ _).mp accepted
    intro address current
    by_cases leftEq : address=left
    · subst address
      exact closed parent left (by simp [commandEdges]) (old parent active)
    · by_cases rightEq : address=right
      · subst address
        exact closed parent right (by simp [commandEdges]) (old parent active)
      · exact old address (by simpa [split,leftEq,rightEq] using current)

theorem run_active_closed (affected : Owner) (commands : List Command) (world finished : World)
    (relation : Nat → Prop) (old : ∀ address,world.active address=true → relation address)
    (closed : ∀ parent target,(parent,target)∈ledger commands → relation parent → relation target)
    (accepted : run (withdrawnCurrent affected) (withdrawnReady affected) world commands=some finished) :
    ∀ address,finished.active address=true → relation address := by
  induction commands generalizing world with
  | nil =>
    have equal : world=finished := Option.some.inj accepted
    subst finished
    exact old
  | cons command rest ih =>
    cases first : step (withdrawnCurrent affected) (withdrawnReady affected) world command with
    | none => simp [run,first] at accepted
    | some next =>
      apply ih next (step_active_closed affected world next command relation old
        (fun parent target member related => closed parent target (by simp [ledger,member]) related) first)
        (fun parent target member related => closed parent target (by change (parent,target)∈commandEdges command++ledger rest; exact List.mem_append_right _ member) related)
      simpa [run,first] using accepted

theorem canonical_live_descendant (affected : Owner) (history : Factor) (commands : List Command) (finished : World)
    (accepted : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history commands=some finished) :
    ∀ address,finished.active address=true → Descendant (ledger commands) 4 address := by
  apply run_active_closed affected commands (canonicalWorld history) finished (Descendant (ledger commands) 4)
  · intro address active
    have equal : address=4 := by simpa [canonicalWorld] using active
    exact Or.inl equal.symm
  · intro parent target member related
    exact descendant_closed _ _ _ _ related member
  · simpa [extend,canonical_from_actual] using accepted

theorem canonical_live_ancestry (affected : Owner) (leftNames rightNames : Owner → CarrierId)
    (history : Factor) (commands : List Command) (finished : World)
    (accepted : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history commands=some finished) (address : Nat) (active : finished.active address=true) :
    ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
      (withdrawnReady affected) history commands 0 address=some true := by
  apply (ancestry_true_exact _ _ _ _ _ _ _ _ _ _).mpr
  refine ⟨canonicalWorld history,finished,canonical_from_actual history,?_,
    canonical_seed_retained affected leftNames rightNames history,rfl,?_⟩
  · simpa [extend,canonical_from_actual] using accepted
  · exact canonical_live_descendant affected history commands finished accepted address active

-- Same actual world, same actual current assignment, every finite safe stream.
theorem canonical_safe_live_return (affected : Owner) (leftNames rightNames : Owner → CarrierId)
    (history : Factor) (commands : List Command) (finished : World) (safe : SafeCommands commands)
    (accepted : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history commands=some finished)
    (address : Nat) (state : ModeExecution.Registers) (active : finished.active address=true) (read : finished.read address=some state) :
    ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
      (withdrawnReady affected) history commands 0 address=some true ∧
    PostWithdrawalQualifiedPrototype.qualifiedPackageAt (withdrawnCurrent affected) false state ∧
    ContinuationLaw affected false state :=
  ⟨canonical_live_ancestry affected leftNames rightNames history commands finished accepted address active,
    canonical_live_package affected history commands finished safe accepted address state active read⟩

theorem run_append_actual (affected : Owner) (commands suffix : List Command) (world : World) :
    run (withdrawnCurrent affected) (withdrawnReady affected) world (commands++suffix)=
      (run (withdrawnCurrent affected) (withdrawnReady affected) world commands).bind
        (fun next => run (withdrawnCurrent affected) (withdrawnReady affected) next suffix) := by
  induction commands generalizing world with
  | nil => simp [run]
  | cons command rest ih => simp [run,ih,Option.bind_assoc]

-- Nonvacuous further advancement from ANY actual live state of an accepted stream.
theorem canonical_further_advance (affected : Owner) (leftNames rightNames : Owner → CarrierId)
    (history : Factor) (commands : List Command) (world : World) (safe : SafeCommands commands)
    (accepted : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history commands=some world)
    (parent target : Nat) (state : ModeExecution.Registers)
    (active : world.active parent=true) (read : world.read parent=some state) (fresh : world.read target=none) :
    ∃ outcome finished,
      extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
        history (commands++[.advance parent target false outcome])=some finished ∧
      finished.read target=some (ResourceRuntime.update (PublicationResources.runtime false)
        (NativePackageBundle.nativeInputs (withdrawnCurrent affected)) (withdrawnReady affected) state () false outcome) ∧
      ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
        (withdrawnReady affected) history (commands++[.advance parent target false outcome]) 0 target=some true ∧
      ResourceRuntime.StepLaw (PublicationResources.cfg false) (PublicationResources.runtime false)
        (NativePackageBundle.nativeInputs (withdrawnCurrent affected)) (withdrawnReady affected) state () false outcome ∧
      ContinuationLaw affected false (ResourceRuntime.update (PublicationResources.runtime false)
        (NativePackageBundle.nativeInputs (withdrawnCurrent affected)) (withdrawnReady affected) state () false outcome) := by
  have live := canonical_safe_continuation affected history commands world safe accepted
  obtain ⟨outcome,finished,stepRead,finishedLive,nextLaw⟩ := live_supported_advance affected world live parent target state active read fresh
  obtain ⟨before,beforeRead,updated,whole⟩ := safe_advance_whole_law affected world finished parent target outcome live stepRead
  have equal : before=state := Option.some.inj (beforeRead.symm.trans read)
  subst before
  have actual : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history (commands++[.advance parent target false outcome])=some finished := by
    have base : run (withdrawnCurrent affected) (withdrawnReady affected) (canonicalWorld history) commands=some world := by
      simpa [extend,canonical_from_actual] using accepted
    simp [extend,canonical_from_actual,run_append_actual,base,run,stepRead]
  have activeNext : finished.active target=true := by
    obtain ⟨s,row,hr,ha,hm,hactive,hfresh,hs,rfl⟩ := (advance_some_exact _ _ _ _ _ _ _ _).mp stepRead
    simp [advanced]
  exact ⟨outcome,finished,actual,updated,
    canonical_live_ancestry affected leftNames rightNames history _ finished actual target activeNext,whole,nextLaw⟩

-- Fission after arbitrary successful updates copies their FULL updated registers.
theorem canonical_further_fission (affected : Owner) (leftNames rightNames : Owner → CarrierId)
    (history : Factor) (commands : List Command) (world : World) (safe : SafeCommands commands)
    (accepted : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history commands=some world)
    (parent left right : Nat) (state : ModeExecution.Registers)
    (active : world.active parent=true) (read : world.read parent=some state)
    (freshL : world.read left=none) (freshR : world.read right=none) (distinct : left≠right) :
    ∃ finished,
      extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
        history (commands++[.fission parent left right])=some finished ∧
      finished.read left=some state ∧ finished.read right=some state ∧
      ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
        (withdrawnReady affected) history (commands++[.fission parent left right]) 0 left=some true ∧
      ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
        (withdrawnReady affected) history (commands++[.fission parent left right]) 0 right=some true ∧
      PostWithdrawalQualifiedPrototype.qualifiedPackageAt (withdrawnCurrent affected) false state ∧
      ContinuationLaw affected false state := by
  have law := canonical_safe_continuation affected history commands world safe accepted parent state active read
  let finished := split world parent left right state
  have stepRead : step (withdrawnCurrent affected) (withdrawnReady affected) world (.fission parent left right)=some finished :=
    (fission_some_exact _ _ _ _ _ _ _).mpr ⟨state,read,law.1,active,freshL,freshR,distinct,rfl⟩
  have actual : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history (commands++[.fission parent left right])=some finished := by
    have base : run (withdrawnCurrent affected) (withdrawnReady affected) (canonicalWorld history) commands=some world := by
      simpa [extend,canonical_from_actual] using accepted
    simp [extend,canonical_from_actual,run_append_actual,base,run,stepRead]
  exact ⟨finished,actual,by simp [finished,split],by simp [finished,split],
    canonical_live_ancestry affected leftNames rightNames history _ finished actual left (by simp [finished,split]),
    canonical_live_ancestry affected leftNames rightNames history _ finished actual right (by simp [finished,split]),
    (law.2 state [] StrategyGame.Play.initial).1,law.2⟩

def FreshAbove (world : World) (bound : Nat) : Prop := ∀ address,bound<address → world.read address=none

-- Construct every finite length from actual normalized controller responses.
-- No accepted stream, intermediate state, or positive outcome is supplied.
theorem canonical_arbitrarily_long (affected : Owner) (history : Factor) (length : Nat) :
    ∃ commands finished state, SafeCommands commands ∧ commands.length=length ∧
      extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
        history commands=some finished ∧
      finished.active (4+length)=true ∧ finished.read (4+length)=some state ∧ FreshAbove finished (4+length) := by
  induction length with
  | zero =>
    refine ⟨[],canonicalWorld history,(canonicalReceipt false history).entry,by simp [SafeCommands],rfl,?_,rfl,rfl,?_⟩
    · simp [extend,canonical_from_actual,run]
    · intro address greater
      exact (canonical_fresh_exact history address).mpr greater
  | succ length ih =>
    obtain ⟨commands,world,state,safe,size,actual,active,read,fresh⟩ := ih
    have live := canonical_safe_continuation affected history commands world safe actual
    obtain ⟨outcome,finished,first,finishedLive,nextLaw⟩ :=
      live_supported_advance affected world live (4+length) (4+(length+1)) state active read (fresh _ (by omega))
    obtain ⟨s,row,parentRead,rowRead,mode,parentActive,targetFresh,positive,shape⟩ := (advance_some_exact _ _ _ _ _ _ _ _).mp first
    have stateEq : s=state := Option.some.inj (parentRead.symm.trans read)
    subst s
    let next := ResourceRuntime.update (PublicationResources.runtime false)
      (NativePackageBundle.nativeInputs (withdrawnCurrent affected)) (withdrawnReady affected) state () false outcome
    have extended : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
        history (commands++[.advance (4+length) (4+(length+1)) false outcome])=some finished := by
      have base : run (withdrawnCurrent affected) (withdrawnReady affected) (canonicalWorld history) commands=some world := by
        simpa [extend,canonical_from_actual] using actual
      simp [extend,canonical_from_actual,run_append_actual,base,run,first]
    refine ⟨commands++[.advance (4+length) (4+(length+1)) false outcome],finished,next,?_,?_,extended,?_,?_,?_⟩
    · intro command member
      simp only [List.mem_append,List.mem_singleton] at member
      rcases member with old|rfl
      · exact safe command old
      · rfl
    · simp [size]
    · simp [shape,advanced]
    · simp [shape,advanced,NativeReceiptExtensionPrototype.put,next]
    · intro address greater
      have different : address≠4+(length+1) := by omega
      simpa [shape,advanced,NativeReceiptExtensionPrototype.put,different] using fresh address (by omega)

-- Arbitrarily many actual advances followed by genuine copied branching.
-- Every returned branch retains the whole historical qualified package and
-- its own full continuation game, while resource accounts remain shared.
theorem canonical_arbitrary_length_fission (affected : Owner) (leftNames rightNames : Owner → CarrierId)
    (history : Factor) (length : Nat) :
    ∃ commands finished state,
      SafeCommands commands ∧ commands.length=length+1 ∧
      extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
        history commands=some finished ∧
      finished.read (5+length)=some state ∧ finished.read (6+length)=some state ∧
      ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
        (withdrawnReady affected) history commands 0 (5+length)=some true ∧
      ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
        (withdrawnReady affected) history commands 0 (6+length)=some true ∧
      PostWithdrawalQualifiedPrototype.qualifiedPackageAt (withdrawnCurrent affected) false state ∧
      ContinuationLaw affected false state := by
  obtain ⟨commands,world,state,safe,size,actual,active,read,fresh⟩ := canonical_arbitrarily_long affected history length
  obtain ⟨finished,extended,leftRead,rightRead,leftSeed,rightSeed,package,law⟩ :=
    canonical_further_fission affected leftNames rightNames history commands world safe actual
      (4+length) (5+length) (6+length) state active read (fresh _ (by omega)) (fresh _ (by omega)) (by omega)
  refine ⟨commands++[.fission (4+length) (5+length) (6+length)],finished,state,?_,?_,extended,
    leftRead,rightRead,leftSeed,rightSeed,package,law⟩
  · intro command member
    simp only [List.mem_append,List.mem_singleton] at member
    rcases member with old|rfl
    · exact safe command old
    · trivial
  · simp [size]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeSafeClosurePrototype
