import CSTTT.Fallback.PackageIndependence

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeReceiptExtensionPrototype
open RegisterInterpreter NativeTwoHopReceiptPrototype
open CSTTT.FallbackTheory.OperationalTrace
set_option autoImplicit false
-- Class (b): a phase-addressed view retains complete actual registers, not just their predictive factor.
structure World where
  read : Nat → Option ModeExecution.Registers
  active : Nat → Bool
  edges : List (Nat × Nat)
  source : Nat
  entry : Nat
-- All five occupied phases are derived from the two actual executed event lists.
-- No snapshot/capture record is invented. Phase addresses are not physical clocks.
noncomputable def phaseWorld (pair : ReceiptPair) : Option World := by
  classical
  exact match pair.left.edges,pair.right.edges with
  | [(s,m),(m',j)],[(u,n),(n',t)] =>
      if m=m' ∧ n=n' ∧ u≤j then
        let offset := j-u
        let finish := t+offset
        let slots := [(s,pair.left.initial),(m,pair.left.terminal),(j,pair.left.entry),
          (n+offset,pair.right.terminal),(finish,pair.right.entry)]
        if (slots.map Prod.fst).Nodup then
          some ⟨fun k => (slots.find? (fun e => e.1=k)).map Prod.snd,
            fun k => decide (k=finish),pair.edges,s,finish⟩
        else none
      else none
  | _,_ => none
noncomputable def fromActual (acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) : Option World := (execute acquired ready history).bind phaseWorld
-- Actual row proposals and literal copying are the only extension commands.
inductive Command where
  | advance (parent target : Nat) (action : Bool) (outcome : Factor)
  | fission (parent left right : Nat)
def put (world : World) (key : Nat) (value : ModeExecution.Registers) : Nat → Option ModeExecution.Registers :=
  fun k => if k=key then some value else world.read k
def advanced (world : World) (parent target : Nat) (next : ModeExecution.Registers) : World :=
  ⟨put world target next,(fun k => if k=target then true else world.active k),
    (parent,target)::world.edges,world.source,world.entry⟩
def split (world : World) (parent left right : Nat) (state : ModeExecution.Registers) : World :=
  ⟨(fun k => if k=left ∨ k=right then some state else world.read k),
    (fun k => if k=left ∨ k=right then true else world.active k),
    (parent,left)::(parent,right)::world.edges,world.source,world.entry⟩
-- This guard reads the actual optional row; it never uses the rows helper's missing-row default.
noncomputable def step (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (world : World) : Command → Option World := by
  classical
  exact fun command => match command with
  | .advance parent target action outcome => do
      let state ← world.read parent
      let row ← (PublicationResources.runtime false).execution.row.eval (NativePackageBundle.nativeInputs current) state ((),action)
      if (state ()).2=false ∧ world.active parent=true ∧ world.read target=none ∧ ∃ weight,(outcome,weight)∈row ∧ 0<weight then
        some (advanced world parent target
          (ResourceRuntime.update (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current) ready state () action outcome))
      else none
  | .fission parent left right => do
      let state ← world.read parent
      if (state ()).2=false ∧ world.active parent=true ∧ world.read left=none ∧ world.read right=none ∧ left≠right then
        some (split world parent left right state)
      else none
-- Fission copies the full native state. It does not assert disjoint ownership of the two copies' resource accounts.
noncomputable def run (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current)) :
    World → List Command → Option World
  | world,[] => some world
  | world,command::rest => (step current ready world command).bind (fun next => run current ready next rest)
noncomputable def extend (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) : Option World :=
  (fromActual acquired acquiredReady history).bind (fun world => run current currentReady world commands)
-- All-partial failures propagate before any native command can manufacture a world.
theorem failed_acquisition_rejects (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) (missing : execute acquired acquiredReady history=none) :
    extend current acquired acquiredReady currentReady history commands=none := by
  simp [extend,fromActual,missing]
-- Canonical frame is a readback of existing published interpreter states, with every interior phase occupied.
noncomputable def canonicalWorld (history : Factor) : World :=
  let left := canonicalReceipt true history
  let right := canonicalReceipt false history
  let slots := [(0,left.initial),(1,left.terminal),(2,left.entry),(3,right.terminal),(4,right.entry)]
  ⟨fun k => (slots.find? (fun e => e.1=k)).map Prod.snd,fun k => decide (k=4),[(0,1),(1,2),(2,3),(3,4)],0,4⟩
theorem canonical_from_actual (history : Factor) :
    fromActual NativePackageBundle.canonical PublicationReplay.ready history=some (canonicalWorld history) := by
  rw [fromActual,canonical_two_hop]
  simp only [Option.bind_some,phaseWorld]
  rfl
theorem canonical_phase_reads (history : Factor) :
    (canonicalWorld history).read 0=some (canonicalReceipt true history).initial ∧
    (canonicalWorld history).read 1=some (canonicalReceipt true history).terminal ∧
    (canonicalWorld history).read 2=some (canonicalReceipt true history).entry ∧
    (canonicalWorld history).read 3=some (canonicalReceipt false history).terminal ∧
    (canonicalWorld history).read 4=some (canonicalReceipt false history).entry ∧
    (canonicalReceipt true history).entry=(canonicalReceipt false history).initial := by
  exact ⟨rfl,rfl,rfl,rfl,rfl,actual_middle history⟩
theorem canonical_fresh_exact (history : Factor) (address : Nat) :
    (canonicalWorld history).read address=none ↔ 4<address := by
  simp only [canonicalWorld]
  cases address with
  | zero => simp
  | succ a => cases a with
    | zero => simp
    | succ b => cases b with
      | zero => simp
      | succ c => cases c with
        | zero => simp
        | succ d => cases d with
          | zero => simp
          | succ e => simp

-- Exact success conditions use the optional row and the entire actual updater.
theorem advance_some_exact (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (world finished : World) (parent target : Nat) (action : Bool) (outcome : Factor) :
    step current ready world (.advance parent target action outcome)=some finished ↔ ∃ state row,
      world.read parent=some state ∧
      (PublicationResources.runtime false).execution.row.eval (NativePackageBundle.nativeInputs current) state ((),action)=some row ∧
      (state ()).2=false ∧ world.active parent=true ∧ world.read target=none ∧ (∃ weight,(outcome,weight)∈row ∧ 0<weight) ∧
      finished=advanced world parent target (ResourceRuntime.update (PublicationResources.runtime false)
        (NativePackageBundle.nativeInputs current) ready state () action outcome) := by
  classical
  cases read : world.read parent with
  | none => simp [step,read]
  | some state =>
    cases row : (PublicationResources.runtime false).execution.row.eval (NativePackageBundle.nativeInputs current) state ((),action) with
    | none => simp [step,read,row]
    | some entries =>
      by_cases guard : (state ()).2=false ∧ world.active parent=true ∧ world.read target=none ∧ ∃ weight,(outcome,weight)∈entries ∧ 0<weight
      · simp [step,read,row,guard]
        exact eq_comm
      · simp [step,read,row,guard]
        intro mode a b weight member positive _
        exact guard ⟨mode,a,b,⟨weight,member,positive⟩⟩
theorem fission_some_exact (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (world finished : World) (parent left right : Nat) :
    step current ready world (.fission parent left right)=some finished ↔ ∃ state,
      world.read parent=some state ∧ (state ()).2=false ∧ world.active parent=true ∧ world.read left=none ∧ world.read right=none ∧
      left≠right ∧ finished=split world parent left right state := by
  classical
  cases read : world.read parent with
  | none => simp [step,read]
  | some state =>
    by_cases guard : (state ()).2=false ∧ world.active parent=true ∧ world.read left=none ∧ world.read right=none ∧ left≠right
    · simp [step,read,guard]
      exact eq_comm
    · simp [step,read,guard]
      exact fun mode a b c d _ => guard ⟨mode,a,b,c,d⟩
-- Direct raw row failure excludes actual advancement; no default zero row is counted as an observation.
theorem missing_row_rejected (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (world : World) (parent target : Nat) (action : Bool) (outcome : Factor) (state : ModeExecution.Registers)
    (read : world.read parent=some state)
    (missing : (PublicationResources.runtime false).execution.row.eval (NativePackageBundle.nativeInputs current) state ((),action)=none) :
    step current ready world (.advance parent target action outcome)=none := by simp [step,read,missing]
theorem positive_row_present (current : Assignment Owner NativePackageBundle.Value)
    (state : ModeExecution.Registers) (action : Bool) (outcome : Factor)
    (supported : StrategyGame.PositiveSupport (ResourceRuntime.rows (PublicationResources.runtime false)
      (NativePackageBundle.nativeInputs current)) state () action outcome) :
    ∃ row,(PublicationResources.runtime false).execution.row.eval (NativePackageBundle.nativeInputs current) state ((),action)=some row ∧
      ∃ weight,(outcome,weight)∈row ∧ 0<weight := by
  unfold StrategyGame.PositiveSupport ResourceRuntime.rows at supported
  cases row : (PublicationResources.runtime false).execution.row.eval (NativePackageBundle.nativeInputs current) state ((),action) with
  | none => simp [row] at supported
  | some entries => exact ⟨entries,rfl,by simpa [row] using supported⟩
-- Every successful step preserves old paths and adds only its declared primitive edges.
def commandEdges : Command → List (Nat × Nat)
  | .advance parent target _ _ => [(parent,target)]
  | .fission parent left right => [(parent,left),(parent,right)]
def ledger (commands : List Command) : List (Nat × Nat) := commands.flatMap commandEdges
theorem step_edges_exact (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (world finished : World) (command : Command) (accepted : step current ready world command=some finished) :
    finished.edges=commandEdges command++world.edges := by
  cases command with
  | advance parent target action outcome =>
    obtain ⟨state,row,read,hr,mode,active,fresh,supported,rfl⟩ := (advance_some_exact _ _ _ _ _ _ _ _).mp accepted
    rfl
  | fission parent left right =>
    obtain ⟨state,read,mode,active,freshL,freshR,distinct,rfl⟩ := (fission_some_exact _ _ _ _ _ _ _).mp accepted
    rfl
theorem step_paths (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (world finished : World) (command : Command) (accepted : step current ready world command=some finished)
    (source target : Nat) (path : Path world.edges source target) : Path finished.edges source target := by
  apply CSTTT.FallbackTheory.NativeDescendant.path_inclusion _ _ _ _ _ path
  rw [step_edges_exact _ _ _ _ _ accepted]
  exact fun edge member => List.mem_append_right _ member
theorem actual_fission_return (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (world finished : World) (source parent left right : Nat) (path : Path world.edges source parent)
    (accepted : step current ready world (.fission parent left right)=some finished) :
    Path finished.edges source left ∧ Path finished.edges source right ∧ finished.read left=finished.read right ∧
      finished.active left=true ∧ finished.active right=true := by
  obtain ⟨state,read,mode,active,freshL,freshR,distinct,rfl⟩ := (fission_some_exact _ _ _ _ _ _ _).mp accepted
  have retained := step_paths _ _ _ _ _ accepted source parent path
  exact ⟨.extend retained (by simp [split]),.extend retained (by simp [split]),by simp [split],by simp [split],by simp [split]⟩
-- Freshness checks include every actual historical phase, so a command cannot overwrite an unexposed interior node.
theorem historical_phase_overwrite_rejected (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (address : Nat) (bound : address≤4) (action : Bool) (outcome : Factor) :
    step current ready (canonicalWorld history) (.advance 4 address action outcome)=none := by
  classical
  have occupied : (canonicalWorld history).read address≠none := fun eq => by
    have greater := (canonical_fresh_exact history address).mp eq
    omega
  simp only [step,show (canonicalWorld history).read 4=some (canonicalReceipt false history).entry from rfl,
    bind,Option.bind_some]
  cases row : (PublicationResources.runtime false).execution.row.eval (NativePackageBundle.nativeInputs current)
    (canonicalReceipt false history).entry ((),action) <;> simp [occupied]

-- Every edge used by a continuation has actually passed its full native step guard.
theorem run_edges_realized (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (commands : List Command) (world finished : World) (accepted : run current ready world commands=some finished) :
    (∀ edge∈world.edges,edge∈finished.edges) ∧ (∀ edge∈ledger commands,edge∈finished.edges) := by
  induction commands generalizing world with
  | nil =>
    have equal : world=finished := Option.some.inj accepted
    subst finished
    exact ⟨fun _ h => h,by simp [ledger]⟩
  | cons command rest ih =>
    cases first : step current ready world command with
    | none => simp [run,first] at accepted
    | some next =>
      have tail : run current ready next rest=some finished := by simpa [run,first] using accepted
      have realized := ih next tail
      have shape := step_edges_exact current ready world next command first
      refine ⟨?_,?_⟩
      · intro edge member
        exact realized.1 edge (by rw [shape]; exact List.mem_append_right _ member)
      · intro edge member
        simp only [ledger,List.flatMap_cons,List.mem_append] at member
        rcases member with head|tail
        · exact realized.1 edge (by rw [shape]; exact List.mem_append_left _ head)
        · exact realized.2 edge tail
-- Reflexivity is permitted only AFTER a positive actual acquisition seed.
def Descendant (edges : List (Nat × Nat)) (entry target : Nat) : Prop := entry=target ∨ Path edges entry target
theorem descendant_closed (edges : List (Nat × Nat)) (entry parent target : Nat)
    (related : Descendant edges entry parent) (edge : (parent,target)∈edges) : Descendant edges entry target := by
  rcases related with rfl|path
  · exact Or.inr (.one edge)
  · exact Or.inr (.extend path edge)
theorem descendant_least (edges : List (Nat × Nat)) (entry : Nat) (relation : Nat → Prop)
    (seed : relation entry) (closed : ∀ parent target,relation parent → (parent,target)∈edges → relation target) :
    ∀ target,Descendant edges entry target → relation target := by
  intro target related
  rcases related with rfl|path
  · exact seed
  · induction path with
    | one member => exact closed _ _ seed member
    | extend previous member ih => exact closed _ _ ih member
-- Actual acquisition, actual raw Seed and actual accepted commands are all recomputed from primitive assignments.
noncomputable def ancestryDecision (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) (source target : Nat) : Option Bool := do
  let world ← fromActual acquired acquiredReady history
  let _ ← run current currentReady world commands
  let seed ← retainedDecision leftNames rightNames current acquired acquiredReady history world.source world.entry
  some (decide (source=world.source) && seed &&
    (decide (target=world.entry) || CSTTT.FallbackTheory.ExecutableSeed.pathBit (ledger commands) world.entry target))
theorem ancestry_some_exact (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) (source target : Nat) (value : Bool) :
    ancestryDecision leftNames rightNames current acquired acquiredReady currentReady history commands source target=some value ↔
    ∃ world finished seed,fromActual acquired acquiredReady history=some world ∧
      run current currentReady world commands=some finished ∧
      retainedDecision leftNames rightNames current acquired acquiredReady history world.source world.entry=some seed ∧
      value=(decide (source=world.source) && seed &&
        (decide (target=world.entry) || CSTTT.FallbackTheory.ExecutableSeed.pathBit (ledger commands) world.entry target)) := by
  simp only [ancestryDecision,bind,Option.bind_eq_some_iff,Option.some.injEq]
  constructor
  · rintro ⟨world,hw,finished,hf,seed,hs,eq⟩; exact ⟨world,finished,seed,hw,hf,hs,eq.symm⟩
  · rintro ⟨world,finished,seed,hw,hf,hs,eq⟩; exact ⟨world,hw,finished,hf,seed,hs,eq.symm⟩
theorem ancestry_true_exact (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) (source target : Nat) :
    ancestryDecision leftNames rightNames current acquired acquiredReady currentReady history commands source target=some true ↔
    ∃ world finished,fromActual acquired acquiredReady history=some world ∧ run current currentReady world commands=some finished ∧
      retainedDecision leftNames rightNames current acquired acquiredReady history world.source world.entry=some true ∧
      source=world.source ∧ Descendant (ledger commands) world.entry target := by
  rw [ancestry_some_exact]
  simp only [eq_comm (a:=true),Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,
    CSTTT.FallbackTheory.ExecutableSeed.path_bit_exact]
  constructor
  · rintro ⟨world,finished,seed,hw,hf,hs,⟨root,positive⟩,path⟩
    subst seed
    exact ⟨world,finished,hw,hf,hs,root,by simpa [Descendant,eq_comm] using path⟩
  · rintro ⟨world,finished,hw,hf,hs,root,path⟩
    exact ⟨world,finished,true,hw,hf,hs,⟨root,rfl⟩,by simpa [Descendant,eq_comm] using path⟩
-- A least continuation relation: every nonseed target needs an already related predecessor and an actual accepted edge.
theorem actual_ancestry_least (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) (world finished : World)
    (hw : fromActual acquired acquiredReady history=some world) (hf : run current currentReady world commands=some finished)
    (hs : retainedDecision leftNames rightNames current acquired acquiredReady history world.source world.entry=some true)
    (relation : Nat → Nat → Prop) (seed : relation world.source world.entry)
    (closed : ∀ root parent target,relation root parent → (parent,target)∈ledger commands → relation root target) :
    (∀ target,Descendant (ledger commands) world.entry target →
      ancestryDecision leftNames rightNames current acquired acquiredReady currentReady history commands world.source target=some true) ∧
    (∀ root target,ancestryDecision leftNames rightNames current acquired acquiredReady currentReady history commands root target=some true →
      relation root target) := by
  constructor
  · intro target path
    exact (ancestry_true_exact _ _ _ _ _ _ _ _ _ _).mpr ⟨world,finished,hw,hf,hs,rfl,path⟩
  · intro root target actual
    obtain ⟨base,last,hbase,hlast,hseed,equal,path⟩ := (ancestry_true_exact _ _ _ _ _ _ _ _ _ _).mp actual
    have same : base=world := Option.some.inj (hbase.symm.trans hw)
    subst base; subst root
    exact descendant_least (ledger commands) world.entry (relation world.source) seed (closed world.source) target path
-- Accepted native edges, not every event edge, supply Gamma after the independently checked Seed.
theorem ancestry_requires_predecessor (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) (source target : Nat)
    (actual : ancestryDecision leftNames rightNames current acquired acquiredReady currentReady history commands source target=some true) :
    ∃ world finished,fromActual acquired acquiredReady history=some world ∧ run current currentReady world commands=some finished ∧
      (target=world.entry ∨ ∃ predecessor,Descendant (ledger commands) world.entry predecessor ∧ (predecessor,target)∈ledger commands) := by
  obtain ⟨world,finished,hw,hf,hs,root,path⟩ := (ancestry_true_exact _ _ _ _ _ _ _ _ _ _).mp actual
  refine ⟨world,finished,hw,hf,?_⟩
  rcases path with equal|path
  · exact Or.inl equal.symm
  · cases path with
    | one member => exact Or.inr ⟨world.entry,Or.inl rfl,member⟩
    | extend previous member => exact Or.inr ⟨_,Or.inr previous,member⟩

def withdrawnCurrent (affected : Owner) : Assignment Owner NativePackageBundle.Value :=
  PublicationComposition.cutReceiver affected NativePackageBundle.canonical
def withdrawnReady (affected : Owner) :
    ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs (withdrawnCurrent affected)) :=
  PostWithdrawalPrototype.cutReady affected false NativePackageBundle.canonical (PublicationResources.ready false)
theorem canonical_final_continuation (affected : Owner) (history : Factor) :
    PublicationResources.entries false (canonicalReceipt false history).entry ∧
    NativeAcquiredWithdrawalPrototype.ContinuationLaw affected false (canonicalReceipt false history).entry := by
  obtain ⟨pair,actual,seed,path,middle,future,entry,continuation⟩ :=
    combined_withdrawal_return affected ModeExecution.firstNames ModeExecution.secondNames history
  have equal := Option.some.inj ((canonical_two_hop history).symm.trans actual)
  subst pair
  exact ⟨entry,continuation⟩
theorem canonical_seed_retained (affected : Owner) (leftNames rightNames : Owner → CarrierId) (history : Factor) :
    retainedDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
      history (canonicalWorld history).source (canonicalWorld history).entry=some true := by
  change retainedDecision leftNames rightNames (PublicationComposition.cutReceiver affected NativePackageBundle.canonical)
    NativePackageBundle.canonical PublicationReplay.ready history 0 4=some true
  rw [combined_decision_cut]
  exact canonical_combined_positive leftNames rightNames history
theorem canonical_fission_execution (affected : Owner) (history : Factor) (left right : Nat)
    (freshL : 4<left) (freshR : 4<right) (distinct : left≠right) :
    extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history [.fission 4 left right]=some (split (canonicalWorld history) 4 left right (canonicalReceipt false history).entry) := by
  have accepted := (fission_some_exact (withdrawnCurrent affected) (withdrawnReady affected) (canonicalWorld history)
    (split (canonicalWorld history) 4 left right (canonicalReceipt false history).entry) 4 left right).mpr
    ⟨(canonicalReceipt false history).entry,rfl,rfl,rfl,(canonical_fresh_exact _ _).mpr freshL,(canonical_fresh_exact _ _).mpr freshR,distinct,rfl⟩
  simp [extend,canonical_from_actual,run,accepted]
theorem canonical_fission_ancestry (affected : Owner) (leftNames rightNames : Owner → CarrierId) (history : Factor)
    (left right : Nat) (freshL : 4<left) (freshR : 4<right) (distinct : left≠right) :
    ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
      (withdrawnReady affected) history [.fission 4 left right] 0 left=some true ∧
    ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
      (withdrawnReady affected) history [.fission 4 left right] 0 right=some true := by
  have execution := canonical_fission_execution affected history left right freshL freshR distinct
  have hf : run (withdrawnCurrent affected) (withdrawnReady affected) (canonicalWorld history) [.fission 4 left right]=
    some (split (canonicalWorld history) 4 left right (canonicalReceipt false history).entry) := by
    simpa [extend,canonical_from_actual] using execution
  have seeded := canonical_seed_retained affected leftNames rightNames history
  constructor
  · apply (ancestry_true_exact _ _ _ _ _ _ _ _ _ _).mpr
    refine ⟨canonicalWorld history,_,canonical_from_actual history,hf,seeded,rfl,Or.inr (.one ?_)⟩
    simp [ledger,commandEdges,canonicalWorld]
  · apply (ancestry_true_exact _ _ _ _ _ _ _ _ _ _).mpr
    refine ⟨canonicalWorld history,_,canonical_from_actual history,hf,seeded,rfl,Or.inr (.one ?_)⟩
    simp [ledger,commandEdges,canonicalWorld]
-- Both full-state copies inherit individual native continuations. Their resource accounts are not asserted disjoint.
theorem canonical_fission_full_return (affected : Owner) (leftNames rightNames : Owner → CarrierId) (history : Factor)
    (left right : Nat) (freshL : 4<left) (freshR : 4<right) (distinct : left≠right) :
    ∃ finished,extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history [.fission 4 left right]=some finished ∧
      finished.read left=some (canonicalReceipt false history).entry ∧ finished.read right=some (canonicalReceipt false history).entry ∧
      ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
        (withdrawnReady affected) history [.fission 4 left right] 0 left=some true ∧
      ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
        (withdrawnReady affected) history [.fission 4 left right] 0 right=some true ∧
      PublicationResources.entries false (canonicalReceipt false history).entry ∧
      NativeAcquiredWithdrawalPrototype.ContinuationLaw affected false (canonicalReceipt false history).entry := by
  have ancestry := canonical_fission_ancestry affected leftNames rightNames history left right freshL freshR distinct
  have laws := canonical_final_continuation affected history
  exact ⟨_,canonical_fission_execution affected history left right freshL freshR distinct,
    by simp [split],by simp [split],ancestry.1,ancestry.2,laws.1,laws.2⟩
-- Nonvacuous advancement uses the actual controller's positive outcome, full updater and entire StepLaw at the actual final entry.
theorem canonical_supported_advance_return (affected : Owner) (leftNames rightNames : Owner → CarrierId) (history : Factor)
    (target : Nat) (fresh : 4<target) :
    ∃ outcome next finished,
      extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
        history [.advance 4 target false outcome]=some finished ∧ finished.read target=some next ∧
      next=ResourceRuntime.update (PublicationResources.runtime false) (NativePackageBundle.nativeInputs (withdrawnCurrent affected))
        (withdrawnReady affected) (canonicalReceipt false history).entry () false outcome ∧
      StrategyGame.PositiveSupport (ResourceRuntime.rows (PublicationResources.runtime false)
        (NativePackageBundle.nativeInputs (withdrawnCurrent affected))) (canonicalReceipt false history).entry () false outcome ∧
      ResourceRuntime.StepLaw (PublicationResources.cfg false) (PublicationResources.runtime false)
        (NativePackageBundle.nativeInputs (withdrawnCurrent affected)) (withdrawnReady affected) (canonicalReceipt false history).entry () false outcome ∧
      ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
        (withdrawnReady affected) history [.advance 4 target false outcome] 0 target=some true := by
  have laws := (canonical_final_continuation affected history).2 _ [] StrategyGame.Play.initial
  obtain ⟨outcome,supported⟩ := (laws.2.2 ()).2.1.2.2
  have fullLaw := (laws.2.2 ()).2.2 outcome supported
  obtain ⟨row,hrow,sup⟩ := positive_row_present (withdrawnCurrent affected) (canonicalReceipt false history).entry false outcome supported
  let next := ResourceRuntime.update (PublicationResources.runtime false) (NativePackageBundle.nativeInputs (withdrawnCurrent affected))
    (withdrawnReady affected) (canonicalReceipt false history).entry () false outcome
  let finished := advanced (canonicalWorld history) 4 target next
  have accepted : step (withdrawnCurrent affected) (withdrawnReady affected) (canonicalWorld history) (.advance 4 target false outcome)=some finished :=
    (advance_some_exact _ _ _ _ _ _ _ _).mpr ⟨_,row,rfl,hrow,rfl,rfl,(canonical_fresh_exact _ _).mpr fresh,sup,rfl⟩
  have hf : run (withdrawnCurrent affected) (withdrawnReady affected) (canonicalWorld history) [.advance 4 target false outcome]=some finished := by
    simp [run,accepted]
  refine ⟨outcome,next,finished,?_,by simp [finished,advanced,put],rfl,supported,fullLaw,?_⟩
  · simpa [extend,canonical_from_actual] using hf
  · apply (ancestry_true_exact _ _ _ _ _ _ _ _ _ _).mpr
    refine ⟨canonicalWorld history,finished,canonical_from_actual history,hf,canonical_seed_retained affected leftNames rightNames history,rfl,Or.inr (.one ?_)⟩
    simp [ledger,commandEdges,canonicalWorld]

-- Missing consumed data and an available negative remain distinct for every partial assignment.
theorem ancestry_none_exact (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) (source target : Nat) :
    ancestryDecision leftNames rightNames current acquired acquiredReady currentReady history commands source target=none ↔
    fromActual acquired acquiredReady history=none ∨ ∃ world,fromActual acquired acquiredReady history=some world ∧
      (run current currentReady world commands=none ∨
        retainedDecision leftNames rightNames current acquired acquiredReady history world.source world.entry=none) := by
  cases base : fromActual acquired acquiredReady history with
  | none => simp [ancestryDecision,base]
  | some world =>
    cases continuation : run current currentReady world commands with
    | none => simp [ancestryDecision,base,continuation]
    | some finished =>
      cases seed : retainedDecision leftNames rightNames current acquired acquiredReady history world.source world.entry with
      | none => simp [ancestryDecision,base,continuation,seed]
      | some value => simp [ancestryDecision,base,continuation,seed]
theorem false_bit_exact (bit : Bool) : false=bit ↔ ¬bit=true := by cases bit <;> decide
theorem ancestry_false_exact (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) (source target : Nat) :
    ancestryDecision leftNames rightNames current acquired acquiredReady currentReady history commands source target=some false ↔
    ∃ world finished seed,fromActual acquired acquiredReady history=some world ∧ run current currentReady world commands=some finished ∧
      retainedDecision leftNames rightNames current acquired acquiredReady history world.source world.entry=some seed ∧
      ¬(source=world.source ∧ seed=true ∧ Descendant (ledger commands) world.entry target) := by
  rw [ancestry_some_exact]
  simp only [false_bit_exact,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,
    CSTTT.FallbackTheory.ExecutableSeed.path_bit_exact,Descendant]
  simp only [and_assoc,eq_comm (a:=target)]
-- Raw current predictive owner absence rejects the actual global readout, even when native readiness at the other owner holds.
theorem missing_predictive_owner_rejected (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) (source target : Nat) (missing : current true=none) :
    ancestryDecision leftNames rightNames current acquired acquiredReady currentReady history commands source target=none := by
  cases base : fromActual acquired acquiredReady history with
  | none => simp [ancestryDecision,base]
  | some world =>
    cases continuation : run current currentReady world commands <;>
      simp [ancestryDecision,base,NativeTwoHopReceiptPrototype.retainedDecision,missing]
-- A related continuation target must occur in a genuine accepted ledger, unless it is the original positively seeded entry.
theorem disconnected_target_excluded (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) (source target : Nat)
    (away : ∀ world,fromActual acquired acquiredReady history=some world → target≠world.entry)
    (noIncoming : ∀ parent,(parent,target)∉ledger commands) :
    ancestryDecision leftNames rightNames current acquired acquiredReady currentReady history commands source target≠some true := by
  intro actual
  obtain ⟨world,finished,hw,hf,hs,root,related⟩ := (ancestry_true_exact _ _ _ _ _ _ _ _ _ _).mp actual
  rcases related with same|path
  · exact away world hw same.symm
  · exact no_incoming_excludes (ledger commands) target noIncoming world.entry path

-- The phase view preserves the actual native event graph; it cannot substitute an unrelated provenance ledger.
theorem phase_world_edges (pair : ReceiptPair) (world : World) (assigned : phaseWorld pair=some world) :
    world.edges=pair.edges := by
  unfold phaseWorld at assigned
  split at assigned
  · split at assigned
    · dsimp only at assigned
      split at assigned
      · have eq := Option.some.inj assigned
        cases eq
        rfl
      · cases assigned
    · cases assigned
  · cases assigned
theorem from_actual_edges (acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (world : World) (assigned : fromActual acquired ready history=some world) :
    ∃ pair,execute acquired ready history=some pair ∧ world.edges=pair.edges := by
  obtain ⟨pair,actual,frame⟩ := Option.bind_eq_some_iff.mp assigned
  exact ⟨pair,actual,phase_world_edges pair world frame⟩
theorem actual_seed_path (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (ready : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (history : Factor) (world : World) (assigned : fromActual acquired ready history=some world)
    (positive : retainedDecision leftNames rightNames current acquired ready history world.source world.entry=some true) :
    Path world.edges world.source world.entry := by
  obtain ⟨pair,actual,frameEdges⟩ := from_actual_edges acquired ready history world assigned
  obtain ⟨left,right,original,received,edges,hl,hr,read,path,pred⟩ := (retained_true_exact _ _ _ _ _ _ _ _).mp positive
  obtain ⟨other,computed,outer⟩ := (combined_read_some_exact _ _ _ _ _ _ _ _).mp read
  have same : other=pair := Option.some.inj (computed.symm.trans actual)
  subst other
  obtain ⟨first,last,hFirst,hLast,root,target,contents⟩ := (outer_read_some_exact _ _ _ _ _ _).mp outer
  have emitted : edges=pair.edges := congrArg (fun x : Factor × Factor × List (Nat × Nat) => x.2.2) contents
  rw [frameEdges,←emitted]
  exact path
-- Every computed continuation ancestry has a positive-length path in the SAME actual finished native world.
theorem ancestry_actual_path (leftNames rightNames : Owner → CarrierId)
    (current acquired : Assignment Owner NativePackageBundle.Value)
    (acquiredReady : ∀ cell, AcquisitionExecution.Ready (PublicationReplay.raw cell) (NativePackageBundle.nativeInputs acquired))
    (currentReady : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (history : Factor) (commands : List Command) (source target : Nat)
    (actual : ancestryDecision leftNames rightNames current acquired acquiredReady currentReady history commands source target=some true) :
    ∃ finished,extend current acquired acquiredReady currentReady history commands=some finished ∧ Path finished.edges source target := by
  obtain ⟨world,finished,assigned,continued,positive,root,desc⟩ := (ancestry_true_exact _ _ _ _ _ _ _ _ _ _).mp actual
  have seedPath := actual_seed_path leftNames rightNames current acquired acquiredReady history world assigned positive
  have realized := run_edges_realized current currentReady commands world finished continued
  have retained := CSTTT.FallbackTheory.NativeDescendant.path_inclusion _ _ realized.1 _ _ seedPath
  refine ⟨finished,by simp [extend,assigned,continued],?_⟩
  subst source
  rcases desc with equal|path
  · exact equal ▸ retained
  · have continuation := CSTTT.FallbackTheory.NativeDescendant.path_inclusion _ _ realized.2 _ _ path
    exact CSTTT.FallbackTheory.ExecutableSeed.path_trans retained continuation

-- The literal target mode is checked on every extension; source-mode rows cannot qualify as target-native continuation.
theorem wrong_mode_rejected (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (world : World) (parent target left right : Nat) (action : Bool) (outcome : Factor) (state : ModeExecution.Registers)
    (read : world.read parent=some state) (mode : (state ()).2≠false) :
    step current ready world (.advance parent target action outcome)=none ∧
      step current ready world (.fission parent left right)=none := by
  constructor
  · simp only [step,read,bind,Option.bind_some]
    cases row : (PublicationResources.runtime false).execution.row.eval (NativePackageBundle.nativeInputs current) state ((),action) <;> simp [mode]
  · simp [step,read,mode]
theorem duplicate_fission_rejected (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (world : World) (parent target : Nat) : step current ready world (.fission parent target target)=none := by
  cases read : world.read parent <;> simp [step,read]
theorem unsupported_row_rejected (current : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (PublicationResources.runtime false) (NativePackageBundle.nativeInputs current))
    (world : World) (parent target : Nat) (action : Bool) (outcome : Factor) (state : ModeExecution.Registers) (row : List (Factor × Rat))
    (read : world.read parent=some state)
    (actual : (PublicationResources.runtime false).execution.row.eval (NativePackageBundle.nativeInputs current) state ((),action)=some row)
    (unsupported : ¬∃ weight,(outcome,weight)∈row ∧ 0<weight) :
    step current ready world (.advance parent target action outcome)=none := by simp [step,read,actual,unsupported]
-- No second query-root is introduced by descendants or fission, even for otherwise successful arbitrary command streams.
theorem canonical_other_source_false (affected : Owner) (leftNames rightNames : Owner → CarrierId) (history : Factor)
    (commands : List Command) (finished : World) (source target : Nat) (other : source≠0)
    (accepted : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history commands=some finished) :
    ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
      (withdrawnReady affected) history commands source target=some false := by
  have hf : run (withdrawnCurrent affected) (withdrawnReady affected) (canonicalWorld history) commands=some finished := by
    simpa [extend,canonical_from_actual] using accepted
  apply (ancestry_false_exact _ _ _ _ _ _ _ _ _ _).mpr
  refine ⟨canonicalWorld history,finished,true,canonical_from_actual history,hf,canonical_seed_retained affected leftNames rightNames history,?_⟩
  exact fun positive => other positive.1
-- A disconnected queried address is a genuinely available false observation on every successful canonical extension.
theorem canonical_disconnected_false (affected : Owner) (leftNames rightNames : Owner → CarrierId) (history : Factor)
    (commands : List Command) (finished : World) (target : Nat) (away : target≠4)
    (noIncoming : ∀ parent,(parent,target)∉ledger commands)
    (accepted : extend (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready (withdrawnReady affected)
      history commands=some finished) :
    ancestryDecision leftNames rightNames (withdrawnCurrent affected) NativePackageBundle.canonical PublicationReplay.ready
      (withdrawnReady affected) history commands 0 target=some false := by
  have hf : run (withdrawnCurrent affected) (withdrawnReady affected) (canonicalWorld history) commands=some finished := by
    simpa [extend,canonical_from_actual] using accepted
  apply (ancestry_false_exact _ _ _ _ _ _ _ _ _ _).mpr
  refine ⟨canonicalWorld history,finished,true,canonical_from_actual history,hf,canonical_seed_retained affected leftNames rightNames history,?_⟩
  rintro ⟨_,_,same|path⟩
  · exact away same.symm
  · exact no_incoming_excludes (ledger commands) target noIncoming 4 path
end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeReceiptExtensionPrototype
