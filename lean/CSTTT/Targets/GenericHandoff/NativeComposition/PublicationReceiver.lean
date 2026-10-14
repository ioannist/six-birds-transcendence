import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationPhysical

/-! A heterogeneous receiver retains arbitrary incoming physical counters,
terminal, full past and path. Raw initialization and the ACTUAL ModeExecution
receive instruction compute its result; historical activation is checked first.
No received run or class map is supplied as primitive content. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationReceiver
open RegisterInterpreter RegisterInitialization ModeExecution PublicationReplay

structure Input where
  terminal : Factor
  counter : Nat
  ticks : Nat
  past : List Factor
  path : List Bool
  history : History
  route : Route

def initialState (cell : Owner) (p : NativeComposition.Input × NativeComposition.Input) (i : Input) : ModeExecution.State :=
  ((⟨i.terminal,i.counter,i.ticks,(i.past,i.path),p.2.temporal.receiverFunded &&
    p.2.temporal.resource.rechargeAvailable && decide (p.2.temporal.ledger.initial ≥ p.2.temporal.ledger.cost)⟩ : Frame.State),
    swapOwner cell)
def initializer (cell : Owner) : InitialProgram Owner MemoryValue Unit (fun _ => ModeExecution.State) Input :=
  fun _ => .map (fun p : (NativeComposition.Input × NativeComposition.Input) × Input => initialState cell p.1 p.2)
    (.pair (.cell cell) (.environment id))
def active (cell : Owner) (p : NativeComposition.Input × NativeComposition.Input) :=
  NominalProtocol.active (PublicationNominal.specification cell) (PublicationNominal.data p)
def receive (cell : Owner) (a : Assignment Owner MemoryValue) (i : Input) : Option ModeExecution.State := do
  let p ← a cell
  if active cell p then
    let initialized ← (initializer cell ()).eval a noRegisters i
    (receiveExpr cell (swapOwner cell)).eval a (ModeExecution.pack initialized) (i.history,i.route)
  else none
def sourceClass (cell : Owner) (p : NativeComposition.Input × NativeComposition.Input) (i : Input) :=
  TemporalFactorRules.prediction (factorSchema (swapOwner cell)) p.2.temporal i.terminal
def receivedClass (cell : Owner) (a : Assignment Owner MemoryValue) (i : Input) : Option Frame.Predictive := do
  let p ← a cell
  let arrived ← receive cell a i
  pure (TemporalFactorRules.prediction (factorSchema cell) p.1.temporal arrived.1.factor)

theorem initializer_decoded (cell : Owner) (a : Assignment Owner MemoryValue) (i : Input) :
    (initializer cell ()).eval a noRegisters i=(a cell).map (fun p => initialState cell p i) := by
  cases ha : a cell <;> simp [initializer,Expr.eval,ha]
theorem receive_decoded (cell : Owner) (a : Assignment Owner MemoryValue) (i : Input) :
    receive cell a i=(a cell).bind (fun p => if active cell p then
      some (received p (swapOwner cell) (initialState cell p i)) else none) := by
  cases ha : a cell with
  | none => simp [receive,ha]
  | some p =>
    by_cases hb : active cell p=true
    all_goals simp [receive,ha,hb,initializer_decoded,receiveExpr,targetData,Expr.eval,
      Expr.reenv_eval,ModeExecution.pack,received]

theorem received_class_decoded (cell : Owner) (a : Assignment Owner MemoryValue) (i : Input) :
    receivedClass cell a i=(a cell).bind (fun p => if active cell p then
      some (TemporalFactorRules.prediction (factorSchema cell) p.1.temporal i.terminal) else none) := by
  cases ha : a cell
  · simp [receivedClass,ha]
  · simp only [receivedClass,ha,Option.bind_some,receive_decoded,ha]
    split
    · simp [received,initialState]
    · rfl
theorem missing_receive (cell : Owner) (a : Assignment Owner MemoryValue) (hm : a cell=none) (i : Input) :
    receive cell a i=none ∧ receivedClass cell a i=none := by
  simp [receive_decoded,received_class_decoded,hm]
theorem inactive_receive (cell : Owner) (a : Assignment Owner MemoryValue)
    (p : NativeComposition.Input × NativeComposition.Input) (hp : a cell=some p) (hn : active cell p=false) (i : Input) :
    receive cell a i=none ∧ receivedClass cell a i=none := by
  simp [receive_decoded,received_class_decoded,hp,hn]
theorem assigned_receiver (cell : Owner) : active cell (PublicationExecution.episodePair (round cell))=true := by
  cases cell <;> rfl

def output (cell : Owner) (i : Input) : ModeExecution.State :=
  ((⟨i.terminal,i.counter,i.ticks,(i.past++i.past,i.path),true⟩ : Frame.State),cell)
theorem actual_receive (cell : Owner) (i : Input) : receive cell PublicationResources.assignment i=some (output cell i) := by
  have hp : PublicationResources.assignment cell=some (PublicationExecution.episodePair (round cell)) :=
    PublicationExecution.assigned_pair cell
  rw [receive_decoded,hp]
  simp only [Option.bind_some,assigned_receiver,ite_true]
  cases cell <;> rfl
theorem actual_source_class (cell : Owner) (i : Input) :
    sourceClass cell (PublicationExecution.episodePair (round cell)) i=
      TemporalFactorRules.prediction (factorSchema false) (AvailabilityFactor.temporal false) i.terminal := by
  cases cell <;> rfl
theorem actual_received_class (cell : Owner) (i : Input) :
    receivedClass cell PublicationResources.assignment i=
      some (sourceClass cell (PublicationExecution.episodePair (round cell)) i) := by
  have hp : PublicationResources.assignment cell=some (PublicationExecution.episodePair (round cell)) :=
    PublicationExecution.assigned_pair cell
  rw [received_class_decoded,hp]
  simp only [Option.bind_some,assigned_receiver,ite_true]
  cases cell <;> rfl

def ContentFaithful (cell : Owner) (a : Assignment Owner MemoryValue) : Prop :=
  ∃ p, a cell=some p ∧
    (∃ x y : Input, sourceClass cell p x≠sourceClass cell p y) ∧
    (∀ i : Input, ∃ cls, receivedClass cell a i=some cls) ∧
    ∀ x y : Input, sourceClass cell p x≠sourceClass cell p y → receivedClass cell a x≠receivedClass cell a y
def sample (s : Factor) : Input := ⟨s,0,0,[],[],s,s⟩
theorem actual_content_faithful (cell : Owner) : ContentFaithful cell PublicationResources.assignment := by
  refine ⟨PublicationExecution.episodePair (round cell),PublicationExecution.assigned_pair cell,?_,?_,?_⟩
  · refine ⟨sample (false,false,false),sample (true,false,false),?_⟩
    rw [actual_source_class,actual_source_class]
    decide +kernel
  · intro i; exact ⟨_,actual_received_class cell i⟩
  · intro x y hn
    rw [actual_received_class,actual_received_class]
    exact fun h => hn (Option.some.inj h)
theorem inactive_not_faithful (cell : Owner) (a : Assignment Owner MemoryValue)
    (p : NativeComposition.Input × NativeComposition.Input) (hp : a cell=some p) (hn : active cell p=false) :
    ¬ ContentFaithful cell a := by
  rintro ⟨q,hq,_,ht,_⟩
  obtain ⟨cls,hc⟩ := ht (sample (false,false,false))
  rw [(inactive_receive cell a p hp hn _).2] at hc
  contradiction
theorem missing_not_faithful (cell : Owner) (a : Assignment Owner MemoryValue) (hm : a cell=none) :
    ¬ ContentFaithful cell a := by
  rintro ⟨p,hp,_⟩
  rw [hm] at hp
  contradiction

def cutSource (p : NativeComposition.Input × NativeComposition.Input) :=
  ({p.1 with receiver := {p.1.receiver with sourcePresent := false}},p.2)
theorem cut_active (cell : Owner) (p : NativeComposition.Input × NativeComposition.Input) : active cell (cutSource p)=false := by
  simp [active,NominalProtocol.active,PublicationNominal.data,cutSource]
theorem cut_copied_source (p : NativeComposition.Input × NativeComposition.Input) : (cutSource p).2=p.2 := rfl

def cutAt (cell : Owner) (a : Assignment Owner MemoryValue) : Assignment Owner MemoryValue :=
  fun o => if o=cell then (a o).map cutSource else a o
theorem cut_at_copied_source (cell o : Owner) (a : Assignment Owner MemoryValue) :
    (cutAt cell a o).map Prod.snd=(a o).map Prod.snd := by
  by_cases he : o=cell
  · simp [cutAt,he,Option.map_map,Function.comp_def,cutSource]
  · simp [cutAt,he]
theorem cut_at_receive (cell : Owner) (a : Assignment Owner MemoryValue) (i : Input) :
    receive cell (cutAt cell a) i=none ∧ receivedClass cell (cutAt cell a) i=none := by
  cases hp : a cell with
  | none => apply missing_receive; simp [cutAt,hp]
  | some p =>
    apply inactive_receive cell _ (cutSource p)
    · simp [cutAt,hp]
    · exact cut_active cell p
theorem cut_at_not_faithful (cell : Owner) (a : Assignment Owner MemoryValue) :
    ¬ ContentFaithful cell (cutAt cell a) := by
  rintro ⟨p,hp,_,ht,_⟩
  obtain ⟨cls,hc⟩ := ht (sample (false,false,false))
  rw [(cut_at_receive cell a _).2] at hc
  contradiction

def terminalInput (cell : Owner) (h : Factor) : Input :=
  ⟨h,start cell+(jump cell-1),start cell+(jump cell-1),List.replicate (copies cell) h,[false,true],h,h⟩
theorem initialized_actual_terminal (cell : Owner) (h : Factor) :
    initialState cell (PublicationExecution.episodePair (round cell)) (terminalInput cell h)=
      PublicationPhysical.terminalRun cell h () := by
  cases cell <;> rfl
theorem actual_receiver_square (cell : Owner) (h : Factor) :
    receive cell PublicationResources.assignment (terminalInput cell h)=
      some (AcquisitionExecution.receive (PublicationReplay.raw cell) PublicationResources.assignment
        (PublicationReplay.ready cell) (PublicationPhysical.terminalRun cell h) h h ()) := by
  rw [actual_receive,PublicationPhysical.receive_terminal]
  cases cell <;> rfl

/-- An inverse recovers the actual full incoming past and event path, and all
physical counters and terminal, from the received state. -/
def decode (x : ModeExecution.State) : Factor × Nat × Nat × List Factor × List Bool :=
  (x.1.factor,x.1.counter,x.1.ticks,x.1.residue.1.take (x.1.residue.1.length/2),x.1.residue.2)
theorem full_payload_recovered (cell : Owner) (i : Input) :
    decode (output cell i)=(i.terminal,i.counter,i.ticks,i.past,i.path) := by
  simp only [decode,output,half_double]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationReceiver
