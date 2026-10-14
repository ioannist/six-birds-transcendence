import CSTTT.Targets.GenericHandoff.RawCorridorSequence
import CSTTT.Targets.GenericHandoff.RegisterInitialization

/-! Raw three-carrier acquisition geometry. All legs are interpreted from
assigned event/path/funding/seed instructions. This is not a full handoff. -/
namespace CSTTT.TargetTheory.GenericHandoff.RawCorridorSequenceModels
open RegisterInterpreter CSTTT.CorridorTheory.AtomicChain
abbrev LocalStage := Fin 3
abbrev Input := AcquisitionCorridor.View LocalStage Bool Unit Unit
abbrev Value (_ : Bool) := Input
def stageList : List LocalStage := [0,1,2]
def event (id : Bool) : AcquisitionExecution.Event LocalStage :=
  if id then ⟨1,2,false,true,true,true,1⟩ else ⟨0,1,true,true,true,true,1⟩
def leftHistory : List String := ["root"]
def rightHistory : List String := ["root","left-mix","left-exit"]
def leftInput : Input :=
  ⟨fun _ => ⟨(),[false,true]⟩,event,stageList,⟨true,true,true,true⟩,⟨fun _ => 0,fun _ => leftHistory⟩⟩
def rightInput : Input :=
  {leftInput with seeds := ⟨fun _ => 0,fun _ => rightHistory⟩}
def canonical : Assignment Bool Value | false => some leftInput | true => some rightInput
def cut : Assignment Bool Value | false => some leftInput | true => none
def unfunded : Assignment Bool Value
  | false => some leftInput
  | true => some {rightInput with receiver := {rightInput.receiver with targetFunded := false}}
def leftSource : Nat := 17
def middleCarrier : Nat := 55
def finalTarget : Nat := 101
def rightOffset : Nat := 2
def brokenOffset : Nat := 3

def acquisition (cell : Bool) :
    AcquisitionExecution.Raw Bool Value Unit (fun _ => Nat) Unit Unit Unit LocalStage Bool Unit Unit where
  initializer := fun _ => .literal 0
  histories := ⟨.literal (fun _ => [((),(),())])⟩
  routes := ⟨cell,fun v => v.routes⟩
  events := ⟨cell,fun v => v.events⟩
  realized := ⟨cell,fun v => v.realized⟩
  receiver := ⟨cell,fun v => v.receiver⟩
  receive := fun _ => .register ()
  arrivalResponse := .literal ((),())
  execution := ⟨[()],[()],[()],.literal [((),1)],fun _ => .map Nat.succ (.register ())⟩

def schema (source target offset : Nat) : AcquisitionExecution.Schema LocalStage Bool Unit Unit :=
  ⟨stageList,[false,true],[()],[()],0,2,⟨source⟩,⟨target⟩,fun s => offset+s.val⟩
def names (side : Bool) : AcquisitionCorridor.Names Bool :=
  if side then ⟨fun e => if e then "right-exit" else "right-mix","right-root"⟩
  else ⟨fun e => if e then "left-exit" else "left-mix","left-root"⟩
def raw (cell : Bool) (source target offset : Nat) :
    AcquisitionCorridor.Raw Bool Value Unit (fun _ => Nat) Unit Unit Unit LocalStage Bool Unit Unit :=
  ⟨acquisition cell,schema source target offset,names cell,⟨.map (fun v => v.seeds) (.cell cell)⟩⟩
def left := raw false leftSource middleCarrier 0
def right := raw true middleCarrier finalTarget rightOffset
def wrongClock := raw true middleCarrier finalTarget brokenOffset
def loopRight := raw true middleCarrier leftSource rightOffset

def request (m : AcquisitionCorridor.Raw Bool Value Unit (fun _ => Nat) Unit Unit Unit LocalStage Bool Unit Unit) :
    RawCorridorSequence.Request Bool Value :=
  ⟨Unit,(fun _ => Nat),Unit,Unit,Unit,LocalStage,Bool,Unit,Unit,inferInstance,m,()⟩
def requests := [request left,request right]
def wrongRequests := [request left,request wrongClock]
def loopRequests := [request left,request loopRight]

theorem read_equation (cell : Bool) (source target offset : Nat) (a : Assignment Bool Value) :
    AcquisitionCorridor.read (raw cell source target offset) a = a cell := by
  cases h : a cell <;> simp [raw,acquisition,AcquisitionCorridor.read,CellView.read,
    StaticView.read,Expr.eval,h]

theorem left_leg_equation (a : Assignment Bool Value) :
    RawCorridorSequence.leg (request left) a =
      (a false).map (fun v => AcquisitionCorridor.leg left v ()) := by
  simp only [RawCorridorSequence.leg,request,left,read_equation]
theorem right_leg_equation (a : Assignment Bool Value) :
    RawCorridorSequence.leg (request right) a =
      (a true).map (fun v => AcquisitionCorridor.leg right v ()) := by
  simp only [RawCorridorSequence.leg,request,right,read_equation]

theorem ready (cell : Bool) (a : Assignment Bool Value) (h : (a cell).isSome = true) :
    AcquisitionExecution.Ready (acquisition cell) a := by
  refine ⟨?_,?_,?_,?_,?_⟩
  · intro k hk
    have he : k = cell := by simpa [acquisition,AcquisitionExecution.Raw.dependencies,StaticView.dependencies,Expr.dependencies] using hk
    subst k; exact h
  · intro r k hk; simp [acquisition,Expr.dependencies] at hk
  · intro k hk; simp [acquisition,Expr.dependencies] at hk
  · intro r k hk; simp [acquisition,Expr.dependencies] at hk
  · intro r k hk; simp [acquisition,Expr.dependencies] at hk

theorem left_view_check : AcquisitionCorridor.ViewCheck left leftInput := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,?_,?_,?_⟩
  · intro e he; cases e <;> decide +kernel
  · intro i j hi hj hn
    cases i <;> cases j <;> simp [left,raw,names] at hn ⊢
  · intro r hr; cases r
    refine ⟨by decide +kernel,?_,?_,by decide +kernel,by decide +kernel,?_⟩
    · refine ⟨false,[true],rfl,rfl,?_,?_,true,rfl,rfl,rfl,rfl⟩
      · decide +kernel
      · decide +kernel
    · refine ⟨rfl,rfl,rfl,fun _ => ⟨false,by decide +kernel,by decide +kernel,by decide +kernel,rfl,rfl,rfl⟩⟩
    · unfold AtomicLegPass; decide +kernel
theorem right_view_check : AcquisitionCorridor.ViewCheck right rightInput := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,?_,?_,?_⟩
  · intro e he; cases e <;> decide +kernel
  · intro i j hi hj hn
    cases i <;> cases j <;> simp [right,raw,names] at hn ⊢
  · intro r hr; cases r
    refine ⟨by decide +kernel,?_,?_,by decide +kernel,by decide +kernel,?_⟩
    · refine ⟨false,[true],rfl,rfl,?_,?_,true,rfl,rfl,rfl,rfl⟩
      · decide +kernel
      · decide +kernel
    · refine ⟨rfl,rfl,rfl,fun _ => ⟨false,by decide +kernel,by decide +kernel,by decide +kernel,rfl,rfl,rfl⟩⟩
    · unfold AtomicLegPass; decide +kernel
theorem loop_view_check : AcquisitionCorridor.ViewCheck loopRight rightInput := by
  refine ⟨by decide +kernel,by decide +kernel,by decide +kernel,by decide +kernel,?_,?_,?_⟩
  · intro e he; cases e <;> decide +kernel
  · intro i j hi hj hn
    cases i <;> cases j <;> simp [loopRight,raw,names] at hn ⊢
  · intro r hr; cases r
    refine ⟨by decide +kernel,?_,?_,by decide +kernel,by decide +kernel,?_⟩
    · refine ⟨false,[true],rfl,rfl,?_,?_,true,rfl,rfl,rfl,rfl⟩
      · decide +kernel
      · decide +kernel
    · refine ⟨rfl,rfl,rfl,fun _ => ⟨false,by decide +kernel,by decide +kernel,by decide +kernel,rfl,rfl,rfl⟩⟩
    · unfold AtomicLegPass; decide +kernel
theorem left_parent : RawCorridorSequence.Parent (request left) canonical :=
  ⟨⟨ready false canonical rfl,leftInput,by change AcquisitionCorridor.read (raw false leftSource middleCarrier 0) canonical = _; rw [read_equation]; rfl,left_view_check⟩,by change () ∈ [()]; simp⟩
theorem right_parent : RawCorridorSequence.Parent (request right) canonical :=
  ⟨⟨ready true canonical rfl,rightInput,by change AcquisitionCorridor.read (raw true middleCarrier finalTarget rightOffset) canonical = _; rw [read_equation]; rfl,right_view_check⟩,by change () ∈ [()]; simp⟩
theorem loop_parent : RawCorridorSequence.Parent (request loopRight) canonical :=
  ⟨⟨ready true canonical rfl,rightInput,by change AcquisitionCorridor.read (raw true middleCarrier leftSource rightOffset) canonical = _; rw [read_equation]; rfl,loop_view_check⟩,by change () ∈ [()]; simp⟩

theorem checked : RawCorridorSequence.Checked canonical requests := by
  refine ⟨by simp [requests],?_,by decide +kernel,by change some 17 ≠ some 101; decide +kernel⟩
  intro q hq
  rcases List.mem_cons.mp hq with he | hr
  · subst q; exact left_parent
  · have he : q = request right := by simpa [requests] using hr
    subst q; exact right_parent
theorem positive : RawCorridorSequence.Readout canonical requests :=
  RawCorridorSequence.constructs canonical requests checked

def actualLegs : List FiniteAtomicLeg :=
  [AcquisitionCorridor.leg left leftInput (),AcquisitionCorridor.leg right rightInput ()]
theorem actual_chain : RawCorridorSequence.chain canonical requests = some actualLegs := by decide +kernel
theorem actual_length : actualLegs.length = 2 := rfl
theorem actual_carriers : actualLegs.map (·.source) = [17,55] ∧ actualLegs.map (·.target) = [55,101] := by
  constructor <;> rfl
theorem actual_middle_support :
    ∃ s ∈ chainStages actualLegs, middleCarrier ∈ s.support := by
  refine ⟨exit (AcquisitionCorridor.leg left leftInput ()),?_,?_⟩ <;> decide +kernel

theorem missing_right : ¬ RawCorridorSequence.Readout cut requests := by
  apply RawCorridorSequence.missing_at cut requests (request right) (by simp [requests])
  rw [right_leg_equation]
  rfl
theorem left_leg_positive : RawCorridorSequence.leg (request left) canonical =
    some (AcquisitionCorridor.leg left leftInput ()) := by rw [left_leg_equation]; rfl
theorem wrong_clock_leg : RawCorridorSequence.leg (request wrongClock) canonical =
    some (AcquisitionCorridor.leg wrongClock rightInput ()) := by
  change (AcquisitionCorridor.read (raw true middleCarrier finalTarget brokenOffset) canonical).map _ = _
  rw [read_equation]
  rfl
theorem wrong_clock_seam : AdjacentFrontierCheck (AcquisitionCorridor.leg left leftInput ())
    (AcquisitionCorridor.leg wrongClock rightInput ()) = false := by decide +kernel
theorem wrong_clock_no_readout : ¬ RawCorridorSequence.Readout canonical wrongRequests :=
  RawCorridorSequence.bad_first_seam_no_readout canonical (request left) (request wrongClock) []
    _ _ left_leg_positive wrong_clock_leg wrong_clock_seam

theorem unfunded_leg : RawCorridorSequence.leg (request right) unfunded =
    some (AcquisitionCorridor.leg right {rightInput with receiver := {rightInput.receiver with targetFunded := false}} ()) := by
  rw [right_leg_equation]; rfl
theorem unfunded_leg_bad :
    ¬ AtomicLegPass (AcquisitionCorridor.leg right {rightInput with receiver := {rightInput.receiver with targetFunded := false}} ()) := by
  unfold AtomicLegPass
  decide +kernel
theorem unfunded_no_readout : ¬ RawCorridorSequence.Readout unfunded requests :=
  RawCorridorSequence.bad_leg_no_readout unfunded requests (request right) (by simp [requests])
    _ unfunded_leg unfunded_leg_bad

theorem loop_parents : ∀ q ∈ loopRequests, RawCorridorSequence.Parent q canonical := by
  intro q hq
  rcases List.mem_cons.mp hq with he | hr
  · subst q; exact left_parent
  · have he : q = request loopRight := by simpa [loopRequests] using hr
    subst q; exact loop_parent
theorem loop_seam : RawCorridorSequence.seams canonical loopRequests = some true := by decide +kernel
theorem loop_not_outer : ¬ RawCorridorSequence.OuterDistinct loopRequests := by
  change ¬ (some 17 ≠ some 17)
  simp
theorem loop_no_readout : ¬ RawCorridorSequence.Readout canonical loopRequests :=
  RawCorridorSequence.equal_outer_no_readout canonical loopRequests loop_not_outer
theorem parent_and_join_not_sufficient :
    ¬ ∀ a : Assignment Bool Value, ∀ qs : List (RawCorridorSequence.Request Bool Value),
      qs ≠ [] → (∀ q ∈ qs, RawCorridorSequence.Parent q a) →
      RawCorridorSequence.seams a qs = some true → RawCorridorSequence.Readout a qs := by
  intro h
  exact loop_no_readout (h canonical loopRequests (by simp [loopRequests]) loop_parents loop_seam)

end CSTTT.TargetTheory.GenericHandoff.RawCorridorSequenceModels
