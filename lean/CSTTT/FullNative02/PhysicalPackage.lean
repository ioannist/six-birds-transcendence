import CSTTT.FullNative02.RetainedHistory
import CSTTT.FullNative.SharedPackage

namespace CSTTT.FullNative02.Package
open FullNative
open TargetTheory.GenericHandoff FixedPointVerifier
set_option autoImplicit false
set_option maxHeartbeats 16000000

def matrix (w : World) (owner : Nat) (t : State) : Rat :=
  ((normalizedNative renewable w owner false).map fun e =>
    if (e.1.residents owner).map Resident.current=some t then e.2 else 0).sum
def current (w : World) (owner : Nat) : Option (Nat × Nat × Nat) := do
  let (r,_,_) ← access w owner
  pure (publicLens r.current,((nativeRows renewable w owner false).map Prod.snd).sum,
    ((nativeRows renewable w owner true).map Prod.snd).sum)
def emitted (w : World) (owner : Nat) (observe : State → Nat) (word : List Bool) (out : List Nat) : Rat :=
  Binding.emittedLaw (fun w a => normalizedNative renewable w owner a)
    (fun w => match w.residents owner with | none => 0 | some r => observe r.current) w word out

theorem matrix_from_installed (w : World) (owner : Nat) (r : Resident) (key : Token)
    (h : access w owner=some (r,.canonical32,key)) : matrix w owner=Objecthood.P r.current := by
  funext t
  simp only [matrix,normalizedNative,native_rows_from_access _ _ _ _ _ _ h false,
    ROM.program,Objecthood.P,List.map_map,Function.comp_def]
  simp [advance,put,rationalRows,List.map_map,Function.comp_def]

/-- Exactly the inherited G21 physical grade, including its two-step
nonuniqueness counter-trace. It is a law of the installed generator matrix,
separate from every increasing history register. -/
def PhysicalC1 (_ : State) : Prop :=
  (∀ perturb squared,
    Probability states (Objecthood.stationary perturb) ∧
    Fixed states (Objecthood.closure perturb squared) (Objecthood.stationary perturb) ∧
    Objecthood.stationary perturb≠(fun _ => (1:Rat)/32) ∧
    (15:Rat)/16 ≤ mass Objecthood.core (Objecthood.stationary perturb) ∧
    Objecthood.stationaryTV perturb=(if perturb then 319/5536 else 1/22) ∧
    Objecthood.defect perturb squared=(if perturb then
      (if squared then 30675375/268435456 else 465/512)
      else (if squared then 195/2048 else 1))) ∧
  (∀ perturb squared, perturb=true ∨ squared=false → ∀ v,
    Probability states v → Fixed states (Objecthood.closure perturb squared) v →
    v=Objecthood.stationary perturb) ∧
  (Probability states (Objecthood.phaseLaw false) ∧
   Probability states (Objecthood.phaseLaw true) ∧
   Fixed states (Objecthood.closure false true) (Objecthood.phaseLaw false) ∧
   Fixed states (Objecthood.closure false true) (Objecthood.phaseLaw true) ∧
   Objecthood.phaseLaw false≠Objecthood.phaseLaw true)

theorem physical_c1 (s : State) : PhysicalC1 s :=
  (SharedPackage.computed_c1 PhysicalExecution.source PhysicalExecution.source_sector).2

theorem current_from_installed (w : World) (owner : Nat) (r : Resident) (key : Token)
    (h : access w owner=some (r,.canonical32,key)) :
    current w owner=some (Binding.currentPublic r.current) := by
  simp only [current,h,Bind.bind,Option.bind]
  simp only [native_rows_from_access _ _ _ _ _ _ h false,
    native_rows_from_access _ _ _ _ _ _ h true,ROM.program,List.map_map]
  rfl

theorem emitted_from_installed (w : World) (owner : Nat) (r : Resident) (rom : ROM) (key : Token)
    (h : access w owner=some (r,rom,key)) (observe : State → Nat)
    (word : List Bool) (out : List Nat) :
    emitted w owner observe word out=Binding.emittedLaw (rationalRows rom.program) observe r.current word out := by
  unfold emitted
  induction word generalizing w r out with
  | nil => cases out <;> rfl
  | cons action rest ih =>
    cases out with
    | nil => rfl
    | cons o os =>
      simp only [Binding.emittedLaw,normalizedNative,native_rows_from_access _ _ _ _ _ _ h action,
        rationalRows,List.foldr_map]
      congr 1
      funext e acc
      have next := renewable_access_after w owner r rom key h action e
      have present := (binding_facts _ _ _ _ _ (access_facts _ _ _ _ _ next).1).1
      simp only [present]
      exact congrArg (fun z => (if observe e.1=o then (e.2:Rat)/16*z else 0)+acc) (ih _ _ next os)

def split (w : World) (owner : Nat) (r : Resident) (key : Token) (right : Bool) : World :=
  advance renewable w owner r .canonical32 key false
    (Binding.splitState r.current right,weight r.current false right)

theorem split_actual (w : World) (owner : Nat) (r : Resident) (key : Token)
    (h : access w owner=some (r,.canonical32,key)) (right : Bool) :
    (split w owner r key right,weight r.current false right)∈nativeRows renewable w owner false := by
  rw [native_rows_from_access _ _ _ _ _ _ h false]
  exact List.mem_map.mpr ⟨_,(Binding.split_supported _ right).1,rfl⟩

theorem split_readouts (w : World) (owner : Nat) (r : Resident) (key : Token)
    (h : access w owner=some (r,.canonical32,key)) :
    current (split w owner r key false) owner=current (split w owner r key true) owner ∧
    ((Temporal.actual (split w owner r key false) owner).map (fun r => r.context))=
      ((Temporal.actual (split w owner r key true) owner).map (fun r => r.context)) ∧
    ((Temporal.actual (split w owner r key false) owner).map (fun r => classes model r.current))≠
      ((Temporal.actual (split w owner r key true) owner).map (fun r => classes model r.current)) := by
  have left := renewable_access_after w owner r .canonical32 key h false
    (Binding.splitState r.current false,weight r.current false false)
  have right := renewable_access_after w owner r .canonical32 key h false
    (Binding.splitState r.current true,weight r.current false true)
  have leftBinding := (access_facts _ _ _ _ _ left).1
  have rightBinding := (access_facts _ _ _ _ _ right).1
  refine ⟨?_,?_,?_⟩
  · simp only [split]
    rw [current_from_installed _ _ _ _ left,current_from_installed _ _ _ _ right]
    exact congrArg some (Binding.split_promotion _).1
  · simp only [Temporal.actual,split,leftBinding,rightBinding,Option.map_some,Temporal.frameROM]
    simp [advance,transact,put,renewable,AccountExecution.renewable]
  · simp only [Temporal.actual,split,leftBinding,rightBinding,Option.map_some,Temporal.frame,Temporal.frameROM,
      Option.some.injEq]
    intro equal
    exact (Binding.split_promotion _).2 (Option.some.inj equal)

theorem current_non_exposure (w v : World) (owner other : Nat)
    (r s : Resident) (key k : Token)
    (hw : access w owner=some (r,.canonical32,key))
    (hv : access v other=some (s,.canonical32,k))
    (iw : r.current.outside=false) (iv : s.current.outside=false) : current w owner=current v other := by
  rw [current_from_installed _ _ _ _ hw,current_from_installed _ _ _ _ hv,
    Binding.inside_public _ iw,Binding.inside_public _ iv]

theorem actual_branch_all_words (w v : World) (owner other : Nat)
    (r s : Resident) (key k : Token)
    (hw : access w owner=some (r,.canonical32,key))
    (hv : access v other=some (s,.canonical32,k)) (right : Bool) (word : List Bool) (out : List Nat) :
    emitted w owner (Binding.branch right) word out=emitted v other (Binding.branch right) word out := by
  rw [emitted_from_installed _ _ _ _ _ hw,emitted_from_installed _ _ _ _ _ hv]
  exact Binding.branchwise_universal _ _ right word out

theorem actual_split_joint_gap (w : World) (owner : Nat) (r : Resident) (key : Token)
    (h : access w owner=some (r,.canonical32,key)) :
    emitted (split w owner r key false) owner Binding.joint [false] [0]=1/8 ∧
    emitted (split w owner r key true) owner Binding.joint [false] [0]=3/8 := by
  have left := renewable_access_after w owner r .canonical32 key h false
    (Binding.splitState r.current false,weight r.current false false)
  have right := renewable_access_after w owner r .canonical32 key h false
    (Binding.splitState r.current true,weight r.current false true)
  simp only [split]
  rw [emitted_from_installed _ _ _ _ _ left,emitted_from_installed _ _ _ _ _ right]
  exact Binding.split_joint_gap r.current

theorem actual_joint_coherence (w v : World) (owner other : Nat) (r s : Resident) (key k : Token)
    (hw : access w owner=some (r,.canonical32,key))
    (hv : access v other=some (s,.canonical32,k))
    (same : Temporal.code (Temporal.frame w r key)=Temporal.code (Temporal.frame v s k))
    (word : List Bool) (out : List Nat) :
    emitted w owner Binding.joint word out=emitted v other Binding.joint word out := by
  rw [emitted_from_installed _ _ _ _ _ hw,emitted_from_installed _ _ _ _ _ hv]
  exact Binding.joint_coherence _ _ (congrArg Prod.fst same) word out

end CSTTT.FullNative02.Package
