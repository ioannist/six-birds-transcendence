import CSTTT.Targets.GenericHandoff.NativeComposition.EpisodeReplay

/-! The retrospective first-target future and the next-source future share
the actual middle publication. Their roots have physical origins 0 and 2.
Closure includes every declared outcome, including outcomes of weight zero. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.MiddleFuture
open RegisterInterpreter ModeExecution EpisodeMap CSTTT.TransportTheory

abbrev source := MemoryFrames.raw true false true firstNames
abbrev target := MemoryFrames.raw false true true secondNames

def initializer (cell : Owner) (copy : Bool) (start : Nat) :
    RegisterInitialization.InitialProgram Owner MemoryValue Unit (fun _ => Frame.State) Factor :=
  fun _ => .map (fun p : (Input × Input) × Factor =>
    let d := (MemoryFrames.selectInput copy p.1).temporal
    (⟨(d.histories p.2).getD 0 p.2,start,start,(d.histories p.2,routePath d p.2),
      d.receiverFunded && d.resource.rechargeAvailable && decide (d.ledger.initial ≥ d.ledger.cost)⟩ : Frame.State))
    (.pair (.cell cell) (.environment id))

theorem initializer_ready (cell : Owner) (copy : Bool) (start : Nat)
    (a : Assignment Owner MemoryValue) (ha : (a cell).isSome=true) :
    RegisterInitialization.Ready (initializer cell copy start) a := by
  intro r k hk
  have he : k=cell := by simpa [initializer,Expr.dependencies] using hk
  subst k
  exact ha

theorem initializer_missing (cell : Owner) (copy : Bool) (start : Nat)
    (a : Assignment Owner MemoryValue) (hm : a cell=none) (h : Factor) :
    RegisterInitialization.evaluate (initializer cell copy start) a h ()=none := by
  simp [RegisterInitialization.evaluate,initializer,Expr.eval,hm]

theorem source_ready : RegisterFuture.RawReady source nativeAssignment :=
  MemoryFrames.ready true false true firstNames nativeAssignment rfl
theorem target_ready : RegisterFuture.RawReady target nativeAssignment :=
  MemoryFrames.ready false true true secondNames nativeAssignment rfl
theorem map_ready : RegisterSubstitution.Ready translation nativeAssignment :=
  translation_ready nativeAssignment rfl

abbrev sourceInitReady := initializer_ready true false 0 nativeAssignment rfl
abbrev targetInitReady := initializer_ready false true 2 nativeAssignment rfl
noncomputable def sourceRoot (h : Factor) : Frame.Registers :=
  RegisterInitialization.initial (initializer true false 0) nativeAssignment sourceInitReady h
noncomputable def targetRoot (h : Factor) : Frame.Registers :=
  RegisterInitialization.initial (initializer false true 2) nativeAssignment targetInitReady h

def middleState (h : Factor) (time : Nat) : Frame.State :=
  ⟨h,time,time,(List.replicate 4 h,[false,true]),true⟩

theorem root_equation (h : Factor) (start : Nat) (cell : Owner) (copy : Bool)
    (hp : MemoryFrames.selectInput copy (episodePair (if cell then 0 else 1))=roundInput 1)
    (hr : RegisterInitialization.Ready (initializer cell copy start) nativeAssignment) :
    RegisterInitialization.initial (initializer cell copy start) nativeAssignment hr h =
      Frame.pack (middleState h start) := by
  funext r
  have he := RegisterInitialization.initial_eq (initializer cell copy start) nativeAssignment hr h r
  change some (let d := (MemoryFrames.selectInput copy (episodePair (if cell then 0 else 1))).temporal
    (⟨(d.histories h).getD 0 h,start,start,(d.histories h,routePath d h),
      d.receiverFunded && d.resource.rechargeAvailable && decide (d.ledger.initial ≥ d.ledger.cost)⟩ : Frame.State)) =
      some (RegisterInitialization.initial (initializer cell copy start) nativeAssignment hr h r) at he
  simp only [hp,round_path] at he
  exact (Option.some.inj he).symm

theorem source_root (h : Factor) : sourceRoot h=Frame.pack (middleState h 0) :=
  root_equation h 0 true false rfl sourceInitReady
theorem target_root (h : Factor) : targetRoot h=Frame.pack (middleState h 2) :=
  root_equation h 2 false true rfl targetInitReady

noncomputable def sourceRoots := factors.map sourceRoot
noncomputable def targetRoots := factors.map targetRoot
abbrev SourceClosure := RegisterFuture.Closure source nativeAssignment source_ready sourceRoots
abbrev TargetClosure := RegisterFuture.Closure target nativeAssignment target_ready targetRoots

theorem source_next (x : Frame.Registers) (da : Unit × Bool) (o : Factor) :
    RegisterFuture.next source nativeAssignment source_ready x da o=Frame.pack (stepState (x ()) o) := by
  rw [MemoryFrames.next true false true firstNames nativeAssignment source_ready (episodePair 0) rfl]
  exact congrArg Frame.pack (round_update true 1 (x ()) da.2 o)

theorem target_next (x : Frame.Registers) (da : Unit × Bool) (o : Factor) :
    RegisterFuture.next target nativeAssignment target_ready x da o=Frame.pack (stepState (x ()) o) := by
  rw [MemoryFrames.next false true true secondNames nativeAssignment target_ready (episodePair 1) rfl]
  exact congrArg Frame.pack (round_update true 1 (x ()) da.2 o)

def Shape (x : Frame.Registers) : Prop :=
  (x ()).funded=true ∧ ∃ h : Factor, (x ()).residue=(List.replicate 4 h,[false,true])

theorem closure_shape (x : Frame.Registers) (hx : SourceClosure x) : Shape x := by
  induction hx with
  | root x hm =>
    obtain ⟨h,_,rfl⟩ := List.mem_map.mp hm
    rw [source_root]
    exact ⟨rfl,h,rfl⟩
  | step hx da o ho ih =>
    change Shape (RegisterFuture.next source nativeAssignment source_ready _ da o)
    rw [source_next]
    exact ih

theorem middle_past_double (h : Factor) :
    List.replicate 4 h=List.replicate 2 h++List.replicate 2 h := rfl

theorem translation_on_closure (x : Frame.Registers) (hx : SourceClosure x) :
    RegisterSubstitution.translate translation nativeAssignment map_ready x ()=Frame.pack (shifted (x ())) := by
  rw [native_translation]
  obtain ⟨_,h,hp⟩ := closure_shape x hx
  exact congrArg Frame.pack (past_restored (x ()) (List.replicate 2 h)
    ((congrArg Prod.fst hp).trans (middle_past_double h)))

theorem translated_root (h : Factor) :
    RegisterSubstitution.translate translation nativeAssignment map_ready (sourceRoot h) ()=targetRoot h := by
  rw [translation_on_closure _ (FutureClosure.root _ (List.mem_map.mpr ⟨h,factor_mem h,rfl⟩)),source_root,target_root]
  rfl

theorem translated_successor (x : Frame.Registers) (hx : SourceClosure x) (da : Unit × Bool) (o : Factor) :
    RegisterSubstitution.translate translation nativeAssignment map_ready
      (RegisterFuture.next source nativeAssignment source_ready x da o) () =
    RegisterFuture.next target nativeAssignment target_ready
      (RegisterSubstitution.translate translation nativeAssignment map_ready x ()) da o := by
  have hn : SourceClosure (RegisterFuture.next source nativeAssignment source_ready x da o) :=
    FutureClosure.step hx da o (factor_mem o)
  rw [translation_on_closure _ hn,translation_on_closure x hx,source_next,target_next]
  rfl

theorem translated_closure (x : Frame.Registers) (hx : SourceClosure x) :
    TargetClosure (RegisterSubstitution.translate translation nativeAssignment map_ready x ()) := by
  induction hx with
  | root x hm =>
    obtain ⟨h,hh,rfl⟩ := List.mem_map.mp hm
    rw [translated_root]
    exact FutureClosure.root _ (List.mem_map.mpr ⟨h,hh,rfl⟩)
  | step hx da o ho ih =>
    change TargetClosure (RegisterSubstitution.translate translation nativeAssignment map_ready
      (RegisterFuture.next source nativeAssignment source_ready _ da o) ())
    rw [translated_successor _ hx]
    exact FutureClosure.step ih da o ho

theorem translation_is_supported_episode (x : Frame.Registers) (hx : SourceClosure x) :
    SupportedAcquisitionSequence.postExit firstAcquisition nativeAssignment native_first_ready
      (x ()).factor (x ()).factor
      (SupportedAcquisitionSequence.fromStart firstAcquisition nativeAssignment native_first_ready
        (ModeExecution.pack (halfPast (x ()),false)) (x ()).factor) =
      some (ModeExecution.pack
        (RegisterSubstitution.translate translation nativeAssignment map_ready x () (),true)) :=
  translation_from_interpreted_episode native_first_ready map_ready x (closure_shape x hx).1

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.MiddleFuture
