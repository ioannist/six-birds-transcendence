import CSTTT.Fallback.CachedSeed
import CSTTT.Fallback.ReceiptAncestry
import CSTTT.Fallback.NativeDescendant

namespace CSTTT.FallbackTheory.GuardedFusion
open CSTTT.TransportTheory
open CSTTT.FallbackTheory.OperationalTrace
open CSTTT.FallbackTheory.SharedOperationalSeed
variable {H S T E R SC TC RR M : Type} [DecidableEq S] [DecidableEq T]
-- All new declarations are class (b); raw rows/tokens are primitives, stores and guards are computed.
structure Program (T : Type) where
  rows : T → T → List (T × Nat)
  scale : Nat
abbrev Credits := List (Nat × Nat)
structure World (S T : Type) where
  store : Store S T
  credits : Credits
structure Command (T : Type) where
  left : Nat
  right : Nat
  target : Nat
  leftAction : Nat
  rightAction : Nat
  outcome : T
def jointWeight (program : Program T) (left right outcome : T) : Nat :=
  ((program.rows left right).map (fun entry => if entry.1=outcome then entry.2 else 0)).sum
def rowValid (program : Program T) (left right : T) : Bool :=
  (program.rows left right).all (fun entry => decide (0<entry.2)) &&
    decide (((program.rows left right).map Prod.snd).sum=program.scale) && decide (0<program.scale)
def housed (store : Store S T) (owner : Nat) : Bool :=
  match store.read owner with
  | some (.target _) => store.active owner
  | _ => false
def allocated (credits : Credits) (owner : Nat) : Bool := credits.any (fun entry => decide (entry.2=owner))
def guard (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : Command T) (left right : T) : Bool :=
  rowValid program left right && decide (0<jointWeight program left right command.outcome) &&
    decide (0<b.targetActionStep left command.leftAction command.outcome) &&
    decide (0<b.targetActionStep right command.rightAction command.outcome) &&
    decide (command.left≠command.right) && (world.store.read command.target).isNone &&
    world.store.active command.left && world.store.active command.right &&
    decide ((world.credits.map Prod.fst).Nodup) &&
    world.credits.all (fun entry => housed world.store entry.2) &&
    allocated world.credits command.left && allocated world.credits command.right
def transfer (credits : Credits) (left right target : Nat) : Credits :=
  credits.map (fun entry => (entry.1,if entry.2=left ∨ entry.2=right then target else entry.2))
def merged (world : World S T) (command : Command T) : World S T :=
  ⟨⟨put world.store.read command.target (.target command.outcome),
    switch (switch (switch world.store.active command.left false) command.right false) command.target true,
    (command.left,command.target)::(command.right,command.target)::world.store.edges,
    world.store.clock+1,world.store.captured⟩,
    transfer world.credits command.left command.right command.target⟩
def step (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : Command T) : Option (World S T) := do
  let .target left ← world.store.read command.left | none
  let .target right ← world.store.read command.right | none
  if guard b program world command left right then some (merged world command) else none
def run (b : RawBridge H S T E R SC TC RR M) (program : Program T) :
    World S T → List (Command T) → Option (World S T)
  | world,[] => some world
  | world,command::rest => (step b program world command).bind (fun next => run b program next rest)
def actualRun (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T))
    (rawCredits : Option Credits) (commands : List (Command T)) : Option (World S T) := do
  let program ← rawProgram
  let credits ← rawCredits
  let originStore ← computedStore inputs
  let store ← NativeDescendant.run b originStore native
  run b program ⟨store,credits⟩ commands

theorem guard_iff (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : Command T) (left right : T) :
    guard b program world command left right=true ↔
      rowValid program left right=true ∧ 0<jointWeight program left right command.outcome ∧
      0<b.targetActionStep left command.leftAction command.outcome ∧
      0<b.targetActionStep right command.rightAction command.outcome ∧ command.left≠command.right ∧
      world.store.read command.target=none ∧ world.store.active command.left=true ∧
      world.store.active command.right=true ∧ (world.credits.map Prod.fst).Nodup ∧
      (∀ entry∈world.credits,housed world.store entry.2=true) ∧
      allocated world.credits command.left=true ∧ allocated world.credits command.right=true := by
  simp [guard,List.all_eq_true,and_assoc]
theorem step_present_iff (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : Command T) :
    (step b program world command).isSome ↔ ∃ left right,
      world.store.read command.left=some (.target left) ∧ world.store.read command.right=some (.target right) ∧
      guard b program world command left right=true := by
  cases hl : world.store.read command.left with
  | none => simp [step,hl]
  | some value =>
    cases value with
    | source payload => simp [step,hl]
    | record origin time payload => simp [step,hl]
    | target left =>
      cases hr : world.store.read command.right with
      | none => simp [step,hl,hr]
      | some value =>
        cases value with
        | source payload => simp [step,hl,hr]
        | record origin time payload => simp [step,hl,hr]
        | target right => simp [step,hl,hr]
theorem step_exact (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : Command T) (left right : T)
    (hl : world.store.read command.left=some (.target left))
    (hr : world.store.read command.right=some (.target right))
    (accepted : guard b program world command left right=true) :
    step b program world command=some (merged world command) := by simp [step,hl,hr,accepted]
theorem step_return (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world finished : World S T) (command : Command T) (executed : step b program world command=some finished) :
    ∃ left right,world.store.read command.left=some (.target left) ∧
      world.store.read command.right=some (.target right) ∧ guard b program world command left right=true ∧
      finished=merged world command := by
  have present : (step b program world command).isSome := by rw [executed]; rfl
  obtain ⟨left,right,hl,hr,accepted⟩ := (step_present_iff b program world command).mp present
  exact ⟨left,right,hl,hr,accepted,(Option.some.inj (executed.symm.trans (step_exact b program world command left right hl hr accepted)))⟩
theorem row_valid_iff (program : Program T) (left right : T) : rowValid program left right=true ↔
    (∀ entry∈program.rows left right,0<entry.2) ∧
      ((program.rows left right).map Prod.snd).sum=program.scale ∧ 0<program.scale := by
  simp [rowValid,List.all_eq_true,and_assoc]
theorem joint_conflict_rejects (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : Command T) (left right : T)
    (hl : world.store.read command.left=some (.target left))
    (hr : world.store.read command.right=some (.target right))
    (zero : jointWeight program left right command.outcome=0) : step b program world command=none := by
  simp [step,hl,hr,guard,zero]
theorem duplicate_credit_rejects (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : Command T) (duplicate : ¬(world.credits.map Prod.fst).Nodup) :
    step b program world command=none := by
  cases hl : world.store.read command.left with
  | none => simp [step,hl]
  | some value =>
    cases value with
    | source payload => simp [step,hl]
    | record origin time payload => simp [step,hl]
    | target left =>
      cases hr : world.store.read command.right with
      | none => simp [step,hl,hr]
      | some value =>
        cases value with
        | source payload => simp [step,hl,hr]
        | record origin time payload => simp [step,hl,hr]
        | target right => simp [step,hl,hr,guard,duplicate]
theorem transferred_tokens (credits : Credits) (left right target : Nat) :
    (transfer credits left right target).map Prod.fst=credits.map Prod.fst := by
  simp [transfer,List.map_map,Function.comp_def]
theorem merged_exclusive (world : World S T) (command : Command T)
    (exclusive : (world.credits.map Prod.fst).Nodup) : ((merged world command).credits.map Prod.fst).Nodup := by
  simpa only [merged,transferred_tokens] using exclusive
theorem transfer_member_iff (credits : Credits) (left right target token owner : Nat) :
    (token,owner)∈transfer credits left right target ↔ ∃ previous,
      (token,previous)∈credits ∧ owner=(if previous=left ∨ previous=right then target else previous) := by
  simp only [transfer,List.mem_map]
  constructor
  · rintro ⟨⟨oldToken,previous⟩,member,equal⟩
    have tokenEq := congrArg Prod.fst equal
    have ownerEq := congrArg Prod.snd equal
    simp only at tokenEq ownerEq
    subst oldToken
    exact ⟨previous,member,ownerEq.symm⟩
  · rintro ⟨previous,member,equal⟩
    exact ⟨(token,previous),member,by simp [equal]⟩
theorem missing_program_rejects (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (credits : Option Credits) (commands : List (Command T)) :
    actualRun b inputs native none credits commands=none := by simp [actualRun]
theorem missing_credits_rejects (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T)) (commands : List (Command T)) :
    actualRun b inputs native program none commands=none := by cases program <;> simp [actualRun]
theorem missing_prefix_rejects (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T)) (credits : Option Credits)
    (commands : List (Command T)) (missing : computedStore inputs=none) :
    actualRun b inputs native program credits commands=none := by cases program <;> cases credits <;> simp [actualRun,missing]
-- Class (b): housing is exactly a typed actual parent with an active bit.
theorem housed_iff (store : Store S T) (owner : Nat) : housed store owner=true ↔
    ∃ payload,store.read owner=some (.target payload) ∧ store.active owner=true := by
  cases read : store.read owner with
  | none => simp [housed,read]
  | some value =>
    cases value with
    | source payload => simp [housed,read]
    | record origin time payload => simp [housed,read]
    | target payload => simp [housed,read]
-- Class (b): allocation means an actual primitive token belongs to the declared event owner.
theorem allocated_iff (credits : Credits) (owner : Nat) : allocated credits owner=true ↔
    ∃ token,(token,owner)∈credits := by
  simp only [allocated,List.any_eq_true,decide_eq_true_eq]
  constructor
  · rintro ⟨⟨token,previous⟩,member,equal⟩
    simp only at equal
    subst previous
    exact ⟨token,member⟩
  · rintro ⟨token,member⟩
    exact ⟨(token,owner),member,rfl⟩
-- Class (b): actual transfer retains housing because the merged parents retire and their new owner is written.
theorem merged_housed_owner (world : World S T) (command : Command T) (owner : Nat)
    (fresh : world.store.read command.target=none) (available : housed world.store owner=true) :
    housed (merged world command).store (if owner=command.left ∨ owner=command.right then command.target else owner)=true := by
  by_cases parent : owner=command.left ∨ owner=command.right
  · simp [parent,merged,housed,put,switch]
  · obtain ⟨payload,read,active⟩ := (housed_iff world.store owner).mp available
    have separate := NativeDescendant.occupied_not_fresh world.store.read owner command.target (.target payload) read fresh
    have leftNe : owner≠command.left := fun equal => parent (Or.inl equal)
    have rightNe : owner≠command.right := fun equal => parent (Or.inr equal)
    simp [parent,merged,housed,put,switch,separate,leftNe,rightNe,read,active]
-- Class (b): every actual merged ledger entry is still housed on an active typed event.
theorem merged_housing (world : World S T) (command : Command T)
    (fresh : world.store.read command.target=none)
    (housing : ∀ entry∈world.credits,housed world.store entry.2=true) :
    ∀ entry∈(merged world command).credits,housed (merged world command).store entry.2=true := by
  intro entry member
  obtain ⟨old,contained,equal⟩ := List.mem_map.mp member
  subst entry
  exact merged_housed_owner world command old.2 fresh (housing old contained)
-- Class (b): actual target readout, parent retirement and retained capture journal follow from the checked step.
theorem actual_merged_readouts (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world finished : World S T) (command : Command T) (executed : step b program world command=some finished) :
    finished.store.read command.target=some (.target command.outcome) ∧ finished.store.active command.target=true ∧
    finished.store.active command.left=false ∧ finished.store.active command.right=false ∧
    finished.store.captured=world.store.captured := by
  obtain ⟨left,right,hl,hr,accepted,equal⟩ := step_return b program world finished command executed
  have checks := (guard_iff b program world command left right).mp accepted
  have fresh := checks.2.2.2.2.2.1
  have leftNe := NativeDescendant.occupied_not_fresh world.store.read command.left command.target (.target left) hl fresh
  have rightNe := NativeDescendant.occupied_not_fresh world.store.read command.right command.target (.target right) hr fresh
  rw [equal]
  simp [merged,put,switch,leftNe,rightNe]
-- Class (b): every checked step preserves identifiers, exclusivity and the same-world resource housing invariant.
theorem step_resource_return (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world finished : World S T) (command : Command T) (executed : step b program world command=some finished) :
    finished.credits.map Prod.fst=world.credits.map Prod.fst ∧ (finished.credits.map Prod.fst).Nodup ∧
      ∀ entry∈finished.credits,housed finished.store entry.2=true := by
  obtain ⟨left,right,hl,hr,accepted,equal⟩ := step_return b program world finished command executed
  obtain ⟨_,_,_,_,_,fresh,_,_,exclusive,housing,_,_⟩ := (guard_iff b program world command left right).mp accepted
  rw [equal]
  exact ⟨transferred_tokens _ _ _ _,merged_exclusive world command exclusive,merged_housing world command fresh housing⟩
-- Class (b): successful arbitrary finite merger streams conserve all tokens and preserve exclusive actual housing.
theorem run_resources (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (commands : List (Command T)) (world finished : World S T)
    (exclusive : (world.credits.map Prod.fst).Nodup)
    (housing : ∀ entry∈world.credits,housed world.store entry.2=true)
    (executed : run b program world commands=some finished) :
    finished.credits.map Prod.fst=world.credits.map Prod.fst ∧ (finished.credits.map Prod.fst).Nodup ∧
      ∀ entry∈finished.credits,housed finished.store entry.2=true := by
  induction commands generalizing world with
  | nil =>
    have equal : world=finished := Option.some.inj executed
    exact equal ▸ ⟨rfl,exclusive,housing⟩
  | cons command rest ih =>
    cases first : step b program world command with
    | none => simp [run,first] at executed
    | some next =>
      have tail : run b program next rest=some finished := by simpa [run,first] using executed
      have current := step_resource_return b program world next command first
      have later := ih next current.2.1 current.2.2 tail
      exact ⟨later.1.trans current.1,later.2⟩
-- Class (b): each fusion generates exactly two incoming event edges, retaining all prior edges.
theorem step_edges (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world finished : World S T) (command : Command T) (executed : step b program world command=some finished) :
    finished.store.edges=(command.left,command.target)::(command.right,command.target)::world.store.edges := by
  obtain ⟨_,_,_,_,_,equal⟩ := step_return b program world finished command executed
  rw [equal]; rfl
-- Class (b): successful merger streams retain the starting graph.
theorem run_edges_retained (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (commands : List (Command T)) (world finished : World S T) (executed : run b program world commands=some finished) :
    ∀ edge∈world.store.edges,edge∈finished.store.edges := by
  induction commands generalizing world with
  | nil =>
    have equal : world=finished := Option.some.inj executed
    exact equal ▸ (fun _ member => member)
  | cons command rest ih =>
    cases first : step b program world command with
    | none => simp [run,first] at executed
    | some next =>
      have tail : run b program next rest=some finished := by simpa [run,first] using executed
      intro edge member
      apply ih next tail edge
      rw [step_edges b program world next command first]
      simp [member]
-- Class (b): both genuine positive-length predecessor paths enter the actual common target, with separate sources allowed.
theorem step_paths (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world finished : World S T) (command : Command T) (leftSource rightSource : Nat)
    (leftPath : Path world.store.edges leftSource command.left)
    (rightPath : Path world.store.edges rightSource command.right)
    (executed : step b program world command=some finished) :
    Path finished.store.edges leftSource command.target ∧ Path finished.store.edges rightSource command.target := by
  rw [step_edges b program world finished command executed]
  have retain : ∀ edge∈world.store.edges,edge∈(command.left,command.target)::(command.right,command.target)::world.store.edges :=
    fun edge member => by simp [member]
  exact ⟨.extend (NativeDescendant.path_inclusion _ _ retain _ _ leftPath) (by simp),
    .extend (NativeDescendant.path_inclusion _ _ retain _ _ rightPath) (by simp)⟩
-- Class (b): a disconnected occupied twin cannot be used as a fresh merger output.
theorem step_boundary_retained (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world finished : World S T) (command : Command T) (twin : Nat) (content : Content S T)
    (occupied : world.store.read twin=some content) (boundary : ∀ parent,(parent,twin)∉world.store.edges)
    (executed : step b program world command=some finished) :
    finished.store.read twin=some content ∧ ∀ parent,(parent,twin)∉finished.store.edges := by
  obtain ⟨left,right,_,_,accepted,equal⟩ := step_return b program world finished command executed
  have checks := (guard_iff b program world command left right).mp accepted
  have separate := NativeDescendant.occupied_not_fresh world.store.read twin command.target content occupied checks.2.2.2.2.2.1
  rw [equal]
  exact ⟨by simp [merged,put,separate,occupied],by intro parent; simpa [merged,separate] using boundary parent⟩
-- Class (b): every successful finite merger stream preserves the actual occupied disconnected boundary.
theorem run_boundary_retained (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (commands : List (Command T)) (world finished : World S T) (twin : Nat) (content : Content S T)
    (occupied : world.store.read twin=some content) (boundary : ∀ parent,(parent,twin)∉world.store.edges)
    (executed : run b program world commands=some finished) :
    finished.store.read twin=some content ∧ ∀ parent,(parent,twin)∉finished.store.edges := by
  induction commands generalizing world with
  | nil =>
    have equal : world=finished := Option.some.inj executed
    exact equal ▸ ⟨occupied,boundary⟩
  | cons command rest ih =>
    cases first : step b program world command with
    | none => simp [run,first] at executed
    | some next =>
      have current := step_boundary_retained b program world next command twin content occupied boundary first
      have tail : run b program next rest=some finished := by simpa [run,first] using executed
      exact ih next current.1 current.2 tail
-- Class (b): actual cached path decision directly rejects the disconnected twin after every successful fusion stream.
theorem run_twin_readout (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (commands : List (Command T)) (world finished : World S T) (twin source : Nat) (content : Content S T)
    (occupied : world.store.read twin=some content) (boundary : ∀ parent,(parent,twin)∉world.store.edges)
    (executed : run b program world commands=some finished) :
    CachedSeed.pathBit finished.store.edges source twin=false := by
  have finalBoundary := (run_boundary_retained b program commands world finished twin content occupied boundary executed).2
  rw [CachedSeed.path_bit_eq]
  exact ExecutableSeed.no_incoming_bit_false _ source twin finalBoundary
-- Class (b): every partial actual run result is exactly a derived prefix/native/fusion execution witness.
theorem actual_run_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T))
    (rawCredits : Option Credits) (commands : List (Command T)) (finished : World S T) :
    actualRun b inputs native rawProgram rawCredits commands=some finished ↔ ∃ program credits originStore store,
      rawProgram=some program ∧ rawCredits=some credits ∧ computedStore inputs=some originStore ∧
      NativeDescendant.run b originStore native=some store ∧ run b program ⟨store,credits⟩ commands=some finished := by
  change rawProgram.bind (fun program => rawCredits.bind (fun credits =>
    (computedStore inputs).bind (fun originStore => (NativeDescendant.run b originStore native).bind
      (fun store => run b program ⟨store,credits⟩ commands))))=some finished ↔ _
  simp only [Option.bind_eq_some_iff]
  constructor
  · rintro ⟨program,hp,credits,hc,originStore,ho,store,hs,finished⟩
    exact ⟨program,credits,originStore,store,hp,hc,ho,hs,finished⟩
  · rintro ⟨program,credits,originStore,store,hp,hc,ho,hs,finished⟩
    exact ⟨program,hp,credits,hc,originStore,ho,store,hs,finished⟩
-- Class (b): the only raw-level structural path bit observes the actual computed final world.
def actualPath (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) (source target : Nat) : Option Bool :=
  (actualRun b inputs native program credits commands).map (fun world => CachedSeed.pathBit world.store.edges source target)
-- Class (b): actual None has exactly execution failure semantics on every partial assignment.
theorem actual_path_none_iff (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) (source target : Nat) :
    actualPath b inputs native program credits commands source target=none ↔
      actualRun b inputs native program credits commands=none := by
  simp [actualPath]
-- Class (b): true iff is exact actual positive-length final-graph reachability, never a recognition field.
theorem actual_path_true_iff (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) (source target : Nat) :
    actualPath b inputs native program credits commands source target=some true ↔ ∃ finished,
      actualRun b inputs native program credits commands=some finished ∧ Path finished.store.edges source target := by
  simp only [actualPath,Option.map_eq_some_iff,CachedSeed.path_bit_exact]
-- Class (b): false retains availability separately from exclusion; missing consumed primitives are never false defaults.
theorem actual_path_false_iff (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) (source target : Nat) :
    actualPath b inputs native program credits commands source target=some false ↔ ∃ finished,
      actualRun b inputs native program credits commands=some finished ∧ ¬Path finished.store.edges source target := by
  simp only [actualPath,Option.map_eq_some_iff]
  apply exists_congr
  intro finished
  apply and_congr_right
  intro _
  constructor
  · intro negative positive
    have bit := (CachedSeed.path_bit_exact _ _ _).mpr positive
    rw [negative] at bit
    cases bit
  · intro absent
    cases bit : CachedSeed.pathBit finished.store.edges source target with
    | false => rfl
    | true => exact False.elim (absent ((CachedSeed.path_bit_exact _ _ _).mp bit))
-- Class (b): the actual raw readout at an initial disconnected occupied twin is directly some false after every successful stream.
theorem actual_twin_path_false (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T))
    (rawCredits : Option Credits) (commands : List (Command T)) (finished : World S T)
    (twin source : Nat) (payload : T) (originStore : Store S T)
    (computed : computedStore inputs=some originStore) (occupied : originStore.read twin=some (.target payload))
    (boundary : ∀ parent,(parent,twin)∉originStore.edges)
    (executed : actualRun b inputs native rawProgram rawCredits commands=some finished) :
    actualPath b inputs native rawProgram rawCredits commands source twin=some false := by
  obtain ⟨program,credits,origin,store,hp,hc,ho,hs,hr⟩ := (actual_run_exact b inputs native rawProgram rawCredits commands finished).mp executed
  have same : origin=originStore := Option.some.inj (ho.symm.trans computed)
  subst origin
  have nativeBoundary := NativeDescendant.run_boundary_retained b native originStore store twin (.target payload) occupied boundary hs
  have bit := run_twin_readout b program commands ⟨store,credits⟩ finished twin source (.target payload) nativeBoundary.1 nativeBoundary.2 hr
  simp [actualPath,executed,bit]
open CSTTT.FallbackTheory.FiniteClosure CSTTT.FallbackTheory.FiniteHorn
-- Class (b): raw command addresses determine candidate merger edges; successful execution will realize all of them.
def fusionLedger (commands : List (Command T)) : List (Nat × Nat) :=
  commands.flatMap (fun command => [(command.left,command.target),(command.right,command.target)])
-- Class (b): a successful stream realizes its entire command-derived ledger in its actual final graph.
theorem run_ledger_realized (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (commands : List (Command T)) (world finished : World S T) (executed : run b program world commands=some finished) :
    ∀ edge∈fusionLedger commands,edge∈finished.store.edges := by
  induction commands generalizing world with
  | nil => simp [fusionLedger]
  | cons command rest ih =>
    cases first : step b program world command with
    | none => simp [run,first] at executed
    | some next =>
      have tail : run b program next rest=some finished := by simpa [run,first] using executed
      intro edge member
      simp only [fusionLedger,List.flatMap_cons,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with (head|head)|later
      · subst edge
        apply run_edges_retained b program rest next finished tail
        rw [step_edges b program world next command first]; simp
      · subst edge
        apply run_edges_retained b program rest next finished tail
        rw [step_edges b program world next command first]; simp
      · exact ih next tail edge later
-- Class (b): native receipts and fusion execution arise from the same checked prefix and actual program/credit reads.
def actualRecordedFusion (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T))
    (rawCredits : Option Credits) (commands : List (Command T)) :
    Option (World S T × List (ReceiptAncestry.Receipt S T)) := do
  let program ← rawProgram
  let credits ← rawCredits
  let (store,receipts) ← ReceiptAncestry.actualRecorded b inputs native
  let finished ← run b program ⟨store,credits⟩ commands
  some (finished,receipts)
-- Class (b): recording the native lineage does not alter any partial fusion execution result.
theorem recorded_fusion_execution_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T))
    (rawCredits : Option Credits) (commands : List (Command T)) :
    (actualRecordedFusion b inputs native rawProgram rawCredits commands).map Prod.fst=
      actualRun b inputs native rawProgram rawCredits commands := by
  cases hp : rawProgram with
  | none => simp [actualRecordedFusion,actualRun,hp]
  | some program =>
    cases hc : rawCredits with
    | none => simp [actualRecordedFusion,actualRun,hp,hc]
    | some credits =>
      cases ho : computedStore inputs with
      | none => simp [actualRecordedFusion,actualRun,ReceiptAncestry.actualRecorded,hp,hc,ho]
      | some originStore =>
        cases hn : ReceiptAncestry.recordedRun b originStore native with
        | none =>
          have nativeNone : NativeDescendant.run b originStore native=none := by
            simpa [hn] using (ReceiptAncestry.recorded_run_exact b native originStore).symm
          simp [actualRecordedFusion,actualRun,ReceiptAncestry.actualRecorded,hp,hc,ho,hn,nativeNone]
        | some result =>
          obtain ⟨store,receipts⟩ := result
          have nativeSome : NativeDescendant.run b originStore native=some store := by
            simpa [hn] using (ReceiptAncestry.recorded_run_exact b native originStore).symm
          cases hf : run b program ⟨store,credits⟩ commands <;>
            simp [actualRecordedFusion,actualRun,ReceiptAncestry.actualRecorded,hp,hc,ho,hn,nativeSome,hf]
-- Class (b): exact intermediate-witness characterization on all partial raw inputs.
theorem recorded_fusion_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T))
    (rawCredits : Option Credits) (commands : List (Command T))
    (finished : World S T) (receipts : List (ReceiptAncestry.Receipt S T)) :
    actualRecordedFusion b inputs native rawProgram rawCredits commands=some (finished,receipts) ↔
    ∃ program credits originStore store,rawProgram=some program ∧ rawCredits=some credits ∧
      computedStore inputs=some originStore ∧ ReceiptAncestry.recordedRun b originStore native=some (store,receipts) ∧
      run b program ⟨store,credits⟩ commands=some finished := by
  change rawProgram.bind (fun program => rawCredits.bind (fun credits =>
    (ReceiptAncestry.actualRecorded b inputs native).bind (fun result =>
      (run b program ⟨result.1,credits⟩ commands).bind (fun finalWorld => some (finalWorld,result.2)))))=some (finished,receipts) ↔ _
  simp only [Option.bind_eq_some_iff,Option.some.injEq,Prod.mk.injEq]
  constructor
  · rintro ⟨program,hp,credits,hc,⟨store,nativeReceipts⟩,hn,finalWorld,hf,equal,receiptEqual⟩
    subst finalWorld
    change nativeReceipts=receipts at receiptEqual
    subst nativeReceipts
    cases ho : computedStore inputs with
    | none => simp [ReceiptAncestry.actualRecorded,ho] at hn
    | some originStore =>
      have recorded : ReceiptAncestry.recordedRun b originStore native=some (store,receipts) := by
        simpa [ReceiptAncestry.actualRecorded,ho] using hn
      exact ⟨program,credits,originStore,store,hp,hc,rfl,recorded,hf⟩
  · rintro ⟨program,credits,originStore,store,hp,hc,ho,hn,hf⟩
    exact ⟨program,hp,credits,hc,(store,receipts),by simp [ReceiptAncestry.actualRecorded,ho,hn],finished,hf,rfl,rfl⟩
variable {N : Type} [DecidableEq N]
open ReceiptAncestry
-- Class (b): generalize the accepted Seed/ledger proof to the actual combined native/fusion edge ledger.
def closureBit (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (edges : List (Nat × Nat)) : N × N → Bool :=
  CachedSeed.readCache (CachedSeed.iterateCache (ExecutableSeed.pairEnum nodes)
    (gamma (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address edges))
    (seedBits b inputs address) (ExecutableSeed.pairEnum nodes).elems.length)
-- Class (b): generalize the accepted Seed/ledger proof to the actual combined native/fusion edge ledger.
theorem closure_bit_exact (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (edges : List (Nat × Nat)) :
    closureBit nodes address b inputs edges=ancestry (ExecutableSeed.pairEnum nodes)
      (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address edges) := by
  simp only [closureBit,CachedSeed.cache_iterate_exact,ancestry,closure]
-- Class (b): generalize the accepted Seed/ledger proof to the actual combined native/fusion edge ledger.
theorem closure_least (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (edges : List (Nat × Nat)) :
    gamma (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address edges)
      (closureBit nodes address b inputs edges)=closureBit nodes address b inputs edges ∧
    ∀ upper,Below (seedBits b inputs address) upper →
      Below (gamma (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address edges) upper) upper →
      Below (closureBit nodes address b inputs edges) upper := by
  rw [closure_bit_exact]
  exact ancestry_least_fixed _ _ _ _
-- Class (b): generalize the accepted Seed/ledger proof to the actual combined native/fusion edge ledger.
theorem closure_seed_retained (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (edges : List (Nat × Nat)) (root target : N)
    (seed : Seed b inputs (address root) (address target)) : closureBit nodes address b inputs edges (root,target)=true := by
  rw [closure_bit_exact]
  exact ancestry_contains_seed _ _ _ _ _ ((seed_bits_exact b inputs address (root,target)).mpr seed)
-- Class (b): generalize the accepted Seed/ledger proof to the actual combined native/fusion edge ledger.
theorem closure_descendant (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (edges : List (Nat × Nat)) (root parent target : N)
    (previous : closureBit nodes address b inputs edges (root,parent)=true)
    (edge : (address parent,address target)∈edges) :
    closureBit nodes address b inputs edges (root,target)=true := by
  have applied : gamma (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address edges)
      (closureBit nodes address b inputs edges) (root,target)=true := by
    apply (gamma_iff _ _ _ _ _).mpr
    right; right
    refine ⟨⟨[(root,parent)],(root,target)⟩,native_rule_member nodes root parent target,rfl,by simp,?_,?_⟩
    · exact (edge_enabled_exact address edges root parent target).mpr edge
    · intro pair member
      have equal : pair=(root,parent) := by simpa using member
      exact equal ▸ previous
  have fixed := congrFun (closure_least nodes address b inputs edges).1 (root,target)
  exact fixed ▸ applied
-- Class (b): generalize the accepted Seed/ledger proof to the actual combined native/fusion edge ledger.
theorem closure_no_seed_source (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (edges : List (Nat × Nat)) (root : N)
    (missing : ∀ target,¬ Seed b inputs (address root) (address target)) :
    ∀ target,closureBit nodes address b inputs edges (root,target)=false := by
  let blocked : N × N → Bool := fun pair => decide (pair.1=root)
  have seedOutside : ∀ pair,seedBits b inputs address pair=true → blocked pair=false := by
    intro pair member
    by_cases equal : pair.1=root
    · have impossible := missing pair.2
      have seed := (seed_bits_exact b inputs address pair).mp member
      rw [equal] at seed
      exact False.elim (impossible seed)
    · simp [blocked,equal]
  have ruleOutside : ∀ rule∈nativeRules nodes,edgeEnabled address edges rule=true →
      blocked rule.conclusion=true → ∃ predecessor∈rule.prerequisites,blocked predecessor=true := by
    intro rule member _ conclusion
    obtain ⟨source,parent,target,rfl⟩ := native_rule_shape nodes rule member
    exact ⟨(source,parent),by simp,conclusion⟩
  have excluded := component_exclusion (ExecutableSeed.pairEnum nodes) (seedBits b inputs address)
    (nativeRules nodes) (edgeEnabled address edges) blocked seedOutside ruleOutside
  intro target
  rw [closure_bit_exact]
  cases bit : ancestry (ExecutableSeed.pairEnum nodes) (seedBits b inputs address)
      (nativeRules nodes) (edgeEnabled address edges) (root,target) with
  | false => rfl
  | true => have impossible := excluded (root,target) bit; simp [blocked] at impossible
-- Class (b): generalize the accepted Seed/ledger proof to the actual combined native/fusion edge ledger.
theorem closure_origin (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (edges : List (Nat × Nat)) :
    ∀ pair,closureBit nodes address b inputs edges pair=true → ∃ seeded : N,
      Seed b inputs (address pair.1) (address seeded) ∧
        (seeded=pair.2 ∨ Path edges (address seeded) (address pair.2)) := by
  have origin : ∀ n pair,iterate
      (gamma (seedBits b inputs address) (nativeRules nodes) (edgeEnabled address edges))
      (seedBits b inputs address) n pair=true → ∃ seeded : N,
        Seed b inputs (address pair.1) (address seeded) ∧
          (seeded=pair.2 ∨ Path edges (address seeded) (address pair.2)) := by
    intro n
    induction n with
    | zero =>
      intro pair member
      exact ⟨pair.2,(seed_bits_exact b inputs address pair).mp member,Or.inl rfl⟩
    | succ n ih =>
      intro pair member
      rcases (gamma_iff _ _ _ _ _).mp member with seed|prior|⟨rule,mem,conclusion,_,guard,all⟩
      · exact ⟨pair.2,(seed_bits_exact b inputs address pair).mp seed,Or.inl rfl⟩
      · exact ih pair prior
      · obtain ⟨root,parent,target,rfl⟩ := native_rule_shape nodes rule mem
        cases conclusion
        have edge := (edge_enabled_exact address edges root parent target).mp guard
        obtain ⟨seeded,seed,previous⟩ := ih (root,parent) (all (root,parent) (by simp))
        refine ⟨seeded,seed,Or.inr ?_⟩
        rcases previous with equal|path
        · cases equal; exact .one edge
        · exact .extend path edge
  simpa only [closureBit,CachedSeed.cache_iterate_exact] using origin (ExecutableSeed.pairEnum nodes).elems.length
-- Class (b): generalize the accepted Seed/ledger proof to the actual combined native/fusion edge ledger.
theorem closure_ledger_complete (nodes : CSTTT.FiniteEnum N) (address : N → Nat) (b : RawBridge H S T E R SC TC RR M)
    (inputs : RawInputs S T) (edges : List (Nat × Nat))
    (cover : ∀ edge∈edges,∃ parent : N,address parent=edge.1)
    (root first last : N) (previous : closureBit nodes address b inputs edges (root,first)=true)
    (path : Path edges (address first) (address last)) :
    closureBit nodes address b inputs edges (root,last)=true := by
  have lift : ∀ a c,Path edges a c → ∀ start stop : N,
      address start=a → address stop=c → closureBit nodes address b inputs edges (root,start)=true →
        closureBit nodes address b inputs edges (root,stop)=true := by
    intro a c path
    induction path with
    | one member =>
      intro start stop startEq stopEq prior
      apply closure_descendant nodes address b inputs edges root start stop prior
      simpa [startEq,stopEq] using member
    | extend previous member ih =>
      intro start stop startEq stopEq prior
      obtain ⟨parent,parentEq⟩ := cover _ member
      apply closure_descendant nodes address b inputs edges root parent stop
      · exact ih start parent startEq parentEq prior
      · simpa [parentEq,stopEq] using member
  exact lift _ _ path first last rfl rfl previous
-- Class (b): this ledger combines only actual native receipt edges and the checked fusion stream's edges.
def combinedLedger (receipts : List (ReceiptAncestry.Receipt S T)) (commands : List (Command T)) : List (Nat × Nat) :=
  ReceiptAncestry.ledgerEdges receipts ++ fusionLedger commands
-- Class (b): every combined ledger edge is realized by its actual native or fusion execution.
theorem combined_ledger_realized (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (native : List (NativeDescendant.Command T)) (commands : List (Command T))
    (originStore store : Store S T) (credits : Credits) (finished : World S T)
    (receipts : List (ReceiptAncestry.Receipt S T))
    (recorded : ReceiptAncestry.recordedRun b originStore native=some (store,receipts))
    (fused : run b program ⟨store,credits⟩ commands=some finished) :
    ∀ edge∈combinedLedger receipts commands,edge∈finished.store.edges := by
  intro edge member
  rcases List.mem_append.mp member with nativeEdge|fusionEdge
  · exact run_edges_retained b program commands ⟨store,credits⟩ finished fused edge
      (ReceiptAncestry.ledger_edges_realized b native originStore store receipts recorded edge nativeEdge)
  · exact run_ledger_realized b program commands ⟨store,credits⟩ finished fused edge fusionEdge
-- Class (b): every actual predictive Seed retains its strict positive-length source path through both execution stages.
theorem combined_seed_path (b : RawBridge H S T E R SC TC RR M) (program : Program T) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (commands : List (Command T))
    (originStore store : Store S T) (credits : Credits) (finished : World S T)
    (receipts : List (ReceiptAncestry.Receipt S T)) (source seeded : Nat)
    (computed : computedStore inputs=some originStore)
    (recorded : ReceiptAncestry.recordedRun b originStore native=some (store,receipts))
    (fused : run b program ⟨store,credits⟩ commands=some finished) (seed : Seed b inputs source seeded) :
    Path finished.store.edges source seeded := by
  exact NativeDescendant.path_inclusion _ _
    (run_edges_retained b program commands ⟨store,credits⟩ finished fused) _ _
    (ReceiptAncestry.recorded_seed_path b inputs native originStore store receipts source seeded computed recorded seed)
-- Class (b): final ancestry uses its actual final graph frame and the computed combined ledger; no caller frame is accepted.
def finishedAncestry (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (Command T)) (result : World S T × List (ReceiptAncestry.Receipt S T))
    (source target : Nat) : Bool :=
  let nodes := ExecutableSeed.graphEnum result.1.store.edges source target
  closureBit nodes Subtype.val b inputs (combinedLedger result.2 commands)
    (⟨source,by simp [ExecutableSeed.graphAddresses]⟩,⟨target,by simp [ExecutableSeed.graphAddresses]⟩)
-- Class (b): exact return is a real predictive Seed followed by zero or more actual native/fusion ledger edges.
theorem combined_finished_exact (b : RawBridge H S T E R SC TC RR M) (program : Program T) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (commands : List (Command T))
    (originStore store : Store S T) (credits : Credits) (finished : World S T)
    (receipts : List (ReceiptAncestry.Receipt S T)) (source target : Nat)
    (computed : computedStore inputs=some originStore)
    (recorded : ReceiptAncestry.recordedRun b originStore native=some (store,receipts))
    (fused : run b program ⟨store,credits⟩ commands=some finished) :
    finishedAncestry b inputs commands (finished,receipts) source target=true ↔ ∃ seeded : Nat,
      Seed b inputs source seeded ∧ (seeded=target ∨ Path (combinedLedger receipts commands) seeded target) := by
  let nodes := ExecutableSeed.graphEnum finished.store.edges source target
  let root : ExecutableSeed.GraphNode finished.store.edges source target := ⟨source,by simp [ExecutableSeed.graphAddresses]⟩
  let last : ExecutableSeed.GraphNode finished.store.edges source target := ⟨target,by simp [ExecutableSeed.graphAddresses]⟩
  let edges := combinedLedger receipts commands
  constructor
  · intro member
    obtain ⟨seeded,seed,path⟩ := closure_origin nodes Subtype.val b inputs edges (root,last) member
    refine ⟨seeded.val,seed,?_⟩
    rcases path with equal|path
    · exact Or.inl (congrArg Subtype.val equal)
    · exact Or.inr path
  · rintro ⟨point,seed,path⟩
    have actualPath := combined_seed_path b program inputs native commands originStore store credits finished receipts source point computed recorded fused seed
    let start : ExecutableSeed.GraphNode finished.store.edges source target :=
      ⟨point,ReceiptAncestry.path_endpoint_in_frame finished.store.edges source target source point actualPath⟩
    have initial : closureBit nodes Subtype.val b inputs edges (root,start)=true :=
      closure_seed_retained nodes Subtype.val b inputs edges root start seed
    rcases path with equal|path
    · have same : start=last := Subtype.ext equal
      change closureBit nodes Subtype.val b inputs edges (root,last)=true
      rw [← same]; exact initial
    · have cover : ∀ edge∈edges,∃ parent : ExecutableSeed.GraphNode finished.store.edges source target,parent.val=edge.1 := by
        intro edge member
        have realized := combined_ledger_realized b program native commands originStore store credits finished receipts recorded fused edge member
        exact ⟨⟨edge.1,(ExecutableSeed.graph_endpoints finished.store.edges source target edge realized).1⟩,rfl⟩
      exact closure_ledger_complete nodes Subtype.val b inputs edges cover root start last initial path
-- Class (b): concatenate two positive-length paths without adding any reflexive edge.
theorem path_append (edges : List (Nat × Nat)) (source middle target : Nat)
    (first : Path edges source middle) (second : Path edges middle target) : Path edges source target := by
  induction second with
  | one member => exact .extend first member
  | extend previous member ih => exact .extend ih member
-- Class (b): ancestry true forces an actual positive-length source path in the final world; the converse is deliberately not assumed.
theorem combined_finished_path (b : RawBridge H S T E R SC TC RR M) (program : Program T) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (commands : List (Command T))
    (originStore store : Store S T) (credits : Credits) (finished : World S T)
    (receipts : List (ReceiptAncestry.Receipt S T)) (source target : Nat)
    (computed : computedStore inputs=some originStore)
    (recorded : ReceiptAncestry.recordedRun b originStore native=some (store,receipts))
    (fused : run b program ⟨store,credits⟩ commands=some finished)
    (member : finishedAncestry b inputs commands (finished,receipts) source target=true) :
    Path finished.store.edges source target := by
  obtain ⟨point,seed,path⟩ := (combined_finished_exact b program inputs native commands originStore store credits finished receipts source target computed recorded fused).mp member
  have initial := combined_seed_path b program inputs native commands originStore store credits finished receipts source point computed recorded fused seed
  rcases path with equal|path
  · exact equal ▸ initial
  · exact path_append _ _ _ _ initial (NativeDescendant.path_inclusion _ _
      (combined_ledger_realized b program native commands originStore store credits finished receipts recorded fused) _ _ path)
-- Class (b): actual scientific ancestry observes only the actual optional recorded shared-input execution.
def actualAncestry (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) (source target : Nat) : Option Bool :=
  (actualRecordedFusion b inputs native program credits commands).map (fun result => finishedAncestry b inputs commands result source target)
-- Class (b): scientific absence is exactly actual execution failure for all partial inputs.
theorem actual_ancestry_none_iff (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) (source target : Nat) :
    actualAncestry b inputs native program credits commands source target=none ↔
      actualRun b inputs native program credits commands=none := by
  simp only [actualAncestry,Option.map_eq_none_iff]
  rw [← recorded_fusion_execution_exact b inputs native program credits commands]
  simp
-- Class (b): positive ancestry exactly reconstructs the computed prefix, accepted native receipts and successful guarded merger stream.
theorem actual_ancestry_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T))
    (rawCredits : Option Credits) (commands : List (Command T)) (source target : Nat) :
    actualAncestry b inputs native rawProgram rawCredits commands source target=some true ↔
    ∃ program credits originStore store finished receipts,rawProgram=some program ∧ rawCredits=some credits ∧
      computedStore inputs=some originStore ∧ ReceiptAncestry.recordedRun b originStore native=some (store,receipts) ∧
      run b program ⟨store,credits⟩ commands=some finished ∧ ∃ seeded : Nat,
        Seed b inputs source seeded ∧ (seeded=target ∨ Path (combinedLedger receipts commands) seeded target) := by
  constructor
  · intro member
    obtain ⟨⟨finished,receipts⟩,recorded,bit⟩ := Option.map_eq_some_iff.mp member
    obtain ⟨program,credits,originStore,store,hp,hc,ho,hn,hf⟩ := (recorded_fusion_exact b inputs native rawProgram rawCredits commands finished receipts).mp recorded
    exact ⟨program,credits,originStore,store,finished,receipts,hp,hc,ho,hn,hf,
      (combined_finished_exact b program inputs native commands originStore store credits finished receipts source target ho hn hf).mp bit⟩
  · rintro ⟨program,credits,originStore,store,finished,receipts,hp,hc,ho,hn,hf,origin⟩
    apply Option.map_eq_some_iff.mpr
    exact ⟨(finished,receipts),(recorded_fusion_exact b inputs native rawProgram rawCredits commands finished receipts).mpr ⟨program,credits,originStore,store,hp,hc,ho,hn,hf⟩,
      (combined_finished_exact b program inputs native commands originStore store credits finished receipts source target ho hn hf).mpr origin⟩
-- Class (b): direct some-false is available execution with no scientific ancestry, separate from failed consumed primitives.
theorem actual_ancestry_false_iff (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) (source target : Nat) :
    actualAncestry b inputs native program credits commands source target=some false ↔
      (actualRun b inputs native program credits commands).isSome ∧
        actualAncestry b inputs native program credits commands source target≠some true := by
  rw [← recorded_fusion_execution_exact b inputs native program credits commands]
  cases read : actualRecordedFusion b inputs native program credits commands with
  | none => simp [actualAncestry,read]
  | some result => cases bit : finishedAncestry b inputs commands result source target <;> simp [actualAncestry,read,bit]
-- Class (b): missing consumed raw source rejects the actual scientific readout, including all fusion programs/credits.
theorem missing_source_ancestry (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) (source target : Nat) (missing : inputs.rawSource=none) :
    actualAncestry b inputs native program credits commands source target=none := by
  apply (actual_ancestry_none_iff b inputs native program credits commands source target).mpr
  apply missing_prefix_rejects
  simp [computedStore,SourceCheckedTrace.checkedExecute,missing]
-- Class (b): a positive actual scientific readout implies the actual structural readout, not conversely.
theorem actual_ancestry_implies_path (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) (source target : Nat)
    (positive : actualAncestry b inputs native program credits commands source target=some true) :
    actualPath b inputs native program credits commands source target=some true := by
  obtain ⟨⟨finished,receipts⟩,recorded,bit⟩ := Option.map_eq_some_iff.mp positive
  obtain ⟨joint,allocation,originStore,store,hp,hc,ho,hn,hf⟩ :=
    (recorded_fusion_exact b inputs native program credits commands finished receipts).mp recorded
  have execution : actualRun b inputs native program credits commands=some finished := by
    rw [← recorded_fusion_execution_exact b inputs native program credits commands,recorded]; rfl
  apply (actual_path_true_iff b inputs native program credits commands source target).mpr
  exact ⟨finished,execution,combined_finished_path b joint inputs native commands originStore store allocation finished receipts source target ho hn hf bit⟩
-- Class (b): every actual successful native/fusion stream returns some false at an occupied disconnected twin for scientific ancestry itself.
theorem actual_twin_ancestry_false (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) (finished : World S T)
    (originStore : Store S T) (twin source : Nat) (payload : T)
    (computed : computedStore inputs=some originStore) (occupied : originStore.read twin=some (.target payload))
    (boundary : ∀ parent,(parent,twin)∉originStore.edges)
    (executed : actualRun b inputs native program credits commands=some finished) :
    actualAncestry b inputs native program credits commands source twin=some false := by
  apply (actual_ancestry_false_iff b inputs native program credits commands source twin).mpr
  refine ⟨by rw [executed]; rfl,?_⟩
  intro positive
  have structural := actual_ancestry_implies_path b inputs native program credits commands source twin positive
  have negative := actual_twin_path_false b inputs native program credits commands finished twin source payload originStore computed occupied boundary executed
  rw [negative] at structural
  cases structural
-- Class (b): structural paths and arbitrary supported joint rows cannot create ancestry for a source without any actual predictive Seed.
theorem actual_no_seed_source_false (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) (source target : Nat)
    (missing : ∀ target,¬Seed b inputs source target) :
    actualAncestry b inputs native program credits commands source target=some false ↔
      (actualRun b inputs native program credits commands).isSome := by
  constructor
  · intro negative
    exact ((actual_ancestry_false_iff b inputs native program credits commands source target).mp negative).1
  · intro present
    apply (actual_ancestry_false_iff b inputs native program credits commands source target).mpr
    refine ⟨present,?_⟩
    intro positive
    obtain ⟨_,_,_,_,_,_,_,_,_,_,_,seeded,seed,_⟩ := (actual_ancestry_exact b inputs native program credits commands source target).mp positive
    exact missing seeded seed
-- Class (b): empty-prefix primitive failure propagates through every finite suffix.
theorem rejected_head (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world : World S T) (command : Command T) (rest : List (Command T))
    (rejected : step b program world command=none) : run b program world (command::rest)=none := by
  simp [run,rejected]
-- Class (b): every command of a successful actual stream has genuinely checked intermediate worlds, not supplied support certificates.
theorem every_command_checked (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (commands : List (Command T)) (world finished : World S T) (executed : run b program world commands=some finished) :
    ∀ command∈commands,∃ before after,step b program before command=some after := by
  induction commands generalizing world with
  | nil => simp
  | cons command rest ih =>
    cases first : step b program world command with
    | none => simp [run,first] at executed
    | some next =>
      have tail : run b program next rest=some finished := by simpa [run,first] using executed
      intro query member
      rcases List.mem_cons.mp member with head|later
      · subst query; exact ⟨world,next,first⟩
      · exact ih next tail query later
-- Class (b): both already-related predecessor coordinates enter the actual common target under a checked executed fusion command.
theorem executed_fusion_ancestry (nodes : CSTTT.FiniteEnum N) (address : N → Nat)
    (b : RawBridge H S T E R SC TC RR M) (program : Program T) (inputs : RawInputs S T)
    (commands : List (Command T)) (world finished : World S T) (receipts : List (ReceiptAncestry.Receipt S T))
    (command : Command T) (member : command∈commands) (executed : run b program world commands=some finished)
    (leftRoot rightRoot left right target : N) (leftEq : address left=command.left)
    (rightEq : address right=command.right) (targetEq : address target=command.target)
    (leftAncestor : closureBit nodes address b inputs (combinedLedger receipts commands) (leftRoot,left)=true)
    (rightAncestor : closureBit nodes address b inputs (combinedLedger receipts commands) (rightRoot,right)=true) :
    closureBit nodes address b inputs (combinedLedger receipts commands) (leftRoot,target)=true ∧
    closureBit nodes address b inputs (combinedLedger receipts commands) (rightRoot,target)=true ∧
    ∃ before after leftPayload rightPayload,
      step b program before command=some after ∧ before.store.read command.left=some (.target leftPayload) ∧
      before.store.read command.right=some (.target rightPayload) ∧ guard b program before command leftPayload rightPayload=true := by
  have leftEdge : (address left,address target)∈combinedLedger receipts commands := by
    apply List.mem_append.mpr; right
    exact List.mem_flatMap.mpr ⟨command,member,by simp [leftEq,targetEq]⟩
  have rightEdge : (address right,address target)∈combinedLedger receipts commands := by
    apply List.mem_append.mpr; right
    exact List.mem_flatMap.mpr ⟨command,member,by simp [rightEq,targetEq]⟩
  obtain ⟨before,after,checked⟩ := every_command_checked b program commands world finished executed command member
  obtain ⟨leftPayload,rightPayload,hl,hr,accepted,_⟩ := step_return b program before after command checked
  exact ⟨closure_descendant nodes address b inputs _ leftRoot left target leftAncestor leftEdge,
    closure_descendant nodes address b inputs _ rightRoot right target rightAncestor rightEdge,
    before,after,leftPayload,rightPayload,checked,hl,hr,accepted⟩
-- Class (b): mathematical provenance is defined from actual predictive Seed and a specified edge ledger, not selected as an output witness.
def Provenance (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (edges : List (Nat × Nat)) (source target : Nat) : Prop :=
  ∃ seeded,Seed b inputs source seeded ∧ (seeded=target ∨ Path edges seeded target)
-- Class (b): closure means propagation along an explicitly specified ledger edge.
def LedgerClosed (edges : List (Nat × Nat)) (relation : Nat → Nat → Prop) : Prop :=
  ∀ source parent target,(parent,target)∈edges → relation source parent → relation source target
-- Class (b): every nonseed relation member has a genuinely related predecessor and a declared ledger edge.
def LedgerNoExNihilo (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (edges : List (Nat × Nat)) (relation : Nat → Nat → Prop) : Prop :=
  ∀ source target,relation source target → Seed b inputs source target ∨
    ∃ parent,relation source parent ∧ (parent,target)∈edges
-- Class (b): ledger closure propagates along every positive-length ledger path.
theorem closed_path (edges : List (Nat × Nat)) (relation : Nat → Nat → Prop)
    (closed : LedgerClosed edges relation) (source first last : Nat)
    (initial : relation source first) (path : Path edges first last) : relation source last := by
  induction path with
  | one member => exact closed _ _ _ member initial
  | extend previous member ih => exact closed _ _ _ member ih
-- Class (b): this is the original least operational ancestry schema, with concrete derived closed/no-ex-nihilo predicates.
theorem provenance_least (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (edges : List (Nat × Nat)) :
    CSTTT.Prospects.LeastOperationalAncestry Nat (Seed b inputs) (Provenance b inputs edges)
      (LedgerClosed edges) (LedgerNoExNihilo b inputs edges) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro source target seed
    exact ⟨target,seed,Or.inl rfl⟩
  · intro source parent target member previous
    obtain ⟨point,seed,path⟩ := previous
    refine ⟨point,seed,Or.inr ?_⟩
    rcases path with equal|path
    · subst point; exact .one member
    · exact .extend path member
  · intro source target member
    obtain ⟨point,seed,path⟩ := member
    rcases path with equal|path
    · exact Or.inl (equal ▸ seed)
    · right
      cases path with
      | one edge => exact ⟨point,⟨point,seed,Or.inl rfl⟩,edge⟩
      | extend previous edge => exact ⟨_,⟨point,seed,Or.inr previous⟩,edge⟩
  · intro relation contains closed _ source target member
    obtain ⟨point,seed,path⟩ := member
    have initial := contains source point seed
    rcases path with equal|path
    · exact equal ▸ initial
    · exact closed_path edges relation closed source point target initial path
-- Class (b): actual optional execution supplies the provenance equivalence for every query simultaneously.
theorem actual_relation_exact (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T))
    (rawCredits : Option Credits) (commands : List (Command T)) (finished : World S T)
    (receipts : List (ReceiptAncestry.Receipt S T))
    (recorded : actualRecordedFusion b inputs native rawProgram rawCredits commands=some (finished,receipts)) :
    ∀ source target,actualAncestry b inputs native rawProgram rawCredits commands source target=some true ↔
      Provenance b inputs (combinedLedger receipts commands) source target := by
  obtain ⟨program,credits,originStore,store,hp,hc,ho,hn,hf⟩ := (recorded_fusion_exact b inputs native rawProgram rawCredits commands finished receipts).mp recorded
  intro source target
  simp only [actualAncestry,recorded,Option.map_some,Option.some.injEq]
  exact combined_finished_exact b program inputs native commands originStore store credits finished receipts source target ho hn hf
-- Class (b): the original least-ancestry statement returns to the actual readout of every successfully computed partial campaign execution.
theorem actual_least_operational_ancestry (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T))
    (rawCredits : Option Credits) (commands : List (Command T)) (finished : World S T)
    (receipts : List (ReceiptAncestry.Receipt S T))
    (recorded : actualRecordedFusion b inputs native rawProgram rawCredits commands=some (finished,receipts)) :
    CSTTT.Prospects.LeastOperationalAncestry Nat (Seed b inputs)
      (fun source target => actualAncestry b inputs native rawProgram rawCredits commands source target=some true)
      (LedgerClosed (combinedLedger receipts commands)) (LedgerNoExNihilo b inputs (combinedLedger receipts commands)) := by
  have equal : (fun source target => actualAncestry b inputs native rawProgram rawCredits commands source target=some true)=
      Provenance b inputs (combinedLedger receipts commands) := by
    funext source target
    exact propext (actual_relation_exact b inputs native rawProgram rawCredits commands finished receipts recorded source target)
  rw [equal]
  exact provenance_least b inputs (combinedLedger receipts commands)
-- Class (b): the original disconnected-twin exclusion schema holds for the actual structural and scientific readouts on every partial assignment.
theorem actual_independent_twin_exclusion (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (Command T)) :
    CSTTT.Prospects.IndependentTwinExclusion Nat
      (fun source target => actualPath b inputs native program credits commands source target=some true)
      (fun source target => actualAncestry b inputs native program credits commands source target=some true) := by
  intro source twin disconnected ancestor
  exact disconnected (actual_ancestry_implies_path b inputs native program credits commands source twin ancestor)
end CSTTT.FallbackTheory.GuardedFusion
