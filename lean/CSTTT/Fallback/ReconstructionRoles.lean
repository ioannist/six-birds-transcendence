import CSTTT.Fallback.GuardedFusion

namespace CSTTT.FallbackTheory.FusionRolesPrototype
open CSTTT.TransportTheory
open CSTTT.FallbackTheory.OperationalTrace
open CSTTT.FallbackTheory.SharedOperationalSeed
open CSTTT.FallbackTheory.GuardedFusion
variable {H S T E R SC TC RR M : Type} [DecidableEq S] [DecidableEq T]
-- Class (b): only an actual historical source in the computed prefix can seed a source coordinate.
omit [DecidableEq T] in
theorem seed_requires_source (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (origin : Store S T) (source target : Nat) (computed : computedStore inputs=some origin)
    (seed : Seed b inputs source target) : ∃ payload,origin.read source=some (.source payload) := by
  obtain ⟨original,decoded,edges,read,_,_⟩ := seed
  unfold readAt at read
  rw [computed] at read
  cases hs : origin.read source with
  | none => simp [hs] at read
  | some content =>
    cases content with
    | source payload => exact ⟨payload,rfl⟩
    | target payload => simp [hs] at read
    | record address time payload => simp [hs] at read
-- Class (b): absence of a historical source directly refutes every Seed, on every partial input.
omit [DecidableEq T] in
theorem non_source_has_no_seed (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (origin : Store S T) (source : Nat) (computed : computedStore inputs=some origin)
    (notSource : ∀ payload,origin.read source≠some (.source payload)) : ∀ target,¬Seed b inputs source target := by
  intro target seed
  obtain ⟨payload,read⟩ := seed_requires_source b inputs origin source target computed seed
  exact notSource payload read
-- Class (b): actual available scientific ancestry is some false at every non-source root.
theorem non_source_actual_ancestry_false (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (GuardedFusion.Command T)) (origin : Store S T) (source target : Nat)
    (computed : computedStore inputs=some origin) (notSource : ∀ payload,origin.read source≠some (.source payload)) :
    actualAncestry b inputs native program credits commands source target=some false ↔
      (actualRun b inputs native program credits commands).isSome := by
  exact actual_no_seed_source_false b inputs native program credits commands source target
    (non_source_has_no_seed b inputs origin source computed notSource)
-- Class (b): a typed target query is derived from the same optional full execution.
def actualTarget (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (GuardedFusion.Command T)) (target : Nat) : Option T := do
  let world ← actualRun b inputs native program credits commands
  let .target payload ← world.store.read target | none
  some payload
-- Class (b): exact all-partial target availability, with no default world or payload.
theorem actual_target_some_iff (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (GuardedFusion.Command T)) (target : Nat) (payload : T) :
    actualTarget b inputs native program credits commands target=some payload ↔ ∃ world,
      actualRun b inputs native program credits commands=some world ∧ world.store.read target=some (.target payload) := by
  unfold actualTarget
  cases hr : actualRun b inputs native program credits commands with
  | none => simp
  | some world =>
    cases hc : world.store.read target with
    | none => simp [hc]
    | some content => cases content <;> simp [hc]
-- Class (b): absence distinguishes unavailable execution from an available non-target read on every partial input.
theorem actual_target_none_iff (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (GuardedFusion.Command T)) (target : Nat) :
    actualTarget b inputs native program credits commands target=none ↔
      actualRun b inputs native program credits commands=none ∨ ∃ world,
        actualRun b inputs native program credits commands=some world ∧
        ∀ payload,world.store.read target≠some (.target payload) := by
  cases hr : actualRun b inputs native program credits commands with
  | none => simp [actualTarget,hr]
  | some world =>
    cases hc : world.store.read target with
    | none => simp [actualTarget,hr,hc]
    | some content => cases content <;> simp [actualTarget,hr,hc]
-- Class (b): direct refutation when the original schema turns a target branch into a historical source.
theorem original_fusion_schema_refuted (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (GuardedFusion.Command T)) (origin : Store S T)
    (source left right fused : Nat) (payload : T)
    (computed : computedStore inputs=some origin) (notSource : ∀ state,origin.read left≠some (.source state))
    (targetPresent : actualTarget b inputs native program credits commands fused=some payload) :
    ¬ CSTTT.Prospects.FallbackFissionFusionEmpty Nat
      (fun root target => actualAncestry b inputs native program credits commands root target=some true)
      source left right fused (fun target => actualTarget b inputs native program credits commands target=none) := by
  obtain ⟨world,run,read⟩ := (actual_target_some_iff b inputs native program credits commands fused payload).mp targetPresent
  have negative := (non_source_actual_ancestry_false b inputs native program credits commands origin left fused
    computed notSource).mpr (by rw [run]; rfl)
  rintro ⟨_,_,branches|empty⟩
  · have positive : actualAncestry b inputs native program credits commands left fused=some true := branches.1
    rw [negative] at positive
    cases positive
  · rw [targetPresent] at empty
    cases empty
-- Class (b): target-to-target accepted ledger descent has a distinct role from source-relative ancestry.
def AcceptedDescendant (receipts : List (ReceiptAncestry.Receipt S T)) (commands : List (GuardedFusion.Command T))
    (parent target : Nat) : Prop := Path (combinedLedger receipts commands) parent target
-- Class (b): every actual accepted fusion contributes both predecessor edges.
theorem executed_fusion_descendants (b : RawBridge H S T E R SC TC RR M) (program : Program T)
    (world finished : World S T) (commands : List (GuardedFusion.Command T)) (command : GuardedFusion.Command T)
    (receipts : List (ReceiptAncestry.Receipt S T))
    (executed : run b program world commands=some finished) (member : command∈commands) :
    AcceptedDescendant receipts commands command.left command.target ∧
    AcceptedDescendant receipts commands command.right command.target ∧
    ∃ before after,step b program before command=some after := by
  refine ⟨.one ?_,.one ?_,every_command_checked b program commands world finished executed command member⟩
  all_goals apply List.mem_append.mpr; right
  all_goals exact List.mem_flatMap.mpr ⟨command,member,by simp⟩
-- Class (b): source-relative ancestry propagates along actual accepted target descent.
theorem rooted_ancestry_propagates (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (program : Option (Program T))
    (credits : Option Credits) (commands : List (GuardedFusion.Command T)) (finished : World S T)
    (receipts : List (ReceiptAncestry.Receipt S T)) (source parent target : Nat)
    (recorded : actualRecordedFusion b inputs native program credits commands=some (finished,receipts))
    (ancestor : actualAncestry b inputs native program credits commands source parent=some true)
    (descendant : AcceptedDescendant receipts commands parent target) :
    actualAncestry b inputs native program credits commands source target=some true := by
  apply (actual_relation_exact b inputs native program credits commands finished receipts recorded source target).mpr
  exact closed_path (combinedLedger receipts commands) (Provenance b inputs (combinedLedger receipts commands))
    (provenance_least b inputs (combinedLedger receipts commands)).2.1 source parent target
    ((actual_relation_exact b inputs native program credits commands finished receipts recorded source parent).mp ancestor) descendant


-- Class (b): a typed replacement keeps source ancestry and target descent as separate relations.
def RootedFissionFusionEmpty (ancestry descendant : Nat → Nat → Prop)
    (source left right fused : Nat) (emptyTarget : Nat → Prop) : Prop :=
  ancestry source left ∧ ancestry source right ∧
    ((descendant left fused ∧ descendant right fused ∧ ancestry source fused) ∨ emptyTarget fused)
-- Class (b): exact actual typed return for every accepted merger, retaining its computed conflict guard.
theorem actual_rooted_fusion_return (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (native : List (NativeDescendant.Command T)) (rawProgram : Option (Program T))
    (rawCredits : Option Credits) (commands : List (GuardedFusion.Command T)) (finished : World S T)
    (receipts : List (ReceiptAncestry.Receipt S T)) (command : GuardedFusion.Command T) (source : Nat)
    (recorded : actualRecordedFusion b inputs native rawProgram rawCredits commands=some (finished,receipts))
    (member : command∈commands)
    (leftAncestor : actualAncestry b inputs native rawProgram rawCredits commands source command.left=some true)
    (rightAncestor : actualAncestry b inputs native rawProgram rawCredits commands source command.right=some true) :
    RootedFissionFusionEmpty
      (fun root target => actualAncestry b inputs native rawProgram rawCredits commands root target=some true)
      (AcceptedDescendant receipts commands) source command.left command.right command.target
      (fun target => actualTarget b inputs native rawProgram rawCredits commands target=none) ∧
    ∃ program before after leftPayload rightPayload,
      rawProgram=some program ∧ step b program before command=some after ∧
      before.store.read command.left=some (.target leftPayload) ∧
      before.store.read command.right=some (.target rightPayload) ∧
      guard b program before command leftPayload rightPayload=true := by
  obtain ⟨program,credits,origin,store,hp,hc,ho,hn,hf⟩ :=
    (recorded_fusion_exact b inputs native rawProgram rawCredits commands finished receipts).mp recorded
  obtain ⟨leftPath,rightPath,before,after,checked⟩ :=
    executed_fusion_descendants b program ⟨store,credits⟩ finished commands command receipts hf member
  obtain ⟨leftPayload,rightPayload,hl,hr,accepted,_⟩ := step_return b program before after command checked
  exact ⟨⟨leftAncestor,rightAncestor,Or.inl ⟨leftPath,rightPath,
    rooted_ancestry_propagates b inputs native rawProgram rawCredits commands finished receipts source command.left
      command.target recorded leftAncestor leftPath⟩⟩,
    program,before,after,leftPayload,rightPayload,hp,checked,hl,hr,accepted⟩

namespace Example
open CSTTT.POS04 CSTTT.Objecthood.T1Audit CSTTT.FallbackTheory.SourceCheckedTrace
-- Class (b): a raw instance already declared among the committed36 recipes; no derived verdict primitive.
def inputs : RawInputs KState KState :=
  ⟨0,some .p0w0,some id,3,destructiveWithTwin 0 1 2 6 2 .p1w0⟩
def program : Program KState :=
  ⟨fun left right => if left=.p0w0 ∧ right=.p0w0 then [(.p1w0,2),(.p1w1,2)] else [],4⟩
def command : GuardedFusion.Command KState := ⟨3,4,5,0,0,.p1w0⟩
-- Closed forms are derived snapshots, justified by the actual interpreter equations below.
def origin : Store KState KState := withRawTwin 0 1 2 6 2 id .p0w0 .p1w0
def splitStore : Store KState KState := NativeDescendant.split origin 2 3 4 .p0w0
def world : World KState KState := merged ⟨splitStore,[(100,3),(101,4)]⟩ command

theorem computed_origin : computedStore inputs=some origin := by
  exact actual_checked_program 0 1 2 6 2 3 id KState.p0w0 KState.p1w0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
theorem fission_step : NativeDescendant.step (pos04RawBridge .positive) origin (.fission 2 3 4)=some splitStore := by
  simp [NativeDescendant.step,origin,withRawTwin,activated,dormant,erased,captured,initial,put,switch,splitStore]
theorem fusion_step : GuardedFusion.step (pos04RawBridge .positive) program ⟨splitStore,[(100,3),(101,4)]⟩ command=some world := by
  change GuardedFusion.step (pos04RawBridge .positive) program ⟨splitStore,[(100,3),(101,4)]⟩ command=some (merged ⟨splitStore,[(100,3),(101,4)]⟩ command)
  have reads : splitStore.read 3=some (.target .p0w0) ∧ splitStore.read 4=some (.target .p0w0) := by
    simp [splitStore,NativeDescendant.split,put]
  have accepted : guard (pos04RawBridge .positive) program ⟨splitStore,[(100,3),(101,4)]⟩ command .p0w0 .p0w0=true := by
    decide +kernel
  dsimp only [command] at accepted
  simp [GuardedFusion.step,command,reads.1,reads.2,accepted]
theorem actual_execution : actualRun (pos04RawBridge .positive) inputs [.fission 2 3 4]
    (some program) (some [(100,3),(101,4)]) [command]=some world := by
  simp [actualRun,computed_origin,NativeDescendant.run,fission_step,GuardedFusion.run,fusion_step]
theorem target_present : actualTarget (pos04RawBridge .positive) inputs [.fission 2 3 4]
    (some program) (some [(100,3),(101,4)]) [command] 5=some .p1w0 := by
  apply (actual_target_some_iff _ _ _ _ _ _ _ _).mpr
  exact ⟨world,actual_execution,by simp [world,merged,command,put]⟩
theorem original_schema_counterexample :
    ¬ CSTTT.Prospects.FallbackFissionFusionEmpty Nat
      (fun source target => actualAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
        (some program) (some [(100,3),(101,4)]) [command] source target=some true)
      0 3 4 5 (fun target => actualTarget (pos04RawBridge .positive) inputs [.fission 2 3 4]
        (some program) (some [(100,3),(101,4)]) [command] target=none) := by
  apply original_fusion_schema_refuted (pos04RawBridge .positive) inputs [.fission 2 3 4]
    (some program) (some [(100,3),(101,4)]) [command] origin 0 3 4 5 .p1w0 computed_origin
  · intro payload
    simp [origin,withRawTwin,activated,dormant,erased,captured,initial,put]
  · exact target_present


-- Class (b): the committed released raw bridge laws construct the predictive Seed, without enumeration shortcuts.
theorem actual_seed : Seed (pos04RawBridge .positive) inputs 0 2 := by
  apply (root_seed_exact (pos04RawBridge .positive) inputs 2).mpr
  exact CSTTT.FallbackTheory.OperationalSeed.actual_seed_constructed (pos04RawBridge .positive)
    CSTTT.FallbackTheory.ReleasedPredictiveQuotient.released_map_laws 0 1 2 6 2 3 KState.p0w0 KState.p1w0
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
-- Class (b): actual computed receipts, not a supplied ledger, drive the scientific readout.
theorem actual_recorded : actualRecordedFusion (pos04RawBridge .positive) inputs [.fission 2 3 4]
    (some program) (some [(100,3),(101,4)]) [command]=
      some (world,[⟨origin,.fission 2 3 4,splitStore⟩]) := by
  simp [actualRecordedFusion,ReceiptAncestry.actualRecorded,computed_origin,ReceiptAncestry.recordedRun,
    fission_step,GuardedFusion.run,fusion_step]
-- Class (b): this concrete countermodel really has both ancestral branches and the fused ancestral output.
theorem actual_branch_and_fused_ancestry :
    actualAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
      (some program) (some [(100,3),(101,4)]) [command] 0 3=some true ∧
    actualAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
      (some program) (some [(100,3),(101,4)]) [command] 0 4=some true ∧
    actualAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
      (some program) (some [(100,3),(101,4)]) [command] 0 5=some true := by
  have positive (target : Nat) (path : Path
      (combinedLedger [⟨origin,NativeDescendant.Command.fission 2 3 4,splitStore⟩] [command]) 2 target) :
      actualAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
        (some program) (some [(100,3),(101,4)]) [command] 0 target=some true := by
    apply (actual_relation_exact _ _ _ _ _ _ _ _ actual_recorded 0 target).mpr
    exact ⟨2,actual_seed,Or.inr path⟩
  have leftEdge : (2,3)∈combinedLedger [⟨origin,NativeDescendant.Command.fission 2 3 4,splitStore⟩] [command] := by
    simp [combinedLedger,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges]
  have rightEdge : (2,4)∈combinedLedger [⟨origin,NativeDescendant.Command.fission 2 3 4,splitStore⟩] [command] := by
    simp [combinedLedger,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges]
  have fusionEdge : (3,5)∈combinedLedger [⟨origin,NativeDescendant.Command.fission 2 3 4,splitStore⟩] [command] := by
    simp [combinedLedger,ReceiptAncestry.ledgerEdges,ReceiptAncestry.receiptEdges,fusionLedger,command]
  exact ⟨positive 3 (.one leftEdge),positive 4 (.one rightEdge),positive 5 (.extend (.one leftEdge) fusionEdge)⟩
-- Class (b): the repaired typed source-relative statement succeeds on the same actual raw countermodel.
theorem actual_typed_successor : RootedFissionFusionEmpty
      (fun source target => actualAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
        (some program) (some [(100,3),(101,4)]) [command] source target=some true)
      (AcceptedDescendant [⟨origin,NativeDescendant.Command.fission 2 3 4,splitStore⟩] [command])
      0 3 4 5 (fun target => actualTarget (pos04RawBridge .positive) inputs [.fission 2 3 4]
        (some program) (some [(100,3),(101,4)]) [command] target=none) := by
  exact (actual_rooted_fusion_return _ _ _ _ _ _ _ _ command 0 actual_recorded (by simp)
    actual_branch_and_fused_ancestry.1 actual_branch_and_fused_ancestry.2.1).1
-- Class (b): both target-as-source queries directly return some false, despite genuine successful fusion ancestry.
theorem branch_roots_actual_false :
    actualAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
      (some program) (some [(100,3),(101,4)]) [command] 3 5=some false ∧
    actualAncestry (pos04RawBridge .positive) inputs [.fission 2 3 4]
      (some program) (some [(100,3),(101,4)]) [command] 4 5=some false := by
  constructor
  · apply (non_source_actual_ancestry_false _ _ _ _ _ _ origin 3 5 computed_origin ?_).mpr
      (by rw [actual_execution]; rfl)
    intro payload
    simp [origin,withRawTwin,activated,dormant,erased,captured,initial,put]
  · apply (non_source_actual_ancestry_false _ _ _ _ _ _ origin 4 5 computed_origin ?_).mpr
      (by rw [actual_execution]; rfl)
    intro payload
    simp [origin,withRawTwin,activated,dormant,erased,captured,initial,put]
end Example
end CSTTT.FallbackTheory.FusionRolesPrototype

namespace CSTTT.FallbackTheory.ReconstructionRolesPrototype
open CSTTT.TransportTheory CSTTT.FallbackTheory.RawPredictiveQuotient
open CSTTT.FallbackTheory.OperationalTrace CSTTT.FallbackTheory.SharedOperationalSeed
open CSTTT.FallbackTheory.FusionRolesPrototype
variable {H S T E R SC TC RR M : Type} [DecidableEq S] [DecidableEq T]
set_option autoImplicit false
-- Structural equality reads TWO actual typed targets in the same execution; neither target is a historical-source slot.
def SameActualTargets (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (program : Option (GuardedFusion.Program T)) (credits : Option GuardedFusion.Credits) (left right : Nat) : Prop :=
  ∃ payload, actualTarget b inputs [] program credits [] left=some payload ∧
    actualTarget b inputs [] program credits [] right=some payload
-- Explicit rooted repair: historical source ancestry and target-to-target structural comparison have different types/roles.
def RootedTwinSeparation (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (program : Option (GuardedFusion.Program T)) (credits : Option GuardedFusion.Credits) (source reconstruction twin : Nat) : Prop :=
  SameActualTargets b inputs program credits reconstruction twin ∧
    GuardedFusion.actualAncestry b inputs [] program credits [] source reconstruction=some true ∧
    GuardedFusion.actualAncestry b inputs [] program credits [] source twin=some false
-- Direct original-schema refutation on every partial prefix: its target-as-source ancestry query cannot succeed when both compared slots are typed targets.
theorem original_schema_refuted (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (program : Option (GuardedFusion.Program T)) (credits : Option GuardedFusion.Credits)
    (sourceDerived : Nat → Nat → Prop) :
    ¬CSTTT.Prospects.DestructiveReconstructionTwinSeparation Nat
      (SameActualTargets b inputs program credits) sourceDerived
      (fun root target => GuardedFusion.actualAncestry b inputs [] program credits [] root target=some true) := by
  rintro ⟨reconstruction,twin,⟨payload,readLeft,readRight⟩,_,ancestral,_⟩
  cases hp : program with
  | none => simp [actualTarget,GuardedFusion.actualRun,hp] at readLeft
  | some p =>
    cases hc : credits with
    | none => simp [actualTarget,GuardedFusion.actualRun,hc] at readLeft
    | some c =>
      cases ho : computedStore inputs with
      | none => simp [actualTarget,GuardedFusion.actualRun,ho] at readLeft
      | some origin =>
        have run : GuardedFusion.actualRun b inputs [] (some p) (some c) []=some ⟨origin,c⟩ := by
          simp [GuardedFusion.actualRun,ho,NativeDescendant.run,GuardedFusion.run]
        have targetRead : origin.read reconstruction=some (.target payload) := by
          simp [actualTarget,hp,hc,GuardedFusion.actualRun,ho,NativeDescendant.run,GuardedFusion.run] at readLeft
          cases content : origin.read reconstruction with
          | none => simp [content] at readLeft
          | some value => cases value <;> simp_all
        have negative := (non_source_actual_ancestry_false b inputs [] (some p) (some c) [] origin reconstruction twin ho
          (fun state => by rw [targetRead]; intro eq; cases eq)).mpr (by rw [run]; rfl)
        rw [hp,hc,negative] at ancestral
        cases ancestral
-- Primitive raw source/copy instruction; no computed Store or lineage bit is a field.
def rawInputs (b : RawBridge H S T E R SC TC RR M) (source record target twin duration maxAge : Nat) (payload : S) : RawInputs S T :=
  ⟨source,some payload,some b.mapState,maxAge,destructiveWithTwin source record target twin duration (b.mapState payload)⟩
omit [DecidableEq T] in
theorem computed_origin (b : RawBridge H S T E R SC TC RR M)
    (source record target twin duration maxAge : Nat) (payload : S)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1≤maxAge) :
    computedStore (rawInputs b source record target twin duration maxAge payload)=
      some (withRawTwin source record target twin duration b.mapState payload (b.mapState payload)) :=
  CSTTT.FallbackTheory.SourceCheckedTrace.actual_checked_program source record target twin duration maxAge b.mapState payload (b.mapState payload) sr st sw rt rw tw age
-- The repaired return is constructed from actual source-checked execution and imported RAW MapLaws, not assuming any final Seed.
theorem repaired_constructive_return (b : RawBridge H S T E R SC TC RR M) (laws : MapLaws b)
    (program : GuardedFusion.Program T) (credits : GuardedFusion.Credits)
    (source record target twin duration maxAge : Nat) (payload : S)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1≤maxAge) :
    RootedTwinSeparation b (rawInputs b source record target twin duration maxAge payload) (some program) (some credits) source target twin ∧
    ∃ world, GuardedFusion.actualRun b (rawInputs b source record target twin duration maxAge payload) [] (some program) (some credits) []=some world ∧
      world.store.active source=false ∧ world.store.read source=some (.source payload) ∧
      world.store.read record=some (.record source 1 payload) ∧
      world.store.read target=world.store.read twin ∧ world.store.active target=true ∧ world.store.active twin=true ∧
      (∀ query, targetFuture b (b.mapState payload) query=sourceFuture b payload query) := by
  let inputs := rawInputs b source record target twin duration maxAge payload
  let origin := withRawTwin source record target twin duration b.mapState payload (b.mapState payload)
  have computed : computedStore inputs=some origin := computed_origin b source record target twin duration maxAge payload sr st sw rt rw tw age
  have run : GuardedFusion.actualRun b inputs [] (some program) (some credits) []=some ⟨origin,credits⟩ := by
    simp [GuardedFusion.actualRun,computed,NativeDescendant.run,GuardedFusion.run]
  have recorded : GuardedFusion.actualRecordedFusion b inputs [] (some program) (some credits) []=some (⟨origin,credits⟩,[]) := by
    simp [GuardedFusion.actualRecordedFusion,ReceiptAncestry.actualRecorded,computed,ReceiptAncestry.recordedRun,GuardedFusion.run]
  have seed : Seed b inputs source target := by
    apply (root_seed_exact b inputs target).mpr
    exact CSTTT.FallbackTheory.OperationalSeed.actual_seed_constructed b laws source record target twin duration maxAge payload (b.mapState payload) sr st sw rt rw tw age
  have positive : GuardedFusion.actualAncestry b inputs [] (some program) (some credits) [] source target=some true := by
    apply (GuardedFusion.actual_relation_exact b inputs [] (some program) (some credits) [] _ [] recorded source target).mpr
    exact ⟨target,seed,Or.inl rfl⟩
  have targetRead : origin.read target=some (.target (b.mapState payload)) := by simp [origin,withRawTwin,activated,put,tw]
  have twinRead : origin.read twin=some (.target (b.mapState payload)) := by simp [origin,withRawTwin,put]
  have negative : GuardedFusion.actualAncestry b inputs [] (some program) (some credits) [] source twin=some false :=
    GuardedFusion.actual_twin_ancestry_false b inputs [] (some program) (some credits) [] _ origin twin source (b.mapState payload)
      computed twinRead (by intro parent; simp [origin,withRawTwin,activated,Ne.symm rw,Ne.symm tw]) run
  have same : SameActualTargets b inputs (some program) (some credits) target twin := by
    refine ⟨b.mapState payload,?_,?_⟩
    · exact (actual_target_some_iff _ _ _ _ _ _ _ _).mpr ⟨⟨origin,credits⟩,run,targetRead⟩
    · exact (actual_target_some_iff _ _ _ _ _ _ _ _).mpr ⟨⟨origin,credits⟩,run,twinRead⟩
  have erased := OperationalPredictiveReturn.actual_source_erased b source record target twin duration maxAge payload (b.mapState payload)
    sr st sw rt rw tw age origin computed
  have separated := OperationalPredictiveReturn.actual_equal_twin_separation b source record target twin duration maxAge payload (b.mapState payload) rfl
    sr st sw rt rw tw age origin computed
  exact ⟨⟨same,positive,negative⟩,⟨origin,credits⟩,run,erased.1,erased.2.1,erased.2.2,separated.1,separated.2.1,separated.2.2.1,
    actual_future_transport b laws payload⟩

-- The independent initialized twin remains a directly false scientific readout after EVERY successful finite native/fusion suffix, including missing optional program/credits.
theorem twin_false_iff_available_after_suffix (b : RawBridge H S T E R SC TC RR M)
    (native : List (NativeDescendant.Command T)) (program : Option (GuardedFusion.Program T))
    (credits : Option GuardedFusion.Credits) (commands : List (GuardedFusion.Command T))
    (source record target twin duration maxAge querySource : Nat) (payload : S)
    (sr : source≠record) (st : source≠target) (sw : source≠twin)
    (rt : record≠target) (rw : record≠twin) (tw : target≠twin) (age : 2+duration-1≤maxAge) :
    GuardedFusion.actualAncestry b (rawInputs b source record target twin duration maxAge payload) native program credits commands querySource twin=some false ↔
      (GuardedFusion.actualRun b (rawInputs b source record target twin duration maxAge payload) native program credits commands).isSome=true := by
  constructor
  · intro negative
    exact ((GuardedFusion.actual_ancestry_false_iff _ _ _ _ _ _ _ _).mp negative).1
  · intro available
    cases run : GuardedFusion.actualRun b (rawInputs b source record target twin duration maxAge payload) native program credits commands with
    | none => simp [run] at available
    | some world =>
      let origin := withRawTwin source record target twin duration b.mapState payload (b.mapState payload)
      have computed := computed_origin b source record target twin duration maxAge payload sr st sw rt rw tw age
      exact GuardedFusion.actual_twin_ancestry_false b _ native program credits commands world origin twin querySource (b.mapState payload)
        computed (by simp [origin,withRawTwin,put])
        (by intro parent; simp [origin,withRawTwin,activated,Ne.symm rw,Ne.symm tw]) run
-- The source-checked interpreter actually passes through a dormant state BEFORE activating either target; copied record evidence remains populated.
omit [DecidableEq T] in
theorem actual_checked_dormant_prefix (b : RawBridge H S T E R SC TC RR M)
    (source record duration maxAge : Nat) (payload : S) (distinct : source≠record) :
    CSTTT.FallbackTheory.SourceCheckedTrace.checkedExecute (some b.mapState) maxAge source (some payload)
      [.snapshot source record,.erase source,.gap duration]=some (dormant source record duration payload) := by
  simp [CSTTT.FallbackTheory.SourceCheckedTrace.checkedExecute,CSTTT.FallbackTheory.SourceCheckedTrace.checkedRun,
    CSTTT.FallbackTheory.SourceCheckedTrace.checkedStep,step,initial,captured,erased,dormant,put,switch,distinct,Ne.symm distinct]
end CSTTT.FallbackTheory.ReconstructionRolesPrototype
