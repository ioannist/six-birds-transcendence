import CSTTT.Autonomy.FiniteProgress
import CSTTT.Autonomy.NativePolicyBridge
import CSTTT.Targets.GenericHandoff.ResourceCellReindex
import CSTTT.Targets.GenericHandoff.InitialProgramComposition
import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationResources

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): the exact shared primitive projection declared before instantiation.
def project (k : Owner) (p : NativePackageBundle.Value k) : MemoryValue k := (p.1.native,p.2.native)
-- Class (b): actual native runtime on the full shared primitive bundle.
def native (cell : Owner) := ResourceCellReindex.raw id project (PublicationResources.runtime cell)
-- Class (b): actual copied-source initialization; the empty register type excludes a supplied run.
def sourceInitializer (cell : Owner) : InitialProgram Owner NativePackageBundle.Value Unit (fun _ => ModeExecution.State) History :=
  CellReindex.initializer id project (ModeExecution.initializer cell (swapOwner cell) (PublicationReplay.start cell))
-- Class (b): same actual source/target mode execution program.
def historyProgram (cell : Owner) : Program Owner NativePackageBundle.Value Unit (fun _ => ModeExecution.State) (Unit × Bool × Factor) :=
  CellReindex.program id project (PublicationReplay.raw cell).execution.program
-- Class (b): actual receiver initialization instruction preserves the current incoming run.
def receiveProgram (cell : Owner) : Program Owner NativePackageBundle.Value Unit (fun _ => ModeExecution.State) (History × Route) :=
  CellReindex.program id project (PublicationReplay.raw cell).receive
-- Class (b): composed raw source history, actual receive and one actual exit.
def entryInitializer (cell : Owner) : InitialProgram Owner NativePackageBundle.Value Unit (fun _ => ModeExecution.State) History :=
  let history := InitialProgramComposition.iterate (sourceInitializer cell) (historyProgram cell)
    (fun h => ((),false,h)) (PublicationReplay.copies cell-1)
  let arrived := InitialProgramComposition.after history (receiveProgram cell) (fun h => (h,h))
  InitialProgramComposition.after arrived (historyProgram cell) (fun h => ((),false,h))
-- Class (b): the primitive pullback is literally the released native-input projection for every partial assignment.
theorem actual_pullback (a : Assignment Owner NativePackageBundle.Value) :
    CellReindex.pullback id project a=NativePackageBundle.nativeInputs a := rfl
-- Class (b): exact native runtime readiness for every partial shared-bundle assignment.
theorem native_ready_iff (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    ResourceRuntime.Ready (native cell) a ↔ (a cell).isSome=true := by
  rw [native,ResourceCellReindex.ready_iff,actual_pullback,PublicationResources.ready_iff]
  simp [NativePackageBundle.nativeInputs]
-- Class (b): every syntactically consumed initializer cell is precisely the selected owner.
theorem initializer_dependencies (cell k : Owner) :
    k∈(entryInitializer cell ()).dependencies ↔ k=cell := by
  cases cell <;>
    simp [entryInitializer,sourceInitializer,historyProgram,receiveProgram,InitialProgramComposition.iterate,
      InitialProgramComposition.after,RegisterSubstitution.substitute,CellReindex.initializer,CellReindex.program,
      CellReindex.expression,PublicationReplay.copies,PublicationReplay.start,PublicationReplay.raw,
      ModeExecution.acquisition,ModeExecution.initializer,ModeExecution.execution,ModeExecution.updateExpr,
      ModeExecution.context,ModeExecution.activeData,ModeExecution.targetData,ModeExecution.sourceData,
      ModeExecution.receiveExpr,Expr.dependencies,Expr.reenv]
-- Class (b): exact all-partial raw initialization readiness, independent of supported-entry validity.
theorem initializer_ready_iff (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    RegisterInitialization.Ready (entryInitializer cell) a ↔ (a cell).isSome=true := by
  constructor
  · intro ready; exact ready () cell ((initializer_dependencies cell cell).mpr rfl)
  · intro present r k member
    cases r
    have same := (initializer_dependencies cell k).mp member
    subst k; exact present
-- Class (b): the canonical initialized entry is DERIVED from the actual composed raw programs.
theorem canonical_initializer (cell : Owner) (h : Factor) :
    evaluate (entryInitializer cell) NativePackageBundle.canonical h ()=
      some (PublicationResources.run cell h (PublicationReplay.start cell+PublicationReplay.copies cell) ()) := by
  cases cell
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
-- Class (b): missing selected raw bundle directly rejects actual initialization.
theorem missing_initializer (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (missing : a cell=none) (h : Factor) : evaluate (entryInitializer cell) a h ()=none :=
  missing_evaluation _ a () cell ((initializer_dependencies cell cell).mpr rfl) missing h
-- Class (b): a local primitive test assignment contains only the selected raw bundle.
def selectedAssignment (cell : Owner) (p : NativePackageBundle.Value cell) : Assignment Owner NativePackageBundle.Value :=
  fun k => if k=cell then some p else none
-- Class (b): the selected raw bundle makes the exact initializer ready.
theorem selected_initializer_ready (cell : Owner) (p : NativePackageBundle.Value cell) :
    RegisterInitialization.Ready (entryInitializer cell) (selectedAssignment cell p) :=
  (initializer_ready_iff _ _).mpr (by simp [selectedAssignment])
-- Class (b): the selected raw bundle makes the same actual native runtime ready.
theorem selected_native_ready (cell : Owner) (p : NativePackageBundle.Value cell) :
    ResourceRuntime.Ready (native cell) (selectedAssignment cell p) :=
  (native_ready_iff _ _).mpr (by simp [selectedAssignment])
-- Class (b): proof of actual optional presence; this supplies no computational observation value.
theorem expression_present {Cell R Env X : Type} {Value : Cell → Type} {RV : R → Type}
    (e : Expr Cell Value R RV Env X) (a : Assignment Cell Value)
    (ready : Complete e.dependencies a) (run : Registers R RV) (env : Env) :
    (e.eval a run env).isSome=true := by
  obtain ⟨value,eq⟩ := e.present_of_complete a ready run env
  rw [eq]; rfl
-- Class (b): computational extraction of the ACTUAL optional expression, with no default or choice value.
def exactRead {Cell R Env X : Type} {Value : Cell → Type} {RV : R → Type}
    (e : Expr Cell Value R RV Env X) (a : Assignment Cell Value)
    (ready : Complete e.dependencies a) (run : Registers R RV) (env : Env) : X :=
  (e.eval a run env).get (expression_present e a ready run env)
-- Class (b): exact return of the raw optional expression that extraction consumes.
theorem exact_read_eq {Cell R Env X : Type} {Value : Cell → Type} {RV : R → Type}
    (e : Expr Cell Value R RV Env X) (a : Assignment Cell Value)
    (ready : Complete e.dependencies a) (run : Registers R RV) (env : Env) :
    e.eval a run env=some (exactRead e a ready run env) := (Option.some_get _).symm
-- Class (b): selected raw initialization, read computationally from the same expression.
def selectedInitial (cell : Owner) (p : NativePackageBundle.Value cell) (h : Factor) : ModeExecution.State :=
  exactRead (entryInitializer cell ()) (selectedAssignment cell p) (selected_initializer_ready cell p ()) noRegisters h
-- Class (b): declared zero-counter/tick test preserves all other ACTUAL initialized coordinates.
def responseTest (cell : Owner) (p : NativePackageBundle.Value cell) (h : Factor) : ModeExecution.Registers :=
  let initial := selectedInitial cell p h
  ModeExecution.pack ({initial.1 with counter := 0, ticks := 0},initial.2)
-- Class (b): exact selected readiness of native progress, part of the same complete runtime.
theorem progress_ready (cell : Owner) (p : NativePackageBundle.Value cell) :
    Complete (native cell).progress.dependencies (selectedAssignment cell p) := by
  intro k hk
  exact (selected_native_ready cell p).2.2 k (by simp [ResourceRuntime.Raw.readDependencies,hk])
-- Class (b): exact selected readiness of native record; no writer success is assumed.
theorem record_ready (cell : Owner) (p : NativePackageBundle.Value cell) :
    Complete (native cell).record.dependencies (selectedAssignment cell p) := by
  intro k hk
  exact (selected_native_ready cell p).2.2 k (by simp [ResourceRuntime.Raw.readDependencies,hk])
-- Class (b): exact selected readiness of actual charge data.
theorem charge_ready (cell : Owner) (p : NativePackageBundle.Value cell) :
    Complete (native cell).charge.dependencies (selectedAssignment cell p) := by
  intro k hk
  exact (selected_native_ready cell p).2.2 k (by simp [ResourceRuntime.Raw.readDependencies,hk])
-- Class (b): response data derive from actual initialized test, row, charge, updater and both native readouts.
def selectedResponse (cell : Owner) (p : NativePackageBundle.Value cell) (act : Bool)
    (h : Factor) (_ : Unit) : RawRechargingPolicy.Response Factor Bool Factor :=
  let a := selectedAssignment cell p
  let ready := selected_native_ready cell p
  let test := responseTest cell p h
  let charge := exactRead (native cell).charge a (charge_ready cell p) test ((),act)
  let beforeProgress := exactRead (native cell).progress a (progress_ready cell p) test ()
  let beforeRecord := exactRead (native cell).record a (record_ready cell p) test ()
  ⟨act,charge.owner,exactRead (native cell).execution.row a ready.1 test ((),act),fun o =>
    let nextState := exactRead ((native cell).execution.program ()) a (ready.2.1 ()) test ((),act,o)
    let next := ModeExecution.pack nextState
    ⟨nextState.1.factor,
      exactRead (native cell).progress a (progress_ready cell p) next ()-beforeProgress,
      exactRead (native cell).record a (record_ready cell p) next ()-beforeRecord,
      (charge.debit true : Rat),(charge.credit true : Rat)⟩⟩
-- Class (b): actual raw table expression consumes the selected bundle before deriving any response.
def responseView (cell : Owner) (act : Bool) : StaticView Owner NativePackageBundle.Value
    (Factor → Unit → RawRechargingPolicy.Response Factor Bool Factor) :=
  ⟨.map (fun p => selectedResponse cell p act) (.cell cell)⟩
-- Class (b): every partial assignment gives exactly the response derived from its selected primitive bundle.
theorem response_view_eq (cell : Owner) (act : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    (responseView cell act).read a=(a cell).map (fun p => selectedResponse cell p act) := rfl
-- Class (b): every actually consumed key agrees with the local raw test assignment; no other owner is supplied.
theorem selected_agrees (cell : Owner) (p : NativePackageBundle.Value cell)
    (a : Assignment Owner NativePackageBundle.Value) (assigned : a cell=some p)
    (keys : List Owner) (complete : Complete keys (selectedAssignment cell p)) :
    Agrees keys a (selectedAssignment cell p) := by
  intro k member
  have present := complete k member
  by_cases same : k=cell
  · subst k; simpa [selectedAssignment] using assigned
  · simp [selectedAssignment,same] at present
-- Class (b): the local computational initializer equals the same actual optional expression on EVERY partial assignment with its selected bundle.
theorem selected_initializer_eq (cell : Owner) (p : NativePackageBundle.Value cell)
    (a : Assignment Owner NativePackageBundle.Value) (assigned : a cell=some p) (h : Factor) :
    evaluate (entryInitializer cell) a h ()=some (selectedInitial cell p h) := by
  exact ((entryInitializer cell ()).locality
    (selected_agrees cell p a assigned _ (selected_initializer_ready cell p ())) noRegisters h).trans
      (exact_read_eq _ _ _ _ _)
-- Class (b): the derived response row is exactly the ACTUAL row on the same initialized test and partial primitive assignment.
theorem response_row_eq (cell : Owner) (p : NativePackageBundle.Value cell) (act : Bool)
    (a : Assignment Owner NativePackageBundle.Value) (assigned : a cell=some p) (h : Factor) :
    (native cell).execution.row.eval a (responseTest cell p h) ((),act)=some (selectedResponse cell p act h ()).rows := by
  exact ((native cell).execution.row.locality
    (selected_agrees cell p a assigned _ (selected_native_ready cell p).1) (responseTest cell p h) ((),act)).trans
      (exact_read_eq (native cell).execution.row (selectedAssignment cell p) (selected_native_ready cell p).1
        (responseTest cell p h) ((),act))
-- Class (b): exact optional native charge from the same raw test and partial assignment.
theorem response_charge_eq (cell : Owner) (p : NativePackageBundle.Value cell) (act : Bool)
    (a : Assignment Owner NativePackageBundle.Value) (assigned : a cell=some p) (h : Factor) :
    (native cell).charge.eval a (responseTest cell p h) ((),act)=some
      (exactRead (native cell).charge (selectedAssignment cell p) (charge_ready cell p) (responseTest cell p h) ((),act)) := by
  exact ((native cell).charge.locality
    (selected_agrees cell p a assigned _ (charge_ready cell p)) _ _).trans (exact_read_eq _ _ _ _ _)
-- Class (b): every actual native next register is the computationally read raw program result, without a substituted updater verdict.
theorem response_update_eq (cell : Owner) (p : NativePackageBundle.Value cell) (act : Bool)
    (a : Assignment Owner NativePackageBundle.Value) (assigned : a cell=some p)
    (ready : ResourceRuntime.Ready (native cell) a) (h o : Factor) :
    ResourceRuntime.update (native cell) a ready (responseTest cell p h) () act o=
      ModeExecution.pack (exactRead ((native cell).execution.program ()) (selectedAssignment cell p)
        ((selected_native_ready cell p).2.1 ()) (responseTest cell p h) ((),act,o)) := by
  funext r; cases r
  have actual := checked_execute_eq (native cell).execution.program a ready.2.1 (responseTest cell p h) ((),act,o) ()
  have observed := (((native cell).execution.program ()).locality
    (selected_agrees cell p a assigned _ ((selected_native_ready cell p).2.1 ()))
      (responseTest cell p h) ((),act,o)).trans
        (exact_read_eq ((native cell).execution.program ()) (selectedAssignment cell p)
          ((selected_native_ready cell p).2.1 ()) (responseTest cell p h) ((),act,o))
  exact (Option.some.inj (actual.symm.trans observed))
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): substitute the actual composed raw initializer into the actual native observation.
def initializedView {X : Type} (cell : Owner) (h : Factor)
    (e : Expr Owner NativePackageBundle.Value Unit (fun _ => ModeExecution.State) Unit X) :
    StaticView Owner NativePackageBundle.Value X :=
  ⟨(RegisterSubstitution.substitute (entryInitializer cell) (e.reenv (fun _ : History => ()))).reenv (fun _ => h)⟩
-- Class (b): exact all-partial ready transfer for an actually consumed native observation.
theorem initialized_view_ready {X : Type} (cell : Owner) (h : Factor)
    (e : Expr Owner NativePackageBundle.Value Unit (fun _ => ModeExecution.State) Unit X)
    (a : Assignment Owner NativePackageBundle.Value)
    (hp : RegisterInitialization.Ready (entryInitializer cell) a) (he : Complete e.dependencies a) :
    Complete (initializedView cell h e).dependencies a := by
  change Complete ((RegisterSubstitution.substitute _ _).reenv _).dependencies a
  rw [Expr.reenv_dependencies]
  apply (RegisterSubstitution.complete_iff _ _ a).mpr
  exact ⟨by simpa only [Expr.reenv_dependencies] using he,fun r _ => hp r⟩
-- Class (b): actual full dispatcher, unchanged primitive package cells, actual computed response and four initialized observations.
def model (cell : Owner) (hist : Factor) (act : Bool) :
    RawRechargingPolicy.Raw Owner NativePackageBundle.Value Factor Unit Bool Factor where
  states := ⟨factors,factor_mem⟩
  disturbances := ⟨[()],fun d => by cases d; simp⟩
  outcomes := ⟨factors,factor_mem⟩
  target := (PublicationResources.cfg cell).target
  clauses := NativeClosedPackage.package cell false
  cells := fun k => .cell k
  response := responseView cell act
  initialFactor := ⟨.map (fun x => x.1.factor) ((entryInitializer cell ()).reenv (fun _ => hist))⟩
  initialProgress := initializedView cell hist (native cell).progress
  initialRecord := initializedView cell hist (native cell).record
  initialBalance := initializedView cell hist (.map (fun accounts => ((accounts true).balance : Rat)) (native cell).accounts)
-- Class (b): same-assignment native progress readiness, no accepted-policy premise.
theorem assigned_progress_ready (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (native cell) a) : Complete (native cell).progress.dependencies a := by
  intro k hk; exact ready.2.2 k (by simp [ResourceRuntime.Raw.readDependencies,hk])
-- Class (b): same-assignment native record readiness, no writer premise.
theorem assigned_record_ready (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (native cell) a) : Complete (native cell).record.dependencies a := by
  intro k hk; exact ready.2.2 k (by simp [ResourceRuntime.Raw.readDependencies,hk])
-- Class (b): same-assignment native accounts readiness, no solvency premise.
theorem assigned_accounts_ready (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ready : ResourceRuntime.Ready (native cell) a) : Complete (native cell).accounts.dependencies a := by
  intro k hk; exact ready.2.2 k (by simp [ResourceRuntime.Raw.readDependencies,hk])
-- Class (b): exact readiness of the entire constructed model for EVERY partial primitive assignment.
theorem model_ready_iff (cell : Owner) (hist : Factor) (act : Bool) (a : Assignment Owner NativePackageBundle.Value) :
    RawRechargingPolicy.Ready (model cell hist act) a ↔ (a cell).isSome=true := by
  constructor
  · intro ready
    exact ready.1 cell (by simp [model,responseView,StaticView.dependencies,Expr.dependencies])
  · intro present
    have hp := (initializer_ready_iff cell a).mpr present
    have hn := (native_ready_iff cell a).mpr present
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro k hk
      have same : k=cell := by simpa [model,responseView,StaticView.dependencies,Expr.dependencies] using hk
      subst k; exact present
    · simpa [model,StaticView.dependencies,Expr.dependencies,Expr.reenv_dependencies] using hp ()
    · exact initialized_view_ready cell hist _ a hp (assigned_progress_ready cell a hn)
    · exact initialized_view_ready cell hist _ a hp (assigned_record_ready cell a hn)
    · exact initialized_view_ready cell hist _ a hp (assigned_accounts_ready cell a hn)
-- Class (b): constructed package assignment is literally the original partial primitive assignment, for every factor.
theorem model_factor_assignment (cell : Owner) (hist x : Factor) (act : Bool)
    (a : Assignment Owner NativePackageBundle.Value) :
    RawRechargingPolicy.factorAssignment (model cell hist act) a x=a := rfl
-- Class (b): entire eight-clause model acceptance equals the actual original native closed package, without a success premise.
theorem model_package_iff (cell : Owner) (hist x : Factor) (act : Bool)
    (a : Assignment Owner NativePackageBundle.Value) :
    RawRechargingPolicy.PackageAt (model cell hist act) a x ↔ (NativeClosedPackage.package cell false).accept a := Iff.rfl
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): every assigned raw bundle gives exactly the initialized native observation, on the same partial assignment.
theorem initialized_view_eq {X : Type} (cell : Owner) (h : Factor)
    (e : Expr Owner NativePackageBundle.Value Unit (fun _ => ModeExecution.State) Unit X)
    (a : Assignment Owner NativePackageBundle.Value) (p : NativePackageBundle.Value cell)
    (assigned : a cell=some p) :
    (initializedView cell h e).read a=e.eval a (ModeExecution.pack (selectedInitial cell p h)) () := by
  unfold initializedView StaticView.read
  rw [Expr.reenv_eval,RegisterSubstitution.evaluation]
  have initialized : RegisterSubstitution.evaluateTranslation (entryInitializer cell) a noRegisters h=
      fun r => some (ModeExecution.pack (selectedInitial cell p h) r) := by
    funext r; cases r
    exact selected_initializer_eq cell p a assigned h
  rw [initialized,RegisterSubstitution.total_registers,Expr.reenv_eval]
-- Class (b): extract only the already released canonical raw bundle; no new primitive or initialized snapshot.
def canonicalValue (cell : Owner) : NativePackageBundle.Value cell :=
  (NativePackageBundle.canonical cell).get (by cases cell <;> rfl)
-- Class (b): exact original canonical assignment receipt.
theorem canonical_assigned (cell : Owner) : NativePackageBundle.canonical cell=some (canonicalValue cell) :=
  (Option.some_get _).symm
-- Class (b): computational local initializer returns the actual canonical composed entry.
theorem selected_canonical_initial (cell : Owner) (h : Factor) :
    selectedInitial cell (canonicalValue cell) h=
      PublicationResources.run cell h (PublicationReplay.start cell+PublicationReplay.copies cell) () := by
  exact Option.some.inj ((selected_initializer_eq cell (canonicalValue cell)
    NativePackageBundle.canonical (canonical_assigned cell) h).symm.trans (canonical_initializer cell h))
-- Class (b): the declared reset response test is exactly an actual released generated native state at time zero.
theorem canonical_response_test (cell : Owner) (h : Factor) :
    responseTest cell (canonicalValue cell) h=PublicationResources.run cell h 0 := by
  rw [responseTest,selected_canonical_initial]
  cases cell <;> rfl
-- Class (b): original shared-bundle canonical projection is literally the released native assignment.
theorem canonical_pullback : CellReindex.pullback id project NativePackageBundle.canonical=PublicationResources.assignment := rfl
-- Class (b): native progress readout on every generated time, with no bounded-time hypothesis.
theorem canonical_progress (cell : Owner) (h : Factor) (time : Nat) :
    (native cell).progress.eval NativePackageBundle.canonical (PublicationResources.run cell h time) ()=some time := rfl
-- Class (b): actual strict record readout on every generated time, inherited writer semantics.
theorem canonical_record (cell : Owner) (h : Factor) (time : Nat) :
    (native cell).record.eval NativePackageBundle.canonical (PublicationResources.run cell h time) ()=some time := by
  change (CellReindex.expression id project _).eval _ _ _=some time
  rw [CellReindex.evaluation,canonical_pullback]
  exact PublicationResources.target_record_eval cell h time
-- Class (b): actual funded unit account readout on every generated time.
theorem canonical_accounts (cell : Owner) (h : Factor) (time : Nat) :
    (native cell).accounts.eval NativePackageBundle.canonical (PublicationResources.run cell h time) ()=
      some (PublicationResources.accounts cell) := by
  change (CellReindex.expression id project _).eval _ _ _=some _
  rw [CellReindex.evaluation,canonical_pullback]
  exact PublicationResources.target_accounts cell h time
-- Class (b): native optional decoding is the actual generated factor/time/unit account, for all natural times.
theorem canonical_decode (cell : Owner) (h : Factor) (time : Nat) :
    NativePolicyBridge.decodeNative (native cell) true NativePackageBundle.canonical (PublicationResources.run cell h time)=
      some (RawRechargingPolicy.EventState.mk h time time 1) := by
  apply (NativePolicyBridge.decode_native_some_iff _ _ _ _ _).mpr
  exact ⟨rfl,canonical_progress cell h time,canonical_record cell h time,
    PublicationResources.accounts cell,canonical_accounts cell h time,rfl⟩
-- Class (b): response equality preserves every computed field including all outcome branches.
theorem response_ext {X A O : Type} (r s : RawRechargingPolicy.Response X A O)
    (ha : r.action=s.action) (ho : r.owner=s.owner) (hr : r.rows=s.rows) (hb : r.branch=s.branch) : r=s := by
  cases r; cases s; simp_all
-- Class (b): exact canonical response computes from the same selected raw initializer/runtime, for every factor and outcome.
theorem canonical_response (cell : Owner) (h : Factor) :
    selectedResponse cell (canonicalValue cell) false h ()=
      ⟨false,(PublicationResources.cfg cell).target,[(h,1)],fun o => ⟨o,1,1,1,1⟩⟩ := by
  cases cell
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j
  all_goals apply response_ext
  all_goals first | rfl | (decide +kernel) | (funext o; rcases o with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl)
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): canonical readiness follows from actual selected-bundle presence.
theorem canonical_model_ready (cell : Owner) (hist : Factor) :
    RawRechargingPolicy.Ready (model cell hist false) NativePackageBundle.canonical :=
  (model_ready_iff _ _ _ _).mpr (by rw [canonical_assigned]; rfl)
-- Class (b): complete derived table equals the actual canonical response, independent of readiness proof choice.
theorem canonical_table (cell : Owner) (hist x : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) NativePackageBundle.canonical) (d : Unit) :
    RawRechargingPolicy.table (model cell hist false) NativePackageBundle.canonical ready x d=
      ⟨false,(PublicationResources.cfg cell).target,[(x,1)],fun o => ⟨o,1,1,1,1⟩⟩ := by
  have actual := RawRechargingPolicy.table_eq (model cell hist false) NativePackageBundle.canonical ready
  change (responseView cell false).read NativePackageBundle.canonical=some _ at actual
  rw [response_view_eq,canonical_assigned,Option.map_some] at actual
  rw [← Option.some.inj actual]
  cases d
  exact canonical_response cell x
-- Class (b): the four initialized raw observations actually decode to the derived native entry, not a supplied EventState.
theorem canonical_decode_initial (cell : Owner) (hist : Factor) :
    RawRechargingPolicy.decodeInitial (model cell hist false) NativePackageBundle.canonical=
      some (RawRechargingPolicy.EventState.mk hist
        (PublicationReplay.start cell+PublicationReplay.copies cell)
        (PublicationReplay.start cell+PublicationReplay.copies cell) 1) := by
  have hf : (model cell hist false).initialFactor.read NativePackageBundle.canonical=some hist := by
    change (((entryInitializer cell ()).reenv (fun _ : Unit => hist)).eval NativePackageBundle.canonical noRegisters ()).map (fun s => s.1.factor) = some hist
    rw [Expr.reenv_eval]
    change (evaluate (entryInitializer cell) NativePackageBundle.canonical hist ()).map _=some hist
    rw [canonical_initializer]; rfl
  have hp : (model cell hist false).initialProgress.read NativePackageBundle.canonical=
      some (PublicationReplay.start cell+PublicationReplay.copies cell) := by
    change (initializedView cell hist (native cell).progress).read _=_
    rw [initialized_view_eq cell hist _ _ _ (canonical_assigned cell),selected_canonical_initial]
    exact canonical_progress cell hist _
  have hr : (model cell hist false).initialRecord.read NativePackageBundle.canonical=
      some (PublicationReplay.start cell+PublicationReplay.copies cell) := by
    change (initializedView cell hist (native cell).record).read _=_
    rw [initialized_view_eq cell hist _ _ _ (canonical_assigned cell),selected_canonical_initial]
    exact canonical_record cell hist _
  have hb : (model cell hist false).initialBalance.read NativePackageBundle.canonical=some 1 := by
    change (initializedView cell hist (.map (fun accounts => ((accounts true).balance : Rat)) (native cell).accounts)).read _=_
    rw [initialized_view_eq cell hist _ _ _ (canonical_assigned cell),selected_canonical_initial]
    change ((native cell).accounts.eval NativePackageBundle.canonical (PublicationResources.run cell hist (PublicationReplay.start cell+PublicationReplay.copies cell)) ()).map _=some 1
    rw [canonical_accounts]; rfl
  simp only [RawRechargingPolicy.decodeInitial,hf,hp,hr,hb]
  rfl
-- Class (b): total initial EventState is exactly the optional raw readout, for any readiness proof.
theorem canonical_initial (cell : Owner) (hist : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) NativePackageBundle.canonical) :
    RawRechargingPolicy.initial (model cell hist false) NativePackageBundle.canonical ready=
      RawRechargingPolicy.EventState.mk hist
        (PublicationReplay.start cell+PublicationReplay.copies cell)
        (PublicationReplay.start cell+PublicationReplay.copies cell) 1 :=
  Option.some.inj ((RawRechargingPolicy.initial_eq _ _ ready).symm.trans (canonical_decode_initial cell hist))
-- Class (b): the full eight-clause package is actually accepted at every finite factor.
theorem canonical_package (cell : Owner) (hist x : Factor) :
    RawRechargingPolicy.PackageAt (model cell hist false) NativePackageBundle.canonical x :=
  (model_package_iff _ _ _ _ _).mpr (NativeClosedPackage.actual_package cell false)
-- Class (b): all eight factors are retained using the derived table and full original dispatcher.
theorem canonical_retains (cell : Owner) (hist x : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) NativePackageBundle.canonical) :
    RawRechargingPolicy.Retains (model cell hist false) NativePackageBundle.canonical ready factors x := by
  refine ⟨canonical_package cell hist x,?_⟩
  intro d
  rw [canonical_table]
  refine ⟨rfl,?_,?_⟩
  · refine ⟨?_,?_,x,1,by simp,by decide +kernel⟩
    · intro e he; simp only [List.mem_singleton] at he; subst e; change (0:Rat)≤1; decide +kernel
    · simp [Rat.add_zero]
  · intro o w member _
    exact ⟨factor_mem o,by change 0<(1:Nat); decide +kernel,by change 0<(1:Nat); decide +kernel,by change (0:Rat)≤1; decide +kernel,Rat.le_refl⟩
-- Class (b): greatest computed invariant contains every factor, derived from actual viability.
theorem canonical_greatest_contains (cell : Owner) (hist x : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) NativePackageBundle.canonical) :
    x∈RawRechargingPolicy.greatest (model cell hist false) NativePackageBundle.canonical ready :=
  RawRechargingPolicy.greatest_contains_every_viable _ _ ready factors
    (fun y _ => canonical_retains cell hist y ready) (factor_mem x)
-- Class (b): reserve is computed from every raw-derived outcome cost and equals the actual unit account.
theorem canonical_reserve (cell : Owner) (hist : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) NativePackageBundle.canonical) :
    RawRechargingPolicy.reserve (model cell hist false) NativePackageBundle.canonical ready=1 := by
  unfold RawRechargingPolicy.reserve RawRechargingPolicy.costs
  simp only [canonical_table]
  change RawRechargingPolicy.maxCost (factors.flatMap (fun _ => [()].flatMap (fun _ => factors.map (fun _ => (1 : Rat)))))=1
  decide +kernel
-- Class (b): initial native policy is total on the actual greatest invariant and computed reserve.
theorem canonical_total (cell : Owner) (hist : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) NativePackageBundle.canonical) :
    RawRechargingPolicy.TotalComputedPolicy (model cell hist false) NativePackageBundle.canonical ready := by
  unfold RawRechargingPolicy.TotalComputedPolicy
  rw [canonical_initial,canonical_reserve]
  exact ⟨canonical_greatest_contains cell hist hist ready,Rat.le_refl⟩
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): actual total raw initialization is the released native entry, independent of proof extraction.
theorem canonical_native_initial (cell : Owner) (hist : Factor)
    (ph : RegisterInitialization.Ready (entryInitializer cell) NativePackageBundle.canonical) :
    RegisterInitialization.initial (entryInitializer cell) NativePackageBundle.canonical ph hist=
      PublicationResources.run cell hist (PublicationReplay.start cell+PublicationReplay.copies cell) := by
  funext r; cases r
  exact Option.some.inj ((RegisterInitialization.initial_eq _ _ ph hist ()).symm.trans (canonical_initializer cell hist))
-- Class (b): actual native readiness on the original shared canonical assignment.
theorem canonical_native_ready (cell : Owner) : ResourceRuntime.Ready (native cell) NativePackageBundle.canonical :=
  (native_ready_iff _ _).mpr (by rw [canonical_assigned]; rfl)
-- Class (b): actual optional row on every generated time is the positive singleton safe response.
theorem canonical_native_row (cell : Owner) (h : Factor) (time : Nat) :
    (native cell).execution.row.eval NativePackageBundle.canonical (PublicationResources.run cell h time) ((),false)=some [(h,1)] := by
  obtain ⟨rows,he⟩ := (native cell).execution.row.present_of_complete NativePackageBundle.canonical
    (canonical_native_ready cell).1 (PublicationResources.run cell h time) ((),false)
  have translated := ResourceCellReindex.rows_equation id project (PublicationResources.runtime cell)
    NativePackageBundle.canonical (PublicationResources.run cell h time) () false
  have old := PublicationExecution.safe_episode_rows cell (swapOwner cell) (PublicationReplay.start cell)
    (PublicationReplay.stride cell) PublicationResources.assignment (PublicationReplay.round cell)
    (PublicationExecution.assigned_pair cell) (PublicationResources.run cell h time) ()
  change ResourceRuntime.rows (PublicationResources.runtime cell) PublicationResources.assignment (PublicationResources.run cell h time) () false=[(h,1)] at old
  rw [canonical_pullback,old] at translated
  change ResourceRuntime.rows (native cell) NativePackageBundle.canonical (PublicationResources.run cell h time) () false=[(h,1)] at translated
  simp only [ResourceRuntime.rows,he,Option.getD_some] at translated
  exact he.trans (congrArg some translated)
-- Class (b): actual native update on every generated time is the next released generated state.
theorem canonical_native_update (cell : Owner) (h : Factor) (time : Nat)
    (nh : ResourceRuntime.Ready (native cell) NativePackageBundle.canonical) :
    ResourceRuntime.update (native cell) NativePackageBundle.canonical nh (PublicationResources.run cell h time) () false h=
      PublicationResources.run cell h (time+1) := by
  have he := ResourceCellReindex.update_equation id project (PublicationResources.runtime cell)
    NativePackageBundle.canonical nh ((ResourceCellReindex.ready_iff _ _ _ _).mp nh)
    (PublicationResources.run cell h time) () false h
  exact he.trans (PublicationResources.target_update cell h time)
-- Class (b): the entire native ownership/removed-resource/source-absence predicate is actually true for all generated states.
theorem canonical_native_closed (cell : Owner) (h : Factor) (time : Nat) :
    ResourceRuntime.ResourceClosed (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical (PublicationResources.run cell h time) := by
  apply (ResourceCellReindex.closed_iff id project (PublicationResources.runtime cell) _ _ _).mpr
  exact PublicationResources.target_resource_closed cell h time
-- Class (b): actual safe native action is legal, with full vector account constraints.
theorem canonical_native_legal (cell : Owner) (h : Factor) (time : Nat) :
    ResourceRuntime.Legal (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical (PublicationResources.run cell h time) () false := by
  apply (ResourceCellReindex.legal_iff id project (PublicationResources.runtime cell) _ _ _ _ _).mpr
  exact PublicationResources.target_legal cell h time
-- Class (b): actual native after-state, residue and all four strict advancement/resource clauses hold universally in time.
theorem canonical_native_step_law (cell : Owner) (h : Factor) (time : Nat)
    (nh : ResourceRuntime.Ready (native cell) NativePackageBundle.canonical) :
    ResourceRuntime.StepLaw (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical nh
      (PublicationResources.run cell h time) () false h := by
  apply (ResourceCellReindex.step_law_iff id project (PublicationResources.runtime cell) _ _ nh
    (PublicationResources.ready cell) _ _ _ _).mpr
  exact PublicationResources.target_step_law cell h time
-- Class (b): auxiliary native generated-state relation; contains no acceptance or solvency verdict.
def related (cell : Owner) (r : ModeExecution.Registers) (x : RawRechargingPolicy.EventState Factor) : Prop :=
  ∃ h time, r=PublicationResources.run cell h time ∧ x=⟨h,time,time,1⟩
-- Class (b): CONSTRUCT the native binding; its fields are discharged by actual raw initial/read/update/full resource laws.
set_option maxHeartbeats 1600000 in
def binding (cell : Owner) (hist : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) NativePackageBundle.canonical)
    (nh : ResourceRuntime.Ready (native cell) NativePackageBundle.canonical)
    (ph : RegisterInitialization.Ready (entryInitializer cell) NativePackageBundle.canonical) :
    NativePolicyBridge.LocalBinding (model cell hist false) NativePackageBundle.canonical ready (native cell)
      (PublicationResources.cfg cell) nh (entryInitializer cell) ph hist where
  account := true
  auxiliary := related cell
  nativeCells := fun k => .cell k
  target := rfl
  init := by
    rw [canonical_native_initial,canonical_initial]
    exact ⟨canonical_decode cell hist _,hist,_,rfl,rfl⟩
  packageCells := by
    intro r x _ _ k
    rfl
  row := by
    intro r x _ aux d
    obtain ⟨h,time,rfl,rfl⟩ := aux
    cases d
    rw [canonical_table]
    exact canonical_native_row cell h time
  update := by
    intro r x _ aux _ _ d o w member _
    obtain ⟨h,time,rfl,rfl⟩ := aux
    cases d
    simp only [canonical_table,List.mem_singleton,Prod.mk.injEq] at member
    obtain ⟨ho,hw⟩ := member
    subst o; subst w
    simp only [canonical_table,RawRechargingPolicy.step]
    rw [canonical_native_update]
    have cancel : (1 : Rat)-1+1=1 := by decide +kernel
    rw [cancel]
    exact ⟨canonical_decode cell h (time+1),h,time+1,rfl,rfl⟩
  closed := by
    intro r x _ aux _ _
    obtain ⟨h,time,rfl,rfl⟩ := aux
    exact canonical_native_closed cell h time
  legal := by
    intro r x _ aux _ _ d
    obtain ⟨h,time,rfl,rfl⟩ := aux
    cases d
    rw [canonical_table]
    exact canonical_native_legal cell h time
  advancement := by
    intro r x _ aux _ _ d o w member _
    obtain ⟨h,time,rfl,rfl⟩ := aux
    cases d
    simp only [canonical_table,List.mem_singleton,Prod.mk.injEq] at member
    obtain ⟨ho,hw⟩ := member
    subst o; subst w
    rw [canonical_table]
    exact canonical_native_step_law cell h time nh
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): actual acquisition instruction on the same full primitive bundle namespace.
def acquisition (cell : Owner) := AcquisitionCellReindex.raw id project (PublicationReplay.raw cell)
-- Class (b): exact translated semantic Entry equivalence for EVERY partial assignment, without a supported mirror assumption.
theorem acquisition_entry_iff (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ah : AcquisitionExecution.Ready (acquisition cell) a)
    (jh : AcquisitionExecution.Ready (PublicationReplay.raw cell) (CellReindex.pullback id project a))
    (r : ModeExecution.Registers) :
    AcquisitionExecution.Entry (PublicationReplay.schema cell) (acquisition cell) a ah r ↔
      AcquisitionExecution.Entry (PublicationReplay.schema cell) (PublicationReplay.raw cell)
        (CellReindex.pullback id project a) jh r := by
  have rows : AcquisitionExecution.rows (acquisition cell) a=
      AcquisitionExecution.rows (PublicationReplay.raw cell) (CellReindex.pullback id project a) := by
    funext r d act
    exact AcquisitionCellReindex.rows_equation id project (PublicationReplay.raw cell) a r d act
  have arrival : ∀ rid arrived, AcquisitionExecution.Arrival (PublicationReplay.schema cell) (acquisition cell) a ah rid arrived ↔
      AcquisitionExecution.Arrival (PublicationReplay.schema cell) (PublicationReplay.raw cell) (CellReindex.pullback id project a) jh rid arrived :=
    AcquisitionCellReindex.arrival_iff id project (PublicationReplay.raw cell) a ah jh (PublicationReplay.schema cell)
  have update : ∀ run d act o, AcquisitionExecution.update (acquisition cell) a ah run d act o=
      AcquisitionExecution.update (PublicationReplay.raw cell) (CellReindex.pullback id project a) jh run d act o :=
    AcquisitionCellReindex.update_equation id project (PublicationReplay.raw cell) a ah jh
  have routes : (acquisition cell).routes.read a=(PublicationReplay.raw cell).routes.read (CellReindex.pullback id project a) :=
    CellReindex.cell_view_equation id project _ a
  have response : ∀ arrived env, (acquisition cell).arrivalResponse.eval a arrived env=
      (PublicationReplay.raw cell).arrivalResponse.eval (CellReindex.pullback id project a) arrived env :=
    CellReindex.evaluation id project _ a
  have domain : AcquisitionExecution.DomainCheck (PublicationReplay.schema cell) (acquisition cell)=
      AcquisitionExecution.DomainCheck (PublicationReplay.schema cell) (PublicationReplay.raw cell) := rfl
  have disturbances : (acquisition cell).execution.disturbances=(PublicationReplay.raw cell).execution.disturbances := rfl
  have actions : (acquisition cell).execution.actions=(PublicationReplay.raw cell).execution.actions := rfl
  simp only [AcquisitionExecution.Entry,domain,arrival,update,rows,routes,response,disturbances,actions]
-- Class (b): actual canonical acquisition readiness is inherited by exact primitive translation.
theorem canonical_acquisition_ready (cell : Owner) : AcquisitionExecution.Ready (acquisition cell) NativePackageBundle.canonical :=
  (AcquisitionCellReindex.ready_iff id project (PublicationReplay.raw cell) NativePackageBundle.canonical).mpr (PublicationReplay.ready cell)
-- Class (b): every actual semantic native entry is produced by the raw composed initializer; no chosen-entry restriction.
theorem every_native_entry_initialized (cell : Owner) (r : ModeExecution.Registers)
    (entry : AcquisitionExecution.Entry (PublicationReplay.schema cell) (acquisition cell) NativePackageBundle.canonical (canonical_acquisition_ready cell) r)
    (ph : RegisterInitialization.Ready (entryInitializer cell) NativePackageBundle.canonical) :
    ∃ hist, r=RegisterInitialization.initial (entryInitializer cell) NativePackageBundle.canonical ph hist := by
  have original := (acquisition_entry_iff cell NativePackageBundle.canonical (canonical_acquisition_ready cell) (PublicationReplay.ready cell) r).mp entry
  cases cell
  · obtain ⟨h,he⟩ := PublicationExecution.all_second_entries (PublicationReplay.ready false) r original
    refine ⟨h,?_⟩
    rw [canonical_native_initial]
    exact he
  · obtain ⟨h,he⟩ := PublicationExecution.all_first_entries (PublicationReplay.ready true) r original
    refine ⟨h,?_⟩
    rw [canonical_native_initial]
    exact he
-- Class (b): every raw selector has an actual semantic entry, establishing nonvacuity independently of continuation.
theorem every_initialized_is_native_entry (cell : Owner) (hist : Factor)
    (ph : RegisterInitialization.Ready (entryInitializer cell) NativePackageBundle.canonical) :
    AcquisitionExecution.Entry (PublicationReplay.schema cell) (acquisition cell) NativePackageBundle.canonical (canonical_acquisition_ready cell)
      (RegisterInitialization.initial (entryInitializer cell) NativePackageBundle.canonical ph hist) := by
  apply (acquisition_entry_iff cell NativePackageBundle.canonical (canonical_acquisition_ready cell) (PublicationReplay.ready cell) _).mpr
  rw [canonical_native_initial]
  cases cell
  · exact PublicationExecution.second_semantic_entry (PublicationReplay.ready false) hist
  · exact PublicationExecution.first_semantic_entry (PublicationReplay.ready true) hist
-- Class (b): original resource domain declaration holds on the translated actual runtime.
theorem canonical_native_domain (cell : Owner) : ResourceRuntime.DomainCheck (PublicationResources.cfg cell) (native cell) :=
  (ResourceCellReindex.domain_iff id project (PublicationResources.runtime cell) _).mpr (PublicationResources.domain cell)
-- Class (b): all six actual removed-resource roles and retained/removed account separation hold on the same assignment.
theorem canonical_native_withdrawal (cell : Owner) : ResourceRuntime.WithdrawalCheck (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical :=
  (ResourceCellReindex.withdrawal_iff id project (PublicationResources.runtime cell) _ _).mpr (PublicationResources.withdrawal_check cell)
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): actual decoded-policy native trajectory, initialized by composed raw instructions.
noncomputable def trajectory (cell : Owner) (hist : Factor) (stream : Nat → Unit) (outcomes : Nat → Factor) : Nat → ModeExecution.Registers :=
  NativePolicyBridge.nativeRun (model cell hist false) NativePackageBundle.canonical (canonical_model_ready cell hist)
    (native cell) (canonical_native_ready cell) (entryInitializer cell)
    ((initializer_ready_iff _ _).mpr (by rw [canonical_assigned]; rfl)) hist stream outcomes
-- Class (b): support is the actual native row on each actual trajectory state; no supplied support verdict.
def Supported (cell : Owner) (hist : Factor) (stream : Nat → Unit) (outcomes : Nat → Factor) : Prop :=
  ∀ n, StrategyGame.PositiveSupport (ResourceRuntime.rows (native cell) NativePackageBundle.canonical)
    (trajectory cell hist stream outcomes n) (stream n) false (outcomes n)
-- Class (b): every disturbance stream has an actually supported infinite native outcome stream.
theorem native_outcomes_exist (cell : Owner) (hist : Factor) (stream : Nat → Unit) :
    ∃ outcomes, Supported cell hist stream outcomes := by
  have actual := NativePolicyBridge.every_disturbance_has_native_supported_outcomes
    (model cell hist false) NativePackageBundle.canonical (canonical_model_ready cell hist)
    (native cell) (PublicationResources.cfg cell) (canonical_native_ready cell) (entryInitializer cell)
    ((initializer_ready_iff _ _).mpr (by rw [canonical_assigned]; rfl)) hist
    (binding cell hist _ _ _) (canonical_total cell hist _) stream
  simpa only [canonical_table] using actual
-- Class (b): all supported native streams return the full original package and native resource/strict advancement laws at every time.
theorem native_infinite_laws (cell : Owner) (hist : Factor) (stream : Nat → Unit) (outcomes : Nat → Factor)
    (supported : Supported cell hist stream outcomes) (n : Nat) :
    let r := trajectory cell hist stream outcomes n
    let x := RawRechargingPolicy.outcomeTrajectory (model cell hist false) NativePackageBundle.canonical (canonical_model_ready cell hist) stream outcomes n
    let y := RawRechargingPolicy.outcomeTrajectory (model cell hist false) NativePackageBundle.canonical (canonical_model_ready cell hist) stream outcomes (n+1)
    (NativeClosedPackage.package cell false).accept NativePackageBundle.canonical ∧
    ResourceRuntime.ResourceClosed (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical r ∧
    ResourceRuntime.Legal (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical r (stream n) false ∧
    ResourceRuntime.StepLaw (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical (canonical_native_ready cell) r (stream n) false (outcomes n) ∧
    NativePolicyBridge.decodeNative (native cell) true NativePackageBundle.canonical r=some x ∧
    x.progress<y.progress ∧ x.record<y.record ∧ 0≤x.balance := by
  have actual := NativePolicyBridge.every_native_supported_operational_laws
    (model cell hist false) NativePackageBundle.canonical (canonical_model_ready cell hist)
    (native cell) (PublicationResources.cfg cell) (canonical_native_ready cell) (entryInitializer cell)
    ((initializer_ready_iff _ _).mpr (by rw [canonical_assigned]; rfl)) hist
    (binding cell hist _ _ _) (canonical_total cell hist _) stream outcomes
    (by simpa only [canonical_table] using supported) n
  simpa only [canonical_table] using actual
-- Class (b): direct actual support forces the canonical factor and exact native next state for every step.
theorem native_trajectory_exact (cell : Owner) (hist : Factor) (stream : Nat → Unit) (outcomes : Nat → Factor)
    (supported : Supported cell hist stream outcomes) : ∀ n,
    trajectory cell hist stream outcomes n=PublicationResources.run cell hist (PublicationReplay.start cell+PublicationReplay.copies cell+n) := by
  intro n
  induction n with
  | zero => exact canonical_native_initial cell hist ((initializer_ready_iff _ _).mpr (by rw [canonical_assigned]; rfl))
  | succ n ih =>
    have hp := supported n
    have du : stream n=() := Subsingleton.elim _ _
    rw [ih,du] at hp
    unfold StrategyGame.PositiveSupport ResourceRuntime.rows at hp
    rw [canonical_native_row] at hp
    simp only [Option.getD_some,List.mem_singleton,Prod.mk.injEq] at hp
    obtain ⟨w,⟨ho,_⟩,_⟩ := hp
    change ResourceRuntime.update (native cell) NativePackageBundle.canonical (canonical_native_ready cell)
      (trajectory cell hist stream outcomes n) (stream n)
      (RawRechargingPolicy.table (model cell hist false) NativePackageBundle.canonical (canonical_model_ready cell hist)
        (RawRechargingPolicy.outcomeTrajectory (model cell hist false) NativePackageBundle.canonical (canonical_model_ready cell hist) stream outcomes n).factor (stream n)).action (outcomes n)=_
    rw [canonical_table,ih,du,ho,canonical_native_update,Nat.add_assoc]
-- Class (b): the ACTUAL native decoder is total and has unbounded strict progress/record with positive unit balance on every supported stream.
theorem native_decode_exact (cell : Owner) (hist : Factor) (stream : Nat → Unit) (outcomes : Nat → Factor)
    (supported : Supported cell hist stream outcomes) (n : Nat) :
    NativePolicyBridge.decodeNative (native cell) true NativePackageBundle.canonical (trajectory cell hist stream outcomes n)=
      some (RawRechargingPolicy.EventState.mk hist
        (PublicationReplay.start cell+PublicationReplay.copies cell+n)
        (PublicationReplay.start cell+PublicationReplay.copies cell+n) 1) := by
  rw [native_trajectory_exact cell hist stream outcomes supported n]
  exact canonical_decode cell hist _
-- Class (b): source withdrawal is an actual native false readout at every supported time.
theorem native_source_absent (cell : Owner) (hist : Factor) (stream : Nat → Unit) (outcomes : Nat → Factor)
    (supported : Supported cell hist stream outcomes) (n : Nat) :
    (native cell).sourcePresent.eval NativePackageBundle.canonical (trajectory cell hist stream outcomes n) ()=some false := by
  rw [native_trajectory_exact cell hist stream outcomes supported n]
  change (CellReindex.expression id project _).eval _ _ _=some false
  rw [CellReindex.evaluation,canonical_pullback]
  exact PublicationResources.target_absence cell _
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRechargeControls
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition CSTTT.AutonomyTheory.NativeRecharge
inductive Mutation where
  | canonical | nativeMissing | supplementMissing | otherMissing | rechargeZero | ownerSource | writersFalse | rowsZero
  deriving Repr
def patchCurrent (cell : Owner) (f : Input → Input) : Assignment Owner NativePackageBundle.Value :=
  put NativePackageBundle.canonical cell ((NativePackageBundle.canonical cell).map (fun p => ({p.1 with native := f p.1.native},p.2)))
def assignment (cell : Owner) : Mutation → Assignment Owner NativePackageBundle.Value
  | .canonical => NativePackageBundle.canonical
  | .nativeMissing => NativePackageBundle.fromArms (put NativePackagePrimitives.canonical (.inl cell) none)
  | .supplementMissing => NativePackageBundle.fromArms (put NativePackagePrimitives.canonical (.inr cell) none)
  | .otherMissing => put NativePackageBundle.canonical (swapOwner cell) none
  | .rechargeZero => patchCurrent cell (fun i => {i with temporal := {i.temporal with ledger := {i.temporal.ledger with recharge := 0}}})
  | .ownerSource => patchCurrent cell (fun i => {i with temporal := {i.temporal with resource := {i.temporal.resource with owner := swapOwner cell}}})
  | .writersFalse => patchCurrent cell (fun i => {i with temporal := {i.temporal with writers := fun _ => false}})
  | .rowsZero => patchCurrent cell (fun i => {i with temporal := {i.temporal with rows := fun _ _ => []}})
def acquisition (cell : Owner) := AcquisitionCellReindex.raw id project (PublicationReplay.raw cell)
def supportedFold (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) :
    ModeExecution.State → List (Unit × Bool × Factor) → Option ModeExecution.State
  | state, [] => some state
  | state, (d,act,o)::rest =>
    if SupportedAcquisitionSequence.stepCheck (acquisition cell) a (ModeExecution.pack state) d act o then do
      let next ← ((acquisition cell).execution.program ()).eval a (ModeExecution.pack state) (d,act,o)
      supportedFold cell a next rest
    else none
def supportedEntry (cell : Owner) (a : Assignment Owner NativePackageBundle.Value) (h : Factor) : Option ModeExecution.State := do
  let routes ← (acquisition cell).routes.read a
  let hist := (routes h).history
  let source ← ((acquisition cell).initializer ()).eval a noRegisters hist
  let histories ← (acquisition cell).histories.read a
  let terminal ← supportedFold cell a source (histories hist)
  let arrived ← ((acquisition cell).receive ()).eval a (ModeExecution.pack terminal) (hist,h)
  let da ← (acquisition cell).arrivalResponse.eval a (ModeExecution.pack arrived) (hist,h)
  if SupportedAcquisitionSequence.stepCheck (acquisition cell) a (ModeExecution.pack arrived) da.1 da.2 h then
    ((acquisition cell).execution.program ()).eval a (ModeExecution.pack arrived) (da.1,da.2,h)
  else none
end CSTTT.AutonomyTheory.NativeRechargeControls

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): every clause scope consumes exactly the selected shared primitive owner.
theorem package_scope_only (cell : Owner) (copy : Bool) (k : ClauseDispatcher.Kind) (owner : Owner) :
    owner∈((NativeClosedPackage.package cell copy).rule k).scope ↔ owner=cell := by
  cases k <;> simp [NativeClosedPackage.package,ClauseDispatcher.Rule.scope,ObjecthoodCells.Bindings.scope,ProfileRules.ClauseBindings.scope,
    ProfileRules.Bindings.scope,ExposureRules.Bindings.scope,ProtocolCreditRules.Bindings.scope,TemporalFactorCells.Bindings.scope,
    JointRules.Bindings.scope,OperationalViability.Bindings.scope,NativePackageBindings.c1,NativePackageBindings.profile,
    NativePackageBindings.exposure,NativePackageBindings.factor,NativePackageBindings.operational,
    NativePackageBindings.nativeView,NativePackageBindings.objecthoodView,CellReindex.cellView,
    NativeObjecthoodCells.bindings,NativeObjecthoodCells.cellOwner,ProfileCells.bindings,ExposureRepair.bindings,
    MemoryFrames.bindings,NativeOperationalCells.bindings,NativeCreditCells.bindings,NativeJointCells.bindings]
-- Class (b): the full eight-clause package depends only on the selected raw bundle, for every partial assignment.
theorem selected_package_iff (cell : Owner) (copy : Bool) (a : Assignment Owner NativePackageBundle.Value)
    (assigned : a cell=NativePackageBundle.canonical cell) :
    (NativeClosedPackage.package cell copy).accept a ↔ (NativeClosedPackage.package cell copy).accept NativePackageBundle.canonical := by
  apply ClauseDispatcher.Package.locality
  intro kind owner member
  have same := (package_scope_only cell copy kind owner).mp member
  subst owner; exact assigned
-- Class (b): the existing unconsumed-other-owner missing control preserves the complete actual package.
theorem other_missing_package (cell : Owner) :
    (NativeClosedPackage.package cell false).accept (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .otherMissing) := by
  apply (selected_package_iff cell false _ (by cases cell <;> rfl)).mpr
  exact NativeClosedPackage.actual_package cell false
-- Class (b): existing frozen wrong-owner mutation gives the actual source account owner for every generated time.
theorem wrong_owner_account (cell : Owner) (h : Factor) (time : Nat) :
    ((native cell).accounts.eval (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .ownerSource)
      (PublicationResources.run cell h time) ()).map (fun accounts => (accounts true).owner)=
      some (some (PublicationResources.cfg cell).source) := by
  cases cell <;> rfl
-- Class (b): existing frozen wrong-owner mutation directly refutes the actual full ResourceClosed readout, for every generated time.
theorem wrong_owner_not_closed (cell : Owner) (h : Factor) (time : Nat) :
    ¬ ResourceRuntime.ResourceClosed (PublicationResources.cfg cell) (native cell)
      (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .ownerSource) (PublicationResources.run cell h time) := by
  rintro ⟨accounts,required,w,ha,hr,_,_,_,_,_,ownership,_⟩
  have required_eq : required=[true] := (Option.some.inj hr).symm
  have actual := wrong_owner_account cell h time
  rw [ha,Option.map_some] at actual
  have demanded := (ownership true (by rw [required_eq]; simp)).1
  rw [demanded] at actual
  have same : (PublicationResources.cfg cell).target=(PublicationResources.cfg cell).source := Option.some.inj (Option.some.inj actual)
  cases cell <;> contradiction
-- Class (b): existing writer-false mutation has actual zero record for every generated time, not merely failed acceptance.
theorem writer_false_record (cell : Owner) (h : Factor) (time : Nat) :
    (native cell).record.eval (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .writersFalse) (PublicationResources.run cell h time) ()=some 0 := by
  cases cell
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
-- Class (b): existing zero-row mutation has actual empty target support at every generated time.
theorem zero_native_rows (cell : Owner) (h : Factor) (time : Nat) :
    (native cell).execution.row.eval (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .rowsZero) (PublicationResources.run cell h time) ((),false)=some [] := by
  cases cell
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
-- Class (b): existing unrecharged mutation has actual defined raw initialization and unfunded/zero-record/zero-balance decoded exit.
theorem unrecharged_initial_decoder (cell : Owner) (h : Factor) :
    (evaluate (entryInitializer cell) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .rechargeZero) h ()).bind
      (fun s => NativePolicyBridge.decodeNative (native cell) true (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .rechargeZero) (ModeExecution.pack s))=
      some (RawRechargingPolicy.EventState.mk h (PublicationReplay.start cell+PublicationReplay.copies cell) 0 0) := by
  cases cell
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): actual charge owner is obtained from the same raw native assignment at every generated time/action.
theorem canonical_native_charge (cell : Owner) (h : Factor) (time : Nat) (d : Unit) (act : Bool) :
    (native cell).charge.eval NativePackageBundle.canonical (PublicationResources.run cell h time) (d,act)=
      some (PublicationResources.charge cell) := by
  change (CellReindex.expression id project _).eval _ _ _=some _
  rw [CellReindex.evaluation,canonical_pullback]
  exact PublicationResources.target_charge cell h time d act
-- Class (b): every actual generated selected action has an actual target charge owner readout.
theorem native_selected_action_owner (cell : Owner) (hist : Factor) (stream : Nat → Unit) (outcomes : Nat → Factor)
    (supported : Supported cell hist stream outcomes) (n : Nat) :
    ((native cell).charge.eval NativePackageBundle.canonical (trajectory cell hist stream outcomes n) (stream n,false)).map ResourceRuntime.Charge.owner=
      some (PublicationResources.cfg cell).target := by
  rw [native_trajectory_exact cell hist stream outcomes supported n,canonical_native_charge,Option.map_some]
  cases cell <;> rfl
-- Class (b): all actual generated native factors remain inside the exact finite factor carrier.
theorem native_factor_inside (cell : Owner) (hist : Factor) (stream : Nat → Unit) (outcomes : Nat → Factor)
    (supported : Supported cell hist stream outcomes) (n : Nat) :
    ResourceRuntime.Inside (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical
      (trajectory cell hist stream outcomes n) := by
  rw [native_trajectory_exact cell hist stream outcomes supported n]
  exact ⟨hist,factor_mem hist,rfl⟩
-- Class (b): the ACTUAL canonical trajectory cannot lie in any finite FULL native-state list; this justifies the disclosed N10 event-register lift.
theorem native_full_state_not_finite (cell : Owner) (hist : Factor) (stream : Nat → Unit) (outcomes : Nat → Factor)
    (supported : Supported cell hist stream outcomes) (states : List ModeExecution.Registers) :
    ¬ ∀ n, trajectory cell hist stream outcomes n∈states := by
  intro inside
  apply FiniteProgress.no_infinite_strict_finite_state_run states (fun r => (r ()).1.counter)
  refine ⟨trajectory cell hist stream outcomes,inside,?_⟩
  intro n
  rw [native_trajectory_exact cell hist stream outcomes supported n,native_trajectory_exact cell hist stream outcomes supported (n+1)]
  change PublicationReplay.start cell+PublicationReplay.copies cell+n<PublicationReplay.start cell+PublicationReplay.copies cell+(n+1)
  omega
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): packing the sole actual native register preserves every coordinate.
theorem pack_unit (r : ModeExecution.Registers) : ModeExecution.pack (r ())=r := by
  funext k; cases k; rfl
-- Class (b): the executable supported fold returns exactly the scalar coordinate of the original checked supported fold, for every partial ready assignment/word.
theorem supported_fold_mirror_eq (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ah : AcquisitionExecution.Ready (acquisition cell) a) (state : ModeExecution.State)
    (word : List (Unit × Bool × Factor)) :
    CSTTT.AutonomyTheory.NativeRechargeControls.supportedFold cell a state word=
      (SupportedAcquisitionSequence.supportedFold (acquisition cell) a ah (ModeExecution.pack state) word).map (fun r => r ()) := by
  have acq_eq : CSTTT.AutonomyTheory.NativeRechargeControls.acquisition cell=acquisition cell := rfl
  induction word generalizing state with
  | nil => rfl
  | cons event rest ih =>
    rcases event with ⟨d,act,o⟩
    have actual := checked_execute_eq (acquisition cell).execution.program a ah.2.2.2.1 (ModeExecution.pack state) (d,act,o) ()
    change ((acquisition cell).execution.program ()).eval a (ModeExecution.pack state) (d,act,o)=
      some (AcquisitionExecution.update (acquisition cell) a ah (ModeExecution.pack state) d act o ()) at actual
    by_cases hc : SupportedAcquisitionSequence.stepCheck (acquisition cell) a (ModeExecution.pack state) d act o=true
    · simp only [CSTTT.AutonomyTheory.NativeRechargeControls.supportedFold,acq_eq,SupportedAcquisitionSequence.supportedFold,hc,ite_true,actual,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
      simpa only [pack_unit] using ih (AcquisitionExecution.update (acquisition cell) a ah (ModeExecution.pack state) d act o ())
    · simp only [CSTTT.AutonomyTheory.NativeRechargeControls.supportedFold,acq_eq,SupportedAcquisitionSequence.supportedFold,hc,Bool.false_eq_true,ite_false,Option.map_none]
-- Class (b): executable optional entry is exactly the ORIGINAL supported entry readout on every partial ready assignment; it supplies no route/normalization verdict.
theorem supported_entry_mirror_eq (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ah : AcquisitionExecution.Ready (acquisition cell) a) (rid : Factor) :
    CSTTT.AutonomyTheory.NativeRechargeControls.supportedEntry cell a rid=
      (SupportedAcquisitionSequence.firstEntry (acquisition cell) a ah rid rid).map (fun r => r ()) := by
  unfold CSTTT.AutonomyTheory.NativeRechargeControls.supportedEntry SupportedAcquisitionSequence.firstEntry
    SupportedAcquisitionSequence.postExit SupportedAcquisitionSequence.firstArrival SupportedAcquisitionSequence.fromStart
  simp only [show CSTTT.AutonomyTheory.NativeRechargeControls.acquisition cell=acquisition cell from rfl]
  cases hr : (acquisition cell).routes.read a with
  | none => simp only [hr,Option.bind_eq_bind,Option.bind_none,Option.map_none]
  | some routes =>
    simp only [hr,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
    have initial := RegisterInitialization.initial_eq (acquisition cell).initializer a ah.2.1 (routes rid).history ()
    change ((acquisition cell).initializer ()).eval a noRegisters (routes rid).history=
      some (AcquisitionExecution.initial (acquisition cell) a ah (routes rid).history ()) at initial
    rw [initial]
    simp only [Option.bind_some,Option.pure_def]
    cases hh : (acquisition cell).histories.read a with
    | none => simp only [hh,Option.bind_none,Option.map_none]
    | some histories =>
      simp only [hh,Option.bind_some,Option.pure_def]
      rw [supported_fold_mirror_eq cell a ah,pack_unit]
      cases hf : SupportedAcquisitionSequence.supportedFold (acquisition cell) a ah
        (AcquisitionExecution.initial (acquisition cell) a ah (routes rid).history) (histories (routes rid).history) with
      | none => simp only [hf,Option.map_none,Option.bind_none,Option.map_none]
      | some terminal =>
        simp only [hf,Option.map_some,Option.bind_some,Option.pure_def]
        rw [pack_unit]
        have receive := checked_execute_eq (acquisition cell).receive a ah.2.2.2.2 terminal ((routes rid).history,rid) ()
        change ((acquisition cell).receive ()).eval a terminal ((routes rid).history,rid)=
          some (AcquisitionExecution.receive (acquisition cell) a ah terminal (routes rid).history rid ()) at receive
        rw [receive]
        simp only [Option.bind_some,Option.bind_eq_bind]
        rw [pack_unit]
        cases da : (acquisition cell).arrivalResponse.eval a
          (AcquisitionExecution.receive (acquisition cell) a ah terminal (routes rid).history rid) ((routes rid).history,rid) with
        | none => simp only [da,Option.bind_none,Option.map_none]
        | some response =>
          simp only [da,Option.bind_some,Option.pure_def]
          by_cases hc : SupportedAcquisitionSequence.stepCheck (acquisition cell) a
            (AcquisitionExecution.receive (acquisition cell) a ah terminal (routes rid).history rid) response.1 response.2 rid=true
          · simp only [hc,ite_true,Option.map_some]
            exact checked_execute_eq (acquisition cell).execution.program a ah.2.2.2.1 _ (response.1,response.2,rid) ()
          · simp only [hc,Bool.false_eq_true,ite_false,Option.map_none]
-- Class (b): actual supported-entry absence is equivalent to executable absence on EVERY partial ready assignment.
theorem supported_entry_none_iff (cell : Owner) (a : Assignment Owner NativePackageBundle.Value)
    (ah : AcquisitionExecution.Ready (acquisition cell) a) (rid : Factor) :
    CSTTT.AutonomyTheory.NativeRechargeControls.supportedEntry cell a rid=none ↔
      SupportedAcquisitionSequence.firstEntry (acquisition cell) a ah rid rid=none := by
  rw [supported_entry_mirror_eq cell a ah rid]
  cases SupportedAcquisitionSequence.firstEntry (acquisition cell) a ah rid rid <;> simp
-- Class (b): the controller actually decoding prior native registers has the same total trajectory, on every supported stream.
theorem native_optional_trajectory_eq (cell : Owner) (hist : Factor) (stream : Nat → Unit) (outcomes : Nat → Factor)
    (supported : Supported cell hist stream outcomes) (n : Nat) :
    NativePolicyBridge.optionalNativeRun (model cell hist false) NativePackageBundle.canonical (canonical_model_ready cell hist)
      (native cell) (canonical_native_ready cell) true (entryInitializer cell)
      ((initializer_ready_iff _ _).mpr (by rw [canonical_assigned]; rfl)) hist stream outcomes n=
      some (trajectory cell hist stream outcomes n) := by
  exact NativePolicyBridge.optional_native_run_eq (model cell hist false) NativePackageBundle.canonical (canonical_model_ready cell hist)
    (native cell) (PublicationResources.cfg cell) (canonical_native_ready cell) (entryInitializer cell)
    ((initializer_ready_iff _ _).mpr (by rw [canonical_assigned]; rfl)) hist
    (binding cell hist _ _ _) (canonical_total cell hist _) stream outcomes
    (by simpa only [canonical_table] using supported) n
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): constructive every-entry native infinite return; finite factor and unbounded native event registers remain explicit.
theorem every_native_entry_infinite_return (cell : Owner) (entry : ModeExecution.Registers)
    (he : AcquisitionExecution.Entry (PublicationReplay.schema cell) (acquisition cell) NativePackageBundle.canonical (canonical_acquisition_ready cell) entry) :
    ∃ hist : Factor,
      (∀ stream outcomes, entry=trajectory cell hist stream outcomes 0) ∧
      (∀ stream, ∃ outcomes, Supported cell hist stream outcomes) ∧
      ∀ stream outcomes, Supported cell hist stream outcomes → ∀ n,
        let r := trajectory cell hist stream outcomes n
        (NativeClosedPackage.package cell false).accept NativePackageBundle.canonical ∧
        ResourceRuntime.Inside (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical r ∧
        ResourceRuntime.ResourceClosed (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical r ∧
        ResourceRuntime.Legal (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical r (stream n) false ∧
        ResourceRuntime.StepLaw (PublicationResources.cfg cell) (native cell) NativePackageBundle.canonical (canonical_native_ready cell) r (stream n) false (outcomes n) ∧
        NativePolicyBridge.decodeNative (native cell) true NativePackageBundle.canonical r=
          some (RawRechargingPolicy.EventState.mk hist
            (PublicationReplay.start cell+PublicationReplay.copies cell+n)
            (PublicationReplay.start cell+PublicationReplay.copies cell+n) 1) ∧
        (native cell).sourcePresent.eval NativePackageBundle.canonical r ()=some false ∧
        ((native cell).charge.eval NativePackageBundle.canonical r (stream n,false)).map ResourceRuntime.Charge.owner=some (PublicationResources.cfg cell).target := by
  obtain ⟨hist,initialized⟩ := every_native_entry_initialized cell entry he
    ((initializer_ready_iff _ _).mpr (by rw [canonical_assigned]; rfl))
  refine ⟨hist,fun _ _ => initialized,native_outcomes_exist cell hist,?_⟩
  intro stream outcomes supported n
  have laws := native_infinite_laws cell hist stream outcomes supported n
  exact ⟨laws.1,native_factor_inside cell hist stream outcomes supported n,laws.2.1,laws.2.2.1,laws.2.2.2.1,
    native_decode_exact cell hist stream outcomes supported n,native_source_absent cell hist stream outcomes supported n,
    native_selected_action_owner cell hist stream outcomes supported n⟩
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): actual table extraction returns the selected primitive response on every partial assignment.
theorem assigned_table (cell : Owner) (hist x : Factor) (act : Bool)
    (a : Assignment Owner NativePackageBundle.Value) (p : NativePackageBundle.Value cell)
    (assigned : a cell=some p) (ready : RawRechargingPolicy.Ready (model cell hist act) a) (d : Unit) :
    RawRechargingPolicy.table (model cell hist act) a ready x d=selectedResponse cell p act x d := by
  have actual := RawRechargingPolicy.table_eq (model cell hist act) a ready
  change (responseView cell act).read a=some _ at actual
  rw [response_view_eq,assigned,Option.map_some] at actual
  exact congrFun (congrFun (Option.some.inj actual).symm x) d
-- Class (b): the full fixed-policy retention law survives ANY partial assignment agreeing on the selected canonical bundle.
theorem selected_canonical_retains (cell : Owner) (hist x : Factor)
    (a : Assignment Owner NativePackageBundle.Value) (assigned : a cell=NativePackageBundle.canonical cell)
    (ready : RawRechargingPolicy.Ready (model cell hist false) a) :
    RawRechargingPolicy.Retains (model cell hist false) a ready factors x := by
  refine ⟨(model_package_iff _ _ _ _ _).mpr ((selected_package_iff _ _ _ assigned).mpr (NativeClosedPackage.actual_package cell false)),?_⟩
  intro d
  rw [assigned_table cell hist x false a (canonicalValue cell) (assigned.trans (canonical_assigned cell)) ready d]
  cases d
  rw [canonical_response]
  refine ⟨rfl,?_,?_⟩
  · refine ⟨?_,?_,x,1,by simp,by decide +kernel⟩
    · intro e he; simp only [List.mem_singleton] at he; subst e; change (0:Rat)≤1; decide +kernel
    · simp [Rat.add_zero]
  · intro o w member _
    exact ⟨factor_mem o,by change 0<(1:Nat); decide +kernel,by change 0<(1:Nat); decide +kernel,by change (0:Rat)≤1; decide +kernel,Rat.le_refl⟩
-- Class (b): missing unconsumed other bundle preserves the whole greatest invariant, not just numerical readouts.
theorem other_missing_greatest (cell : Owner) (hist x : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .otherMissing)) :
    x∈RawRechargingPolicy.greatest (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .otherMissing) ready := by
  apply RawRechargingPolicy.greatest_contains_every_viable _ _ ready factors
    (fun y _ => selected_canonical_retains cell hist y _ (by cases cell <;> rfl) ready)
  exact factor_mem x
-- Class (b): an actual empty computed response row directly refutes retention for any proposed invariant.
theorem empty_table_not_retains (cell : Owner) (hist x : Factor) (act : Bool)
    (a : Assignment Owner NativePackageBundle.Value) (ready : RawRechargingPolicy.Ready (model cell hist act) a)
    (S : List Factor) (empty : (RawRechargingPolicy.table (model cell hist act) a ready x ()).rows=[]) :
    ¬ RawRechargingPolicy.Retains (model cell hist act) a ready S x := by
  intro retained
  obtain ⟨o,w,member,_⟩ := (retained.2 ()).2.1.2.2
  rw [empty] at member
  exact List.not_mem_nil member
-- Class (b): all eight current-row deletion responses actually have no native support.
theorem zero_response_rows (cell : Owner) (h : Factor) :
    ((responseView cell false).read (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .rowsZero)).map (fun f => (f h ()).rows)=some [] := by
  cases cell
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
-- Class (b): all eight unrecharged responses inherit the actual unfunded exit and have no native support.
theorem unrecharged_response_rows (cell : Owner) (h : Factor) :
    ((responseView cell false).read (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .rechargeZero)).map (fun f => (f h ()).rows)=some [] := by
  cases cell
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
-- Class (b): the declared unavailable action has actual empty support at its frozen selector.
theorem unavailable_response_rows (cell : Owner) :
    ((responseView cell true).read NativePackageBundle.canonical).map (fun f => (f (false,false,false) ()).rows)=some [] := by
  cases cell <;> rfl
-- Class (b): wrong ownership is the actual source charge owner for every raw-derived response factor.
theorem wrong_response_owner (cell : Owner) (h : Factor) :
    ((responseView cell false).read (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .ownerSource)).map (fun f => (f h ()).owner)=
      some (PublicationResources.cfg cell).source := by
  cases cell
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
-- Class (b): the writer ablation has an actual zero record increment on every outcome branch.
theorem writer_response_increment (cell : Owner) (h o : Factor) :
    ((responseView cell false).read (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .writersFalse)).map
      (fun f => ((f h ()).branch o).recordIncrement)=some 0 := by
  cases cell
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j
  all_goals rcases o with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
-- Class (b): a raw response observation equals the complete extracted table observation, independently of readiness proof choice.
theorem table_observation_eq {Y : Type} (cell : Owner) (hist x : Factor) (act : Bool)
    (a : Assignment Owner NativePackageBundle.Value) (ready : RawRechargingPolicy.Ready (model cell hist act) a)
    (f : RawRechargingPolicy.Response Factor Bool Factor → Y) :
    ((responseView cell act).read a).map (fun t => f (t x ()))=
      some (f (RawRechargingPolicy.table (model cell hist act) a ready x ())) := by
  have actual := RawRechargingPolicy.table_eq (model cell hist act) a ready
  change (responseView cell act).read a=some _ at actual
  rw [actual,Option.map_some]
-- Class (b): actual observed support absence refutes retention and hence membership in the greatest invariant.
theorem observed_empty_not_greatest (cell : Owner) (hist x : Factor) (act : Bool)
    (a : Assignment Owner NativePackageBundle.Value) (ready : RawRechargingPolicy.Ready (model cell hist act) a)
    (empty : ((responseView cell act).read a).map (fun t => (t x ()).rows)=some []) :
    ∀ S, ¬ RawRechargingPolicy.Retains (model cell hist act) a ready S x := by
  have actual := table_observation_eq cell hist x act a ready (fun r => r.rows)
  have noRows := Option.some.inj (actual.symm.trans empty)
  intro S; exact empty_table_not_retains cell hist x act a ready S noRows
-- Class (b): empty-response controls refute actual greatest membership, not just a sufficient gate.
theorem observed_empty_outside_greatest (cell : Owner) (hist x : Factor) (act : Bool)
    (a : Assignment Owner NativePackageBundle.Value) (ready : RawRechargingPolicy.Ready (model cell hist act) a)
    (empty : ((responseView cell act).read a).map (fun t => (t x ()).rows)=some []) :
    x∉RawRechargingPolicy.greatest (model cell hist act) a ready := by
  intro inside
  exact observed_empty_not_greatest cell hist x act a ready empty _ (RawRechargingPolicy.greatest_retains _ _ ready x inside)
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): exact whole-model readiness of all frozen mutation recipes, every selector and action.
theorem control_model_ready_iff (cell : Owner) (hist : Factor) (act : Bool) (variant : CSTTT.AutonomyTheory.NativeRechargeControls.Mutation) :
    RawRechargingPolicy.Ready (model cell hist act) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell variant) ↔
      variant≠.nativeMissing ∧ variant≠.supplementMissing := by
  rw [model_ready_iff]
  cases cell <;> cases variant <;> simp [CSTTT.AutonomyTheory.NativeRechargeControls.assignment,CSTTT.AutonomyTheory.NativeRechargeControls.patchCurrent,put,
    NativePackageBundle.fromArms,NativePackagePrimitives.canonical,NativePackageBundle.canonical,swapOwner] <;> rfl
-- Class (b): direct complete Retains refutation from the frozen recharge control's actual empty row.
theorem unrecharged_not_retains (cell : Owner) (hist x : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .rechargeZero)) (S : List Factor) :
    ¬ RawRechargingPolicy.Retains (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .rechargeZero) ready S x :=
  observed_empty_not_greatest cell hist x false _ ready (unrecharged_response_rows cell x) S
-- Class (b): direct complete Retains refutation from the frozen empty-row control.
theorem zero_rows_not_retains (cell : Owner) (hist x : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .rowsZero)) (S : List Factor) :
    ¬ RawRechargingPolicy.Retains (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .rowsZero) ready S x :=
  observed_empty_not_greatest cell hist x false _ ready (zero_response_rows cell x) S
-- Class (b): the declared unavailable action refutes actual Retains at its actual selector.
theorem unavailable_not_retains (cell : Owner) (hist : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist true) NativePackageBundle.canonical) (S : List Factor) :
    ¬ RawRechargingPolicy.Retains (model cell hist true) NativePackageBundle.canonical ready S (false,false,false) :=
  observed_empty_not_greatest cell hist (false,false,false) true _ ready (unavailable_response_rows cell) S
-- Class (b): actual source charge ownership contradicts the full retention target ownership clause.
theorem wrong_owner_not_retains (cell : Owner) (hist x : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .ownerSource)) (S : List Factor) :
    ¬ RawRechargingPolicy.Retains (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .ownerSource) ready S x := by
  intro retained
  have actual := table_observation_eq cell hist x false _ ready (fun r => r.owner)
  have wrong := Option.some.inj (actual.symm.trans (wrong_response_owner cell x))
  have owned := (retained.2 ()).1
  change (RawRechargingPolicy.table (model cell hist false) _ ready x ()).owner=(PublicationResources.cfg cell).target at owned
  have same := wrong.symm.trans owned
  cases cell <;> contradiction
-- Class (b): actual zero branch record increments contradict strict record retention for every positive supported branch.
theorem writer_false_not_retains (cell : Owner) (hist x : Factor)
    (ready : RawRechargingPolicy.Ready (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .writersFalse)) (S : List Factor) :
    ¬ RawRechargingPolicy.Retains (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .writersFalse) ready S x := by
  intro retained
  obtain ⟨o,w,member,positive⟩ := (retained.2 ()).2.1.2.2
  have strict := ((retained.2 ()).2.2 o w member positive).2.2.1
  have actual := table_observation_eq cell hist x false _ ready (fun r => (r.branch o).recordIncrement)
  have zero := Option.some.inj (actual.symm.trans (writer_response_increment cell x o))
  rw [zero] at strict
  exact Nat.lt_irrefl 0 strict
-- Class (b): direct Retains refutations exclude the actual greatest set, independently of a sufficient-check implementation.
theorem refuted_retention_outside_greatest (cell : Owner) (hist x : Factor) (act : Bool)
    (a : Assignment Owner NativePackageBundle.Value) (ready : RawRechargingPolicy.Ready (model cell hist act) a)
    (refutation : ∀ S, ¬ RawRechargingPolicy.Retains (model cell hist act) a ready S x) :
    x∉RawRechargingPolicy.greatest (model cell hist act) a ready := by
  intro inside
  exact refutation _ (RawRechargingPolicy.greatest_retains _ _ ready x inside)
-- Class (b): every factor is outside the computed greatest invariant for any of the four actual failing native mechanism recipes.
theorem mechanism_controls_outside_greatest (cell : Owner) (hist x : Factor) (variant : CSTTT.AutonomyTheory.NativeRechargeControls.Mutation)
    (failure : variant=.rechargeZero ∨ variant=.rowsZero ∨ variant=.ownerSource ∨ variant=.writersFalse)
    (ready : RawRechargingPolicy.Ready (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell variant)) :
    x∉RawRechargingPolicy.greatest (model cell hist false) (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell variant) ready := by
  apply refuted_retention_outside_greatest cell hist x false _ ready
  rcases failure with same|same|same|same
  · subst variant; exact unrecharged_not_retains cell hist x ready
  · subst variant; exact zero_rows_not_retains cell hist x ready
  · subst variant; exact wrong_owner_not_retains cell hist x ready
  · subst variant; exact writer_false_not_retains cell hist x ready
-- Class (b): actual zero-row controls reject the original supported entry readback, all selectors and both owners.
set_option maxHeartbeats 800000 in
theorem zero_rows_supported_entry_none (cell : Owner) (hist : Factor) :
    CSTTT.AutonomyTheory.NativeRechargeControls.supportedEntry cell (CSTTT.AutonomyTheory.NativeRechargeControls.assignment cell .rowsZero) hist=none := by
  cases cell
  all_goals rcases hist with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> decide +kernel
end CSTTT.AutonomyTheory.NativeRecharge

namespace CSTTT.AutonomyTheory.NativeRecharge
open CSTTT CSTTT.TargetTheory.GenericHandoff RegisterInterpreter RegisterInitialization
open NativeComposition
-- Class (b): the wrong-owner primitive patch leaves actual raw initialization unchanged, all selectors and both owners.
theorem wrong_owner_initializer (cell : Owner) (hist : Factor) :
    evaluate (entryInitializer cell) (NativeRechargeControls.assignment cell .ownerSource) hist ()=
      some (PublicationResources.run cell hist (PublicationReplay.start cell+PublicationReplay.copies cell) ()) := by
  cases cell
  all_goals rcases hist with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
-- Class (b): the wrong-owner control directly refutes ResourceClosed at its ACTUAL raw initialized candidate.
theorem wrong_owner_initialized_not_closed (cell : Owner) (hist : Factor) (state : ModeExecution.State)
    (initialized : evaluate (entryInitializer cell) (NativeRechargeControls.assignment cell .ownerSource) hist ()=some state) :
    ¬ ResourceRuntime.ResourceClosed (PublicationResources.cfg cell) (native cell)
      (NativeRechargeControls.assignment cell .ownerSource) (ModeExecution.pack state) := by
  have same := Option.some.inj ((wrong_owner_initializer cell hist).symm.trans initialized)
  rw [← same,pack_unit]
  exact wrong_owner_not_closed cell hist _
-- Class (b): every factor is directly refuted, so these four actual mechanism controls have EMPTY greatest invariant.
theorem mechanism_controls_greatest_empty (cell : Owner) (hist : Factor) (variant : NativeRechargeControls.Mutation)
    (failure : variant=.rechargeZero ∨ variant=.rowsZero ∨ variant=.ownerSource ∨ variant=.writersFalse)
    (ready : RawRechargingPolicy.Ready (model cell hist false) (NativeRechargeControls.assignment cell variant)) :
    RawRechargingPolicy.greatest (model cell hist false) (NativeRechargeControls.assignment cell variant) ready=[] := by
  cases eq : RawRechargingPolicy.greatest (model cell hist false) (NativeRechargeControls.assignment cell variant) ready with
  | nil => rfl
  | cons first rest =>
    have outside := mechanism_controls_outside_greatest cell hist first variant failure ready
    rw [eq] at outside
    exact False.elim (outside (by simp))
-- Class (b): these controls directly refute the total computed policy from actual empty greatestness.
theorem mechanism_controls_not_total (cell : Owner) (hist : Factor) (variant : NativeRechargeControls.Mutation)
    (failure : variant=.rechargeZero ∨ variant=.rowsZero ∨ variant=.ownerSource ∨ variant=.writersFalse)
    (ready : RawRechargingPolicy.Ready (model cell hist false) (NativeRechargeControls.assignment cell variant)) :
    ¬ RawRechargingPolicy.TotalComputedPolicy (model cell hist false) (NativeRechargeControls.assignment cell variant) ready := by
  intro total
  have inside := total.1
  rw [mechanism_controls_greatest_empty cell hist variant failure ready] at inside
  exact List.not_mem_nil inside
end CSTTT.AutonomyTheory.NativeRecharge
