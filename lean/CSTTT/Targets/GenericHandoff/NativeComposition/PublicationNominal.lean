import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationResources
import CSTTT.Targets.GenericHandoff.NominalProtocol

/-! Nominal metadata reads actual runtime source presence at the supplied run.
The historical acquisition receiver remains primitive content. No impossible
all-context equality to one static source-presence flag is asserted. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationNominal
open RegisterInterpreter PublicationReplay PublicationResources

def specification (cell : Owner) : NominalProtocol.Specification Factor Bool Factor History Route Stage Bool Owner Bool :=
  ⟨some,NativeOperationalCells.schema cell,factors,factors,stages,0,2,true,1,1,[true]⟩
def events (p : Input × Input) : List (AcquisitionEndpoint.SupportedEvent Stage Bool) :=
  p.2.temporal.events.map (fun e => ⟨e.id,e.fromStage,e.toStage,e.atomic,e.strictStep,
    !e.id && p.1.receiver.sourcePresent,p.1.receiver.targetFunded⟩)
def data (p : Input × Input) : NominalProtocol.Data Factor Bool Factor History Route Stage Bool Owner :=
  ⟨p.2.temporal.rows,p.1.temporal.rows,p.2.temporal.policy,p.1.temporal.policy,p.1.temporal.ticks,
    p.1.temporal.resource,p.1.temporal.ledger,p.1.temporal.histories,events p,p.2.temporal.realized,
    p.1.receiver,p.1.temporal.routes,p.1.temporal.writers⟩
def views (cell : Owner) : NominalProtocol.Views Owner MemoryValue Factor Bool Factor History Route Stage Bool Owner :=
  ⟨⟨cell,fun p => p.2.temporal.rows⟩,⟨cell,fun p => p.1.temporal.rows⟩,
    ⟨cell,fun p => p.2.temporal.policy⟩,⟨cell,fun p => p.1.temporal.policy⟩,
    ⟨cell,fun p => p.1.temporal.ticks⟩,⟨cell,fun p => p.1.temporal.resource⟩,
    ⟨cell,fun p => p.1.temporal.ledger⟩,⟨cell,fun p => p.1.temporal.histories⟩,
    ⟨cell,events⟩,⟨cell,fun p => p.2.temporal.realized⟩,⟨cell,fun p => p.1.receiver⟩,
    ⟨cell,fun p => p.1.temporal.routes⟩,⟨cell,fun p => p.1.temporal.writers⟩⟩
def metadata (cell : Owner) : Expr Owner MemoryValue Unit (fun _ => ModeExecution.State) Unit (NominalProtocol.Metadata Bool) :=
  .map (fun p : ResourceRuntime.Withdrawal Bool × Bool => ⟨p.1.removedRoles,p.1.retained,p.2⟩)
    (.pair (.map (fun p : Input × Input => p.1.withdrawal) (.cell cell)) (runtime cell).sourcePresent)
def metadataValue (p : Input × Input) (cell mode : Owner) : NominalProtocol.Metadata Bool :=
  ⟨p.1.withdrawal.removedRoles,p.1.withdrawal.retained,decide (mode=swapOwner cell)⟩
def PassAt (cell : Owner) (a : Assignment Owner MemoryValue) (x : ModeExecution.Registers) : Prop :=
  ∃ wd, (metadata cell).eval a x ()=some wd ∧ NominalProtocol.Pass (specification cell) wd (views cell) a

theorem decoded (cell : Owner) (a : Assignment Owner MemoryValue) :
    (NominalProtocol.reader (views cell)).read a=(a cell).map data := by
  cases ha : a cell <;> simp [NominalProtocol.reader,views,StaticView.read,StaticView.ofCell,Expr.eval,CellView.read,ha,data]
theorem metadata_decoded (cell : Owner) (a : Assignment Owner MemoryValue) (x : ModeExecution.Registers) :
    (metadata cell).eval a x ()=(a cell).map (fun p => metadataValue p cell (x ()).2) := by
  cases ha : a cell <;> simp [metadata,runtime,ModeExecution.resources,ModeExecution.stateExpr,Expr.eval,ha,metadataValue]
theorem pass_iff (cell : Owner) (a : Assignment Owner MemoryValue) (x : ModeExecution.Registers) :
    PassAt cell a x ↔ ∃ p, a cell=some p ∧
      NominalProtocol.check (specification cell) (metadataValue p cell (x ()).2) (data p) := by
  simp only [PassAt,NominalProtocol.Pass,metadata_decoded,decoded]
  cases a cell <;> simp
theorem missing_rejected (cell : Owner) (a : Assignment Owner MemoryValue) (x : ModeExecution.Registers)
    (hm : a cell=none) : ¬ PassAt cell a x := by
  rw [pass_iff]
  simp [hm]
theorem source_mode_rejected (cell : Owner) (a : Assignment Owner MemoryValue) (x : ModeExecution.Registers)
    (hx : (x ()).2=swapOwner cell) : ¬ PassAt cell a x := by
  rw [pass_iff]
  rintro ⟨p,_,h⟩
  have habsent := h.2.2.1
  simp [metadataValue,hx] at habsent

theorem withdrawn_operational (cell : Owner) :
    NominalProtocol.withdrawn (specification cell)
      (metadataValue (PublicationExecution.episodePair (round cell)) cell cell)
      (data (PublicationExecution.episodePair (round cell)))=
      NativeOperationalCells.data (AvailabilityFactor.input cell) := by
  cases cell <;> rfl
theorem canonical_check (cell : Owner) :
    NominalProtocol.check (specification cell)
      (metadataValue (PublicationExecution.episodePair (round cell)) cell cell)
      (data (PublicationExecution.episodePair (round cell))) := by
  unfold NominalProtocol.check
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro role hr; cases cell <;> exact hr
  · intro role hr; cases cell <;> exact hr
  · cases cell <;> rfl
  · rw [withdrawn_operational]; exact (NativeOperationalCells.actual_accept cell).2.2.1
  · rw [withdrawn_operational]; exact (NativeOperationalCells.actual_accept cell).2.2.2.1
  · intro s hs a ha he; cases cell <;> rfl
  · exact (by decide +kernel : factors≠[])
  · intro rid hr; cases cell <;> rfl
  · cases cell <;> decide +kernel
  · rw [withdrawn_operational]; exact (NativeOperationalCells.actual_accept cell).2.2.2.2
  · intro rid hr
    cases cell
    all_goals rcases rid with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> decide +kernel

theorem actual_pass_at (cell : Owner) (x : ModeExecution.Registers) (hx : (x ()).2=cell) :
    PassAt cell assignment x := by
  rw [pass_iff]
  refine ⟨PublicationExecution.episodePair (round cell),PublicationExecution.assigned_pair cell,?_⟩
  rw [hx]
  exact canonical_check cell
theorem required_is_actual (cell : Owner) (a : Assignment Owner MemoryValue) (x : ModeExecution.Registers) :
    (runtime cell).required.eval a x ()=some (specification cell).required := rfl
theorem c8_is_actual (cell : Owner) : (NativeClosedPackage.package cell false).rule .c8=
    ClauseDispatcher.Rule.c8 inferInstance inferInstance inferInstance (specification cell).viability
      (specification cell).outcomes (NativePackageBindings.operational cell false) := by
  cases cell <;> rfl
theorem every_safe_play_pass (cell : Owner) (entry : ModeExecution.Registers) (he : entries cell entry)
    (x : ModeExecution.Registers) (past : List ModeExecution.Registers)
    (hp : StrategyGame.Play (ResourceRuntime.rows (runtime cell) assignment)
      (ResourceRuntime.update (runtime cell) assignment (PublicationResources.ready cell)) safeController entry (x::past)) :
    PassAt cell assignment x := by
  obtain ⟨h,time,rfl⟩ := every_safe_play_inside cell entry he _ hp x past rfl
  exact actual_pass_at cell _ rfl

def qualifiedPackageAt (cell : Owner) (x : ModeExecution.Registers) : Prop :=
  packageAt cell x ∧ PassAt cell assignment x
def QualifiedOperationalReadout (cell : Owner) : Prop :=
  StrategyGame.GameReadout (ResourceRuntime.rows (runtime cell) assignment)
    (ResourceRuntime.update (runtime cell) assignment (PublicationResources.ready cell)) (entries cell)
    (ResourceRuntime.DomainCheck (cfg cell) (runtime cell) ∧ ResourceRuntime.WithdrawalCheck (cfg cell) (runtime cell) assignment)
    (qualifiedPackageAt cell) (ResourceRuntime.ResourceClosed (cfg cell) (runtime cell) assignment)
    (ResourceRuntime.Legal (cfg cell) (runtime cell) assignment)
    (ResourceRuntime.StepLaw (cfg cell) (runtime cell) assignment (PublicationResources.ready cell))
theorem qualified_operational_autonomy (cell : Owner) : QualifiedOperationalReadout cell := by
  refine ⟨⟨domain cell,withdrawal_check cell⟩,entries_nonempty cell,safeController,?_⟩
  intro entry he x past hp
  have hx := every_safe_play_inside cell entry he _ hp x past rfl
  refine ⟨⟨package_inside cell x hx,every_safe_play_pass cell entry he x past hp⟩,?_,?_⟩
  · obtain ⟨h,time,rfl⟩ := hx; exact target_resource_closed cell h time
  · intro d; cases d
    obtain ⟨h,time,rfl⟩ := hx
    refine ⟨target_legal cell h time,target_normalized cell h time,?_⟩
    intro o ho
    have he := (target_positive_unique cell h o time).mp ho
    subst o
    exact target_step_law cell h time

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationNominal
