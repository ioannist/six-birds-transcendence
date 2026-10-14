import CSTTT.Targets.GenericHandoff.NativeComposition.FissionReadout

/-! The full certificate is populated from executed branch readouts. Named
C5 owner AND housing transport and whole C7 histories are derived from the
same publication, and autonomy includes actual owner readouts on all plays. -/
namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
open RegisterInterpreter PublicationReplay CSTTT.TransportTheory
local instance : DecidableEq PublicationFuture.Observation := instDecidableEqTemporalSnapshotReadout

def TransportLane (branch : Bool) (b : Assignment Owner NativePackageBundle.Value) : Prop :=
  ∀ p, b true=some p →
    ProtocolCreditRules.Transport (namedCreditTables (names true) p.2)
      (namedCreditTables (branchNames branch) p.1) NativeCreditCells.protocols id id (namedCreditImage branch) ∧
    JointHistoryTransport.Transport NativeJointCells.schema NativeJointCells.schema
      (NativeJointCells.data p.2) (NativeJointCells.data p.1) NativeJointCells.historyImage
theorem computed_transport (r : Raw) (branch : Bool) (hc : r.cutCurrentSource branch=false) :
    TransportLane branch (assignment r branch) := by
  intro p hp
  have he : PublicationMaps.exposure (r.initial branch) true=some p := by simpa [assignment,hc] using hp
  have publication := PublicationReturn.exposed_publication (r.initial branch) true p he
  rw [publication]
  exact ⟨named_raw_credit_transport branch p.2,PublicationMaps.raw_joint_transport p.2⟩

def Realized (b : Assignment Owner NativePackageBundle.Value) (hb : PublicationComposition.Ready b) (h : Factor) : Prop :=
  PublicationReturn.Realized b hb true h ∧ Function.Injective (names true)
def Lineage (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) : Prop :=
  FullFutureComposition.Laws (PublicationComposition.sourceFuture b hb true) (targetFuture branch b hb)
    (PublicationComposition.SourceClosure b hb true) (PublicationComposition.translate b hb true)
    (renameObservation branch ∘ PublicationFuture.image true) ∧
  FullFutureSufficient (PublicationComposition.sourceFuture b hb true) ∧
  FullFutureSufficient (targetFuture branch b hb) ∧ LegLane branch b ∧ TransportLane branch b ∧
  Function.Injective (branchNames branch)
def Autonomous (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) : Prop :=
  NamedControllerWins branch b hb ∧
  PublicationComposition.ControllerWins b hb true PublicationResources.safeController ∧ OwnerControl branch b hb

noncomputable def exitSignature (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) (h : Factor) : PublicationReturn.Signature :=
  {PublicationReturn.exitSignature b hb true h with
    future := targetFuture branch b hb
    corridor := (PublicationReturn.leg b true h).map (fun l => CSTTT.CorridorTheory.AtomicChain.exit (renameLeg branch l))}
noncomputable def summary (r : Raw) (hr : Ready r) (branch : Bool) (h : Factor) :
    FullHandoffData (Option PlacedBundle) PublicationReturn.Signature where
  source := ⟨17⟩
  target := ⟨branchTarget branch⟩
  sourcePackage := sourcePackage (assignment r branch)
  targetPackage := targetPackage branch (assignment r branch)
  entry := PublicationReturn.entrySignature (assignment r branch) (hr branch) true h
  exit := exitSignature branch (assignment r branch) (hr branch) h
  routeStatus := PublicationReturn.routeStatus (assignment r branch) true h
  targetOwner := ((targetFuture branch (assignment r branch) (hr branch)).observe
    (PublicationComposition.targetRoot (assignment r branch) (hr branch) true h)).owner
  realized := Realized (assignment r branch) (hr branch) h
  lineage := Lineage branch (assignment r branch) (hr branch)
  autonomous := Autonomous branch (assignment r branch) (hr branch)

theorem realized_of_checks (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) (checks : BranchChecks branch b hb) (h : Factor) : Realized b hb h := by
  obtain ⟨_,hp,hr,he,_,_,_⟩ := checks.parent
  obtain ⟨middle,final,hm,_,_,hentry,_,hroot,_⟩ := he.2 h
  exact ⟨⟨hp true true,hp true false,hr true,he.1 true h,middle,hm,hentry,hroot⟩,
    PublicationFuture.names_injective true⟩
theorem lineage_of_checks (r : Raw) (hr : Ready r) (branch : Bool)
    (checks : BranchChecks branch (assignment r branch) (hr branch))
    (hc : r.cutCurrentSource branch=false) : Lineage branch (assignment r branch) (hr branch) := by
  obtain ⟨_,_,_,_,hf,_,_⟩ := checks.parent
  exact ⟨target_laws branch _ _ hf,hf.2.1 true true,target_independently_sufficient branch _ _ hf,
    checks.leg,computed_transport r branch hc,branch_names_injective branch⟩
theorem autonomous_of_checks (branch : Bool) (b : Assignment Owner NativePackageBundle.Value)
    (hb : PublicationComposition.Ready b) (checks : BranchChecks branch b hb) : Autonomous branch b hb := by
  obtain ⟨_,_,_,_,_,_,hw⟩ := checks.parent
  exact ⟨checks.autonomy,hw true,checks.owners⟩
theorem certificate_of_checks (r : Raw) (hr : Ready r) (branch : Bool)
    (checks : BranchChecks branch (assignment r branch) (hr branch))
    (hc : r.cutCurrentSource branch=false) (h : Factor) : FullHandoffCertificate (summary r hr branch h) := by
  refine ⟨?_,checks.targetOwner h,realized_of_checks branch _ _ checks h,
    lineage_of_checks r hr branch checks hc,autonomous_of_checks branch _ _ checks⟩
  change (⟨17⟩ : CarrierId)≠⟨branchTarget branch⟩
  cases branch <;> decide +kernel

/-- The actual readout returns both complete certificates and a literally
shared whole source package, physical initializer, future, root and corridor. -/
theorem computed_full_fork (r : Raw) (h : Readout r) :
    ∃ hr : Ready r,
      (∀ branch factor, Nonempty (FullHandoffCertificate (summary r hr branch factor))) ∧
      (∀ factor, (summary r hr false factor).sourcePackage=(summary r hr true factor).sourcePackage ∧
        (summary r hr false factor).entry=(summary r hr true factor).entry) := by
  obtain ⟨hr,hc,hp,hs⟩ := h
  refine ⟨hr,?_,?_⟩
  · intro branch factor
    exact ⟨certificate_of_checks r hr branch (hc branch)
      (current_source_required r branch ⟨hr,hc,hp,hs⟩) factor⟩
  · intro factor
    exact ⟨hp,hs factor⟩
theorem canonical_certificate (branch : Bool) (h : Factor) :
    FullHandoffCertificate (summary canonicalRaw canonical_ready branch h) := by
  apply certificate_of_checks
  · simpa only [canonical_assignment] using canonical_branch_checks branch
  · rfl
theorem canonical_whole_source (h : Factor) :
    (summary canonicalRaw canonical_ready false h).sourcePackage=(summary canonicalRaw canonical_ready true h).sourcePackage ∧
    (summary canonicalRaw canonical_ready false h).entry=(summary canonicalRaw canonical_ready true h).entry := by
  constructor
  · rfl
  · rfl

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.NativeFission
