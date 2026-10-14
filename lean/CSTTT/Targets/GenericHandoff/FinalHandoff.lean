import CSTTT.Targets.GenericHandoff.NominalHandoff
import CSTTT.Targets.GenericHandoff.ReceiverGate

/-! Owning handoff with nominal and receiver raw recipes. Source/staged/package,
complete actual lineage, nominal autonomy, receiver/counterfactual, retained
route status and recognition scope are independent defined checks. The three
lane conclusions consume their own subchecks. Full autonomy's same-package
implication remains disclosed; operational autonomy has separate semantics. -/
namespace CSTTT.TargetTheory.GenericHandoff.FinalHandoff
open RegisterInterpreter

structure Raw (SC Cell : Type) (SourceValue : SC → Type) (Value : Cell → Type)
    (R SR TR : Type) (RV : R → Type) (SRV : SR → Type) (TRV : TR → Type)
    (S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint : Type) where
  base : OwningHandoff.RawHandoff SC Cell SourceValue Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint
  nominal : NominalHandoff.Instructions Cell Value S Resource
  receiver : ReceiverGate.Instructions base

variable {SC Cell R SR TR S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint : Type}
  {SourceValue : SC → Type} {Value : Cell → Type} {RV : R → Type} {SRV : SR → Type} {TRV : TR → Type}
local notation "Model" => Raw SC Cell SourceValue Value R SR TR RV SRV TRV S A O H HF Route Stage Id Owner D P Q Factor Resource Endpoint
variable [DecidableEq Cell] [DecidableEq S] [DecidableEq O] [DecidableEq Route]
  [DecidableEq Stage] [DecidableEq Id] [DecidableEq Owner] [DecidableEq Resource]

def IntegratedTargetRealization (m : Model) (a : Assignment SC SourceValue) :=
  OwningHandoff.IntegratedTargetRealization m.base a

def PostWithdrawalFullAutonomy (m : Model) (a : Assignment SC SourceValue) :=
  NominalHandoff.FullAutonomy m.base m.nominal a
def PostWithdrawalOperationalAutonomy (m : Model) (a : Assignment SC SourceValue) :=
  NominalHandoff.OperationalAutonomy m.base m.nominal a

def ReceiverReadout (m : Model) (a : Assignment SC SourceValue) :=
  ReceiverGate.Readout m.base m.receiver (OwningHandoff.target m.base a)

def recognitionStatusOf (m : Model) := OwningHandoff.recognitionStatusOf m.base

variable [DecidableEq P] [DecidableEq Q]
def StrictTemporalLineage (m : Model) (a : Assignment SC SourceValue) :=
  OwningHandoff.StrictTemporalLineage m.base a

def ScopeCheck (m : Model) (a : Assignment SC SourceValue) : Prop :=
  RuntimeComponents.retainedRouteStatus m.base.schema m.base.runtime m.base.route (OwningHandoff.target m.base a) = .routeIndexed ∧
    recognitionStatusOf m = .notAddressed

def HandoffPass_F (m : Model) (a : Assignment SC SourceValue) : Prop :=
  NominalHandoff.HandoffPass_F m.base m.nominal a ∧
    ReceiverGate.Subcheck m.base m.receiver (OwningHandoff.target m.base a) ∧ ScopeCheck m a

def HandoffPass_O (m : Model) (a : Assignment SC SourceValue) : Prop :=
  NominalHandoff.HandoffPass_O m.base m.nominal a ∧
    ReceiverGate.Subcheck m.base m.receiver (OwningHandoff.target m.base a) ∧ ScopeCheck m a

theorem temporalFIACHCertificateSoundness_generic_F (m : Model) (a : Assignment SC SourceValue)
    (h : HandoffPass_F m a) :
    IntegratedTargetRealization m a ∧ StrictTemporalLineage m a ∧ PostWithdrawalFullAutonomy m a :=
  NominalHandoff.soundness_F m.base m.nominal a h.1

theorem temporalFIACHCertificateSoundness_generic_O (m : Model) (a : Assignment SC SourceValue)
    (h : HandoffPass_O m a) :
    IntegratedTargetRealization m a ∧ StrictTemporalLineage m a ∧ PostWithdrawalOperationalAutonomy m a :=
  NominalHandoff.soundness_O m.base m.nominal a h.1

theorem receiver_soundness_F (m : Model) (a : Assignment SC SourceValue) (h : HandoffPass_F m a) : ReceiverReadout m a :=
  ReceiverGate.soundness m.base m.receiver _ h.1.2.2.2.2.2.1.1.2.2.1 h.2.1

theorem receiver_soundness_O (m : Model) (a : Assignment SC SourceValue) (h : HandoffPass_O m a) : ReceiverReadout m a :=
  ReceiverGate.soundness m.base m.receiver _ h.1.2.2.2.2.2.1.1.2.2.1 h.2.1

omit [DecidableEq P] [DecidableEq Q] in
theorem full_autonomy_implies_package (m : Model) (a : Assignment SC SourceValue)
    (h : PostWithdrawalFullAutonomy m a) : IntegratedTargetRealization m a :=
  OwningHandoff.full_autonomy_implies_package m.base a h.2

omit [DecidableEq P] [DecidableEq Q] in
theorem package_failure_implies_no_full (m : Model) (a : Assignment SC SourceValue)
    (h : ¬ IntegratedTargetRealization m a) : ¬ PostWithdrawalFullAutonomy m a :=
  fun full => h (full_autonomy_implies_package m a full)

theorem receiver_failure_no_handoff (m : Model) (a : Assignment SC SourceValue) (h : ¬ ReceiverReadout m a) :
    ¬ HandoffPass_F m a ∧ ¬ HandoffPass_O m a :=
  ⟨fun pass => h (receiver_soundness_F m a pass),fun pass => h (receiver_soundness_O m a pass)⟩

end CSTTT.TargetTheory.GenericHandoff.FinalHandoff
