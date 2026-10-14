import CSTTT.Targets.GenericHandoff.ClauseDispatcher
import CSTTT.Targets.GenericHandoff.TemporalFactorClosure

/-! The closed C6 dispatcher derives its runtime obligations from the decoded
shared primitives. No future, code, observer, dynamics, or closure is supplied.
This is the finite temporal constructor; arbitrary run-context recipes still
need their own sound lifting proof in the hybrid handoff architecture. -/
namespace CSTTT.TargetTheory.GenericHandoff.ClauseDispatcher
open CSTTT.TransportTheory
variable {Cell S A O H RouteId Stage Id Owner : Type} {Value : Cell → Type}
  [DecidableEq S] [DecidableEq O] [DecidableEq RouteId] [DecidableEq Stage] [DecidableEq Id]
  [DecidableEq Owner]

/-- All-state, all-word sufficiency and the nonempty realized run closure are
consequences of the SAME decoded raw C6 rule, not additional acceptance flags. -/
theorem c6_runtime_soundness
    (cfg : TemporalFactorRules.Schema S A O H RouteId Stage Id Owner)
    (v : TemporalFactorCells.Bindings Cell Value S A O H RouteId Stage Id Owner)
    (a : Assignment Cell Value) (period : Nat)
    (h : (Rule.c6 inferInstance inferInstance inferInstance inferInstance inferInstance cfg v).accept a) :
    ∃ d, TemporalFactorCells.decoded v a = some d ∧
      TemporalFactorRules.Accept cfg d ∧
      FullFutureSufficient (TemporalFactorRules.future cfg d period) ∧
      TemporalFactorRules.ClosureLaws cfg d period ∧
      (∃ x ∈ TemporalFactorRules.roots cfg d, ∃ y ∈ TemporalFactorRules.roots cfg d,
        x ≠ y ∧ TemporalFactorRules.code cfg d period x = TemporalFactorRules.code cfg d period y) ∧
      (∀ x, TemporalFactorRules.Closure cfg d x → ∀ act o,
        TemporalFactorRules.budgetAfter d = d.ledger.initial ∧ TemporalFactorRules.budgetAfter d > 0 ∧
        (TemporalFactorRules.update cfg d x act o).funded = true ∧
        (TemporalFactorRules.observe cfg d period (TemporalFactorRules.update cfg d x act o)).progress >
          (TemporalFactorRules.observe cfg d period x).progress ∧
        (TemporalFactorRules.observe cfg d period (TemporalFactorRules.update cfg d x act o)).record =
          (TemporalFactorRules.observe cfg d period x).record + cfg.stageAdvance) := by
  obtain ⟨d,hd,ha⟩ := h
  exact ⟨d,hd,ha,TemporalFactorRules.all_words cfg d period ha,
    TemporalFactorRules.closure_laws cfg d period,
    TemporalFactorRules.accepted_coarse_roots cfg d period ha,
    fun x hx act o => TemporalFactorRules.accepted_advancement cfg d period ha x hx act o⟩

end CSTTT.TargetTheory.GenericHandoff.ClauseDispatcher
