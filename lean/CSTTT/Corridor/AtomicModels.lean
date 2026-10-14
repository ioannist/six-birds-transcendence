import CSTTT.Corridor.AtomicChain

/-! Verbatim operative data from the frozen COR-POS-02 JSON files.
Stored transport/status verdicts are NOT used. New raw update recipes are
successive snapshot differences and residue suffixes, with exact equations and
positive increments checked separately; they describe the finite recorded
execution, not an unbounded transition model or a proof of nonflat holonomy.
The additive intervention semantics are the frozen model's rule.
-/
namespace CSTTT.CorridorTheory.AtomicChain.Models

/-- Source: cst-tt/models/corridors/COR-POS-02A.model.json, episode.stages. -/
def leftStages : List RawStage := [
  ⟨[17],true,⟨0,0,0,0,0,["route-root"],"leg-S-M-source-maint",17⟩⟩,
  ⟨[17, 55],true,⟨1,1,1,1,1,["route-root", "leg-S-M-mixed"],"leg-S-M-mixed-maint",17⟩⟩,
  ⟨[55],true,⟨2,2,2,2,3,["route-root", "leg-S-M-mixed", "leg-S-M-target"],"leg-S-M-target-maint",55⟩⟩]
/-- Source: COR-POS-02A.model.json, episode.events (source order). -/
def leftEvents : List RawEvent := [
  ⟨"s-chain-entry",17,0⟩,
  ⟨"leg-S-M-source-mixed",17,1⟩,
  ⟨"leg-S-M-target-mixed",55,1⟩,
  ⟨"m-boundary",55,2⟩]
/-- Source: COR-POS-02A.model.json, episode.dependencies. -/
def leftDependencies : List RawDependency := [
  ⟨"s-chain-entry","leg-S-M-source-mixed"⟩,
  ⟨"s-chain-entry","leg-S-M-target-mixed"⟩,
  ⟨"leg-S-M-source-mixed","m-boundary"⟩,
  ⟨"leg-S-M-target-mixed","m-boundary"⟩]
/-- Source: COR-POS-02A.model.json, carrier_chain. -/
def leftCarriers : List Nat := [17, 55]
/-- Derived by the disclosed successive-difference/suffix rule above. -/
def leftUpdates : List ReadoutUpdate := [
  ⟨1,1,1,1,1,["leg-S-M-mixed"],"leg-S-M-mixed-maint",17⟩,
  ⟨1,1,1,1,2,["leg-S-M-target"],"leg-S-M-target-maint",55⟩]
/-- Source: COR-POS-02A.model.json, legs[0], additive counterfactual and audit IDs. -/
def left : FiniteAtomicLeg where
  source := 17
  target := 55
  stages := leftStages
  events := leftEvents
  dependencies := leftDependencies
  updates := leftUpdates
  base := ⟨0,0,0⟩
  sourceContribution := ⟨1,0,1⟩
  targetContribution := ⟨1,2,2⟩
  sourceAudit := "leg-S-M-source-mixed"
  targetAudit := "leg-S-M-target-mixed"
  laterAudit := "m-boundary"

/-- Source: cst-tt/models/corridors/COR-POS-02B.model.json, episode.stages. -/
def rightStages : List RawStage := [
  ⟨[55],true,⟨2,2,2,2,3,["route-root", "leg-S-M-mixed", "leg-S-M-target"],"leg-S-M-target-maint",55⟩⟩,
  ⟨[55, 101],true,⟨3,3,3,3,4,["route-root", "leg-S-M-mixed", "leg-S-M-target", "leg-M-T-mixed"],"leg-M-T-mixed-maint",55⟩⟩,
  ⟨[101],true,⟨4,4,4,4,6,["route-root", "leg-S-M-mixed", "leg-S-M-target", "leg-M-T-mixed", "leg-M-T-target"],"leg-M-T-target-maint",101⟩⟩]
/-- Source: COR-POS-02B.model.json, episode.events (source order). -/
def rightEvents : List RawEvent := [
  ⟨"m-boundary",55,0⟩,
  ⟨"leg-M-T-source-mixed",55,1⟩,
  ⟨"leg-M-T-target-mixed",101,1⟩,
  ⟨"t-chain-exit",101,2⟩]
/-- Source: COR-POS-02B.model.json, episode.dependencies. -/
def rightDependencies : List RawDependency := [
  ⟨"m-boundary","leg-M-T-source-mixed"⟩,
  ⟨"m-boundary","leg-M-T-target-mixed"⟩,
  ⟨"leg-M-T-source-mixed","t-chain-exit"⟩,
  ⟨"leg-M-T-target-mixed","t-chain-exit"⟩]
/-- Source: COR-POS-02B.model.json, carrier_chain. -/
def rightCarriers : List Nat := [55, 101]
/-- Derived by the disclosed successive-difference/suffix rule above. -/
def rightUpdates : List ReadoutUpdate := [
  ⟨1,1,1,1,1,["leg-M-T-mixed"],"leg-M-T-mixed-maint",55⟩,
  ⟨1,1,1,1,2,["leg-M-T-target"],"leg-M-T-target-maint",101⟩]
/-- Source: COR-POS-02B.model.json, legs[0], additive counterfactual and audit IDs. -/
def right : FiniteAtomicLeg where
  source := 55
  target := 101
  stages := rightStages
  events := rightEvents
  dependencies := rightDependencies
  updates := rightUpdates
  base := ⟨2,2,3⟩
  sourceContribution := ⟨1,0,1⟩
  targetContribution := ⟨1,2,2⟩
  sourceAudit := "leg-M-T-source-mixed"
  targetAudit := "leg-M-T-target-mixed"
  laterAudit := "t-chain-exit"

/-- Source: cst-tt/models/corridors/COR-POS-02-COMPOSED.model.json, episode.stages. -/
def composedStages : List RawStage := [
  ⟨[17],true,⟨0,0,0,0,0,["route-root"],"leg-S-M-source-maint",17⟩⟩,
  ⟨[17, 55],true,⟨1,1,1,1,1,["route-root", "leg-S-M-mixed"],"leg-S-M-mixed-maint",17⟩⟩,
  ⟨[55],true,⟨2,2,2,2,3,["route-root", "leg-S-M-mixed", "leg-S-M-target"],"leg-S-M-target-maint",55⟩⟩,
  ⟨[55, 101],true,⟨3,3,3,3,4,["route-root", "leg-S-M-mixed", "leg-S-M-target", "leg-M-T-mixed"],"leg-M-T-mixed-maint",55⟩⟩,
  ⟨[101],true,⟨4,4,4,4,6,["route-root", "leg-S-M-mixed", "leg-S-M-target", "leg-M-T-mixed", "leg-M-T-target"],"leg-M-T-target-maint",101⟩⟩]
/-- Source: COR-POS-02-COMPOSED.model.json, episode.events (source order). -/
def composedEvents : List RawEvent := [
  ⟨"leg-M-T-source-mixed",55,3⟩,
  ⟨"leg-M-T-target-mixed",101,3⟩,
  ⟨"leg-S-M-source-mixed",17,1⟩,
  ⟨"leg-S-M-target-mixed",55,1⟩,
  ⟨"m-boundary",55,2⟩,
  ⟨"s-chain-entry",17,0⟩,
  ⟨"t-chain-exit",101,4⟩]
/-- Source: COR-POS-02-COMPOSED.model.json, episode.dependencies. -/
def composedDependencies : List RawDependency := [
  ⟨"s-chain-entry","leg-S-M-source-mixed"⟩,
  ⟨"s-chain-entry","leg-S-M-target-mixed"⟩,
  ⟨"leg-S-M-source-mixed","m-boundary"⟩,
  ⟨"leg-S-M-target-mixed","m-boundary"⟩,
  ⟨"m-boundary","leg-M-T-source-mixed"⟩,
  ⟨"m-boundary","leg-M-T-target-mixed"⟩,
  ⟨"leg-M-T-source-mixed","t-chain-exit"⟩,
  ⟨"leg-M-T-target-mixed","t-chain-exit"⟩]
/-- Source: COR-POS-02-COMPOSED.model.json, carrier_chain. -/
def composedCarriers : List Nat := [17, 55, 101]

theorem left_pass : AtomicLegPass left := by unfold AtomicLegPass; decide
theorem right_pass : AtomicLegPass right := by unfold AtomicLegPass; decide
theorem exact_frontier : AdjacentFrontierCheck left right = true := by decide
theorem two_leg_pass : CorridorPass [left,right] := by unfold CorridorPass; decide

theorem two_leg_corridor : StrictCorridorWitness [left,right] :=
  strictTemporalCorridorComposition_generic _ two_leg_pass

theorem composed_stages_exact : chainStages [left,right] = composedStages := by decide

theorem composed_events_exact :
    (chainEvents [left,right]).length = composedEvents.length ∧
    (chainEvents [left,right]).all (fun e => composedEvents.contains e) = true ∧
    composedEvents.all (fun e => (chainEvents [left,right]).contains e) = true := by decide

theorem composed_dependencies_exact :
    chainDependencies [left,right] = composedDependencies := by decide

theorem two_leg_append : StrictCorridorWitness ([left] ++ [right]) := by
  apply append_corridor
  · unfold CorridorPass; decide
  · unfold CorridorPass; decide
  · decide
  · decide

theorem route_comparison_domains_nonempty :
    (routeExecutions left).length = 2 ∧ (routeExecutions right).length = 2 := by decide

theorem route_status_computed : routeStatusOf left = .routeIndexed ∧
    routeStatusOf right = .routeIndexed := by decide

end CSTTT.CorridorTheory.AtomicChain.Models
