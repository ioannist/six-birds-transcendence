import CSTTT.FullNative02.Acquisition
import CSTTT.FullNative02.Ownership

namespace CSTTT.FullNative02
open FullNative
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

theorem main_positive_rows :
    fusionRows renewable branchesWorld mainRequest =
      (meeting mainParents.rom mainParents.left.current mainParents.right.current false false).map
        (fun p => (settle renewable branchesWorld mainRequest mainParents p
          (pairProbability mainParents.rom mainParents.left.current mainParents.right.current false false p),
          pairProbability mainParents.rom mainParents.left.current mainParents.right.current false false p)) := by
  have acts : mainRequest.leftAction=false ∧ mainRequest.rightAction=false := by decide +kernel
  simp only [fusionRows,main_view,acts.1,acts.2,if_neg (Nat.ne_of_gt main_meeting_present)]

/-- Every actual supported output of the frozen main row witnesses the original
relation-valued schema; all probabilities and parent paths are computed. -/
theorem every_actual_positive_output (outcome : Settlement) (probability : Rat)
    (member : (outcome,probability)∈fusionRows renewable branchesWorld mainRequest) :
    ∃ born, outcome.kind=.created born ∧
      Prospects.FallbackFissionFusionEmpty Node (ancestry outcome.world) (.birth 0)
        mainParents.left.version mainParents.right.version born
        (EmptyTarget renewable branchesWorld mainRequest) := by
  rw [main_positive_rows] at member
  obtain ⟨pair,_,eq⟩ := List.mem_map.mp member
  have ho := congrArg Prod.fst eq
  cases ho
  exact ⟨.birth (branchesWorld.events.length+2),fusion_birth_from_execution _ _ _ _ _ _,
    original_positive_fusion _ _ _ _ _ _ _ branches_source_ancestry.1 branches_source_ancestry.2⟩

def firstPairRun : Option Pair :=
  (meeting mainParents.rom mainParents.left.current mainParents.right.current false false).head?
theorem first_pair_available : firstPairRun.isSome=true := by decide +kernel
def firstPair : Pair := firstPairRun.get first_pair_available
theorem first_pair_supported :
    firstPair∈meeting mainParents.rom mainParents.left.current mainParents.right.current false false := by
  exact List.mem_of_head? (Option.some_get first_pair_available).symm

def firstProbability : Rat :=
  pairProbability mainParents.rom mainParents.left.current mainParents.right.current false false firstPair
def fused : World := (settle renewable branchesWorld mainRequest mainParents firstPair firstProbability).world

theorem first_output_is_actual :
    (settle renewable branchesWorld mainRequest mainParents firstPair firstProbability,firstProbability)∈
      fusionRows renewable branchesWorld mainRequest := by
  rw [main_positive_rows]
  exact List.mem_map.mpr ⟨firstPair,first_pair_supported,rfl⟩

theorem actual_fusion_readouts :
    fused.residents 1=none ∧ fused.residents 2=none ∧
    (fused.residents 3).map Resident.installed=some (some .canonical32) ∧
    (fused.residents 3).map Resident.receipts=some [] ∧
    (fused.residents 3).map Resident.birthCursor=some 7 ∧
    (fused.residents 3).map Resident.birth=some (.birth 24) ∧
    fused.accounts.custody 1=.local 3 ∧ fused.accounts.custody 2=.local 3 ∧
    fused.accounts.cursor 1=7 ∧ fused.accounts.cursor 2=7 ∧
    fused.accounts.charge 1=true ∧ fused.accounts.charge 2=true ∧ fused.fresh 3=false := by
  decide +kernel

def gapRun : Option World := do
  let staged ← writeSnapshot sourceWorld 0 1 2
  let first ← activate (sourceRetire staged) 1
  activate first 2
theorem destructive_gap_available : gapRun.isSome=true := by decide +kernel

def absentFirst : List (World × Nat) := nativeRows absent (initial 8) 0 false
theorem absent_first_preserved : absentFirst.length=8 ∧
    (∀ e∈absentFirst, e.1.accounts.charge 0=false ∧ nativeRows absent e.1 0 false=[]) := by
  decide +kernel

def probeRequest : FusionRequest := {mainRequest with rightAction := true}
theorem probe_empty_control : (parentView branchesWorld probeRequest).isSome=true ∧
    ((fusionRows renewable branchesWorld probeRequest).map fun e => (e.1.kind,e.2))=
      [(.empty (prospective probeRequest),1)] := by decide +kernel

theorem actual_probe_original_empty :
    Prospects.FallbackFissionFusionEmpty Node (ancestry branchesWorld) (.birth 0)
      mainParents.left.version mainParents.right.version (prospective probeRequest)
      (EmptyTarget renewable branchesWorld probeRequest) :=
  original_empty_fusion renewable branchesWorld probeRequest mainParents
    (by decide +kernel) (by decide +kernel) (.birth 0)
    branches_source_ancestry.1 branches_source_ancestry.2

def phaseRun : Option World := chooseNative renewable branchesWorld 1 false (phaseState true)
theorem phase_run_available : phaseRun.isSome=true := by decide +kernel
def phaseWorld : World := phaseRun.get phase_run_available
def phaseRequestRun : Option FusionRequest := requestFor phaseWorld 1 2 3 false false
theorem phase_request_available : phaseRequestRun.isSome=true := by decide +kernel
def phaseRequest : FusionRequest := phaseRequestRun.get phase_request_available
theorem phase_empty_control : (parentView phaseWorld phaseRequest).isSome=true ∧
    ((fusionRows renewable phaseWorld phaseRequest).map fun e => (e.1.kind,e.2))=
      [(.empty (prospective phaseRequest),1)] := by decide +kernel

theorem unavailable_controls :
    (parentView branchesWorld {mainRequest with right := 1}).isNone=true ∧
    (parentView branchesWorld {mainRequest with output := 1}).isNone=true ∧
    (parentView branchesWorld {mainRequest with output := 8}).isNone=true ∧
    (parentView branchesWorld {mainRequest with leftVersion := .birth 0}).isNone=true := by decide +kernel

def poolRun : Option World := partition fused 3 4 5 [1] [2]
theorem pool_partition_available : poolRun.isSome=true := by decide +kernel
def poolWorld : World := poolRun.get pool_partition_available
def poolRequestRun : Option FusionRequest := requestFor poolWorld 4 5 6 false false
theorem pool_request_available : poolRequestRun.isSome=true := by decide +kernel
def poolRequest : FusionRequest := poolRequestRun.get pool_request_available
theorem pool_refusion_supported : (parentView poolWorld poolRequest).isSome=true ∧
    0<(fusionRows renewable poolWorld poolRequest).length := by decide +kernel

/-- The default positive execution's derived graph is strictly ordered. The
generic acyclicity theorem also applies whenever this computed condition holds. -/
theorem actual_ledgers_ordered :
    (∀ e∈ledgerEdges branchesWorld, nodeRank e.1<nodeRank e.2) ∧
    (∀ e∈ledgerEdges fused, nodeRank e.1<nodeRank e.2) ∧
    (∀ e∈ledgerEdges poolWorld, nodeRank e.1<nodeRank e.2) := by decide +kernel

abbrev ActualMode := Mode FullNative.SnapshotExecution.World World
def mainMode : ActualMode := .fullNative02 branchesWorld

end CSTTT.FullNative02
