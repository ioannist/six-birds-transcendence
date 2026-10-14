import CSTTT.FullNative02.Transport

namespace CSTTT.FullNative02
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 8192

def missingProgram : World := {branchesWorld with
  residents := put branchesWorld.residents 1
    ((branchesWorld.residents 1).map fun r => {r with installed := none})}
def unequalProgram : World := {branchesWorld with
  residents := put branchesWorld.residents 2
    ((branchesWorld.residents 2).map fun r => {r with installed := some .flat32})}
def wrongCustody : World := {branchesWorld with accounts :=
  {branchesWorld.accounts with custody := put branchesWorld.accounts.custody 1 .external}}
def aliasedCustody : World := {branchesWorld with accounts :=
  {branchesWorld.accounts with custody := put branchesWorld.accounts.custody 2 (.local 1)}}
def disabledKey : World := {branchesWorld with accounts :=
  {branchesWorld.accounts with charge := put branchesWorld.accounts.charge 1 false}}

theorem actual_account_program_rejections :
    (parentView missingProgram mainRequest).isNone=true ∧
    (parentView unequalProgram mainRequest).isNone=true ∧
    (parentView wrongCustody mainRequest).isNone=true ∧
    (parentView aliasedCustody mainRequest).isNone=true ∧
    (parentView disabledKey mainRequest).isNone=true := by decide +kernel

def unequalBootRun : Option World := do
  let left ← boot (initial 8) 1 1 .canonical32
  boot left 2 2 .flat32
theorem unequal_boot_available : unequalBootRun.isSome=true := by decide +kernel
def unequalBootWorld : World := unequalBootRun.get unequal_boot_available
def unequalBootRequestRun : Option FusionRequest := requestFor unequalBootWorld 1 2 3 false false
theorem unequal_boot_request_available : unequalBootRequestRun.isSome=true := by decide +kernel
def unequalBootRequest : FusionRequest := unequalBootRequestRun.get unequal_boot_request_available
theorem genuine_unequal_rom_rejection :
    (access unequalBootWorld 1).isSome=true ∧ (access unequalBootWorld 2).isSome=true ∧
    (parentView unequalBootWorld unequalBootRequest).isNone=true := by decide +kernel

def forgedVersion : World := {branchesWorld with
  residents := put branchesWorld.residents 1
    ((branchesWorld.residents 1).map fun r => {r with version := .version 999})}
theorem forged_version_rejected :
    (parentView forgedVersion {mainRequest with leftVersion := .version 999}).isNone=true := by decide +kernel

theorem conditional_native_probability_difference :
    firstProbability=(1/40 : Rat) ∧ (firstPair.1.weight : Rat)/16=(1/16 : Rat) ∧
    firstProbability≠(firstPair.1.weight : Rat)/16 := by decide +kernel

theorem spent_capability_and_split_rejections :
    (parentView fused {mainRequest with output := 3}).isNone=true ∧
    (partition fused 3 4 5 [] [1,2]).isNone=true ∧
    (partition fused 3 4 5 [1] [1,2]).isNone=true ∧
    (partition fused 3 4 4 [1] [2]).isNone=true := by decide +kernel

def stageRun : Option World := writeSnapshot sourceWorld 0 1 2
theorem stage_available : stageRun.isSome=true := by decide +kernel
def stageWorld : World := stageRun.get stage_available
def malformedCapture : World := {stageWorld with
  slots := put stageWorld.slots 1
    ((stageWorld.slots 1).map fun slot => {slot with capture := {slot.capture with count := 99}})}
def aliasedSlot : World := {stageWorld with
  slots := put stageWorld.slots 2 ((stageWorld.slots 2).map fun slot => {slot with key := 1})}
theorem actual_capture_rejections :
    (activate malformedCapture 1).isNone=true ∧
    (writeSnapshot (initial 8) 0 1 2).isNone=true ∧
    (boot stageWorld 1 1 .canonical32).isNone=true := by decide +kernel

theorem aliased_reservation_rejected : (activate aliasedSlot 2).isNone=true := by decide +kernel

def twinRun : Option World := do
  let newborn ← boot sourceWorld 1 1 .canonical32
  runChoices renewable newborn 1 sixCycle
theorem twin_available : twinRun.isSome=true := by decide +kernel
def twinWorld : World := twinRun.get twin_available

theorem hardware_never_target (w : World) (address : Nat) :
    ∀ e∈ledgerEdges w, e.2≠Node.hardware address := by
  suffices ∀ es start, ∀ e∈ledgerEdgesFrom start es, e.2≠Node.hardware address from this w.events 0
  intro es
  induction es with
  | nil => simp [ledgerEdgesFrom]
  | cons event rest ih =>
    intro start edge member
    simp only [ledgerEdgesFrom,List.mem_append] at member
    rcases member with first | remaining
    · have direct : ∀ e∈eventEdges start event, e.2≠Node.hardware address := by
        cases event <;> simp [eventEdges]
      exact direct edge first
    · exact ih (start+1) edge remaining

theorem no_ancestry_to_hardware (w : World) (source : Node) (address : Nat) :
    ¬ancestry w source (.hardware address) := by
  intro h
  rcases no_ex_nihilo w source (.hardware address) h with edge | ⟨p,_,edge⟩
  · exact hardware_never_target w address _ edge rfl
  · exact hardware_never_target w address _ edge rfl

theorem twin_no_source_ancestry : ¬ancestry twinWorld (.birth 0) (.birth 7) := by
  have only : ∀ e∈ledgerEdges twinWorld, e.2=Node.birth 7 → e.1=Node.hardware 1 := by decide +kernel
  intro h
  rcases no_ex_nihilo twinWorld (.birth 0) (.birth 7) h with edge | ⟨p,previous,edge⟩
  · have impossible := only _ edge rfl
    cases impossible
  · have hp := only _ edge rfl
    have hp' : p=Node.hardware 1 := hp
    rw [hp'] at previous
    exact no_ancestry_to_hardware twinWorld (.birth 0) 1 previous

theorem twin_native_structure :
    (twinWorld.residents 1).map (fun r => (r.installed,r.current,r.receipts.length))=
      (sourceWorld.residents 0).map (fun r => (r.installed,r.current,r.receipts.length)) := by decide +kernel

def tokenZeroRun : Option World := do
  let copied ← bootstrap sourceWorld 0 1 2
  let left ← runChoices renewable copied 1 sixCycle
  runChoices renewable left 2 sixCycle
theorem token_zero_run_available : tokenZeroRun.isSome=true := by decide +kernel
def tokenZeroWorld : World := tokenZeroRun.get token_zero_run_available
def tokenZeroRequestRun : Option FusionRequest := requestFor tokenZeroWorld 0 1 3 false false
theorem token_zero_request_available : tokenZeroRequestRun.isSome=true := by decide +kernel
def tokenZeroRequest : FusionRequest := tokenZeroRequestRun.get token_zero_request_available
theorem token_zero_view_available : (parentView tokenZeroWorld tokenZeroRequest).isSome=true := by decide +kernel
def tokenZeroParents : Parents := (parentView tokenZeroWorld tokenZeroRequest).get token_zero_view_available
def tokenZeroPairRun : Option Pair :=
  (meeting tokenZeroParents.rom tokenZeroParents.left.current tokenZeroParents.right.current false false).head?
theorem token_zero_pair_available : tokenZeroPairRun.isSome=true := by decide +kernel
def tokenZeroPair : Pair := tokenZeroPairRun.get token_zero_pair_available
def tokenZeroFused : World :=
  (settle renewable tokenZeroWorld tokenZeroRequest tokenZeroParents tokenZeroPair
    (pairProbability tokenZeroParents.rom tokenZeroParents.left.current tokenZeroParents.right.current false false tokenZeroPair)).world
theorem transferred_token_zero_survives :
    tokenZeroParents.outputKey=0 ∧ (withdraw tokenZeroFused).accounts.custody 0=.local 3 ∧
    (withdraw tokenZeroFused).accounts.cursor 0=7 ∧ (withdraw tokenZeroFused).accounts.charge 0=true ∧
    (access (withdraw tokenZeroFused) 3).isSome=true := by decide +kernel

end CSTTT.FullNative02
