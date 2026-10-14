import CSTTT.FullNative02.ProtocolReturn
import CSTTT.FullNative02.Transfer
import CSTTT.FullNative02.PartitionReadouts

namespace CSTTT.FullNative02
set_option autoImplicit false

inductive Command where
  | native (owner : Nat) (action : Bool)
  | snapshot (source left right : Nat)
  | activation (address : Nat)
  | partition (parent left right : Nat) (xs ys : List Token)
  | boot (address : Nat) (key : Token) (rom : ROM)
  | fusion (request : FusionRequest)
  | retire | withdraw

def deterministicRows (result : Option World) : List (World × Rat) :=
  result.toList.map fun w => (w,1)

def protocolRows (supply : Supply) (w : World) : Command → List (World × Rat)
  | .native a action => normalizedNative supply w a action
  | .snapshot source left right => deterministicRows (writeSnapshot w source left right)
  | .activation a => deterministicRows (activate w a)
  | .partition parent left right xs ys => deterministicRows (partition w parent left right xs ys)
  | .boot a key rom => deterministicRows (boot w a key rom)
  | .fusion q => (fusionRows supply w q).map fun e => (e.1.world,e.2)
  | .retire => [(sourceRetire w,1)]
  | .withdraw => [(withdraw w,1)]

def installedProtocolRows (supply : Supply) (w : ActualMode) (command : Command) :
    List (ActualMode × Rat) :=
  match w with
  | .legacy _ => []
  | .fullNative02 current => (protocolRows supply current command).map fun e => (.fullNative02 e.1,e.2)

theorem installed_protocol_rejects_legacy (supply : Supply)
    (w : FullNative.SnapshotExecution.World) (command : Command) :
    installedProtocolRows supply (.legacy w) command=[] := rfl

theorem deterministic_support (result : Option World) (w : World) (probability : Rat)
    (member : (w,probability)∈deterministicRows result) : result=some w ∧ probability=1 := by
  cases result with
  | none => simp [deterministicRows] at member
  | some v =>
    simp only [deterministicRows,Option.toList_some,List.map_cons,List.map_nil,
      List.mem_cons,List.not_mem_nil,or_false,Prod.mk.injEq] at member
    cases member.1
    exact ⟨rfl,member.2⟩

theorem protocol_support_is_history_step (supply : Supply) (w v : World) (command : Command)
    (probability : Rat) (member : (v,probability)∈protocolRows supply w command) : Step supply w v := by
  cases command with
  | native a action =>
    obtain ⟨e,he,eq⟩ := List.mem_map.mp member
    cases eq
    exact .native he
  | snapshot source left right => exact .snapshot (deterministic_support _ _ _ member).1
  | activation address => exact .activation (deterministic_support _ _ _ member).1
  | partition parent left right xs ys => exact .partition (deterministic_support _ _ _ member).1
  | boot address key rom => exact .boot (deterministic_support _ _ _ member).1
  | fusion q =>
    obtain ⟨e,he,eq⟩ := List.mem_map.mp member
    cases eq
    exact .fusion he
  | retire => cases List.mem_singleton.mp member; exact .retire w
  | withdraw => cases List.mem_singleton.mp member; exact .withdraw w

/-- All positive branches of the actual protocol interpreter preserve the
general history, ledger and resource inventory invariants. -/
theorem all_protocol_histories (supply : Supply) (inventory : Nat) (rom : ROM)
    (w v : World) (history : History supply inventory rom w) (command : Command)
    (probability : Rat) (member : (v,probability)∈protocolRows supply w command) :
    History supply inventory rom v ∧ Ordered v ∧ Housed v ∧
      v.inventory=inventory ∧ (∀ a, w.fresh a=false → v.fresh a=false) ∧
      (∀ x y, ancestry w x y → ancestry v x y) := by
  have step := protocol_support_is_history_step supply w v command probability member
  have next := History.next history step
  have invariants := history_invariants supply inventory rom v next
  exact ⟨next,invariants.2,all_history_accounts_housed _ _ _ _ next,
    invariants.1.1,
    fun a spent => consumed_capability_never_returns _ _ _ step
      (history_invariants _ _ _ _ history).2 a spent,
    fun x y path => footprint_ancestry _ _
      (step_invariants _ _ _ step (history_invariants _ _ _ _ history).2).1 x y path⟩

end CSTTT.FullNative02
