import CSTTT.Fallback.OperationalSeed

namespace CSTTT.FallbackTheory.NativeDescendant
open CSTTT.TransportTheory
open CSTTT.FallbackTheory.OperationalTrace
open CSTTT.FallbackTheory.SharedOperationalSeed
variable {H S T E R SC TC RR M : Type} [DecidableEq S]
-- Class (b): primitive proposed native step or exact copied fission; no edge, ancestry or final verdict input.
inductive Command (T : Type) where
  | advance (parent target action : Nat) (outcome : T)
  | fission (parent left right : Nat)
-- Class (b): derived write result with actual target payload, generated graph edge and retained capture journal.
def advanced (store : Store S T) (parent target : Nat) (outcome : T) : Store S T :=
  ⟨put store.read target (.target outcome),switch store.active target true,
    (parent,target)::store.edges,store.clock+1,store.captured⟩
-- Class (b): both copies are generated from the actual read parent payload; none is a supplied derived snapshot.
def split (store : Store S T) (parent left right : Nat) (payload : T) : Store S T :=
  ⟨put (put store.read left (.target payload)) right (.target payload),
    switch (switch store.active left true) right true,
    (parent,left)::(parent,right)::store.edges,store.clock+1,store.captured⟩
-- Class (b): native row support and fresh actor outputs implement transition/fission admissibility, not a supplied guard Bool.
def step (b : RawBridge H S T E R SC TC RR M) (store : Store S T) : Command T → Option (Store S T)
  | .advance parent target action outcome => do
      let .target payload ← store.read parent | none
      if store.active parent && (store.read target).isNone && decide (0<b.targetActionStep payload action outcome) then
        some (advanced store parent target outcome)
      else none
  | .fission parent left right => do
      let .target payload ← store.read parent | none
      if store.active parent && (store.read left).isNone && (store.read right).isNone && decide (left≠right) then
        some (split store parent left right payload)
      else none
-- Class (b): actual extension propagates failure and never accepts externally supplied edges or stores as raw campaign fields.
def run (b : RawBridge H S T E R SC TC RR M) : Store S T → List (Command T) → Option (Store S T)
  | store,[] => some store
  | store,command::rest => (step b store command).bind (fun next => run b next rest)
-- Class (b): campaign extension consumes the SAME source-checked raw prefix execution, with no supplied world snapshot.
def extendActual (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (Command T)) : Option (Store S T) :=
  (computedStore inputs).bind (fun store => run b store commands)
-- Class (b): actual failed prefix rejects all subsequent command streams on every partial raw assignment.
theorem missing_prefix_rejects (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (Command T)) (failed : computedStore inputs=none) : extendActual b inputs commands=none := by
  simp [extendActual,failed]
-- Class (b): exact every-partial native step presence, including typed read, activity, output freshness and actual supported raw row.
theorem advance_present_iff (b : RawBridge H S T E R SC TC RR M) (store : Store S T)
    (parent target action : Nat) (outcome : T) :
    (step b store (.advance parent target action outcome)).isSome ↔ ∃ payload,
      store.read parent=some (.target payload) ∧ store.active parent=true ∧ store.read target=none ∧
      0<b.targetActionStep payload action outcome := by
  cases read : store.read parent with
  | none => simp [step,read]
  | some content =>
    cases content with
    | source payload => simp [step,read]
    | record origin time payload => simp [step,read]
    | target payload => simp [step,read,and_assoc]
-- Class (b): exact every-partial fission presence; same payload alone never bypasses actual typed parent and fresh distinct outputs.
theorem fission_present_iff (b : RawBridge H S T E R SC TC RR M) (store : Store S T)
    (parent left right : Nat) : (step b store (.fission parent left right)).isSome ↔ ∃ payload,
      store.read parent=some (.target payload) ∧ store.active parent=true ∧ store.read left=none ∧
      store.read right=none ∧ left≠right := by
  cases read : store.read parent with
  | none => simp [step,read]
  | some content =>
    cases content with
    | source payload => simp [step,read]
    | record origin time payload => simp [step,read]
    | target payload => simp [step,read,and_assoc]
-- Class (b): an unsupported actual target row rejects the actual native advance readout directly.
theorem unsupported_advance_rejects (b : RawBridge H S T E R SC TC RR M) (store : Store S T)
    (parent target action : Nat) (payload outcome : T) (read : store.read parent=some (.target payload))
    (unsupported : b.targetActionStep payload action outcome=0) :
    step b store (.advance parent target action outcome)=none := by simp [step,read,unsupported]
-- Class (b): paths persist when generated actual edge lists retain all previous edges.
theorem path_inclusion (old new : List (Nat × Nat)) (included : ∀ edge, edge∈old → edge∈new)
    (source target : Nat) (path : Path old source target) : Path new source target := by
  induction path with
  | one member => exact .one (included _ member)
  | extend previous member ih => exact .extend ih (included _ member)
-- Class (b): every actual native advance extends operational ancestry through its generated predecessor edge.
theorem advance_ancestry (store : Store S T) (source parent target : Nat) (outcome : T)
    (path : Path store.edges source parent) : Path (advanced store parent target outcome).edges source target := by
  exact .extend (path_inclusion _ _ (fun edge member => List.mem_cons_of_mem _ member) _ _ path) (by simp [advanced])
-- Class (b): both source-derived actual fission targets inherit ancestry, with no unique-identity selector conclusion.
theorem fission_ancestry (store : Store S T) (source parent left right : Nat) (payload : T)
    (path : Path store.edges source parent) :
    Path (split store parent left right payload).edges source left ∧
    Path (split store parent left right payload).edges source right := by
  have retained := path_inclusion store.edges (split store parent left right payload).edges
    (fun edge member => by simp [split,member]) source parent path
  exact ⟨.extend retained (by simp [split]),.extend retained (by simp [split])⟩
-- Class (b): supported fission returns exactly equal payloads and both active targets, while retaining the original journal.
theorem fission_equal_readouts (store : Store S T) (parent left right : Nat) (payload : T) (distinct : left≠right) :
    (split store parent left right payload).read left=some (.target payload) ∧
    (split store parent left right payload).read right=some (.target payload) ∧
    (split store parent left right payload).active left=true ∧
    (split store parent left right payload).active right=true ∧
    (split store parent left right payload).captured=store.captured := by
  simp [split,put,switch,distinct]

-- Class (b): primitive row support and read/freshness conditions calculate the actual advance execution result.
theorem advance_exact (b : RawBridge H S T E R SC TC RR M) (store : Store S T)
    (parent target action : Nat) (payload outcome : T) (read : store.read parent=some (.target payload))
    (active : store.active parent=true) (fresh : store.read target=none)
    (supported : 0<b.targetActionStep payload action outcome) :
    step b store (.advance parent target action outcome)=some (advanced store parent target outcome) := by
  simp [step,read,active,fresh,supported]
-- Class (b): typed read/activity and distinct fresh slots calculate the actual two-copy result.
theorem fission_exact (b : RawBridge H S T E R SC TC RR M) (store : Store S T)
    (parent left right : Nat) (payload : T) (read : store.read parent=some (.target payload))
    (active : store.active parent=true) (freshLeft : store.read left=none) (freshRight : store.read right=none)
    (distinct : left≠right) : step b store (.fission parent left right)=some (split store parent left right payload) := by
  simp [step,read,active,freshLeft,freshRight,distinct]
-- Class (b): successful actual advance yields a supported native row, derived ancestry and actual active target payload.
theorem actual_advance_return (b : RawBridge H S T E R SC TC RR M) (store finished : Store S T)
    (source parent target action : Nat) (outcome : T) (path : Path store.edges source parent)
    (executed : step b store (.advance parent target action outcome)=some finished) :
    (∃ payload,store.read parent=some (.target payload) ∧ 0<b.targetActionStep payload action outcome) ∧
    Path finished.edges source target ∧ finished.read target=some (.target outcome) ∧
    finished.active target=true ∧ finished.captured=store.captured := by
  have presence : (step b store (.advance parent target action outcome)).isSome := by rw [executed]; rfl
  obtain ⟨payload,read,active,fresh,supported⟩ := (advance_present_iff b store parent target action outcome).mp presence
  have equality := Option.some.inj ((advance_exact b store parent target action payload outcome read active fresh supported).symm.trans executed)
  rw [← equality]
  exact ⟨⟨payload,read,supported⟩,advance_ancestry store source parent target outcome path,by simp [advanced,put],
    by simp [advanced,switch],rfl⟩
-- Class (b): actual successful fission returns both source-derived branches with equal actual payloads and both activity bits.
theorem actual_fission_return (b : RawBridge H S T E R SC TC RR M) (store finished : Store S T)
    (source parent left right : Nat) (path : Path store.edges source parent)
    (executed : step b store (.fission parent left right)=some finished) :
    Path finished.edges source left ∧ Path finished.edges source right ∧
    finished.read left=finished.read right ∧ finished.active left=true ∧ finished.active right=true ∧
    finished.captured=store.captured := by
  have presence : (step b store (.fission parent left right)).isSome := by rw [executed]; rfl
  obtain ⟨payload,read,active,freshLeft,freshRight,distinct⟩ := (fission_present_iff b store parent left right).mp presence
  have equality := Option.some.inj ((fission_exact b store parent left right payload read active freshLeft freshRight distinct).symm.trans executed)
  rw [← equality]
  obtain ⟨leftPath,rightPath⟩ := fission_ancestry store source parent left right payload path
  obtain ⟨leftRead,rightRead,leftActive,rightActive,journal⟩ := fission_equal_readouts store parent left right payload distinct
  exact ⟨leftPath,rightPath,leftRead.trans rightRead.symm,leftActive,rightActive,journal⟩
-- Class (b): supported advance is returned by the actual shared raw prefix plus one extension command.
theorem actual_prefix_advance (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T) (store : Store S T)
    (computed : computedStore inputs=some store) (parent target action : Nat) (payload outcome : T)
    (read : store.read parent=some (.target payload)) (active : store.active parent=true)
    (fresh : store.read target=none) (supported : 0<b.targetActionStep payload action outcome) :
    extendActual b inputs [.advance parent target action outcome]=some (advanced store parent target outcome) := by
  simp [extendActual,computed,run,advance_exact b store parent target action payload outcome read active fresh supported]
-- Class (b): both copied branches are returned by the actual shared raw prefix plus one fission command.
theorem actual_prefix_fission (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T) (store : Store S T)
    (computed : computedStore inputs=some store) (parent left right : Nat) (payload : T)
    (read : store.read parent=some (.target payload)) (active : store.active parent=true)
    (freshLeft : store.read left=none) (freshRight : store.read right=none) (distinct : left≠right) :
    extendActual b inputs [.fission parent left right]=some (split store parent left right payload) := by
  simp [extendActual,computed,run,fission_exact b store parent left right payload read active freshLeft freshRight distinct]

-- Class (b): an actual occupied address cannot pass the primitive fresh-slot check.
theorem occupied_not_fresh {A : Type} (read : Nat → Option A) (key fresh : Nat) (value : A)
    (occupied : read key=some value) (available : read fresh=none) : key≠fresh := by
  intro equal
  subst fresh
  rw [occupied] at available
  cases available
-- Class (b): every actual successful primitive preserves an occupied disconnected boundary, using its own freshness checks.
theorem occupied_boundary_retained (b : RawBridge H S T E R SC TC RR M) (store finished : Store S T)
    (command : Command T) (key : Nat) (content : Content S T) (occupied : store.read key=some content)
    (missing : ∀ predecessor,(predecessor,key)∉store.edges) (executed : step b store command=some finished) :
    finished.read key=some content ∧ ∀ predecessor,(predecessor,key)∉finished.edges := by
  cases command with
  | advance parent target action outcome =>
    have presence : (step b store (.advance parent target action outcome)).isSome := by rw [executed]; rfl
    obtain ⟨payload,read,active,fresh,supported⟩ := (advance_present_iff b store parent target action outcome).mp presence
    have equality := Option.some.inj ((advance_exact b store parent target action payload outcome read active fresh supported).symm.trans executed)
    rw [← equality]
    have distinct := occupied_not_fresh store.read key target content occupied fresh
    refine ⟨by simp [advanced,put,distinct,occupied],?_⟩
    intro predecessor
    simpa [advanced,distinct] using missing predecessor
  | fission parent left right =>
    have presence : (step b store (.fission parent left right)).isSome := by rw [executed]; rfl
    obtain ⟨payload,read,active,freshLeft,freshRight,distinct⟩ := (fission_present_iff b store parent left right).mp presence
    have equality := Option.some.inj ((fission_exact b store parent left right payload read active freshLeft freshRight distinct).symm.trans executed)
    rw [← equality]
    have keyLeft := occupied_not_fresh store.read key left content occupied freshLeft
    have keyRight := occupied_not_fresh store.read key right content occupied freshRight
    refine ⟨by simp [split,put,keyLeft,keyRight,occupied],?_⟩
    intro predecessor
    simpa [split,keyLeft,keyRight] using missing predecessor
-- Class (b): every finite actual extension retains the disconnected occupied boundary, independently of raw command choices.
theorem run_boundary_retained (b : RawBridge H S T E R SC TC RR M) (commands : List (Command T))
    (store finished : Store S T) (key : Nat) (content : Content S T) (occupied : store.read key=some content)
    (missing : ∀ predecessor,(predecessor,key)∉store.edges) (executed : run b store commands=some finished) :
    finished.read key=some content ∧ ∀ predecessor,(predecessor,key)∉finished.edges := by
  induction commands generalizing store with
  | nil =>
    have equal : store=finished := Option.some.inj executed
    exact equal ▸ ⟨occupied,missing⟩
  | cons command rest ih =>
    cases stepResult : step b store command with
    | none => simp [run,stepResult] at executed
    | some next =>
      have boundary := occupied_boundary_retained b store next command key content occupied missing stepResult
      apply ih next boundary.1 boundary.2
      simpa [run,stepResult] using executed
-- Class (b): an actually disconnected initialized twin remains excluded from every source after every successful native extension.
theorem actual_twin_extension_excluded (b : RawBridge H S T E R SC TC RR M) (inputs : RawInputs S T)
    (commands : List (Command T)) (store finished : Store S T) (computed : computedStore inputs=some store)
    (twin : Nat) (rawTwin : T) (occupied : store.read twin=some (.target rawTwin))
    (missing : ∀ predecessor,(predecessor,twin)∉store.edges)
    (executed : extendActual b inputs commands=some finished) :
    finished.read twin=some (.target rawTwin) ∧ ∀ source,¬ Path finished.edges source twin := by
  have extension : run b store commands=some finished := by simpa [extendActual,computed] using executed
  have boundary := run_boundary_retained b commands store finished twin (.target rawTwin) occupied missing extension
  exact ⟨boundary.1,no_incoming_excludes finished.edges twin boundary.2⟩
end CSTTT.FallbackTheory.NativeDescendant
