import CSTTT.POS04.Assigned.C457Adapters

/-! Method-level single-cell/subfield sensitivity probes. These are not new
scientific model declarations. C4/C5/C7 stay at the declared surrogate grades. -/
namespace CSTTT.POS04.Assigned
open CSTTT.Objecthood.T1Audit

theorem c4_missing_rejected (a : Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c4) : ¬ C4Accept (put a k none) tag := by
  intro h; exact missing_cell_rejected _ a k hk h.1.1.1

theorem c5_missing_rejected (a : Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c5) : ¬ C5Accept (put a k none) tag := by
  intro h; exact missing_cell_rejected _ a k hk h.1.1

theorem c7_missing_rejected (a : Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c7) : ¬ C7Accept (put a k none) tag := by
  intro h; exact missing_cell_rejected _ a k hk h.1.1.1

/-- Shared raw histories feed all three clauses. No empty path can certify a
connector, an anchored generator or an admissible assemblage history. -/
def emptyHistories (a : Assignment) := put a .histories (some (fun _ => []))

theorem c4_histories_guard (tag : Tag) : ¬ C4Accept (emptyHistories canonical) tag := by
  intro h
  have he := h.1.2.2.1
  cases tag <;> change none = some KState.p1w0 at he <;> contradiction

theorem c5_histories_guard (tag : Tag) : ¬ C5Accept (emptyHistories canonical) tag := by
  intro h
  have hn : historySupported (clauseExtra (emptyHistories canonical) tag .c5) .repA ≠ true := by
    cases tag <;> decide
  exact hn (h.2.2.2.2.2.2 .u (by decide))

theorem c7_histories_guard (tag : Tag) : ¬ C7Accept (emptyHistories canonical) tag := by
  intro h
  have hn : historySupported (clauseExtra (emptyHistories canonical) tag .c7) .repA ≠ true := by
    cases tag <;> decide
  exact hn (h.2.2.1 .repA (by decide))

def emptyChannels (a : Assignment) := put a .channels (some [])
theorem c4_channels_guard (tag : Tag) : ¬ C4Accept (emptyChannels canonical) tag := by
  intro h
  rcases h.2.2.2 with ⟨c,hc,_⟩
  have he : (clauseExtra (emptyChannels canonical) tag .c4).channels = [] := by
    cases tag <;> rfl
  simp [he] at hc

def emptyEvents (a : Assignment) := put a .eventTable (some [])
def noRealization (a : Assignment) := put a .realized (some [])
def sourceWithdrawn (a : Assignment) := mapCell a .receiverInput (fun r => {r with sourcePresent := false})
def unfundedReceiver (a : Assignment) := mapCell a .receiverInput (fun r => {r with funded := false})
def unfundedTargetReceiver (a : Assignment) :=
  mapCell a .receiverInput (fun r => {r with targetReceiverFunded := false})

theorem c7_events_guard (tag : Tag) : ¬ C7Accept (emptyEvents canonical) tag := by
  intro h
  have hn : mixed7 (clauseExtra (emptyEvents canonical) tag .c7) ≠ true := by
    cases tag <;> decide
  exact hn h.2.2.2.2.1

theorem c7_realization_guard (tag : Tag) : ¬ C7Accept (noRealization canonical) tag := by
  intro h
  have hn : mixed7 (clauseExtra (noRealization canonical) tag .c7) ≠ true := by
    cases tag <;> decide
  exact hn h.2.2.2.2.1

theorem c7_source_presence_guard (tag : Tag) : ¬ C7Accept (sourceWithdrawn canonical) tag := by
  intro h
  have hn : active7 (clauseExtra (sourceWithdrawn canonical) tag .c7) ≠ true := by
    cases tag <;> decide
  exact hn h.2.2.2.2.2.1

theorem c7_receiver_funding_guard (tag : Tag) : ¬ C7Accept (unfundedReceiver canonical) tag := by
  intro h
  have hn : active7 (clauseExtra (unfundedReceiver canonical) tag .c7) ≠ true := by
    cases tag <;> decide
  exact hn h.2.2.2.2.2.1

theorem c7_target_funding_guard (tag : Tag) : ¬ C7Accept (unfundedTargetReceiver canonical) tag := by
  intro h
  have hn : active7 (clauseExtra (unfundedTargetReceiver canonical) tag .c7) ≠ true := by
    cases tag <;> decide
  exact hn h.2.2.2.2.2.1

/-- Every display is computed from the raw relation; remove one marginal
branch distinction and the two displays become equal. -/
def flatLeft (a : Assignment) (tag : Tag) :=
  mapCell a (.joint tag) (fun j => {j with left := fun _ => .repA})
def flatRight (a : Assignment) (tag : Tag) :=
  mapCell a (.joint tag) (fun j => {j with right := fun _ => .classB})
def flatCoupling (a : Assignment) (tag : Tag) :=
  mapCell a (.joint tag) (fun j => {j with coupling := fun _ => coupling .diagonal})
def flatReassembly (a : Assignment) (tag : Tag) :=
  mapCell a (.joint tag) (fun j => {j with reassembly := fun _ => .diagonal})
def noJointObservable (a : Assignment) (tag : Tag) :=
  mapCell a (.joint tag) (fun j => {j with observables := []})

theorem c7_left_guard (tag : Tag) : ¬ C7Accept (flatLeft canonical tag) tag := by
  intro h
  have he : recombination7 (clauseExtra (flatLeft canonical tag) tag .c7) .diagonal =
      recombination7 (clauseExtra (flatLeft canonical tag) tag .c7) .crossed := by
    cases tag <;> decide
  exact h.2.2.2.1.2.2 he

theorem c7_right_guard (tag : Tag) : ¬ C7Accept (flatRight canonical tag) tag := by
  intro h
  have he : recombination7 (clauseExtra (flatRight canonical tag) tag .c7) .diagonal =
      recombination7 (clauseExtra (flatRight canonical tag) tag .c7) .crossed := by
    cases tag <;> decide
  exact h.2.2.2.1.2.2 he

theorem c7_coupling_guard (tag : Tag) : ¬ C7Accept (flatCoupling canonical tag) tag := by
  intro h
  have he : recombination7 (clauseExtra (flatCoupling canonical tag) tag .c7) .diagonal =
      recombination7 (clauseExtra (flatCoupling canonical tag) tag .c7) .crossed := by
    cases tag <;> decide
  exact h.2.2.2.1.2.2 he

theorem c7_observable_guard (tag : Tag) : ¬ C7Accept (noJointObservable canonical tag) tag := by
  intro h
  have he : recombination7 (clauseExtra (noJointObservable canonical tag) tag .c7) .diagonal =
      recombination7 (clauseExtra (noJointObservable canonical tag) tag .c7) .crossed := by
    cases tag <;> decide
  exact h.2.2.2.1.2.2 he

theorem c7_reassembly_guard (tag : Tag) : ¬ C7Accept (flatReassembly canonical tag) tag := by
  intro h
  have he := (h.2.1 .crossed (by decide)).1
  have hn : (clauseExtra (flatReassembly canonical tag) tag .c7).joint.coupling .crossed ≠
      coupling ((clauseExtra (flatReassembly canonical tag) tag .c7).joint.reassembly .crossed) := by
    cases tag <;> decide
  exact hn he

def noGenerators (a : Assignment) (tag : Tag) :=
  mapCell a (.protocols tag) (fun p => {p with edges := fun _ => []})
def noGeneratorOwner (a : Assignment) (tag : Tag) :=
  mapCell a (.protocols tag) (fun p => {p with owner := fun _ => .none})
def noTargetHousing (a : Assignment) :=
  mapCell a (.protocols .target) (fun p => {p with housing := fun _ => .none})

theorem c5_edges_guard (tag : Tag) : ¬ C5Accept (noGenerators canonical tag) tag := by
  intro h
  have hn : credit5 (clauseExtra (noGenerators canonical tag) tag .c5) .clockwise ≠ .self := by
    cases tag <;> decide
  exact hn h.2.1

theorem c5_owner_guard (tag : Tag) : ¬ C5Accept (noGeneratorOwner canonical tag) tag := by
  intro h
  have hc : credit5 (clauseExtra (noGeneratorOwner canonical tag) tag .c5) .clockwise = .self := by
    cases tag <;> decide
  have he := ((h.2.2.2.2.2.1 .clockwise (by decide)).1 hc)
  cases tag <;> contradiction

/-- Housing is not a credit input: its guard is the staged raw transport
check, not a fabricated local credit failure. -/
theorem c5_housing_guard : ¬ C5Transport (noTargetHousing canonical) := by
  intro h
  have he := (h.2.2 .clockwise (by decide)).2.2
  have hn : c5TranslateOwner ((clauseExtra (noTargetHousing canonical) .source .c5).protocols.housing .clockwise) ≠
      (clauseExtra (noTargetHousing canonical) .target .c5).protocols.housing .clockwise := by decide
  exact hn he

theorem canonical_future_references (tag : Tag) : FutureReferenceGate canonical tag := by
  refine ⟨canonical_complete _,?_⟩
  rw [canonical_extra]
  cases tag <;> decide

def cappedRoutes (a : Assignment) := mapCell a .routeTable (fun rs => rs.take 1)
def noWriters (a : Assignment) := put a .writers (some (fun _ _ => false))

theorem future_route_table_guard (tag : Tag) : ¬ FutureReferenceGate (cappedRoutes canonical) tag := by
  intro h
  have hn : (routeIds.all fun id =>
    ((clauseExtra (cappedRoutes canonical) tag .c6).routes.any fun r => r.id == id && !r.eventPath.isEmpty &&
      historySupported (clauseExtra (cappedRoutes canonical) tag .c6) r.sourceHistory) &&
    (clauseExtra (cappedRoutes canonical) tag .c6).writers tag id) ≠ true := by
    cases tag <;> decide
  exact hn h.2

theorem future_writer_guard (tag : Tag) : ¬ FutureReferenceGate (noWriters canonical) tag := by
  intro h
  have hn : (routeIds.all fun id =>
    ((clauseExtra (noWriters canonical) tag .c6).routes.any fun r => r.id == id && !r.eventPath.isEmpty &&
      historySupported (clauseExtra (noWriters canonical) tag .c6) r.sourceHistory) &&
    (clauseExtra (noWriters canonical) tag .c6).writers tag id) ≠ true := by
    cases tag <;> decide
  exact hn h.2

/-- A nonempty duplicate-history table also fails: branch records are actual
paths, not independently meaningful history names. -/
def duplicateHistories (a : Assignment) := put a .histories (some (fun _ => [.p1w0]))
theorem c7_duplicate_history_guard (tag : Tag) : ¬ C7Accept (duplicateHistories canonical) tag := by
  intro h
  have hn : ¬ (historyIds.map (clauseExtra (duplicateHistories canonical) tag .c7).histories).Nodup := by
    cases tag <;> decide
  exact hn h.1.2.2

theorem future_reference_missing_rejected (a : Assignment) (tag : Tag) (k : Cell)
    (hk : k ∈ clauseScope tag .c6) : ¬ FutureReferenceGate (put a k none) tag := by
  intro h
  exact missing_cell_rejected _ a k hk h.1

end CSTTT.POS04.Assigned
