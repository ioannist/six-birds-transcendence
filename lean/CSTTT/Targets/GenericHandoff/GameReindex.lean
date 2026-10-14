import CSTTT.Targets.GenericHandoff.GameInvariantCompleteness

/-! Internal strategy-game representation transport. The raw adapter must
prove the coordinate bijection AND the exact row/updater/predicate equations.
No response branch is quotiented or discarded. This is a representation theorem,
not a freely parameterized RawHandoff certificate. -/
namespace CSTTT.TargetTheory.GenericHandoff.StrategyGame

structure RunReindex (X Y : Type) where
  encode : X → Y
  decode : Y → X
  decode_encode : ∀ x, decode (encode x) = x
  encode_decode : ∀ y, encode (decode y) = y

variable {X Y D A O : Type}

def RunReindex.rows (iso : RunReindex X Y) (rows : Rows X D A O) : Rows Y D A O :=
  fun y => rows (iso.decode y)
def RunReindex.update (iso : RunReindex X Y) (next : Updater X D A O) : Updater Y D A O :=
  fun y d a o => iso.encode (next (iso.decode y) d a o)

/-- Exact pullback of every interpretation, including all entry states and
all positive-support responses. -/
def RunReindex.certificate (iso : RunReindex X Y)
    {rows : Rows X D A O} {next : Updater X D A O}
    {entries : X → Prop} {withdrawal : Prop}
    {package resources : X → Prop}
    {legal : X → D → A → Prop} {law : X → D → A → O → Prop}
    (cert : InvariantCertificate rows next entries withdrawal package resources legal law) :
    InvariantCertificate (iso.rows rows) (iso.update next)
      (fun y => entries (iso.decode y)) withdrawal
      (fun y => package (iso.decode y)) (fun y => resources (iso.decode y))
      (fun y => legal (iso.decode y)) (fun y => law (iso.decode y)) where
  inside y := cert.inside (iso.decode y)
  withdrawn := cert.withdrawn
  entriesNonempty := by
    obtain ⟨x,hx⟩ := cert.entriesNonempty
    exact ⟨iso.encode x,by simpa only [iso.decode_encode] using hx⟩
  entriesInside := fun y hy => cert.entriesInside (iso.decode y) hy
  packageInside := fun y hy => cert.packageInside (iso.decode y) hy
  resourcesInside := fun y hy => cert.resourcesInside (iso.decode y) hy
  response y hy d := by
    obtain ⟨a,ha,hn,hs⟩ := cert.response (iso.decode y) hy d
    refine ⟨a,ha,hn,?_⟩
    intro o ho
    have hh := hs o ho
    simpa only [RunReindex.update,iso.decode_encode] using hh

theorem RunReindex.soundness (iso : RunReindex X Y)
    {rows : Rows X D A O} {next : Updater X D A O}
    {entries : X → Prop} {withdrawal : Prop}
    {package resources : X → Prop}
    {legal : X → D → A → Prop} {law : X → D → A → O → Prop}
    (h : GameReadout rows next entries withdrawal package resources legal law) :
    GameReadout (iso.rows rows) (iso.update next)
      (fun y => entries (iso.decode y)) withdrawal
      (fun y => package (iso.decode y)) (fun y => resources (iso.decode y))
      (fun y => legal (iso.decode y)) (fun y => law (iso.decode y)) := by
  obtain ⟨cert⟩ := game_invariant_completeness h
  exact invariant_game_soundness _ _ _ _ _ _ _ _ (iso.certificate cert)

def RunReindex.inverse (iso : RunReindex X Y) : RunReindex Y X :=
  ⟨iso.decode,iso.encode,iso.encode_decode,iso.decode_encode⟩

theorem RunReindex.game_iff (iso : RunReindex X Y)
    {rows : Rows X D A O} {next : Updater X D A O}
    {entries : X → Prop} {withdrawal : Prop}
    {package resources : X → Prop}
    {legal : X → D → A → Prop} {law : X → D → A → O → Prop} :
    GameReadout (iso.rows rows) (iso.update next)
      (fun y => entries (iso.decode y)) withdrawal
      (fun y => package (iso.decode y)) (fun y => resources (iso.decode y))
      (fun y => legal (iso.decode y)) (fun y => law (iso.decode y)) ↔
    GameReadout rows next entries withdrawal package resources legal law := by
  constructor
  · intro h
    have hh := iso.inverse.soundness h
    have hr : iso.inverse.rows (iso.rows rows) = rows := by
      funext x d a
      exact congrArg (fun x => rows x d a) (iso.decode_encode x)
    have hn : iso.inverse.update (iso.update next) = next := by
      funext x d a o
      change iso.decode (iso.encode (next (iso.decode (iso.encode x)) d a o)) = next x d a o
      rw [iso.decode_encode,iso.decode_encode]
    rw [hr,hn] at hh
    simpa only [RunReindex.inverse,iso.decode_encode] using hh
  · exact iso.soundness

end CSTTT.TargetTheory.GenericHandoff.StrategyGame
