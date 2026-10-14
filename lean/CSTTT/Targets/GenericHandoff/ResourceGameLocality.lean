import CSTTT.Targets.GenericHandoff.ResourceRuntime

/-! Resource game locality on the raw instruction dependency scope.
Row equality is deliberately not required: legality and step expenditure do
not inspect the response table. Supported response transport is a separate law. -/
namespace CSTTT.TargetTheory.GenericHandoff.ResourceRuntime
open RegisterInterpreter
variable {Cell R D A O Factor Resource Residue : Type}
  {Value : Cell → Type} {RV : R → Type}

theorem read_locality (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    {a b : Assignment Cell Value} (he : Agrees raw.readDependencies a b)
    {Env X : Type} (e : Expr Cell Value R RV Env X) (hd : e.dependencies ⊆ raw.readDependencies) :
    e.eval a = e.eval b := by
  funext r env
  exact e.locality (fun k hk => he k (hd hk)) r env

theorem inside_locality (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    {a b : Assignment Cell Value} (he : Agrees raw.readDependencies a b) (r : Registers R RV) :
    Inside cfg raw a r ↔ Inside cfg raw b r := by
  have hf := read_locality raw he raw.factor (by intro k hk; simp [Raw.readDependencies,hk])
  have hfr := congrFun (congrFun hf r) ()
  simp only [Inside,hfr]

theorem legal_locality (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    {a b : Assignment Cell Value} (he : Agrees raw.readDependencies a b)
    (r : Registers R RV) (d : D) (act : A) : Legal cfg raw a r d act ↔ Legal cfg raw b r d act := by
  have ha := read_locality raw he raw.accounts (by intro k hk; simp [Raw.readDependencies,hk])
  have hn := read_locality raw he raw.required (by intro k hk; simp [Raw.readDependencies,hk])
  have hc := read_locality raw he raw.charge (by intro k hk; simp [Raw.readDependencies,hk])
  have hw := view_locality raw.withdrawal (he _ (by simp [Raw.readDependencies]))
  have har := congrFun (congrFun ha r) ()
  have hnr := congrFun (congrFun hn r) ()
  have hcr := congrFun (congrFun hc r) (d,act)
  simp only [Legal,har,hnr,hcr,hw]

theorem step_locality (cfg : Schema Factor Resource)
    (raw : Raw Cell Value R RV D A O Factor Resource Residue)
    {a b : Assignment Cell Value} (ha : Ready raw a) (hb : Ready raw b)
    (he : Agrees raw.readDependencies a b)
    (hp : ∀ reg, Agrees (raw.execution.program reg).dependencies a b)
    (r : Registers R RV) (d : D) (act : A) (o : O) :
    StepLaw cfg raw a ha r d act o ↔ StepLaw cfg raw b hb r d act o := by
  have hu := update_locality raw ha hb hp r d act o
  have hac := read_locality raw he raw.accounts (by intro k hk; simp [Raw.readDependencies,hk])
  have hc := read_locality raw he raw.charge (by intro k hk; simp [Raw.readDependencies,hk])
  have hd := read_locality raw he raw.advances (by intro k hk; simp [Raw.readDependencies,hk])
  have ho := read_locality raw he raw.order (by intro k hk; simp [Raw.readDependencies,hk])
  have ht := read_locality raw he raw.ticks (by intro k hk; simp [Raw.readDependencies,hk])
  have hg := read_locality raw he raw.progress (by intro k hk; simp [Raw.readDependencies,hk])
  have hr := read_locality raw he raw.record (by intro k hk; simp [Raw.readDependencies,hk])
  have hs := read_locality raw he raw.residue (by intro k hk; simp [Raw.readDependencies,hk])
  have haccounts (run : Registers R RV) := congrFun (congrFun hac run) ()
  have hcharge := congrFun (congrFun hc r) (d,act)
  have hadvance := congrFun (congrFun hd r) (d,act,o)
  have horder (run : Registers R RV) := congrFun (congrFun ho run) ()
  have hticks (run : Registers R RV) := congrFun (congrFun ht run) ()
  have hprogress (run : Registers R RV) := congrFun (congrFun hg run) ()
  have hrecord (run : Registers R RV) := congrFun (congrFun hr run) ()
  have hresidue (run : Registers R RV) := congrFun (congrFun hs run) ()
  simp only [StepLaw,hu,resource_locality cfg raw he,haccounts,hcharge,hadvance,horder,hticks,hprogress,hrecord,hresidue]

end CSTTT.TargetTheory.GenericHandoff.ResourceRuntime
