import CSTTT.POS04.Data
import CSTTT.Targets.GenericHandoff.NativeComposition.Factor

/-!
Paper-support numeric pins for existing, frozen model definitions. These are
not registry evidence and introduce no model data or alternative enumerations.
The POS-04 ambient enumeration includes the two exits omitted from TaggedState.
-/

namespace CSTTT.PaperSupport

theorem pos04_tagged_ambient_count :
    (POS04.tags.flatMap (fun tag =>
      POS04.ambientStates.map (fun s => (tag, s)))).length = 24 := by
  decide

theorem pos04_tagged_lethal_count :
    (POS04.tags.flatMap (fun tag =>
      (POS04.ambientStates.filter POS04.isLethalHazard).map
        (fun s => (tag, s)))).length = 4 := by
  decide

theorem pos04_c1_epsilon : POS04.c1Epsilon = (1 / 16 : Rat) := by
  rfl

theorem g7_native_factor_count :
    TargetTheory.GenericHandoff.NativeComposition.factors.length = 8 := by
  decide

end CSTTT.PaperSupport
