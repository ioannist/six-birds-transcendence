import CSTTT.Targets.GenericHandoff.NativeComposition.PublicationFuture
import CSTTT.Transport.SnapshotImages

namespace CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationFuture
open RegisterInterpreter CSTTT.TransportTheory PublicationReplay
abbrev Observation := TemporalSnapshotReadout Frame.Predictive Frame.Residue Bool

def routeImage (r : Frame.Residue) : Frame.Residue := (r.1++r.1,r.2)
theorem route_image_injective : Function.Injective routeImage := by
  intro x y h
  have hf := congrArg (fun r : Frame.Residue => (r.1.take (r.1.length/2),r.2)) h
  simpa only [routeImage,half_double] using hf

/-- Transpose the two actual carrier names. Unlike a constant replacement,
this preserves distinctions on the entire observation alphabet. -/
def ownerImage (cell : Owner) (c : CarrierId) : CarrierId :=
  if c=names cell (swapOwner cell) then names cell cell
  else if c=names cell cell then names cell (swapOwner cell) else c
theorem different_owners (cell : Owner) : names cell (swapOwner cell)≠names cell cell := by
  cases cell <;> decide +kernel
theorem owner_image_source (cell : Owner) : ownerImage cell (names cell (swapOwner cell))=names cell cell := by
  simp [ownerImage]
theorem owner_image_involution (cell : Owner) (c : CarrierId) : ownerImage cell (ownerImage cell c)=c := by
  have hd := different_owners cell
  by_cases hs : c=names cell (swapOwner cell)
  · subst c
    simp [ownerImage,hd]
  · by_cases ht : c=names cell cell
    · subst c
      simp [ownerImage,hd,Ne.symm hd]
    · simp [ownerImage,hs,ht]
theorem owner_image_injective (cell : Owner) : Function.Injective (ownerImage cell) := by
  intro x y h
  simpa only [owner_image_involution] using congrArg (ownerImage cell) h

def maps (cell : Owner) : SnapshotRawMaps Frame.Predictive Frame.Predictive Frame.Residue Bool :=
  ⟨id,(·+jump cell),id,(·+jump cell),(·+jump cell),routeImage,id,ownerImage cell⟩
abbrev image (cell : Owner) := mapSnapshotReadout (maps cell)
theorem image_injective (cell : Owner) : Function.Injective (image cell) := by
  intro x y he
  have hp := congrArg TemporalSnapshotReadout.predictive he
  have ho := congrArg TemporalSnapshotReadout.order he
  have ht := congrArg TemporalSnapshotReadout.tickPhase he
  have hg := congrArg TemporalSnapshotReadout.progress he
  have hd := congrArg TemporalSnapshotReadout.record he
  have hr := congrArg TemporalSnapshotReadout.residue he
  have hm := congrArg TemporalSnapshotReadout.maintenance he
  have hw := congrArg TemporalSnapshotReadout.owner he
  simp only [mapSnapshotReadout,maps,id_eq] at hp ho ht hg hd hr hm hw
  have hr' := route_image_injective hr
  have hw' := owner_image_injective cell hw
  cases x; cases y
  dsimp at hp ho ht hg hd hr' hm hw'
  congr <;> omega

theorem selected_writer (cell : Owner) (copy : Bool) (h : Factor) :
    TemporalFactorRules.writer (factorSchema (AvailabilityPublication.dataOwner cell copy))
      (AvailabilityPublication.selected cell copy).temporal
      (if copy then (List.replicate (copies cell) h,[false,true])
       else routeImage (List.replicate (copies cell) h,[false,true]))=true := by
  cases cell <;> cases copy
  all_goals rcases h with ⟨p,v,j⟩; cases p <;> cases v <;> cases j <;> rfl
theorem selected_prediction (cell : Owner) (s : Factor) :
    TemporalFactorRules.prediction (factorSchema (AvailabilityPublication.dataOwner cell false))
      (AvailabilityPublication.selected cell false).temporal s=
    TemporalFactorRules.prediction (factorSchema (AvailabilityPublication.dataOwner cell true))
      (AvailabilityPublication.selected cell true).temporal s := by
  cases cell <;> rfl
theorem selected_owner (cell : Owner) (copy : Bool) :
    (AvailabilityPublication.selected cell copy).temporal.resource.owner=
      if copy then swapOwner cell else cell := by
  cases cell <;> cases copy <;> rfl

theorem translated_observation (cell : Owner) (x : Frame.Registers) (hx : SourceClosure cell x) :
    RegisterFuture.observation (target cell) NativePackageBundle.canonical (frameReady cell false) (translate cell x)=
      image cell (RegisterFuture.observation (source cell) NativePackageBundle.canonical (frameReady cell true) x) := by
  obtain ⟨hf,h,hr⟩ := closure_shape cell x hx
  have hphase : ((x ()).ticks+jump cell)%2=(x ()).ticks%2 := by
    cases cell <;> simp only [jump,Bool.false_eq_true,ite_false,ite_true] <;> omega
  have hws : TemporalFactorRules.writer (factorSchema (AvailabilityPublication.dataOwner cell true))
      (AvailabilityPublication.selected cell true).temporal
      (List.replicate (copies cell) h,[false,true])=true := selected_writer cell true h
  rw [observation_equation,observation_equation]
  simp only [translate,interpreted_translation,Frame.pack,TemporalRuntimeCoherence.observationImage,
    TemporalFactorRules.observe,shifted,mapSnapshotReadout,maps,id_eq]
  simp only [selected_prediction,hf,hr,hws,Bool.true_and,ite_true,
    selected_owner,Bool.false_eq_true,ite_false,ite_true,hphase]
  have hw : TemporalFactorRules.writer (factorSchema (AvailabilityPublication.dataOwner cell false))
      (AvailabilityPublication.selected cell false).temporal
        (routeImage (List.replicate (copies cell) h,[false,true]))=true := selected_writer cell false h
  simp only [routeImage] at hw ⊢
  rw [hw]
  simp only [Bool.true_and,ite_true,owner_image_source]

end CSTTT.TargetTheory.GenericHandoff.NativeComposition.PublicationFuture
