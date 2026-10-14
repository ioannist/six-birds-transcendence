import CSTTT.Corridor.RawDirectSuccessor
import CSTTT.Corridor.FiniteDirectSuccessor
namespace CSTTT.CorridorTheory.RawDirectValidity
open CSTTT CSTTT.DirectSuccessorTheory
open CSTTT.CorridorTheory.AtomicChain CSTTT.CorridorTheory.RawDirectSuccessor

def AlternativeParent (raw : Raw) : Prop :=
  ∃ left∈incoming raw, ∃ right∈incoming raw, left.parent≠right.parent

/-- Every old certificate field is now an explicit raw computation statement.
Predictive equality permits zero advance, whereas the four temporal counters
are strictly increasing, as in the adopted structural direct readout. -/
def data (raw : Raw) (b : Boundary) (a : Assignment) : AtomicDirectSuccessorData where
  source := ⟨b.sourceCarrier⟩
  target := ⟨b.targetCarrier⟩
  immediateEdge := ImmediateDirect raw b a
  payloadComplete := ∀ d∈generated raw a,
    d.sourcePayload=b.source.frontier ∧ d.frontier=b.target.frontier
  payloadHashBound := ∀ (Digest : Type) (hash : Frontier → Digest),
    ∀ d∈generated raw a, hash d.frontier=hash b.target.frontier
  edgeNecessary := generated raw a≠[] ∧ generated raw (deleteSource raw a)=[]
  storageMediated := StorageMediated raw a
  replayableArchive := ArchivalReplay raw a
  alternativeTemporalParent := AlternativeParent raw
  singleUseToken := ∃ d next, fire raw a=some (d,next) ∧
    generated raw next=[] ∧ fire raw next=none ∧ ¬ ImmediateDirect raw b next
  predictiveStep := b.target.frontier.predictive=b.source.frontier.predictive+raw.receiver.predictiveAdvance
  orderStep := b.source.frontier.order<b.target.frontier.order
  tickStep := b.source.frontier.tick<b.target.frontier.tick
  progressStep := b.source.frontier.progress<b.target.frontier.progress
  recordStep := b.source.frontier.record<b.target.frontier.record
  routeDisciplined := b.target.frontier.residue=b.source.frontier.residue++raw.receiver.appendResidue ∧
    raw.receiver.appendResidue≠[]
  ownershipTransferred := b.source.frontier.owner=b.sourceCarrier ∧
    b.target.frontier.owner=b.targetCarrier ∧ raw.receiver.nextOwner=b.targetCarrier

theorem raw_constructs_old_certificate (raw : Raw) (b : Boundary) (a : Assignment)
    (h : ImmediateDirect raw b a) : AtomicDirectSuccessorCertificate (data raw b a) := by
  obtain ⟨edge,c,hi,hd,hpresent,hunused,hg⟩ := (direct_readout_iff raw b a).mp h
  rcases hg with ⟨distinct,parent,child,kind,provenance,sourceLive,targetLive,
    sourceSupport,targetSupport,sourceOwner,targetOwner,payload,adjacent,targetAdvance,
    step,sourceStage,distinctEvents⟩
  have hstep := step
  simp only [readoutStep,decide_eq_true_eq] at hstep
  rcases hstep with ⟨predictive,_,_,_,_,_,_,_,_,residue,append,_,_,nextOwner,_⟩
  have exclusions := actual_direct_exclusions raw b a h
  obtain ⟨_,_,_,_,generation,deleted,_⟩ := direct_constructive_generation raw b a h
  refine {
    distinctCarriers := ?_
    immediateEdge := h
    payloadComplete := ?_
    payloadHashBound := ?_
    edgeNecessary := ?_
    notStorageMediated := exclusions.2.2.1
    notReplayableArchive := exclusions.2.1
    noAlternativeTemporalParent := ?_
    singleUseToken := actual_fire_single_use raw b a h
    predictiveStep := predictive
    orderStep := (direct_strict_temporal_steps raw b a h).1
    tickStep := (direct_strict_temporal_steps raw b a h).2.1
    progressStep := (direct_strict_temporal_steps raw b a h).2.2.1
    recordStep := (direct_strict_temporal_steps raw b a h).2.2.2
    routeDisciplined := ⟨residue,append⟩
    ownershipTransferred := ⟨sourceOwner,targetOwner,nextOwner.symm.trans targetOwner⟩ }
  · intro equal
    exact distinct (congrArg CarrierId.code equal)
  · intro d member
    exact ⟨(complete_payload_hash_binding (fun x : Frontier => x) raw b a h d member).1,
      (complete_payload_hash_binding (fun x : Frontier => x) raw b a h d member).2.1⟩
  · intro Digest hash d member
    exact (complete_payload_hash_binding hash raw b a h d member).2.2
  · refine ⟨?_,deleted⟩
    intro empty
    rw [empty] at generation
    contradiction
  · simp [data,AlternativeParent,hi]

end CSTTT.CorridorTheory.RawDirectValidity
