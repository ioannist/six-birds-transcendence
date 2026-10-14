# Acyclic Local-Witness Gluing

## Landed statement

`CSTTT.PackageTheory.acyclicLocalWitnessGluing` takes:

1. a rooted parent presentation with a decreasing rank;
2. a scope cover;
3. the running-intersection property;
4. edge-compatible local assignments;
5. independent local acceptance proofs;
6. independent hard-gate proofs.

It constructs one global assignment and proves that its restriction equals every local assignment.

The proof has two nontrivial steps:

- `localEqualityAlongScopedReach` propagates equality along a coordinate-preserving tree path;
- `gluedAssignmentAgrees` uses running intersection to connect the chosen local representative to any other clause containing that coordinate.

Acyclic rooted shape is verified by the executable certificate checker. Running intersection and edge agreement are the premises that perform the gluing work.

## Bounded corroboration

The deterministic binary checker evaluated **1,025,416** local scope/assignment candidates over path and star trees of two to four nodes. **18,972** candidates satisfied all theorem premises; all **18,972** glued successfully, with zero violations.

This exhaustive finite run corroborates the formal source. Python is not a proof oracle and the run is not represented as a replacement for Lean kernel checking. The local environment lacks `lean` and `lake`, so compilation remains pending.

## Boundary controls

- `PC-10`: edge disagreement blocks gluing;
- `PC-11`: a disconnected parent graph is not a join-tree certificate;
- `PC-12`: edge checks can pass while a nonedge conflict is hidden when running intersection fails;
- `PC-13`: a supplied global record can disagree with the canonical glued assignment.

The previously frozen `CM-08` and `CM-15` remain the local/global and branchwise/recombination no-go companions.
