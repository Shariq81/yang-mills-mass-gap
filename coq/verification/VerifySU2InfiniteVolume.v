(* =========================================================================
   verification/VerifySU2InfiniteVolume.v

   SOLUTION VERIFICATION MODULE FOR TARGET 9 (infinite-volume limit of the
   4D SU(2) Wilson lattice gauge theory at strong coupling).

   Assigns the repository's submitted Coq proofs
     - ym.su2_volume.SU2Volume.su2_volume_dependence
     - ym.su2_infinite_volume.SU2InfiniteVolume.su2_thermodynamic_limit
     - ym.su2_infinite_volume.SU2InfiniteVolume.su2_infinite_volume_clustering
     - ym.su2_infinite_volume.SU2InfiniteVolume.su2_infinite_volume_area_law
   to the exact frozen propositions declared in
   `verification/ChallengeSU2InfiniteVolume.v`.

   The submitted proofs are stated directly on the frozen definitions, so no
   bridging lemmas are needed: every assignment is a single `exact`.

   This file declares ZERO Axioms, ZERO Parameters, and ZERO Admitted lemmas.
   ========================================================================= *)

Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import ym.su2_volume.
Require Import ym.su2_infinite_volume.

Module VerifySU2InfiniteVolume.

  (* TARGET 9a: exponentially small dependence on the volume. *)
  Theorem verified_su2gauge4D_volume_dependence :
    ChallengeSU2InfiniteVolume.Challenge_SU2Gauge4D_VolumeDependence.
  Proof. exact SU2Volume.su2_volume_dependence. Qed.

  (* TARGET 9b: the infinite-volume Gibbs expectation exists. *)
  Theorem verified_su2gauge4D_thermodynamic_limit :
    ChallengeSU2InfiniteVolume.Challenge_SU2Gauge4D_ThermodynamicLimit.
  Proof. exact SU2InfiniteVolume.su2_thermodynamic_limit. Qed.

  (* TARGET 9c: exponential clustering of the infinite-volume Gibbs state. *)
  Theorem verified_su2gauge4D_infinite_volume_clustering :
    ChallengeSU2InfiniteVolume.Challenge_SU2Gauge4D_InfiniteVolumeClustering.
  Proof. exact SU2InfiniteVolume.su2_infinite_volume_clustering. Qed.

  (* TARGET 9d: Wilson-loop area law of the infinite-volume Gibbs state. *)
  Theorem verified_su2gauge4D_infinite_volume_area_law :
    ChallengeSU2InfiniteVolume.Challenge_SU2Gauge4D_InfiniteVolumeAreaLaw.
  Proof. exact SU2InfiniteVolume.su2_infinite_volume_area_law. Qed.

End VerifySU2InfiniteVolume.
