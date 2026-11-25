(* =========================================================================
   verification/VerifySU2MassGap.v

   SOLUTION VERIFICATION MODULE FOR TARGET 10 (uniqueness and symmetries of
   the infinite-volume state, reflection positivity, and the transfer-matrix
   mass gap of the 4D SU(2) Wilson lattice gauge theory at strong coupling).

   Assigns the repository's submitted Coq proofs
     - ym.su2_uniqueness.SU2Uniqueness.su2_infinite_volume_uniqueness
     - ym.su2_mass_gap.SU2MassGap.su2_infinite_volume_symmetry
     - ym.su2_mass_gap.SU2MassGap.su2_reflection_positivity
     - ym.su2_multi_clustering.SU2MultiClustering.su2_multi_plaquette_clustering
     - ym.su2_mass_gap.SU2MassGap.su2_transfer_matrix_mass_gap
     - ym.su2_mass_gap.SU2MassGap.su2_transfer_matrix_norm_bound
   to the exact frozen propositions declared in
   `verification/ChallengeSU2MassGap.v`.

   The submitted proofs are stated directly on the frozen definitions, so no
   bridging lemmas are needed: every assignment is a single `exact`.

   This file declares ZERO Axioms, ZERO Parameters, and ZERO Admitted lemmas.
   ========================================================================= *)

Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import ym.su2_uniqueness.
Require Import ym.su2_multi_clustering.
Require Import ym.su2_mass_gap.

Module VerifySU2MassGap.

  (* TARGET 10a: the infinite-volume state does not depend on the exhausting
     sequence of finite volumes. *)
  Theorem verified_su2gauge4D_infinite_volume_uniqueness :
    ChallengeSU2MassGap.Challenge_SU2Gauge4D_InfiniteVolumeUniqueness.
  Proof. exact SU2Uniqueness.su2_infinite_volume_uniqueness. Qed.

  (* TARGET 10b: translation and time-reflection invariance. *)
  Theorem verified_su2gauge4D_infinite_volume_symmetry :
    ChallengeSU2MassGap.Challenge_SU2Gauge4D_InfiniteVolumeSymmetry.
  Proof. exact SU2MassGap.su2_infinite_volume_symmetry. Qed.

  (* TARGET 10c: reflection positivity of the infinite-volume state. *)
  Theorem verified_su2gauge4D_reflection_positivity :
    ChallengeSU2MassGap.Challenge_SU2Gauge4D_ReflectionPositivity.
  Proof. exact SU2MassGap.su2_reflection_positivity. Qed.

  (* TARGET 10d: exponential clustering of multi-plaquette observables. *)
  Theorem verified_su2gauge4D_multi_plaquette_clustering :
    ChallengeSU2MassGap.Challenge_SU2Gauge4D_MultiPlaquetteClustering.
  Proof. exact SU2MultiClustering.su2_multi_plaquette_clustering. Qed.

  (* TARGET 10e: the mass gap of the transfer operator. *)
  Theorem verified_su2gauge4D_transfer_matrix_mass_gap :
    ChallengeSU2MassGap.Challenge_SU2Gauge4D_TransferMatrixMassGap.
  Proof. exact SU2MassGap.su2_transfer_matrix_mass_gap. Qed.

  (* TARGET 10f: the norm of the transfer operator on the orthogonal
     complement of the vacuum. *)
  Theorem verified_su2gauge4D_transfer_matrix_norm_bound :
    ChallengeSU2MassGap.Challenge_SU2Gauge4D_TransferMatrixNormBound.
  Proof. exact SU2MassGap.su2_transfer_matrix_norm_bound. Qed.

End VerifySU2MassGap.
