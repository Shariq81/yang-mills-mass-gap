(* =========================================================================
   verification/VerifySU2Gauge.v

   SOLUTION VERIFICATION MODULE FOR TARGET 8 (4D SU(2) Wilson lattice gauge
   theory at strong coupling).

   Assigns the repository's submitted Coq proofs
     - ym.su2_clustering.SU2Clustering.su2_strong_coupling_clustering
     - ym.su2_area_law.SU2AreaLaw.su2_wilson_loop_area_law
     - ym.su2_haar_limit.SU2HaarLimit.su2_haar_state_exists
     - ym.su2_haar_limit.SU2HaarLimit.su2_haar_clustering
     - ym.su2_haar_limit.SU2HaarLimit.su2_haar_wilson_loop_area_law
   to the exact frozen propositions declared in
   `verification/ChallengeSU2Gauge.v`.

   The submitted proofs are stated directly on the frozen definitions, so no
   bridging lemmas are needed: every assignment is a single `exact`.

   This file declares ZERO Axioms, ZERO Parameters, and ZERO Admitted lemmas.
   ========================================================================= *)

Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import ym.su2_clustering.
Require Import ym.su2_area_law.
Require Import ym.su2_haar_limit.

Module VerifySU2Gauge.

  (* TARGET 8a: exponential clustering at strong coupling, uniformly in the
     finite volume and in the finite a-priori link distribution. *)
  Theorem verified_su2gauge4D_strong_coupling_clustering :
    ChallengeSU2Gauge.Challenge_SU2Gauge4D_StrongCouplingClustering.
  Proof. exact SU2Clustering.su2_strong_coupling_clustering. Qed.

  (* TARGET 8b: Wilson-loop area law at strong coupling, uniformly in the
     finite volume and in the center-symmetric finite a-priori distribution. *)
  Theorem verified_su2gauge4D_wilson_loop_area_law :
    ChallengeSU2Gauge.Challenge_SU2Gauge4D_WilsonLoopAreaLaw.
  Proof. exact SU2AreaLaw.su2_wilson_loop_area_law. Qed.

  (* TARGET 8c: the Haar-measure Gibbs expectation exists. *)
  Theorem verified_su2gauge4D_haar_state_exists :
    ChallengeSU2Gauge.Challenge_SU2Gauge4D_HaarStateExists.
  Proof. exact SU2HaarLimit.su2_haar_state_exists. Qed.

  (* TARGET 8d: exponential clustering for the Haar-measure Gibbs state. *)
  Theorem verified_su2gauge4D_haar_clustering :
    ChallengeSU2Gauge.Challenge_SU2Gauge4D_HaarClustering.
  Proof. exact SU2HaarLimit.su2_haar_clustering. Qed.

  (* TARGET 8e: Wilson-loop area law for the Haar-measure Gibbs state. *)
  Theorem verified_su2gauge4D_haar_wilson_loop_area_law :
    ChallengeSU2Gauge.Challenge_SU2Gauge4D_HaarWilsonLoopAreaLaw.
  Proof. exact SU2HaarLimit.su2_haar_wilson_loop_area_law. Qed.

End VerifySU2Gauge.
