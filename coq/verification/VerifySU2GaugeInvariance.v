(* =========================================================================
   verification/VerifySU2GaugeInvariance.v

   SOLUTION VERIFICATION MODULE FOR TARGET 11 (bi-invariance of the Haar
   measure of SU(2) realized by the Hopf grids, and gauge invariance of the
   Gibbs states of the 4D SU(2) Wilson lattice gauge theory).

   Assigns the repository's submitted Coq proofs
     - ym.su2_haar_invariance.SU2HaarInvariance.su2_haar_bi_invariance
     - ym.su2_gauge_invariance.SU2GaugeInvariance.su2_haar_gauge_invariance
     - ym.su2_gauge_invariance.SU2GaugeInvariance.su2_infinite_volume_gauge_invariance
   to the exact frozen propositions declared in
   `verification/ChallengeSU2GaugeInvariance.v`.

   The submitted proofs are stated directly on the frozen definitions, so no
   bridging lemmas are needed: every assignment is a single `exact`.

   This file declares ZERO Axioms, ZERO Parameters, and ZERO Admitted lemmas.
   ========================================================================= *)

Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2GaugeInvariance.
Require Import ym.su2_haar_invariance.
Require Import ym.su2_gauge_invariance.

Module VerifySU2GaugeInvariance.

  (* TARGET 11a: existence, bi-invariance and inversion invariance of the
     Haar integral of SU(2). *)
  Theorem verified_su2_haar_bi_invariance :
    ChallengeSU2GaugeInvariance.Challenge_SU2_HaarBiInvariance.
  Proof. exact SU2HaarInvariance.su2_haar_bi_invariance. Qed.

  (* TARGET 11b: gauge invariance of the finite-volume Haar-measure Gibbs
     state. *)
  Theorem verified_su2gauge4D_haar_gauge_invariance :
    ChallengeSU2GaugeInvariance.Challenge_SU2Gauge4D_HaarGaugeInvariance.
  Proof. exact SU2GaugeInvariance.su2_haar_gauge_invariance. Qed.

  (* TARGET 11c: gauge invariance of the infinite-volume Gibbs state. *)
  Theorem verified_su2gauge4D_infinite_volume_gauge_invariance :
    ChallengeSU2GaugeInvariance.Challenge_SU2Gauge4D_InfiniteVolumeGaugeInvariance.
  Proof. exact SU2GaugeInvariance.su2_infinite_volume_gauge_invariance. Qed.

End VerifySU2GaugeInvariance.
