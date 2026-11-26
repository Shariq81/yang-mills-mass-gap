(* =========================================================================
   verification/VerifySU2GaugeSymmetry.v

   SOLUTION VERIFICATION MODULE FOR TARGET 15 (the action of the gauge
   group on the Osterwalder-Schrader Hilbert space of the 4D SU(2) Wilson
   lattice gauge theory at strong coupling).

   Assigns the repository's submitted Coq proof
     - ym.su2_gauge_symmetry.SU2GaugeSymmetry.su2_gauge_symmetry
   to the exact frozen proposition declared in
   `verification/ChallengeSU2GaugeSymmetry.v`.

   The submitted proof is stated directly on the frozen definitions, so no
   bridging lemma is needed: the assignment is a single `exact`.

   This file declares ZERO Axioms, ZERO Parameters, and ZERO Admitted lemmas.
   ========================================================================= *)

Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import verification.ChallengeSU2GaugeInvariance.
Require Import verification.ChallengeSU2HilbertSpace.
Require Import verification.ChallengeSU2TransferSpectrum.
Require Import verification.ChallengeSU2GaugeSymmetry.
Require Import ym.su2_gauge_symmetry.

Module VerifySU2GaugeSymmetry.

  (* TARGET 15: the gauge group acts on the Osterwalder-Schrader Hilbert
     space by unitary operators that depend only on the restriction of the
     gauge transformation to the hyperplane t = 0, commute with the
     transfer operator and fix the vacuum. *)
  Theorem verified_su2gauge4D_gauge_symmetry :
    ChallengeSU2GaugeSymmetry.Challenge_SU2Gauge4D_GaugeSymmetry.
  Proof. exact SU2GaugeSymmetry.su2_gauge_symmetry. Qed.

End VerifySU2GaugeSymmetry.
