(* =========================================================================
   verification/VerifySU2TransferSpectrum.v

   SOLUTION VERIFICATION MODULE FOR TARGET 14 (the spectrum of the transfer
   operator of the 4D SU(2) Wilson lattice gauge theory at strong coupling
   on its Osterwalder-Schrader Hilbert space).

   Assigns the repository's submitted Coq proof
     - ym.su2_transfer_spectrum.SU2TransferSpectrum.su2_transfer_spectrum
   to the exact frozen proposition declared in
   `verification/ChallengeSU2TransferSpectrum.v`.

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
Require Import verification.ChallengeSU2HilbertSpace.
Require Import verification.ChallengeSU2TransferSpectrum.
Require Import ym.su2_transfer_spectrum.

Module VerifySU2TransferSpectrum.

  (* TARGET 14: the spectrum of the transfer operator is contained in
     [0, exp(- mu / 2)] together with {1}, and 1 belongs to it. *)
  Theorem verified_su2gauge4D_transfer_spectrum :
    ChallengeSU2TransferSpectrum.Challenge_SU2Gauge4D_TransferSpectrum.
  Proof. exact SU2TransferSpectrum.su2_transfer_spectrum. Qed.

End VerifySU2TransferSpectrum.
