(* =========================================================================
   verification/VerifySU2TransferPositivity.v

   SOLUTION VERIFICATION MODULE FOR TARGET 12 (positivity of the transfer
   operator of the 4D SU(2) Wilson lattice gauge theory).

   Assigns the repository's submitted Coq proofs
     - ym.su2_transfer_positivity.SU2TransferPositivity.su2_transfer_matrix_positivity
     - ym.su2_transfer_positivity.SU2TransferPositivity.su2_transfer_matrix_spectral_bounds
     - ym.su2_transfer_positivity.SU2TransferPositivity.su2_transfer_matrix_symmetry
     - ym.su2_transfer_positivity.SU2TransferPositivity.su2_transfer_matrix_contraction
   to the exact frozen propositions declared in
   `verification/ChallengeSU2TransferPositivity.v`.

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
Require Import verification.ChallengeSU2TransferPositivity.
Require Import ym.su2_transfer_positivity.

Module VerifySU2TransferPositivity.

  (* TARGET 12a: positivity of the transfer operator. *)
  Theorem verified_su2gauge4D_transfer_matrix_positivity :
    ChallengeSU2TransferPositivity.Challenge_SU2Gauge4D_TransferMatrixPositivity.
  Proof. exact SU2TransferPositivity.su2_transfer_matrix_positivity. Qed.

  (* TARGET 12b: two-sided bound for the transfer operator on the orthogonal
     complement of the vacuum. *)
  Theorem verified_su2gauge4D_transfer_matrix_spectral_bounds :
    ChallengeSU2TransferPositivity.Challenge_SU2Gauge4D_TransferMatrixSpectralBounds.
  Proof. exact SU2TransferPositivity.su2_transfer_matrix_spectral_bounds. Qed.

  (* TARGET 12c: symmetry of the form and of the transfer operator. *)
  Theorem verified_su2gauge4D_transfer_matrix_symmetry :
    ChallengeSU2TransferPositivity.Challenge_SU2Gauge4D_TransferMatrixSymmetry.
  Proof. exact SU2TransferPositivity.su2_transfer_matrix_symmetry. Qed.

  (* TARGET 12d: the transfer operator is a contraction. *)
  Theorem verified_su2gauge4D_transfer_matrix_contraction :
    ChallengeSU2TransferPositivity.Challenge_SU2Gauge4D_TransferMatrixContraction.
  Proof. exact SU2TransferPositivity.su2_transfer_matrix_contraction. Qed.

End VerifySU2TransferPositivity.
