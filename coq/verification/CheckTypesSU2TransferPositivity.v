(* =========================================================================
   verification/CheckTypesSU2TransferPositivity.v

   Typechecks that the 4 verified Target 12 theorems in
   `VerifySU2TransferPositivity` have the exact frozen proposition types
   declared in `ChallengeSU2TransferPositivity`. Kept separate from
   `CheckAxiomsSU2TransferPositivity.v` so the axiom log contains ONLY
   `Print Assumptions` output.
   ========================================================================= *)

Require Import verification.ChallengeSU2TransferPositivity.
Require Import verification.VerifySU2TransferPositivity.

Check (VerifySU2TransferPositivity.verified_su2gauge4D_transfer_matrix_positivity :
         ChallengeSU2TransferPositivity.Challenge_SU2Gauge4D_TransferMatrixPositivity).
Check (VerifySU2TransferPositivity.verified_su2gauge4D_transfer_matrix_spectral_bounds :
         ChallengeSU2TransferPositivity.Challenge_SU2Gauge4D_TransferMatrixSpectralBounds).
Check (VerifySU2TransferPositivity.verified_su2gauge4D_transfer_matrix_symmetry :
         ChallengeSU2TransferPositivity.Challenge_SU2Gauge4D_TransferMatrixSymmetry).
Check (VerifySU2TransferPositivity.verified_su2gauge4D_transfer_matrix_contraction :
         ChallengeSU2TransferPositivity.Challenge_SU2Gauge4D_TransferMatrixContraction).
