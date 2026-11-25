(* =========================================================================
   verification/CheckAxiomsSU2TransferPositivity.v

   Emits ONLY the `Print Assumptions` blocks of the 4 frozen Target 12
   propositions, with no interleaved `Check` output. `replay.sh` appends this
   output to the outputs of the other `CheckAxioms*.v` files, and
   `check_allowlist.py` parses every top-level identifier inside every
   `Axioms:` block.
   ========================================================================= *)

Require Import verification.VerifySU2TransferPositivity.

Print Assumptions VerifySU2TransferPositivity.verified_su2gauge4D_transfer_matrix_positivity.
Print Assumptions VerifySU2TransferPositivity.verified_su2gauge4D_transfer_matrix_spectral_bounds.
Print Assumptions VerifySU2TransferPositivity.verified_su2gauge4D_transfer_matrix_symmetry.
Print Assumptions VerifySU2TransferPositivity.verified_su2gauge4D_transfer_matrix_contraction.
