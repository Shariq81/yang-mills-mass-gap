(* =========================================================================
   verification/CheckAxiomsSU2MassGap.v

   Emits ONLY the `Print Assumptions` blocks of the 6 frozen Target 10
   propositions, with no interleaved `Check` output. `replay.sh` appends this
   output to the outputs of the other `CheckAxioms*.v` files, and
   `check_allowlist.py` parses every top-level identifier inside every
   `Axioms:` block.
   ========================================================================= *)

Require Import verification.VerifySU2MassGap.

Print Assumptions VerifySU2MassGap.verified_su2gauge4D_infinite_volume_uniqueness.
Print Assumptions VerifySU2MassGap.verified_su2gauge4D_infinite_volume_symmetry.
Print Assumptions VerifySU2MassGap.verified_su2gauge4D_reflection_positivity.
Print Assumptions VerifySU2MassGap.verified_su2gauge4D_multi_plaquette_clustering.
Print Assumptions VerifySU2MassGap.verified_su2gauge4D_transfer_matrix_mass_gap.
Print Assumptions VerifySU2MassGap.verified_su2gauge4D_transfer_matrix_norm_bound.
