(* =========================================================================
   verification/CheckAxiomsSU2InfiniteVolume.v

   Emits ONLY the `Print Assumptions` blocks of the 4 frozen Target 9
   propositions, with no interleaved `Check` output. `replay.sh` appends this
   output to the outputs of the other `CheckAxioms*.v` files, and
   `check_allowlist.py` parses every top-level identifier inside every
   `Axioms:` block.
   ========================================================================= *)

Require Import verification.VerifySU2InfiniteVolume.

Print Assumptions VerifySU2InfiniteVolume.verified_su2gauge4D_volume_dependence.
Print Assumptions VerifySU2InfiniteVolume.verified_su2gauge4D_thermodynamic_limit.
Print Assumptions VerifySU2InfiniteVolume.verified_su2gauge4D_infinite_volume_clustering.
Print Assumptions VerifySU2InfiniteVolume.verified_su2gauge4D_infinite_volume_area_law.
