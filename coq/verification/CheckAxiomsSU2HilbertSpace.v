(* =========================================================================
   verification/CheckAxiomsSU2HilbertSpace.v

   Emits ONLY the `Print Assumptions` block of the frozen Target 13
   proposition, with no interleaved `Check` output. `replay.sh` appends this
   output to the outputs of the other `CheckAxioms*.v` files, and
   `check_allowlist.py` parses every top-level identifier inside every
   `Axioms:` block.
   ========================================================================= *)

Require Import verification.VerifySU2HilbertSpace.

Print Assumptions VerifySU2HilbertSpace.verified_su2gauge4D_os_hilbert_space.
