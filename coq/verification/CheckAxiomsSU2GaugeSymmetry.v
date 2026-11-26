(* =========================================================================
   verification/CheckAxiomsSU2GaugeSymmetry.v

   Emits ONLY the `Print Assumptions` block of the frozen Target 15
   proposition, with no interleaved `Check` output. `replay.sh` appends this
   output to the outputs of the other `CheckAxioms*.v` files, and
   `check_allowlist.py` parses every top-level identifier inside every
   `Axioms:` block.
   ========================================================================= *)

Require Import verification.VerifySU2GaugeSymmetry.

Print Assumptions VerifySU2GaugeSymmetry.verified_su2gauge4D_gauge_symmetry.
