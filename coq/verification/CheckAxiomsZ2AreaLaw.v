(* =========================================================================
   verification/CheckAxiomsZ2AreaLaw.v

   Emits ONLY the `Print Assumptions` block of the frozen Target 7e
   proposition, with no interleaved `Check` output. `replay.sh` appends this
   output to the outputs of `CheckAxioms.v` and `CheckAxiomsZ2Gauge.v`, and
   `check_allowlist.py` parses every top-level identifier inside every
   `Axioms:` block.
   ========================================================================= *)

Require Import verification.VerifyZ2AreaLaw.

Print Assumptions VerifyZ2AreaLaw.verified_z2gauge4D_wilson_loop_area_law.
