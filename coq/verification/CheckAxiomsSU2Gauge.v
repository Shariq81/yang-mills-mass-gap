(* =========================================================================
   verification/CheckAxiomsSU2Gauge.v

   Emits ONLY the `Print Assumptions` blocks of the 5 frozen Target 8
   propositions, with no interleaved `Check` output. `replay.sh` appends this
   output to the outputs of `CheckAxioms.v`, `CheckAxiomsZ2Gauge.v` and
   `CheckAxiomsZ2AreaLaw.v`, and `check_allowlist.py` parses every top-level
   identifier inside every `Axioms:` block.
   ========================================================================= *)

Require Import verification.VerifySU2Gauge.

Print Assumptions VerifySU2Gauge.verified_su2gauge4D_strong_coupling_clustering.
Print Assumptions VerifySU2Gauge.verified_su2gauge4D_wilson_loop_area_law.
Print Assumptions VerifySU2Gauge.verified_su2gauge4D_haar_state_exists.
Print Assumptions VerifySU2Gauge.verified_su2gauge4D_haar_clustering.
Print Assumptions VerifySU2Gauge.verified_su2gauge4D_haar_wilson_loop_area_law.
