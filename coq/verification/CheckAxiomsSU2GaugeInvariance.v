(* =========================================================================
   verification/CheckAxiomsSU2GaugeInvariance.v

   Emits ONLY the `Print Assumptions` blocks of the 3 frozen Target 11
   propositions, with no interleaved `Check` output. `replay.sh` appends this
   output to the outputs of the other `CheckAxioms*.v` files, and
   `check_allowlist.py` parses every top-level identifier inside every
   `Axioms:` block.
   ========================================================================= *)

Require Import verification.VerifySU2GaugeInvariance.

Print Assumptions VerifySU2GaugeInvariance.verified_su2_haar_bi_invariance.
Print Assumptions VerifySU2GaugeInvariance.verified_su2gauge4D_haar_gauge_invariance.
Print Assumptions VerifySU2GaugeInvariance.verified_su2gauge4D_infinite_volume_gauge_invariance.
