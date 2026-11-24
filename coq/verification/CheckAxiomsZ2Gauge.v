(* =========================================================================
   verification/CheckAxiomsZ2Gauge.v

   Emits ONLY `Print Assumptions` blocks (one per frozen Target 7
   proposition), with no interleaved `Check` output. `replay.sh` appends
   this output to the output of `CheckAxioms.v`, and `check_allowlist.py`
   parses every top-level identifier inside every `Axioms:` block.
   ========================================================================= *)

Require Import verification.VerifyZ2Gauge.

Print Assumptions VerifyZ2Gauge.verified_z2gauge4D_strong_coupling_expansion.
Print Assumptions VerifyZ2Gauge.verified_z2gauge4D_strong_coupling_clustering.
Print Assumptions VerifyZ2Gauge.verified_z2gauge4D_surface_polymer_gas.
Print Assumptions VerifyZ2Gauge.verified_z2gauge4D_free_energy_cluster_expansion.
