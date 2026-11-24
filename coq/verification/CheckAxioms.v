(* =========================================================================
   verification/CheckAxioms.v

   Emits ONLY `Print Assumptions` blocks (one per frozen Challenge target),
   with no interleaved `Check` output, so `check_allowlist.py` parses every
   top-level identifier inside every `Axioms:` block with zero prefix skips.
   ========================================================================= *)

Require Import verification.Verify.

Print Assumptions Verify.verified_connects_implies_dist_bound.
Print Assumptions Verify.verified_conditional_exponential_decay.
Print Assumptions Verify.verified_master_conditional_statement.
Print Assumptions Verify.verified_lattice4D_exact21.
Print Assumptions Verify.verified_lattice4D_coordination24.
Print Assumptions Verify.verified_kotecky_preiss_pinned_bound.
Print Assumptions Verify.verified_kotecky_preiss_exponential_decay.
Print Assumptions Verify.verified_lattice4D_kp_exponential_decay.
Print Assumptions Verify.verified_kotecky_preiss_log_partition_fn.
Print Assumptions Verify.verified_kotecky_preiss_log_ratio_decay.
Print Assumptions Verify.verified_lattice4D_partition_fn_decay.
