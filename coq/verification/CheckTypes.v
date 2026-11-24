(* =========================================================================
   verification/CheckTypes.v

   Typechecks that each verified theorem in `Verify` has the exact frozen
   proposition type declared in `Challenge`. Kept separate from
   `CheckAxioms.v` so `axioms.log` contains ONLY `Print Assumptions` output.
   ========================================================================= *)

Require Import verification.Challenge.
Require Import verification.Verify.

Check (Verify.verified_connects_implies_dist_bound :
         Challenge.Challenge_ConnectsImpliesDistBound).
Check (Verify.verified_conditional_exponential_decay :
         Challenge.Challenge_ConditionalExponentialDecay).
Check (Verify.verified_master_conditional_statement :
         Challenge.Challenge_MasterConditionalStatement).
Check (Verify.verified_lattice4D_exact21 :
         Challenge.Challenge_Lattice4D_Exact21).
Check (Verify.verified_lattice4D_coordination24 :
         Challenge.Challenge_Lattice4D_Coordination24).
Check (Verify.verified_kotecky_preiss_pinned_bound :
         Challenge.Challenge_KoteckyPreiss_PinnedBound).
Check (Verify.verified_kotecky_preiss_exponential_decay :
         Challenge.Challenge_KoteckyPreiss_ExponentialDecay).
Check (Verify.verified_lattice4D_kp_exponential_decay :
         Challenge.Challenge_Lattice4D_KP_ExponentialDecay).
Check (Verify.verified_kotecky_preiss_log_partition_fn :
         Challenge.Challenge_KoteckyPreiss_LogPartitionFn).
Check (Verify.verified_kotecky_preiss_log_ratio_decay :
         Challenge.Challenge_KoteckyPreiss_LogRatioDecay).
Check (Verify.verified_lattice4D_partition_fn_decay :
         Challenge.Challenge_Lattice4D_PartitionFn_Decay).
