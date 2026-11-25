(* =========================================================================
   verification/CheckTypesSU2Gauge.v

   Typechecks that the 5 verified Target 8 theorems in `VerifySU2Gauge` have
   the exact frozen proposition types declared in `ChallengeSU2Gauge`. Kept
   separate from `CheckAxiomsSU2Gauge.v` so the axiom log contains ONLY
   `Print Assumptions` output.
   ========================================================================= *)

Require Import verification.ChallengeSU2Gauge.
Require Import verification.VerifySU2Gauge.

Check (VerifySU2Gauge.verified_su2gauge4D_strong_coupling_clustering :
         ChallengeSU2Gauge.Challenge_SU2Gauge4D_StrongCouplingClustering).
Check (VerifySU2Gauge.verified_su2gauge4D_wilson_loop_area_law :
         ChallengeSU2Gauge.Challenge_SU2Gauge4D_WilsonLoopAreaLaw).
Check (VerifySU2Gauge.verified_su2gauge4D_haar_state_exists :
         ChallengeSU2Gauge.Challenge_SU2Gauge4D_HaarStateExists).
Check (VerifySU2Gauge.verified_su2gauge4D_haar_clustering :
         ChallengeSU2Gauge.Challenge_SU2Gauge4D_HaarClustering).
Check (VerifySU2Gauge.verified_su2gauge4D_haar_wilson_loop_area_law :
         ChallengeSU2Gauge.Challenge_SU2Gauge4D_HaarWilsonLoopAreaLaw).
