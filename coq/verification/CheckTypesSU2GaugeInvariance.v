(* =========================================================================
   verification/CheckTypesSU2GaugeInvariance.v

   Typechecks that the 3 verified Target 11 theorems in
   `VerifySU2GaugeInvariance` have the exact frozen proposition types
   declared in `ChallengeSU2GaugeInvariance`. Kept separate from
   `CheckAxiomsSU2GaugeInvariance.v` so the axiom log contains ONLY
   `Print Assumptions` output.
   ========================================================================= *)

Require Import verification.ChallengeSU2GaugeInvariance.
Require Import verification.VerifySU2GaugeInvariance.

Check (VerifySU2GaugeInvariance.verified_su2_haar_bi_invariance :
         ChallengeSU2GaugeInvariance.Challenge_SU2_HaarBiInvariance).
Check (VerifySU2GaugeInvariance.verified_su2gauge4D_haar_gauge_invariance :
         ChallengeSU2GaugeInvariance.Challenge_SU2Gauge4D_HaarGaugeInvariance).
Check (VerifySU2GaugeInvariance.verified_su2gauge4D_infinite_volume_gauge_invariance :
         ChallengeSU2GaugeInvariance.Challenge_SU2Gauge4D_InfiniteVolumeGaugeInvariance).
