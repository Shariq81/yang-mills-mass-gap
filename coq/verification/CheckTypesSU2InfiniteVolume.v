(* =========================================================================
   verification/CheckTypesSU2InfiniteVolume.v

   Typechecks that the 4 verified Target 9 theorems in
   `VerifySU2InfiniteVolume` have the exact frozen proposition types declared
   in `ChallengeSU2InfiniteVolume`. Kept separate from
   `CheckAxiomsSU2InfiniteVolume.v` so the axiom log contains ONLY
   `Print Assumptions` output.
   ========================================================================= *)

Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.VerifySU2InfiniteVolume.

Check (VerifySU2InfiniteVolume.verified_su2gauge4D_volume_dependence :
         ChallengeSU2InfiniteVolume.Challenge_SU2Gauge4D_VolumeDependence).
Check (VerifySU2InfiniteVolume.verified_su2gauge4D_thermodynamic_limit :
         ChallengeSU2InfiniteVolume.Challenge_SU2Gauge4D_ThermodynamicLimit).
Check (VerifySU2InfiniteVolume.verified_su2gauge4D_infinite_volume_clustering :
         ChallengeSU2InfiniteVolume.Challenge_SU2Gauge4D_InfiniteVolumeClustering).
Check (VerifySU2InfiniteVolume.verified_su2gauge4D_infinite_volume_area_law :
         ChallengeSU2InfiniteVolume.Challenge_SU2Gauge4D_InfiniteVolumeAreaLaw).
