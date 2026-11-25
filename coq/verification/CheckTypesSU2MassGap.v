(* =========================================================================
   verification/CheckTypesSU2MassGap.v

   Typechecks that the 6 verified Target 10 theorems in `VerifySU2MassGap`
   have the exact frozen proposition types declared in
   `ChallengeSU2MassGap`. Kept separate from `CheckAxiomsSU2MassGap.v` so
   the axiom log contains ONLY `Print Assumptions` output.
   ========================================================================= *)

Require Import verification.ChallengeSU2MassGap.
Require Import verification.VerifySU2MassGap.

Check (VerifySU2MassGap.verified_su2gauge4D_infinite_volume_uniqueness :
         ChallengeSU2MassGap.Challenge_SU2Gauge4D_InfiniteVolumeUniqueness).
Check (VerifySU2MassGap.verified_su2gauge4D_infinite_volume_symmetry :
         ChallengeSU2MassGap.Challenge_SU2Gauge4D_InfiniteVolumeSymmetry).
Check (VerifySU2MassGap.verified_su2gauge4D_reflection_positivity :
         ChallengeSU2MassGap.Challenge_SU2Gauge4D_ReflectionPositivity).
Check (VerifySU2MassGap.verified_su2gauge4D_multi_plaquette_clustering :
         ChallengeSU2MassGap.Challenge_SU2Gauge4D_MultiPlaquetteClustering).
Check (VerifySU2MassGap.verified_su2gauge4D_transfer_matrix_mass_gap :
         ChallengeSU2MassGap.Challenge_SU2Gauge4D_TransferMatrixMassGap).
Check (VerifySU2MassGap.verified_su2gauge4D_transfer_matrix_norm_bound :
         ChallengeSU2MassGap.Challenge_SU2Gauge4D_TransferMatrixNormBound).
