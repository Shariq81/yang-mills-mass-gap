(* =========================================================================
   verification/CheckTypesZ2Gauge.v

   Typechecks that each verified Target 7 theorem in `VerifyZ2Gauge` has the
   exact frozen proposition type declared in `ChallengeZ2Gauge`. Kept
   separate from `CheckAxiomsZ2Gauge.v` so the axiom log contains ONLY
   `Print Assumptions` output.
   ========================================================================= *)

Require Import verification.ChallengeZ2Gauge.
Require Import verification.VerifyZ2Gauge.

Check (VerifyZ2Gauge.verified_z2gauge4D_strong_coupling_expansion :
         ChallengeZ2Gauge.Challenge_Z2Gauge4D_StrongCouplingExpansion).
Check (VerifyZ2Gauge.verified_z2gauge4D_strong_coupling_clustering :
         ChallengeZ2Gauge.Challenge_Z2Gauge4D_StrongCouplingClustering).
Check (VerifyZ2Gauge.verified_z2gauge4D_surface_polymer_gas :
         ChallengeZ2Gauge.Challenge_Z2Gauge4D_SurfacePolymerGas).
Check (VerifyZ2Gauge.verified_z2gauge4D_free_energy_cluster_expansion :
         ChallengeZ2Gauge.Challenge_Z2Gauge4D_FreeEnergyClusterExpansion).
