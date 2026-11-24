(* =========================================================================
   verification/VerifyZ2Gauge.v

   SOLUTION VERIFICATION MODULE FOR TARGET 7 (4D Z_2 Wilson lattice gauge
   theory at strong coupling).

   Assigns the repository's submitted Coq proofs
     - ym.z2_gauge_expansion.Z2GaugeExpansion.z2_strong_coupling_expansion
     - ym.z2_gauge_clustering.Z2GaugeClustering.z2_strong_coupling_clustering
     - ym.z2_polymer_gas.Z2PolymerGas.z2_surface_polymer_gas
     - ym.z2_free_energy.Z2FreeEnergy.z2_free_energy_cluster_expansion
   to the exact frozen propositions declared in
   `verification/ChallengeZ2Gauge.v`.

   The submitted proofs are stated directly on the frozen definitions, so no
   bridging lemmas are needed: each assignment is a single `exact`.

   This file declares ZERO Axioms, ZERO Parameters, and ZERO Admitted lemmas.
   ========================================================================= *)

Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.z2_polymer_gas.
Require Import ym.z2_free_energy.

Module VerifyZ2Gauge.

  (* TARGET 7a: exact strong-coupling expansion (closed mod-2 surfaces). *)
  Theorem verified_z2gauge4D_strong_coupling_expansion :
    ChallengeZ2Gauge.Challenge_Z2Gauge4D_StrongCouplingExpansion.
  Proof. exact Z2GaugeExpansion.z2_strong_coupling_expansion. Qed.

  (* TARGET 7b: exponential clustering of the connected plaquette correlator. *)
  Theorem verified_z2gauge4D_strong_coupling_clustering :
    ChallengeZ2Gauge.Challenge_Z2Gauge4D_StrongCouplingClustering.
  Proof. exact Z2GaugeClustering.z2_strong_coupling_clustering. Qed.

  (* TARGET 7c: exact representation as a hard-core gas of surface polymers. *)
  Theorem verified_z2gauge4D_surface_polymer_gas :
    ChallengeZ2Gauge.Challenge_Z2Gauge4D_SurfacePolymerGas.
  Proof. exact Z2PolymerGas.z2_surface_polymer_gas. Qed.

  (* TARGET 7d: Kotecky-Preiss criterion and free-energy cluster expansion. *)
  Theorem verified_z2gauge4D_free_energy_cluster_expansion :
    ChallengeZ2Gauge.Challenge_Z2Gauge4D_FreeEnergyClusterExpansion.
  Proof. exact Z2FreeEnergy.z2_free_energy_cluster_expansion. Qed.

End VerifyZ2Gauge.
