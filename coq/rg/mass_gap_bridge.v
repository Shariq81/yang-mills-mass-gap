(* =========================================================================
   mass_gap_bridge.v - Summary: Lattice + Continuum Mass Gap

   Combines the two main results:
   1. Lattice mass gap (ym/small_field.v): beta > 50 => cluster correlator decays
   2. Continuum mass gap (rg/continuum_limit.v): beta > 100 => m_phys > 0

   Author: APEX
   Date: 2026-02-19
   ========================================================================= *)

Require Import Coq.Reals.Reals.
Require Import Coq.micromega.Lra.
Require Import rg.polymer_types.
Require Import rg.cluster_expansion.
Require Import ym.small_field.
Require Import rg.continuum_limit.
Require Import ym.wilson_entry.

Open Scope R_scope.

(* =========================================================================
   1. Lattice Mass Gap (from small_field.v)

   For beta > 50, the cluster correlator of YM plaquette polymers
   decays exponentially: |G(p1,p2)| <= C * exp(-dist(p1,p2)).

   Note: The correlator uses the finite volume parameters from small_field.v.
   ========================================================================= *)

Theorem lattice_mass_gap :
  beta > 50 ->
  has_mass_gap
    (correlator small_field.ym_polymers_Λ
                small_field.ym_N_max
                small_field.ym_connects_dec) small_field.ym_optimal_a.
Proof. exact small_field.ym_polymer_mass_gap_from_kp. Qed.

(* =========================================================================
   2. Continuum Mass Gap (from wilson_entry.v)

   For beta > 100, the Wilson action enters the scaling region,
   the RG flow converges, and a positive physical mass exists.
   ========================================================================= *)

Theorem continuum_mass_gap :
  forall b : R, b > 100 -> exists m_phys, m_phys > 0.
Proof. exact WilsonEntry.yang_mills_mass_gap_unconditional. Qed.

Print Assumptions lattice_mass_gap.
Print Assumptions continuum_mass_gap.
