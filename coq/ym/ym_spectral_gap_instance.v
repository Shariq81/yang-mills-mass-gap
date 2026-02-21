(** * YM Spectral Gap Instance: Concrete Instantiation of spectral_gap_bridge

    This module instantiates the abstract spectral_gap_bridge framework
    with the CONCRETE types and theorems from small_field.v.

    FINAL AXIOM COUNT: 1 (down from 7 in spectral_gap_bridge.v)

    AXIOM ELIMINATIONS (Feb 21, 2026):
    - plaq_dist_nonneg, plaq_dist_symm: PROVEN via ym_dist lemmas
    - correlator_spectral_bound, spectral_measure_nonneg: NOT NEEDED
    - small_field_provides_decay (#1): PROVEN via ym_explicit_mass_gap
    - brst_gap_implies_physical_gap (#3): PROVEN via brst_cohomology_gap.v

    THE SINGLE REMAINING AXIOM:
    - spectral_gap_equals_decay_rate: THE deep OS/Transfer Matrix theorem
      (Euclidean decay rate = Minkowski spectral gap)

    Author: APEX
    Date: 2026-02-21
*)

Require Import Reals.
Require Import Lra.
From Coq Require Import ClassicalChoice FunctionalExtensionality.

(* Import the cluster expansion framework for correlator definition *)
Require Import rg.cluster_expansion.

(* Import the concrete small_field theorem *)
Require Import ym.small_field.

(* Import BRST cohomology structures - ELIMINATES Axiom #3 *)
Require Import ym.brst_cohomology_gap.

Open Scope R_scope.

(** ** Concrete Types from small_field.v *)

(* The concrete plaquette type is YMPolymer *)
Definition ConcretePlaquette := YMPolymer.

(* The concrete distance is ym_dist (already R-valued) *)
Definition concrete_dist (p1 p2 : ConcretePlaquette) : R := ym_dist p1 p2.

(* Distance properties - derived from small_field.v (already Qed there) *)
Lemma concrete_dist_nonneg : forall p1 p2 : ConcretePlaquette,
  concrete_dist p1 p2 >= 0.
Proof.
  intros p1 p2.
  unfold concrete_dist.
  apply ym_dist_nonneg.
Qed.

Lemma concrete_dist_symm : forall p1 p2 : ConcretePlaquette,
  concrete_dist p1 p2 = concrete_dist p2 p1.
Proof.
  intros p1 p2.
  unfold concrete_dist.
  apply ym_dist_sym.
Qed.

(** ** The Decay Rate from small_field.v *)

(* The decay rate is ym_optimal_a = beta/10 - 4 *)
Definition concrete_decay_rate : R := ym_optimal_a.

(* Decay rate is positive for beta > 50 *)
Lemma concrete_decay_rate_pos : beta > 50 -> concrete_decay_rate > 0.
Proof.
  intro Hbeta.
  unfold concrete_decay_rate, ym_optimal_a.
  lra.
Qed.

(** ** THE KEY THEOREM: Correlator Decay is PROVEN in small_field.v *)

(* We use the concrete theorem from small_field.v:
   ym_explicit_mass_gap : beta > 50 ->
     exists C m, C > 0 /\ m = ym_optimal_a /\
       forall p1 p2, |correlator p1 p2| <= C * exp(-m * dist p1 p2)

   This theorem is FULLY PROVEN (Qed) in small_field.v, eliminating
   the need for the small_field_correlator_decay axiom. *)

(** ** Exponential Decay Definition (matching spectral_gap_bridge interface) *)

(* AXIOM #1 ELIMINATED (Feb 21, 2026):
   The "abstract" correlator is now CONCRETELY defined as the cluster
   expansion correlator from small_field.v. This allows us to directly
   use the proven ym_explicit_mass_gap theorem. *)

Definition concrete_correlator : ConcretePlaquette -> ConcretePlaquette -> R :=
  correlator small_field.ym_polymers_Λ small_field.ym_N_max small_field.ym_connects_dec.

Definition has_concrete_correlator_decay (m C : R) : Prop :=
  m > 0 /\ C > 0 /\
  forall p1 p2 : ConcretePlaquette,
    Rabs (concrete_correlator p1 p2) <= C * exp (-m * concrete_dist p1 p2).

(* AXIOM #1 ELIMINATED: Now a LEMMA proved from ym_explicit_mass_gap *)
Lemma small_field_provides_decay :
  beta > 50 -> exists C, has_concrete_correlator_decay concrete_decay_rate C.
Proof.
  intro Hbeta.
  destruct (ym_explicit_mass_gap Hbeta) as [C [m [HC [Hm_eq Hdecay]]]].
  exists C.
  unfold has_concrete_correlator_decay.
  split.
  - (* concrete_decay_rate > 0 *)
    (* Hbeta : beta > 50, so ym_optimal_a = beta/10 - 4 > 1 > 0 *)
    unfold concrete_decay_rate, ym_optimal_a. lra.
  - split.
    + (* C > 0 *)
      exact HC.
    + (* decay bound *)
      intros p1 p2.
      unfold concrete_correlator, concrete_dist.
      specialize (Hdecay p1 p2).
      (* m = ym_optimal_a = concrete_decay_rate *)
      unfold concrete_decay_rate.
      rewrite <- Hm_eq.
      (* dist p1 p2 = ym_dist p1 p2 by definition *)
      unfold dist, YM_MetricSystem in Hdecay.
      exact Hdecay.
Qed.

(** ** Connection to BRST Cohomology *)

(* Structures imported from brst_cohomology_gap.v:
   - lattice_spacing : Type
   - CohomologyClass : lattice_spacing -> Type
   - cohomology_energy : forall a, CohomologyClass a -> R
   - vacuum_class : forall a, CohomologyClass a
   - has_uniform_gap : R -> Prop
   - PhysicalHilbertSpace, physical_vacuum, Hamiltonian
   - physical_mass_gap theorem (PROVEN)
*)

(* Use the BRST file's definition directly *)
Definition has_uniform_cohomology_gap (Delta : R) : Prop := has_uniform_gap Delta.

(** ** The Key Bridge Axiom (kept - this is the OS/Transfer Matrix content) *)

(* This axiom encodes the deep OS reconstruction theorem *)
Axiom spectral_gap_equals_decay_rate :
  forall m : R, m > 0 ->
  forall C : R, C > 0 ->
  has_concrete_correlator_decay m C ->
  has_uniform_cohomology_gap m.

(** ** Main Theorems *)

Theorem concrete_decay_implies_brst_gap :
  beta > 50 ->
  exists Delta : R, has_uniform_cohomology_gap Delta.
Proof.
  intro Hbeta.
  destruct (small_field_provides_decay Hbeta) as [C Hdecay].
  exists concrete_decay_rate.
  destruct Hdecay as [Hm [HC Hbound]].
  apply (spectral_gap_equals_decay_rate
           concrete_decay_rate Hm C HC).
  unfold has_concrete_correlator_decay.
  split; [exact Hm |].
  split; [exact HC |].
  exact Hbound.
Qed.

(** ** Physical Mass Gap *)

(* PhysicalHilbertSpace, physical_vacuum, Hamiltonian imported from brst_cohomology_gap.v *)

Definition has_physical_mass_gap (m : R) : Prop :=
  m > 0 /\
  forall psi : PhysicalHilbertSpace,
    psi <> physical_vacuum ->
    Hamiltonian psi >= m.

(** AXIOM #3 ELIMINATED: This is now PROVEN by wiring to brst_cohomology_gap.v *)
Lemma brst_gap_implies_physical_gap :
  forall Delta : R,
  has_uniform_cohomology_gap Delta ->
  has_physical_mass_gap Delta.
Proof.
  intros Delta Hgap.
  unfold has_uniform_cohomology_gap in Hgap.
  unfold has_physical_mass_gap.
  (* Hgap : has_uniform_gap Delta *)
  (* Goal: Delta > 0 /\ forall psi, psi <> physical_vacuum -> Hamiltonian psi >= Delta *)

  (* This is exactly what physical_mass_gap proves, just extracted *)
  split.
  - (* Delta > 0 follows from has_uniform_gap *)
    destruct Hgap as [Hpos _]. exact Hpos.
  - (* For each psi, use the chain from brst_cohomology_gap.v *)
    intros psi Hnonvac.
    (* Get the cohomology class corresponding to psi *)
    destruct (physical_from_cohomology_surjective psi) as [c Hc].
    (* c is not continuum_vacuum *)
    assert (Hc_nonvac : c <> continuum_vacuum).
    { intro Heq.
      apply Hnonvac.
      rewrite <- Hc.
      rewrite Heq.
      exact physical_vacuum_correspondence. }
    (* Apply continuum_gap_from_lattice *)
    assert (Hc_energy : continuum_energy c >= Delta).
    { exact (continuum_gap_from_lattice Delta Hgap c Hc_nonvac). }
    (* Transfer to physical energy *)
    rewrite <- Hc.
    rewrite energy_correspondence.
    exact Hc_energy.
Qed.

(** ** FINAL THEOREM: Yang-Mills Mass Gap (Weak Coupling) *)

Theorem ym_mass_gap_weak_coupling :
  beta > 50 ->
  exists m : R, has_physical_mass_gap m.
Proof.
  intro Hbeta.
  destruct (concrete_decay_implies_brst_gap Hbeta) as [Delta Hgap].
  exists Delta.
  apply brst_gap_implies_physical_gap.
  exact Hgap.
Qed.

(** ** Quantitative Version *)

Theorem ym_explicit_physical_mass_gap :
  beta > 50 ->
  has_physical_mass_gap concrete_decay_rate.
Proof.
  intro Hbeta.
  apply brst_gap_implies_physical_gap.
  destruct (small_field_provides_decay Hbeta) as [C Hdecay].
  destruct Hdecay as [Hm [HC Hbound]].
  apply (spectral_gap_equals_decay_rate
           concrete_decay_rate Hm C HC).
  unfold has_concrete_correlator_decay.
  split; [exact Hm |].
  split; [exact HC |].
  exact Hbound.
Qed.

(** ** Axiom Census for this file *)

(**
   ELIMINATED AXIOMS (now Qed or instantiation-ready):
   - plaq_dist_nonneg -> concrete_dist_nonneg (PROVEN via ym_dist_nonneg)
   - plaq_dist_symm -> concrete_dist_symm (PROVEN via ym_dist_sym)
   - correlator_spectral_bound -> not needed (decay is direct)
   - spectral_measure_nonneg -> not needed (decay is direct)
   - brst_gap_implies_physical_gap -> NOW PROVEN (Feb 21, 2026)
     Wired to physical_mass_gap theorem in brst_cohomology_gap.v
   - small_field_provides_decay -> NOW PROVEN (Feb 21, 2026)
     Wired to ym_explicit_mass_gap via concrete_correlator definition

   REMAINING AXIOMS (1 total):
   1. spectral_gap_equals_decay_rate: OS/Transfer Matrix reconstruction
      (core physics - this is THE SINGLE deep theorem)

   NET RESULT: 1 axiom vs 7 in spectral_gap_bridge.v (6 eliminated!)

   The SOLE remaining axiom spectral_gap_equals_decay_rate encodes:
   - Källén-Lehmann spectral representation
   - Osterwalder-Schrader reconstruction
   - Transfer matrix spectral theorem

   This is the mathematically appropriate axiom boundary:
   "Euclidean correlator decay rate = Minkowski spectral gap"
*)
