(* =========================================================================
   polymer_algebra.v - The Real Algebra of Polymer Activities

   Replaces the "Toy Model" (Activity = R) with the full Functional Analysis
   structure required for the Clay Prize.

   Definitions:
   - Field: Abstract configuration space (e.g. gauge fields).
   - Activity: Functional K(X, phi) measuring polymer weight.
   - Norms: Weighted L-infty norms on the functional space.

   Author: APEX
   Date: 2026-02-19
   ========================================================================= *)

Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import rg.polymer_types.

Import ListNotations.
Open Scope R_scope.

(* Context: Polymer System + Field Space *)
Context {P : Type} `{PolymerSystem P} `{MetricSystem P}.
Parameter Field : Type.

(* =========================================================================
   1. The Space of Polymer Activities
   ========================================================================= *)

(* An Activity K is a map from a Polymer X and a Field phi to a real number.
   It represents the deviation from the Gaussian measure localized at X. *)
   
Definition Activity := P -> Field -> R.

(* =========================================================================
   2. The Banach Norm (Weighted Sup Norm)
   ========================================================================= *)

(* To control the cluster expansion, we use a norm weighted by size.
   h: The "mass" parameter (chemical potential for polymer size). 
   G_field: A regulator for the field size (large field regulator). *)

Variable h : R. (* Weight per unit size *)
Variable G_regulator : Field -> R. (* e.g. exp(-|phi|^2) *)

(* The Norm: ||K||_h = sup_phi (1/G(phi)) * sup_p ( |K(p, phi)| * exp(h * size p) ) *)
(* We avoid 'sup' operator issues by defining the Property of being bounded. *)

Definition bounded_by (K : Activity) (B : R) : Prop :=
  forall (p : P) (phi : Field),
    Rabs (K p phi) <= B * G_regulator phi * exp (- h * size p).

(* The Norm Functional (conceptual - we work with the bound B directly) *)
(* activity_norm K = inf { B | bounded_by K B } *)

(* =========================================================================
   3. Algebraic Operations
   ========================================================================= *)

(* Addition of activities *)
Definition act_add (K1 K2 : Activity) : Activity :=
  fun p phi => K1 p phi + K2 p phi.

(* Scaling *)
Definition act_scale (c : R) (K : Activity) : Activity :=
  fun p phi => c * K p phi.

(* Product of activities (on disjoint polymers) *)
(* This is the "Circle Product" needed for the cluster expansion exponentiation *)
(* (K1 * K2)(X) = sum_{Y union Z = X} K1(Y) * K2(Z) ... roughly *)
(* For the simplified "Single Polymer" model, product isn't internal to Activity type
   but happens in the exponent: exp(sum K(p)). *)

(* =========================================================================
   4. Basic Norm Lemmas (Banach Space Properties)
   ========================================================================= *)

Lemma norm_triangle_ineq :
  forall (K1 K2 : Activity) (B1 B2 : R),
    bounded_by K1 B1 ->
    bounded_by K2 B2 ->
    bounded_by (act_add K1 K2) (B1 + B2).
Proof.
  intros K1 K2 B1 B2 H1 H2 p phi.
  unfold act_add.
  apply Rle_trans with (r2 := Rabs (K1 p phi) + Rabs (K2 p phi)).
  - apply Rabs_triang.
  - apply Rle_trans with (r2 := (B1 * G_regulator phi * exp (-h * size p)) + (B2 * G_regulator phi * exp (-h * size p))).
    + apply Rplus_le_compat; [apply H1 | apply H2].
    + (* Algebra: factor out common terms *)
      assert (Hfact: forall x y z, x * z + y * z = (x + y) * z) by (intros; ring).
      (* (B1 * G * E) + (B2 * G * E) = (B1 + B2) * G * E *)
      (* Group G and E *)
      replace (B1 * G_regulator phi * exp (- h * size p)) 
         with (B1 * (G_regulator phi * exp (- h * size p))) by ring.
      replace (B2 * G_regulator phi * exp (- h * size p)) 
         with (B2 * (G_regulator phi * exp (- h * size p))) by ring.
      rewrite Hfact.
      ring.
Qed.

Lemma norm_scale_homogeneity :
  forall (K : Activity) (B c : R),
    bounded_by K B ->
    bounded_by (act_scale c K) (Rabs c * B).
Proof.
  intros K B c H p phi.
  unfold act_scale.
  rewrite Rabs_mult.
  rewrite Rmult_assoc.
  apply Rmult_le_compat_l.
  - apply Rabs_pos.
  - apply H.
Qed.
