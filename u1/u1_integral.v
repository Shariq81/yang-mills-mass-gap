(* =========================================================================
   u1_integral.v - Haar Measure and Product Integration for U(1)

   Tier 0 minimal stack: finite-dimensional integrals via an abstract RInt
   interface (portable to environments without Coquelicot).
   No σ-algebras, no abstract measure theory.

   U(1) ≅ S¹ ≅ [0, 2π) with normalized Haar measure (1/2π) dθ
   ========================================================================= *)

From Coq Require Import Reals.
From Coq Require Import List.
From Coq Require Import Permutation.
From Coq Require Import Lra.
From Coq Require Import Ranalysis1.
From Coq Require Import FunctionalExtensionality.

Require Import U1.u1_lattice.
Import U1Lattice.

Import ListNotations.
Open Scope R_scope.

Module U1Integral.

(* =========================================================================
   Part 1: Basic Constants
   ========================================================================= *)

Definition two_pi : R := 2 * PI.

Lemma two_pi_pos : two_pi > 0.
Proof.
  unfold two_pi.
  apply Rmult_lt_0_compat; [lra | exact PI_RGT_0].
Qed.

Lemma two_pi_neq_0 : two_pi <> 0.
Proof. apply Rgt_not_eq. exact two_pi_pos. Qed.

(* =========================================================================
   Part 2: Single U(1) Haar Integral

   For f : R -> R, the normalized Haar integral is:
     ∫_{U(1)} f dμ = (1/2π) ∫_0^{2π} f(θ) dθ

   We keep RInt abstract in Tier 0 and only require its constant-function rule.
   ========================================================================= *)

Parameter RInt : (R -> R) -> R -> R -> R.
Axiom RInt_const : forall c a b, RInt (fun _ => c) a b = c * (b - a).

(* Haar integral on U(1) *)
Definition haar_u1_integral (f : R -> R) : R :=
  (/ two_pi) * RInt f 0 two_pi.

(* =========================================================================
   Part 3: Key Properties of Haar Integral

   We axiomatize these for now; proving them requires showing
   integrability conditions which adds complexity.
   ========================================================================= *)

(* Normalization: integral of constant 1 is 1 *)
Lemma haar_normalized : haar_u1_integral (fun _ => 1) = 1.
Proof.
  unfold haar_u1_integral.
  rewrite RInt_const.
  unfold two_pi.
  (* Goal: / (2 * PI) * (1 * (2 * PI - 0)) = 1 *)
  replace (2 * PI - 0) with (2 * PI) by ring.
  field.
  assert (H : PI > 0) by exact PI_RGT_0.
  lra.
Qed.

(* Linearity *)
Axiom haar_linear_add : forall f g,
  haar_u1_integral (fun theta => f theta + g theta) =
  haar_u1_integral f + haar_u1_integral g.

Axiom haar_linear_scale : forall c f,
  haar_u1_integral (fun theta => c * f theta) = c * haar_u1_integral f.

(* Positivity: non-negative functions integrate to non-negative values *)
Axiom haar_nonneg : forall f,
  (forall theta, 0 <= theta <= two_pi -> f theta >= 0) ->
  haar_u1_integral f >= 0.

(* Strict positivity: strictly positive continuous functions have positive integral *)
Axiom haar_pos : forall f,
  (forall theta, 0 <= theta <= two_pi -> f theta > 0) ->
  haar_u1_integral f > 0.

(* Boundedness *)
Axiom haar_bounded : forall f M,
  (forall theta, 0 <= theta <= two_pi -> Rabs (f theta) <= M) ->
  Rabs (haar_u1_integral f) <= M.

(* Translation invariance (Haar property) - optional for now *)
Axiom haar_translation_invariant : forall f phi,
  haar_u1_integral (fun theta => f (theta + phi)) = haar_u1_integral f.

(* Reflection invariance: θ ↦ -θ preserves Haar measure *)
(* This is provable from substitution: ∫_0^{2π} f(-θ) dθ = ∫_0^{2π} f(θ) dθ *)
Axiom haar_reflection_invariant : forall f,
  haar_u1_integral (fun theta => f (- theta)) = haar_u1_integral f.

(* Two-variable swap primitive (minimal analytic Fubini primitive). *)
Axiom haar_swap2 : forall (f : R -> R -> R),
  haar_u1_integral (fun x => haar_u1_integral (fun y => f x y)) =
  haar_u1_integral (fun y => haar_u1_integral (fun x => f x y)).

(* =========================================================================
   Part 4: Product Haar Integral (Iterated)

   For a configuration U : cfg, we integrate over all link angles.
   This is the finite-dimensional path integral.

   Product integral is defined by iteration over the link list.
   ========================================================================= *)

(* Update configuration at one link *)
Definition cfg_update (U : cfg) (l : link) (theta : R) : cfg :=
  fun l' => if link_eq_dec l' l then theta else U l'.

(* Pointwise sign-flip transform on configurations *)
Definition cfg_flip (flip : link -> bool) (U : cfg) : cfg :=
  fun l => if flip l then - U l else U l.

(* Iterated product integral over a list of links *)
Fixpoint haar_prod_integral (ls : list link) (F : cfg -> R) (U : cfg) : R :=
  match ls with
  | nil => F U
  | l :: ls' =>
      haar_u1_integral (fun theta =>
        haar_prod_integral ls' F (cfg_update U l theta))
  end.

Lemma haar_prod_integral_ext : forall ls F G U,
  (forall V, F V = G V) ->
  haar_prod_integral ls F U = haar_prod_integral ls G U.
Proof.
  induction ls as [| l ls' IH]; intros F G U HFG.
  - simpl. apply HFG.
  - simpl.
    assert (Heq :
      (fun theta : R =>
         haar_prod_integral ls' F (cfg_update U l theta)) =
      (fun theta : R =>
         haar_prod_integral ls' G (cfg_update U l theta))).
    {
      apply functional_extensionality.
      intro theta.
      apply IH.
      exact HFG.
    }
    rewrite Heq.
    reflexivity.
Qed.

Lemma haar_u1_integral_ext : forall f g,
  (forall theta, f theta = g theta) ->
  haar_u1_integral f = haar_u1_integral g.
Proof.
  intros f g Hfg.
  apply f_equal.
  apply functional_extensionality.
  exact Hfg.
Qed.

Lemma cfg_update_comm : forall U l1 l2 t1 t2,
  l1 <> l2 ->
  cfg_update (cfg_update U l1 t1) l2 t2 =
  cfg_update (cfg_update U l2 t2) l1 t1.
Proof.
  intros U l1 l2 t1 t2 Hneq.
  unfold cfg_update.
  apply functional_extensionality.
  intro l.
  destruct (link_eq_dec l l2) as [Hl2|Hl2];
  destruct (link_eq_dec l l1) as [Hl1|Hl1];
  subst; try contradiction; reflexivity.
Qed.

(* Full configuration integral (over all links in finite volume) *)
Definition integral_over_cfg (L : lattice_size) (F : cfg -> R) : R :=
  haar_prod_integral (all_links L) F (fun _ => 0).

(* =========================================================================
   Part 5: Properties of Product Integral
   ========================================================================= *)

(* Normalization of product integral *)
Lemma haar_prod_normalized : forall ls U,
  haar_prod_integral ls (fun _ => 1) U = 1.
Proof.
  induction ls as [| l ls' IH]; intros U.
  - simpl. reflexivity.
  - simpl.
    assert (Heq :
      (fun theta : R => haar_prod_integral ls' (fun _ : cfg => 1) (cfg_update U l theta))
      = (fun _ : R => 1)).
    {
      apply functional_extensionality.
      intros theta. apply IH.
    }
    rewrite Heq.
    apply haar_normalized.
Qed.

(* Linearity of product integral *)
Lemma haar_prod_linear_add : forall ls F G U,
  haar_prod_integral ls (fun V => F V + G V) U =
  haar_prod_integral ls F U + haar_prod_integral ls G U.
Proof.
  induction ls as [| l ls' IH]; intros F G U.
  - simpl. ring.
  - simpl.
    replace
      (fun theta : R =>
         haar_prod_integral ls' (fun V : cfg => F V + G V) (cfg_update U l theta))
      with
      (fun theta : R =>
         haar_prod_integral ls' F (cfg_update U l theta) +
         haar_prod_integral ls' G (cfg_update U l theta)).
    2:{
      apply functional_extensionality.
      intro theta.
      symmetry.
      apply IH.
    }
    rewrite haar_linear_add.
    reflexivity.
Qed.

Lemma haar_prod_linear_scale : forall ls c F U,
  haar_prod_integral ls (fun V => c * F V) U =
  c * haar_prod_integral ls F U.
Proof.
  induction ls as [| l ls' IH]; intros c F U.
  - simpl. ring.
  - simpl.
    replace
      (fun theta : R =>
         haar_prod_integral ls' (fun V : cfg => c * F V) (cfg_update U l theta))
      with
      (fun theta : R =>
         c * haar_prod_integral ls' F (cfg_update U l theta)).
    2:{
      apply functional_extensionality.
      intro theta.
      symmetry.
      apply IH.
    }
    rewrite haar_linear_scale.
    reflexivity.
Qed.

(* Positivity of product integral *)
Lemma haar_prod_nonneg : forall ls F U,
  (forall V, F V >= 0) ->
  haar_prod_integral ls F U >= 0.
Proof.
  induction ls as [| l ls' IH]; intros F U HF.
  - simpl. exact (HF U).
  - simpl.
    apply haar_nonneg.
    intros theta Htheta.
    apply IH.
    exact HF.
Qed.

Lemma haar_prod_pos : forall ls F U,
  (forall V, F V > 0) ->
  haar_prod_integral ls F U > 0.
Proof.
  induction ls as [| l ls' IH]; intros F U HF.
  - simpl. exact (HF U).
  - simpl.
    apply haar_pos.
    intros theta Htheta.
    apply IH.
    exact HF.
Qed.

Lemma haar_prod_swap_adj : forall l1 l2 ls F U,
  haar_prod_integral (l1 :: l2 :: ls) F U =
  haar_prod_integral (l2 :: l1 :: ls) F U.
Proof.
  intros l1 l2 ls F U.
  simpl.
  destruct (link_eq_dec l1 l2) as [Heq|Hneq].
  - subst l2. reflexivity.
  - rewrite (haar_swap2 (fun t1 t2 =>
      haar_prod_integral ls F (cfg_update (cfg_update U l1 t1) l2 t2))).
    apply haar_u1_integral_ext.
    intro t2.
    apply haar_u1_integral_ext.
    intro t1.
    rewrite (cfg_update_comm U l1 l2 t1 t2 Hneq).
    reflexivity.
Qed.

Lemma haar_prod_integral_perm : forall ls1 ls2 F U,
  Permutation ls1 ls2 ->
  haar_prod_integral ls1 F U = haar_prod_integral ls2 F U.
Proof.
  intros ls1 ls2 F U Hperm.
  revert F U.
  induction Hperm; intros F U.
  - reflexivity.
  - simpl.
    apply haar_u1_integral_ext.
    intro theta.
    apply IHHperm.
  - apply haar_prod_swap_adj.
  - etransitivity; eauto.
Qed.

Lemma haar_prod_append : forall ls1 ls2 F U,
  haar_prod_integral (ls1 ++ ls2) F U =
  haar_prod_integral ls1 (fun V => haar_prod_integral ls2 F V) U.
Proof.
  induction ls1 as [| l ls1' IH]; intros ls2 F U.
  - reflexivity.
  - simpl.
    apply haar_u1_integral_ext.
    intro theta.
    apply IH.
Qed.

(* Fubini: integration order doesn't matter *)
Lemma haar_prod_fubini : forall ls1 ls2 F U,
  haar_prod_integral (ls1 ++ ls2) F U =
  haar_prod_integral ls2 (fun V => haar_prod_integral ls1 F V) U.
Proof.
  intros ls1 ls2 F U.
  transitivity (haar_prod_integral (ls2 ++ ls1) F U).
  - apply haar_prod_integral_perm.
    apply Permutation_app_comm.
  - rewrite haar_prod_append.
    reflexivity.
Qed.

(* Reflection/sign-flip invariance outside the integrated support.
   If no integrated variable is flipped, cfg_flip only changes coordinates
   outside ls and therefore preserves any ls-supported integrand. *)
Definition supported_on (ls : list link) (F : cfg -> R) : Prop :=
  forall U V, (forall l, In l ls -> U l = V l) -> F U = F V.

Lemma cfg_flip_id_on_ls_false : forall ls flip U,
  (forall l, In l ls -> flip l = false) ->
  forall l, In l ls -> cfg_flip flip U l = U l.
Proof.
  intros ls flip U Hflip l Hin.
  unfold cfg_flip.
  rewrite (Hflip l Hin).
  reflexivity.
Qed.

Lemma haar_prod_reflection_invariant : forall ls (flip : link -> bool) F U,
  supported_on ls F ->
  (forall l, In l ls -> flip l = false) ->
  haar_prod_integral ls F U =
  haar_prod_integral ls (fun V => F (cfg_flip flip V)) U.
Proof.
  intros ls flip F U Hsupp Hflip.
  apply haar_prod_integral_ext.
  intro V.
  apply Hsupp.
  intros l Hin.
  symmetry.
  exact (cfg_flip_id_on_ls_false ls flip V Hflip l Hin).
Qed.

(* =========================================================================
   Part 6: Full Configuration Integral Properties
   ========================================================================= *)

Lemma integral_normalized : forall L,
  integral_over_cfg L (fun _ => 1) = 1.
Proof.
  intros L. unfold integral_over_cfg.
  apply haar_prod_normalized.
Qed.

Lemma integral_linear_add : forall L F G,
  integral_over_cfg L (fun U => F U + G U) =
  integral_over_cfg L F + integral_over_cfg L G.
Proof.
  intros L F G.
  unfold integral_over_cfg.
  apply haar_prod_linear_add.
Qed.

Lemma integral_linear_scale : forall L c F,
  integral_over_cfg L (fun U => c * F U) = c * integral_over_cfg L F.
Proof.
  intros L c F.
  unfold integral_over_cfg.
  apply haar_prod_linear_scale.
Qed.

Lemma integral_nonneg : forall L F,
  (forall U, F U >= 0) ->
  integral_over_cfg L F >= 0.
Proof.
  intros L F Hpos. unfold integral_over_cfg.
  apply haar_prod_nonneg. exact Hpos.
Qed.

Lemma integral_pos : forall L F,
  (forall U, F U > 0) ->
  integral_over_cfg L F > 0.
Proof.
  intros L F Hpos. unfold integral_over_cfg.
  apply haar_prod_pos. exact Hpos.
Qed.

End U1Integral.
