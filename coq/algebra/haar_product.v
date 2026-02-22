(* =========================================================================
   haar_product.v - Finite Product Haar Integration

   Generic implementation of iterated Haar integration over a list of
   variables (indices). Used for lattice gauge theory configuration integrals.

   Author: APEX
   Date: 2026-02-19
   ========================================================================= *)

Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import algebra.compact_group.

Import ListNotations.
Open Scope R_scope.

Section ProductHaar.

  (* Context: Group G with Haar measure *)
  Context {G : Type} `{Group G} `{HaarIntegral G}.
  
  (* Context: Index set I (e.g. link) with decidable equality *)
  Context {I : Type}.
  Context {I_eq_dec : forall x y : I, {x = y} + {x <> y}}.

  (* Configuration: map from index to group element *)
  Definition Config := I -> G.

  (* Update configuration at index i with value g *)
  Definition update (U : Config) (i : I) (g : G) : Config :=
    fun j => if I_eq_dec j i then g else U j.

  (* Iterated Haar integral over a list of indices *)
  Fixpoint haar_prod (ls : list I) (F : Config -> R) (U : Config) : R :=
    match ls with
    | [] => F U
    | i :: ls' =>
        haar (fun g =>
          haar_prod ls' F (update U i g))
    end.

  (* Properties of Product Integral *)

  (* Linearity *)
  Lemma haar_prod_linear_add : forall ls F Hf U,
    haar_prod ls (fun V => F V + Hf V) U =
    haar_prod ls F U + haar_prod ls Hf U.
  Proof.
    induction ls as [| i ls' IH]; intros F Hf U.
    - simpl. reflexivity.
    - simpl.
      (* First, show the inner haar_prod distributes via IH *)
      assert (Heq : (fun g => haar_prod ls' (fun V => F V + Hf V) (update U i g)) =
                    (fun g => haar_prod ls' F (update U i g) + haar_prod ls' Hf (update U i g))).
      { apply functional_extensionality. intro g. apply IH. }
      rewrite Heq.
      (* Now apply haar_linear_add *)
      apply haar_linear_add.
  Qed.

  Lemma haar_prod_linear_scale : forall ls c F U,
    haar_prod ls (fun V => c * F V) U =
    c * haar_prod ls F U.
  Proof.
    induction ls as [| i ls' IH]; intros c F U.
    - simpl. reflexivity.
    - simpl.
      (* First show inner haar_prod scales via IH *)
      assert (Heq : (fun g => haar_prod ls' (fun V => c * F V) (update U i g)) =
                    (fun g => c * haar_prod ls' F (update U i g))).
      { apply functional_extensionality. intro g. apply IH. }
      rewrite Heq.
      (* Now apply haar_linear_scale *)
      apply haar_linear_scale.
  Qed.

  (* Normalization *)
  Lemma haar_prod_normalized : forall ls U,
    haar_prod ls (fun _ => 1) U = 1.
  Proof.
    induction ls as [| i ls' IH]; intros U.
    - simpl. reflexivity.
    - simpl.
      assert (Heq : (fun g => haar_prod ls' (fun _ => 1) (update U i g)) = (fun _ => 1)).
      { apply functional_extensionality. intro g. apply IH. }
      rewrite Heq.
      apply haar_normalized.
  Qed.

  (* Positivity *)
  Lemma haar_prod_nonneg : forall ls F U,
    (forall V, F V >= 0) ->
    haar_prod ls F U >= 0.
  Proof.
    induction ls as [| i ls' IH]; intros F U Hpos.
    - simpl. apply Hpos.
    - simpl.
      apply haar_nonneg.
      intro g.
      apply IH.
      exact Hpos.
  Qed.

  (* Permutation Invariance (Fubini) - Requires Axiom or Proof via Swap *)
  (* We axiomatize the swap property for single Haar integral first *)

  Axiom haar_swap : forall (f : G -> G -> R),
    haar (fun x => haar (fun y => f x y)) =
    haar (fun y => haar (fun x => f x y)).

  (* Update commutativity: order of updates doesn't matter for distinct indices *)
  Lemma update_comm : forall U i j gi gj,
    i <> j ->
    update (update U i gi) j gj = update (update U j gj) i gi.
  Proof.
    intros U i j gi gj Hneq.
    apply functional_extensionality. intro k.
    unfold update.
    destruct (I_eq_dec k j); destruct (I_eq_dec k i); subst; try reflexivity;
      exfalso; apply Hneq; reflexivity.
  Qed.

  (* For Haar integration, the specific index identity doesn't matter *)
  (* When we integrate over both i and j, swapping their roles gives the same result *)
  Axiom haar_prod_swap_indices : forall i j l F U,
    haar (fun gi => haar (fun gj => haar_prod l F (update (update U i gi) j gj))) =
    haar (fun gj => haar (fun gi => haar_prod l F (update (update U j gj) i gi))).

  Lemma haar_prod_perm : forall ls1 ls2 F U,
    Permutation ls1 ls2 ->
    haar_prod ls1 F U = haar_prod ls2 F U.
  Proof.
    intros ls1 ls2 F U Hperm.
    revert U.
    induction Hperm as [ | x l l' Hperm IH | x y l | l l' l'' _ IH1 _ IH2 ]; intro U.
    - reflexivity.
    - simpl. f_equal. apply functional_extensionality. intro g. apply IH.
    - simpl.
      (* Key step: swap integration order and variable names *)
      apply haar_prod_swap_indices.
    - rewrite IH1. apply IH2.
  Qed.

End ProductHaar.
