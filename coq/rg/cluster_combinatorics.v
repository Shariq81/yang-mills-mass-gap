(* =========================================================================
   cluster_combinatorics.v - Stage 1: Well-Formed Clusters and List Lemmas

   Provides the combinatorial infrastructure for:
   - Well-formed (duplicate-free) clusters
   - Induction on cluster size
   - Removing elements from clusters

   This is the foundation for the tree-graph expansion in Stage 2/3.

   Author: APEX
   Date: 2026-02-19
   ========================================================================= *)

Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Require Import Coq.Sorting.Permutation.
Require Import rg.polymer_types.

Import ListNotations.
Open Scope R_scope.

Section ClusterCombinatorics.

  Context {P : Type} `{PolymerSystem P} `{MetricSystem P}.

  (* =========================================================================
     1. Well-Formed Clusters (no duplicates)
     ========================================================================= *)

  (* A well-formed cluster has no duplicate polymers *)
  Definition wf_cluster (X : list P) : Prop := NoDup X.

  Lemma wf_nil : wf_cluster [].
  Proof. constructor. Qed.

  Lemma wf_cons : forall p X,
      ~ In p X -> wf_cluster X -> wf_cluster (p :: X).
  Proof. intros. constructor; assumption. Qed.

  Lemma wf_tail : forall p X,
      wf_cluster (p :: X) -> wf_cluster X.
  Proof. intros p X Hwf. inversion Hwf; assumption. Qed.

  Lemma wf_head_notin : forall p X,
      wf_cluster (p :: X) -> ~ In p X.
  Proof. intros p X Hwf. inversion Hwf; assumption. Qed.

  (* =========================================================================
     2. Cluster Size Lemmas
     ========================================================================= *)

  Fixpoint cluster_size_list (X : list P) : R :=
    match X with
    | []     => 0
    | p :: rest => size p + cluster_size_list rest
    end.

  Lemma cluster_size_nonneg : forall X,
      0 <= cluster_size_list X.
  Proof.
    induction X as [| p rest IH].
    - simpl. lra.
    - simpl.
      assert (Hsp : size p >= 1) by apply size_pos.
      lra.
  Qed.

  (* =========================================================================
     2a. Decidable Equality (needed for remove and wf_cluster induction)
     ========================================================================= *)

  Class DecidableEq (A : Type) := {
    eq_dec : forall (x y : A), {x = y} + {x <> y}
  }.

  Context `{DecidableEq P}.

  Fixpoint list_remove (p : P) (X : list P) : list P :=
    match X with
    | [] => []
    | q :: rest =>
        if eq_dec p q then rest else q :: list_remove p rest
    end.

  Lemma cluster_size_ge_card : forall X,
      INR (length X) <= cluster_size_list X.
  Proof.
    induction X as [| p rest IH].
    - simpl. lra.
    - change (length (p :: rest)) with (S (length rest)).
      rewrite S_INR.
      simpl.
      assert (Hsp : size p >= 1) by apply size_pos.
      lra.
  Qed.

  (* Removing an element strictly decreases size *)
  Lemma cluster_size_remove : forall p X,
      In p X ->
      cluster_size_list X = size p + cluster_size_list (list_remove p X).
  Proof.
  intros.
Qed.

  Lemma in_list_remove_ne : forall p q X,
      p <> q ->
      In p X ->
      In p (list_remove q X).
  Proof.
    intros p q X Hne HIn.
    induction X as [| r rest IH].
    - inversion HIn.
    - simpl in HIn. simpl.
      destruct (eq_dec q r) as [Heq | Hne'].
      + subst. destruct HIn as [Heq' | HIn'].
        * subst. congruence.
        * exact HIn'.
      + simpl. destruct HIn as [Heq' | HIn'].
        * left. exact Heq'.
        * right. apply IH. exact HIn'.
  Qed.

  (* Helper: if x is in the list after removing y, x was in the original *)
  Lemma in_list_remove_inv : forall x y l,
      In x (list_remove y l) -> In x l.
  Proof.
    intros x y l HIn.
    induction l as [| h t IH].
    - simpl in HIn. inversion HIn.
    - simpl in HIn. destruct (eq_dec y h) as [Heq | Hne].
      + right. exact HIn.
      + simpl in HIn. destruct HIn as [Heq' | HIn'].
        * left. exact Heq'.
        * right. apply IH. exact HIn'.
  Qed.

  Lemma wf_list_remove : forall p X,
      wf_cluster X ->
      wf_cluster (list_remove p X).
  Proof.
  intros.
Qed.

  (* =========================================================================
     4. Induction Principle on wf_cluster
     ========================================================================= *)

  (* The key: wf clusters can be decomposed by removing one element *)
  Lemma wf_cluster_induction :
    forall (Q : list P -> Prop),
      Q [] ->
      (forall p X, wf_cluster (p :: X) -> Q X -> Q (p :: X)) ->
      forall X, wf_cluster X -> Q X.
  Proof.
    intros Q Hnil Hcons X HWF.
    induction X as [| p rest IH].
    - exact Hnil.
    - apply Hcons.
      + exact HWF.
      + apply IH. apply wf_tail in HWF. exact HWF.
  Qed.

End ClusterCombinatorics.
