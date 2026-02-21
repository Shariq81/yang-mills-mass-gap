(* =========================================================================
   rooted_tree.v - Stage 3: Rooted Tree Recursion for Cluster Bounds

   Implements the rooted-tree expansion approach to proving the pinned bound.
   Instead of Cayley counting, uses a recursive "peel one neighbor" argument
   that applies KP at each tree edge.

   The key insight (Brydges 1986, simplified):
     sum over rooted trees on X rooted at p
       = product over neighbors of p of (sum over their rooted subtrees)
     KP controls each neighbor sum.

   Author: APEX
   Date: 2026-02-19
   ========================================================================= *)

Require Import Coq.Reals.Reals.
Require Import Coq.Reals.Exp_prop.
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lra.
Require Import rg.polymer_types.
Require Import rg.cluster_combinatorics.

Import ListNotations.
Open Scope R_scope.

Section RootedTree.

  Context {P : Type}
    `{PS  : PolymerSystem P}
    `{MS  : MetricSystem P}
    `{CS  : ConnectivitySystem P}
    `{SS  : SummationSystem P}
    `{DEq : DecidableEq P}.

  (* =========================================================================
     1. The Rooted Tree Activity Sum
     ========================================================================= *)

  (* rtree_weight_sum root X a = sum over rooted spanning trees of X
     rooted at root of: product of exp(a * size v) * activity v for each non-root vertex.
     
     We DEFINE this by the recursive formula (not by enumeration):
     rtree_sum(root, {root}) = 1
     rtree_sum(root, X) = (1/(|X|-1)) * 
       sum_{q in X, q != root, adj root q}
         activity q * exp(a * size q) * rtree_sum(q, X \ {root})
     
     This is the Brydges recursion in its simplest form. *)

  (* For Coq, we phrase it via: 
     The sum over trees with given vertex set and root is bounded by exp(a * cluster_size X)
     We prove this by strong induction on |X|. *)

  (* The bound we ultimately need:
     sum over wf clusters X containing both p1, p2 of [|w(X)| * exp(a * |X|)]
       <= exp(a * size p1) * exp(a * size p2)
     
     Proved by:
     1. |ursell_factor X| <= sum_trees_rooted_both_p1_p2 (tree_graph_majorant)
     2. tree_graph_majorant * prod_activity <= something_from_KP
     3. something_from_KP <= exp(a * s1) * exp(a * s2) by rooted KP induction *)

  (* =========================================================================
     2. Core KP Induction Lemma (Stage 4 target)

     Proves that the rooted tree sum is bounded by exp(a * size root)
     by iterating KP along tree edges.
     ========================================================================= *)

  (* Axiomatize the KP sum to match sum_overlap *)
  (* In the main proof, kp_sum p = sum_overlap p (fun q => activity q * exp (a * size q)) *)
  (* Under kp_sum_condition a:  kp_sum p <= a * size p *)

  (* The rooted bound:
     For any finite wf cluster X and root in X:
     sum_{spanning trees T of X rooted at root} 
       prod_{q in X, q != root} (activity q * exp(a * size q) * [q adj parent(q) in T])
     <= exp(a * cluster_size_list (list_remove root X))
  *)

  (* We state this as the key theorem we will prove by induction *)
  (* For now, we state it as an axiom (the "hard" Stage 4 induction) *)

  (* KP sum condition in terms of sum_overlap *)
  Definition kp_condition_via_sum (a : R) : Prop :=
    forall p,
      sum_overlap p (fun q => activity q * exp (a * size q)) <= a * size p.

  (* KEY LEMMA (Stage 4, to be proved by induction): *)
  (* The sum of weighted activities over a "next-hop neighbor" set 
     is bounded by one application of KP *)
  Lemma kp_one_step :
    forall (a : R) (p : P),
      a > 0 ->
      kp_condition_via_sum a ->
      sum_overlap p (fun q => activity q * exp (a * size q))
      <= a * size p.
  Proof.
    intros a p Ha Hkp.
    apply Hkp.
  Qed.

  (* =========================================================================
     3. The Pinned Bound Statement (Stage 0: exact target)
     ========================================================================= *)

  (*
     TARGET THEOREM (not yet proved, will replace Hypothesis):

     Theorem connecting_bounded_by_pinned_from_KP :
       forall (a : R) (p1 p2 : P),
         a > 0 ->
         kp_condition_via_sum a ->
         (forall X, connects X p1 p2 ->
            Rabs (cluster_weight X) * exp (a * cluster_size_list X)
            <= activity p1 * exp (a * size p1) *
               activity p2 * exp (a * size p2) *
               tree_sum_factor p1 p2 a) ->
         sum_connecting p1 p2 (fun X =>
           Rabs (cluster_weight X) * exp (a * cluster_size_list X))
         <= exp (a * size p1) * exp (a * size p2).

     ==> This follows once we prove the tree_graph_majorant and rooted KP bound.
  *)

  (* =========================================================================
     Definitions
     ========================================================================= *)
  Variable a : R.
  Hypothesis Ha_pos : a > 0.

  (* Abstract neighbors excluding a forbidden set *)
  Variable nbr_excluding : P -> list P -> list P.

  Definition prod_overlap_excluding (p : P) (forb : list P) (f : P -> R) : R :=
    fold_right Rmult 1 (map f (nbr_excluding p forb)).

  Definition sum_overlap_excluding (p : P) (forb : list P) (f : P -> R) : R :=
    fold_right Rplus 0 (map f (nbr_excluding p forb)).

  (* The recursive rooted sum (bounded depth k) *)
  Fixpoint rooted_sum (k : nat) (p : P) (forb : list P) : R :=
    match k with
    | 0%nat => 0 (* Base case *)
    | S k' =>
        activity p * exp (a * size p) *
        prod_overlap_excluding p forb (fun q => 1 + rooted_sum k' q (p :: forb))
    end.

  (* We assume activity is non-negative everywhere, as standard for K-P models *)
  Hypothesis activity_nonneg : forall p, 0 <= activity p.
  Hypothesis size_nonneg : forall p, 0 <= size p.

  (* =========================================================================
     Helper Lemmas
     ========================================================================= *)

  Lemma one_plus_le_exp :
    forall x : R, 0 <= x -> 1 + x <= exp x.
  Proof.
    intros x Hx.
    apply exp_ineq1_le.
  Qed.

  Lemma fold_right_Rmult_nonneg :
    forall (l : list P) (f : P -> R),
      (forall q, In q l -> 0 <= f q) ->
      0 <= fold_right Rmult 1 (map f l).
  Proof.
    intros l f Hnonneg.
    induction l as [|x xs IH]; simpl.
    - lra.
    - apply Rmult_le_pos.
      + apply Hnonneg. left. reflexivity.
      + apply IH. intros q Hq. apply Hnonneg. right. exact Hq.
  Qed.

  Lemma prod_le_exp_sum :
    forall (l : list P) (f : P -> R),
      (forall q, In q l -> 0 <= f q) ->
      fold_right Rmult 1 (map (fun q => 1 + f q) l)
      <= exp (fold_right Rplus 0 (map f l)).
  Proof.
    intros l f Hnonneg.
    induction l as [|x xs IH]; simpl.
    - rewrite exp_0. right. lra.
    - set (sx := fold_right Rplus 0 (map f xs)).
      assert (Hfx : 0 <= f x). { apply Hnonneg. left. reflexivity. }
      assert (IH' : fold_right Rmult 1 (map (fun q : P => 1 + f q) xs) <= exp sx).
      { apply IH. intros q Hq. apply Hnonneg. right. exact Hq. }
      assert (Hhead : 1 + f x <= exp (f x)).
      { apply one_plus_le_exp. exact Hfx. }
      eapply Rle_trans.
      + apply Rmult_le_compat; try lra.
        * apply fold_right_Rmult_nonneg. intros q Hq.
          assert (Hfq : 0 <= f q). { apply Hnonneg. right. exact Hq. }
          lra.
        * exact Hhead.
        * exact IH'.
      + rewrite <- exp_plus. right. ring.
  Qed.

  (* KP sum over a subset (excluding) is bounded by the full KP condition *)
  Hypothesis sum_excluding_le_full :
    forall p forb f,
      (forall q, In q (nbr_excluding p forb) -> 0 <= f q) ->
      sum_overlap_excluding p forb f <= sum_overlap p f.

  Lemma kp_exponent_bound :
    forall p forb,
      kp_condition_via_sum a ->
      sum_overlap_excluding p forb (fun q => activity q * exp (a * size q))
      <= a * size p.
  Proof.
    intros p forb Hkp.
    eapply Rle_trans.
    - apply sum_excluding_le_full.
      intros q Hq.
      assert (H1 : 0 <= activity q) by apply activity_nonneg.
      assert (H2 : 0 < exp (a * size q)) by apply exp_pos.
      nra.
    - apply Hkp.
  Qed.

  Lemma sum_list_R_mono :
    forall (l : list P) (f g : P -> R),
      (forall q, In q l -> f q <= g q) ->
      fold_right Rplus 0 (map f l) <= fold_right Rplus 0 (map g l).
  Proof.
    intros l f g Hle.
    induction l as [|x xs IH]; simpl.
    - right. reflexivity.
    - assert (Hlex : f x <= g x). { apply Hle. left. reflexivity. }
      assert (HIH : fold_right Rplus 0 (map f xs) <= fold_right Rplus 0 (map g xs)).
      { apply IH. intros q Hq. apply Hle. right. exact Hq. }
      lra.
  Qed.

  Hypothesis hkp_strong :
    forall p,
      sum_overlap p (fun q => activity q * exp (2 * a * size q)) <= a * size p.

  Lemma exp_le : forall x y, x <= y -> exp x <= exp y.
  Proof.
    intros x y Hle_exp. destruct (Rle_lt_or_eq_dec x y Hle_exp) as [Hlt | Heq].
    - apply Rlt_le. apply exp_increasing. exact Hlt.
    - rewrite Heq. right. reflexivity.
  Qed.

  Lemma prod_neighbors_le_exp_kp :
    forall p forb k,
      kp_condition_via_sum a ->
      (forall q, In q (nbr_excluding p forb) -> 0 <= rooted_sum k q (p::forb)) ->
      (forall q, In q (nbr_excluding p forb) -> rooted_sum k q (p::forb) <= activity q * exp (2 * a * size q)) ->
      prod_overlap_excluding p forb (fun q => 1 + rooted_sum k q (p::forb))
      <= exp (a * size p).
  Proof.
    intros p forb k Hkp Hnonneg Hle.
    unfold prod_overlap_excluding.
    set (L := nbr_excluding p forb).
    set (f := fun q => rooted_sum k q (p::forb)).

    assert (Hprod : fold_right Rmult 1 (map (fun q => 1 + f q) L) <= exp (fold_right Rplus 0 (map f L))).
    { apply prod_le_exp_sum. intros q Hq. unfold f. apply Hnonneg. exact Hq. }

    assert (Hsum : fold_right Rplus 0 (map f L) <= fold_right Rplus 0 (map (fun q => activity q * exp (2 * a * size q)) L)).
    { apply sum_list_R_mono. exact Hle. }

    assert (HKPsum : fold_right Rplus 0 (map (fun q => activity q * exp (2 * a * size q)) L) <= a * size p).
    { eapply Rle_trans.
      - apply sum_excluding_le_full. intros q Hq.
        assert (0 <= activity q) by apply activity_nonneg.
        assert (0 < exp (2 * a * size q)) by apply exp_pos. nra.
      - apply hkp_strong. }

    eapply Rle_trans; [exact Hprod|].
    apply exp_le. lra.
  Qed.

  (* =========================================================================
     The Engine Target
     ========================================================================= *)

  Lemma rooted_sum_nonneg :
    forall k p forb, 0 <= rooted_sum k p forb.
  Proof.
    intros k. induction k as [|k IH]; intros p forb; simpl.
    - lra.
    - assert (H1 : 0 <= activity p) by apply activity_nonneg.
      assert (H2 : 0 < exp (a * size p)) by apply exp_pos.
      assert (H3 : 0 <= prod_overlap_excluding p forb (fun q => 1 + rooted_sum k q (p :: forb))).
      { apply fold_right_Rmult_nonneg. intros q Hq.
        assert (H4 : 0 <= rooted_sum k q (p :: forb)) by apply IH. lra. }
      apply Rmult_le_pos.
      + apply Rmult_le_pos; [exact H1|apply Rlt_le; exact H2].
      + exact H3.
  Qed.

  Lemma rooted_sum_le_exp2a_bound :
    forall k p forb,
      kp_condition_via_sum a ->
      rooted_sum k p forb <= activity p * exp (2 * a * size p).
  Proof.
    intros k.
    induction k as [|k IH]; intros p forb Hkp; simpl.
    - assert (0 < exp (2 * a * size p)) by apply exp_pos.
      assert (0 <= activity p) by apply activity_nonneg.
      nra.
    - eapply Rle_trans.
      + apply Rmult_le_compat_l.
        * assert (0 < exp (a * size p)) by apply exp_pos.
          assert (0 <= activity p) by apply activity_nonneg.
          nra.
        * apply (prod_neighbors_le_exp_kp p forb k); try assumption.
          -- intros q Hq. apply rooted_sum_nonneg.
          -- intros q Hq. apply IH. exact Hkp.
      + replace (activity p * exp (a * size p) * exp (a * size p))
        with (activity p * (exp (a * size p) * exp (a * size p))) by ring.
        rewrite <- exp_plus.
        replace (a * size p + a * size p) with (2 * a * size p) by ring.
        right. reflexivity.
  Qed.

End RootedTree.

(* =========================================================================
   What comes next (Stage 4 actual proof):
   
   1. Define `spanning_tree_sum root X a` as a fixpoint on wf_cluster X
   2. Prove `spanning_tree_sum root X a <= exp (a * cluster_size_list X)`
      by induction on (length X)
   3. At each step: 
      - case |X| = 1 (root only): trivial
      - case |X| > 1: expand over neighbors, apply KP, apply IH
   4. Apply this to bound `cluster_weight X * exp(a * |X|)` via tree-graph majorant
   ========================================================================= *)
