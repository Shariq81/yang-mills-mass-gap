(* =========================================================================
   pinned_bound.v - Overlap-Graph Pinned Bound Skeleton

   PURPOSE
   - Provide the exact overlap-land theorem interface for proving the
     connecting-cluster pinned bound from KP.
   - Keep overlap (KP graph) and adj (path graph) as SEPARATE relations.
   - Rooted-tree recursion skeleton: T(p,S) ≤ exp(a·size p) · ∏_{q∈Nbr(p)\S} (1+T(q,S∪{p}))
   - Induction on depth k; no Fixpoint over trees yet.

   STATUS
   - Structural skeleton only (proof obligations intentionally left open).
   - Intended as the staging file for Stage 2-6 combinatorics work.
   ========================================================================= *)

From Coq Require Import List Reals Lra.
Require Import Coq.Classes.RelationClasses.
Require Import Coq.Reals.Exp_prop.
Require Import Coq.Reals.Rpower.
Require Import Coq.Reals.RIneq.
Require Import Coq.Logic.FunctionalExtensionality.
Import ListNotations.
Open Scope R_scope.

Require Import rg.polymer_types.
Require Import rg.tree_graph.
Require Import rg.cluster_expansion.
Require Import Coq.Lists.ListDec.

Section PinnedBound.

Context {P : Type}.
Context `{PolymerSystem P}.
Context `{MetricSystem P}.
Context `{ConnectivitySystem P}.
Context `{SummationSystem P}.

Variable eq_dec : forall x y : P, {x = y} + {x <> y}.
Variable overlap_dec : forall x y : P, {overlap x y} + {~ overlap x y}.

Definition Cluster : Type := list P.

(* hard-core Mayer function *)
Definition zeta_hc (u v : P) : R :=
  if overlap_dec u v then (-1) else 0.

Lemma zeta_hc_abs_le_1 :
  forall u v, 0 <= Rabs (zeta_hc u v) <= 1.
Proof.
  intros u v. unfold zeta_hc.
  destruct (overlap_dec u v).
  - (* Rabs (-1) = 1 *)
    unfold Rabs. destruct (Rcase_abs (-1)); lra.
  - (* Rabs 0 = 0 *)
    rewrite Rabs_R0. lra.
Qed.

Lemma one_plus_abs_le_2 :
  forall u v, 0 <= 1 + Rabs (zeta_hc u v) <= 2.
Proof.
  intros u v.
  pose proof (zeta_hc_abs_le_1 u v) as [Hlo Hhi].
  split; lra.
Qed.

Lemma one_plus_zeta_hc_is_0_or_1 :
  forall u v, (1 + zeta_hc u v = 0) \/ (1 + zeta_hc u v = 1).
Proof.
  intros u v. unfold zeta_hc.
  destruct (overlap_dec u v).
  - left. lra.
  - right. lra.
Qed.

Lemma one_plus_abs_zeta_hc_is_1_or_2 :
  forall u v, (1 + Rabs (zeta_hc u v) = 1) \/ (1 + Rabs (zeta_hc u v) = 2).
Proof.
  intros u v. unfold zeta_hc.
  destruct (overlap_dec u v).
  - (* Rabs (-1) = 1 *)
    right. unfold Rabs. destruct (Rcase_abs (-1)); lra.
  - (* Rabs 0 = 0 *)
    left. rewrite Rabs_R0. lra.
Qed.

(* =========================================================================
   1. Two Relations: Overlap vs Adjacency (NEVER COERCE)

   - overlap (from PolymerSystem): incompatibility for KP sums / Mayer expansion.
     Nbr(p) = { q | overlap p q }.
   - adj (from ConnectivitySystem): adjacency for cluster paths.
     Path connectivity uses adj, NOT overlap.

   Translation points are explicit; add shares_edge_implies_overlap ONLY if
   it holds in your model (often it doesn't).
   ========================================================================= *)

(* Overlap graph: paths via overlap edges (for KP / tree recursion) *)
Definition overlap_edge_in (X : Cluster) (p q : P) : Prop :=
  In p X /\ In q X /\ overlap p q.

Inductive overlap_path_in_cluster (X : Cluster) : P -> P -> Prop :=
| opath_refl : forall p,
    In p X ->
    overlap_path_in_cluster X p p
| opath_step : forall p q r,
    overlap_edge_in X p q ->
    overlap_path_in_cluster X q r ->
    overlap_path_in_cluster X p r.

Definition connects_overlap (X : Cluster) (p1 p2 : P) : Prop :=
  In p1 X /\ In p2 X /\ overlap_path_in_cluster X p1 p2.

(* Path graph: uses adj (from ConnectivitySystem). Kept separate. *)
Definition adj_edge_in (X : Cluster) (p q : P) : Prop :=
  In p X /\ In q X /\ adj p q.

Inductive adj_path_in_cluster (X : Cluster) : P -> P -> Prop :=
| apath_refl : forall p, In p X -> adj_path_in_cluster X p p
| apath_step : forall p q r,
    adj_edge_in X p q ->
    adj_path_in_cluster X q r ->
    adj_path_in_cluster X p r.

Definition connects_adj (X : Cluster) (p1 p2 : P) : Prop :=
  In p1 X /\ In p2 X /\ adj_path_in_cluster X p1 p2.

(* Translation hypothesis: adjacency implies overlap (true in YM: shared edge => shared vertex) *)
Hypothesis adj_implies_overlap : forall p q, adj p q -> overlap p q.

(* Path conversion: adj-path => overlap-path *)
Lemma adj_path_implies_overlap_path :
  forall (X : Cluster) (p1 p2 : P),
    adj_path_in_cluster X p1 p2 ->
    overlap_path_in_cluster X p1 p2.
Proof.
  intros X p1 p2 Hpath.
  induction Hpath as [p' | p' q' r' Hadj_edge Hpath' IH].
  - apply opath_refl. assumption.
  - destruct Hadj_edge as [Hp [Hq Hadj]].
    apply opath_step with q'.
    + unfold overlap_edge_in. repeat split; try assumption.
      apply adj_implies_overlap. exact Hadj.
    + exact IH.
Qed.

(* path_in_cluster (from cluster_expansion) => adj_path_in_cluster *)
Lemma path_in_cluster_implies_adj_path :
  forall (X : Cluster) (p1 p2 : P),
    path_in_cluster X p1 p2 -> adj_path_in_cluster X p1 p2.
Proof.
  intros X p1 p2 Hpath.
  induction Hpath as [X0 p0 Hin | X' p0 q0 r0 Hin Hadj Hpath' IH].
  - apply apath_refl. exact Hin.
  - apply apath_step with q0.
    + unfold adj_edge_in. repeat split.
      * exact Hin.
      * apply (path_in_cluster_start_in X' q0 r0 Hpath').
      * exact Hadj.
    + exact IH.
Qed.

(* connects_adj => connects_overlap *)
Lemma connects_adj_implies_connects_overlap :
  forall (X : Cluster) (p1 p2 : P),
    connects_adj X p1 p2 -> connects_overlap X p1 p2.
Proof.
  intros X p1 p2 [Hp1 [Hp2 Hpath]].
  unfold connects_overlap.
  repeat split; try assumption.
  apply adj_path_implies_overlap_path. exact Hpath.
Qed.

(* connects (from cluster_expansion) => connects_overlap *)
Lemma connects_implies_connects_overlap :
  forall (X : Cluster) (p1 p2 : P),
    connects X p1 p2 -> connects_overlap X p1 p2.
Proof.
  intros X p1 p2 [Hp1 [Hp2 Hpath]].
  apply connects_adj_implies_connects_overlap.
  unfold connects_adj. repeat split; try assumption.
  apply path_in_cluster_implies_adj_path. exact Hpath.
Qed.

(* =========================================================================
   2. Neighbors for Recursion (Overlap Graph, EXCLUDING SELF)

   For tree recursion, we sum/product over q with overlap p q AND q ≠ p.
   The full overlap relation may be reflexive; the recursion must exclude self.
   ========================================================================= *)

Parameter neighbors_for_recursion : P -> list P.
Hypothesis neighbors_for_recursion_spec : forall p q,
  In q (neighbors_for_recursion p) <-> overlap p q /\ q <> p.

(* Degree bound: hook for coordination_bound (e.g. 24 for 4D plaquettes) *)
Parameter overlap_degree_bound : nat.
Hypothesis neighbors_for_recursion_length :
  forall p, (length (neighbors_for_recursion p) <= overlap_degree_bound)%nat.
Hypothesis neighbors_for_recursion_NoDup :
  forall p, NoDup (neighbors_for_recursion p).

Definition nbr_excluding (p : P) (S : list P) : list P :=
  filter (fun q => match in_dec eq_dec q S with left _ => false | right _ => true end)
        (neighbors_for_recursion p).

Definition sum_overlap_excluding (p : P) (S : list P) (f : P -> R) : R :=
  fold_right Rplus 0 (map f (nbr_excluding p S)).

Definition prod_overlap_excluding (p : P) (S : list P) (f : P -> R) : R :=
  fold_right Rmult 1 (map f (nbr_excluding p S)).

(* Helper: filter doesn't increase length *)
Lemma filter_length_le : forall (A : Type) (f : A -> bool) (l : list A),
  (length (filter f l) <= length l)%nat.
Proof.
  intros A f l.
  induction l as [|x xs IH].
  - simpl. apply Nat.le_refl.
  - simpl. destruct (f x).
    + simpl. apply le_n_S. exact IH.
    + apply Nat.le_trans with (length xs).
      * exact IH.
      * apply Nat.le_succ_diag_r.
Qed.

(* Filter preserves NoDup *)
Lemma filter_NoDup : forall (A : Type) (f : A -> bool) (l : list A),
  NoDup l -> NoDup (filter f l).
Proof.
  intros A f l Hnd.
  induction Hnd as [|x l Hnotin Hnd IH].
  - constructor.
  - simpl. destruct (f x) eqn:Hfx.
    + constructor.
      * intro Habs. apply filter_In in Habs. destruct Habs as [Hin _]. contradiction.
      * exact IH.
    + exact IH.
Qed.

(* nbr_excluding has NoDup (filter of NoDup list) *)
Lemma nbr_excluding_NoDup : forall p S, NoDup (nbr_excluding p S).
Proof.
  intros p S.
  unfold nbr_excluding.
  apply filter_NoDup.
  apply neighbors_for_recursion_NoDup.
Qed.

(* Neighbor finiteness: built into sum_overlap_excluding (finite list) *)
Lemma nbr_excluding_finite : forall p S, (length (nbr_excluding p S) <= overlap_degree_bound)%nat.
Proof.
  intros p S.
  unfold nbr_excluding.
  apply Nat.le_trans with (length (neighbors_for_recursion p)).
  - apply filter_length_le.
  - apply neighbors_for_recursion_length.
Qed.

(* Exclude self: neighbors_for_recursion already excludes p *)
Lemma nbr_excluding_no_self : forall p S, ~ In p (nbr_excluding p S).
Proof.
  intros p S Hin.
  unfold nbr_excluding in Hin.
  apply filter_In in Hin.
  destruct Hin as [Hin Hpass].
  apply neighbors_for_recursion_spec in Hin.
  destruct Hin as [_ Hneq].
  contradiction.
Qed.

(* Membership spec: recursion only touches sum/prod_overlap_excluding *)
Lemma nbr_excluding_spec : forall p S q,
  In q (nbr_excluding p S) <-> overlap p q /\ q <> p /\ ~ In q S.
Proof.
  intros p S q.
  unfold nbr_excluding.
  rewrite filter_In.
  split.
  - intros [Hin Hpass].
    apply neighbors_for_recursion_spec in Hin.
    destruct Hin as [Hov Hneq].
    split; [exact Hov | split; [exact Hneq |]].
    destruct (in_dec eq_dec q S) as [HinS | Hnotin].
    + discriminate.
    + exact Hnotin.
  - intros [Hov [Hneq Hnin]].
    split.
    + apply neighbors_for_recursion_spec. split; assumption.
    + destruct (in_dec eq_dec q S) as [Hin' | _]; [contradiction | reflexivity].
Qed.

(* S ⊆ S' => nbr_excluding p S' ⊆ nbr_excluding p S (more forbidden => fewer neighbors) *)
Lemma nbr_excluding_antimono : forall p S S' q,
  (forall x, In x S -> In x S') ->
  In q (nbr_excluding p S') ->
  In q (nbr_excluding p S).
Proof.
  intros p S S' q Hsub Hin.
  apply nbr_excluding_spec in Hin.
  apply nbr_excluding_spec.
  destruct Hin as [Hov [Hneq Hnin']].
  split; [exact Hov | split; [exact Hneq |]].
  intro Hin. apply Hnin'. apply Hsub. exact Hin.
Qed.

(* Product monotonicity: multiplicative analogue of sum_list_map_monotone.
   If ∀q∈Nbr(p)\S, 0 ≤ f q ≤ g q, then ∏(1+f) ≤ ∏(1+g). *)
Lemma fold_right_Rmult_nonneg : forall (l : list P) (f : P -> R),
  (forall x, In x l -> 0 <= f x) ->
  0 <= fold_right Rmult 1 (map f l).
Proof.
  intros l f Hf.
  induction l as [|q qs IH]; simpl.
  - lra.
  - apply Rmult_le_pos; [apply Hf; left; reflexivity | apply IH; intros x Hx; apply Hf; right; exact Hx].
Qed.

Lemma fold_right_Rmult_mono : forall (l : list P) (f g : P -> R),
  (forall x, In x l -> 0 <= f x <= g x) ->
  fold_right Rmult 1 (map f l) <= fold_right Rmult 1 (map g l).
Proof.
  intros l f g Hfg.
  induction l as [|q qs IH]; simpl.
  - lra.
  - assert (Hq : 0 <= f q <= g q) by (apply Hfg; left; reflexivity).
    assert (Hqs : fold_right Rmult 1 (map f qs) <= fold_right Rmult 1 (map g qs))
      by (apply IH; intros x Hx; apply Hfg; right; exact Hx).
    assert (Hf_nonneg : 0 <= fold_right Rmult 1 (map f qs))
      by (apply fold_right_Rmult_nonneg; intros x Hx; destruct (Hfg x (or_intror Hx)) as [Hfx _]; exact Hfx).
    assert (Hg_nonneg : 0 <= fold_right Rmult 1 (map g qs))
      by (apply fold_right_Rmult_nonneg; intros x Hx;
          destruct (Hfg x (or_intror Hx)) as [Hfx Hfgx];
          apply Rle_trans with (f x); [exact Hfx | exact Hfgx]).
    destruct Hq as [Hfq Hfgq].
    apply Rmult_le_compat; [exact Hfq | exact Hf_nonneg | exact Hfgq | exact Hqs].
Qed.

Lemma prod_overlap_excluding_mono :
  forall p S (f g : P -> R),
    (forall q, In q (nbr_excluding p S) -> 0 <= f q <= g q) ->
    prod_overlap_excluding p S f <= prod_overlap_excluding p S g.
Proof.
  intros p S f g Hfg.
  unfold prod_overlap_excluding.
  apply fold_right_Rmult_mono.
  intros x Hx.
  apply Hfg. exact Hx.
Qed.

(* Corollary: (1+f) ≤ (1+g) pointwise => product bound *)
Lemma prod_overlap_excluding_mono_1plus :
  forall p S (f g : P -> R),
    (forall q, In q (nbr_excluding p S) -> 0 <= f q /\ 1 + f q <= 1 + g q) ->
    prod_overlap_excluding p S (fun q => 1 + f q) <=
    prod_overlap_excluding p S (fun q => 1 + g q).
Proof.
  intros p S f g Hfg.
  apply prod_overlap_excluding_mono.
  intros q Hin.
  destruct (Hfg q Hin) as [Hf Hle].
  split; [lra | exact Hle].
Qed.

(* Variant with explicit 0 <= g: avoids lra needing to derive it from f <= g *)
Lemma prod_overlap_excluding_mono_1plus' :
  forall p S (f g : P -> R),
    (forall q, In q (nbr_excluding p S) -> 0 <= f q /\ 0 <= g q /\ 1 + f q <= 1 + g q) ->
    prod_overlap_excluding p S (fun q => 1 + f q) <=
    prod_overlap_excluding p S (fun q => 1 + g q).
Proof.
  intros p S f g Hfg.
  apply prod_overlap_excluding_mono.
  intros q Hin.
  destruct (Hfg q Hin) as [Hf [Hg Hle]].
  split; [lra | exact Hle].
Qed.

(* =========================================================================
   3. Rooted-Tree Recursion Skeleton (Weitz / cluster-expansion style)

   T(p,S) = contribution of trees rooted at p avoiding polymers in S.
   Recursion: T(p,S) ≤ exp(a·size p) · ∏_{q∈Nbr(p)\S} (1 + T(q, S∪{p}))

   We use induction on depth k; no Fixpoint over trees yet.
   ========================================================================= *)

Variable a : R.
(* Needed for rooted_sum_le_rooted_upper when rooted_upper includes activity *)
Hypothesis activity_ge_1 : forall p, 1 <= activity p.

Inductive RootedTree : Type :=
| rt_leaf : P -> RootedTree
| rt_node : P -> list RootedTree -> RootedTree.

Parameter RootedTree_eq_dec : forall t u : RootedTree, {t = u} + {t <> u}.

Parameter tree_weight : RootedTree -> R.
Hypothesis tree_weight_leaf : forall p, tree_weight (rt_leaf p) = exp (a * size p).
Hypothesis tree_weight_node_nonneg : forall p children,
  (forall t, In t children -> 0 <= tree_weight t) ->
  0 <= tree_weight (rt_node p children).
Hypothesis tree_weight_nonneg : forall t, 0 <= tree_weight t.
(* One-sided bound: node weight ≤ root factor × product of child weights.
   Minimal assumption for rooted_sum_rec_bound; discharge when tree_weight is defined. *)
Hypothesis tree_weight_node_le : forall p children,
  tree_weight (rt_node p children)
  <= exp (a * size p) * fold_right Rmult 1 (map tree_weight children).
(* Empty-children node has weight 0; needed for rooted_sum_Sk_le_sum_over_sublists. *)
Hypothesis tree_weight_node_nil : forall p, tree_weight (rt_node p []) = 0.

Inductive is_rooted_tree_of_depth : nat -> P -> list P -> RootedTree -> Prop :=
| rt_depth_0 : forall p S, is_rooted_tree_of_depth 0 p S (rt_leaf p)
| rt_depth_succ : forall k p forbidden (children : list RootedTree) (qs : list P),
    Forall2 (fun t q => In q (nbr_excluding p forbidden) /\ is_rooted_tree_of_depth k q (p :: forbidden) t)
            children qs ->
    NoDup qs ->
    is_rooted_tree_of_depth (Datatypes.S k) p forbidden (rt_node p children).

Parameter trees_of_depth_at_most : nat -> P -> list P -> list RootedTree.
Hypothesis trees_of_depth_at_most_spec : forall k p S t,
  In t (trees_of_depth_at_most k p S) <-> is_rooted_tree_of_depth k p S t.
Hypothesis trees_of_depth_at_most_NoDup : forall k p S, NoDup (trees_of_depth_at_most k p S).

(* Cover: every tree of depth ≤ S k is either leaf or node with children from neighbors.
   qs is a filtered sublist of nbr_excluding (order preserved), so In qs (all_sublists ...). *)
Hypothesis trees_of_depth_at_most_succ_cover :
  forall k p forbidden t,
    In t (trees_of_depth_at_most (Datatypes.S k) p forbidden) ->
    t = rt_leaf p \/
    exists children qs (pred : P -> bool),
      t = rt_node p children /\
      qs = filter pred (nbr_excluding p forbidden) /\
      Forall2 (fun tr q =>
                 In q qs /\
                 In tr (trees_of_depth_at_most k q (p :: forbidden)))
              children qs.

Fixpoint sum_list (l : list R) : R :=
  match l with
  | [] => 0
  | x :: xs => x + sum_list xs
  end.

(* Helper: remove non-member is identity *)
Lemma remove_not_in_early {A : Type} (eqA : forall x y : A, {x = y} + {x <> y}) :
  forall (l : list A) (x : A), ~ In x l -> remove eqA x l = l.
Proof.
  intros l x Hnin. induction l as [|y l' IH]; simpl.
  - reflexivity.
  - destruct (eqA x y) as [Heq|Hneq].
    + subst. exfalso. apply Hnin. left. reflexivity.
    + f_equal. apply IH. intro Hc. apply Hnin. right. exact Hc.
Qed.

(* In elt l -> sum over l = f elt + sum over (remove elt l).
   Coq's List.remove removes ALL occurrences; hence we require NoDup. *)
Lemma sum_list_map_remove_one (A : Type) (eqA : forall x y : A, {x = y} + {x <> y}) :
  forall (l : list A) (elt : A) (f : A -> R),
    NoDup l -> In elt l ->
    sum_list (map f l) = f elt + sum_list (map f (remove eqA elt l)).
Proof.
  intros l elt f Hnd Hin.
  induction l as [|b l' IH]; [contradiction|].
  inversion Hnd as [|? ? Hnin Hnd']; subst.
  simpl. destruct (eqA elt b) as [Heq|Hneq].
  - subst. simpl. destruct (eqA b b) as [_|Hc]; [|contradiction].
    rewrite (remove_not_in_early eqA l' b Hnin). ring.
  - destruct Hin as [Heq'|Hin]; [subst; contradiction|].
    simpl. destruct (eqA elt b) as [Hc|_]; [subst; contradiction|].
    rewrite (IH Hnd' Hin). ring.
Qed.

(* When In elem l, sum over l = f elem + sum over (remove a l) - requires NoDup for remove-all *)
Lemma sum_list_map_remove (A : Type) (eqA : forall x y : A, {x = y} + {x <> y}) :
  forall (l : list A) (elt : A) (f : A -> R),
    NoDup l ->
    In elt l ->
    sum_list (map f l) = f elt + sum_list (map f (remove eqA elt l)).
Proof.
  intros l elt f Hnd Hin.
  induction l as [|b l' IHl]; [contradiction |].
  inversion Hnd as [|? ? Hnin Hnd']. subst.
  simpl.
  destruct (eqA elt b) as [Heq|Hneq].
  - subst.
    simpl.
    destruct (eqA b b) as [_|Hcontra]; [|contradiction].
    assert (Hrm : remove eqA b l' = l').
    { assert (Hrm_aux : forall l0 : list A, ~ In b l0 -> remove eqA b l0 = l0).
      { induction l0 as [|c l0 IH0]; intros Hnotin; simpl.
        - reflexivity.
        - destruct (eqA b c) as [Heqbc|Hneqbc].
          + subst. exfalso. apply Hnotin. left. reflexivity.
          + f_equal.
            apply IH0.
            intro Hc. apply Hnotin. right. exact Hc. }
      apply Hrm_aux. exact Hnin. }
    rewrite Hrm. reflexivity.
  - destruct Hin as [Heq'|Hin'].
    { subst. contradiction. }
    simpl.
    destruct (eqA elt b) as [Hcontra|_].
    { exfalso. apply Hneq. exact Hcontra. }
    rewrite IHl by assumption.
    ring.
Qed.

Lemma sum_list_map_nonneg (A : Type) :
  forall (l : list A) (f : A -> R),
    (forall x, In x l -> 0 <= f x) ->
    0 <= sum_list (map f l).
Proof.
  intros l f Hf.
  induction l as [|x xs IH]; simpl.
  - lra.
  - apply Rplus_le_le_0_compat.
    + apply Hf. left. reflexivity.
    + apply IH. intros y Hy. apply Hf. right. exact Hy.
Qed.

(* If x is not in l, remove does nothing *)
Lemma remove_notin (A : Type) (eqA : forall x y : A, {x = y} + {x <> y}) :
  forall (l : list A) (x : A), ~ In x l -> remove eqA x l = l.
Proof.
  intros l x Hnotin.
  induction l as [|hd tl IH]; simpl.
  - reflexivity.
  - destruct (eqA x hd) as [Heq | Hneq].
    + subst. exfalso. apply Hnotin. left. reflexivity.
    + f_equal. apply IH. intro Hin. apply Hnotin. right. exact Hin.
Qed.

(* NoDup is preserved through remove *)
Lemma NoDup_remove_elt (A : Type) (eqA : forall x y : A, {x = y} + {x <> y}) :
  forall (l : list A) (x : A), NoDup l -> NoDup (remove eqA x l).
Proof.
  intros l x Hnd. induction l as [|hd tl IH]; simpl.
  - constructor.
  - inversion Hnd as [|? ? Hnin Hnd']. subst.
    destruct (eqA x hd) as [Heq|Hneq].
    + apply IH. exact Hnd'.
    + constructor.
      * intro Hc. apply in_remove in Hc. destruct Hc as [Hc _]. contradiction.
      * apply IH. exact Hnd'.
Qed.

(* Helper: remove non-member is identity *)
Lemma remove_not_in {A : Type} (eqA : forall x y : A, {x = y} + {x <> y}) :
  forall (l : list A) (x : A), ~ In x l -> remove eqA x l = l.
Proof.
  intros l x Hnin. induction l as [|y l' IH]; simpl.
  - reflexivity.
  - destruct (eqA x y) as [Heq|Hneq].
    + subst. exfalso. apply Hnin. left. reflexivity.
    + f_equal. apply IH. intro Hc. apply Hnin. right. exact Hc.
Qed.

(* In x (remove y l) -> In x l. Transport membership without NoDup. *)
Lemma In_remove_elim (A : Type) (eqA : forall x y : A, {x = y} + {x <> y}) :
  forall (x y : A) (l : list A), In x (remove eqA y l) -> In x l.
Proof. intros x y l Hx. apply in_remove in Hx. destruct Hx as [Hin _]. exact Hin. Qed.

(* Product analogue of sum_list_map_remove: factor out one element *)
Lemma prod_map_remove_factor (A : Type) (eqA : forall x y : A, {x = y} + {x <> y}) :
  forall (l : list A) (f : A -> R) (elem : A),
    NoDup l ->
    In elem l ->
    fold_right Rmult 1 (map f l)
    = f elem * fold_right Rmult 1 (map f (remove eqA elem l)).
Proof.
  intros l f elem Hnd Hin.
  induction Hnd as [|x xs Hnotin Hnd IH]; simpl in *.
  - contradiction.
  - destruct Hin as [Hin|Hin].
    + subst x.
      simpl. destruct (eqA elem elem) as [_|Hneq]; [|contradiction].
      rewrite remove_not_in by exact Hnotin. ring.
    + simpl. destruct (eqA elem x) as [Heq|Hneq].
      * subst x. contradiction.
      * rewrite IH by exact Hin. simpl. ring.
Qed.

(* Sum over included list: incl l1 l2 + NoDup l1 + NoDup l2 + nonneg f on l2 => sum l1 <= sum l2.
   NoDup l2 required because List.remove removes all occurrences. *)
Lemma sum_list_map_incl_nodupfree (A : Type) (eqA : forall x y : A, {x = y} + {x <> y}) :
  forall (l1 l2 : list A) (f : A -> R),
    incl l1 l2 -> NoDup l1 -> NoDup l2 ->
    (forall x, In x l2 -> 0 <= f x) ->
    sum_list (map f l1) <= sum_list (map f l2).
Proof.
  intros l1 l2 f Hincl Hnd1 Hnd2 Hf. revert l2 Hincl Hnd2 Hf.
  induction l1 as [|hd l1' IH]; intros l2 Hincl Hnd2 Hf; simpl.
  - apply sum_list_map_nonneg. exact Hf.
  - inversion Hnd1 as [|? ? Hnin Hnd1']. subst.
    assert (Hhd : In hd l2) by (apply Hincl; left; reflexivity).
    rewrite (sum_list_map_remove A eqA l2 hd f Hnd2 Hhd).
    assert (Hnd2' : NoDup (remove eqA hd l2)) by (apply NoDup_remove_elt; exact Hnd2).
    assert (Hincl' : incl l1' (remove eqA hd l2)).
    { intros z Hz. apply in_in_remove; [intro Heq; subst; contradiction | apply Hincl; right; exact Hz]. }
    assert (Hf' : forall x, In x (remove eqA hd l2) -> 0 <= f x).
    { intros x Hx. apply Hf. apply (In_remove_elim A eqA x hd l2). exact Hx. }
    specialize (IH Hnd1' (remove eqA hd l2) Hincl' Hnd2' Hf').
    lra.
Qed.

(* Sum over included list: incl l1 l2 + NoDup both + nonneg f => sum l1 <= sum l2 *)
Lemma sum_list_map_incl (A : Type) (eqA : forall x y : A, {x = y} + {x <> y}) :
  forall (l1 l2 : list A) (f : A -> R),
    incl l1 l2 -> NoDup l1 -> NoDup l2 ->
    (forall x, In x l2 -> 0 <= f x) ->
    sum_list (map f l1) <= sum_list (map f l2).
Proof.
  intros l1 l2 f Hincl Hnd1 Hnd2 Hf. revert l2 Hincl Hnd2 Hf.
  induction l1 as [|hd l1' IH]; intros l2 Hincl Hnd2 Hf; simpl.
  - apply sum_list_map_nonneg. exact Hf.
  - inversion Hnd1 as [|? ? Hnin Hnd1']. subst.
    assert (Hhd : In hd l2) by (apply Hincl; left; reflexivity).
    rewrite (sum_list_map_remove A eqA l2 hd f Hnd2 Hhd).
    assert (Hincl' : incl l1' (remove eqA hd l2)).
    { intros z Hz. apply in_in_remove; [intro Heq; subst; contradiction | apply Hincl; right; exact Hz]. }
    assert (Hnd2' : NoDup (remove eqA hd l2)) by (apply NoDup_remove_elt; exact Hnd2).
    assert (Hf' : forall z, In z (remove eqA hd l2) -> 0 <= f z).
    { intros z Hz. apply Hf. apply in_remove in Hz. destruct Hz as [Hz _]. exact Hz. }
    specialize (IH Hnd1' (remove eqA hd l2) Hincl' Hnd2' Hf').
    apply Rplus_le_compat; [apply Rle_refl | exact IH].
Qed.

(* Sum over sublists: Σ_{S⊆L} ∏_{x∈S} F(x) = ∏_{x∈L} (1 + F(x)).
   Used for independent-choice relaxation in rooted_sum_rec_bound. *)
Fixpoint sum_over_sublists {A : Type} (L : list A) (F : A -> R) : R :=
  match L with
  | [] => 1
  | x :: xs => sum_over_sublists xs F + F x * sum_over_sublists xs F
  end.

Lemma fold_right_Rmult_nonneg_gen (A : Type) (l : list A) (f : A -> R) :
  (forall x, In x l -> 0 <= f x) ->
  0 <= fold_right Rmult 1 (map f l).
Proof.
  intros Hf. induction l as [|hd tl IH]; simpl; [lra|].
  apply Rmult_le_pos; [apply Hf; left; reflexivity | apply IH; intros x Hx; apply Hf; right; exact Hx].
Qed.

Lemma sum_over_sublists_eq_prod_1plus (A : Type) :
  forall (L : list A) (F : A -> R),
    (forall x, In x L -> 0 <= F x) ->
    sum_over_sublists L F = fold_right Rmult 1 (map (fun x => 1 + F x) L).
Proof.
  intros L F HF.
  induction L as [|hd tl IH]; simpl.
  - reflexivity.
  - rewrite IH by (intros y Hy; apply HF; right; exact Hy).
    ring_simplify. reflexivity.
Qed.

Lemma sum_over_sublists_nonneg (A : Type) :
  forall (L : list A) (F : A -> R),
    (forall x, In x L -> 0 <= F x) ->
    0 <= sum_over_sublists L F.
Proof.
  intros L F HF.
  induction L as [|y ys IH]; simpl.
  - lra.
  - assert (Hsub : 0 <= sum_over_sublists ys F).
    { apply IH. intros z Hz. apply HF. right. exact Hz. }
    assert (HFy : 0 <= F y) by (apply HF; left; reflexivity).
    nra.
Qed.

(* Product over a NoDup sublist is <= sum_over_sublists *)
Lemma prod_over_sublist_le_sum_over_sublists (A : Type) (eqA : forall x y : A, {x = y} + {x <> y}) :
  forall (L qs : list A) (F : A -> R),
    NoDup qs ->
    (forall x, In x qs -> In x L) ->
    (forall x, In x L -> 0 <= F x) ->
    fold_right Rmult 1 (map F qs) <= sum_over_sublists L F.
Proof.
  induction L as [|x xs IH]; intros qs F Hndup Hsub Hnonneg; simpl.
  - assert (qs = []).
    { destruct qs as [|q qs']; [reflexivity|].
      exfalso. specialize (Hsub q (or_introl eq_refl)). contradiction.
    }
    subst qs. simpl. lra.
  - destruct (in_dec eqA x qs) as [Hx_in|Hx_notin].
    + set (qs' := remove eqA x qs).
      assert (Hndup' : NoDup qs').
      { subst qs'. apply NoDup_remove_elt. exact Hndup. }
      assert (Hsub' : forall y, In y qs' -> In y xs).
      { intros y Hy. apply in_remove in Hy. destruct Hy as [Hy_in Hneq].
        specialize (Hsub y Hy_in). simpl in Hsub.
        destruct Hsub as [Hyx|Hyxs]; [subst y; contradiction|exact Hyxs]. }
      assert (Hnonneg_xs : forall y, In y xs -> 0 <= F y).
      { intros y Hy. apply Hnonneg. right. exact Hy. }
      specialize (IH qs' F Hndup' Hsub' Hnonneg_xs).
      assert (Hprod : fold_right Rmult 1 (map F qs) = F x * fold_right Rmult 1 (map F qs')).
      { subst qs'. apply (prod_map_remove_factor A eqA qs F x); assumption. }
      rewrite Hprod.
      set (S := sum_over_sublists xs F).
      assert (HFx : 0 <= F x) by (apply Hnonneg; left; reflexivity).
      assert (Hleq : F x * fold_right Rmult 1 (map F qs') <= F x * S).
      { apply Rmult_le_compat_l. exact HFx. unfold S. exact IH. }
      assert (HS_nonneg : 0 <= S).
      { unfold S. apply sum_over_sublists_nonneg. intros y Hy. apply Hnonneg. right. exact Hy. }
      lra.
    + assert (Hsub' : forall y, In y qs -> In y xs).
      { intros y Hy. specialize (Hsub y Hy). simpl in Hsub.
        destruct Hsub as [Hyx|Hyxs]; [subst y; contradiction|exact Hyxs]. }
      assert (Hnonneg_xs : forall y, In y xs -> 0 <= F y).
      { intros y Hy. apply Hnonneg. right. exact Hy. }
      specialize (IH qs F Hndup Hsub' Hnonneg_xs).
      set (S := sum_over_sublists xs F) in *.
      assert (HS_nonneg : 0 <= S).
      { unfold S. apply sum_over_sublists_nonneg. exact Hnonneg_xs. }
      assert (HFx : 0 <= F x) by (apply Hnonneg; left; reflexivity).
      assert (Hrhs : S <= S + F x * S) by nra.
      lra.
Qed.

Definition rooted_sum (k : nat) (p : P) (forbidden : list P) : R :=
  sum_list (map tree_weight (trees_of_depth_at_most k p forbidden)).

(* Definitional majorant: the recursion RHS. Activity-weighted for KP control.
   Proves rooted_sum_rec_bound via rooted_sum_le_rooted_upper (requires activity >= 1). *)
Fixpoint rooted_upper (k : nat) (p : P) (forbidden : list P) : R :=
  match k with
  | 0 => activity p * exp (a * size p)
  | S k' => activity p * exp (a * size p) *
            prod_overlap_excluding p forbidden (fun q => 1 + rooted_upper k' q (p :: forbidden))
  end.

Lemma sum_list_nonneg (l : list R) : (forall x, In x l -> 0 <= x) -> 0 <= sum_list l.
Proof.
  induction l as [|x xs IH]; simpl; intros Hnonneg; [lra|].
  apply Rplus_le_le_0_compat; [apply Hnonneg; left; reflexivity | apply IH; intros y Hy; apply Hnonneg; right; exact Hy].
Qed.

Lemma rooted_sum_nonneg : forall k p forbidden, 0 <= rooted_sum k p forbidden.
Proof.
  intros k p forbidden. unfold rooted_sum.
  apply sum_list_nonneg. intros t Ht. apply in_map_iff in Ht. destruct Ht as [tr [Heq Hin]]. subst. apply tree_weight_nonneg.
Qed.

Lemma rooted_upper_nonneg : forall k p forbidden, 0 <= rooted_upper k p forbidden.
Proof.
  induction k as [|k' IH]; intros p forbidden; unfold rooted_upper; simpl.
  - (* 0 <= activity p * exp *)
    eapply Rmult_le_pos. apply Rge_le, activity_nonneg. apply Rlt_le. apply exp_pos.
  - (* 0 <= (activity p * exp) * prod *)
    apply Rmult_le_pos.
    + eapply Rmult_le_pos. apply Rge_le, activity_nonneg. apply Rlt_le. apply exp_pos.
    + apply fold_right_Rmult_nonneg.
      intros q Hq. apply Rle_trans with 1.
      * lra.
      * replace 1 with (1 + 0) at 1 by ring. apply Rplus_le_compat_l. apply IH.
Qed.

(* In a nonnegative sum, each term ≤ total *)
Lemma sum_list_map_elt_le (A : Type) (l : list A) (f : A -> R) (x : A) :
  In x l ->
  (forall y, In y l -> 0 <= f y) ->
  f x <= sum_list (map f l).
Proof.
  intros Hin Hf.
  induction l as [|hd l' IH]; [contradiction |].
  destruct Hin as [Heq|Hin']; [subst; simpl |].
  - rewrite <- Rplus_0_r at 1. apply Rplus_le_compat_l.
    apply sum_list_nonneg. intros r Hr. apply in_map_iff in Hr. destruct Hr as [z [Heq Hz]]. subst.
    apply Hf. right. exact Hz.
  - simpl. eapply Rle_trans. apply IH; [exact Hin' | intros z Hz; apply Hf; right; exact Hz].
    assert (Hhd : 0 <= f hd) by (apply Hf; left; reflexivity). lra.
Qed.

Lemma tree_weight_le_rooted_sum :
  forall k q forb tr,
    In tr (trees_of_depth_at_most k q forb) ->
    tree_weight tr <= rooted_sum k q forb.
Proof.
  intros k q forb tr Hin. unfold rooted_sum.
  apply sum_list_map_elt_le; [exact Hin | intros t _; apply tree_weight_nonneg].
Qed.

Lemma sum_list_map_monotone (A : Type) (l : list A) (f g : A -> R) :
  (forall x, In x l -> f x <= g x) ->
  sum_list (map f l) <= sum_list (map g l).
Proof.
  induction l as [|x xs IH]; intros Hfg; simpl.
  - lra.
  - assert (Hx : f x <= g x) by (apply Hfg; left; reflexivity).
    assert (Hxs : sum_list (map f xs) <= sum_list (map g xs)) by (apply IH; intros y Hy; apply Hfg; right; exact Hy).
    lra.
Qed.

(* Forall2 P children qs with P tr q := tree_weight tr <= F q => product bound *)
Lemma Forall2_fold_right_Rmult_le (A B : Type) (children : list A) (qs : list B)
  (f : A -> R) (g : B -> R) :
  Forall2 (fun x y => f x <= g y) children qs ->
  (forall x, In x children -> 0 <= f x) ->
  (forall y, In y qs -> 0 <= g y) ->
  fold_right Rmult 1 (map f children) <= fold_right Rmult 1 (map g qs).
Proof.
  intros Hfa Hf Hg.
  induction Hfa as [|x y xs ys Hxy Hfa' IH]; simpl.
  - lra.
  - apply Rmult_le_compat.
    + apply Hf. left. reflexivity.
    + apply fold_right_Rmult_nonneg_gen. intros z Hz. apply Hf. right. exact Hz.
    + exact Hxy.
    + apply IH; [intros z Hz; apply Hf; right; exact Hz | intros z Hz; apply Hg; right; exact Hz].
Qed.

(* Moved rooted_sum_le_rooted_upper downwards *)

(* Product over sublist <= product over full list when each factor >= 1 *)
Lemma fold_right_Rmult_ge_1 (l : list P) (f : P -> R) :
  (forall x, In x l -> 1 <= f x) ->
  1 <= fold_right Rmult 1 (map f l).
Proof.
  intros Hf. induction l as [|x xs IH]; simpl.
  - lra.
  - assert (Hfx_ge_1 : 1 <= f x) by (apply Hf; left; reflexivity).
    assert (Hprod_ge_1 : 1 <= fold_right Rmult 1 (map f xs)) by (apply IH; intros y Hy; apply Hf; right; exact Hy).
    assert (Hfx_pos : 0 <= f x) by lra.
    assert (Hprod_pos : 0 <= fold_right Rmult 1 (map f xs)) by lra.
    replace 1 with (1 * 1) at 1 by ring.
    apply Rmult_le_compat; lra.
Qed.

Lemma prod_sublist_le_prod_1plus :
  forall k p forbidden (qs : list P),
    NoDup qs ->
    (forall q, In q qs -> In q (nbr_excluding p forbidden)) ->
    (forall q, In q qs -> rooted_sum k q (p :: forbidden) <= rooted_upper k q (p :: forbidden)) ->
    fold_right Rmult 1 (map (fun q => rooted_sum k q (p :: forbidden)) qs)
    <= prod_overlap_excluding p forbidden (fun q => 1 + rooted_upper k q (p :: forbidden)).
Proof.
  intros k p forbidden qs Hndqs Hsub Hmono.
  set (L := nbr_excluding p forbidden).
  (* Step 1: ∏_{q∈qs} rooted_sum q <= sum_over_sublists L rooted_upper *)
  assert (Hstep1 : fold_right Rmult 1 (map (fun q => rooted_sum k q (p :: forbidden)) qs)
           <= sum_over_sublists L (fun q => rooted_upper k q (p :: forbidden))).
  {
    eapply Rle_trans.
    - (* Bound rooted_sum by rooted_upper pointwise *)
      apply fold_right_Rmult_mono.
      intros q Hq.
      split.
      + apply rooted_sum_nonneg.
      + apply Hmono. exact Hq.
    - apply (prod_over_sublist_le_sum_over_sublists P eq_dec L qs).
      + exact Hndqs.
      + exact Hsub.
      + intros q Hq. apply rooted_upper_nonneg.
  }
  (* Step 2: sum_over_sublists L rooted_upper = prod_overlap_excluding (1+rooted_upper) *)
  unfold prod_overlap_excluding, L.
  rewrite <- sum_over_sublists_eq_prod_1plus.
  - exact Hstep1.
  - intros q Hq. apply rooted_upper_nonneg.
Qed.

(* =========================================================================
   EXPLICIT MAJORANT ENUMERATION (Option A)
   gen_trees_Sk k p forb = all trees built by independent choices from neighbor sublists
   ========================================================================= *)

(* All sublists of elem list *)
Fixpoint all_sublists {A : Type} (L : list A) : list (list A) :=
  match L with
  | [] => [[]]
  | x :: xs => all_sublists xs ++ map (cons x) (all_sublists xs)
  end.

(* Cartesian product: all ways to pick one from each list *)
Fixpoint all_choices {A : Type} (lists : list (list A)) : list (list A) :=
  match lists with
  | [] => [[]]
  | l :: ls => flat_map (fun x => map (cons x) (all_choices ls)) l
  end.

(* Majorant enumeration: leaf + all nodes from all sublists × all choices *)
Definition gen_trees_Sk (k : nat) (p : P) (forb : list P) : list RootedTree :=
  rt_leaf p ::
  flat_map (fun qs =>
    map (rt_node p) (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs)))
  (all_sublists (nbr_excluding p forb)).

Hypothesis gen_trees_Sk_NoDup : forall k p forb, NoDup (gen_trees_Sk k p forb).

(* Helper: all_sublists contains empty *)
Lemma all_sublists_nil {A : Type} (L : list A) : In [] (all_sublists L).
Proof.
  induction L as [|x xs IH]; simpl.
  - left. reflexivity.
  - apply in_app_iff. left. exact IH.
Qed.

(* In x (filter p l) -> In x l. Reduces plumbing when using filter. *)
Lemma In_filter_implies_In {A : Type} (p : A -> bool) (x : A) (l : list A) :
  In x (filter p l) -> In x l.
Proof.
  intros Hx. apply filter_In in Hx. destruct Hx as [Hx _]. exact Hx.
Qed.

(* Forall2 R children qs -> qs = filter pred L -> forall q, In q qs -> In q L *)
Lemma Forall2_filter_In {A B : Type} (R : A -> B -> Prop) (children : list A) (qs : list B)
  (pred : B -> bool) (L : list B) :
  qs = filter pred L ->
  Forall2 R children qs ->
  forall q, In q qs -> In q L.
Proof.
  intros Heq _ q Hq. subst qs. apply (In_filter_implies_In pred). exact Hq.
Qed.

(* Every filter-result is a subsequence; all_sublists enumerates subsequences. *)
Lemma filter_in_all_sublists {A : Type} (pred : A -> bool) :
  forall (L : list A), In (filter pred L) (all_sublists L).
Proof.
  induction L as [|x xs IH]; simpl.
  - left. reflexivity.
  - destruct (pred x) eqn:Hpred; simpl.
    + apply in_or_app. right. apply in_map. exact IH.
    + apply in_or_app. left. exact IH.
Qed.

(* Forall2 R la lb -> In b lb -> exists a, In a la /\ R a b *)
Lemma Forall2_in_right {A B : Type} (R : A -> B -> Prop) :
  forall la lb b, Forall2 R la lb -> In b lb -> exists a, In a la /\ R a b.
Proof.
  intros la lb b Hfa Hin. revert b Hin.
  induction Hfa as [|a' b' la' lb' Hab' Hfa' IH]; intros b Hin; simpl in Hin; [contradiction|].
  destruct Hin as [Heq|Hin].
  - subst. exists a'. split; [left; reflexivity|exact Hab'].
  - destruct (IH _ Hin) as [aa [Haa Raa]]. exists aa. split; [right; exact Haa|exact Raa].
Qed.

(* Forall2 (fun a b => In a (f b)) la lb -> Forall2 (fun a b => In a b) la (map f lb) *)
Lemma Forall2_map_in {A B : Type} (f : B -> list A) :
  forall (la : list A) (lb : list B),
    Forall2 (fun a b => In a (f b)) la lb ->
    Forall2 (fun a b => In a b) la (map f lb).
Proof.
  intros la lb Hfa. induction Hfa as [|aa bb la' lb' Hab Hfa' IH]; simpl; constructor.
  - exact Hab.
  - exact IH.
Qed.

(* Forall2 (fun c l => In c l) children lists => In children (all_choices lists) *)
Lemma Forall2_In_all_choices {A : Type} :
  forall (lists : list (list A)) (children : list A),
    length children = length lists ->
    Forall2 (fun c l => In c l) children lists ->
    In children (all_choices lists).
Proof.
  intros lists children Hlen Hfa.
  revert children Hlen Hfa.
  induction lists as [|l ls IH]; intros children Hlen Hfa.
  - inversion Hfa. simpl. left. reflexivity.
  - inversion Hfa as [|c l' cs ls' Hc Hfa']. subst.
    simpl. apply in_flat_map. exists c. split.
    + exact Hc.
    + apply in_map. apply IH.
      * injection Hlen. auto.
      * exact Hfa'.
Qed.

(* Helper: sum over append *)
Lemma sum_list_app (l1 l2 : list R) : sum_list (l1 ++ l2) = sum_list l1 + sum_list l2.
Proof.
  induction l1 as [|x xs IH]; simpl.
  - lra.
  - rewrite IH. lra.
Qed.

(* sum_list (map (fun a => c * f a) l) = c * sum_list (map f l) *)
Lemma sum_list_map_mult_const (A : Type) (c : R) (f : A -> R) (l : list A) :
  sum_list (map (fun a => c * f a) l) = c * sum_list (map f l).
Proof.
  induction l as [|x xs IH]; simpl; [ring|].
  rewrite IH. ring.
Qed.

(* Helper: sum over flat_map *)
Lemma sum_list_flat_map {A B : Type} (g : A -> list B) (f : B -> R) (l : list A) :
  sum_list (map f (flat_map g l)) = sum_list (map (fun a => sum_list (map f (g a))) l).
Proof.
  induction l as [|x xs IH]; simpl.
  - reflexivity.
  - rewrite map_app, sum_list_app. rewrite IH. reflexivity.
Qed.

(* H3: Sum over all_choices factorizes into product of sums
   Σ_{children ∈ all_choices [l1,...,ln]} ∏ f(children) = ∏ (Σ_{x∈li} f(x)) *)
Lemma all_choices_sum_prod_factorizes {A : Type} (f : A -> R) :
  forall (lists : list (list A)),
    (forall l, In l lists -> forall x, In x l -> 0 <= f x) ->
    sum_list (map (fun children => fold_right Rmult 1 (map f children)) (all_choices lists)) =
    fold_right Rmult 1 (map (fun l => sum_list (map f l)) lists).
Proof.
  intros lists Hnonneg.
  induction lists as [|l ls IH]; simpl.
  - ring.
  - (* all_choices (l :: ls) = flat_map (fun x => map (cons x) (all_choices ls)) l *)
    rewrite sum_list_flat_map.
    (* Inner sum: sum over map (cons a) (all_choices ls) of prod = f a * sum over all_choices ls of prod *)
    assert (Hinner : forall x,
      sum_list (map (fun children => fold_right Rmult 1 (map f children))
                    (map (cons x) (all_choices ls))) =
      f x * sum_list (map (fun cs => fold_right Rmult 1 (map f cs)) (all_choices ls))).
    { intro x.
      rewrite map_map.
      (* prod (x::cs) = f x * prod cs *)
      replace (map (fun cs => fold_right Rmult 1 (map f (x :: cs))) (all_choices ls))
        with (map (fun cs => f x * fold_right Rmult 1 (map f cs)) (all_choices ls))
        by (apply map_ext; intro cs; simpl; ring).
      apply sum_list_map_mult_const. }
    (* Replace inner sums via Hinner *)
    replace (map (fun x => sum_list (map (fun children => fold_right Rmult 1 (map f children))
                                        (map (cons x) (all_choices ls)))) l)
      with (map (fun x => f x * sum_list (map (fun cs => fold_right Rmult 1 (map f cs))
                                              (all_choices ls))) l).
    2: { apply map_ext. intro x. symmetry. apply Hinner. }
    (* Apply IH *)
    rewrite IH.
    2: { intros l' Hl' y Hy. apply (Hnonneg l' (or_intror Hl') y Hy). }
    (* Step 5: Factor out the constant product *)
    set (rhs := fold_right Rmult 1 (map (fun l0 => sum_list (map f l0)) ls)).
    (* f z * rhs = rhs * f z via commutativity *)
    assert (Hswap : map (fun z => f z * rhs) l = map (fun z => rhs * f z) l).
    { apply map_ext_in. intros z Hz. apply Rmult_comm. }
    rewrite Hswap.
    rewrite (sum_list_map_mult_const A rhs f l).
    simpl. ring.
Qed.

(* Every tree of depth S k is in the generator list *)
Lemma gen_trees_cover :
  forall k p forbidden t,
    In t (trees_of_depth_at_most (Datatypes.S k) p forbidden) ->
    In t (gen_trees_Sk k p forbidden).
Proof.
  intros k p forbidden t Ht.
  destruct (trees_of_depth_at_most_succ_cover k p forbidden t Ht) as [Hleaf|Hnode].
  - subst t. unfold gen_trees_Sk. simpl. left. reflexivity.
  - destruct Hnode as [children [qs [pred [-> [Heq Hfa]]]]].
    unfold gen_trees_Sk. simpl. right.
    apply in_flat_map. exists qs. split.
    + subst qs. apply filter_in_all_sublists.
    + apply in_map. apply Forall2_In_all_choices.
      * apply Forall2_length in Hfa. rewrite map_length. exact Hfa.
      * apply Forall2_map_in. eapply Forall2_impl; [|exact Hfa].
        intros tr q [Hq Hin]. exact Hin.
Qed.

(* sum_list (map (fun qs => ∏_{q∈qs} F q) (all_sublists L)) = sum_over_sublists L F *)
Lemma sum_over_sublists_as_sum {A : Type} (L : list A) (F : A -> R) :
  sum_list (map (fun qs => fold_right Rmult 1 (map F qs)) (all_sublists L)) =
  sum_over_sublists L F.
Proof.
  induction L as [|x xs IH]; simpl.
  - lra.
  - (* all_sublists (x::xs) = all_sublists xs ++ map (cons x) (all_sublists xs) *)
    rewrite map_app. rewrite sum_list_app.
    rewrite map_map.
    replace (map (fun qs => fold_right Rmult 1 (map F (x :: qs))) (all_sublists xs))
      with (map (fun qs => F x * fold_right Rmult 1 (map F qs)) (all_sublists xs)).
    2: { apply map_ext. intro qs. simpl. ring. }
    rewrite (sum_list_map_mult_const (list A) (F x) (fun qs => fold_right Rmult 1 (map F qs)) (all_sublists xs)).
    rewrite IH. ring.
Qed.

(* all_sublists L = [] :: tl for some tl *)
Lemma all_sublists_cons_nil {A : Type} (L : list A) :
  exists tl, all_sublists L = [] :: tl.
Proof.
  induction L as [|x xs [tl IH]]; simpl.
  - exists []. reflexivity.
  - exists (tl ++ map (cons x) (all_sublists xs)). rewrite IH. reflexivity.
Qed.

(* sum_list (map (fun qs => ∏) (tl (all_sublists L))) = sum_over_sublists L F - 1 *)
Lemma sum_over_sublists_tl {A : Type} (L : list A) (F : A -> R) :
  sum_list (map (fun qs => fold_right Rmult 1 (map F qs)) (tl (all_sublists L))) =
  sum_over_sublists L F - 1.
Proof.
  destruct (all_sublists_cons_nil L) as [rest Heq]. rewrite Heq. simpl.
  (* Goal: sum_list (map ... rest) = sum_over_sublists L F - 1 *)
  (* all_sublists L = [] :: rest, so sum over all_sublists = 1 + sum over rest *)
  assert (Hsum : sum_list (map (fun qs => fold_right Rmult 1 (map F qs)) ([] :: rest))
              = 1 + sum_list (map (fun qs => fold_right Rmult 1 (map F qs)) rest)).
  { simpl. ring. }
  rewrite <- Heq in Hsum. rewrite sum_over_sublists_as_sum in Hsum.
  lra.
Qed.

(* Helper: bound on sum over gen_trees_Sk node terms *)
Lemma sum_gen_trees_Sk_le :
  forall k p forb,
    sum_list (map tree_weight (gen_trees_Sk k p forb)) <=
    exp (a * size p) *
    sum_over_sublists (nbr_excluding p forb) (fun q => rooted_sum k q (p :: forb)).
Proof.
  intros k p forb.
  unfold gen_trees_Sk. simpl.
  rewrite tree_weight_leaf.
  set (L := nbr_excluding p forb).
  set (F := fun q => rooted_sum k q (p :: forb)).
  (* RHS: exp * sum_over_sublists L F = exp * (1 + sum_over_sublists_tail) *)
  (* LHS: exp + sum over flat_map of node weights *)
  rewrite sum_list_flat_map.
  
  (* Break all_sublists L into [] :: rest *)
  destruct (all_sublists_cons_nil L) as [rest Hrest].
  rewrite Hrest. simpl.

  (* First term of sum_list map is for [] *)
  (* map (rt_node p) [ [] ] = [ rt_node p [] ] *)
  rewrite tree_weight_node_nil.
  rewrite Rplus_0_l.
  rewrite Rplus_0_l.

  (* Now we bound the rest of the node terms *)
  assert (Hnode_bound :
    sum_list (map (fun qs => sum_list (map tree_weight
      (map (rt_node p) (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs)))))
      rest)
    <= exp (a * size p) *
      sum_list (map (fun qs => sum_list (map (fun children => fold_right Rmult 1 (map tree_weight children))
        (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs))))
        rest)).
  {
    assert (Hexp_pos : 0 < exp (a * size p)) by apply exp_pos.
    assert (Hinner_le : forall qs,
      sum_list (map tree_weight
        (map (rt_node p) (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs))))
      <= exp (a * size p) *
        sum_list (map (fun children => fold_right Rmult 1 (map tree_weight children))
          (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs)))).
    { intro qs. rewrite map_map.
      eapply Rle_trans.
      - apply sum_list_map_monotone.
        intros children _. apply tree_weight_node_le.
      - induction (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs)) as [|cs css IHcs];
          simpl; [lra|]. lra.
    }
    clear Hrest.
    induction rest as [|qs0 rest' IHr]; simpl; [lra|].
    pose proof (Hinner_le qs0) as Hinner0.
    assert (Hprod_nonneg : 0 <= sum_list (map (fun children => fold_right Rmult 1 (map tree_weight children))
      (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs0)))).
    { apply sum_list_nonneg. intros r Hr. apply in_map_iff in Hr. destruct Hr as [cs [Heq Hin]]. subst.
      apply fold_right_Rmult_nonneg_gen. intros t Ht. apply tree_weight_nonneg. }
    nra.
  }

  assert (Hfact :
    forall qs,
    sum_list (map (fun children => fold_right Rmult 1 (map tree_weight children))
      (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs))) =
    fold_right Rmult 1 (map F qs)).
  {
    intro qs.
    rewrite (all_choices_sum_prod_factorizes tree_weight
      (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs)).
    - rewrite map_map. reflexivity.
    - intros l' Hl' x Hx. apply tree_weight_nonneg.
  }

  assert (Hrewrite :
    sum_list (map (fun qs => sum_list (map (fun children => fold_right Rmult 1 (map tree_weight children))
      (all_choices (map (fun q => trees_of_depth_at_most k q (p :: forb)) qs))))
      rest) =
    sum_list (map (fun qs => fold_right Rmult 1 (map F qs)) rest)).
  { apply f_equal. apply map_ext. intro qs. apply Hfact. }

  rewrite Hrewrite in Hnode_bound.
  
  pose proof (sum_over_sublists_tl L F) as Htl.
  rewrite Hrest in Htl. simpl in Htl.
  
  rewrite Htl in Hnode_bound.

  (* DEBUG: if nra fails, uncomment to see goal (coqc batch mode):
     Fail assert False by (idtac).
     Or: match goal with |- ?G => idtac "GOAL:" G end; Fail assert False by exact I. *)

  nra.
Qed.

(* Direct route: rooted_sum (S k) <= exp * sum_over_sublists = exp * prod (1+rooted_sum). *)
Lemma rooted_sum_Sk_le_sum_over_sublists :
  forall k p forbidden,
    rooted_sum (Datatypes.S k) p forbidden <=
    exp (a * size p) *
    sum_over_sublists (nbr_excluding p forbidden) (fun q => rooted_sum k q (p :: forbidden)).
Proof.
  intros k p forbidden.
  unfold rooted_sum at 1.
  eapply Rle_trans.
  - apply (sum_list_map_incl RootedTree RootedTree_eq_dec
      (trees_of_depth_at_most (Datatypes.S k) p forbidden)
      (gen_trees_Sk k p forbidden)
      tree_weight).
    + intros t Ht. apply gen_trees_cover. exact Ht.
    + apply trees_of_depth_at_most_NoDup.
    + apply gen_trees_Sk_NoDup.
    + intros t _. apply tree_weight_nonneg.
  - apply sum_gen_trees_Sk_le.
Qed.

Lemma rooted_sum_rec_bound :
  forall k p forbidden,
    rooted_sum (Datatypes.S k) p forbidden <=
    exp (a * size p) *
    prod_overlap_excluding p forbidden (fun q => 1 + rooted_sum k q (p :: forbidden)).
Proof.
  intros k p forbidden.
  eapply Rle_trans.
  - apply rooted_sum_Sk_le_sum_over_sublists.
  - rewrite sum_over_sublists_eq_prod_1plus by (intros q Hq; apply rooted_sum_nonneg).
    apply Rle_refl.
Qed.

(* rooted_sum_le_rooted_upper moved below rooted_sum_rec_bound *)
Lemma rooted_sum_le_rooted_upper :
  forall k p forbidden,
    rooted_sum k p forbidden <= rooted_upper k p forbidden.
Proof.
  induction k as [|k IH]; intros p forbidden.
  - (* k = 0: leaf only *)
    unfold rooted_sum, rooted_upper.
    assert (Hspec : forall t, In t (trees_of_depth_at_most 0 p forbidden) -> t = rt_leaf p).
    { intros t Ht. rewrite trees_of_depth_at_most_spec in Ht. inversion Ht. reflexivity. }
    assert (Hincl : incl (trees_of_depth_at_most 0 p forbidden) [rt_leaf p]).
    { intros t Ht. apply Hspec in Ht. subst. left. reflexivity. }
    eapply Rle_trans. apply (sum_list_map_incl RootedTree RootedTree_eq_dec
      (trees_of_depth_at_most 0 p forbidden) [rt_leaf p] tree_weight).
    + exact Hincl.
    + apply trees_of_depth_at_most_NoDup.
    + constructor; [intro; contradiction | constructor].
    + intros t _. apply tree_weight_nonneg.
    + simpl. rewrite tree_weight_leaf, Rplus_0_r.
      (* exp <= activity p * exp since 1 <= activity p *)
      rewrite <- Rmult_1_l at 1.
      apply (Rmult_le_compat_r (exp (a * size p)) 1 (activity p));
        [apply Rlt_le; apply exp_pos | apply activity_ge_1].
  - (* k = S k *)
    unfold rooted_upper; fold rooted_upper.
    eapply Rle_trans.
    + apply rooted_sum_rec_bound.
    + eapply Rle_trans.
      * apply Rmult_le_compat_l.
        -- apply Rlt_le, exp_pos.
        -- apply prod_overlap_excluding_mono_1plus.
           intros q Hq. split.
           ++ apply rooted_sum_nonneg.
           ++ apply Rplus_le_compat_l. apply IH.
      * (* exp * prod <= activity * exp * prod since 1 <= activity *)
        set (ep := exp (a * size p) * prod_overlap_excluding p forbidden (fun q => 1 + rooted_upper k q (p :: forbidden))).
        replace (ep) with (1 * ep) at 1 by ring.
        rewrite Rmult_assoc. apply (Rmult_le_compat_r ep 1 (activity p)).
        -- assert (Hep : 0 <= ep).
           { eapply Rmult_le_pos. apply Rlt_le. apply exp_pos.
             apply fold_right_Rmult_nonneg; intros q Hq; apply Rle_trans with 1; [lra|]; replace (1) with (1 + 0) at 1 by ring; apply Rplus_le_compat_l; apply rooted_upper_nonneg. }
           exact Hep.
        -- apply activity_ge_1.
Qed.

(* Forbidden set as predicate: Forbidden_in S x := In x S.
   Monotonicity: S ⊆ S' (more forbidden) => rooted_sum k p S' ≤ rooted_sum k p S. *)
Definition Forbidden_in (S : list P) (x : P) : Prop := In x S.

(* Admissible under S' => admissible under S when S ⊆ S' *)
Lemma is_rooted_tree_of_depth_mono : forall k p S S' t,
  (forall x, In x S -> In x S') ->
  is_rooted_tree_of_depth k p S' t ->
  is_rooted_tree_of_depth k p S t.
Proof.
  intros k p S S' t Hsub Ht.
  revert p S S' t Hsub Ht.
  induction k as [|k IH]; intros p S S' t Hsub Ht.
  - (* k = 0: leaf *)
    inversion Ht. subst. apply rt_depth_0.
  - (* k = S k: node *)
    inversion Ht as [|k' p' forb children qs Hfa Hnd]. subst k' p'.
    apply (rt_depth_succ k p S children qs). 2: exact Hnd.
    apply Forall2_impl with (2 := Hfa).
    intros tr q [Hin Hsubtree].
    split.
    + apply nbr_excluding_antimono with (S' := S'); [exact Hsub | exact Hin].
    + apply IH with (S' := p :: S'); [| exact Hsubtree].
      intros x Hx. simpl in Hx. destruct Hx as [Heq|Hx]; [left; exact Heq | right; apply Hsub; exact Hx].
Qed.

(* Monotonicity wrt forbidden set: (∀x, F x -> G x) => more forbidden => smaller sum *)
Lemma rooted_sum_mono_forbidden :
  forall k p forbidden forbidden',
    (forall x, Forbidden_in forbidden x -> Forbidden_in forbidden' x) ->
    rooted_sum k p forbidden' <= rooted_sum k p forbidden.
Proof.
  intros k p forbidden forbidden' Hsub.
  unfold rooted_sum, Forbidden_in in *.
  apply (sum_list_map_incl RootedTree RootedTree_eq_dec
         (trees_of_depth_at_most k p forbidden')
         (trees_of_depth_at_most k p forbidden)
         tree_weight).
  - intros t Ht. apply trees_of_depth_at_most_spec.
    apply trees_of_depth_at_most_spec in Ht.
    apply is_rooted_tree_of_depth_mono with (S' := forbidden'); [exact Hsub | exact Ht].
  - apply trees_of_depth_at_most_NoDup.
  - apply trees_of_depth_at_most_NoDup.
  - intros t _. apply tree_weight_nonneg.
Qed.

(* List-inclusion form (equivalent) *)
Lemma rooted_sum_mono_forbidden_list :
  forall k p S S',
    (forall x, In x S -> In x S') ->
    rooted_sum k p S' <= rooted_sum k p S.
Proof.
  intros k p S S' Hsub.
  apply rooted_sum_mono_forbidden.
  unfold Forbidden_in. exact Hsub.
Qed.

(* =========================================================================
   4. KP Inequality (Assembly Lemma)

   From kp_sum_explicit_eq_sum_overlap and ym_satisfies_kp, we have:
   sum_overlap p (fun q => Rabs(activity q) * exp(a * size q)) ≤ a * size p

   This is the single reusable lemma for the recursion step.
   ========================================================================= *)

Definition kp_sum_condition (a_param : R) : Prop :=
  forall p : P,
    sum_overlap p (fun q => Rabs (activity q) * exp (a_param * size q)) <= a_param * size p.

(* Strong KP: sum over neighbors of activity * exp(2a*size) <= a*size. Needed for exp2a bound. *)
Hypothesis hkp_strong :
  forall p, sum_overlap p (fun q => activity q * exp (2 * a * size q)) <= a * size p.

(* sum_overlap_excluding sums over a subset of overlap neighbors *)
Hypothesis sum_excluding_le_full :
  forall p forb f,
    (forall q, In q (nbr_excluding p forb) -> 0 <= f q) ->
    sum_overlap_excluding p forb f <= sum_overlap p f.

Lemma kp_step_bound :
  forall (a_param : R) p,
    a_param > 0 ->
    kp_sum_condition a_param ->
    sum_overlap p (fun q => Rabs (activity q) * exp (a_param * size q)) <= a_param * size p.
Proof.
  intros a_param p _ Hkp.
  apply Hkp.
Qed.

(* Coordination bound axiom: abstract sum_overlap count ≤ degree.
   YM proves this from length(neighbors p) ≤ 24. *)
Hypothesis coordination_bound_axiom :
  forall p, sum_overlap p (fun _ => 1) <= INR (overlap_degree_bound).

Lemma sum_overlap_count_bound :
  forall p,
    sum_overlap p (fun _ => 1) <= INR (overlap_degree_bound).
Proof. exact coordination_bound_axiom. Qed.

(* Helper: sum of constant 1 = length *)
Lemma sum_ones_eq_length (A : Type) (l : list A) :
  fold_right Rplus 0 (map (fun _ => 1) l) = INR (length l).
Proof.
  induction l as [|x xs IH].
  - simpl. reflexivity.
  - simpl fold_right. simpl map. simpl length.
    rewrite IH. rewrite S_INR. lra.
Qed.

(* sum_overlap_excluding count: provable from nbr_excluding (no axiom) *)
Lemma sum_overlap_excluding_count_bound :
  forall p S,
    sum_overlap_excluding p S (fun _ => 1) <= INR (overlap_degree_bound).
Proof.
  intros p S.
  unfold sum_overlap_excluding.
  rewrite sum_ones_eq_length.
  apply le_INR.
  apply nbr_excluding_finite.
Qed.

(* =========================================================================
   5. Cluster Machinery (unchanged)
   ========================================================================= *)

Fixpoint cluster_size (X : Cluster) : R :=
  match X with
  | [] => 0
  | p :: X' => size p + cluster_size X'
  end.

Definition wf_cluster (X : Cluster) : Prop := NoDup X.

Variable V_lt : P -> P -> Prop.
Variable V_lt_dec : forall u v : P, {V_lt u v} + {~V_lt u v}.
(* needed for tree enumeration and deciders; X-first to match tree_graph's is_connected *)
Variable is_connected_dec : forall (X : Cluster) (G : Graph), {is_connected X V_lt V_lt_dec G} + {~ is_connected X V_lt V_lt_dec G}.
Variable is_tree_dec : forall (X : Cluster) (G : Graph), {is_tree X V_lt V_lt_dec G} + {~ is_tree X V_lt V_lt_dec G}.
Variable edge_in_A_G_dec : forall (G : Graph) (u v : P), {edge_in_A_G V_lt G u v} + {~ edge_in_A_G V_lt G u v}.

(* complete_edges for tree_graph: all valid edges on X *)
Parameter complete_edges : Cluster -> list (@Edge P).
Hypothesis complete_edges_NoDup : forall X, NoDup (complete_edges X).
Hypothesis complete_edges_correct : forall X e,
  In e (complete_edges X) <-> (In (eu e) X /\ In (ev e) X /\ eu e <> ev e).

(* Penrose majorant hypotheses (from tree_graph.v Section) *)
Hypothesis connected_in_bucket :
  forall X G, In G (connected_graphs_X X V_lt V_lt_dec (complete_edges X) (is_connected_dec X)) ->
              In G (bucket_graphs V_lt (complete_edges X) edge_in_A_G_dec (penrose_tree X V_lt V_lt_dec G)).
Hypothesis penrose_tree_in_trees :
  forall X G, In G (connected_graphs_X X V_lt V_lt_dec (complete_edges X) (is_connected_dec X)) ->
              In (penrose_tree X V_lt V_lt_dec G) (trees_X X V_lt V_lt_dec (complete_edges X) (is_tree_dec X)).
Hypothesis connected_graphs_NoDup :
  forall X, NoDup (connected_graphs_X X V_lt V_lt_dec (complete_edges X) (is_connected_dec X)).
Hypothesis hard_core_compatible :
  forall X T e, In T (trees_X X V_lt V_lt_dec (complete_edges X) (is_tree_dec X)) ->
                In e (A_edges_G V_lt (complete_edges X) edge_in_A_G_dec T) ->
                0 <= zeta_hc (eu e) (ev e).

Definition ursell_factor (X : Cluster) : R :=
  sum_list (map (graph_weight zeta_hc) (connected_graphs_X X V_lt V_lt_dec (complete_edges X) (is_connected_dec X))).

Lemma ursell_factor_def_eq_tree_graph_sum :
  forall (X : Cluster),
    ursell_factor X =
    sum_list (map (graph_weight zeta_hc) (connected_graphs_X X V_lt V_lt_dec (complete_edges X) (is_connected_dec X))).
Proof.
  intro X. reflexivity.
Qed.

Fixpoint prod_activity (X : Cluster) : R :=
  match X with
  | [] => 1
  | p :: X' => activity p * prod_activity X'
  end.

Definition cluster_weight (X : Cluster) : R :=
  ursell_factor X * prod_activity X.

Parameter connecting_support : P -> P -> list Cluster.
Hypothesis connecting_support_spec :
  forall p1 p2 X, In X (connecting_support p1 p2) <-> connects_overlap X p1 p2.

Definition sum_connecting_overlap (p1 p2 : P) (f : Cluster -> R) : R :=
  sum_list (map f (connecting_support p1 p2)).

(* =========================================================================
   6. Existing Lemmas (overlap path, wf_cluster, etc.)
   ========================================================================= *)

Lemma overlap_path_trans_edge :
  forall X p q r,
    overlap_path_in_cluster X p q ->
    overlap_edge_in X q r ->
    overlap_path_in_cluster X p r.
Proof.
  intros X p q r Hpq.
  revert r.
  induction Hpq as [p0 Hp0 | p0 q0 r0 Hedge0 Hpath0 IH].
  - intros s Hedge.
    apply opath_step with s.
    + exact Hedge.
    + destruct Hedge as [_ [Hs _]]. apply opath_refl. exact Hs.
  - intros s Hedge.
    apply opath_step with q0.
    + exact Hedge0.
    + apply IH. exact Hedge.
Qed.

Lemma overlap_path_sym :
  forall X p q,
    overlap_path_in_cluster X p q ->
    overlap_path_in_cluster X q p.
Proof.
  intros X p q Hpq.
  induction Hpq as [p0 Hp0 | p0 q0 r0 Hedge0 Hpath0 IH].
  - apply opath_refl. exact Hp0.
  - apply overlap_path_trans_edge with q0.
    + exact IH.
    + destruct Hedge0 as [Hp0 [Hq0 Hov]].
      unfold overlap_edge_in.
      split; [exact Hq0 | split; [exact Hp0 | apply overlap_sym; exact Hov]].
Qed.

Lemma wf_cluster_remove :
  forall (p : P) X,
    wf_cluster X ->
    wf_cluster (remove eq_dec p X).
Proof.
  intros p X Hwf.
  unfold wf_cluster in *.
  induction X as [|x xs IH].
  - simpl. constructor.
  - simpl. destruct (eq_dec p x) as [Heq | Hneq].
    + apply IH. inversion Hwf as [|? ? Hnotin' Hnodup']. exact Hnodup'.
    + constructor.
      * inversion Hwf as [|? ? Hnotin' Hnodup']. subst.
        intro Hcontra.
        apply in_remove in Hcontra.
        destruct Hcontra as [Hin _].
        contradiction.
      * apply IH. inversion Hwf as [|? ? Hnotin' Hnodup']. exact Hnodup'.
Qed.

Lemma connects_overlap_implies_nonempty :
  forall X p1 p2,
    connects_overlap X p1 p2 ->
    X <> [].
Proof.
  intros X p1 p2 [Hp1 _].
  destruct X as [|x xs].
  - simpl in Hp1. contradiction.
  - discriminate.
Qed.

(* =========================================================================
   7. Tree-Graph Majorant Interface (unchanged stubs)
   ========================================================================= *)

Definition Tree (X : Cluster) := @Graph P.
Definition is_spanning_tree (X : Cluster) (T : @Graph P) : Prop :=
  In T (trees_X X V_lt V_lt_dec (complete_edges X) (is_tree_dec X)).

Definition sum_over_spanning_trees (X : Cluster) (f : @Graph P -> R) : R :=
  sum_list (map f (trees_X X V_lt V_lt_dec (complete_edges X) (is_tree_dec X))).

Lemma w_edge_hc_le_1 :
  forall (e : @Edge P),
    0 <= w_edge zeta_hc e <= 1.
Proof.
  intro e.
  unfold w_edge.
  apply zeta_hc_abs_le_1.
Qed.

Lemma graph_abs_weight_hc_le_1 :
  forall (G : Graph),
    0 <= graph_abs_weight zeta_hc G <= 1.
Proof.
  induction G as [|e G IH]; simpl.
  - split; lra.
  - destruct IH as [IH0 IH1].
    destruct (w_edge_hc_le_1 e) as [Hw0 Hw1].
    split.
    + nra.
    + nra.
Qed.

Lemma sum_tree_abs_weight_le_tree_count :
  forall X,
    sum_list (map (fun T => graph_abs_weight zeta_hc T) (trees_X X V_lt V_lt_dec (complete_edges X) (is_tree_dec X)))
    <=
    sum_list (map (fun _ => 1) (trees_X X V_lt V_lt_dec (complete_edges X) (is_tree_dec X))).
Proof.
  intro X.
  apply sum_list_map_monotone.
  intros T HT.
  pose proof (graph_abs_weight_hc_le_1 T) as [_ Hle].
  exact Hle.
Qed.

Lemma closure_factor_hc_nonneg :
  forall X (edge_dec : forall (G0 : @Graph P) (u v : P), {edge_in_A_G V_lt G0 u v} + {~ edge_in_A_G V_lt G0 u v}) T,
    0 <= fold_right Rmult 1
      (map (fun e => 1 + zeta_hc (eu e) (ev e)) (A_edges_G V_lt (complete_edges X) edge_dec T)).
Proof.
  intros X edge_T T.
  induction (A_edges_G V_lt (complete_edges X) edge_T T) as [|e es IH]; simpl.
  - lra.
  - destruct (one_plus_zeta_hc_is_0_or_1 (eu e) (ev e)) as [Hz0|Hz1].
    + rewrite Hz0. nra.
    + rewrite Hz1. nra.
Qed.

Lemma closure_factor_hc_le_1 :
  forall X (edge_dec : forall (G0 : @Graph P) (u v : P), {edge_in_A_G V_lt G0 u v} + {~ edge_in_A_G V_lt G0 u v}) T,
    fold_right Rmult 1
      (map (fun e => 1 + zeta_hc (eu e) (ev e)) (A_edges_G V_lt (complete_edges X) edge_dec T))
    <= 1.
Proof.
  intros X edge_T T.
  induction (A_edges_G V_lt (complete_edges X) edge_T T) as [|e es IH]; simpl.
  - lra.
  - destruct (one_plus_zeta_hc_is_0_or_1 (eu e) (ev e)) as [Hz0|Hz1].
    + rewrite Hz0. nra.
    + rewrite Hz1. nra.
Qed.

(* =========================================================================
   Bridge and connecting-cluster bounds (Option A: activity-weighted)
   ========================================================================= *)

Hypothesis rooted_expansion_bridge :
  forall (a_param : R) p1 p2 (k : nat),
    a_param > 0 ->
    (k >= overlap_degree_bound)%nat ->
    sum_connecting_overlap p1 p2
      (fun X => Rabs (cluster_weight X) * exp (a_param * cluster_size X)) <=
    rooted_sum k p1 [] * rooted_sum k p2 [p1].

Lemma two_root_rooted_sum_bound :
  forall k p1 p2,
    rooted_sum k p1 [] * rooted_sum k p2 [p1] <=
    rooted_upper k p1 [] * rooted_upper k p2 [p1].
Proof.
  intros k p1 p2.
  apply Rmult_le_compat.
  - apply rooted_sum_nonneg.
  - apply rooted_sum_nonneg.
  - apply rooted_sum_le_rooted_upper.
  - apply rooted_sum_le_rooted_upper.
Qed.

(* Helper lemmas for rooted_upper_exp2a_bound *)
Lemma one_plus_le_exp (x : R) : 0 <= x -> 1 + x <= exp x.
Proof. intros _. exact (exp_ineq1_le x). Qed.

Lemma sum_list_R_mono (l : list P) (f g : P -> R) :
  (forall q, In q l -> f q <= g q) ->
  fold_right Rplus 0 (map f l) <= fold_right Rplus 0 (map g l).
Proof.
  induction l as [|x xs IH]; intros Hle; simpl.
  - lra.
  - assert (Hx : f x <= g x) by (apply Hle; left; reflexivity).
    assert (Hxs : fold_right Rplus 0 (map f xs) <= fold_right Rplus 0 (map g xs))
      by (apply IH; intros q Hq; apply Hle; right; exact Hq).
    lra.
Qed.

Lemma prod_le_exp_sum (l : list P) (f : P -> R) :
  (forall q, In q l -> 0 <= f q) ->
  fold_right Rmult 1 (map (fun q => 1 + f q) l) <= exp (fold_right Rplus 0 (map f l)).
Proof.
  induction l as [|x xs IH]; intros Hnonneg; simpl.
  - rewrite exp_0. lra.
  - set (sx := fold_right Rplus 0 (map f xs)).
    assert (Hfx : 0 <= f x) by (apply Hnonneg; left; reflexivity).
    assert (IH' : fold_right Rmult 1 (map (fun q => 1 + f q) xs) <= exp sx).
    { apply IH. intros q Hq. apply Hnonneg. right. exact Hq. }
    assert (Hhead : 1 + f x <= exp (f x)) by (apply one_plus_le_exp; exact Hfx).
    eapply Rle_trans.
    + apply Rmult_le_compat; try lra.
      * apply fold_right_Rmult_nonneg. intros q Hq.
        assert (Hfq : 0 <= f q) by (apply Hnonneg; right; exact Hq). lra.
      * exact Hhead.
      * exact IH'.
    + replace (fold_right Rplus 0 (map f (x :: xs))) with (f x + sx) by (simpl; reflexivity).
      apply Req_le. apply eq_sym. apply exp_plus.
Qed.

Lemma exp_le x y : x <= y -> exp x <= exp y.
Proof.
  intros Hxy. destruct (Rle_lt_or_eq_dec x y Hxy) as [Hlt|Heq].
  - apply Rlt_le. apply exp_increasing. exact Hlt.
  - rewrite Heq. apply Req_le. exact (eq_refl (exp y)).
Qed.

Lemma prod_overlap_rooted_upper_le_exp :
  forall p forb k,
    (forall q, In q (nbr_excluding p forb) -> 0 <= rooted_upper k q (p :: forb)) ->
    (forall q, In q (nbr_excluding p forb) -> rooted_upper k q (p :: forb) <= activity q * exp (2 * a * size q)) ->
    prod_overlap_excluding p forb (fun q => 1 + rooted_upper k q (p :: forb)) <= exp (a * size p).
Proof.
  intros p forb k Hnonneg Hle.
  unfold prod_overlap_excluding.
  set (L := nbr_excluding p forb).
  set (f := fun q => rooted_upper k q (p :: forb)).
  assert (Hprod : fold_right Rmult 1 (map (fun q => 1 + f q) L) <= exp (fold_right Rplus 0 (map f L))).
  { apply prod_le_exp_sum. intros q Hq. unfold f. apply Hnonneg. exact Hq. }
  assert (Hsum : fold_right Rplus 0 (map f L) <= fold_right Rplus 0 (map (fun q => activity q * exp (2 * a * size q)) L)).
  { apply sum_list_R_mono. exact Hle. }
  assert (HKP : fold_right Rplus 0 (map (fun q => activity q * exp (2 * a * size q)) L) <= a * size p).
  { eapply Rle_trans.
    - apply sum_excluding_le_full. intros q Hq.
      eapply Rmult_le_pos. apply Rge_le, activity_nonneg. apply Rlt_le, exp_pos.
    - apply hkp_strong. }
  eapply Rle_trans; [exact Hprod|].
  apply exp_le. lra.
Qed.

Lemma rooted_upper_exp2a_bound :
  forall k p forb,
    rooted_upper k p forb <= activity p * exp (2 * a * size p).
Proof.
  induction k as [|k' IH]; intros p forb; unfold rooted_upper; fold rooted_upper.
  - replace (2 * a * size p) with (a * size p + a * size p) by ring.
    rewrite exp_plus. apply Rmult_le_compat_l.
    + apply Rge_le, activity_nonneg.
    + assert (Hasp : 0 <= a * size p).
      { eapply Rle_trans. 2: apply hkp_strong.
        apply sum_overlap_nonneg. intros. eapply Rmult_le_pos. apply Rge_le, activity_nonneg. apply Rlt_le, exp_pos. }
      rewrite <- exp_plus. apply exp_le. nra.
  - eapply Rle_trans.
    + apply Rmult_le_compat_l.
      * eapply Rmult_le_pos. apply Rge_le, activity_nonneg. apply Rlt_le. apply exp_pos.
      * apply prod_overlap_rooted_upper_le_exp.
        -- intros q Hq. apply rooted_upper_nonneg.
        -- intros q Hq. apply IH.
    + replace (activity p * exp (a * size p) * exp (a * size p))
        with (activity p * (exp (a * size p) * exp (a * size p))) by ring.
      rewrite <- exp_plus. replace (a * size p + a * size p) with (2 * a * size p) by ring.
      apply Rle_refl.
Qed.

Lemma connecting_cluster_sum_le_tree_sum :
  forall p1 p2,
    a > 0 ->
    kp_sum_condition a ->
    sum_connecting_overlap p1 p2
      (fun X => Rabs (cluster_weight X) * exp (a * cluster_size X)) <=
    (activity p1 * exp (2 * a * size p1)) * (activity p2 * exp (2 * a * size p2)).
Proof.
  intros p1 p2 Ha Hkp.
  eapply Rle_trans.
  - apply (rooted_expansion_bridge a p1 p2 overlap_degree_bound Ha). apply Nat.le_refl.
  - eapply Rle_trans.
    + apply two_root_rooted_sum_bound.
    + apply Rmult_le_compat.
      * apply rooted_upper_nonneg.
      * apply rooted_upper_nonneg.
      * apply rooted_upper_exp2a_bound.
      * apply rooted_upper_exp2a_bound.
Qed.

Theorem connecting_bounded_by_pinned_from_KP :
  forall (p1 p2 : P),
    a > 0 ->
    kp_sum_condition a ->
    sum_connecting_overlap p1 p2
      (fun X => Rabs (cluster_weight X) * exp (a * cluster_size X)) <=
    (activity p1 * exp (2 * a * size p1)) * (activity p2 * exp (2 * a * size p2)).
Proof. intros p1 p2 Ha Hkp. apply connecting_cluster_sum_le_tree_sum; assumption. Qed.

Lemma sum_connecting_overlap_monotone :
  forall p1 p2 f g,
    (forall X, connects_overlap X p1 p2 -> f X <= g X) ->
    sum_connecting_overlap p1 p2 f <= sum_connecting_overlap p1 p2 g.
Proof.
  intros p1 p2 f g Hle.
  unfold sum_connecting_overlap.
  apply sum_list_map_monotone.
  intros X HX. apply Hle. apply (proj1 (connecting_support_spec p1 p2 X)). exact HX.
Qed.

Parameter in_volume : P -> Prop.
Parameter cluster_in_volume : Cluster -> Prop.
Hypothesis cluster_in_volume_spec : forall X, cluster_in_volume X -> forall p, In p X -> in_volume p.

Lemma connecting_overlap_respects_volume :
  forall X p1 p2,
    cluster_in_volume X ->
    connects_overlap X p1 p2 ->
    in_volume p1 /\ in_volume p2.
Proof.
  intros X p1 p2 Hvol Hconn.
  destruct Hconn as [Hp1 [Hp2 _]].
  split.
  - apply (cluster_in_volume_spec X Hvol p1 Hp1).
  - apply (cluster_in_volume_spec X Hvol p2 Hp2).
Qed.

(* =========================================================================
   Cluster Pinned Bridge (nested: uses PinnedBound context)
   Proves sum_connecting (adj) <= sum_connecting_overlap.
   ========================================================================= *)
Section ClusterPinnedBridge.

Variable polymers_Λ : list P.
Variable N_max : nat.
Variable connects_dec : forall (X : Cluster) (p1 p2 : P),
  {connects X p1 p2} + {~ connects X p1 p2}.

Definition list_P_eq_dec : forall l1 l2 : list P, {l1 = l2} + {l1 <> l2} :=
  list_eq_dec eq_dec.

Definition weight_nonneg (f : Cluster -> R) : Prop := forall X, 0 <= f X.

Hypothesis connecting_support_NoDup : forall p1 p2, NoDup (connecting_support p1 p2).
Hypothesis clusters_Λ_N_NoDup : NoDup (clusters_Λ_N P polymers_Λ N_max).

Lemma sum_conditional_eq_sum_filter (A : Type) (l : list A) (pred : A -> bool) (f : A -> R) :
  fold_right Rplus 0 (map (fun x => if pred x then f x else 0) l) =
  sum_list (map f (filter pred l)).
Proof.
  induction l as [|x xs IH]; simpl.
  - reflexivity.
  - destruct (pred x); simpl; rewrite IH; ring.
Qed.

Lemma sum_connecting_le_sum_overlap :
  forall (p1 p2 : P) (f : Cluster -> R),
    weight_nonneg f ->
    sum_connecting_concrete polymers_Λ N_max connects_dec p1 p2 f <=
    sum_connecting_overlap p1 p2 f.
Proof.
  intros p1 p2 f Hnneg.
  unfold sum_connecting_concrete, sum_connecting_impl, sum_connecting_overlap.
  set (L := clusters_Λ_N P polymers_Λ N_max).
  set (P_conn := fun X => if connects_dec X p1 p2 then true else false).
  apply Rle_trans with (r2 := fold_right Rplus 0 (map (fun X => if P_conn X then f X else 0) L)).
  - apply Req_le. apply f_equal2; [reflexivity|]. apply map_ext. intros X. unfold P_conn.
    destruct (connects_dec X p1 p2); reflexivity.
  - eapply Rle_trans.
    + apply Req_le. apply (sum_conditional_eq_sum_filter Cluster L P_conn f).
    + apply (sum_list_map_incl Cluster list_P_eq_dec (filter P_conn L) (connecting_support p1 p2) f).
      * intros X HX. apply filter_In in HX. destruct HX as [HinL Hconn].
        apply (proj2 (connecting_support_spec p1 p2 X)). unfold P_conn in Hconn.
        destruct (connects_dec X p1 p2) as [Hc|Hnc]; [apply connects_implies_connects_overlap; exact Hc |].
        exfalso. unfold P_conn in Hconn. destruct (connects_dec X p1 p2); inversion Hconn.
      * apply NoDup_filter. exact clusters_Λ_N_NoDup.
      * exact (connecting_support_NoDup p1 p2).
      * intros X HX. apply Hnneg.
Qed.

End ClusterPinnedBridge.

End PinnedBound.