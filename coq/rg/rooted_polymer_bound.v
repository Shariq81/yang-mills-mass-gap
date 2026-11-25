(* =========================================================================
   rg/rooted_polymer_bound.v

   Two abstract statements about plaquette sets ATTACHED TO A ROOT, used for
   the Wilson-loop area law (Target 7e), where the root is the loop:

   1. `kp_rooted_connected_subset_bound` (entropy of rooted connected sets).
      Under the single-polymer Kotecky-Preiss inequality at the root p0 and
      on Lambda,

        sum_{S sublist of Lambda, (p0 :: S) connected}
            prod_{q in S} |w(q)| e^{d(q)}   <=   exp(a(p0)).

      It follows from the rooted tree-sum bound `kp_tree_sum_bound` of
      rg/kotecky_preiss.v, the fact that a connected graph has a spanning
      tree, and the 1/k! symmetrisation of rg/connected_subset_bound.v.

   2. `rooted_expansion` (the part of a subset attached to the root).
      In the setting of rg/polymer_representation.v (plaquettes with link
      supports, a weight rho that factorizes over non-touching parts), for a
      root p0 outside the duplicate-free list l,

        sum_{S <= l} rho (p0 :: S)
          = sum_{G <= l, (p0 :: G) connected}
              rho (p0 :: G) * sum_{T <= l, T does not touch p0 :: G} rho T.

   Depends ONLY on Coq stdlib + rg.dup_clustering + the Kotecky-Preiss engine
   files + rg.polymer_representation + rg.connected_subset_bound.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra.
From rg Require Import dup_clustering.
From rg Require Import penrose_tree_bound poly_exp_bound tree_cut_bijection
                       kotecky_preiss exp_series_limit cluster_log_partition.
From rg Require Import polymer_representation connected_subset_bound.
Import ListNotations.
Import DupClustering.
Import PenroseTreeBound PolyExpBound TreeCutBijection KoteckyPreiss ExpSeriesLimit
       ClusterLogPartition.
Open Scope R_scope.

Module RootedPolymerBound.

  (* =======================================================================
     1. Entropy of connected sets attached to a root
     ======================================================================= *)

  (* The rooted tree sums of rg/kotecky_preiss.v, written as a cluster series *)
  Lemma tree_sum_upto_kp_series : forall {P : Type} (ob : P -> P -> bool)
      (Lambda : list P) (wt : P -> R) (p0 : P) (N : nat),
    tree_sum_upto ob Lambda wt N p0 =
    INR (tree_count ob [p0]) * prod_weight wt [] +
    kp_series Lambda N (fun Y => INR (tree_count ob (p0 :: Y)) * prod_weight wt Y).
  Proof.
    intros P ob Lambda wt p0 N. unfold tree_sum_upto. induction N as [| N IH].
    - cbn [sum_f_R0 kp_series]. unfold tree_sum_order. rewrite sum_over_tuples_0.
      cbn [fact INR]. rewrite Rinv_1. ring.
    - rewrite tech5, IH. cbn [kp_series]. unfold tree_sum_order. ring.
  Qed.

  Theorem kp_rooted_connected_subset_bound :
    forall {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w a d : P -> R) (p0 : P),
      (forall x y, ob x y = ob y x) ->
      0 <= a p0 ->
      (forall p, In p Lambda -> 0 <= a p) ->
      kp_at ob Lambda w a d p0 ->
      (forall p, In p Lambda -> kp_at ob Lambda w a d p) ->
      fold_right Rplus 0
        (map (fun S =>
                if is_connectedb (length (p0 :: S)) (graph_edges ob (p0 :: S))
                then prod_weight (fun q => Rabs (w q) * exp (d q)) S else 0)
             (sublists Lambda))
      <= exp (a p0).
  Proof.
    intros P ob Lambda w a d p0 Hsym Ha0 Ha Hkp0 Hkp.
    set (wt := fun q : P => Rabs (w q) * exp (d q)).
    assert (Hwt : forall q, 0 <= wt q).
    { intro q. unfold wt. apply Rmult_le_pos; [apply Rabs_pos | left; apply exp_pos]. }
    set (G := fun Y : list P => INR (tree_count ob (p0 :: Y)) * prod_weight wt Y).
    assert (HGnn : forall X, 0 <= G X).
    { intro X. unfold G.
      apply Rmult_le_pos; [apply pos_INR | apply prod_weight_nonneg; exact Hwt]. }
    assert (HGat : ConnectedSubsetBound.at_inv G).
    { intros pre x y post. unfold G.
      rewrite (ConnectedSubsetBound.prod_weight_adj_swap wt pre x y post).
      change (p0 :: pre ++ x :: y :: post) with ((p0 :: pre) ++ x :: y :: post).
      rewrite (ConnectedSubsetBound.tree_count_adj_swap ob (p0 :: pre) x y post Hsym).
      reflexivity. }
    apply Rle_trans with (fold_right Rplus 0 (map G (sublists Lambda))).
    - apply fold_right_Rplus_le. intros S _.
      destruct (is_connectedb (length (p0 :: S)) (graph_edges ob (p0 :: S))) eqn:Hc.
      + unfold G.
        pose proof (ConnectedSubsetBound.connected_tree_count_pos ob (p0 :: S) Hc) as Htc.
        apply le_INR in Htc. cbn [INR] in Htc.
        pose proof (prod_weight_nonneg wt S Hwt) as Hpw.
        rewrite <- (Rmult_1_l (prod_weight wt S)) at 1.
        apply Rmult_le_compat_r; assumption.
      + apply HGnn.
    - eapply Rle_trans;
        [apply (ConnectedSubsetBound.sublists_sum_le_kp_series Lambda G HGnn HGat
                  (length Lambda) (le_n _)) |].
      apply Rle_trans with (tree_sum_upto ob Lambda wt (length Lambda) p0).
      + apply Req_le. symmetry.
        exact (tree_sum_upto_kp_series ob Lambda wt p0 (length Lambda)).
      + exact (kp_tree_sum_bound ob Lambda w a d p0 Hsym Ha0 Ha Hkp0 Hkp (length Lambda)).
  Qed.

  (* =======================================================================
     2. Expansion of a rooted subset sum over the part attached to the root
     ======================================================================= *)

  Section RootedExpansion.
    Variables (L B : Type).
    Variable eqbL : L -> L -> bool.
    Hypothesis eqbL_spec : forall x y, eqbL x y = true <-> x = y.
    Variable eqbB : B -> B -> bool.
    Hypothesis eqbB_spec : forall x y, eqbB x y = true <-> x = y.
    Variable supp : B -> list L.
    Hypothesis supp_nonempty : forall b, supp b <> [].
    Variable rho : list B -> R.
    Hypothesis rho_factor : forall (S : list B) (f : B -> bool),
      (forall p q, In p S -> In q S -> f p = true -> f q = false ->
                   PolymerRepresentation.touch L B eqbL supp p q = false) ->
      rho S = rho (filter f S) * rho (filter (fun b => negb (f b)) S).

    Local Notation touchP := (PolymerRepresentation.touch L B eqbL supp).
    Local Notation ptouchP := (PolymerRepresentation.ptouch L B eqbL supp).
    Local Notation connbP := (PolymerRepresentation.connb L B eqbL supp).

    Theorem rooted_expansion : forall p0 l, NoDup (p0 :: l) ->
      rsum (sublists l) (fun S => rho (p0 :: S)) =
      rsum (sublists l) (fun G =>
        if connbP (p0 :: G)
        then rho (p0 :: G) *
             rsum (sublists (filter (fun b => negb (ptouchP (p0 :: G) b)) l)) rho
        else 0).
    Proof.
      intros p0 l Hnd. inversion Hnd as [| p0' l' Hp0 Hnd']; subst.
      set (FF := fun G T : list B =>
             if connbP (p0 :: G) && forallb (fun b => negb (ptouchP (p0 :: G) b)) T
             then rho (p0 :: G) * rho T else 0).
      transitivity (rsum (sublists l) (fun G => rsum (sublists l) (fun T => FF G T))).
      - rewrite (PolymerRepresentation.merge_sum B eqbB eqbB_spec l Hnd' FF).
        + apply rsum_ext. intros S HS. symmetry.
          assert (HndS : NoDup (p0 :: S)).
          { constructor.
            - intro Hin. apply Hp0. exact (sublists_incl l S HS p0 Hin).
            - exact (sublists_NoDup_elem l S Hnd' HS). }
          exact (PolymerRepresentation.split_sum L B eqbL eqbL_spec eqbB eqbB_spec
                   supp supp_nonempty rho rho_factor p0 S HndS).
        + intros G T HG HT [x [HxG HxT]]. unfold FF.
          destruct (connbP (p0 :: G)); cbn [andb]; [| reflexivity].
          destruct (forallb (fun b => negb (ptouchP (p0 :: G) b)) T) eqn:Hf; [| reflexivity].
          exfalso. rewrite forallb_forall in Hf. specialize (Hf x HxT).
          apply negb_true_iff in Hf. unfold PolymerRepresentation.ptouch in Hf.
          pose proof (PolymerRepresentation.existsb_false_In
                        (fun p => touchP p x) (p0 :: G) x Hf (or_intror HxG)) as Hno.
          cbv beta in Hno.
          rewrite (PolymerRepresentation.touch_refl L B eqbL eqbL_spec supp supp_nonempty x)
            in Hno.
          discriminate.
      - apply rsum_ext. intros G HG. unfold FF.
        destruct (connbP (p0 :: G)) eqn:Hc; cbn [andb].
        + rewrite <- rsum_scal.
          exact (fold_right_Rplus_sublists_filter
                   (fun b => negb (ptouchP (p0 :: G) b)) l
                   (fun T => rho (p0 :: G) * rho T)).
        + apply rsum_zero. intros T _. reflexivity.
    Qed.
  End RootedExpansion.

End RootedPolymerBound.
