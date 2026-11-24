(* =========================================================================
   rg/connected_subset_bound.v

   Kotecky-Preiss pinned bound for CONNECTED SUBSETS (sublists) of Lambda:

     sum_{S sublist of Lambda, S incompatible with p0, S connected}
         prod_{q in S} |w(q)|   <=   a(p0).

   Route:
     1. tree-count version of the 1-pinned ordered-tuple bound
        (kp_tree_pinned_bound: same proof as kp_overlap_pinned_bound, with
        the spanning-tree count in place of |phi^T|);
     2. connected  ==>  at least one spanning tree;
     3. invariance of the summand under adjacent transpositions;
     4. subsets versus ordered tuples (the 1/k! symmetrisation);
     5. assembly.

   Depends ONLY on Coq stdlib + rg.penrose_tree_bound + rg.poly_exp_bound
   + rg.tree_cut_bijection + rg.kotecky_preiss.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra Permutation.
From rg Require Import penrose_tree_bound poly_exp_bound tree_cut_bijection kotecky_preiss.
Import ListNotations.
Import PenroseTreeBound PolyExpBound TreeCutBijection KoteckyPreiss.
Open Scope R_scope.

Module ConnectedSubsetBound.

  (* =======================================================================
     1. Tree-count version of the 1-pinned overlap bound on ordered tuples
     ======================================================================= *)

  Theorem kp_tree_pinned_bound : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P)
    (w a d : P -> R) (p0 : P),
    (forall x y, ob x y = ob y x) ->
    (0 <= a p0) ->
    (forall p, In p Lambda -> 0 <= a p) ->
    kp_at ob Lambda w a d p0 ->
    (forall p, In p Lambda -> kp_at ob Lambda w a d p) ->
    forall N_max,
      kp_series Lambda N_max (fun X =>
        if existsb (ob p0) X
        then INR (tree_count ob X) * prod_weight (fun q => Rabs (w q) * exp (d q)) X
        else 0) <= a p0.
  Proof.
    intros P ob Lambda w a d p0 Hsym Ha0 Ha_nn Hkp0 Hkp N_max.
    set (wt := fun q => Rabs (w q) * exp (d q)).
    assert (Hwt_nn : forall q, 0 <= wt q)
      by (intro q; unfold wt; apply Rmult_le_pos; [apply Rabs_pos | left; apply exp_pos]).
    destruct N_max as [| N'].
    - simpl. exact Ha0.
    - (* Step 1: bound each order n = S k by
         sum_{q in Lambda, ob p0 q} wt q * tree_sum_order k q *)
      assert (Horder : forall k,
        (/ INR (fact (S k))) *
        sum_over_tuples Lambda (S k) (fun X =>
          if existsb (ob p0) X then INR (tree_count ob X) * prod_weight wt X else 0) <=
        sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_order ob Lambda wt k q)).
      { intro k.
        assert (H1 :
          sum_over_tuples Lambda (S k) (fun X =>
            if existsb (ob p0) X then INR (tree_count ob X) * prod_weight wt X else 0) <=
          sum_over_tuples Lambda (S k) (fun X =>
            fold_right Rplus 0 (map (fun idx =>
              (match nth_error X idx with Some q => if ob p0 q then 1 else 0 | None => 0 end) *
              INR (tree_count ob X) * prod_weight wt X) (seq 0%nat (S k))))).
        { apply sum_over_tuples_le. intros X HX. cbv beta.
          pose proof (tuples_of_length_len Lambda (S k) X HX) as HlenX.
          assert (Hrew : (if existsb (ob p0) X then INR (tree_count ob X) * prod_weight wt X else 0) =
                         (if existsb (ob p0) X then 1 else 0) * (INR (tree_count ob X) * prod_weight wt X))
            by (destruct (existsb (ob p0) X); ring).
          rewrite Hrew.
          replace (fold_right Rplus 0 (map (fun idx =>
              (match nth_error X idx with Some q => if ob p0 q then 1 else 0 | None => 0 end) *
              INR (tree_count ob X) * prod_weight wt X) (seq 0%nat (S k))))
            with (fold_right Rplus 0 (map (fun idx =>
              match nth_error X idx with Some q => if ob p0 q then 1 else 0 | None => 0 end) (seq 0%nat (S k))) *
              (INR (tree_count ob X) * prod_weight wt X)).
          + apply Rmult_le_compat_r.
            * apply Rmult_le_pos; [apply pos_INR | apply prod_weight_nonneg; exact Hwt_nn].
            * rewrite <- HlenX. apply existsb_le_sum_indices.
          + rewrite <- fold_right_Rplus_scale_r.
            apply fold_right_Rplus_ext; intros idx _; ring. }
        eapply Rle_trans; [apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat, fact_pos_R | exact H1] |].
        (* valid_roots_length_sum + sum_valid_roots_trees *)
        assert (Heq_vr :
          sum_over_tuples Lambda (S k) (fun X =>
            fold_right Rplus 0 (map (fun idx =>
              (match nth_error X idx with Some q => if ob p0 q then 1 else 0 | None => 0 end) *
              INR (tree_count ob X) * prod_weight wt X) (seq 0%nat (S k)))) =
          sum_over_tuples Lambda (S k) (fun X =>
            INR (length (valid_roots ob p0 X)) * INR (tree_count ob X) * prod_weight wt X)).
        { apply sum_over_tuples_ext. intros X HX.
          rewrite (valid_roots_length_sum ob p0 X), (tuples_of_length_len Lambda (S k) X HX).
          rewrite <- !fold_right_Rplus_scale_r. apply fold_right_Rplus_ext; intros idx _; ring. }
        rewrite Heq_vr.
        rewrite (sum_valid_roots_trees ob Lambda wt (S k) p0 Hsym ltac:(lia)).
        replace (S k - 1)%nat with k by lia.
        unfold sum_overlap_Lambda, tree_sum_order.
        rewrite <- !fold_right_Rplus_scale.
        apply fold_right_Rplus_le. intros q _.
        destruct (ob p0 q); [| lra].
        assert (HfactS : INR (fact (S k)) = INR (S k) * INR (fact k)).
        { change (fact (S k)) with (S k * fact k)%nat. rewrite mult_INR. reflexivity. }
        assert (Hne1 : INR (S k) <> 0) by (apply not_0_INR; lia).
        assert (Hne2 : INR (fact k) <> 0) by (apply not_0_INR, fact_neq_0).
        rewrite HfactS. right. field. split; assumption. }
      (* Step 2: sum over k = 0..N' *)
      assert (Hkp_le :
        kp_series Lambda (S N') (fun X =>
          if existsb (ob p0) X then INR (tree_count ob X) * prod_weight wt X else 0) <=
        sum_overlap_Lambda ob Lambda p0 (fun q => wt q * tree_sum_upto ob Lambda wt N' q)).
      { clear - Horder. induction N' as [| M IH].
        - cbn [kp_series]. rewrite Rplus_0_l.
          eapply Rle_trans; [exact (Horder 0%nat) |].
          unfold tree_sum_upto; simpl. lra.
        - cbn [kp_series].
          eapply Rle_trans; [apply Rplus_le_compat; [exact IH | exact (Horder (S M))] |].
          unfold sum_overlap_Lambda, tree_sum_upto.
          rewrite <- fold_right_Rplus_plus.
          apply fold_right_Rplus_le. intros q _.
          destruct (ob p0 q); [simpl sum_f_R0; lra | lra]. }
      eapply Rle_trans; [exact Hkp_le |].
      eapply Rle_trans; [| exact Hkp0].
      unfold sum_overlap_Lambda. apply fold_right_Rplus_le. intros q Hq.
      destruct (ob p0 q); [| lra].
      unfold wt.
      replace (Rabs (w q) * exp (a q + d q)) with (Rabs (w q) * exp (d q) * exp (a q))
        by (rewrite exp_plus; ring).
      apply Rmult_le_compat_l; [apply Hwt_nn |].
      exact (kp_tree_sum_bound_Lambda ob Lambda w a d Hsym Ha_nn Hkp N' q Hq).
  Qed.

  (* =======================================================================
     2. Connected incompatibility graph  ==>  at least one spanning tree
     ======================================================================= *)

  Lemma self_in_sublists : forall {A : Type} (l : list A), In l (sublists l).
  Proof.
    induction l as [| x xs IH]; simpl.
    - left; reflexivity.
    - apply in_app_iff. right. apply in_map. exact IH.
  Qed.

  Lemma connected_tree_count_pos : forall {P : Type} (ob : P -> P -> bool) (X : list P),
    is_connectedb (length X) (graph_edges ob X) = true ->
    (1 <= tree_count ob X)%nat.
  Proof.
    intros P ob X Hc. unfold tree_count.
    pose proof (tau_is_spanning_tree (length X) (graph_edges ob X) (graph_edges ob X)
                  (graph_edges_wf ob X) (self_in_sublists (graph_edges ob X)) Hc) as Hin.
    destruct (spanning_trees (length X) (graph_edges ob X)) as [| T Ts].
    - destruct Hin.
    - simpl. lia.
  Qed.

  (* =======================================================================
     3. Invariance under adjacent transpositions
     ======================================================================= *)

  Definition at_inv {P : Type} (G : list P -> R) : Prop :=
    forall (pre : list P) (x y : P) (post : list P),
      G (pre ++ x :: y :: post) = G (pre ++ y :: x :: post).

  Lemma at_inv_cons : forall {P : Type} (G : list P -> R) (p : P),
    at_inv G -> at_inv (fun Y => G (p :: Y)).
  Proof.
    intros P G p Hinv pre x y post. exact (Hinv (p :: pre) x y post).
  Qed.

  Lemma existsb_adj_swap : forall {A : Type} (f : A -> bool) (pre : list A) (x y : A) (post : list A),
    existsb f (pre ++ x :: y :: post) = existsb f (pre ++ y :: x :: post).
  Proof.
    intros A f pre x y post. rewrite !existsb_app. cbn [existsb].
    destruct (existsb f pre); [reflexivity |]. cbn [orb].
    destruct (f x); destruct (f y); reflexivity.
  Qed.

  Lemma prod_weight_adj_swap : forall {P : Type} (wt : P -> R) (pre : list P) (x y : P) (post : list P),
    prod_weight wt (pre ++ x :: y :: post) = prod_weight wt (pre ++ y :: x :: post).
  Proof.
    intros P wt pre x y post. unfold prod_weight, prod_list.
    induction pre as [| p pre IH]; cbn [app map fold_right].
    - ring.
    - rewrite IH. reflexivity.
  Qed.

  Lemma prod_weight_ext : forall {P : Type} (f g : P -> R) (X : list P),
    (forall q, f q = g q) -> prod_weight f X = prod_weight g X.
  Proof.
    intros P f g X Hfg. unfold prod_weight. rewrite (map_ext f g Hfg). reflexivity.
  Qed.

  (* nth_error under the transposition of positions (length pre) and S (length pre) *)
  Lemma nth_error_adj_swap : forall {A : Type} (pre : list A) (x y : A) (post : list A) (j : nat),
    nth_error (pre ++ x :: y :: post) j =
    nth_error (pre ++ y :: x :: post)
      (if Nat.eqb j (length pre) then S (length pre)
       else if Nat.eqb j (S (length pre)) then length pre else j).
  Proof.
    intros A. induction pre as [| p pre IH]; intros x y post j.
    - destruct j as [| [| j]]; reflexivity.
    - destruct j as [| j].
      + reflexivity.
      + cbn [app length nth_error Nat.eqb]. rewrite (IH x y post j).
        destruct (Nat.eqb j (length pre)); [reflexivity |].
        destruct (Nat.eqb j (S (length pre))); reflexivity.
  Qed.

  (* tree_count is invariant under any index involution of the tuple *)
  Lemma tree_count_relabel : forall {P : Type} (ob : P -> P -> bool) (n : nat) (A B : list P)
    (sigma : nat -> nat),
    (forall x y, ob x y = ob y x) ->
    length A = n ->
    length B = n ->
    (forall x, (x < n)%nat -> (sigma x < n)%nat) ->
    (forall x, (x < n)%nat -> sigma (sigma x) = x) ->
    (forall j, nth_error A j = nth_error B (sigma j)) ->
    (forall j, nth_error B j = nth_error A (sigma j)) ->
    tree_count ob A = tree_count ob B.
  Proof.
    intros P ob n A B sigma Hsym HA HB Hs Hinv HAB HBA.
    assert (Hmap_gen : forall A' B' : list P,
      length A' = n -> length B' = n ->
      (forall j, nth_error A' j = nth_error B' (sigma j)) ->
      forall e, In e (graph_edges ob A') -> In (map_edge sigma e) (graph_edges ob B')).
    { intros A' B' HA' HB' Hnth [u v] Hin.
      apply graph_edges_in in Hin. destruct Hin as [Huv [Hvn [x [y [Hx [Hy Hob]]]]]].
      rewrite HA' in Hvn.
      assert (Hsu_ne : sigma u <> sigma v).
      { intro Heq.
        assert (u = v) by (rewrite <- (Hinv u ltac:(lia)), <- (Hinv v Hvn), Heq; reflexivity).
        lia. }
      unfold map_edge, mk_edge; simpl.
      destruct (Nat.ltb_spec (sigma u) (sigma v)).
      - apply graph_edges_in. rewrite HB'. repeat split; [lia | apply Hs; exact Hvn |].
        exists x, y. rewrite <- !Hnth. repeat split; assumption.
      - apply graph_edges_in. rewrite HB'. repeat split; [lia | apply Hs; lia |].
        exists y, x. rewrite <- !Hnth, Hsym. repeat split; assumption. }
    unfold tree_count. rewrite HA, HB.
    refine (proj2 (graph_iso_ursell_and_trees n sigma sigma
                     (graph_edges ob A) (graph_edges ob B) _ _ Hs Hs Hinv Hinv _ _)).
    - rewrite <- HA. apply graph_edges_wf.
    - rewrite <- HB. apply graph_edges_wf.
    - exact (Hmap_gen A B HA HB HAB).
    - exact (Hmap_gen B A HB HA HBA).
  Qed.

  Lemma tree_count_adj_swap : forall {P : Type} (ob : P -> P -> bool) (pre : list P)
    (x y : P) (post : list P),
    (forall x y, ob x y = ob y x) ->
    tree_count ob (pre ++ x :: y :: post) = tree_count ob (pre ++ y :: x :: post).
  Proof.
    intros P ob pre x y post Hsym.
    set (i := length pre).
    set (sigma := fun j : nat =>
      if Nat.eqb j i then S i else if Nat.eqb j (S i) then i else j).
    assert (Hs : forall j, (j < i + S (S (length post)))%nat ->
                           (sigma j < i + S (S (length post)))%nat).
    { intros j Hj. unfold sigma.
      destruct (Nat.eqb_spec j i); [lia |].
      destruct (Nat.eqb_spec j (S i)); lia. }
    assert (Hinv : forall j, sigma (sigma j) = j).
    { intro j. unfold sigma.
      destruct (Nat.eqb_spec j i) as [Hji | Hne].
      - destruct (Nat.eqb_spec (S i) i); [lia |].
        rewrite Nat.eqb_refl. symmetry. exact Hji.
      - destruct (Nat.eqb_spec j (S i)) as [Hjs | Hne2].
        + rewrite Nat.eqb_refl. symmetry. exact Hjs.
        + destruct (Nat.eqb_spec j i); [contradiction |].
          destruct (Nat.eqb_spec j (S i)); [contradiction | reflexivity]. }
    apply (tree_count_relabel ob (i + S (S (length post))) _ _ sigma Hsym).
    - rewrite app_length. reflexivity.
    - rewrite app_length. reflexivity.
    - exact Hs.
    - intros j _. apply Hinv.
    - intro j. exact (nth_error_adj_swap pre x y post j).
    - intro j. exact (nth_error_adj_swap pre y x post j).
  Qed.

  (* =======================================================================
     4. Subsets versus ordered tuples (the 1 / k! symmetrisation)
     ======================================================================= *)

  Lemma kp_series_S : forall {P : Type} (L : list P) (N : nat) (t : list P -> R),
    kp_series L (S N) t =
    kp_series L N t + / INR (fact (S N)) * sum_over_tuples L (S N) t.
  Proof. reflexivity. Qed.

  Lemma kp_series_nonneg : forall {P : Type} (L : list P) (N : nat) (G : list P -> R),
    (forall X, 0 <= G X) -> 0 <= kp_series L N G.
  Proof.
    intros P L N G HG. induction N as [| N IH].
    - cbn [kp_series]. apply Rle_refl.
    - rewrite kp_series_S.
      assert (H : 0 <= / INR (fact (S N)) * sum_over_tuples L (S N) G).
      { apply Rmult_le_pos.
        - left. apply Rinv_0_lt_compat, fact_pos_R.
        - apply sum_over_tuples_nonneg. intros Y _. apply HG. }
      lra.
  Qed.

  Lemma sum_over_tuples_1 : forall {P : Type} (L : list P) (F : list P -> R),
    sum_over_tuples L 1 F = fold_right Rplus 0 (map (fun p => F [p]) L).
  Proof.
    intros P L F. rewrite sum_over_tuples_S.
    apply fold_right_Rplus_ext. intros p _.
    exact (sum_over_tuples_0 L (fun Y => F (p :: Y))).
  Qed.

  Lemma sum_over_tuples_S_cons : forall {P : Type} (a : P) (l : list P) (n : nat) (f : list P -> R),
    sum_over_tuples (a :: l) (S n) f =
    sum_over_tuples (a :: l) n (fun Y => f (a :: Y)) +
    fold_right Rplus 0 (map (fun p => sum_over_tuples (a :: l) n (fun Y => f (p :: Y))) l).
  Proof. intros P a l n f. rewrite sum_over_tuples_S. reflexivity. Qed.

  (* Monotonicity in the polymer list for nonnegative terms *)
  Lemma sum_over_tuples_cons_ge : forall {P : Type} (a : P) (l : list P) (k : nat)
    (F : list P -> R),
    (forall X, 0 <= F X) ->
    sum_over_tuples l k F <= sum_over_tuples (a :: l) k F.
  Proof.
    intros P a l. induction k as [| k IH]; intros F HF.
    - rewrite !sum_over_tuples_0. apply Rle_refl.
    - rewrite (sum_over_tuples_S_cons a l k F), (sum_over_tuples_S l k F).
      assert (H0 : 0 <= sum_over_tuples (a :: l) k (fun Y => F (a :: Y))).
      { apply sum_over_tuples_nonneg. intros Y _. apply HF. }
      assert (H1 :
        fold_right Rplus 0 (map (fun p => sum_over_tuples l k (fun Y => F (p :: Y))) l) <=
        fold_right Rplus 0 (map (fun p => sum_over_tuples (a :: l) k (fun Y => F (p :: Y))) l)).
      { apply fold_right_Rplus_le. intros p _.
        exact (IH (fun Y => F (p :: Y)) (fun Y => HF (p :: Y))). }
      lra.
  Qed.

  (* Key decomposition: tuples over (a :: l) avoiding a, plus tuples containing a
     exactly once (at one of S k positions); all other tuples contribute >= 0. *)
  Lemma sum_over_tuples_cons_decomp : forall {P : Type} (a : P) (l : list P) (k : nat)
    (G : list P -> R),
    (forall X, 0 <= G X) ->
    at_inv G ->
    sum_over_tuples l (S k) G + INR (S k) * sum_over_tuples l k (fun Y => G (a :: Y))
    <= sum_over_tuples (a :: l) (S k) G.
  Proof.
    intros P a l. induction k as [| k IH]; intros G HG Hinv.
    - rewrite (sum_over_tuples_1 l G), (sum_over_tuples_1 (a :: l) G).
      rewrite (sum_over_tuples_0 l (fun Y => G (a :: Y))).
      cbn [map fold_right INR]. lra.
    - rewrite (sum_over_tuples_S_cons a l (S k) G).
      pose proof (sum_over_tuples_cons_ge a l (S k) (fun Y => G (a :: Y))
                    (fun Y => HG (a :: Y))) as H1.
      assert (H2 :
        fold_right Rplus 0 (map (fun p =>
          sum_over_tuples l (S k) (fun Y => G (p :: Y)) +
          INR (S k) * sum_over_tuples l k (fun Y => G (p :: a :: Y))) l) <=
        fold_right Rplus 0 (map (fun p =>
          sum_over_tuples (a :: l) (S k) (fun Y => G (p :: Y))) l)).
      { apply fold_right_Rplus_le. intros p _.
        exact (IH (fun Y => G (p :: Y)) (fun Y => HG (p :: Y)) (at_inv_cons G p Hinv)). }
      assert (H3 :
        fold_right Rplus 0 (map (fun p =>
          sum_over_tuples l (S k) (fun Y => G (p :: Y)) +
          INR (S k) * sum_over_tuples l k (fun Y => G (p :: a :: Y))) l) =
        sum_over_tuples l (S (S k)) G +
        INR (S k) * sum_over_tuples l (S k) (fun Y => G (a :: Y))).
      { rewrite (fold_right_Rplus_plus
          (fun p => sum_over_tuples l (S k) (fun Y => G (p :: Y)))
          (fun p => INR (S k) * sum_over_tuples l k (fun Y => G (p :: a :: Y))) l).
        rewrite (fold_right_Rplus_scale (INR (S k))
          (fun p => sum_over_tuples l k (fun Y => G (p :: a :: Y))) l).
        assert (E :
          fold_right Rplus 0 (map (fun p => sum_over_tuples l k (fun Y => G (p :: a :: Y))) l) =
          sum_over_tuples l (S k) (fun Y => G (a :: Y))).
        { rewrite (sum_over_tuples_S l k (fun Y => G (a :: Y))).
          apply fold_right_Rplus_ext. intros p _.
          apply sum_over_tuples_ext. intros Y _. exact (Hinv [] p a Y). }
        rewrite E, (sum_over_tuples_S l (S k) G). reflexivity. }
      rewrite H3 in H2.
      assert (HS : INR (S (S k)) = INR (S k) + 1) by apply S_INR.
      rewrite HS. lra.
  Qed.

  (* The same, order by order, with the 1 / k! weights *)
  Lemma kp_order_cons : forall {P : Type} (a : P) (l : list P) (k : nat) (G : list P -> R),
    (forall X, 0 <= G X) ->
    at_inv G ->
    / INR (fact (S k)) * sum_over_tuples l (S k) G +
    / INR (fact k) * sum_over_tuples l k (fun Y => G (a :: Y))
    <= / INR (fact (S k)) * sum_over_tuples (a :: l) (S k) G.
  Proof.
    intros P a l k G HG Hinv.
    pose proof (sum_over_tuples_cons_decomp a l k G HG Hinv) as Hd.
    assert (HfactS : INR (fact (S k)) = INR (S k) * INR (fact k)).
    { change (fact (S k)) with (S k * fact k)%nat. rewrite mult_INR. reflexivity. }
    assert (Hne1 : INR (S k) <> 0) by (apply not_0_INR; lia).
    assert (Hne2 : INR (fact k) <> 0) by (apply not_0_INR, fact_neq_0).
    assert (Hinvpos : 0 < / INR (fact (S k))) by (apply Rinv_0_lt_compat, fact_pos_R).
    assert (Heq : / INR (fact k) = / INR (fact (S k)) * INR (S k)).
    { rewrite HfactS. field. split; assumption. }
    rewrite Heq.
    replace (/ INR (fact (S k)) * sum_over_tuples l (S k) G +
             / INR (fact (S k)) * INR (S k) * sum_over_tuples l k (fun Y => G (a :: Y)))
       with (/ INR (fact (S k)) *
             (sum_over_tuples l (S k) G +
              INR (S k) * sum_over_tuples l k (fun Y => G (a :: Y)))) by ring.
    apply Rmult_le_compat_l; [lra | exact Hd].
  Qed.

  Lemma kp_series_cons : forall {P : Type} (a : P) (l : list P) (G : list P -> R),
    (forall X, 0 <= G X) ->
    at_inv G ->
    forall N,
      kp_series l (S N) G + (G [a] + kp_series l N (fun Y => G (a :: Y)))
      <= kp_series (a :: l) (S N) G.
  Proof.
    intros P a l G HG Hinv. induction N as [| N IH].
    - rewrite (kp_series_S l 0 G), (kp_series_S (a :: l) 0 G).
      cbn [kp_series].
      pose proof (kp_order_cons a l 0 G HG Hinv) as Hc.
      assert (E0 : / INR (fact 0) * sum_over_tuples l 0 (fun Y => G (a :: Y)) = G [a]).
      { rewrite (sum_over_tuples_0 l (fun Y => G (a :: Y))).
        change (fact 0) with 1%nat. change (INR 1) with 1. rewrite Rinv_1. ring. }
      rewrite E0 in Hc. lra.
    - rewrite (kp_series_S l (S N) G), (kp_series_S (a :: l) (S N) G),
              (kp_series_S l N (fun Y => G (a :: Y))).
      pose proof (kp_order_cons a l (S N) G HG Hinv) as Hc.
      lra.
  Qed.

  (* Sum over sublists (subsets) is dominated by the 1/k!-weighted tuple series *)
  Theorem sublists_sum_le_kp_series : forall {P : Type} (l : list P) (G : list P -> R),
    (forall X, 0 <= G X) ->
    at_inv G ->
    forall N, (length l <= N)%nat ->
      fold_right Rplus 0 (map G (sublists l)) <= G [] + kp_series l N G.
  Proof.
    intros P. induction l as [| a l IH]; intros G HG Hinv N HN.
    - cbn [sublists map fold_right].
      pose proof (kp_series_nonneg (@nil P) N G HG). lra.
    - destruct N as [| N]; [cbn [length] in HN; lia |].
      cbn [length] in HN.
      cbn [sublists]. rewrite map_app, fold_right_Rplus_app, map_map.
      pose proof (IH G HG Hinv (S N) ltac:(lia)) as IH1.
      pose proof (IH (fun Y => G (a :: Y)) (fun Y => HG (a :: Y))
                    (at_inv_cons G a Hinv) N ltac:(lia)) as IH2.
      cbv beta in IH2.
      pose proof (kp_series_cons a l G HG Hinv N) as Hc.
      lra.
  Qed.

  (* =======================================================================
     5. Main theorem: pinned sum over CONNECTED SUBSETS (sublists) of Lambda
        that are incompatible with p0
     ======================================================================= *)

  (* 5a. Version with general exponential weights exp (d q)
         (no NoDup hypothesis is needed) *)
  Theorem kp_connected_subset_pinned_bound_weighted :
    forall {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w a d : P -> R) (p0 : P),
      (forall x y, ob x y = ob y x) ->
      0 <= a p0 ->
      (forall p, In p Lambda -> 0 <= a p) ->
      kp_at ob Lambda w a d p0 ->
      (forall p, In p Lambda -> kp_at ob Lambda w a d p) ->
      fold_right Rplus 0
        (map (fun X =>
                if existsb (ob p0) X && is_connectedb (length X) (graph_edges ob X)
                then prod_weight (fun q => Rabs (w q) * exp (d q)) X else 0)
             (sublists Lambda))
      <= a p0.
  Proof.
    intros P ob Lambda w a d p0 Hsym Ha0 Ha_nn Hkp0 Hkp.
    set (wt := fun q : P => Rabs (w q) * exp (d q)).
    set (G0 := fun X : list P =>
      if existsb (ob p0) X then INR (tree_count ob X) * prod_weight wt X else 0).
    assert (Hwt_nn : forall q, 0 <= wt q).
    { intro q. unfold wt. apply Rmult_le_pos; [apply Rabs_pos | left; apply exp_pos]. }
    assert (HG0_nn : forall X, 0 <= G0 X).
    { intro X. unfold G0. destruct (existsb (ob p0) X); [| apply Rle_refl].
      apply Rmult_le_pos; [apply pos_INR | apply prod_weight_nonneg; exact Hwt_nn]. }
    assert (HG0_inv : at_inv G0).
    { intros pre x y post. unfold G0.
      rewrite (existsb_adj_swap (ob p0) pre x y post).
      rewrite (tree_count_adj_swap ob pre x y post Hsym).
      rewrite (prod_weight_adj_swap wt pre x y post).
      reflexivity. }
    (* each summand is dominated by the tree-count term G0 *)
    assert (Hterm : forall X : list P,
      (if existsb (ob p0) X && is_connectedb (length X) (graph_edges ob X)
       then prod_weight wt X else 0) <= G0 X).
    { intro X. unfold G0.
      destruct (existsb (ob p0) X) eqn:Hex; cbn [andb]; [| apply Rle_refl].
      destruct (is_connectedb (length X) (graph_edges ob X)) eqn:Hc.
      - pose proof (connected_tree_count_pos ob X Hc) as Htc.
        apply le_INR in Htc. change (INR 1) with 1 in Htc.
        pose proof (prod_weight_nonneg wt X Hwt_nn) as Hpn.
        rewrite <- (Rmult_1_l (prod_weight wt X)) at 1.
        apply Rmult_le_compat_r; assumption.
      - apply Rmult_le_pos; [apply pos_INR | apply prod_weight_nonneg; exact Hwt_nn]. }
    assert (H1 :
      fold_right Rplus 0
        (map (fun X =>
                if existsb (ob p0) X && is_connectedb (length X) (graph_edges ob X)
                then prod_weight wt X else 0)
             (sublists Lambda))
      <= fold_right Rplus 0 (map G0 (sublists Lambda))).
    { apply fold_right_Rplus_le. intros X _. exact (Hterm X). }
    (* subsets versus tuples, then the tree-count pinned tuple bound *)
    pose proof (sublists_sum_le_kp_series Lambda G0 HG0_nn HG0_inv
                  (length Lambda) (le_n (length Lambda))) as H2.
    assert (H3 : kp_series Lambda (length Lambda) G0 <= a p0).
    { exact (kp_tree_pinned_bound ob Lambda w a d p0
               Hsym Ha0 Ha_nn Hkp0 Hkp (length Lambda)). }
    assert (HG00 : G0 [] = 0) by reflexivity.
    rewrite HG00 in H2.
    eapply Rle_trans; [exact H1 |]. lra.
  Qed.

  (* 5b. The requested statement (d = 0) *)
  Theorem kp_connected_subset_pinned_bound :
    forall {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w a : P -> R) (p0 : P),
      (forall x y, ob x y = ob y x) ->
      NoDup Lambda ->
      0 <= a p0 ->
      (forall p, In p Lambda -> 0 <= a p) ->
      kp_at ob Lambda w a (fun _ => 0) p0 ->
      (forall p, In p Lambda -> kp_at ob Lambda w a (fun _ => 0) p) ->
      fold_right Rplus 0
        (map (fun S =>
                if existsb (ob p0) S && is_connectedb (length S) (graph_edges ob S)
                then prod_weight (fun q => Rabs (w q)) S else 0)
             (sublists Lambda))
      <= a p0.
  Proof.
    intros P ob Lambda w a p0 Hsym _ Ha0 Ha_nn Hkp0 Hkp.
    eapply Rle_trans;
      [| exact (kp_connected_subset_pinned_bound_weighted ob Lambda w a (fun _ => 0) p0
                  Hsym Ha0 Ha_nn Hkp0 Hkp)].
    right. apply fold_right_Rplus_ext. intros X _.
    destruct (existsb (ob p0) X && is_connectedb (length X) (graph_edges ob X));
      [| reflexivity].
    apply prod_weight_ext. intro q. cbv beta. rewrite exp_0. ring.
  Qed.

End ConnectedSubsetBound.
