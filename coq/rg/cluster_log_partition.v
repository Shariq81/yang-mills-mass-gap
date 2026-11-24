(* =========================================================================
   rg/cluster_log_partition.v

   Finite-Volume Polymer Partition Function, Absolute Convergence of the
   1 / n! Mayer / Ursell Cluster Expansion to ln Z_Lambda, and Unconditional
   Exponential Decay of the Exact Partition-Function Log Ratio:

     Under the single-polymer Kotecky-Preiss inequality on a finite polymer
     volume Lambda (with reflexive, symmetric incompatibility predicate ob):
       1. Z_Lambda := sum_{S <= Lambda pairwise compatible} prod_{p in S} w(p) > 0
       2. The 1/n! Ursell series converges absolutely (bounded by sum_{Lambda} a)
          and Un_cv (fun N => kp_series Lambda N (ursell * w)) (ln Z_Lambda).
       3. For any two polymers p1, p2 and the four sub-volumes
            Lambda, Lambda_1 = Lambda \ N(p1), Lambda_2 = Lambda \ N(p2),
            Lambda_12 = Lambda \ (N(p1) U N(p2)):
            Z_Lambda, Z_Lambda1, Z_Lambda2, Z_Lambda12 > 0,
            Un_cv (fun N => ursell_correlator ob Lambda N w p1 p2)
                  (ln ((Z_Lambda * Z_Lambda12) / (Z_Lambda1 * Z_Lambda2))),
          and
            |ln ((Z_Lambda * Z_Lambda12) / (Z_Lambda1 * Z_Lambda2))|
              <= a(p1) * exp(c) * exp(- c * dist(p1, p2)).

   Depends ONLY on Coq stdlib + rg.penrose_tree_bound + rg.poly_exp_bound
   + rg.tree_cut_bijection + rg.kotecky_preiss + rg.exp_series_limit.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra Permutation Wf_nat.
From rg Require Import penrose_tree_bound poly_exp_bound tree_cut_bijection
                       kotecky_preiss exp_series_limit.
Import ListNotations.
Import PenroseTreeBound PolyExpBound TreeCutBijection KoteckyPreiss ExpSeriesLimit.
Open Scope R_scope.

Module ClusterLogPartition.

  (* =======================================================================
     1. Pairwise Compatibility, Partition Function Z_Lambda, and Tuple Sums
     ======================================================================= *)

  Fixpoint pairwise_compat {P : Type} (ob : P -> P -> bool) (X : list P) : bool :=
    match X with
    | [] => true
    | x :: xs => forallb (fun y => negb (ob x y)) xs && pairwise_compat ob xs
    end.

  Definition partition_fn {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w : P -> R) : R :=
    fold_right Rplus 0
      (map (fun S => if pairwise_compat ob S then prod_weight w S else 0) (sublists Lambda)).

  Definition compat_tuple_sum {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w : P -> R) (n : nat) : R :=
    (/ INR (fact n)) *
    sum_over_tuples Lambda n (fun X => if pairwise_compat ob X then prod_weight w X else 0).

  Definition ursell_order {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w : P -> R) (n : nat) : R :=
    match n with
    | 0%nat => 0
    | S _ => (/ INR (fact n)) * sum_over_tuples Lambda n (fun X => ursell_fn ob X * prod_weight w X)
    end.

  Lemma sum_f_R0_ursell_order : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w : P -> R) N,
    sum_f_R0 (ursell_order ob Lambda w) N =
    kp_series Lambda N (fun X => ursell_fn ob X * prod_weight w X).
  Proof.
    intros P ob Lambda w. induction N as [| N' IH].
    - simpl. reflexivity.
    - change (sum_f_R0 (ursell_order ob Lambda w) (S N'))
        with (sum_f_R0 (ursell_order ob Lambda w) N' + ursell_order ob Lambda w (S N')).
      cbn [kp_series]. rewrite IH. reflexivity.
  Qed.

  (* =======================================================================
     2. Compatible Ordered-Tuple Sum = Subset Partition Function Z_Lambda
     ======================================================================= *)

  Lemma fold_right_Rplus_sublists_filter : forall {A : Type} (Pb : A -> bool) (l : list A) (f : list A -> R),
    fold_right Rplus 0 (map (fun S => if forallb Pb S then f S else 0) (sublists l)) =
    fold_right Rplus 0 (map f (sublists (filter Pb l))).
  Proof.
    intros A Pb l. induction l as [| a xs IH]; intro f.
    - simpl. ring.
    - simpl sublists. rewrite map_app, fold_right_Rplus_app, map_map.
      simpl filter. destruct (Pb a) eqn:Ea.
      + simpl sublists. rewrite map_app, fold_right_Rplus_app, map_map.
        rewrite (IH f). f_equal.
        transitivity (fold_right Rplus 0 (map (fun S => if forallb Pb S then f (a :: S) else 0) (sublists xs))).
        * apply fold_right_Rplus_ext. intros S _. simpl forallb. rewrite Ea. reflexivity.
        * exact (IH (fun S => f (a :: S))).
      + rewrite (IH f).
        assert (Hz : fold_right Rplus 0
          (map (fun S => if forallb Pb (a :: S) then f (a :: S) else 0) (sublists xs)) = 0).
        { transitivity (fold_right Rplus 0 (map (fun _ => 0) (sublists xs)));
            [| apply fold_right_Rplus_0].
          apply fold_right_Rplus_ext. intros S _. simpl forallb. rewrite Ea. reflexivity. }
        rewrite Hz. ring.
  Qed.

  Lemma partition_fn_nil : forall {P : Type} (ob : P -> P -> bool) (w : P -> R),
    partition_fn ob [] w = 1.
  Proof. intros P ob w. unfold partition_fn, prod_weight, prod_list; simpl; ring. Qed.

  Lemma partition_fn_cons : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Lambda' : list P) (w : P -> R),
    partition_fn ob (p0 :: Lambda') w =
    partition_fn ob Lambda' w +
    w p0 * partition_fn ob (filter (fun q => negb (ob p0 q)) Lambda') w.
  Proof.
    intros P ob p0 Lambda' w.
    unfold partition_fn at 1. simpl sublists.
    rewrite map_app, fold_right_Rplus_app, map_map.
    f_equal.
    transitivity (w p0 * fold_right Rplus 0
      (map (fun S => if forallb (fun q => negb (ob p0 q)) S
                     then (if pairwise_compat ob S then prod_weight w S else 0)
                     else 0) (sublists Lambda'))).
    - rewrite <- fold_right_Rplus_scale. apply fold_right_Rplus_ext. intros S _.
      simpl pairwise_compat. unfold prod_weight, prod_list; simpl.
      destruct (forallb (fun q => negb (ob p0 q)) S); destruct (pairwise_compat ob S); simpl; ring.
    - f_equal. apply fold_right_Rplus_sublists_filter.
  Qed.

  Lemma fold_right_Rplus_filter : forall {A : Type} (Pb : A -> bool) (g : A -> R) (l : list A),
    fold_right Rplus 0 (map (fun x => if Pb x then g x else 0) l) =
    fold_right Rplus 0 (map g (filter Pb l)).
  Proof.
    intros A Pb g. induction l as [| a xs IH]; simpl; [reflexivity |].
    destruct (Pb a); simpl; [rewrite IH; ring | rewrite IH; ring].
  Qed.

  Lemma sum_over_tuples_filter : forall {P : Type} (Pb : P -> bool) (Lambda : list P) n (f : list P -> R),
    sum_over_tuples Lambda n (fun X => if forallb Pb X then f X else 0) =
    sum_over_tuples (filter Pb Lambda) n f.
  Proof.
    intros P Pb Lambda n. induction n as [| n' IH]; intro f.
    - rewrite !sum_over_tuples_0. simpl. reflexivity.
    - rewrite !sum_over_tuples_S.
      rewrite <- fold_right_Rplus_filter.
      apply fold_right_Rplus_ext. intros p _.
      destruct (Pb p) eqn:Ep.
      + transitivity (sum_over_tuples Lambda n' (fun Y => if forallb Pb Y then f (p :: Y) else 0)).
        * apply sum_over_tuples_ext. intros Y _. simpl forallb. rewrite Ep. reflexivity.
        * exact (IH (fun Y => f (p :: Y))).
      + transitivity (sum_over_tuples Lambda n' (fun _ => 0)).
        * apply sum_over_tuples_ext. intros Y _. simpl forallb. rewrite Ep. reflexivity.
        * unfold sum_over_tuples. apply fold_right_Rplus_0.
  Qed.

  Fixpoint interleave_const {P : Type} (p0 : P) (m : list bool) (Y : list P) : list P :=
    match m with
    | [] => []
    | true :: m' => p0 :: interleave_const p0 m' Y
    | false :: m' =>
        match Y with
        | [] => []
        | y :: ys => y :: interleave_const p0 m' ys
        end
    end.

  Lemma interleave_const_all_false : forall {P : Type} (p0 : P) (m : list bool) (Y : list P),
    count_true m = 0%nat -> length Y = length m -> interleave_const p0 m Y = Y.
  Proof.
    intros P p0. induction m as [| [|] m' IH]; intros [| y ys] Hc Hlen;
      simpl in *; try discriminate; try reflexivity.
    f_equal. apply IH; lia.
  Qed.

  Lemma interleave_const_in_p0 : forall {P : Type} (p0 : P) (m : list bool) (Y : list P),
    (1 <= count_true m)%nat ->
    length Y = (length m - count_true m)%nat ->
    In p0 (interleave_const p0 m Y).
  Proof.
    intros P p0. induction m as [| [|] m' IH]; intros Y Hc Hlen;
      cbn [interleave_const count_true length In] in *; try lia.
    - left; reflexivity.
    - pose proof (count_true_le m').
      destruct Y as [| y ys]; cbn [length In] in *; try lia.
      right. apply IH; lia.
  Qed.

  Lemma forallb_false_of_in : forall {A : Type} (f : A -> bool) (l : list A) (x : A),
    In x l -> f x = false -> forallb f l = false.
  Proof.
    intros A f l x Hin Hfx. destruct (forallb f l) eqn:E; [| reflexivity].
    rewrite forallb_forall in E. rewrite (E x Hin) in Hfx. discriminate.
  Qed.

  Lemma interleave_const_compat_ge2 : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (m : list bool) (Y : list P),
    (forall p, ob p p = true) ->
    (2 <= count_true m)%nat ->
    length Y = (length m - count_true m)%nat ->
    pairwise_compat ob (interleave_const p0 m Y) = false.
  Proof.
    intros P ob p0. induction m as [| [|] m' IH]; intros Y Hrefl Hc Hlen;
      cbn [interleave_const count_true length pairwise_compat] in *; try lia.
    - replace (forallb (fun y => negb (ob p0 y)) (interleave_const p0 m' Y)) with false; [reflexivity |].
      symmetry. apply forallb_false_of_in with (x := p0).
      + apply interleave_const_in_p0; lia.
      + rewrite Hrefl; reflexivity.
    - pose proof (count_true_le m').
      destruct Y as [| y ys]; cbn [length pairwise_compat] in *; try lia.
      rewrite (IH ys Hrefl Hc ltac:(lia)), andb_false_r. reflexivity.
  Qed.

  Lemma forallb_interleave_const_1 : forall {P : Type} (f : P -> bool) (p0 : P) (m : list bool) (Y : list P),
    count_true m = 1%nat ->
    length Y = (length m - 1)%nat ->
    forallb f (interleave_const p0 m Y) = f p0 && forallb f Y.
  Proof.
    intros P f p0. induction m as [| [|] m' IH]; intros Y Hc Hlen;
      cbn [interleave_const count_true length forallb] in *; try lia.
    - assert (Hc' : count_true m' = 0%nat) by lia.
      rewrite (interleave_const_all_false p0 m' Y Hc' ltac:(lia)). reflexivity.
    - pose proof (count_true_le m').
      destruct Y as [| y ys]; cbn [length forallb] in *; try lia.
      rewrite (IH ys Hc ltac:(lia)). destruct (f y), (f p0); reflexivity.
  Qed.

  Lemma interleave_const_compat_1 : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (m : list bool) (Y : list P),
    (forall x y, ob x y = ob y x) ->
    count_true m = 1%nat ->
    length Y = (length m - 1)%nat ->
    pairwise_compat ob (interleave_const p0 m Y) =
    forallb (fun y => negb (ob p0 y)) Y && pairwise_compat ob Y.
  Proof.
    intros P ob p0. induction m as [| [|] m' IH]; intros Y Hsym Hc Hlen;
      cbn [interleave_const count_true length pairwise_compat forallb] in *; try lia.
    - assert (Hc' : count_true m' = 0%nat) by lia.
      rewrite (interleave_const_all_false p0 m' Y Hc' ltac:(lia)). reflexivity.
    - pose proof (count_true_le m').
      destruct Y as [| y ys]; cbn [length pairwise_compat forallb] in *; try lia.
      rewrite (forallb_interleave_const_1 (fun z => negb (ob y z)) p0 m' ys Hc ltac:(lia)).
      rewrite (IH ys Hsym Hc ltac:(lia)), (Hsym y p0).
      destruct (ob p0 y), (forallb (fun z => negb (ob y z)) ys),
               (forallb (fun z => negb (ob p0 z)) ys), (pairwise_compat ob ys); reflexivity.
  Qed.

  Lemma prod_weight_interleave_const_1 : forall {P : Type} (w : P -> R) (p0 : P) (m : list bool) (Y : list P),
    count_true m = 1%nat ->
    length Y = (length m - 1)%nat ->
    prod_weight w (interleave_const p0 m Y) = w p0 * prod_weight w Y.
  Proof.
    intros P w p0. induction m as [| [|] m' IH]; intros Y Hc Hlen;
      cbn [interleave_const count_true length] in *; try lia.
    - assert (Hc' : count_true m' = 0%nat) by lia.
      rewrite (interleave_const_all_false p0 m' Y Hc' ltac:(lia)).
      unfold prod_weight, prod_list; simpl; ring.
    - pose proof (count_true_le m').
      destruct Y as [| y ys]; cbn [length] in *; try lia.
      unfold prod_weight, prod_list in *; simpl.
      rewrite (IH ys Hc ltac:(lia)). ring.
  Qed.

  Lemma sum_over_tuples_cons : forall {P : Type} (p0 : P) (Lambda' : list P) n (F : list P -> R),
    sum_over_tuples (p0 :: Lambda') n F =
    fold_right Rplus 0 (map (fun m =>
      sum_over_tuples Lambda' (n - count_true m) (fun Y => F (interleave_const p0 m Y)))
      (all_masks n)).
  Proof.
    intros P p0 Lambda' n. induction n as [| n' IH]; intro F.
    - rewrite sum_over_tuples_0. simpl. rewrite sum_over_tuples_0. ring.
    - rewrite sum_over_tuples_S. cbn [map fold_right all_masks].
      rewrite map_app, fold_right_Rplus_app, !map_map.
      f_equal.
      + rewrite (IH (fun X => F (p0 :: X))).
        apply fold_right_Rplus_ext. intros m _.
        simpl count_true. replace (S n' - S (count_true m))%nat with (n' - count_true m)%nat by lia.
        reflexivity.
      + transitivity (fold_right Rplus 0 (map (fun q =>
          fold_right Rplus 0 (map (fun m =>
            sum_over_tuples Lambda' (n' - count_true m) (fun Y => F (q :: interleave_const p0 m Y)))
            (all_masks n'))) Lambda')).
        * apply fold_right_Rplus_ext. intros q _. exact (IH (fun X => F (q :: X))).
        * rewrite fold_right_Rplus_swap.
          apply fold_right_Rplus_ext. intros m Hm.
          apply all_masks_in in Hm. pose proof (count_true_le m).
          simpl count_true.
          replace (S n' - count_true m)%nat with (S (n' - count_true m)) by lia.
          rewrite sum_over_tuples_S. reflexivity.
  Qed.

  Lemma binomial_n_1 : forall n, binomial n 1%nat = n.
  Proof.
    induction n as [| n' IH]; [reflexivity |].
    change (binomial (S n') 1%nat) with (binomial n' 0%nat + binomial n' 1%nat)%nat.
    rewrite IH. destruct n'; reflexivity.
  Qed.

  Lemma compat_tuple_sum_0 : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w : P -> R),
    compat_tuple_sum ob Lambda w 0%nat = 1.
  Proof.
    intros P ob Lambda w. unfold compat_tuple_sum.
    rewrite sum_over_tuples_0. unfold prod_weight, prod_list; simpl; field.
  Qed.

  Lemma compat_tuple_sum_cons_S : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Lambda' : list P) (w : P -> R) k,
    (forall p, ob p p = true) ->
    (forall x y, ob x y = ob y x) ->
    compat_tuple_sum ob (p0 :: Lambda') w (S k) =
    compat_tuple_sum ob Lambda' w (S k) +
    w p0 * compat_tuple_sum ob (filter (fun q => negb (ob p0 q)) Lambda') w k.
  Proof.
    intros P ob p0 Lambda' w k Hrefl Hsym.
    set (F := fun X => if pairwise_compat ob X then prod_weight w X else 0).
    set (L0 := filter (fun q => negb (ob p0 q)) Lambda').
    set (g := fun r =>
      match r with
      | 0%nat => sum_over_tuples Lambda' (S k) F
      | 1%nat => w p0 * sum_over_tuples L0 k F
      | _ => 0
      end).
    assert (Hsum : sum_over_tuples (p0 :: Lambda') (S k) F =
      sum_over_tuples Lambda' (S k) F + INR (S k) * (w p0 * sum_over_tuples L0 k F)).
    { rewrite sum_over_tuples_cons.
      transitivity (fold_right Rplus 0 (map (fun m => g (count_true m)) (all_masks (S k)))).
      - apply fold_right_Rplus_ext. intros m Hm. apply all_masks_in in Hm.
        destruct (count_true m) as [| [| c']] eqn:Ec.
        + unfold g. replace (S k - 0)%nat with (S k) by lia.
          apply sum_over_tuples_ext. intros Y HY.
          pose proof (tuples_of_length_len Lambda' (S k) Y HY) as HlenY.
          rewrite (interleave_const_all_false p0 m Y Ec ltac:(lia)). reflexivity.
        + unfold g. replace (S k - 1)%nat with k by lia.
          unfold L0. rewrite <- sum_over_tuples_filter, <- sum_over_tuples_scale.
          apply sum_over_tuples_ext. intros Y HY.
          pose proof (tuples_of_length_len Lambda' k Y HY) as HlenY.
          unfold F.
          rewrite (interleave_const_compat_1 ob p0 m Y Hsym Ec ltac:(lia)).
          rewrite (prod_weight_interleave_const_1 w p0 m Y Ec ltac:(lia)).
          destruct (forallb (fun q => negb (ob p0 q)) Y); destruct (pairwise_compat ob Y); simpl; ring.
        + unfold g.
          transitivity (sum_over_tuples Lambda' (S k - S (S c')) (fun _ => 0)).
          * apply sum_over_tuples_ext. intros Y HY.
            pose proof (tuples_of_length_len Lambda' (S k - S (S c')) Y HY) as HlenY.
            unfold F.
            rewrite (interleave_const_compat_ge2 ob p0 m Y Hrefl ltac:(lia) ltac:(lia)). reflexivity.
          * unfold sum_over_tuples. apply fold_right_Rplus_0.
      - rewrite (sum_over_all_masks_by_count (S k) g).
        assert (Hcollapse : forall N, (1 <= N)%nat ->
          sum_f_R0 (fun r => INR (binomial N r) * g r) N =
          INR (binomial N 0%nat) * g 0%nat + INR (binomial N 1%nat) * g 1%nat).
        { intros N HN.
          destruct N as [| N']; [lia |].
          destruct N' as [| N''].
          - simpl. ring.
          - assert (Htail : forall m, (1 <= m)%nat ->
              sum_f_R0 (fun r => INR (binomial (S (S N'')) r) * g r) m =
              INR (binomial (S (S N'')) 0%nat) * g 0%nat + INR (binomial (S (S N'')) 1%nat) * g 1%nat).
            { induction m as [| m' IHm]; intro Hm; [lia |].
              destruct m' as [| m''].
              - simpl. ring.
              - change (sum_f_R0 (fun r => INR (binomial (S (S N'')) r) * g r) (S (S m'')))
                  with (sum_f_R0 (fun r => INR (binomial (S (S N'')) r) * g r) (S m'') +
                        INR (binomial (S (S N'')) (S (S m''))) * g (S (S m''))).
                rewrite (IHm ltac:(lia)). unfold g at 3. ring. }
            apply Htail; lia. }
        rewrite (Hcollapse (S k) ltac:(lia)).
        rewrite binomial_n_1.
        assert (Hb0 : binomial (S k) 0%nat = 1%nat) by reflexivity.
        rewrite Hb0. simpl INR. unfold g. ring. }
    unfold compat_tuple_sum. fold F L0. rewrite Hsum.
    assert (HfactS : INR (fact (S k)) = INR (S k) * INR (fact k)).
    { change (fact (S k)) with (S k * fact k)%nat. rewrite mult_INR. reflexivity. }
    assert (Hne1 : INR (S k) <> 0) by (apply not_0_INR; lia).
    assert (Hne2 : INR (fact k) <> 0) by (apply not_0_INR, fact_neq_0).
    rewrite HfactS. field. split; assumption.
  Qed.

  Lemma length_filter_le : forall {A : Type} (f : A -> bool) (l : list A),
    (length (filter f l) <= length l)%nat.
  Proof.
    induction l as [| a xs IH]; simpl; [lia |].
    destruct (f a); simpl; lia.
  Qed.

  Lemma compat_tuple_sum_zero_gt : forall {P : Type} (ob : P -> P -> bool) (w : P -> R) (Lambda : list P),
    (forall p, ob p p = true) ->
    (forall x y, ob x y = ob y x) ->
    forall n, (length Lambda < n)%nat -> compat_tuple_sum ob Lambda w n = 0.
  Proof.
    intros P ob w Lambda Hrefl Hsym.
    remember (length Lambda) as m eqn:Hm. revert Lambda Hm.
    induction m as [m IH] using lt_wf_ind.
    intros Lambda Hm n Hn.
    destruct Lambda as [| p0 Lambda'].
    - destruct n as [| n']; [simpl in *; lia |].
      unfold compat_tuple_sum, sum_over_tuples. simpl. ring.
    - destruct n as [| k]; [simpl in *; lia |].
      rewrite (compat_tuple_sum_cons_S ob p0 Lambda' w k Hrefl Hsym).
      simpl length in Hm.
      rewrite (IH (length Lambda') ltac:(lia) Lambda' eq_refl (S k) ltac:(lia)).
      pose proof (length_filter_le (fun q => negb (ob p0 q)) Lambda') as Hfl.
      rewrite (IH (length (filter (fun q => negb (ob p0 q)) Lambda')) ltac:(lia)
                  (filter (fun q => negb (ob p0 q)) Lambda') eq_refl k ltac:(lia)).
      ring.
  Qed.

  Theorem compat_tuple_sum_eq_partition_fn : forall {P : Type} (ob : P -> P -> bool) (w : P -> R) (Lambda : list P),
    (forall p, ob p p = true) ->
    (forall x y, ob x y = ob y x) ->
    sum_f_R0 (compat_tuple_sum ob Lambda w) (length Lambda) = partition_fn ob Lambda w.
  Proof.
    intros P ob w Lambda Hrefl Hsym.
    remember (length Lambda) as m eqn:Hm. revert Lambda Hm.
    induction m as [m IH] using lt_wf_ind.
    intros Lambda Hm.
    destruct Lambda as [| p0 Lambda']; subst m.
    - cbn [length sum_f_R0]. rewrite compat_tuple_sum_0, partition_fn_nil. reflexivity.
    - cbn [length] in *.
      rewrite partition_fn_cons.
      set (L0 := filter (fun q => negb (ob p0 q)) Lambda').
      rewrite sum_f_R0_shift.
      rewrite compat_tuple_sum_0.
      transitivity (1 + sum_f_R0 (fun k =>
        compat_tuple_sum ob Lambda' w (S k) + w p0 * compat_tuple_sum ob L0 w k) (length Lambda')).
      + f_equal. apply sum_f_R0_ext. intros k _.
        exact (compat_tuple_sum_cons_S ob p0 Lambda' w k Hrefl Hsym).
      + rewrite sum_f_R0_plus, sum_f_R0_scale.
        replace (1 + (sum_f_R0 (fun k => compat_tuple_sum ob Lambda' w (S k)) (length Lambda') +
                      w p0 * sum_f_R0 (compat_tuple_sum ob L0 w) (length Lambda')))
           with ((compat_tuple_sum ob Lambda' w 0%nat +
                  sum_f_R0 (fun k => compat_tuple_sum ob Lambda' w (S k)) (length Lambda')) +
                 w p0 * sum_f_R0 (compat_tuple_sum ob L0 w) (length Lambda'))
          by (rewrite compat_tuple_sum_0; ring).
        rewrite <- sum_f_R0_shift.
        change (sum_f_R0 (compat_tuple_sum ob Lambda' w) (S (length Lambda')))
          with (sum_f_R0 (compat_tuple_sum ob Lambda' w) (length Lambda') +
                compat_tuple_sum ob Lambda' w (S (length Lambda'))).
        rewrite (compat_tuple_sum_zero_gt ob w Lambda' Hrefl Hsym (S (length Lambda')) ltac:(lia)), Rplus_0_r.
        rewrite (IH (length Lambda') ltac:(lia) Lambda' eq_refl).
        f_equal. f_equal.
        assert (Htail : forall K, (length L0 <= K)%nat ->
          sum_f_R0 (compat_tuple_sum ob L0 w) K = sum_f_R0 (compat_tuple_sum ob L0 w) (length L0)).
        { intros K HK. induction HK as [| K' HK' IHK]; [reflexivity |].
          change (sum_f_R0 (compat_tuple_sum ob L0 w) (S K'))
            with (sum_f_R0 (compat_tuple_sum ob L0 w) K' + compat_tuple_sum ob L0 w (S K')).
          rewrite IHK, (compat_tuple_sum_zero_gt ob w L0 Hrefl Hsym (S K') ltac:(lia)). ring. }
        pose proof (length_filter_le (fun q => negb (ob p0 q)) Lambda') as Hfl.
        fold L0 in Hfl.
        rewrite (Htail (length Lambda') Hfl).
        exact (IH (length L0) ltac:(lia) L0 eq_refl).
  Qed.

  (* =======================================================================
     3. Graph-Component Bijection & Exact Ursell-Partition Recurrence
     ======================================================================= *)

  Lemma pairs_with_head_nil_iff : forall {P : Type} (ob : P -> P -> bool) i x j xs,
    pairs_with_head ob i x j xs = [] <-> forallb (fun y => negb (ob x y)) xs = true.
  Proof.
    intros P ob i x j xs. revert j. induction xs as [| y ys IH]; intro j; [simpl; tauto |].
    simpl. destruct (ob x y); simpl.
    - split; [discriminate | discriminate].
    - exact (IH (S j)).
  Qed.

  Lemma graph_edges_from_nil_iff : forall {P : Type} (ob : P -> P -> bool) X i,
    graph_edges_from ob i X = [] <-> pairwise_compat ob X = true.
  Proof.
    intros P ob. induction X as [| x xs IH]; intro i; [simpl; tauto |].
    simpl. rewrite andb_true_iff. split.
    - intro H. apply app_eq_nil in H. destruct H as [H1 H2].
      split; [apply (pairs_with_head_nil_iff ob i x (S i) xs); exact H1 | apply (IH (S i)); exact H2].
    - intros [H1 H2].
      apply (pairs_with_head_nil_iff ob i x (S i) xs) in H1.
      apply (IH (S i)) in H2. rewrite H1, H2. reflexivity.
  Qed.

  Lemma graph_edges_nil_iff_compat : forall {P : Type} (ob : P -> P -> bool) (X : list P),
    graph_edges ob X = [] <-> pairwise_compat ob X = true.
  Proof. intros P ob X. apply graph_edges_from_nil_iff. Qed.

  Lemma sum_all_subgraphs_eq_compat : forall {P : Type} (ob : P -> P -> bool) (X : list P),
    fold_right Rplus 0 (map (fun H => (-1) ^ length H) (sublists (graph_edges ob X))) =
    if pairwise_compat ob X then 1 else 0.
  Proof.
    intros P ob X.
    pose proof (sum_sublists_interval (graph_edges ob X) (fun _ => false) (fun _ => true)
                  (proj1 (graph_edges_wf ob X)) (fun _ _ H => ltac:(discriminate))) as Hsum.
    transitivity (fold_right Rplus 0 (map (fun H =>
      if forallb (fun e => negb false || edge_mem e H) (graph_edges ob X) && forallb (fun _ => true) H
      then (-1) ^ length H else 0) (sublists (graph_edges ob X)))).
    - apply fold_right_Rplus_ext. intros H _.
      assert (H1 : forall {A : Type} (l : list A), forallb (fun _ => true) l = true).
      { induction l; simpl; [reflexivity | exact IHl]. }
      cbn [negb orb]. rewrite !H1. reflexivity.
    - rewrite Hsum.
      destruct (graph_edges ob X) as [| e es] eqn:Eg.
      + assert (Hc : pairwise_compat ob X = true) by (apply graph_edges_nil_iff_compat; exact Eg).
        rewrite Hc. simpl. reflexivity.
      + assert (Hc : pairwise_compat ob X = false).
        { destruct (pairwise_compat ob X) eqn:Ec; [| reflexivity].
          apply graph_edges_nil_iff_compat in Ec. rewrite Eg in Ec. discriminate. }
        rewrite Hc. simpl. reflexivity.
  Qed.

  Lemma Permutation_fold_right_Rplus : forall l1 l2,
    Permutation l1 l2 -> fold_right Rplus 0 l1 = fold_right Rplus 0 l2.
  Proof.
    intros l1 l2 Hp. induction Hp; simpl; try lra.
  Qed.

  Definition join_comp (E : list (nat * nat)) (mask : list bool)
    (HA HB : list (nat * nat)) : list (nat * nat) :=
    filter (fun e => edge_mem e (embed_edges (pos_A mask) HA ++ embed_edges (pos_B0 mask) HB)) E.

  Definition split_comp {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P)
    (H : list (nat * nat)) : list bool * list (nat * nat) * list (nat * nat) :=
    let mask := mask_of_tree (length Y) H in
    let HA := project_edges (pos_A mask) (graph_edges ob (select_true mask Y)) H in
    let HB := project_edges (pos_B0 mask) (graph_edges ob (p0 :: select_false mask Y)) H in
    (mask, HA, HB).

  Definition valid_comp_triples {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P)
    : list (list bool * list (nat * nat) * list (nat * nat)) :=
    flat_map (fun mask =>
      let YA := select_true mask Y in
      let YB := p0 :: select_false mask Y in
      let connsB := filter (is_connectedb (length YB)) (sublists (graph_edges ob YB)) in
      let subsA := sublists (graph_edges ob YA) in
      flat_map (fun HB => map (fun HA => (mask, HA, HB)) subsA) connsB)
      (all_masks (length Y)).

  Lemma valid_comp_triples_in : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P) mask HA HB,
    In (mask, HA, HB) (valid_comp_triples ob p0 Y) <->
    length mask = length Y /\
    In HA (sublists (graph_edges ob (select_true mask Y))) /\
    In HB (sublists (graph_edges ob (p0 :: select_false mask Y))) /\
    is_connectedb (S (length Y - count_true mask)) HB = true.
  Proof.
    intros P ob p0 Y mask HA HB. unfold valid_comp_triples. rewrite in_flat_map. split.
    - intros [m [Hm Hin1]]. apply all_masks_in in Hm.
      rewrite in_flat_map in Hin1. destruct Hin1 as [hb [Hhb Hin2]].
      rewrite filter_In in Hhb. destruct Hhb as [Hhb_sub Hhb_conn].
      rewrite in_map_iff in Hin2. destruct Hin2 as [ha [Heq Hha]].
      inversion Heq; subst m ha hb.
      simpl length in Hhb_conn. rewrite (select_false_length mask Y Hm), Hm in Hhb_conn.
      repeat split; assumption.
    - intros [Hmlen [HHA [HHB Hconn]]].
      exists mask. split; [apply all_masks_in; exact Hmlen |].
      rewrite in_flat_map. exists HB. split.
      + apply filter_In. split; [exact HHB |].
        simpl length. rewrite (select_false_length mask Y Hmlen), Hmlen. exact Hconn.
      + rewrite in_map_iff. exists HA. split; [reflexivity | exact HHA].
  Qed.

  Lemma valid_comp_triples_NoDup : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P),
    NoDup (valid_comp_triples ob p0 Y).
  Proof.
    intros P ob p0 Y. unfold valid_comp_triples.
    apply NoDup_flat_map_local; [apply all_masks_NoDup | |].
    - intros mask _.
      apply NoDup_flat_map_local.
      + apply NoDup_filter, sublists_NoDup_list, (proj1 (graph_edges_wf ob _)).
      + intros HB _. apply NoDup_map_in.
        * apply sublists_NoDup_list, (proj1 (graph_edges_wf ob _)).
        * intros a1 a2 _ _ H; inversion H; reflexivity.
      + intros b1 b2 [[m a] b] _ _ H1 H2.
        apply in_map_iff in H1; apply in_map_iff in H2.
        destruct H1 as [? [E1 _]]; destruct H2 as [? [E2 _]].
        inversion E1; inversion E2; congruence.
    - intros m1 m2 [[m a] b] _ _ H1 H2.
      apply in_flat_map in H1; destruct H1 as [? [_ H1]]; apply in_map_iff in H1; destruct H1 as [? [E1 _]].
      apply in_flat_map in H2; destruct H2 as [? [_ H2]]; apply in_map_iff in H2; destruct H2 as [? [E2 _]].
      inversion E1; inversion E2; congruence.
  Qed.

  Lemma join_comp_spec : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P) mask HA HB,
    In (mask, HA, HB) (valid_comp_triples ob p0 Y) ->
    let E := graph_edges ob (p0 :: Y) in
    let H := join_comp E mask HA HB in
    In H (sublists E) /\
    length H = (length HA + length HB)%nat /\
    split_comp ob p0 Y H = (mask, HA, HB).
  Proof.
    intros P ob p0 Y mask HA HB Htrip.
    apply valid_comp_triples_in in Htrip.
    destruct Htrip as [Hmlen [HHA [HHB HconnB]]].
    set (k := length Y).
    set (E := graph_edges ob (p0 :: Y)).
    set (EA := graph_edges ob (select_true mask Y)).
    set (EB := graph_edges ob (p0 :: select_false mask Y)).
    set (comb := embed_edges (pos_A mask) HA ++ embed_edges (pos_B0 mask) HB).
    set (H := join_comp E mask HA HB).
    pose proof (graph_edges_wf ob (p0 :: Y)) as HwfE. simpl length in HwfE. fold E k in HwfE.
    pose proof (graph_edges_wf ob (select_true mask Y)) as HwfEA.
    rewrite (select_true_length mask Y Hmlen) in HwfEA. fold EA in HwfEA.
    pose proof (graph_edges_wf ob (p0 :: select_false mask Y)) as HwfEB.
    simpl length in HwfEB. rewrite (select_false_length mask Y Hmlen) in HwfEB. fold EB in HwfEB.
    assert (Hcomb_in_E : incl comb E).
    { intros e He. unfold comb in He. apply in_app_iff in He. destruct He as [He | He].
      - unfold embed_edges in He. apply in_map_iff in He. destruct He as [eA [<- HeA]].
        apply (embed_A_in_E ob p0 mask Y eA Hmlen). exact (sublists_incl EA HA HHA _ HeA).
      - unfold embed_edges in He. apply in_map_iff in He. destruct He as [eB [<- HeB]].
        apply (embed_B0_in_E ob p0 mask Y eB Hmlen). exact (sublists_incl EB HB HHB _ HeB). }
    assert (HH_iff : forall e, In e H <-> In e comb).
    { intro e. unfold H, join_comp. fold comb. rewrite filter_In, edge_mem_iff.
      split; [intros [_ h]; exact h | intro h; split; [apply Hcomb_in_E; exact h | exact h]]. }
    assert (HforA_pos : Forall (fun e => (fst e < snd e)%nat /\ (snd e < length (pos_A mask))%nat) HA).
    { rewrite pos_A_length. exact (sublists_Forall _ EA HA (proj2 HwfEA) HHA). }
    assert (HforB_pos : Forall (fun e => (fst e < snd e)%nat /\ (snd e < length (pos_B0 mask))%nat) HB).
    { rewrite pos_B0_length. exact (sublists_Forall _ EB HB (proj2 HwfEB) HHB). }
    assert (Hnd_embA : NoDup (embed_edges (pos_A mask) HA)).
    { apply NoDup_map_in; [exact (sublists_NoDup_elem EA HA (proj1 HwfEA) HHA) |].
      intros [u1 v1] [u2 v2] H1 H2 Heq.
      pose proof HforA_pos as Hf. rewrite Forall_forall in Hf.
      pose proof (Hf (u1, v1) H1) as L1; pose proof (Hf (u2, v2) H2) as L2. cbn [fst snd] in L1, L2.
      injection Heq as E1 E2. f_equal; apply (pos_A_inj mask); lia || assumption. }
    assert (Hnd_embB : NoDup (embed_edges (pos_B0 mask) HB)).
    { apply NoDup_map_in; [exact (sublists_NoDup_elem EB HB (proj1 HwfEB) HHB) |].
      intros [u1 v1] [u2 v2] H1 H2 Heq.
      pose proof HforB_pos as Hf. rewrite Forall_forall in Hf.
      pose proof (Hf (u1, v1) H1) as L1; pose proof (Hf (u2, v2) H2) as L2. cbn [fst snd] in L1, L2.
      injection Heq as E1 E2. f_equal; apply (pos_B0_inj mask); lia || assumption. }
    assert (Hnd_comb : NoDup comb).
    { unfold comb. apply NoDup_app_local; [exact Hnd_embA | exact Hnd_embB |].
      intros [u v] H1 H2.
      destruct (embed_edges_in_pos _ _ _ _ HforA_pos H1) as [HuA _].
      destruct (embed_edges_in_pos _ _ _ _ HforB_pos H2) as [HuB _].
      exact (pos_A_B0_disjoint mask u HuA HuB). }
    assert (HsubH : In H (sublists E)) by (unfold H, join_comp; apply filter_in_sublists).
    assert (HlenH : length H = (length HA + length HB)%nat).
    { assert (HndH : NoDup H) by (unfold H, join_comp; apply NoDup_filter; exact (proj1 HwfE)).
      assert (Hperm : Permutation H comb) by (apply NoDup_Permutation; assumption).
      rewrite (Permutation_length Hperm). unfold comb. rewrite app_length.
      unfold embed_edges. rewrite !map_length. reflexivity. }
    (* Show reachable H 0 v <-> In v (pos_B0 mask) *)
    assert (Hreach_iff : forall v, (v < S k)%nat -> reachable H 0%nat v <-> In v (pos_B0 mask)).
    { intros v Hv. split.
      - intro Hr.
        assert (Hstay : forall u w, reachable H u w -> In u (pos_B0 mask) -> In w (pos_B0 mask)).
        { intros u w Hrw. induction Hrw; intro HuB; [exact HuB |].
          apply IHHrw.
          destruct H0 as [He | He]; apply HH_iff in He; unfold comb in He; apply in_app_iff in He;
            destruct He as [He | He].
          - destruct (embed_edges_in_pos _ _ _ _ HforA_pos He) as [HuA _].
            exfalso; exact (pos_A_B0_disjoint mask u HuA HuB).
          - destruct (embed_edges_in_pos _ _ _ _ HforB_pos He) as [_ HvB]; exact HvB.
          - destruct (embed_edges_in_pos _ _ _ _ HforA_pos He) as [_ HuA].
            exfalso; exact (pos_A_B0_disjoint mask u HuA HuB).
          - destruct (embed_edges_in_pos _ _ _ _ HforB_pos He) as [HvB _]; exact HvB. }
        apply (Hstay 0%nat v Hr). unfold pos_B0. left; reflexivity.
      - intro HvB.
        pose proof (sublists_Forall _ EB HB (proj2 HwfEB) HHB) as HforB.
        rewrite <- Hmlen in HconnB.
        apply (is_connectedb_iff _ _ HforB) in HconnB. destruct HconnB as [_ HreachB].
        assert (HliftB : forall u w, reachable HB u w ->
          reachable H (nth u (pos_B0 mask) 0%nat) (nth w (pos_B0 mask) 0%nat)).
        { intros u w Hrw. induction Hrw; [apply reach_refl |].
          eapply reach_step; [| exact IHHrw].
          destruct H0 as [Ha | Hb]; [left | right]; apply HH_iff; unfold comb; apply in_app_iff; right;
            unfold embed_edges;
            [apply (in_map (fun e => (nth (fst e) (pos_B0 mask) 0%nat, nth (snd e) (pos_B0 mask) 0%nat)) _ (u, v0) Ha) |
             apply (in_map (fun e => (nth (fst e) (pos_B0 mask) 0%nat, nth (snd e) (pos_B0 mask) 0%nat)) _ (v0, u) Hb)]. }
        destruct (index_of_spec v (pos_B0 mask) HvB) as [Hiv Hnv].
        rewrite pos_B0_length in Hiv.
        rewrite <- Hnv. change 0%nat with (nth 0%nat (pos_B0 mask) 0%nat).
        apply HliftB, HreachB. exact Hiv. }
    (* Hence mask_of_tree k H = mask *)
    assert (Hmask_eq : mask_of_tree k H = mask).
    { pose proof (sublists_Forall _ E H (proj2 HwfE) HsubH) as HwfH.
      apply nth_ext with (d := false) (d' := false).
      - unfold mask_of_tree. rewrite map_length, seq_length. symmetry; exact Hmlen.
      - intros i Hi. unfold mask_of_tree in Hi. rewrite map_length, seq_length in Hi.
        rewrite (mask_of_tree_nth k H i Hi).
        destruct (existsb (Nat.eqb (S i)) (expand_iter (S k) H [0%nat])) eqn:Ex; simpl.
        + apply expand_iter_0_iff in Ex.
          apply reachable_k_to_reachable in Ex.
          apply (Hreach_iff (S i) ltac:(lia)) in Ex.
          destruct (nth i mask false) eqn:Em; [| reflexivity].
          exfalso. apply (pos_A_B0_disjoint mask (S i)); [| exact Ex].
          apply pos_A_in. repeat split; try lia. replace (S i - 1)%nat with i by lia. exact Em.
        + destruct (nth i mask false) eqn:Em; [reflexivity |].
          exfalso.
          assert (HinB : In (S i) (pos_B0 mask)).
          { apply pos_B0_in. right. repeat split; try lia.
            replace (S i - 1)%nat with i by lia.
            erewrite nth_indep; [exact Em | lia]. }
          apply (Hreach_iff (S i) ltac:(lia)) in HinB.
          pose proof (reachable_bounded_length (S k) H 0%nat (S i) HwfH ltac:(lia) HinB) as Hrk.
          assert (Hrk' : reachable_k H (S k) 0%nat (S i)) by (eapply reachable_k_mono; [| exact Hrk]; lia).
          apply expand_iter_0_iff in Hrk'. congruence. }
    (* Hence project_edges recovers HA and HB *)
    assert (HprojA : project_edges (pos_A mask) EA H = HA).
    { apply (sublists_ext EA _ HA (proj1 HwfEA) (filter_in_sublists _ EA) HHA).
      intros [u v]. unfold project_edges. rewrite filter_In, edge_mem_iff, HH_iff.
      unfold comb; rewrite in_app_iff. split.
      - intros [HeEA [HinA | HinB]].
        + pose proof (proj2 HwfEA) as HforEA. rewrite Forall_forall in HforEA.
          pose proof (HforEA (u, v) HeEA) as L. simpl in L.
          apply (embed_edges_in_inv (pos_A mask) HA u v (pos_A_inj mask) HforA_pos);
            try (rewrite pos_A_length; lia); exact HinA.
        + pose proof (proj2 HwfEA) as HforEA. rewrite Forall_forall in HforEA.
          pose proof (HforEA (u, v) HeEA) as L. simpl in L.
          destruct (embed_edges_in_pos _ _ _ _ HforB_pos HinB) as [HuB _].
          exfalso. apply (pos_A_B0_disjoint mask (nth u (pos_A mask) 0%nat));
            [apply nth_In; rewrite pos_A_length; lia | exact HuB].
      - intro HinHA. split; [exact (sublists_incl EA HA HHA _ HinHA) |].
        left. unfold embed_edges.
        exact (in_map (fun e => (nth (fst e) (pos_A mask) 0%nat, nth (snd e) (pos_A mask) 0%nat)) HA (u, v) HinHA). }
    assert (HprojB : project_edges (pos_B0 mask) EB H = HB).
    { apply (sublists_ext EB _ HB (proj1 HwfEB) (filter_in_sublists _ EB) HHB).
      intros [u v]. unfold project_edges. rewrite filter_In, edge_mem_iff, HH_iff.
      unfold comb; rewrite in_app_iff. split.
      - intros [HeEB [HinA | HinB]].
        + pose proof (proj2 HwfEB) as HforEB. rewrite Forall_forall in HforEB.
          pose proof (HforEB (u, v) HeEB) as L. simpl in L.
          destruct (embed_edges_in_pos _ _ _ _ HforA_pos HinA) as [HuA _].
          exfalso. apply (pos_A_B0_disjoint mask (nth u (pos_B0 mask) 0%nat));
            [exact HuA | apply nth_In; rewrite pos_B0_length; lia].
        + pose proof (proj2 HwfEB) as HforEB. rewrite Forall_forall in HforEB.
          pose proof (HforEB (u, v) HeEB) as L. simpl in L.
          apply (embed_edges_in_inv (pos_B0 mask) HB u v (pos_B0_inj mask) HforB_pos);
            try (rewrite pos_B0_length; lia); exact HinB.
      - intro HinHB. split; [exact (sublists_incl EB HB HHB _ HinHB) |].
        right. unfold embed_edges.
        exact (in_map (fun e => (nth (fst e) (pos_B0 mask) 0%nat, nth (snd e) (pos_B0 mask) 0%nat)) HB (u, v) HinHB). }
    repeat split; [exact HsubH | exact HlenH |].
    unfold split_comp. fold E H k. rewrite Hmask_eq. fold EA EB. rewrite HprojA, HprojB. reflexivity.
  Qed.

  Lemma split_comp_spec : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P) H,
    In H (sublists (graph_edges ob (p0 :: Y))) ->
    let '(mask, HA, HB) := split_comp ob p0 Y H in
    In (mask, HA, HB) (valid_comp_triples ob p0 Y) /\
    join_comp (graph_edges ob (p0 :: Y)) mask HA HB = H.
  Proof.
    intros P ob p0 Y H HsubH.
    set (k := length Y).
    set (E := graph_edges ob (p0 :: Y)).
    pose proof (graph_edges_wf ob (p0 :: Y)) as HwfE. simpl length in HwfE. fold E k in HwfE.
    pose proof (sublists_Forall _ E H (proj2 HwfE) HsubH) as HwfH.
    set (mask := mask_of_tree k H).
    assert (Hmlen : length mask = k) by (unfold mask, mask_of_tree; rewrite map_length, seq_length; reflexivity).
    assert (Hmask_nth : forall i, (i < k)%nat ->
      nth i mask false = true <-> ~ reachable H 0%nat (S i)).
    { intros i Hi. unfold mask. rewrite (mask_of_tree_nth k H i Hi), negb_true_iff.
      destruct (existsb (Nat.eqb (S i)) (expand_iter (S k) H [0%nat])) eqn:Ex.
      - split; [discriminate |].
        intro Hnot. apply expand_iter_0_iff in Ex.
        exfalso. apply Hnot. exact (reachable_k_to_reachable H (S k) 0%nat (S i) Ex).
      - split; [intros _ Hreach | intros _; reflexivity].
        pose proof (reachable_bounded_length (S k) H 0%nat (S i) HwfH ltac:(lia) Hreach) as Hrk.
        assert (Hrk' : reachable_k H (S k) 0%nat (S i)) by (eapply reachable_k_mono; [| exact Hrk]; lia).
        apply expand_iter_0_iff in Hrk'. congruence. }
    assert (HposA_iff : forall v, (v < S k)%nat -> In v (pos_A mask) <-> ~ reachable H 0%nat v).
    { intros v Hv. rewrite pos_A_in, Hmlen. split.
      - intros [H1 [H2 H3]]. apply (Hmask_nth (v - 1)%nat ltac:(lia)) in H3.
        replace (S (v - 1)) with v in H3 by lia. exact H3.
      - intro Hnot.
        assert (Hvne0 : v <> 0%nat) by (intro Heq; subst; apply Hnot; apply reach_refl).
        repeat split; try lia.
        apply (Hmask_nth (v - 1)%nat ltac:(lia)). replace (S (v - 1)) with v by lia. exact Hnot. }
    assert (HposB_iff : forall v, (v < S k)%nat -> In v (pos_B0 mask) <-> reachable H 0%nat v).
    { intros v Hv. split.
      - intro HB. destruct (pos_A_B0_cover mask v ltac:(lia)) as [HA | _];
          [exfalso; exact (pos_A_B0_disjoint mask v HA HB) |].
        destruct (Nat.eq_dec v 0%nat) as [-> | Hne]; [apply reach_refl |].
        apply pos_B0_in in HB. destruct HB as [H0 | [H1 [H2 H3]]]; [congruence |].
        destruct (existsb (Nat.eqb v) (expand_iter (S k) H [0%nat])) eqn:Ex.
        + apply expand_iter_0_iff in Ex. exact (reachable_k_to_reachable H (S k) 0%nat v Ex).
        + exfalso.
          assert (Hnt : nth (v - 1)%nat mask false = true).
          { unfold mask. rewrite (mask_of_tree_nth k H (v - 1)%nat ltac:(lia)).
            replace (S (v - 1)) with v by lia. rewrite Ex; reflexivity. }
          erewrite (nth_indep mask true false) in H3; [congruence | lia].
      - intro H0v. destruct (pos_A_B0_cover mask v ltac:(lia)) as [HA | HB]; [| exact HB].
        exfalso. apply (HposA_iff v Hv) in HA. contradiction. }
    set (EA := graph_edges ob (select_true mask Y)).
    set (EB := graph_edges ob (p0 :: select_false mask Y)).
    set (HA := project_edges (pos_A mask) EA H).
    set (HB := project_edges (pos_B0 mask) EB H).
    pose proof (graph_edges_wf ob (select_true mask Y)) as HwfEA.
    rewrite (select_true_length mask Y Hmlen) in HwfEA. fold EA in HwfEA.
    pose proof (graph_edges_wf ob (p0 :: select_false mask Y)) as HwfEB.
    simpl length in HwfEB. rewrite (select_false_length mask Y Hmlen) in HwfEB. fold EB in HwfEB.
    assert (HsubHA : In HA (sublists EA)) by (unfold HA, project_edges; apply filter_in_sublists).
    assert (HsubHB : In HB (sublists EB)) by (unfold HB, project_edges; apply filter_in_sublists).
    (* Every edge of H lies in embed(HA) or embed(HB) *)
    assert (HH_split : forall e, In e H ->
      In e (embed_edges (pos_A mask) HA) \/ In e (embed_edges (pos_B0 mask) HB)).
    { intros [u v] He.
      pose proof HwfH as HforH. rewrite Forall_forall in HforH.
      pose proof (HforH (u, v) He) as Huv. simpl in Huv.
      destruct (pos_A_B0_cover mask u ltac:(lia)) as [HuA | HuB].
      - left.
        assert (HvA : In v (pos_A mask)).
        { apply (HposA_iff v ltac:(lia)). intro H0v.
          apply (HposA_iff u ltac:(lia)) in HuA. apply HuA.
          eapply reachable_trans; [exact H0v | eapply reach_step; [right; exact He | apply reach_refl]]. }
        destruct (index_of_spec u (pos_A mask) HuA) as [Hiu Hnu].
        destruct (index_of_spec v (pos_A mask) HvA) as [Hiv Hnv].
        rewrite pos_A_length in Hiu, Hiv.
        assert (Hiuv : (index_of u (pos_A mask) < index_of v (pos_A mask))%nat).
        { destruct (lt_eq_lt_dec (index_of u (pos_A mask)) (index_of v (pos_A mask))) as [[Hlt | Heq] | Hgt];
            [exact Hlt | rewrite <- Hnu, <- Hnv, Heq in Huv; lia |].
          pose proof (pos_A_strict_mono mask _ _ Hgt ltac:(rewrite pos_A_length; exact Hiu)). lia. }
        assert (HinEA : In (index_of u (pos_A mask), index_of v (pos_A mask)) EA).
        { unfold EA. apply graph_edges_in. rewrite (select_true_length mask Y Hmlen).
          assert (HinE : In (u, v) E) by (exact (sublists_incl E H HsubH _ He)).
          apply graph_edges_in in HinE. destruct HinE as [_ [_ [x [y [Hx [Hy Hob]]]]]].
          repeat split; [exact Hiuv | exact Hiv |].
          exists x, y.
          rewrite (select_true_nth_error p0 mask Y _ Hmlen Hiu), Hnu.
          rewrite (select_true_nth_error p0 mask Y _ Hmlen Hiv), Hnv.
          repeat split; assumption. }
        unfold embed_edges. apply in_map_iff.
        exists (index_of u (pos_A mask), index_of v (pos_A mask)).
        simpl; split; [rewrite Hnu, Hnv; reflexivity |].
        unfold HA, project_edges. apply filter_In. split; [exact HinEA |].
        apply edge_mem_iff. simpl; rewrite Hnu, Hnv; exact He.
      - right.
        assert (H0u : reachable H 0%nat u) by (apply (HposB_iff u ltac:(lia)); exact HuB).
        assert (HvB : In v (pos_B0 mask)).
        { apply (HposB_iff v ltac:(lia)).
          eapply reachable_trans; [exact H0u | eapply reach_step; [left; exact He | apply reach_refl]]. }
        destruct (index_of_spec u (pos_B0 mask) HuB) as [Hiu Hnu].
        destruct (index_of_spec v (pos_B0 mask) HvB) as [Hiv Hnv].
        rewrite pos_B0_length in Hiu, Hiv.
        assert (Hiuv : (index_of u (pos_B0 mask) < index_of v (pos_B0 mask))%nat).
        { destruct (lt_eq_lt_dec (index_of u (pos_B0 mask)) (index_of v (pos_B0 mask))) as [[Hlt | Heq] | Hgt];
            [exact Hlt | rewrite <- Hnu, <- Hnv, Heq in Huv; lia |].
          pose proof (pos_B0_strict_mono mask _ _ Hgt ltac:(rewrite pos_B0_length; exact Hiu)). lia. }
        assert (HinEB : In (index_of u (pos_B0 mask), index_of v (pos_B0 mask)) EB).
        { unfold EB. apply graph_edges_in. simpl length; rewrite (select_false_length mask Y Hmlen).
          assert (HinE : In (u, v) E) by (exact (sublists_incl E H HsubH _ He)).
          apply graph_edges_in in HinE. destruct HinE as [_ [_ [x [y [Hx [Hy Hob]]]]]].
          repeat split; [exact Hiuv | exact Hiv |].
          exists x, y.
          rewrite (select_false_nth_error p0 mask Y _ Hmlen Hiu), Hnu.
          rewrite (select_false_nth_error p0 mask Y _ Hmlen Hiv), Hnv.
          repeat split; assumption. }
        unfold embed_edges. apply in_map_iff.
        exists (index_of u (pos_B0 mask), index_of v (pos_B0 mask)).
        cbv beta; cbn [fst snd]; split; [rewrite Hnu, Hnv; reflexivity |].
        unfold HB, project_edges. apply filter_In. split; [exact HinEB |].
        apply edge_mem_iff. cbv beta; cbn [fst snd]; rewrite Hnu, Hnv; exact He. }
    (* HB is connected on {0, ..., k - count_true mask} *)
    assert (HconnHB : is_connectedb (S (k - count_true mask)) HB = true).
    { pose proof (sublists_Forall _ EB HB (proj2 HwfEB) HsubHB) as HwfHB.
      rewrite Hmlen in HwfHB.
      apply (is_connectedb_iff _ _ HwfHB). split; [lia |].
      assert (Hproj_walk : forall u w, reachable H u w ->
        (u < S k)%nat -> reachable H 0%nat u ->
        reachable HB (index_of u (pos_B0 mask)) (index_of w (pos_B0 mask))).
      { intros u w Hrw. induction Hrw; intros Hu H0u; [apply reach_refl |].
        pose proof (wf_has_edge_lt (S k) H u v HwfH H0) as [_ [Hv _]].
        assert (H0v : reachable H 0%nat v).
        { eapply reachable_trans; [exact H0u | eapply reach_step; [exact H0 | apply reach_refl]]. }
        eapply reach_step; [| exact (IHHrw Hv H0v)].
        assert (HuB : In u (pos_B0 mask)) by (apply (HposB_iff u Hu); exact H0u).
        assert (HvB : In v (pos_B0 mask)) by (apply (HposB_iff v Hv); exact H0v).
        destruct (index_of_spec u (pos_B0 mask) HuB) as [Hiu Hnu].
        destruct (index_of_spec v (pos_B0 mask) HvB) as [Hiv Hnv].
        rewrite pos_B0_length in Hiu, Hiv.
        destruct H0 as [He | He].
        - left. destruct (HH_split (u, v) He) as [HinA | HinB].
          + pose proof (sublists_Forall _ EA HA (proj2 HwfEA) HsubHA) as HforA.
            rewrite <- pos_A_length in HforA.
            destruct (embed_edges_in_pos _ _ _ _ HforA HinA) as [HuA _].
            exfalso; exact (pos_A_B0_disjoint mask u HuA HuB).
          + pose proof (sublists_Forall _ EB HB (proj2 HwfEB) HsubHB) as HforB.
            rewrite <- pos_B0_length in HforB.
            rewrite <- Hnu, <- Hnv in HinB.
            exact (embed_edges_in_inv (pos_B0 mask) HB _ _ (pos_B0_inj mask) HforB
                     ltac:(rewrite pos_B0_length; exact Hiu) ltac:(rewrite pos_B0_length; exact Hiv) HinB).
        - right. destruct (HH_split (v, u) He) as [HinA | HinB].
          + pose proof (sublists_Forall _ EA HA (proj2 HwfEA) HsubHA) as HforA.
            rewrite <- pos_A_length in HforA.
            destruct (embed_edges_in_pos _ _ _ _ HforA HinA) as [HvA _].
            exfalso; exact (pos_A_B0_disjoint mask v HvA HvB).
          + pose proof (sublists_Forall _ EB HB (proj2 HwfEB) HsubHB) as HforB.
            rewrite <- pos_B0_length in HforB.
            rewrite <- Hnu, <- Hnv in HinB.
            exact (embed_edges_in_inv (pos_B0 mask) HB _ _ (pos_B0_inj mask) HforB
                     ltac:(rewrite pos_B0_length; exact Hiv) ltac:(rewrite pos_B0_length; exact Hiu) HinB). }
      intros i Hi.
      assert (Hi_len : (i < length (pos_B0 mask))%nat) by (rewrite pos_B0_length, Hmlen; exact Hi).
      set (v := nth i (pos_B0 mask) 0%nat).
      assert (HvB : In v (pos_B0 mask)) by (unfold v; apply nth_In; exact Hi_len).
      assert (Hv_lt : (v < S k)%nat).
      { apply pos_B0_in in HvB. destruct HvB as [H0 | [_ [Hle _]]]; lia. }
      assert (H0v : reachable H 0%nat v) by (apply (HposB_iff v Hv_lt); exact HvB).
      assert (Hi0 : index_of 0%nat (pos_B0 mask) = 0%nat) by (unfold pos_B0; simpl; reflexivity).
      assert (Hiv : index_of v (pos_B0 mask) = i).
      { destruct (index_of_spec v (pos_B0 mask) HvB) as [Hlt Hnv].
        apply (pos_B0_inj mask); [exact Hlt | exact Hi_len | exact Hnv]. }
      rewrite <- Hi0, <- Hiv.
      apply (Hproj_walk 0%nat v H0v ltac:(lia) (reach_refl H 0%nat)). }
    unfold split_comp. fold k mask EA EB HA HB.
    split.
    - apply valid_comp_triples_in. repeat split; assumption.
    - apply (sublists_ext E _ H (proj1 HwfE) (filter_in_sublists _ E) HsubH).
      intro e. unfold join_comp. rewrite filter_In, edge_mem_iff, in_app_iff. split.
      + intros [_ [HinA | HinB]].
        * unfold embed_edges in HinA. apply in_map_iff in HinA. destruct HinA as [eA [<- HeA]].
          unfold HA, project_edges in HeA. apply filter_In in HeA.
          destruct HeA as [_ Hmem]. apply edge_mem_iff in Hmem. exact Hmem.
        * unfold embed_edges in HinB. apply in_map_iff in HinB. destruct HinB as [eB [<- HeB]].
          unfold HB, project_edges in HeB. apply filter_In in HeB.
          destruct HeB as [_ Hmem]. apply edge_mem_iff in Hmem. exact Hmem.
      + intro He. split; [exact (sublists_incl E H HsubH _ He) | exact (HH_split e He)].
  Qed.

  Lemma compat_ursell_pointwise : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P),
    (if pairwise_compat ob (p0 :: Y) then 1 else 0) =
    fold_right Rplus 0 (map (fun mask =>
      ursell_fn ob (p0 :: select_false mask Y) *
      (if pairwise_compat ob (select_true mask Y) then 1 else 0))
      (all_masks (length Y))).
  Proof.
    intros P ob p0 Y.
    rewrite <- (sum_all_subgraphs_eq_compat ob (p0 :: Y)).
    set (E := graph_edges ob (p0 :: Y)).
    set (triples := valid_comp_triples ob p0 Y).
    set (mapped := map (fun t => let '(mask, HA, HB) := t in join_comp E mask HA HB) triples).
    assert (Hperm : Permutation (sublists E) mapped).
    { apply NoDup_Permutation.
      - apply sublists_NoDup_list, (proj1 (graph_edges_wf ob (p0 :: Y))).
      - unfold mapped. apply NoDup_map_in; [apply valid_comp_triples_NoDup |].
        intros [[m1 a1] b1] [[m2 a2] b2] H1 H2 Heq.
        destruct (join_comp_spec ob p0 Y m1 a1 b1 H1) as [_ [_ Hs1]].
        destruct (join_comp_spec ob p0 Y m2 a2 b2 H2) as [_ [_ Hs2]].
        fold E in Hs1, Hs2. rewrite Heq in Hs1. congruence.
      - intro H. split.
        + intro HinH. unfold mapped. apply in_map_iff.
          exists (split_comp ob p0 Y H).
          pose proof (split_comp_spec ob p0 Y H HinH) as Hsc.
          destruct (split_comp ob p0 Y H) as [[mask HA] HB] eqn:Esc.
          fold E in Hsc. destruct Hsc as [Htrip Hjoin]. split; assumption.
        + intro HinM. unfold mapped in HinM. apply in_map_iff in HinM.
          destruct HinM as [[[mask HA] HB] [<- Htrip]].
          exact (proj1 (join_comp_spec ob p0 Y mask HA HB Htrip)). }
    rewrite (Permutation_fold_right_Rplus _ _ (Permutation_map (fun H => (-1) ^ length H) Hperm)).
    unfold mapped. rewrite map_map.
    transitivity (fold_right Rplus 0 (map (fun t =>
      let '(mask, HA, HB) := t in (-1) ^ length HB * (-1) ^ length HA) triples)).
    - apply fold_right_Rplus_ext. intros [[mask HA] HB] Htrip.
      destruct (join_comp_spec ob p0 Y mask HA HB Htrip) as [_ [Hlen _]].
      fold E in Hlen. rewrite Hlen, pow_add. ring.
    - unfold triples, valid_comp_triples.
      rewrite fold_right_Rplus_flat_map.
      apply fold_right_Rplus_ext. intros mask Hmask.
      rewrite fold_right_Rplus_flat_map.
      transitivity (fold_right Rplus 0 (map (fun HB =>
        (-1) ^ length HB *
        fold_right Rplus 0 (map (fun HA => (-1) ^ length HA) (sublists (graph_edges ob (select_true mask Y)))))
        (filter (is_connectedb (length (p0 :: select_false mask Y)))
                (sublists (graph_edges ob (p0 :: select_false mask Y)))))).
      + apply fold_right_Rplus_ext. intros HB _.
        rewrite map_map, <- fold_right_Rplus_scale. reflexivity.
      + rewrite sum_all_subgraphs_eq_compat, fold_right_Rplus_scale_r.
        f_equal. unfold ursell_fn, ursell_graph.
        rewrite <- fold_right_Rplus_filter. reflexivity.
  Qed.

  Lemma sum_f_R0_rev : forall f k,
    sum_f_R0 (fun r => f (k - r)%nat) k = sum_f_R0 f k.
  Proof.
    intros f k.
    assert (Hgen : forall n g, sum_f_R0 (fun r => g (n - r)%nat) n = sum_f_R0 g n).
    { induction n as [| n' IH]; intro g; [simpl; reflexivity |].
      change (sum_f_R0 (fun r => g (S n' - r)%nat) (S n'))
        with (sum_f_R0 (fun r => g (S n' - r)%nat) n' + g (S n' - S n')%nat).
      rewrite Nat.sub_diag.
      rewrite (sum_f_R0_shift g n').
      replace (sum_f_R0 (fun r => g (S n' - r)%nat) n')
         with (sum_f_R0 (fun r => g (S (n' - r))) n')
        by (apply sum_f_R0_ext; intros r Hr; f_equal; lia).
      rewrite (IH (fun i => g (S i))). ring. }
    exact (Hgen k f).
  Qed.

  Theorem compat_ursell_recurrence : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w : P -> R) k,
    (1 <= k)%nat ->
    INR k * compat_tuple_sum ob Lambda w k =
    sum_f_R0 (fun j =>
      INR (S j) * ursell_order ob Lambda w (S j) * compat_tuple_sum ob Lambda w (k - S j)%nat)
      (k - 1)%nat.
  Proof.
    intros P ob Lambda w k Hk.
    destruct k as [| k']; [lia |].
    replace (S k' - 1)%nat with k' by lia.
    unfold compat_tuple_sum at 1.
    assert (HfactS : INR (fact (S k')) = INR (S k') * INR (fact k')).
    { change (fact (S k')) with (S k' * fact k')%nat. rewrite mult_INR. reflexivity. }
    assert (Hne1 : INR (S k') <> 0) by (apply not_0_INR; lia).
    assert (Hne2 : INR (fact k') <> 0) by (apply not_0_INR, fact_neq_0).
    replace (INR (S k') * (/ INR (fact (S k')) *
             sum_over_tuples Lambda (S k') (fun X => if pairwise_compat ob X then prod_weight w X else 0)))
       with (/ INR (fact k') *
             sum_over_tuples Lambda (S k') (fun X => if pairwise_compat ob X then prod_weight w X else 0))
      by (rewrite HfactS; field; split; assumption).
    rewrite sum_over_tuples_S.
    (* Expand pointwise via compat_ursell_pointwise *)
    assert (Hexp :
      fold_right Rplus 0 (map (fun p0 =>
        sum_over_tuples Lambda k' (fun Y =>
          if pairwise_compat ob (p0 :: Y) then prod_weight w (p0 :: Y) else 0)) Lambda) =
      fold_right Rplus 0 (map (fun mask =>
        sum_over_tuples Lambda (count_true mask)
          (fun YA => if pairwise_compat ob YA then prod_weight w YA else 0) *
        sum_over_tuples Lambda (S (k' - count_true mask))
          (fun Z => ursell_fn ob Z * prod_weight w Z))
        (all_masks k'))).
    { transitivity (fold_right Rplus 0 (map (fun p0 =>
        fold_right Rplus 0 (map (fun mask =>
          sum_over_tuples Lambda k' (fun Y =>
            ((if pairwise_compat ob (select_true mask Y) then prod_weight w (select_true mask Y) else 0) *
             (ursell_fn ob (p0 :: select_false mask Y) * prod_weight w (p0 :: select_false mask Y)))))
          (all_masks k'))) Lambda)).
      - apply fold_right_Rplus_ext. intros p0 _.
        unfold sum_over_tuples at 1.
        transitivity (fold_right Rplus 0 (map (fun Y =>
          fold_right Rplus 0 (map (fun mask =>
            (if pairwise_compat ob (select_true mask Y) then prod_weight w (select_true mask Y) else 0) *
            (ursell_fn ob (p0 :: select_false mask Y) * prod_weight w (p0 :: select_false mask Y)))
            (all_masks k'))) (tuples_of_length Lambda k'))).
        + apply fold_right_Rplus_ext. intros Y HY.
          pose proof (tuples_of_length_len Lambda k' Y HY) as HlenY.
          replace (if pairwise_compat ob (p0 :: Y) then prod_weight w (p0 :: Y) else 0)
             with ((if pairwise_compat ob (p0 :: Y) then 1 else 0) * prod_weight w (p0 :: Y))
            by (destruct (pairwise_compat ob (p0 :: Y)); ring).
          rewrite (compat_ursell_pointwise ob p0 Y), HlenY, <- fold_right_Rplus_scale_r.
          apply fold_right_Rplus_ext. intros mask Hm. apply all_masks_in in Hm.
          assert (Hpw_cons : forall q l, prod_weight w (q :: l) = w q * prod_weight w l)
            by (intros q l; unfold prod_weight, prod_list; simpl; reflexivity).
          rewrite !Hpw_cons, (prod_weight_mask_split w mask Y ltac:(lia)).
          destruct (pairwise_compat ob (select_true mask Y)); ring.
        + rewrite fold_right_Rplus_swap. reflexivity.
      - rewrite fold_right_Rplus_swap.
        apply fold_right_Rplus_ext. intros mask Hm. apply all_masks_in in Hm.
        transitivity (fold_right Rplus 0 (map (fun p0 =>
          sum_over_tuples Lambda (count_true mask)
            (fun YA => if pairwise_compat ob YA then prod_weight w YA else 0) *
          sum_over_tuples Lambda (k' - count_true mask)
            (fun YB => ursell_fn ob (p0 :: YB) * prod_weight w (p0 :: YB))) Lambda)).
        + apply fold_right_Rplus_ext. intros p0 _.
          rewrite <- Hm at 1.
          rewrite (sum_over_tuples_mask_split Lambda mask
            (fun YA => if pairwise_compat ob YA then prod_weight w YA else 0)
            (fun YB => ursell_fn ob (p0 :: YB) * prod_weight w (p0 :: YB))).
          rewrite Hm. reflexivity.
        + rewrite fold_right_Rplus_scale.
          rewrite <- (sum_over_tuples_S Lambda (k' - count_true mask) (fun Z => ursell_fn ob Z * prod_weight w Z)).
          reflexivity. }
    rewrite Hexp.
    set (G := fun r =>
      sum_over_tuples Lambda r
        (fun YA => if pairwise_compat ob YA then prod_weight w YA else 0) *
      sum_over_tuples Lambda (S (k' - r))
        (fun Z => ursell_fn ob Z * prod_weight w Z)).
    change (fold_right Rplus 0 (map (fun mask =>
      sum_over_tuples Lambda (count_true mask)
        (fun YA => if pairwise_compat ob YA then prod_weight w YA else 0) *
      sum_over_tuples Lambda (S (k' - count_true mask))
        (fun Z => ursell_fn ob Z * prod_weight w Z)) (all_masks k')))
      with (fold_right Rplus 0 (map (fun mask => G (count_true mask)) (all_masks k'))).
    rewrite (sum_over_all_masks_by_count k' G).
    rewrite <- sum_f_R0_scale.
    rewrite <- (sum_f_R0_rev (fun j =>
      INR (S j) * ursell_order ob Lambda w (S j) * compat_tuple_sum ob Lambda w (S k' - S j)%nat) k').
    apply sum_f_R0_ext. intros r Hr.
    unfold G, ursell_order, compat_tuple_sum.
    replace (S k' - S (k' - r))%nat with r by lia.
    pose proof (binomial_fact k' r Hr) as Hbf.
    assert (HfS : INR (fact (S (k' - r))) = INR (S (k' - r)) * INR (fact (k' - r))).
    { change (fact (S (k' - r))) with (S (k' - r) * fact (k' - r))%nat. rewrite mult_INR. reflexivity. }
    assert (Hn_r : INR (fact r) <> 0) by (apply not_0_INR, fact_neq_0).
    assert (Hn_kr : INR (fact (k' - r)) <> 0) by (apply not_0_INR, fact_neq_0).
    assert (Hn_Skr : INR (S (k' - r)) <> 0) by (apply not_0_INR; lia).
    rewrite HfS.
    replace (/ INR (fact k') *
             (INR (binomial k' r) *
              (sum_over_tuples Lambda r (fun YA => if pairwise_compat ob YA then prod_weight w YA else 0) *
               sum_over_tuples Lambda (S (k' - r)) (fun Z => ursell_fn ob Z * prod_weight w Z))))
       with ((INR (binomial k' r) * INR (fact r) * INR (fact (k' - r))) * / INR (fact k') *
             (INR (S (k' - r)) *
              (/ (INR (S (k' - r)) * INR (fact (k' - r))) *
               sum_over_tuples Lambda (S (k' - r)) (fun Z => ursell_fn ob Z * prod_weight w Z)) *
              (/ INR (fact r) *
               sum_over_tuples Lambda r (fun YA => if pairwise_compat ob YA then prod_weight w YA else 0))))
      by (field; repeat split; assumption).
    rewrite Hbf. field. repeat split; assumption.
  Qed.

  (* =======================================================================
     4. Absolute Convergence Bound & Target 6a (ln Z_Lambda Limit Theorem)
     ======================================================================= *)

  Lemma existsb_sum_ge_1 : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P) (X : list P) (p : P),
    (forall q, ob q q = true) ->
    In p Lambda ->
    In p X ->
    1 <= fold_right Rplus 0 (map (fun q => if existsb (ob q) X then 1 else 0) Lambda).
  Proof.
    intros P ob Lambda X p Hrefl HinL HinX.
    induction Lambda as [| a xs IH]; [simpl in HinL; contradiction |].
    simpl.
    assert (Hnn : forall l, 0 <= fold_right Rplus 0 (map (fun q => if existsb (ob q) X then 1 else 0) l)).
    { intro l. apply fold_right_Rplus_nonneg. intros q _. destruct (existsb (ob q) X); lra. }
    destruct HinL as [-> | Hin'].
    - assert (Hex : existsb (ob p) X = true).
      { apply existsb_exists. exists p. split; [exact HinX | apply Hrefl]. }
      rewrite Hex. pose proof (Hnn xs). lra.
    - pose proof (IH Hin'). destruct (existsb (ob a) X); lra.
  Qed.

  Lemma kp_abs_convergence : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w a : P -> R),
    (forall p, ob p p = true) ->
    (forall x y, ob x y = ob y x) ->
    (forall p, In p Lambda -> 0 <= a p) ->
    (forall p, In p Lambda -> kp_at ob Lambda w a (fun _ => 0) p) ->
    forall N,
      sum_f_R0 (fun n => Rabs (ursell_order ob Lambda w n)) N <=
      fold_right Rplus 0 (map a Lambda).
  Proof.
    intros P ob Lambda w a Hrefl Hsym Ha_nn Hkp N.
    assert (Hterm : forall n,
      Rabs (ursell_order ob Lambda w n) <=
      fold_right Rplus 0 (map (fun p =>
        match n with
        | 0%nat => 0
        | S _ =>
            (/ INR (fact n)) *
            sum_over_tuples Lambda n (fun X =>
              if existsb (ob p) X
              then Rabs (ursell_fn ob X) * prod_weight (fun q => Rabs (w q) * exp 0) X
              else 0)
        end) Lambda)).
    { intros [| n'].
      - unfold ursell_order. rewrite Rabs_R0, fold_right_Rplus_0. lra.
      - unfold ursell_order.
        rewrite Rabs_mult.
        assert (Hinv : 0 < / INR (fact (S n'))) by (apply Rinv_0_lt_compat, fact_pos_R).
        rewrite (Rabs_right (/ INR (fact (S n'))) ltac:(lra)).
        rewrite fold_right_Rplus_scale.
        apply Rmult_le_compat_l; [lra |].
        unfold sum_over_tuples.
        rewrite fold_right_Rplus_swap.
        apply Rabs_fold_right_Rplus_le. intros X HX.
        rewrite Rabs_mult, Rabs_prod_weight.
        assert (Hexp0 : prod_weight (fun q => Rabs (w q) * exp 0) X = prod_weight (fun q => Rabs (w q)) X).
        { unfold prod_weight, prod_list. f_equal. apply map_ext. intro q. rewrite exp_0. ring. }
        rewrite Hexp0.
        pose proof (tuples_of_length_len Lambda (S n') X HX) as HlenX.
        pose proof (tuples_of_length_in Lambda (S n') X HX) as HinX.
        destruct X as [| x xs]; [simpl in HlenX; discriminate |].
        inversion HinX as [| ? ? HxL _]; subst.
        set (V := Rabs (ursell_fn ob (x :: xs)) * prod_weight (fun q => Rabs (w q)) (x :: xs)).
        assert (HV : 0 <= V)
          by (unfold V; apply Rmult_le_pos; [apply Rabs_pos | apply prod_weight_nonneg; intro q; apply Rabs_pos]).
        apply Rle_trans with (r2 := V * fold_right Rplus 0 (map (fun p => if existsb (ob p) (x :: xs) then 1 else 0) Lambda)).
        + fold V. rewrite <- (Rmult_1_r V) at 1. apply Rmult_le_compat_l; [exact HV |].
          apply (existsb_sum_ge_1 ob Lambda (x :: xs) x Hrefl HxL (or_introl eq_refl)).
        + rewrite <- fold_right_Rplus_scale.
          apply fold_right_Rplus_le. intros p _. unfold V. destruct (existsb (ob p) (x :: xs)); lra. }
    eapply Rle_trans; [apply sum_f_R0_le; intros n _; exact (Hterm n) |].
    assert (Hswap : forall M,
      sum_f_R0 (fun n => fold_right Rplus 0 (map (fun p =>
        match n with
        | 0%nat => 0
        | S _ =>
            (/ INR (fact n)) *
            sum_over_tuples Lambda n (fun X =>
              if existsb (ob p) X
              then Rabs (ursell_fn ob X) * prod_weight (fun q => Rabs (w q) * exp 0) X
              else 0)
        end) Lambda)) M =
      fold_right Rplus 0 (map (fun p =>
        kp_series Lambda M (fun X =>
          if existsb (ob p) X
          then Rabs (ursell_fn ob X) * prod_weight (fun q => Rabs (w q) * exp 0) X
          else 0)) Lambda)).
    { induction M as [| M' IHM].
      - simpl. reflexivity.
      - change (sum_f_R0 _ (S M')) with (sum_f_R0 (fun n => fold_right Rplus 0 (map (fun p =>
          match n with
          | 0%nat => 0
          | S _ =>
              (/ INR (fact n)) *
              sum_over_tuples Lambda n (fun X =>
                if existsb (ob p) X
                then Rabs (ursell_fn ob X) * prod_weight (fun q => Rabs (w q) * exp 0) X
                else 0)
          end) Lambda)) M' + fold_right Rplus 0 (map (fun p =>
            (/ INR (fact (S M'))) *
            sum_over_tuples Lambda (S M') (fun X =>
              if existsb (ob p) X
              then Rabs (ursell_fn ob X) * prod_weight (fun q => Rabs (w q) * exp 0) X
              else 0)) Lambda)).
        rewrite IHM, <- fold_right_Rplus_plus.
        apply fold_right_Rplus_ext. intros p _. cbn [kp_series]. reflexivity. }
    rewrite Hswap.
    apply fold_right_Rplus_le. intros p Hp.
    exact (kp_overlap_pinned_bound ob Lambda w a (fun _ => 0) p Hsym (Ha_nn p Hp) Ha_nn (Hkp p Hp) Hkp N).
  Qed.

  (* TARGET 6a: Partition Function Positivity, Absolute Convergence, and ln Z_Lambda Limit *)
  Theorem kp_log_partition_fn : forall {P : Type} (ob : P -> P -> bool) (Lambda : list P) (w a : P -> R),
    (forall p, ob p p = true) ->
    (forall x y, ob x y = ob y x) ->
    (forall p, In p Lambda -> 0 <= a p) ->
    (forall p, In p Lambda -> kp_at ob Lambda w a (fun _ => 0) p) ->
    0 < partition_fn ob Lambda w /\
    (forall N, sum_f_R0 (fun n => Rabs (ursell_order ob Lambda w n)) N <= fold_right Rplus 0 (map a Lambda)) /\
    Un_cv (fun N => kp_series Lambda N (fun X => ursell_fn ob X * prod_weight w X))
          (ln (partition_fn ob Lambda w)).
  Proof.
    intros P ob Lambda w a Hrefl Hsym Ha_nn Hkp.
    pose proof (kp_abs_convergence ob Lambda w a Hrefl Hsym Ha_nn Hkp) as Habs.
    pose proof (exp_of_abs_conv_recurrence
      (ursell_order ob Lambda w)
      (compat_tuple_sum ob Lambda w)
      (length Lambda)
      (fold_right Rplus 0 (map a Lambda))
      eq_refl
      (compat_tuple_sum_0 ob Lambda w)
      (fun k Hk => compat_ursell_recurrence ob Lambda w k Hk)
      (fun k Hk => compat_tuple_sum_zero_gt ob w Lambda Hrefl Hsym k Hk)
      Habs) as [Hpos Hcv].
    rewrite (compat_tuple_sum_eq_partition_fn ob w Lambda Hrefl Hsym) in Hpos, Hcv.
    repeat split; [exact Hpos | exact Habs |].
    intros eps Heps. destruct (Hcv eps Heps) as [N0 HN0].
    exists N0. intros N HN. rewrite <- sum_f_R0_ursell_order. exact (HN0 N HN).
  Qed.

  (* =======================================================================
     5. Inclusion-Exclusion on Four Sub-Volumes & Target 6b (Log-Ratio Decay)
     ======================================================================= *)

  Lemma kp_at_filter : forall {P : Type} (ob : P -> P -> bool) (Pb : P -> bool)
    (Lambda : list P) (w a d : P -> R) (p : P),
    kp_at ob Lambda w a d p ->
    kp_at ob (filter Pb Lambda) w a d p.
  Proof.
    intros P ob Pb Lambda w a d p Hkp.
    unfold kp_at, sum_overlap_Lambda in *.
    eapply Rle_trans; [| exact Hkp].
    rewrite <- fold_right_Rplus_filter.
    apply fold_right_Rplus_le. intros q _.
    destruct (Pb q); [lra |].
    destruct (ob p q); [| lra].
    apply Rmult_le_pos; [apply Rabs_pos | left; apply exp_pos].
  Qed.

  Lemma kp_at_drop_d : forall {P : Type} (ob : P -> P -> bool)
    (Lambda : list P) (w a d : P -> R) (p : P),
    (forall q, 0 <= d q) ->
    kp_at ob Lambda w a d p ->
    kp_at ob Lambda w a (fun _ => 0) p.
  Proof.
    intros P ob Lambda w a d p Hd Hkp.
    unfold kp_at, sum_overlap_Lambda in *.
    eapply Rle_trans; [| exact Hkp].
    apply fold_right_Rplus_le. intros q _.
    destruct (ob p q); [| lra].
    apply Rmult_le_compat_l; [apply Rabs_pos |].
    pose proof (Hd q) as Hdq.
    destruct (Rle_lt_or_eq_dec 0 (d q) Hdq) as [Hlt | Heq].
    - left. apply exp_increasing. lra.
    - rewrite <- Heq. lra.
  Qed.

  Lemma forallb_negb_eq_negb_existsb : forall {A : Type} (f : A -> bool) (l : list A),
    forallb (fun x => negb (f x)) l = negb (existsb f l).
  Proof.
    intros A f. induction l as [| a xs IH]; [simpl; reflexivity |].
    simpl. rewrite IH. destruct (f a), (existsb f xs); reflexivity.
  Qed.

  Lemma forallb_andb : forall {A : Type} (f g : A -> bool) (l : list A),
    forallb (fun x => f x && g x) l = forallb f l && forallb g l.
  Proof.
    intros A f g. induction l as [| a xs IH]; [simpl; reflexivity |].
    simpl. rewrite IH. destruct (f a), (g a), (forallb f xs), (forallb g xs); reflexivity.
  Qed.

  Lemma kp_correlator_inclusion_exclusion : forall {P : Type} (ob : P -> P -> bool)
    (Lambda : list P) (w : P -> R) (p1 p2 : P) (N : nat),
    let L1 := filter (fun q => negb (ob p1 q)) Lambda in
    let L2 := filter (fun q => negb (ob p2 q)) Lambda in
    let L12 := filter (fun q => negb (ob p1 q) && negb (ob p2 q)) Lambda in
    let F := fun X => ursell_fn ob X * prod_weight w X in
    ursell_correlator ob Lambda N w p1 p2 =
    kp_series Lambda N F - kp_series L1 N F - kp_series L2 N F + kp_series L12 N F.
  Proof.
    intros P ob Lambda w p1 p2 N L1 L2 L12 F.
    unfold ursell_correlator. induction N as [| N' IH].
    - simpl. ring.
    - cbn [kp_series]. rewrite IH.
      assert (Hstep :
        sum_over_tuples Lambda (S N') (fun X => if existsb (ob p1) X && existsb (ob p2) X then F X else 0) =
        sum_over_tuples Lambda (S N') F -
        sum_over_tuples L1 (S N') F -
        sum_over_tuples L2 (S N') F +
        sum_over_tuples L12 (S N') F).
      { unfold L1, L2, L12.
        rewrite <- !sum_over_tuples_filter.
        transitivity (sum_over_tuples Lambda (S N') (fun X =>
          (F X + - (if forallb (fun q => negb (ob p1 q)) X then F X else 0)) +
          (- (if forallb (fun q => negb (ob p2 q)) X then F X else 0) +
           (if forallb (fun q => negb (ob p1 q) && negb (ob p2 q)) X then F X else 0)))).
        - apply sum_over_tuples_ext. intros X _.
          rewrite forallb_andb, !forallb_negb_eq_negb_existsb.
          destruct (existsb (ob p1) X), (existsb (ob p2) X); simpl; ring.
        - rewrite !sum_over_tuples_plus.
          assert (Hopp : forall g, sum_over_tuples Lambda (S N') (fun X => - g X) = - sum_over_tuples Lambda (S N') g).
          { intro g. replace (- sum_over_tuples Lambda (S N') g) with ((-1) * sum_over_tuples Lambda (S N') g) by ring.
            rewrite <- sum_over_tuples_scale. apply sum_over_tuples_ext; intros X _; ring. }
          rewrite !Hopp. ring. }
      unfold F in Hstep. rewrite Hstep. unfold F. ring.
  Qed.

  Lemma Un_cv_comb4 : forall u1 u2 u3 u4 l1 l2 l3 l4,
    Un_cv u1 l1 -> Un_cv u2 l2 -> Un_cv u3 l3 -> Un_cv u4 l4 ->
    Un_cv (fun N => u1 N - u2 N - u3 N + u4 N) (l1 - l2 - l3 + l4).
  Proof.
    intros u1 u2 u3 u4 l1 l2 l3 l4 H1 H2 H3 H4 eps Heps.
    destruct (H1 (eps / 4) ltac:(lra)) as [N1 HN1].
    destruct (H2 (eps / 4) ltac:(lra)) as [N2 HN2].
    destruct (H3 (eps / 4) ltac:(lra)) as [N3 HN3].
    destruct (H4 (eps / 4) ltac:(lra)) as [N4 HN4].
    exists (Nat.max (Nat.max N1 N2) (Nat.max N3 N4)).
    intros N HN.
    specialize (HN1 N ltac:(lia)). specialize (HN2 N ltac:(lia)).
    specialize (HN3 N ltac:(lia)). specialize (HN4 N ltac:(lia)).
    unfold R_dist in *.
    replace (u1 N - u2 N - u3 N + u4 N - (l1 - l2 - l3 + l4))
       with ((u1 N - l1) + (- (u2 N - l2) + (- (u3 N - l3) + (u4 N - l4)))) by ring.
    eapply Rle_lt_trans; [apply Rabs_triang |].
    assert (H234 : Rabs (- (u2 N - l2) + (- (u3 N - l3) + (u4 N - l4))) <=
                   Rabs (u2 N - l2) + Rabs (u3 N - l3) + Rabs (u4 N - l4)).
    { eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp, Rplus_assoc.
      apply Rplus_le_compat_l.
      eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
    lra.
  Qed.

  Lemma Un_cv_Rabs_le : forall u L B,
    Un_cv u L ->
    (forall N, Rabs (u N) <= B) ->
    Rabs L <= B.
  Proof.
    intros u L B Hcv Hub.
    destruct (Rle_lt_dec (Rabs L) B) as [Hle | Hgt]; [exact Hle | exfalso].
    set (eps := (Rabs L - B) / 2).
    destruct (Hcv eps ltac:(unfold eps; lra)) as [N HN].
    specialize (HN N (le_n N)). unfold R_dist in HN.
    pose proof (Hub N) as HBN.
    assert (Htri : Rabs L <= Rabs (u N) + Rabs (u N - L)).
    { replace (Rabs L) with (Rabs (u N + - (u N - L))) by (f_equal; ring).
      eapply Rle_trans; [apply Rabs_triang | rewrite Rabs_Ropp; lra]. }
    unfold eps in HN. lra.
  Qed.

  (* TARGET 6b: Unconditional Partition-Function Log-Ratio Convergence & Exponential Decay *)
  Theorem kp_log_ratio_decay : forall {P : Type} (ob : P -> P -> bool)
    (Lambda : list P) (w a size : P -> R) (dist : P -> P -> R) (c : R) (p1 p2 : P),
    (forall p, ob p p = true) ->
    (forall x y, ob x y = ob y x) ->
    (forall p, dist p p = 0) ->
    (forall p q r, dist p r <= dist p q + dist q r) ->
    (forall p q, ob p q = true -> dist p q <= 1) ->
    (forall p, 1 <= size p) ->
    0 < c ->
    0 <= a p1 ->
    (forall p, In p Lambda -> 0 <= a p) ->
    kp_at ob Lambda w a (fun q => c * size q) p1 ->
    (forall p, In p Lambda -> kp_at ob Lambda w a (fun q => c * size q) p) ->
    let Z := partition_fn ob Lambda w in
    let Z1 := partition_fn ob (filter (fun q => negb (ob p1 q)) Lambda) w in
    let Z2 := partition_fn ob (filter (fun q => negb (ob p2 q)) Lambda) w in
    let Z12 := partition_fn ob (filter (fun q => negb (ob p1 q) && negb (ob p2 q)) Lambda) w in
    0 < Z /\ 0 < Z1 /\ 0 < Z2 /\ 0 < Z12 /\
    Un_cv (fun N => ursell_correlator ob Lambda N w p1 p2) (ln ((Z * Z12) / (Z1 * Z2))) /\
    Rabs (ln ((Z * Z12) / (Z1 * Z2))) <= a p1 * exp c * exp (- c * dist p1 p2).
  Proof.
    intros P ob Lambda w a size dist c p1 p2 Hrefl Hsym Hdist_refl Htri Hob_dist Hsize
           Hc Ha1 Ha_nn Hkp1 Hkp Z Z1 Z2 Z12.
    assert (Hd_nn : forall q, 0 <= c * size q).
    { intro q. pose proof (Hsize q). nra. }
    assert (Hkp0 : forall p, In p Lambda -> kp_at ob Lambda w a (fun _ => 0) p).
    { intros p Hp. exact (kp_at_drop_d ob Lambda w a (fun q => c * size q) p Hd_nn (Hkp p Hp)). }
    set (L1 := filter (fun q => negb (ob p1 q)) Lambda).
    set (L2 := filter (fun q => negb (ob p2 q)) Lambda).
    set (L12 := filter (fun q => negb (ob p1 q) && negb (ob p2 q)) Lambda).
    destruct (kp_log_partition_fn ob Lambda w a Hrefl Hsym Ha_nn Hkp0) as [HZ [_ HcvZ]].
    destruct (kp_log_partition_fn ob L1 w a Hrefl Hsym
      (fun p Hp => Ha_nn p (proj1 (proj1 (filter_In _ p Lambda) Hp)))
      (fun p Hp => kp_at_filter ob _ Lambda w a (fun _ => 0) p (Hkp0 p (proj1 (proj1 (filter_In _ p Lambda) Hp)))))
      as [HZ1 [_ HcvZ1]].
    destruct (kp_log_partition_fn ob L2 w a Hrefl Hsym
      (fun p Hp => Ha_nn p (proj1 (proj1 (filter_In _ p Lambda) Hp)))
      (fun p Hp => kp_at_filter ob _ Lambda w a (fun _ => 0) p (Hkp0 p (proj1 (proj1 (filter_In _ p Lambda) Hp)))))
      as [HZ2 [_ HcvZ2]].
    destruct (kp_log_partition_fn ob L12 w a Hrefl Hsym
      (fun p Hp => Ha_nn p (proj1 (proj1 (filter_In _ p Lambda) Hp)))
      (fun p Hp => kp_at_filter ob _ Lambda w a (fun _ => 0) p (Hkp0 p (proj1 (proj1 (filter_In _ p Lambda) Hp)))))
      as [HZ12 [_ HcvZ12]].
    unfold L1 in HZ1, HcvZ1. unfold L2 in HZ2, HcvZ2. unfold L12 in HZ12, HcvZ12.
    fold Z in HZ, HcvZ. fold Z1 in HZ1, HcvZ1. fold Z2 in HZ2, HcvZ2. fold Z12 in HZ12, HcvZ12.
    assert (Hln_eq : ln Z - ln Z1 - ln Z2 + ln Z12 = ln ((Z * Z12) / (Z1 * Z2))).
    { unfold Rdiv.
      rewrite (ln_mult (Z * Z12) (/ (Z1 * Z2)) ltac:(nra) ltac:(apply Rinv_0_lt_compat; nra)).
      rewrite (ln_mult Z Z12 HZ HZ12).
      rewrite (ln_Rinv (Z1 * Z2) ltac:(nra)).
      rewrite (ln_mult Z1 Z2 HZ1 HZ2).
      ring. }
    assert (Hcv_corr : Un_cv (fun N => ursell_correlator ob Lambda N w p1 p2) (ln ((Z * Z12) / (Z1 * Z2)))).
    { rewrite <- Hln_eq.
      pose proof (Un_cv_comb4 _ _ _ _ _ _ _ _ HcvZ HcvZ1 HcvZ2 HcvZ12) as Hcomb.
      intros eps Heps. destruct (Hcomb eps Heps) as [N0 HN0].
      exists N0. intros N HN.
      rewrite (kp_correlator_inclusion_exclusion ob Lambda w p1 p2 N).
      exact (HN0 N HN). }
    assert (Hdecay : Rabs (ln ((Z * Z12) / (Z1 * Z2))) <= a p1 * exp c * exp (- c * dist p1 p2)).
    { apply (Un_cv_Rabs_le _ _ _ Hcv_corr).
      intro N.
      exact (kp_correlator_exponential_decay ob Lambda w a size dist c p1 p2
               Hsym Hdist_refl Htri Hob_dist Hsize Hc Ha1 Ha_nn Hkp1 Hkp N). }
    repeat split; assumption.
  Qed.

End ClusterLogPartition.
