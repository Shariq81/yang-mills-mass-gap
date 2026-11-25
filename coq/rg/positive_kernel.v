(* =========================================================================
   rg/positive_kernel.v

   Positive kernels on the configurations of a finite product a-priori
   measure (rg/dup_clustering.v).

   A kernel K (U, U') is of "finite rank-one type" (`rk`) if it is a finite
   sum of products k (U) * k (U').  Such kernels are closed under sums,
   products and non-negative multiples, and for them the double sum

       sum_U sum_U'  Y (U) Y (U') K (U, U')  =  sum_k ( sum_U Y (U) k (U) )^2

   is non-negative (`double_rk_nonneg`).  Since every partial sum of the
   exponential series of beta * S, beta >= 0, is again of this type when S
   is, the same holds for the kernel exp (beta * S (U, U'))
   (`double_exp_nonneg`): the exponential of a positive kernel is positive.

   Depends ONLY on Coq stdlib + rg.dup_clustering + rg.product_measure.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra Permutation.
From rg Require Import dup_clustering product_measure.
Import ListNotations.
Import DupClustering.
Open Scope R_scope.

Module PositiveKernel.

  (* =======================================================================
     1. Limits of finite sums
     ======================================================================= *)

  Lemma cv_ext1 : forall (u u' : nat -> R) (l : R),
    (forall n, u n = u' n) -> Un_cv u l -> Un_cv u' l.
  Proof.
    intros u u' l H Hu eps He. destruct (Hu eps He) as [N HN].
    exists N. intros n Hn. rewrite <- H. apply HN. exact Hn.
  Qed.

  Lemma cv_const1 : forall c : R, Un_cv (fun _ => c) c.
  Proof.
    intros c eps He. exists 0%nat. intros n _. unfold R_dist.
    replace (c - c) with 0 by ring. rewrite Rabs_R0. exact He.
  Qed.

  Lemma cv_nonneg1 : forall (u : nat -> R) (l : R),
    Un_cv u l -> (forall n, 0 <= u n) -> 0 <= l.
  Proof.
    intros u l Hu H. apply Rnot_lt_le. intro Hlt.
    destruct (Hu (- l) ltac:(lra)) as [N HN].
    specialize (HN N (le_n N)). unfold R_dist in HN.
    apply Rabs_def2 in HN. specialize (H N). lra.
  Qed.

  Lemma rsum_cv : forall {A : Type} (l : list A) (f : nat -> A -> R) (g : A -> R),
    (forall a, In a l -> Un_cv (fun n => f n a) (g a)) ->
    Un_cv (fun n => rsum l (f n)) (rsum l g).
  Proof.
    intros A l f g. induction l as [| a l IH]; intro H.
    - apply (cv_ext1 (fun _ => 0)); [intro n; reflexivity | apply cv_const1].
    - apply (cv_ext1 (fun n => f n a + rsum l (f n))).
      + intro n. symmetry. apply rsum_cons.
      + rewrite rsum_cons. apply CV_plus.
        * apply H. left. reflexivity.
        * apply IH. intros b Hb. apply H. right. exact Hb.
  Qed.

  Lemma exp_cv : forall x : R,
    Un_cv (fun N => sum_f_R0 (fun i => / INR (fact i) * x ^ i) N) (exp x).
  Proof.
    intro x. unfold exp. destruct (exist_exp x) as [l Hl]. cbn [proj1_sig].
    intros eps He. destruct (Hl eps He) as [N HN]. exists N. exact HN.
  Qed.

  (* =======================================================================
     2. Kernels on configurations
     ======================================================================= *)

  Section PK.
    Variables (L V : Type).
    Variable eqbL : L -> L -> bool.
    Variable vals : list V.

    Local Notation Cfg := (cfg L V).
    Local Notation Csum := (csum L V eqbL vals).

    Lemma csum_cv : forall (F : nat -> Cfg -> R) (G : Cfg -> R),
      (forall U, Un_cv (fun n => F n U) (G U)) ->
      forall E U0, Un_cv (fun n => Csum E (F n) U0) (Csum E G U0).
    Proof.
      intros F G H E. induction E as [| e E IH]; intro U0.
      - cbn [csum]. apply H.
      - cbn [csum].
        apply (rsum_cv vals (fun n v => Csum E (F n) (upd L V eqbL U0 e v))
                 (fun v => Csum E G (upd L V eqbL U0 e v))).
        intros v _. apply IH.
    Qed.

    Definition rk (K : Cfg -> Cfg -> R) : Prop :=
      exists ks : list (Cfg -> R), forall U U', K U U' = rsum ks (fun k => k U * k U').

    Lemma rk_ext : forall K K' : Cfg -> Cfg -> R,
      (forall U U', K U U' = K' U U') -> rk K -> rk K'.
    Proof.
      intros K K' E [ks H]. exists ks. intros U U'. rewrite <- E. apply H.
    Qed.

    Lemma rk_one : forall f : Cfg -> R, rk (fun U U' => f U * f U').
    Proof.
      intro f. exists [f]. intros U U'. rewrite rsum_cons, rsum_nil. ring.
    Qed.

    Lemma rk_const : forall c : R, 0 <= c -> rk (fun _ _ => c).
    Proof.
      intros c Hc. apply (rk_ext (fun U U' : Cfg => sqrt c * sqrt c)).
      - intros U U'. apply sqrt_sqrt. exact Hc.
      - exact (rk_one (fun _ => sqrt c)).
    Qed.

    Lemma rk_plus : forall K K' : Cfg -> Cfg -> R,
      rk K -> rk K' -> rk (fun U U' => K U U' + K' U U').
    Proof.
      intros K K' [ks H] [ks' H']. exists (ks ++ ks'). intros U U'.
      rewrite rsum_app, H, H'. reflexivity.
    Qed.

    Lemma rk_mult : forall K K' : Cfg -> Cfg -> R,
      rk K -> rk K' -> rk (fun U U' => K U U' * K' U U').
    Proof.
      intros K K' [ks H] [ks' H'].
      exists (flat_map (fun k => map (fun k' => fun U : Cfg => k U * k' U) ks') ks).
      intros U U'. rewrite H, H', rsum_mult, rsum_flat_map.
      apply rsum_ext. intros k _. rewrite rsum_map.
      apply rsum_ext. intros k' _. ring.
    Qed.

    Lemma rk_scal : forall (c : R) (K : Cfg -> Cfg -> R),
      0 <= c -> rk K -> rk (fun U U' => c * K U U').
    Proof.
      intros c K Hc HK. exact (rk_mult (fun _ _ => c) K (rk_const c Hc) HK).
    Qed.

    Lemma rk_pow : forall (K : Cfg -> Cfg -> R) (n : nat),
      rk K -> rk (fun U U' => K U U' ^ n).
    Proof.
      intros K n HK. induction n as [| n IH].
      - exact (rk_const 1 Rle_0_1).
      - exact (rk_mult K (fun U U' => K U U' ^ n) HK IH).
    Qed.

    Lemma rk_rsum : forall {A : Type} (l : list A) (K : A -> Cfg -> Cfg -> R),
      (forall a, In a l -> rk (K a)) -> rk (fun U U' => rsum l (fun a => K a U U')).
    Proof.
      intros A l K. induction l as [| a l IH]; intro H.
      - apply (rk_ext (fun _ _ => 0)); [intros; reflexivity | apply rk_const; lra].
      - apply (rk_ext (fun U U' => K a U U' + rsum l (fun b => K b U U'))).
        + intros U U'. symmetry. exact (rsum_cons a l (fun b => K b U U')).
        + apply rk_plus; [apply H; left; reflexivity |].
          apply IH. intros b Hb. apply H. right. exact Hb.
    Qed.

    (* partial sums of the exponential series *)
    Lemma rk_exp_partial : forall (S : Cfg -> Cfg -> R) (beta : R) (N : nat),
      rk S -> 0 <= beta ->
      rk (fun U U' => sum_f_R0 (fun i => / INR (fact i) * (beta * S U U') ^ i) N).
    Proof.
      intros S beta N HS Hb.
      assert (Hterm : forall i,
                rk (fun U U' => / INR (fact i) * (beta * S U U') ^ i)).
      { intro i. apply rk_scal.
        - left. apply Rinv_0_lt_compat. apply INR_fact_lt_0.
        - apply (rk_pow (fun U U' => beta * S U U')). apply rk_scal; assumption. }
      induction N as [| N IH].
      - cbn [sum_f_R0]. apply Hterm.
      - cbn [sum_f_R0].
        exact (rk_plus _ _ IH (Hterm (Datatypes.S N))).
    Qed.

    (* the double sum of a finite rank-one type kernel is a sum of squares *)
    Theorem double_rk_nonneg : forall K : Cfg -> Cfg -> R, rk K ->
      forall (E : list L) (Y : Cfg -> R) (U0 : Cfg),
        0 <= Csum E (fun U => Csum E (fun U' => Y U * Y U' * K U U') U0) U0.
    Proof.
      intros K [ks HK] E Y U0.
      set (c := fun k : Cfg -> R => Csum E (fun U => Y U * k U) U0).
      assert (H : Csum E (fun U => Csum E (fun U' => Y U * Y U' * K U U') U0) U0
                  = rsum ks (fun k => c k * c k)).
      { transitivity (Csum E (fun U => rsum ks (fun k => c k * (Y U * k U))) U0).
        - apply csum_ext. intro U.
          transitivity
            (Csum E (fun U' => rsum ks (fun k => (Y U * k U) * (Y U' * k U'))) U0).
          + apply csum_ext. intro U'. rewrite HK.
            rewrite <- rsum_scal. apply rsum_ext. intros k _. ring.
          + rewrite (ProductMeasure.csum_rsum L V eqbL vals ks E
                       (fun k U' => (Y U * k U) * (Y U' * k U')) U0).
            apply rsum_ext. intros k _. unfold c.
            rewrite (csum_scal L V eqbL vals E (Y U * k U) (fun U' => Y U' * k U') U0).
            ring.
        - rewrite (ProductMeasure.csum_rsum L V eqbL vals ks E
                     (fun k U => c k * (Y U * k U)) U0).
          apply rsum_ext. intros k _.
          rewrite (csum_scal L V eqbL vals E (c k) (fun U => Y U * k U) U0).
          reflexivity. }
      rewrite H. apply rsum_nonneg. intros k _.
      pose proof (Rle_0_sqr (c k)) as Q. unfold Rsqr in Q. exact Q.
    Qed.

    (* the exponential of a finite rank-one type kernel is a positive kernel *)
    Theorem double_exp_nonneg : forall (S : Cfg -> Cfg -> R) (beta : R),
      rk S -> 0 <= beta ->
      forall (E : list L) (Y : Cfg -> R) (U0 : Cfg),
        0 <= Csum E (fun U => Csum E (fun U' => Y U * Y U' * exp (beta * S U U')) U0) U0.
    Proof.
      intros S beta HS Hb E Y U0.
      set (P := fun (N : nat) (U U' : Cfg) =>
                  sum_f_R0 (fun i => / INR (fact i) * (beta * S U U') ^ i) N).
      apply (cv_nonneg1
               (fun N => Csum E (fun U => Csum E (fun U' => Y U * Y U' * P N U U') U0) U0)).
      - apply (csum_cv
                 (fun N U => Csum E (fun U' => Y U * Y U' * P N U U') U0)
                 (fun U => Csum E (fun U' => Y U * Y U' * exp (beta * S U U')) U0)).
        intro U.
        apply (csum_cv (fun N U' => Y U * Y U' * P N U U')
                 (fun U' => Y U * Y U' * exp (beta * S U U'))).
        intro U'.
        apply (CV_mult (fun _ => Y U * Y U') (fun N => P N U U')
                 (Y U * Y U') (exp (beta * S U U'))).
        + apply cv_const1.
        + unfold P. apply exp_cv.
      - intro N. apply double_rk_nonneg. unfold P.
        exact (rk_exp_partial S beta N HS Hb).
    Qed.
  End PK.

End PositiveKernel.
