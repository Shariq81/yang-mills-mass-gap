(* =========================================================================
   rg/exp_series_limit.v

   Real-analysis exponential generating function convergence theorem:
     If c, A : nat -> R satisfy:
       - c 0 = 0, A 0 = 1
       - forall k >= 1, k * A k = sum_{s=1}^k s * c s * A (k - s)
       - forall k > D, A k = 0   (finite polynomial support)
       - sum_{n=0}^N |c n| <= M_ub for all N   (absolute convergence)
     then:
       1. 0 < sum_{k=0}^D A k
       2. Un_cv (fun N => sum_f_R0 c N) (ln (sum_f_R0 A D)).

   Depends ONLY on Coq stdlib + rg.poly_exp_bound.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Arith Lia Lra.
From rg Require Import poly_exp_bound.
Import PolyExpBound.
Open Scope R_scope.

Module ExpSeriesLimit.

  (* =======================================================================
     1. Elementary Quantitative Bounds on exp and Partial Taylor Sums
     ======================================================================= *)

  Lemma exp_ge_1_plus : forall x, 1 + x <= exp x.
  Proof.
    intro x. destruct (Req_dec x 0) as [-> | Hne].
    - rewrite exp_0. lra.
    - left. apply exp_ineq1. exact Hne.
  Qed.

  Lemma exp_lip_half : forall h,
    Rabs h <= / 2 -> Rabs (exp h - 1) <= 2 * Rabs h.
  Proof.
    intros h Hh.
    assert (Hbounds : - (/ 2) <= h /\ h <= / 2)
      by (unfold Rabs in Hh; destruct (Rcase_abs h); lra).
    destruct (Rle_lt_dec 0 h) as [Hpos | Hneg].
    - pose proof (exp_ge_1_plus h) as Hlow.
      pose proof (exp_ge_1_plus (- h)) as Hneg_low.
      rewrite exp_Ropp in Hneg_low.
      pose proof (exp_pos h) as Hpe.
      assert (Hupp : exp h * (1 - h) <= 1).
      { apply Rle_trans with (exp h * / exp h).
        - apply Rmult_le_compat_l; lra.
        - rewrite Rinv_r; lra. }
      assert (Hupp2 : exp h - 1 <= 2 * h).
      { assert (H1mh : / 2 <= 1 - h) by lra.
        assert (Hmult : (exp h - 1) * (1 - h) <= h) by lra.
        nra. }
      rewrite Rabs_right; [rewrite Rabs_right; lra | lra].
    - pose proof (exp_ge_1_plus h) as Hlow.
      assert (Hupp : exp h <= 1) by (rewrite <- exp_0; left; apply exp_increasing; exact Hneg).
      rewrite Rabs_left1; [| lra].
      rewrite Rabs_left; [lra | exact Hneg].
  Qed.

  Lemma exp_diff_lip : forall x y,
    Rabs (x - y) <= / 2 ->
    Rabs (exp x - exp y) <= 2 * exp y * Rabs (x - y).
  Proof.
    intros x y Hxy.
    replace (exp x - exp y) with (exp y * (exp (x - y) - 1))
      by (rewrite Rmult_minus_distr_l, <- exp_plus, Rmult_1_r; f_equal; f_equal; ring).
    rewrite Rabs_mult, (Rabs_right (exp y) ltac:(left; apply exp_pos)).
    pose proof (exp_lip_half (x - y) Hxy) as Hl.
    pose proof (exp_pos y) as Hpe. nra.
  Qed.

  Lemma sum_f_R0_split_tail : forall f N K,
    (N <= K)%nat ->
    sum_f_R0 f K - sum_f_R0 f N =
    match (K - N)%nat with
    | 0%nat => 0
    | S d => sum_f_R0 (fun i => f (S (N + i))%nat) d
    end.
  Proof.
    intros f N K Hle.
    induction Hle as [| K' Hle' IH].
    - rewrite Nat.sub_diag. ring.
    - change (sum_f_R0 f (S K')) with (sum_f_R0 f K' + f (S K')).
      replace (sum_f_R0 f K' + f (S K') - sum_f_R0 f N)
         with ((sum_f_R0 f K' - sum_f_R0 f N) + f (S K')) by ring.
      rewrite IH.
      destruct (K' - N)%nat as [| d] eqn:Ed.
      + assert (K' = N) by lia. subst K'.
        replace (S N - N)%nat with 1%nat by lia. simpl.
        replace (N + 0)%nat with N by lia. ring.
      + replace (S K' - N)%nat with (S (S d)) by lia.
        cbn [sum_f_R0].
        replace (S (N + S d)) with (S K') by lia. ring.
  Qed.

  Lemma Rabs_sum_f_R0_le : forall f g N,
    (forall i, (i <= N)%nat -> Rabs (f i) <= g i) ->
    Rabs (sum_f_R0 f N) <= sum_f_R0 g N.
  Proof.
    intros f g N. induction N as [| N' IH]; intro Hle; simpl.
    - apply Hle; lia.
    - eapply Rle_trans; [apply Rabs_triang |].
      apply Rplus_le_compat; [apply IH; intros i Hi; apply Hle; lia | apply Hle; lia].
  Qed.

  Lemma Rabs_pow : forall x m, Rabs (x ^ m) = (Rabs x) ^ m.
  Proof.
    intros x. induction m as [| m' IH]; simpl; [apply Rabs_R1 | rewrite Rabs_mult, IH; reflexivity].
  Qed.

  Lemma pow_le_compat_nonneg : forall x y m,
    0 <= x -> x <= y -> x ^ m <= y ^ m.
  Proof.
    intros x y m Hx Hxy. induction m as [| m' IH]; simpl; [lra |].
    apply Rmult_le_compat; try exact Hx; try exact Hxy; try exact IH.
    apply pow_le; exact Hx.
  Qed.

  (* Quantitative Taylor tail bound for signed x with |x| <= M *)
  Lemma exp_taylor_err_le : forall x M N,
    Rabs x <= M ->
    Rabs (sum_f_R0 (fun m => / INR (fact m) * x ^ m) N - exp x) <=
    exp M - sum_f_R0 (fun m => / INR (fact m) * M ^ m) N.
  Proof.
    intros x M N HxM.
    assert (HM : 0 <= M) by (pose proof (Rabs_pos x); lra).
    (* Show for every eps > 0, LHS <= RHS + eps *)
    destruct (Rle_lt_dec
      (Rabs (sum_f_R0 (fun m => / INR (fact m) * x ^ m) N - exp x))
      (exp M - sum_f_R0 (fun m => / INR (fact m) * M ^ m) N)) as [Hle | Hgt];
      [exact Hle | exfalso].
    set (eps := (Rabs (sum_f_R0 (fun m => / INR (fact m) * x ^ m) N - exp x) -
                 (exp M - sum_f_R0 (fun m => / INR (fact m) * M ^ m) N)) / 2).
    assert (Heps : 0 < eps) by (unfold eps; lra).
    assert (Hx_cv : infinite_sum (fun m => / INR (fact m) * x ^ m) (exp x)).
    { unfold exp. exact (proj2_sig (exist_exp x)). }
    assert (HM_cv : infinite_sum (fun m => / INR (fact m) * M ^ m) (exp M)).
    { unfold exp. exact (proj2_sig (exist_exp M)). }
    destruct (Hx_cv (eps / 2) ltac:(lra)) as [K1 HK1].
    destruct (HM_cv (eps / 2) ltac:(lra)) as [K2 HK2].
    set (K := Nat.max N (Nat.max K1 K2)).
    specialize (HK1 K ltac:(unfold K; lia)).
    specialize (HK2 K ltac:(unfold K; lia)).
    unfold R_dist in HK1, HK2.
    assert (Htail_le :
      Rabs (sum_f_R0 (fun m => / INR (fact m) * x ^ m) K -
            sum_f_R0 (fun m => / INR (fact m) * x ^ m) N) <=
      sum_f_R0 (fun m => / INR (fact m) * M ^ m) K -
      sum_f_R0 (fun m => / INR (fact m) * M ^ m) N).
    { rewrite !sum_f_R0_split_tail by (unfold K; lia).
      destruct (K - N)%nat as [| d]; [rewrite Rabs_R0; lra |].
      apply Rabs_sum_f_R0_le. intros i _.
      rewrite Rabs_mult, (Rabs_right (/ INR (fact (S (N + i)))) ltac:(left; apply Rinv_0_lt_compat, fact_pos_R)).
      rewrite Rabs_pow.
      apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat, fact_pos_R |].
      apply pow_le_compat_nonneg; [apply Rabs_pos | exact HxM]. }
    assert (Htri :
      Rabs (sum_f_R0 (fun m => / INR (fact m) * x ^ m) N - exp x) <=
      Rabs (sum_f_R0 (fun m => / INR (fact m) * x ^ m) K - sum_f_R0 (fun m => / INR (fact m) * x ^ m) N) +
      Rabs (sum_f_R0 (fun m => / INR (fact m) * x ^ m) K - exp x)).
    { replace (sum_f_R0 (fun m => / INR (fact m) * x ^ m) N - exp x)
         with (- (sum_f_R0 (fun m => / INR (fact m) * x ^ m) K - sum_f_R0 (fun m => / INR (fact m) * x ^ m) N) +
               (sum_f_R0 (fun m => / INR (fact m) * x ^ m) K - exp x)) by ring.
      eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
    apply Rabs_def2 in HK2. unfold eps in *. lra.
  Qed.

  (* Lipschitz bound for partial Taylor polynomial of exp on [0, M] *)
  Lemma pow_diff_le : forall x M m,
    0 <= x -> x <= M ->
    M ^ (S m) - x ^ (S m) <= INR (S m) * M ^ m * (M - x).
  Proof.
    intros x M m Hx HxM. induction m as [| m' IH].
    - simpl. lra.
    - change (M ^ (S (S m'))) with (M * M ^ (S m')).
      change (x ^ (S (S m'))) with (x * x ^ (S m')).
      replace (M * M ^ (S m') - x * x ^ (S m'))
         with ((M - x) * M ^ (S m') + x * (M ^ (S m') - x ^ (S m'))) by ring.
      assert (H2 : x * (M ^ (S m') - x ^ (S m')) <= M * (INR (S m') * M ^ m' * (M - x))).
      { apply Rmult_le_compat; [exact Hx | | exact HxM | exact IH].
        pose proof (pow_le_compat_nonneg x M (S m') Hx HxM); lra. }
      replace (INR (S (S m')) * M ^ (S m') * (M - x))
         with ((M - x) * M ^ (S m') + M * (INR (S m') * M ^ m' * (M - x)))
        by (rewrite (S_INR (S m')); change (M ^ (S m')) with (M * M ^ m'); ring).
      lra.
  Qed.

  Lemma taylor_exp_diff_le : forall x M m0,
    0 <= x -> x <= M ->
    sum_f_R0 (fun m => / INR (fact m) * M ^ m) m0 -
    sum_f_R0 (fun m => / INR (fact m) * x ^ m) m0 <=
    (M - x) * exp M.
  Proof.
    intros x M m0 Hx HxM.
    destruct m0 as [| m0'].
    - simpl. pose proof (exp_pos M). nra.
    - rewrite !sum_f_R0_shift.
      replace ((/ INR (fact 0%nat) * M ^ 0 + sum_f_R0 (fun i => / INR (fact (S i)) * M ^ (S i)) m0') -
               (/ INR (fact 0%nat) * x ^ 0 + sum_f_R0 (fun i => / INR (fact (S i)) * x ^ (S i)) m0'))
         with (sum_f_R0 (fun i => / INR (fact (S i)) * (M ^ (S i) - x ^ (S i))) m0').
      + eapply Rle_trans.
        * apply sum_f_R0_le. intros i _.
          apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat, fact_pos_R |].
          exact (pow_diff_le x M i Hx HxM).
        * assert (Hsimp :
            sum_f_R0 (fun i => / INR (fact (S i)) * (INR (S i) * M ^ i * (M - x))) m0' =
            (M - x) * sum_f_R0 (fun i => / INR (fact i) * M ^ i) m0').
          { rewrite <- sum_f_R0_scale. apply sum_f_R0_ext. intros i _.
            assert (Hf : INR (fact (S i)) = INR (S i) * INR (fact i)).
            { change (fact (S i)) with (S i * fact i)%nat. rewrite mult_INR. reflexivity. }
            assert (Hne1 : INR (S i) <> 0) by (apply not_0_INR; lia).
            assert (Hne2 : INR (fact i) <> 0) by (apply not_0_INR, fact_neq_0).
            rewrite Hf. field. split; assumption. }
          rewrite Hsimp.
          apply Rmult_le_compat_l; [lra |].
          apply exp_partial_sum_le; lra.
      + clear. induction m0' as [| m IH].
        * simpl. ring.
        * cbn [sum_f_R0]. rewrite IH. ring.
  Qed.

  (* =======================================================================
     2. Absolute Convergence -> Real Limits S and M via growing_cv
     ======================================================================= *)

  Lemma growing_cv_le : forall Un l,
    Un_growing Un -> Un_cv Un l -> forall n, Un n <= l.
  Proof.
    intros Un l Hgr Hcv n.
    destruct (Rle_lt_dec (Un n) l) as [Hle | Hgt]; [exact Hle | exfalso].
    set (eps := (Un n - l) / 2).
    assert (Heps : 0 < eps) by (unfold eps; lra).
    destruct (Hcv eps Heps) as [N HN].
    set (K := Nat.max n N).
    specialize (HN K (Nat.le_max_r n N)). unfold R_dist in HN.
    assert (Hmono : Un n <= Un K).
    { assert (Hgen : forall b, (n <= b)%nat -> Un n <= Un b).
      { intros b Hle. induction Hle as [| k' Hle' IH]; [lra | pose proof (Hgr k'); lra]. }
      apply Hgen. unfold K; lia. }
    apply Rabs_def2 in HN. unfold eps in HN. lra.
  Qed.

  Lemma abs_conv_limits : forall (c : nat -> R) (M_ub : R),
    (forall N, sum_f_R0 (fun n => Rabs (c n)) N <= M_ub) ->
    exists S M,
      Un_cv (fun N => sum_f_R0 c N) S /\
      Un_cv (fun N => sum_f_R0 (fun n => Rabs (c n)) N) M /\
      0 <= M /\
      (forall N, sum_f_R0 (fun n => Rabs (c n)) N <= M) /\
      (forall N, Rabs (sum_f_R0 c N) <= M) /\
      Rabs S <= M.
  Proof.
    intros c M_ub Hub.
    set (cp := fun n => Rmax (c n) 0).
    set (cm := fun n => Rmax (- c n) 0).
    assert (Hsplit : forall n, c n = cp n - cm n).
    { intro n. unfold cp, cm, Rmax.
      destruct (Rle_dec (c n) 0); destruct (Rle_dec (- c n) 0); lra. }
    assert (Hcp_nn : forall n, 0 <= cp n) by (intro n; unfold cp; apply Rmax_r).
    assert (Hcm_nn : forall n, 0 <= cm n) by (intro n; unfold cm; apply Rmax_r).
    assert (Hcp_le : forall n, cp n <= Rabs (c n)).
    { intro n. unfold cp. apply Rmax_lub; [apply Rle_abs | apply Rabs_pos]. }
    assert (Hcm_le : forall n, cm n <= Rabs (c n)).
    { intro n. unfold cm. apply Rmax_lub; [rewrite <- Rabs_Ropp; apply Rle_abs | apply Rabs_pos]. }
    assert (Hmk_ub : forall f, (forall N, f N <= M_ub) -> has_ub f).
    { intros f Hf. exists M_ub. intros x [N ->]. apply Hf. }
    destruct (growing_cv (fun N => sum_f_R0 cp N)
                (fun n => ltac:(simpl; pose proof (Hcp_nn (S n)); lra))
                (Hmk_ub _ (fun N => Rle_trans _ _ _ (sum_f_R0_le _ _ N (fun i _ => Hcp_le i)) (Hub N))))
      as [Sp HSp].
    destruct (growing_cv (fun N => sum_f_R0 cm N)
                (fun n => ltac:(simpl; pose proof (Hcm_nn (S n)); lra))
                (Hmk_ub _ (fun N => Rle_trans _ _ _ (sum_f_R0_le _ _ N (fun i _ => Hcm_le i)) (Hub N))))
      as [Sm HSm].
    destruct (growing_cv (fun N => sum_f_R0 (fun n => Rabs (c n)) N)
                (fun n => ltac:(simpl; pose proof (Rabs_pos (c (S n))); lra))
                (Hmk_ub _ Hub))
      as [M HM].
    assert (HS_cv : Un_cv (fun N => sum_f_R0 c N) (Sp - Sm)).
    { intros eps Heps.
      destruct (HSp (eps / 2) ltac:(lra)) as [N1 HN1].
      destruct (HSm (eps / 2) ltac:(lra)) as [N2 HN2].
      exists (Nat.max N1 N2). intros N HN.
      specialize (HN1 N ltac:(lia)). specialize (HN2 N ltac:(lia)).
      unfold R_dist in *.
      assert (Heq : sum_f_R0 c N = sum_f_R0 cp N - sum_f_R0 cm N).
      { clear - Hsplit. induction N as [| N' IH]; simpl; [apply Hsplit | rewrite IH, (Hsplit (S N')); ring]. }
      rewrite Heq.
      replace (sum_f_R0 cp N - sum_f_R0 cm N - (Sp - Sm))
         with ((sum_f_R0 cp N - Sp) - (sum_f_R0 cm N - Sm)) by ring.
      eapply Rle_lt_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
    assert (HM_le : forall N, sum_f_R0 (fun n => Rabs (c n)) N <= M).
    { apply growing_cv_le; [intro n; simpl; pose proof (Rabs_pos (c (S n))); lra | exact HM]. }
    assert (HM_nn : 0 <= M).
    { pose proof (HM_le 0%nat) as H0. simpl in H0. pose proof (Rabs_pos (c 0%nat)). lra. }
    assert (HRabs_N : forall N, Rabs (sum_f_R0 c N) <= M).
    { intro N. eapply Rle_trans; [apply (Rabs_sum_f_R0_le c (fun n => Rabs (c n)) N); intros i _; lra | apply HM_le]. }
    assert (HRabs_S : Rabs (Sp - Sm) <= M).
    { destruct (Rle_lt_dec (Rabs (Sp - Sm)) M) as [Hle | Hgt]; [exact Hle | exfalso].
      set (eps := (Rabs (Sp - Sm) - M) / 2).
      destruct (HS_cv eps ltac:(unfold eps; lra)) as [N HN].
      specialize (HN N (le_n N)). unfold R_dist in HN.
      pose proof (HRabs_N N) as HNle.
      assert (Htri : Rabs (Sp - Sm) <= Rabs (sum_f_R0 c N) + Rabs (sum_f_R0 c N - (Sp - Sm))).
      { replace (Rabs (Sp - Sm)) with (Rabs (sum_f_R0 c N + - (sum_f_R0 c N - (Sp - Sm)))) by (f_equal; ring).
        eapply Rle_trans; [apply Rabs_triang | rewrite Rabs_Ropp; lra]. }
      unfold eps in HN. lra. }
    exists (Sp - Sm), M. repeat split; assumption.
  Qed.

  (* =======================================================================
     3. Polynomial Dominance & Truncated Power Comparison Lemmas
     ======================================================================= *)

  Lemma p_pow_Rabs_le : forall p q m k,
    (forall i, Rabs (p i) <= q i) ->
    Rabs (p_pow p m k) <= p_pow q m k.
  Proof.
    intros p q m. induction m as [| m' IH]; intros k Hpq.
    - simpl. unfold p_one. destruct k; [rewrite Rabs_R1; lra | rewrite Rabs_R0; lra].
    - simpl. unfold p_mul.
      apply Rabs_sum_f_R0_le. intros j _.
      rewrite Rabs_mult.
      apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hpq | apply IH; exact Hpq].
  Qed.

  Lemma p_pow_mono : forall p q m k,
    (forall i, 0 <= p i) ->
    (forall i, p i <= q i) ->
    p_pow p m k <= p_pow q m k.
  Proof.
    intros p q m. induction m as [| m' IH]; intros k Hp Hpq.
    - simpl; lra.
    - simpl. unfold p_mul.
      apply sum_f_R0_le. intros j _.
      apply Rmult_le_compat; [apply Hp | apply p_pow_nonneg; exact Hp | apply Hpq | apply IH; assumption].
  Qed.

  Lemma p_pow_agree_low : forall p q N m k,
    (forall i, (i <= N)%nat -> p i = q i) ->
    (k <= N)%nat ->
    p_pow p m k = p_pow q m k.
  Proof.
    intros p q N m. induction m as [| m' IH]; intros k Hag Hk; [simpl; reflexivity |].
    simpl. unfold p_mul.
    apply sum_f_R0_ext. intros j Hj.
    rewrite (Hag j ltac:(lia)), (IH (k - j)%nat Hag ltac:(lia)). reflexivity.
  Qed.

  Lemma p_exp_trunc_Rabs_le : forall p q M k,
    (forall i, Rabs (p i) <= q i) ->
    Rabs (p_exp_trunc p M k) <= p_exp_trunc q M k.
  Proof.
    intros p q M k Hpq. unfold p_exp_trunc.
    apply Rabs_sum_f_R0_le. intros m _.
    rewrite Rabs_mult, (Rabs_right (/ INR (fact m)) ltac:(left; apply Rinv_0_lt_compat, fact_pos_R)).
    apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat, fact_pos_R | apply p_pow_Rabs_le; exact Hpq].
  Qed.

  Lemma p_exp_trunc_stabilize : forall p M1 M2 k,
    p 0%nat = 0 -> (k <= M1)%nat -> (M1 <= M2)%nat ->
    p_exp_trunc p M2 k = p_exp_trunc p M1 k.
  Proof.
    intros p M1 M2 k Hp0 Hk Hle. unfold p_exp_trunc.
    induction Hle as [| M' Hle' IH]; [reflexivity |].
    cbn [sum_f_R0]. rewrite IH.
    rewrite (p_pow_vanish p (S M') k Hp0 ltac:(lia)). ring.
  Qed.

  Lemma p_exp_trunc_eval1 : forall p D M,
    (forall i, (D < i)%nat -> p i = 0) ->
    sum_f_R0 (p_exp_trunc p M) (M * D)%nat =
    sum_f_R0 (fun m => / INR (fact m) * (sum_f_R0 p D) ^ m) M.
  Proof.
    intros p D M Hsupp. unfold p_exp_trunc.
    assert (Hswap : forall A B (F : nat -> nat -> R),
      sum_f_R0 (fun k => sum_f_R0 (fun m => F k m) B) A =
      sum_f_R0 (fun m => sum_f_R0 (fun k => F k m) A) B).
    { induction A as [| A' IHA]; intros B F; [simpl; reflexivity |].
      change (sum_f_R0 (fun k => sum_f_R0 (fun m => F k m) B) (S A'))
        with (sum_f_R0 (fun k => sum_f_R0 (fun m => F k m) B) A' + sum_f_R0 (fun m => F (S A') m) B).
      rewrite (IHA B F), <- sum_f_R0_plus.
      apply sum_f_R0_ext; intros m _; cbn [sum_f_R0]; reflexivity. }
    rewrite Hswap. apply sum_f_R0_ext. intros m Hm.
    rewrite sum_f_R0_scale. f_equal.
    assert (Htail : forall (f : nat -> R) A B,
      (A <= B)%nat -> (forall i, (A < i)%nat -> f i = 0) ->
      sum_f_R0 f B = sum_f_R0 f A).
    { intros f A B Hle Hf. induction Hle as [| B' Hle' IH]; [reflexivity |].
      cbn [sum_f_R0]. rewrite IH, Hf; [ring | lia]. }
    rewrite (Htail (p_pow p m) (m * D)%nat (M * D)%nat ltac:(nia) (fun k Hk => p_pow_support p D m k Hsupp Hk)).
    exact (p_pow_eval1 p D m Hsupp).
  Qed.

  (* =======================================================================
     4. Main Convergence Theorem: exp(sum c_n) = sum_{k=0}^D A_k
     ======================================================================= *)

  Theorem exp_of_abs_conv_recurrence : forall (c A : nat -> R) (D : nat) (M_ub : R),
    c 0%nat = 0 ->
    A 0%nat = 1 ->
    (forall k, (1 <= k)%nat ->
      INR k * A k = sum_f_R0 (fun j => INR (S j) * c (S j) * A (k - S j)%nat) (k - 1)%nat) ->
    (forall k, (D < k)%nat -> A k = 0) ->
    (forall N, sum_f_R0 (fun n => Rabs (c n)) N <= M_ub) ->
    0 < sum_f_R0 A D /\ Un_cv (fun N => sum_f_R0 c N) (ln (sum_f_R0 A D)).
  Proof.
    intros c A D M_ub Hc0 HA0 Hrec HsuppA Hub.
    destruct (abs_conv_limits c M_ub Hub) as [L [M [HL_cv [HM_cv [HM_nn [HM_le [HRabs_N HRabs_L]]]]]]].
    set (Z := sum_f_R0 A D).
    set (ca := fun n => Rabs (c n)).
    assert (Hca0 : ca 0%nat = 0) by (unfold ca; rewrite Hc0, Rabs_R0; reflexivity).
    assert (Hca_nn : forall n, 0 <= ca n) by (intro n; unfold ca; apply Rabs_pos).
    set (b := fun k => p_exp_trunc ca k k).
    assert (Hb_nn : forall k, 0 <= b k).
    { intro k. unfold b, p_exp_trunc. apply sum_f_R0_nonneg. intros m _.
      apply Rmult_le_pos; [left; apply Rinv_0_lt_compat, fact_pos_R | apply p_pow_nonneg; exact Hca_nn]. }
    (* Step 1: For any N, A k = p_exp_trunc P_N N k for all k <= N *)
    assert (HA_eq : forall N k, (k <= N)%nat ->
      let P_N := fun i => if Nat.leb i N then c i else 0 in
      A k = p_exp_trunc P_N N k).
    { intros N k. induction k as [k IH] using lt_wf_ind. intros Hk P_N.
      assert (HP0 : P_N 0%nat = 0) by (unfold P_N; simpl; exact Hc0).
      destruct k as [| k'].
      - rewrite HA0, (p_exp_trunc_0 P_N N HP0). reflexivity.
      - assert (Hne : INR (S k') <> 0) by (apply not_0_INR; lia).
        apply Rmult_eq_reg_l with (r := INR (S k')); [| exact Hne].
        rewrite (Hrec (S k') ltac:(lia)).
        rewrite (p_exp_trunc_recurrence P_N N (S k') HP0 ltac:(lia)).
        apply sum_f_R0_ext. intros j Hj.
        assert (HPj : P_N (S j) = c (S j)).
        { unfold P_N. destruct (Nat.leb_spec (S j) N); [reflexivity | lia]. }
        rewrite HPj, (IH (S k' - S j)%nat ltac:(lia) ltac:(lia)). reflexivity. }
    (* Step 2: Show sum_{k=0}^N b k approaches exp M from below *)
    assert (Hb_to_expM : forall eps, 0 < eps ->
      exists N0, forall N, (N0 <= N)%nat -> exp M - sum_f_R0 b N < eps).
    { intros eps Heps.
      assert (HM_exp : infinite_sum (fun m => / INR (fact m) * M ^ m) (exp M))
        by (unfold exp; exact (proj2_sig (exist_exp M))).
      destruct (HM_exp (eps / 2) ltac:(lra)) as [m0 Hm0].
      specialize (Hm0 m0 (le_n m0)). unfold R_dist in Hm0.
      apply Rabs_def2 in Hm0.
      pose proof (exp_pos M) as HexpM_pos.
      destruct (HM_cv (eps / (2 * exp M)) ltac:(apply Rdiv_lt_0_compat; lra)) as [D0 HD0].
      specialize (HD0 D0 (le_n D0)). unfold R_dist in HD0. apply Rabs_def2 in HD0.
      exists (Nat.max m0 (m0 * D0)%nat). intros N HN.
      set (Q0 := fun i => if Nat.leb i D0 then ca i else 0).
      assert (HQ0_supp : forall i, (D0 < i)%nat -> Q0 i = 0).
      { intros i Hi. unfold Q0. destruct (Nat.leb_spec i D0); [lia | reflexivity]. }
      assert (HQ0_nn : forall i, 0 <= Q0 i).
      { intro i. unfold Q0. destruct (Nat.leb_spec i D0); [apply Hca_nn | lra]. }
      assert (HQ0_le : forall i, Q0 i <= ca i).
      { intro i. unfold Q0. destruct (Nat.leb_spec i D0); [lra | apply Hca_nn]. }
      assert (HQ0_sum : sum_f_R0 Q0 D0 = sum_f_R0 ca D0).
      { apply sum_f_R0_ext. intros i Hi. unfold Q0. destruct (Nat.leb_spec i D0); [reflexivity | lia]. }
      assert (Hlow : sum_f_R0 (fun m => / INR (fact m) * (sum_f_R0 ca D0) ^ m) m0 <= sum_f_R0 b N).
      { rewrite <- HQ0_sum, <- (p_exp_trunc_eval1 Q0 D0 m0 HQ0_supp).
        eapply Rle_trans; [| apply (sum_f_R0_mono b (m0 * D0)%nat N Hb_nn ltac:(lia))].
        apply sum_f_R0_le. intros k Hk.
        unfold b.
        apply Rle_trans with (r2 := p_exp_trunc ca m0 k).
        - unfold p_exp_trunc. apply sum_f_R0_le. intros m _.
          apply Rmult_le_compat_l; [left; apply Rinv_0_lt_compat, fact_pos_R |].
          exact (p_pow_mono Q0 ca m k HQ0_nn HQ0_le).
        - destruct (le_lt_dec m0 k) as [Hmk | Hkm].
          + unfold p_exp_trunc. apply sum_f_R0_mono; [| exact Hmk].
            intro m. apply Rmult_le_pos; [left; apply Rinv_0_lt_compat, fact_pos_R | apply p_pow_nonneg; exact Hca_nn].
          + rewrite (p_exp_trunc_stabilize ca k m0 k Hca0 (le_n k) ltac:(lia)). lra. }
      pose proof (taylor_exp_diff_le (sum_f_R0 ca D0) M m0
                    (sum_f_R0_nonneg ca D0 (fun i _ => Hca_nn i)) (HM_le D0)) as Htdiff.
      assert (Hmr : (M - sum_f_R0 ca D0) * exp M < eps / 2).
      { apply Rlt_le_trans with (r2 := (eps / (2 * exp M)) * exp M).
        - apply Rmult_lt_compat_r; [exact HexpM_pos | unfold ca; lra].
        - right; field; lra. }
      lra. }
    (* Step 3: Prove exp L = Z by showing Rabs (exp L - Z) < eps for all eps > 0 *)
    assert (HexpL_eq_Z : exp L = Z).
    { destruct (Req_dec (exp L) Z) as [Heq | Hne]; [exact Heq | exfalso].
      set (eps := Rabs (exp L - Z)).
      assert (Heps : 0 < eps) by (unfold eps; apply Rabs_pos_lt; lra).
      pose proof (exp_pos L) as HexpL_pos.
      (* Choose N large enough for all 3 pieces < eps / 3 *)
      destruct (Hb_to_expM (eps / 3) ltac:(lra)) as [N1 HN1].
      assert (HM_exp : infinite_sum (fun m => / INR (fact m) * M ^ m) (exp M))
        by (unfold exp; exact (proj2_sig (exist_exp M))).
      destruct (HM_exp (eps / 3) ltac:(lra)) as [N2 HN2].
      set (delta := Rmin (/ 2) (eps / (6 * exp L))).
      assert (Hdelta : 0 < delta).
      { unfold delta. apply Rmin_pos; [lra | apply Rdiv_lt_0_compat; lra]. }
      destruct (HL_cv delta Hdelta) as [N3 HN3].
      set (N := Nat.max (Nat.max D 1%nat) (Nat.max N1 (Nat.max N2 N3))).
      set (P_N := fun i => if Nat.leb i N then c i else 0).
      set (Q_N := fun i => if Nat.leb i N then ca i else 0).
      assert (HP_supp : forall i, (N < i)%nat -> P_N i = 0)
        by (intros i Hi; unfold P_N; destruct (Nat.leb_spec i N); [lia | reflexivity]).
      assert (HQ_supp : forall i, (N < i)%nat -> Q_N i = 0)
        by (intros i Hi; unfold Q_N; destruct (Nat.leb_spec i N); [lia | reflexivity]).
      assert (HP_sum : sum_f_R0 P_N N = sum_f_R0 c N)
        by (apply sum_f_R0_ext; intros i Hi; unfold P_N; destruct (Nat.leb_spec i N); [reflexivity | lia]).
      assert (HQ_sum : sum_f_R0 Q_N N = sum_f_R0 ca N)
        by (apply sum_f_R0_ext; intros i Hi; unfold Q_N; destruct (Nat.leb_spec i N); [reflexivity | lia]).
      (* Piece A: |sum_{m=0}^N S_N^m/m! - Z| <= exp M - sum_{k=0}^N b k < eps / 3 *)
      assert (HPieceA : Rabs (sum_f_R0 (fun m => / INR (fact m) * (sum_f_R0 c N) ^ m) N - Z) < eps / 3).
      { rewrite <- HP_sum, <- (p_exp_trunc_eval1 P_N N N HP_supp).
        assert (HZ_eq : Z = sum_f_R0 (p_exp_trunc P_N N) N).
        { unfold Z.
          assert (HtailA : forall K, (D <= K)%nat -> sum_f_R0 A K = sum_f_R0 A D).
          { intros K HleDK.
            induction HleDK as [| K' Hle' IH]; [reflexivity |].
            cbn [sum_f_R0]. rewrite IH, (HsuppA (S K') ltac:(lia)). ring. }
          rewrite <- (HtailA N ltac:(unfold N; lia)). apply sum_f_R0_ext. intros k Hk.
          exact (HA_eq N k Hk). }
        rewrite HZ_eq, (sum_f_R0_split_tail (p_exp_trunc P_N N) N (N * N)%nat ltac:(unfold N; nia)).
        assert (Habs_tail :
          Rabs (match (N * N - N)%nat with
                | 0%nat => 0
                | S d => sum_f_R0 (fun i => p_exp_trunc P_N N (S (N + i))) d
                end) <=
          sum_f_R0 (p_exp_trunc Q_N N) (N * N)%nat - sum_f_R0 (p_exp_trunc Q_N N) N).
        { rewrite (sum_f_R0_split_tail (p_exp_trunc Q_N N) N (N * N)%nat ltac:(unfold N; nia)).
          destruct (N * N - N)%nat as [| d]; [rewrite Rabs_R0; lra |].
          apply Rabs_sum_f_R0_le. intros i _.
          apply p_exp_trunc_Rabs_le. intro j. unfold P_N, Q_N, ca.
          destruct (Nat.leb_spec j N); [lra | rewrite Rabs_R0; lra]. }
        eapply Rle_lt_trans; [exact Habs_tail |].
        rewrite (p_exp_trunc_eval1 Q_N N N HQ_supp), HQ_sum.
        assert (HQ_low : sum_f_R0 (p_exp_trunc Q_N N) N = sum_f_R0 b N).
        { apply sum_f_R0_ext. intros k Hk.
          unfold b.
          rewrite <- (p_exp_trunc_stabilize ca k N k Hca0 (le_n k) Hk).
          unfold p_exp_trunc. apply sum_f_R0_ext. intros m _. f_equal.
          apply (p_pow_agree_low Q_N ca N m k).
          - intros i Hi. unfold Q_N. destruct (Nat.leb_spec i N); [reflexivity | lia].
          - exact Hk. }
        rewrite HQ_low.
        pose proof (exp_partial_sum_le (sum_f_R0 ca N) N (sum_f_R0_nonneg ca N (fun i _ => Hca_nn i))) as Hle1.
        assert (Hle2 : exp (sum_f_R0 ca N) <= exp M).
        { unfold ca. destruct (Rle_lt_or_eq_dec _ _ (HM_le N)) as [Hlt | Heq];
            [left; apply exp_increasing; exact Hlt | rewrite Heq; lra]. }
        pose proof (HN1 N ltac:(unfold N; lia)). lra. }
      (* Piece B: |sum_{m=0}^N S_N^m/m! - exp S_N| <= exp M - sum_{m=0}^N M^m/m! < eps / 3 *)
      assert (HPieceB : Rabs (sum_f_R0 (fun m => / INR (fact m) * (sum_f_R0 c N) ^ m) N - exp (sum_f_R0 c N)) < eps / 3).
      { eapply Rle_lt_trans; [apply (exp_taylor_err_le (sum_f_R0 c N) M N (HRabs_N N)) |].
        specialize (HN2 N ltac:(unfold N; lia)). unfold R_dist in HN2. apply Rabs_def2 in HN2. lra. }
      (* Piece C: |exp S_N - exp L| < eps / 3 *)
      assert (HPieceC : Rabs (exp (sum_f_R0 c N) - exp L) < eps / 3).
      { specialize (HN3 N ltac:(unfold N; lia)). unfold R_dist in HN3.
        assert (Hle_half : Rabs (sum_f_R0 c N - L) <= / 2) by (unfold delta in HN3; pose proof (Rmin_l (/ 2) (eps / (6 * exp L))); lra).
        eapply Rle_lt_trans; [apply (exp_diff_lip (sum_f_R0 c N) L Hle_half) |].
        assert (Hlt_d : Rabs (sum_f_R0 c N - L) < eps / (6 * exp L))
          by (unfold delta in HN3; pose proof (Rmin_r (/ 2) (eps / (6 * exp L))); lra).
        apply Rlt_le_trans with (r2 := 2 * exp L * (eps / (6 * exp L))).
        - apply Rmult_lt_compat_l; [lra | exact Hlt_d].
        - right; field; lra. }
      (* Triangle inequality contradicts eps = Rabs (exp L - Z) *)
      assert (Htri : Rabs (exp L - Z) <=
        Rabs (exp (sum_f_R0 c N) - exp L) +
        Rabs (sum_f_R0 (fun m => / INR (fact m) * (sum_f_R0 c N) ^ m) N - exp (sum_f_R0 c N)) +
        Rabs (sum_f_R0 (fun m => / INR (fact m) * (sum_f_R0 c N) ^ m) N - Z)).
      { replace (exp L - Z)
           with (- (exp (sum_f_R0 c N) - exp L) +
                 (- (sum_f_R0 (fun m => / INR (fact m) * (sum_f_R0 c N) ^ m) N - exp (sum_f_R0 c N)) +
                  (sum_f_R0 (fun m => / INR (fact m) * (sum_f_R0 c N) ^ m) N - Z))) by ring.
        eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp.
        rewrite Rplus_assoc. apply Rplus_le_compat_l.
        eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
      unfold eps in *. lra. }
    (* Conclude Z > 0 and Un_cv (sum_f_R0 c) (ln Z) *)
    rewrite <- HexpL_eq_Z. split.
    - apply exp_pos.
    - rewrite ln_exp. exact HL_cv.
  Qed.

End ExpSeriesLimit.
