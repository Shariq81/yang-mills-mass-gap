(* =========================================================================
   ym/su2_haar_moments.v

   Moments of the Haar measure of SU(2) realized by the dyadic Hopf grids
   (`su2_grid_mean` of verification/ChallengeSU2GaugeInvariance.v): the
   Haar integral of a monomial in the four coordinates of S^3 is unchanged
   when the exponents of the second and of the third coordinate are
   exchanged.

     - `gmean_factor`: the grid average of a monomial is a product of three
       one-dimensional means, one for each Hopf coordinate;
     - `Tm_zero`, `haar_mono_odd`: the grid averages of a monomial with an
       odd exponent vanish from the level 1 on (reflection and half-period
       shift of the Hopf angles);
     - `mean_deriv`: the dyadic means of a Lipschitz derivative g' converge
       to g 1 - g 0 (mean value theorem; no Riemann integral is used);
     - `ET_cv`, `EP_cv`: the integration-by-parts identities of the angular
       and of the radial means, as sequences converging to 0;
     - `Mlim`, `Mlim_spec`: the Haar integral of a monomial as a function
       of the exponents;
     - `Mlim_rec`: (c + 1) M(a, b + 2, c, d) = (b + 1) M(a, b, c + 2, d)
       whenever a + b and c + d are even;
     - `moment_swap`: M(a, b, c, d) = M(a, c, b, d).

   Depends ONLY on Coq stdlib + the frozen challenge files
   + rg.dup_clustering + rg.product_measure + ym.su2_algebra
   + ym.su2_haar_grid + ym.su2_haar_grid_conj + ym.su2_haar_mean.
   Every statement below is proved in full; nothing is assumed.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2GaugeInvariance.
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import ym.su2_algebra.
Require Import ym.su2_haar_grid.
Require Import ym.su2_haar_grid_conj.
Require Import ym.su2_haar_mean.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeSU2Gauge ChallengeSU2GaugeInvariance.
Import DupClustering SU2Algebra SU2HaarGrid SU2HaarMean.
Open Scope R_scope.

Module SU2HaarMoments.

  (* =======================================================================
     1. Algebra of the means over an index range
     ======================================================================= *)

  Lemma mean_scal : forall N c (f : nat -> R),
    mean N (fun i => c * f i) = c * mean N f.
  Proof. intros N c f. unfold mean. rewrite rsum_scal. unfold Rdiv. ring. Qed.

  Lemma mean_scal_r : forall N c (f : nat -> R),
    mean N (fun i => f i * c) = mean N f * c.
  Proof. intros N c f. unfold mean. rewrite rsum_scal_r. unfold Rdiv. ring. Qed.

  Lemma mean_plus : forall N (f g : nat -> R),
    mean N (fun i => f i + g i) = mean N f + mean N g.
  Proof. intros N f g. unfold mean. rewrite rsum_plus. unfold Rdiv. ring. Qed.

  Lemma mean_minus : forall N (f g : nat -> R),
    mean N (fun i => f i - g i) = mean N f - mean N g.
  Proof. intros N f g. unfold mean. rewrite rsum_minus. unfold Rdiv. ring. Qed.

  (* reindexing by a permutation of the index range *)
  Lemma mean_perm : forall N (sigma : nat -> nat) (f : nat -> R),
    Permutation (map sigma (seq 0 N)) (seq 0 N) ->
    mean N (fun j => f (sigma j)) = mean N f.
  Proof.
    intros N sigma f H. unfold mean, Rdiv. apply Rmult_eq_compat_r.
    rewrite <- (rsum_map sigma (seq 0 N) f).
    apply ProductMeasure.rsum_perm. exact H.
  Qed.

  (* the mean of a product of functions of three separate indices *)
  Lemma mean3_factor : forall N (f g h : nat -> R),
    mean N (fun i => mean N (fun j => mean N (fun k => f i * g j * h k))) =
    mean N f * mean N g * mean N h.
  Proof.
    intros N f g h.
    transitivity (mean N (fun i => f i * (mean N g * mean N h))).
    - apply mean_ext. intros i _.
      transitivity (mean N (fun j => g j * (f i * mean N h))).
      + apply mean_ext. intros j _.
        rewrite (mean_scal N (f i * g j) h). ring.
      + rewrite (mean_scal_r N (f i * mean N h) g). ring.
    - rewrite (mean_scal_r N (mean N g * mean N h) f). ring.
  Qed.

  Lemma rsum_telescope : forall (h : nat -> R) N,
    rsum (seq 0 N) (fun i => h (S i) - h i) = h N - h 0%nat.
  Proof.
    intros h N. induction N as [| N IH].
    - cbn [seq]. rewrite rsum_nil. ring.
    - rewrite seq_S, rsum_app, rsum_cons, rsum_nil, IH.
      change (0 + N)%nat with N. ring.
  Qed.

  (* =======================================================================
     2. Sequences
     ======================================================================= *)

  Lemma cv_scal : forall (u : nat -> R) (c l : R),
    Un_cv u l -> Un_cv (fun n => c * u n) (c * l).
  Proof.
    intros u c l H.
    apply (CV_mult (fun _ => c) u c l); [| exact H].
    intros eps He. exists 0%nat. intros n _. unfold R_dist.
    replace (c - c) with 0 by ring. rewrite Rabs_R0. exact He.
  Qed.

  Definition bdd (w : nat -> R) : Prop := exists C : R, forall n, Rabs (w n) <= C.

  Lemma bdd_const : forall c, bdd (fun _ => c).
  Proof. intro c. exists (Rabs c). intros _. apply Rle_refl. Qed.

  Lemma bdd_mult : forall w w' : nat -> R,
    bdd w -> bdd w' -> bdd (fun n => w n * w' n).
  Proof.
    intros w w' [C HC] [C' HC']. exists (C * C'). intro n.
    rewrite Rabs_mult.
    apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply HC | apply HC'].
  Qed.

  (* bounded times null is null *)
  Lemma cv0_mult : forall w u : nat -> R,
    bdd w -> Un_cv u 0 -> Un_cv (fun n => w n * u n) 0.
  Proof.
    intros w u [C HC] Hu eps He.
    assert (HC0 : 0 <= C) by (eapply Rle_trans; [apply Rabs_pos | apply (HC 0%nat)]).
    destruct (Hu (eps / (C + 1))) as [n0 Hn0].
    { apply Rdiv_lt_0_compat; lra. }
    exists n0. intros n Hn. specialize (Hn0 n Hn). unfold R_dist in *.
    replace (w n * u n - 0) with (w n * u n) by ring.
    replace (u n - 0) with (u n) in Hn0 by ring.
    rewrite Rabs_mult.
    pose proof (HC n) as Hw. pose proof (Rabs_pos (w n)) as P1.
    pose proof (Rabs_pos (u n)) as P2.
    assert (E : eps = (C + 1) * (eps / (C + 1))) by (field; lra).
    assert (P3 : 0 < eps / (C + 1)) by (apply Rdiv_lt_0_compat; lra).
    rewrite E. apply Rle_lt_trans with (C * Rabs (u n)).
    - apply Rmult_le_compat_r; assumption.
    - nra.
  Qed.

  (* =======================================================================
     3. Bounded Lipschitz functions on [0,1]
     ======================================================================= *)

  Definition blip (f : R -> R) : Prop :=
    exists M L : R, 0 <= M /\ 0 <= L /\
      (forall x, 0 <= x <= 1 -> Rabs (f x) <= M) /\
      (forall x y, 0 <= x <= 1 -> 0 <= y <= 1 ->
         Rabs (f x - f y) <= L * Rabs (x - y)).

  Lemma blip_const : forall c : R, blip (fun _ => c).
  Proof.
    intro c. exists (Rabs c), 0. repeat split.
    - apply Rabs_pos.
    - lra.
    - intros x _. apply Rle_refl.
    - intros x y _ _. replace (c - c) with 0 by ring. rewrite Rabs_R0. lra.
  Qed.

  Lemma blip_id : blip (fun x => x).
  Proof.
    exists 1, 1. repeat split; try lra.
    - intros x Hx. apply Rabs_le. lra.
    - intros x y _ _. lra.
  Qed.

  Lemma blip_compl : blip (fun x => 1 - x).
  Proof.
    exists 1, 1. repeat split; try lra.
    - intros x Hx. apply Rabs_le. lra.
    - intros x y _ _. replace (1 - x - (1 - y)) with (- (x - y)) by ring.
      rewrite Rabs_Ropp. lra.
  Qed.

  Lemma blip_minus : forall f g : R -> R,
    blip f -> blip g -> blip (fun x => f x - g x).
  Proof.
    intros f g (M & L & HM & HL & Hb & Hl) (M' & L' & HM' & HL' & Hb' & Hl').
    exists (M + M'), (L + L'). repeat split; try lra.
    - intros x Hx. unfold Rminus.
      eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp.
      pose proof (Hb x Hx). pose proof (Hb' x Hx). lra.
    - intros x y Hx Hy.
      replace (f x - g x - (f y - g y)) with ((f x - f y) + - (g x - g y)) by ring.
      eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp.
      pose proof (Hl x y Hx Hy). pose proof (Hl' x y Hx Hy). lra.
  Qed.

  Lemma blip_mult : forall f g : R -> R,
    blip f -> blip g -> blip (fun x => f x * g x).
  Proof.
    intros f g (M & L & HM & HL & Hb & Hl) (M' & L' & HM' & HL' & Hb' & Hl').
    exists (M * M'), (M * L' + M' * L). repeat split.
    - apply Rmult_le_pos; assumption.
    - apply Rplus_le_le_0_compat; apply Rmult_le_pos; assumption.
    - intros x Hx. rewrite Rabs_mult.
      apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hb | apply Hb'];
        exact Hx.
    - intros x y Hx Hy.
      replace (f x * g x - f y * g y)
        with (f x * (g x - g y) + g y * (f x - f y)) by ring.
      eapply Rle_trans; [apply Rabs_triang |]. rewrite !Rabs_mult.
      pose proof (Hb x Hx) as B1. pose proof (Hb' y Hy) as B2.
      pose proof (Hl x y Hx Hy) as K1. pose proof (Hl' x y Hx Hy) as K2.
      pose proof (Rabs_pos (f x)) as P1. pose proof (Rabs_pos (g y)) as P2.
      pose proof (Rabs_pos (f x - f y)) as P3. pose proof (Rabs_pos (g x - g y)) as P4.
      pose proof (Rabs_pos (x - y)) as P5.
      assert (A1 : Rabs (f x) * Rabs (g x - g y) <= M * (L' * Rabs (x - y))).
      { apply Rmult_le_compat; assumption. }
      assert (A2 : Rabs (g y) * Rabs (f x - f y) <= M' * (L * Rabs (x - y))).
      { apply Rmult_le_compat; assumption. }
      lra.
  Qed.

  Lemma blip_pow : forall (f : R -> R) k, blip f -> blip (fun x => f x ^ k).
  Proof.
    intros f k Hf. induction k as [| k IH].
    - exact (blip_const 1).
    - exact (blip_mult f (fun x => f x ^ k) Hf IH).
  Qed.

  (* =======================================================================
     4. The dyadic means of a Lipschitz derivative
     ======================================================================= *)

  Lemma mean_deriv : forall g g' : R -> R,
    (forall x, derivable_pt_lim g x (g' x)) -> blip g' ->
    Un_cv (fun n => mean (2 ^ n) (fun i => g' (INR i / INR (2 ^ n)))) (g 1 - g 0).
  Proof.
    intros g g' Hd (M & L & HM & HL & _ & Hlip).
    assert (step : forall N, (0 < N)%nat ->
              Rabs (mean N (fun i => g' (INR i / INR N)) - (g 1 - g 0)) <= L * / INR N).
    { intros N HN.
      assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
      assert (HiN : 0 < / INR N) by (apply Rinv_0_lt_compat; exact HN').
      assert (E : g 1 - g 0 =
                  mean N (fun i => INR N * (g (INR (S i) / INR N) - g (INR i / INR N)))).
      { unfold mean. rewrite rsum_scal.
        rewrite (rsum_telescope (fun i => g (INR i / INR N)) N).
        replace (INR N / INR N) with 1 by (field; lra).
        replace (INR 0 / INR N) with 0 by (cbn [INR]; field; lra).
        field. lra. }
      rewrite E. apply mean_close; [exact HN |]. intros i Hi.
      assert (Hi0 : 0 <= INR i) by apply pos_INR.
      assert (Hi1 : INR i + 1 <= INR N).
      { rewrite <- S_INR. apply le_INR. lia. }
      set (a := INR i / INR N). set (b := INR (S i) / INR N).
      assert (Hba : b - a = / INR N).
      { unfold a, b. rewrite S_INR. field. lra. }
      assert (Ha0 : 0 <= a).
      { unfold a, Rdiv. apply Rmult_le_pos; lra. }
      assert (Hb1 : b <= 1).
      { unfold b. rewrite S_INR. apply Rmult_le_reg_r with (INR N); [exact HN' |].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra. }
      assert (Hab : a < b) by lra.
      destruct (MVT_cor2 g g' a b Hab) as [c [Hc [Hc1 Hc2]]].
      { intros c _. apply Hd. }
      rewrite Hc, Hba.
      replace (g' a - INR N * (g' c * / INR N)) with (g' a - g' c) by (field; lra).
      eapply Rle_trans; [apply Hlip; lra |].
      apply Rmult_le_compat_l; [exact HL |].
      apply Rabs_le. lra. }
    intros eps He.
    destruct (pow2_inv_small (eps / (L + 1))) as [n0 Hn0].
    { apply Rdiv_lt_0_compat; lra. }
    exists n0. intros n Hn. unfold R_dist.
    eapply Rle_lt_trans; [apply step; apply pow2_pos |].
    assert (Hn0' : / INR (2 ^ n) < eps / (L + 1)) by (apply Hn0; lia).
    assert (Hpos : 0 < / INR (2 ^ n)).
    { apply Rinv_0_lt_compat. apply lt_0_INR. apply pow2_pos. }
    assert (E : eps = (L + 1) * (eps / (L + 1))) by (field; lra).
    rewrite E. nra.
  Qed.

  (* =======================================================================
     5. Derivatives
     ======================================================================= *)

  Lemma dl_eq : forall (f : R -> R) (x l l' : R),
    l = l' -> derivable_pt_lim f x l -> derivable_pt_lim f x l'.
  Proof. intros f x l l' E H. rewrite <- E. exact H. Qed.

  Lemma dl_comp : forall (f g : R -> R) (x l1 l2 : R),
    derivable_pt_lim f x l1 -> derivable_pt_lim g (f x) l2 ->
    derivable_pt_lim (fun y => g (f y)) x (l2 * l1).
  Proof. intros f g x l1 l2 H1 H2. exact (derivable_pt_lim_comp f g x l1 l2 H1 H2). Qed.

  Lemma dl_mult : forall (f g : R -> R) (x l1 l2 : R),
    derivable_pt_lim f x l1 -> derivable_pt_lim g x l2 ->
    derivable_pt_lim (fun y => f y * g y) x (l1 * g x + f x * l2).
  Proof. intros f g x l1 l2 H1 H2. exact (derivable_pt_lim_mult f g x l1 l2 H1 H2). Qed.

  Lemma dl_pow : forall (f : R -> R) (x l : R) (n : nat),
    derivable_pt_lim f x l ->
    derivable_pt_lim (fun y => f y ^ S n) x (INR (S n) * f x ^ n * l).
  Proof.
    intros f x l n H.
    apply (dl_comp f (fun y => y ^ S n) x l (INR (S n) * f x ^ n)); [exact H |].
    exact (derivable_pt_lim_pow (f x) (S n)).
  Qed.

  Lemma dl_lin : forall c x : R, derivable_pt_lim (fun y => c * y) x c.
  Proof.
    intros c x. apply (dl_eq _ x (c * 1)); [ring |].
    exact (derivable_pt_lim_scal id c x 1 (derivable_pt_lim_id x)).
  Qed.

  Lemma dl_compl : forall x : R, derivable_pt_lim (fun y => 1 - y) x (-1).
  Proof.
    intro x. apply (dl_eq _ x (0 - 1)); [ring |].
    exact (derivable_pt_lim_minus (fct_cte 1) id x 0 1
             (derivable_pt_lim_const 1 x) (derivable_pt_lim_id x)).
  Qed.

  (* =======================================================================
     6. The angular means
     ======================================================================= *)

  Definition cs (x : R) : R := cos (2 * PI * x).
  Definition sn (x : R) : R := sin (2 * PI * x).

  Definition Tm (N a b : nat) : R :=
    mean N (fun j => cs (INR j / INR N) ^ a * sn (INR j / INR N) ^ b).

  Lemma cs_bounds : forall x, -1 <= cs x <= 1.
  Proof. intro x. apply COS_bound. Qed.

  Lemma sn_bounds : forall x, -1 <= sn x <= 1.
  Proof. intro x. apply SIN_bound. Qed.

  Lemma pow_bounds1 : forall x k, -1 <= x <= 1 -> -1 <= x ^ k <= 1.
  Proof.
    intros x k Hx. induction k as [| k IH]; cbn [pow]; [lra | nra].
  Qed.

  Lemma Tm_bounds : forall N a b, (0 < N)%nat -> -1 <= Tm N a b <= 1.
  Proof.
    intros N a b HN. unfold Tm. apply mean_bounds; [exact HN |]. intros j _.
    pose proof (pow_bounds1 _ a (cs_bounds (INR j / INR N))).
    pose proof (pow_bounds1 _ b (sn_bounds (INR j / INR N))). nra.
  Qed.

  Lemma bdd_Tm : forall a b, bdd (fun n => Tm (2 ^ n) a b).
  Proof.
    intros a b. exists 1. intro n. apply Rabs_le.
    apply Tm_bounds. apply pow2_pos.
  Qed.

  (* cos^2 + sin^2 = 1 *)
  Lemma Tm_pyth : forall N a b,
    Tm N (S (S a)) b + Tm N a (S (S b)) = Tm N a b.
  Proof.
    intros N a b. unfold Tm. rewrite <- mean_plus. apply mean_ext. intros j _.
    pose proof (sin2_cos2 (2 * PI * (INR j / INR N))) as H. unfold Rsqr in H.
    fold (sn (INR j / INR N)) in H. fold (cs (INR j / INR N)) in H.
    cbn [pow].
    transitivity (cs (INR j / INR N) ^ a * sn (INR j / INR N) ^ b
                  * (sn (INR j / INR N) * sn (INR j / INR N)
                     + cs (INR j / INR N) * cs (INR j / INR N))); [ring |].
    rewrite H. ring.
  Qed.

  Lemma pow_neg1_odd : forall k, Nat.odd k = true -> (-1) ^ k = -1.
  Proof.
    intros k H. apply Nat.odd_spec in H. destruct H as [m ->].
    replace (2 * m + 1)%nat with (S (2 * m)) by lia. apply pow_1_odd.
  Qed.

  Lemma pow_opp : forall x k, (- x) ^ k = (-1) ^ k * x ^ k.
  Proof.
    intros x k. replace (- x) with (-1 * x) by ring. apply Rpow_mult_distr.
  Qed.

  (* reflection of the angle *)
  Lemma Tm_reflect : forall N a b, (0 < N)%nat ->
    Tm N a b = (-1) ^ b * Tm N a b.
  Proof.
    intros N a b HN. unfold Tm at 1.
    rewrite <- (mean_perm N (SU2HaarGridConj.rho N)
                 (fun j => cs (INR j / INR N) ^ a * sn (INR j / INR N) ^ b)
                 (SU2HaarGridConj.rho_perm N)).
    unfold Tm. rewrite <- mean_scal. apply mean_ext. intros j Hj.
    destruct (SU2HaarGridConj.trig_reflect (INR j / INR N)
                (INR (SU2HaarGridConj.rho N j) / INR N)
                (SU2HaarGridConj.rho_frac N j Hj)) as [Hc Hs].
    unfold cs, sn. rewrite Hc, Hs, pow_opp. ring.
  Qed.

  (* half-period shift of the angle *)
  Lemma Tm_hshift : forall H a b, (0 < H)%nat ->
    Tm (H + H) a b = (-1) ^ (a + b) * Tm (H + H) a b.
  Proof.
    intros H a b HH. unfold Tm at 1.
    rewrite <- (mean_perm (H + H) (hshift H)
                 (fun j => cs (INR j / INR (H + H)) ^ a * sn (INR j / INR (H + H)) ^ b)
                 (hshift_perm H)).
    unfold Tm. rewrite <- mean_scal. apply mean_ext. intros j Hj.
    destruct (trig_half_shift (INR j / INR (H + H))
                (INR (hshift H j) / INR (H + H))
                (hshift_frac H j HH)) as [Hc Hs].
    unfold cs, sn. rewrite Hc, Hs, !pow_opp, pow_add. ring.
  Qed.

  (* an odd exponent kills the angular mean from the level 1 on *)
  Lemma Tm_zero : forall n a b, Nat.even a && Nat.even b = false ->
    Tm (2 ^ S n) a b = 0.
  Proof.
    intros n a b H.
    assert (HN : (0 < 2 ^ S n)%nat) by apply pow2_pos.
    destruct (Nat.odd b) eqn:Hb.
    - pose proof (Tm_reflect (2 ^ S n) a b HN) as E.
      rewrite (pow_neg1_odd b Hb) in E. lra.
    - assert (Hab : Nat.odd (a + b) = true).
      { rewrite Nat.odd_add. unfold Nat.odd in *.
        destruct (Nat.even a), (Nat.even b); cbn in *; congruence. }
      assert (E2 : (2 ^ S n = 2 ^ n + 2 ^ n)%nat)
        by (rewrite Nat.pow_succ_r'; lia).
      rewrite E2.
      pose proof (Tm_hshift (2 ^ n) a b (pow2_pos n)) as E.
      rewrite (pow_neg1_odd (a + b) Hab) in E. lra.
  Qed.

  (* the integration-by-parts identity of the angular means *)
  Definition gT (a b : nat) (x : R) : R := cs x ^ S a * sn x ^ S b.

  Definition gT' (a b : nat) (x : R) : R :=
    2 * PI * (INR (S b) * (cs x ^ S (S a) * sn x ^ b)
              - INR (S a) * (cs x ^ a * sn x ^ S (S b))).

  Lemma cs_deriv : forall x, derivable_pt_lim cs x (- (2 * PI) * sn x).
  Proof.
    intro x. unfold cs, sn.
    apply (dl_eq _ x (- sin (2 * PI * x) * (2 * PI))); [ring |].
    apply (dl_comp (fun y => 2 * PI * y) cos x (2 * PI) (- sin (2 * PI * x))).
    - apply dl_lin.
    - apply derivable_pt_lim_cos.
  Qed.

  Lemma sn_deriv : forall x, derivable_pt_lim sn x (2 * PI * cs x).
  Proof.
    intro x. unfold cs, sn.
    apply (dl_eq _ x (cos (2 * PI * x) * (2 * PI))); [ring |].
    apply (dl_comp (fun y => 2 * PI * y) sin x (2 * PI) (cos (2 * PI * x))).
    - apply dl_lin.
    - apply derivable_pt_lim_sin.
  Qed.

  Lemma gT_deriv : forall a b x, derivable_pt_lim (gT a b) x (gT' a b x).
  Proof.
    intros a b x. unfold gT, gT'.
    apply (dl_eq _ x
             (INR (S a) * cs x ^ a * (- (2 * PI) * sn x) * sn x ^ S b
              + cs x ^ S a * (INR (S b) * sn x ^ b * (2 * PI * cs x)))).
    - cbn [pow]. ring.
    - apply (dl_mult (fun y => cs y ^ S a) (fun y => sn y ^ S b)).
      + apply dl_pow. apply cs_deriv.
      + apply dl_pow. apply sn_deriv.
  Qed.

  Lemma blip_cs : blip cs.
  Proof.
    pose proof PI_RGT_0 as HPI.
    exists 1, (2 * PI). repeat split; try lra.
    - intros x _. apply Rabs_le. apply cs_bounds.
    - intros x y _ _. unfold cs.
      eapply Rle_trans; [apply cos_lip |].
      replace (2 * PI * x - 2 * PI * y) with (2 * PI * (x - y)) by ring.
      rewrite Rabs_mult, (Rabs_pos_eq (2 * PI)) by lra. lra.
  Qed.

  Lemma blip_sn : blip sn.
  Proof.
    pose proof PI_RGT_0 as HPI.
    exists 1, (2 * PI). repeat split; try lra.
    - intros x _. apply Rabs_le. apply sn_bounds.
    - intros x y _ _. unfold sn.
      eapply Rle_trans; [apply sin_lip |].
      replace (2 * PI * x - 2 * PI * y) with (2 * PI * (x - y)) by ring.
      rewrite Rabs_mult, (Rabs_pos_eq (2 * PI)) by lra. lra.
  Qed.

  Lemma blip_gT' : forall a b, blip (gT' a b).
  Proof.
    intros a b. unfold gT'.
    apply (blip_mult (fun _ => 2 * PI)
             (fun x => INR (S b) * (cs x ^ S (S a) * sn x ^ b)
                       - INR (S a) * (cs x ^ a * sn x ^ S (S b)))).
    - apply blip_const.
    - apply (blip_minus (fun x => INR (S b) * (cs x ^ S (S a) * sn x ^ b))
                        (fun x => INR (S a) * (cs x ^ a * sn x ^ S (S b)))).
      + apply (blip_mult (fun _ => INR (S b)) (fun x => cs x ^ S (S a) * sn x ^ b)).
        * apply blip_const.
        * apply (blip_mult (fun x => cs x ^ S (S a)) (fun x => sn x ^ b)).
          -- apply blip_pow. exact blip_cs.
          -- apply blip_pow. exact blip_sn.
      + apply (blip_mult (fun _ => INR (S a)) (fun x => cs x ^ a * sn x ^ S (S b))).
        * apply blip_const.
        * apply (blip_mult (fun x => cs x ^ a) (fun x => sn x ^ S (S b))).
          -- apply blip_pow. exact blip_cs.
          -- apply blip_pow. exact blip_sn.
  Qed.

  Definition ET (n a b : nat) : R :=
    INR (S b) * Tm (2 ^ n) (S (S a)) b - INR (S a) * Tm (2 ^ n) a (S (S b)).

  Lemma mean_gT' : forall N a b,
    mean N (fun i => gT' a b (INR i / INR N)) =
    2 * PI * (INR (S b) * Tm N (S (S a)) b - INR (S a) * Tm N a (S (S b))).
  Proof.
    intros N a b. unfold gT', Tm.
    rewrite <- !mean_scal, <- mean_minus, <- mean_scal. reflexivity.
  Qed.

  Lemma ET_cv : forall a b, Un_cv (fun n => ET n a b) 0.
  Proof.
    intros a b.
    pose proof PI_RGT_0 as HPI.
    pose proof (mean_deriv (gT a b) (gT' a b) (gT_deriv a b) (blip_gT' a b)) as H.
    assert (E0 : gT a b 1 - gT a b 0 = 0).
    { unfold gT, sn. replace (2 * PI * 1) with (2 * PI) by ring.
      rewrite Rmult_0_r, sin_2PI, sin_0. cbn [pow]. ring. }
    rewrite E0 in H.
    apply (cv_scal _ (/ (2 * PI))) in H.
    replace (/ (2 * PI) * 0) with 0 in H by ring.
    apply (cv_ext0 _ _ _ ) with (2 := H).
    intro n. rewrite mean_gT'. unfold ET. field. lra.
  Qed.

  (* =======================================================================
     7. The radial means
     ======================================================================= *)

  Definition Pm (N p q : nat) : R :=
    mean N (fun i => (1 - INR i / INR N) ^ p * (INR i / INR N) ^ q).

  Definition Sm (N p q : nat) : R :=
    mean N (fun i => sqrt (1 - INR i / INR N) ^ p * sqrt (INR i / INR N) ^ q).

  Lemma sqrt_pow_even : forall x p, 0 <= x -> sqrt x ^ (2 * p) = x ^ p.
  Proof.
    intros x p Hx. rewrite pow_mult, pow2_sqrt by exact Hx. reflexivity.
  Qed.

  Lemma Sm_even : forall N p q, Sm N (2 * p) (2 * q) = Pm N p q.
  Proof.
    intros N p q. unfold Sm, Pm. apply mean_ext. intros i Hi.
    pose proof (frac_range N i Hi) as Hr.
    rewrite !sqrt_pow_even by lra. reflexivity.
  Qed.

  Lemma pow_bounds01 : forall x k, 0 <= x <= 1 -> 0 <= x ^ k <= 1.
  Proof.
    intros x k Hx. induction k as [| k IH]; cbn [pow]; [lra | nra].
  Qed.

  Lemma Pm_bounds : forall N p q, (0 < N)%nat -> 0 <= Pm N p q <= 1.
  Proof.
    intros N p q HN. unfold Pm. apply mean_bounds; [exact HN |]. intros i Hi.
    pose proof (frac_range N i Hi) as Hr.
    assert (Hr' : 0 <= 1 - INR i / INR N <= 1) by lra.
    pose proof (pow_bounds01 _ p Hr'). pose proof (pow_bounds01 _ q Hr). nra.
  Qed.

  Lemma bdd_Pm : forall p q, bdd (fun n => Pm (2 ^ n) p q).
  Proof.
    intros p q. exists 1. intro n. apply Rabs_le.
    pose proof (Pm_bounds (2 ^ n) p q (pow2_pos n)). lra.
  Qed.

  Definition gP (p q : nat) (s : R) : R := (1 - s) ^ S p * s ^ S q.

  Definition gP' (p q : nat) (s : R) : R :=
    INR (S q) * ((1 - s) ^ S p * s ^ q) - INR (S p) * ((1 - s) ^ p * s ^ S q).

  Lemma gP_deriv : forall p q s, derivable_pt_lim (gP p q) s (gP' p q s).
  Proof.
    intros p q s. unfold gP, gP'.
    apply (dl_eq _ s
             (INR (S p) * (1 - s) ^ p * (-1) * s ^ S q
              + (1 - s) ^ S p * (INR (S q) * s ^ q * 1))).
    - cbn [pow]. ring.
    - apply (dl_mult (fun y => (1 - y) ^ S p) (fun y => y ^ S q)).
      + apply (dl_pow (fun y => 1 - y)). apply dl_compl.
      + apply (dl_pow (fun y => y)). exact (derivable_pt_lim_id s).
  Qed.

  Lemma blip_gP' : forall p q, blip (gP' p q).
  Proof.
    intros p q. unfold gP'.
    apply (blip_minus (fun s => INR (S q) * ((1 - s) ^ S p * s ^ q))
                      (fun s => INR (S p) * ((1 - s) ^ p * s ^ S q))).
    - apply (blip_mult (fun _ => INR (S q)) (fun s => (1 - s) ^ S p * s ^ q)).
      + apply blip_const.
      + apply (blip_mult (fun s => (1 - s) ^ S p) (fun s => s ^ q)).
        * apply (blip_pow (fun s => 1 - s)). exact blip_compl.
        * apply (blip_pow (fun s => s)). exact blip_id.
    - apply (blip_mult (fun _ => INR (S p)) (fun s => (1 - s) ^ p * s ^ S q)).
      + apply blip_const.
      + apply (blip_mult (fun s => (1 - s) ^ p) (fun s => s ^ S q)).
        * apply (blip_pow (fun s => 1 - s)). exact blip_compl.
        * apply (blip_pow (fun s => s)). exact blip_id.
  Qed.

  Definition EP (n p q : nat) : R :=
    INR (S q) * Pm (2 ^ n) (S p) q - INR (S p) * Pm (2 ^ n) p (S q).

  Lemma mean_gP' : forall N p q,
    mean N (fun i => gP' p q (INR i / INR N)) =
    INR (S q) * Pm N (S p) q - INR (S p) * Pm N p (S q).
  Proof.
    intros N p q. unfold gP', Pm.
    rewrite <- !mean_scal, <- mean_minus. reflexivity.
  Qed.

  Lemma EP_cv : forall p q, Un_cv (fun n => EP n p q) 0.
  Proof.
    intros p q.
    pose proof (mean_deriv (gP p q) (gP' p q) (gP_deriv p q) (blip_gP' p q)) as H.
    assert (E0 : gP p q 1 - gP p q 0 = 0).
    { unfold gP. cbn [pow]. ring. }
    rewrite E0 in H.
    apply (cv_ext0 _ _ _ ) with (2 := H).
    intro n. rewrite mean_gP'. reflexivity.
  Qed.

  (* =======================================================================
     8. Factorization of the grid averages of the monomials
     ======================================================================= *)

  Lemma mono_gpt : forall N a b c d i j k,
    mono a b c d (gpt N i j k) =
    sqrt (1 - INR i / INR N) ^ (a + b) * sqrt (INR i / INR N) ^ (c + d)
    * (cs (INR j / INR N) ^ a * sn (INR j / INR N) ^ b)
    * (cs (INR k / INR N) ^ c * sn (INR k / INR N) ^ d).
  Proof.
    intros N a b c d i j k. unfold mono, gpt, su2_hopf, cs, sn.
    cbn [qr qi qj qk]. rewrite !Rpow_mult_distr, !pow_add. ring.
  Qed.

  Lemma gmean_factor : forall n a b c d,
    gmean n (mono a b c d) =
    Sm (2 ^ n) (a + b) (c + d) * Tm (2 ^ n) a b * Tm (2 ^ n) c d.
  Proof.
    intros n a b c d. rewrite gmean_mean. unfold Sm, Tm.
    rewrite <- mean3_factor.
    apply mean_ext. intros i _. apply mean_ext. intros j _.
    apply mean_ext. intros k _. apply mono_gpt.
  Qed.

  Definition all_even (a b c d : nat) : bool :=
    Nat.even a && Nat.even b && (Nat.even c && Nat.even d).

  Lemma gmean_mono_odd : forall n a b c d, all_even a b c d = false ->
    gmean (S n) (mono a b c d) = 0.
  Proof.
    intros n a b c d H. rewrite gmean_factor. unfold all_even in H.
    apply andb_false_iff in H. destruct H as [H | H].
    - rewrite (Tm_zero n a b H). ring.
    - rewrite (Tm_zero n c d H). ring.
  Qed.

  Lemma haar_mono_odd : forall a b c d v, all_even a b c d = false ->
    haar_lim (mono a b c d) v -> v = 0.
  Proof.
    intros a b c d v H Hv. apply (haar_unique (mono a b c d)); [exact Hv |].
    intros eps He. exists 1%nat. intros n Hn.
    destruct n as [| n]; [lia |].
    rewrite (gmean_mono_odd n a b c d H). unfold R_dist.
    replace (0 - 0) with 0 by ring. rewrite Rabs_R0. exact He.
  Qed.

  (* =======================================================================
     9. The moments as a function of the exponents
     ======================================================================= *)

  Lemma gmean_cauchy : forall h : Quat -> R, fn_bc h ->
    Cauchy_crit (fun n => gmean n h).
  Proof.
    intros h Hh. destruct (haar_exists h Hh) as [v Hv].
    apply CV_Cauchy. exists v. exact Hv.
  Qed.

  Definition Mlim (a b c d : nat) : R :=
    proj1_sig (R_complete (fun n => gmean n (mono a b c d))
                 (gmean_cauchy (mono a b c d) (fn_bc_mono a b c d))).

  Lemma Mlim_spec : forall a b c d, haar_lim (mono a b c d) (Mlim a b c d).
  Proof.
    intros a b c d. unfold Mlim.
    exact (proj2_sig (R_complete (fun n => gmean n (mono a b c d))
                        (gmean_cauchy (mono a b c d) (fn_bc_mono a b c d)))).
  Qed.

  Lemma Mlim_eq : forall a b c d v, haar_lim (mono a b c d) v -> v = Mlim a b c d.
  Proof.
    intros a b c d v H. exact (haar_unique _ _ _ H (Mlim_spec a b c d)).
  Qed.

  (* the recursion: moving two units of exponent from the second to the
     third coordinate *)
  Lemma Mlim_rec : forall a b c d P Q : nat,
    (a + b = 2 * P)%nat -> (c + d = 2 * Q)%nat ->
    INR (S c) * Mlim a (S (S b)) c d = INR (S b) * Mlim a b (S (S c)) d.
  Proof.
    intros a b c d P Q HP HQ.
    assert (HPr : INR a + INR b = 2 * INR P).
    { rewrite <- plus_INR, HP, mult_INR. cbn [INR]. ring. }
    assert (HQr : INR c + INR d = 2 * INR Q).
    { rewrite <- plus_INR, HQ, mult_INR. cbn [INR]. ring. }
    set (K := 2 * INR (S P) * INR (S Q)).
    assert (HK : 0 < K).
    { unfold K. rewrite !S_INR. pose proof (pos_INR P). pose proof (pos_INR Q). nra. }
    set (Z := fun n => INR (S c) * gmean n (mono a (S (S b)) c d)
                       - INR (S b) * gmean n (mono a b (S (S c)) d)).
    assert (HZ : Un_cv Z (INR (S c) * Mlim a (S (S b)) c d
                          - INR (S b) * Mlim a b (S (S c)) d)).
    { unfold Z. apply CV_minus.
      - apply cv_scal. exact (Mlim_spec a (S (S b)) c d).
      - apply cv_scal. exact (Mlim_spec a b (S (S c)) d). }
    assert (HKZ : Un_cv (fun n => K * Z n) 0).
    { set (w1 := fun n => INR (S b) * INR (S c) * Tm (2 ^ n) a b * Tm (2 ^ n) c d).
      set (w2 := fun n => INR (S c) * INR (S Q) * Pm (2 ^ n) (S P) Q * Tm (2 ^ n) c d).
      set (w3 := fun n => INR (S b) * INR (S P) * Pm (2 ^ n) P (S Q) * Tm (2 ^ n) a b).
      assert (B1 : bdd w1).
      { unfold w1.
        apply (bdd_mult (fun n => INR (S b) * INR (S c) * Tm (2 ^ n) a b)
                        (fun n => Tm (2 ^ n) c d)); [| apply bdd_Tm].
        apply (bdd_mult (fun _ => INR (S b) * INR (S c)) (fun n => Tm (2 ^ n) a b));
          [apply bdd_const | apply bdd_Tm]. }
      assert (B2 : bdd w2).
      { unfold w2.
        apply (bdd_mult (fun n => INR (S c) * INR (S Q) * Pm (2 ^ n) (S P) Q)
                        (fun n => Tm (2 ^ n) c d)); [| apply bdd_Tm].
        apply (bdd_mult (fun _ => INR (S c) * INR (S Q)) (fun n => Pm (2 ^ n) (S P) Q));
          [apply bdd_const | apply bdd_Pm]. }
      assert (B3 : bdd w3).
      { unfold w3.
        apply (bdd_mult (fun n => INR (S b) * INR (S P) * Pm (2 ^ n) P (S Q))
                        (fun n => Tm (2 ^ n) a b)); [| apply bdd_Tm].
        apply (bdd_mult (fun _ => INR (S b) * INR (S P)) (fun n => Pm (2 ^ n) P (S Q)));
          [apply bdd_const | apply bdd_Pm]. }
      pose proof (cv0_mult w1 (fun n => EP n P Q) B1 (EP_cv P Q)) as C1.
      pose proof (cv0_mult w2 (fun n => ET n a b) B2 (ET_cv a b)) as C2.
      pose proof (cv0_mult w3 (fun n => ET n c d) B3 (ET_cv c d)) as C3.
      pose proof (CV_minus _ _ _ _ (CV_minus _ _ _ _ C1 C2) C3) as C.
      replace (0 - 0 - 0) with 0 in C by ring.
      apply (cv_ext0 _ _ _ ) with (2 := C).
      intro n. unfold Z, w1, w2, w3, ET, EP, K.
      rewrite !gmean_factor.
      replace (a + S (S b))%nat with (2 * S P)%nat by lia.
      replace (c + d)%nat with (2 * Q)%nat by lia.
      replace (a + b)%nat with (2 * P)%nat by lia.
      replace (S (S c) + d)%nat with (2 * S Q)%nat by lia.
      rewrite !Sm_even.
      rewrite <- (Tm_pyth (2 ^ n) a b), <- (Tm_pyth (2 ^ n) c d).
      rewrite !S_INR.
      assert (Ha : INR a = 2 * INR P - INR b) by lra.
      assert (Hd : INR d = 2 * INR Q - INR c) by lra.
      rewrite Ha, Hd. ring. }
    pose proof (cv_scal Z K _ HZ) as HKZ'.
    pose proof (UL_sequence _ _ _ HKZ' HKZ) as E.
    apply Rmult_integral in E. destruct E as [E | E]; lra.
  Qed.

  (* =======================================================================
     10. Even exponents: symmetry in the two middle exponents
     ======================================================================= *)

  Lemma Mlim_rec_even : forall i j k l : nat,
    (2 * INR k + 1) * Mlim (2 * i) (2 * S j) (2 * k) (2 * l) =
    (2 * INR j + 1) * Mlim (2 * i) (2 * j) (2 * S k) (2 * l).
  Proof.
    intros i j k l.
    pose proof (Mlim_rec (2 * i) (2 * j) (2 * k) (2 * l) (i + j) (k + l)
                  ltac:(lia) ltac:(lia)) as H.
    replace (S (S (2 * j))) with (2 * S j)%nat in H by lia.
    replace (S (S (2 * k))) with (2 * S k)%nat in H by lia.
    rewrite !S_INR, !mult_INR in H. cbn [INR] in H.
    replace (2 * INR k + 1) with ((1 + 1) * INR k + 1) by ring.
    replace (2 * INR j + 1) with ((1 + 1) * INR j + 1) by ring.
    exact H.
  Qed.

  (* the product of the first j odd numbers *)
  Fixpoint dfact (j : nat) : R :=
    match j with
    | O => 1
    | S j' => (2 * INR j' + 1) * dfact j'
    end.

  Lemma dfact_pos : forall j, 0 < dfact j.
  Proof.
    induction j as [| j IH]; cbn [dfact]; [lra |].
    apply Rmult_lt_0_compat; [| exact IH]. pose proof (pos_INR j). lra.
  Qed.

  Lemma Mlim_shift : forall i l j k : nat,
    Mlim (2 * i) (2 * j) (2 * k) (2 * l) * dfact (j + k) =
    Mlim (2 * i) (2 * 0) (2 * (j + k)) (2 * l) * dfact j * dfact k.
  Proof.
    intros i l j. induction j as [| j IH]; intro k.
    - cbn [dfact Nat.add]. ring.
    - pose proof (IH (S k)) as H1.
      pose proof (Mlim_rec_even i j k l) as H2.
      replace (j + S k)%nat with (S j + k)%nat in H1 by lia.
      cbn [dfact] in H1. cbn [dfact].
      pose proof (pos_INR k) as Pk. pose proof (pos_INR j) as Pj.
      apply Rmult_eq_reg_l with (2 * INR k + 1); [| lra].
      transitivity ((2 * INR k + 1) * Mlim (2 * i) (2 * S j) (2 * k) (2 * l)
                    * dfact (S j + k)); [ring |].
      rewrite H2.
      transitivity ((2 * INR j + 1)
                    * (Mlim (2 * i) (2 * j) (2 * S k) (2 * l) * dfact (S j + k)));
        [ring |].
      rewrite H1. ring.
  Qed.

  Lemma Mlim_swap_even : forall i j k l : nat,
    Mlim (2 * i) (2 * j) (2 * k) (2 * l) = Mlim (2 * i) (2 * k) (2 * j) (2 * l).
  Proof.
    intros i j k l.
    pose proof (Mlim_shift i l j k) as H1.
    pose proof (Mlim_shift i l k j) as H2.
    replace (k + j)%nat with (j + k)%nat in H2 by lia.
    pose proof (dfact_pos (j + k)) as HD.
    apply Rmult_eq_reg_r with (dfact (j + k)); [| lra].
    rewrite H1, H2. ring.
  Qed.

  (* =======================================================================
     11. The theorem
     ======================================================================= *)

  Lemma all_even_swap : forall a b c d, all_even a c b d = all_even a b c d.
  Proof.
    intros a b c d. unfold all_even.
    destruct (Nat.even a), (Nat.even b), (Nat.even c), (Nat.even d); reflexivity.
  Qed.

  Theorem moment_swap : forall (a b c d : nat) (v v' : R),
    haar_lim (mono a b c d) v -> haar_lim (mono a c b d) v' -> v = v'.
  Proof.
    intros a b c d v v' Hv Hv'.
    destruct (all_even a b c d) eqn:He.
    - unfold all_even in He.
      apply andb_true_iff in He. destruct He as [H1 H2].
      apply andb_true_iff in H1. destruct H1 as [Ha Hb].
      apply andb_true_iff in H2. destruct H2 as [Hc Hd].
      apply Nat.even_spec in Ha. destruct Ha as [i ->].
      apply Nat.even_spec in Hb. destruct Hb as [j ->].
      apply Nat.even_spec in Hc. destruct Hc as [k ->].
      apply Nat.even_spec in Hd. destruct Hd as [l ->].
      rewrite (Mlim_eq _ _ _ _ v Hv), (Mlim_eq _ _ _ _ v' Hv').
      apply Mlim_swap_even.
    - rewrite (haar_mono_odd a b c d v He Hv).
      rewrite <- (all_even_swap a b c d) in He.
      rewrite (haar_mono_odd a c b d v' He Hv'). reflexivity.
  Qed.

End SU2HaarMoments.
