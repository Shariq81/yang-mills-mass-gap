(* =========================================================================
   ym/su2_haar_orbit.v

   Two elementary facts about S^3 = SU(2) and its dyadic Hopf grids, used
   to identify the limit of the grid averages:

     - `polar_angle`, `polar_coords`: every point of the unit circle is
       (cos t, sin t), and every point of the plane is r (cos t, sin t)
       with r >= 0;
     - `unit_orbit`: every unit quaternion is obtained from 1 by the
       coordinate-plane rotations `rot01`, `rot23` and the exchange
       `swap12` of ym/su2_haar_mean.v:
         q = rot01 t1 (rot23 t2 (swap12 (rot01 t3 1)));
     - `mean_first_block`, `frac_small`, `gpt_near_one`: the grid points
       whose three indices lie in the first blocks of the index range are
       close to 1 = su2_hopf 0 0 0;
     - `cap_positive`: for every rho > 0 there are c > 0 and n0 such that
       the grid average of level n >= n0 of every function that is >= 0 on
       SU(2) and >= 1 on the rho-neighbourhood of 1 is at least c
       (a neighbourhood of 1 carries a positive fraction of every fine
       grid).

   Dependencies: the Coq standard library (Reals, in particular `acos`),
   verification/ChallengeSU2Gauge.v, verification/ChallengeSU2GaugeInvariance.v,
   rg/dup_clustering.v (`rsum`), ym/su2_algebra.v (`quat_eq`),
   ym/su2_continuity.v (`close_mono`), ym/su2_haar_grid.v (`mean`, `gpt`,
   `hopf_close`), ym/su2_haar_mean.v (`gmean_mean`, `rot01`, `rot23`,
   `swap12`).

   No unproved declarations of any kind.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2GaugeInvariance.
Require Import rg.dup_clustering.
Require Import ym.su2_algebra.
Require Import ym.su2_continuity.
Require Import ym.su2_haar_grid.
Require Import ym.su2_haar_mean.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeSU2Gauge ChallengeSU2GaugeInvariance.
Import DupClustering SU2Algebra SU2Continuity SU2HaarGrid SU2HaarMean.
Open Scope R_scope.

Module SU2HaarOrbit.

  (* =======================================================================
     1. Polar coordinates
     ======================================================================= *)

  (* every point of the unit circle is (cos t, sin t) *)
  Lemma polar_angle : forall x y : R, x * x + y * y = 1 ->
    exists t : R, x = cos t /\ y = sin t.
  Proof.
    intros x y H.
    assert (Hx : -1 <= x <= 1).
    { pose proof (Rle_0_sqr y) as Hy. unfold Rsqr in Hy. split; nra. }
    assert (Hs : sqrt (1 - Rsqr x) = Rabs y).
    { rewrite <- sqrt_Rsqr_abs. apply f_equal. unfold Rsqr. lra. }
    destruct (Rle_lt_dec 0 y) as [Hy | Hy].
    - exists (acos x). split.
      + symmetry. apply cos_acos. exact Hx.
      + rewrite (sin_acos x Hx), Hs. symmetry. apply Rabs_pos_eq. exact Hy.
    - exists (- acos x). split.
      + rewrite cos_neg. symmetry. apply cos_acos. exact Hx.
      + rewrite sin_neg, (sin_acos x Hx), Hs.
        rewrite (Rabs_left y Hy). ring.
  Qed.

  (* every point of the plane is r (cos t, sin t) with r = |(x, y)| *)
  Lemma polar_coords : forall x y : R,
    exists t : R, x = sqrt (x * x + y * y) * cos t /\
                  y = sqrt (x * x + y * y) * sin t.
  Proof.
    intros x y.
    assert (Hnn : 0 <= x * x + y * y).
    { pose proof (Rle_0_sqr x) as Hx. pose proof (Rle_0_sqr y) as Hy.
      unfold Rsqr in *. lra. }
    pose proof (sqrt_pos (x * x + y * y)) as Hr.
    pose proof (sqrt_sqrt (x * x + y * y) Hnn) as Hrr.
    set (r := sqrt (x * x + y * y)) in *.
    destruct (Req_dec r 0) as [E | E].
    - exists 0. rewrite E in Hrr.
      assert (Hx0 : x = 0) by nra. assert (Hy0 : y = 0) by nra.
      rewrite E, Hx0, Hy0. split; ring.
    - assert (Hrp : 0 < r) by lra.
      destruct (polar_angle (x / r) (y / r)) as [t [Hc Hs]].
      { replace (x / r * (x / r) + y / r * (y / r))
          with ((x * x + y * y) / (r * r)) by (field; exact E).
        rewrite <- Hrr. field. exact E. }
      exists t. rewrite <- Hc, <- Hs. split; field; exact E.
  Qed.

  (* =======================================================================
     2. Every unit quaternion lies in the orbit of 1
     ======================================================================= *)

  Lemma orbit_coords : forall t1 t2 t3 : R,
    rot01 t1 (rot23 t2 (swap12 (rot01 t3 qone))) =
    mkQuat (cos t1 * cos t3) (sin t1 * cos t3) (cos t2 * sin t3) (sin t2 * sin t3).
  Proof.
    intros t1 t2 t3. apply quat_eq;
      unfold rot01, rot23, swap12, qone; cbn [qr qi qj qk]; ring.
  Qed.

  (* every unit quaternion is obtained from 1 by rotations in coordinate planes *)
  Theorem unit_orbit : forall q : Quat, su2_unit q ->
    exists t1 t2 t3 : R, q = rot01 t1 (rot23 t2 (swap12 (rot01 t3 qone))).
  Proof.
    intros [a b c d] Hq. unfold su2_unit, qnorm2 in Hq. cbn [qr qi qj qk] in Hq.
    destruct (polar_coords a b) as [t1 [Ha Hb]].
    destruct (polar_coords c d) as [t2 [Hc Hd]].
    assert (Hab : 0 <= a * a + b * b).
    { pose proof (Rle_0_sqr a) as H1. pose proof (Rle_0_sqr b) as H2.
      unfold Rsqr in *. lra. }
    assert (Hcd : 0 <= c * c + d * d).
    { pose proof (Rle_0_sqr c) as H1. pose proof (Rle_0_sqr d) as H2.
      unfold Rsqr in *. lra. }
    pose proof (sqrt_sqrt (a * a + b * b) Hab) as Hr1.
    pose proof (sqrt_sqrt (c * c + d * d) Hcd) as Hr2.
    set (r1 := sqrt (a * a + b * b)) in *.
    set (r2 := sqrt (c * c + d * d)) in *.
    destruct (polar_angle r1 r2) as [t3 [H1 H2]]; [lra |].
    exists t1, t2, t3. rewrite orbit_coords.
    apply quat_eq; cbn [qr qi qj qk]; rewrite <- ?H1, <- ?H2.
    - rewrite Ha at 1. ring.
    - rewrite Hb at 1. ring.
    - rewrite Hc at 1. ring.
    - rewrite Hd at 1. ring.
  Qed.

  (* =======================================================================
     3. The first block of a mean
     ======================================================================= *)

  (* one-sided version of `mean_bounds` *)
  Lemma mean_lower : forall N (f : nat -> R) a, (0 < N)%nat ->
    (forall i, (i < N)%nat -> a <= f i) -> a <= mean N f.
  Proof.
    intros N f a HN H. unfold mean.
    assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
    assert (HS : INR N * a <= rsum (seq 0 N) f).
    { replace (INR N * a) with (rsum (seq 0 N) (fun _ : nat => a))
        by (rewrite rsum_const_length, seq_length; reflexivity).
      apply rsum_le. intros i Hi. apply in_seq in Hi. apply H. lia. }
    replace a with (INR N * a / INR N) by (field; lra).
    unfold Rdiv. apply Rmult_le_compat_r;
      [left; apply Rinv_0_lt_compat; exact HN' | exact HS].
  Qed.

  Lemma mean_ge_first : forall N (g : nat -> R), (0 < N)%nat ->
    (forall i, (i < N)%nat -> 0 <= g i) -> g 0%nat / INR N <= mean N g.
  Proof.
    intros N g HN H. unfold mean, Rdiv.
    assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
    apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact HN' |].
    apply rsum_ge_term.
    - intros x Hx. apply in_seq in Hx. apply H. lia.
    - apply in_seq. lia.
  Qed.

  (* if f >= 0 and f >= c on the first of P consecutive blocks of length A,
     then the mean of f is at least c / P *)
  Lemma mean_first_block : forall N P A (f : nat -> R) c,
    N = (P * A)%nat -> (0 < P)%nat -> (0 < A)%nat ->
    (forall i, (i < N)%nat -> 0 <= f i) ->
    (forall r, (r < A)%nat -> c <= f r) ->
    c / INR P <= mean N f.
  Proof.
    intros N P A f c -> HP HA H0 Hc.
    assert (HP' : 0 < INR P) by (apply lt_0_INR; exact HP).
    rewrite (mean_split P A f HP HA).
    eapply Rle_trans; [| apply mean_ge_first; [exact HP |]].
    - unfold Rdiv. apply Rmult_le_compat_r;
        [left; apply Rinv_0_lt_compat; exact HP' |].
      apply mean_lower; [exact HA |].
      intros r Hr. cbn [Nat.mul Nat.add]. apply Hc. exact Hr.
    - intros i Hi. apply mean_lower; [exact HA |].
      intros r Hr. apply H0. nia.
  Qed.

  (* =======================================================================
     4. Grid points near 1
     ======================================================================= *)

  Lemma hopf_origin : su2_hopf 0 0 0 = qone.
  Proof.
    unfold su2_hopf, qone.
    rewrite Rminus_0_r, Rmult_0_r, sqrt_1, sqrt_0, cos_0, sin_0.
    apply quat_eq; cbn [qr qi qj qk]; ring.
  Qed.

  (* the indices of the first of P blocks of length A give fractions < 1/P *)
  Lemma frac_small : forall N P A i,
    N = (P * A)%nat -> (0 < P)%nat -> (0 < A)%nat -> (i < A)%nat ->
    Rabs (INR i / INR N - 0) < / INR P.
  Proof.
    intros N P A i -> HP HA Hi.
    assert (HP' : 0 < INR P) by (apply lt_0_INR; exact HP).
    assert (HA' : 0 < INR A) by (apply lt_0_INR; exact HA).
    assert (Hi' : INR i < INR A) by (apply lt_INR; exact Hi).
    pose proof (pos_INR i) as Hi0.
    rewrite Rminus_0_r, mult_INR.
    assert (Hinv : 0 < / (INR P * INR A)).
    { apply Rinv_0_lt_compat. apply Rmult_lt_0_compat; assumption. }
    rewrite Rabs_pos_eq.
    - replace (/ INR P) with (INR A / (INR P * INR A)) by (field; lra).
      unfold Rdiv. apply Rmult_lt_compat_r; assumption.
    - unfold Rdiv. apply Rmult_le_pos; [exact Hi0 | left; exact Hinv].
  Qed.

  (* the grid points with indices in the first blocks are close to 1 *)
  Lemma gpt_near_one : forall N Q A B i j k,
    (0 < Q)%nat -> (0 < A)%nat -> (0 < B)%nat ->
    N = (Q * Q * A)%nat -> N = (Q * B)%nat ->
    (i < A)%nat -> (j < B)%nat -> (k < B)%nat ->
    su2_close (9 * / INR Q) (gpt N i j k) qone.
  Proof.
    intros N Q A B i j k HQ HA HB HNA HNB Hi Hj Hk.
    assert (HQ' : 0 < INR Q) by (apply lt_0_INR; exact HQ).
    rewrite <- hopf_origin. unfold gpt.
    apply hopf_close.
    - apply Rinv_0_lt_compat. exact HQ'.
    - apply frac_range. rewrite HNA.
      assert (HQQ : (1 <= Q * Q)%nat) by nia.
      pose proof (Nat.mul_le_mono_r 1 (Q * Q) A HQQ) as HM. lia.
    - lra.
    - replace (/ INR Q * / INR Q) with (/ INR (Q * Q)).
      + apply (frac_small N (Q * Q) A i HNA); [nia | exact HA | exact Hi].
      + rewrite mult_INR. field. lra.
    - apply (frac_small N Q B j HNB HQ HB Hj).
    - apply (frac_small N Q B k HNB HQ HB Hk).
  Qed.

  (* =======================================================================
     5. A neighbourhood of 1 carries a positive fraction of every fine grid
     ======================================================================= *)

  (* a neighbourhood of 1 carries a positive fraction of every fine grid *)
  Theorem cap_positive : forall rho : R, 0 < rho ->
    exists (c : R) (n0 : nat), 0 < c /\
      forall (n : nat) (h : Quat -> R), (n0 <= n)%nat ->
        (forall u, su2_unit u -> 0 <= h u) ->
        (forall u, su2_unit u -> su2_close rho u qone -> 1 <= h u) ->
        c <= gmean n h.
  Proof.
    intros rho Hrho.
    destruct (pow2_inv_small (rho / 9)) as [m Hm]; [lra |].
    specialize (Hm m (Nat.le_refl m)).
    set (Q := (2 ^ m)%nat) in *.
    assert (HQ : (0 < Q)%nat) by apply pow2_pos.
    assert (HQ' : 0 < INR Q) by (apply lt_0_INR; exact HQ).
    assert (HQQ : (0 < Q * Q)%nat) by nia.
    assert (HQQ' : 0 < INR (Q * Q)) by (apply lt_0_INR; exact HQQ).
    exists (1 / INR Q / INR Q / INR (Q * Q)), (2 * m)%nat. split.
    { unfold Rdiv. rewrite Rmult_1_l.
      repeat apply Rmult_lt_0_compat; apply Rinv_0_lt_compat; assumption. }
    intros n h Hn Hpos Hone.
    set (N := (2 ^ n)%nat).
    set (A := (2 ^ (n - 2 * m))%nat).
    set (B := (2 ^ (n - m))%nat).
    assert (HA : (0 < A)%nat) by apply pow2_pos.
    assert (HB : (0 < B)%nat) by apply pow2_pos.
    assert (HNA : N = (Q * Q * A)%nat).
    { unfold N, Q, A. rewrite <- !Nat.pow_add_r. f_equal. lia. }
    assert (HNB : N = (Q * B)%nat).
    { unfold N, Q, B. rewrite <- Nat.pow_add_r. f_equal. lia. }
    assert (HN : (0 < N)%nat) by apply pow2_pos.
    rewrite gmean_mean. fold N.
    assert (Hh0 : forall i j k, (i < N)%nat -> 0 <= h (gpt N i j k)).
    { intros i j k Hi. apply Hpos. apply gpt_unit. exact Hi. }
    assert (Hh1 : forall i j k, (i < A)%nat -> (j < B)%nat -> (k < B)%nat ->
              1 <= h (gpt N i j k)).
    { intros i j k Hi Hj Hk. apply Hone.
      - apply gpt_unit. rewrite HNA. nia.
      - apply (close_mono (9 * / INR Q)); [lra |].
        apply (gpt_near_one N Q A B); assumption. }
    apply (mean_first_block N (Q * Q) A _ _ HNA HQQ HA).
    - intros i Hi. apply mean_lower; [exact HN |]. intros j _.
      apply mean_lower; [exact HN |]. intros k _. apply Hh0. exact Hi.
    - intros i Hi.
      assert (HiN : (i < N)%nat) by (rewrite HNA; nia).
      apply (mean_first_block N Q B _ _ HNB HQ HB).
      + intros j _. apply mean_lower; [exact HN |]. intros k _.
        apply Hh0. exact HiN.
      + intros j Hj.
        apply (mean_first_block N Q B _ _ HNB HQ HB).
        * intros k _. apply Hh0. exact HiN.
        * intros k Hk. apply Hh1; assumption.
  Qed.

End SU2HaarOrbit.
