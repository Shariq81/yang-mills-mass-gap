(* =========================================================================
   ym/su2_haar_torus.v

   Invariance of the Haar integral of SU(2) (the limit of the averages over
   the dyadic Hopf grids) under the maximal torus acting on the two Hopf
   angles:

     - `hopf_rot01`, `hopf_rot23`: the rotation by the angle 2 pi b in the
       plane of the first two (last two) coordinates shifts the first
       (second) Hopf angle by b;
     - `cshift_perm`: the cyclic shift j |-> j + c mod N permutes the index
       range, so a mean over the range is invariant (`mean_cshift`);
     - `gmean_rot01_close`, `gmean_rot23_close`: the grid average of a
       function composed with a rotation differs from the grid average of
       the function by at most its modulus of continuity at 9 / 2^n: the
       shift of the Hopf angle is within the mesh 1 / 2^n of a cyclic
       shift of the grid indices;
     - `haar_rot01`, `haar_rot23`: the Haar integral of a bounded uniformly
       continuous function is invariant under both rotations, for every
       angle t;
     - `rot01_unit`, `rot23_unit`, `fn_bc_rot01`, `fn_bc_rot23`: the
       rotations preserve the unit quaternions and the bounded uniformly
       continuous functions.

   Depends ONLY on Coq stdlib + the frozen challenge files
   + rg.dup_clustering + rg.product_measure + ym.su2_algebra
   + ym.su2_haar_grid + ym.su2_haar_mean.
   Every statement is proved; no unproved declarations.
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
Require Import ym.su2_haar_mean.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeSU2Gauge ChallengeSU2GaugeInvariance.
Import DupClustering SU2Algebra SU2HaarGrid SU2HaarMean.
Open Scope R_scope.

Module SU2HaarTorus.

  (* =======================================================================
     1. Cyclic shifts of an index range
     ======================================================================= *)

  (* the cyclic shift by c of an index of the range with N elements *)
  Definition cshift (N c j : nat) : nat :=
    if (j + c <? N)%nat then (j + c)%nat else (j + c - N)%nat.

  Lemma cshift_lt : forall N c j,
    (c < N)%nat -> (j < N)%nat -> (cshift N c j < N)%nat.
  Proof.
    intros N c j Hc Hj. unfold cshift.
    destruct (Nat.ltb_spec (j + c) N); lia.
  Qed.

  Lemma cshift_perm_split : forall m c,
    Permutation (map (cshift (m + c) c) (seq 0 (m + c))) (seq 0 (m + c)).
  Proof.
    intros m c.
    assert (E : map (cshift (m + c) c) (seq 0 (m + c)) = seq c m ++ seq 0 c).
    { rewrite seq_app, map_app. change (0 + m)%nat with m.
      rewrite (map_ext_in (cshift (m + c) c) (fun j => (j + c)%nat) (seq 0 m)).
      2: { intros j Hj. apply in_seq in Hj. unfold cshift.
           destruct (Nat.ltb_spec (j + c) (m + c)); [reflexivity | lia]. }
      rewrite (map_ext_in (cshift (m + c) c) (fun j => (j - m)%nat) (seq m c)).
      2: { intros j Hj. apply in_seq in Hj. unfold cshift.
           destruct (Nat.ltb_spec (j + c) (m + c)); lia. }
      rewrite (map_add_seq c m 0).
      pose proof (map_sub_seq m c 0) as Hsub.
      change (0 + m)%nat with m in Hsub. rewrite Hsub. reflexivity. }
    rewrite E. replace (m + c)%nat with (c + m)%nat by lia.
    rewrite seq_app. change (0 + c)%nat with c. apply Permutation_app_comm.
  Qed.

  (* the cyclic shift permutes the index range *)
  Lemma cshift_perm : forall N c, (c <= N)%nat ->
    Permutation (map (cshift N c) (seq 0 N)) (seq 0 N).
  Proof.
    intros N c Hc.
    assert (E : N = (N - c + c)%nat) by lia.
    rewrite E. apply cshift_perm_split.
  Qed.

  Lemma mean_cshift : forall N c (f : nat -> R), (c <= N)%nat ->
    mean N (fun j => f (cshift N c j)) = mean N f.
  Proof.
    intros N c f Hc. unfold mean, Rdiv. apply Rmult_eq_compat_r.
    transitivity (rsum (map (cshift N c) (seq 0 N)) f).
    - symmetry. apply rsum_map.
    - apply ProductMeasure.rsum_perm. apply cshift_perm. exact Hc.
  Qed.

  Lemma cshift_frac : forall N c j, (0 < N)%nat ->
    INR (cshift N c j) / INR N = INR (j + c) / INR N \/
    INR (cshift N c j) / INR N = INR (j + c) / INR N - 1.
  Proof.
    intros N c j HN. unfold cshift.
    assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
    destruct (Nat.ltb_spec (j + c) N) as [Hlt | Hge].
    - left. reflexivity.
    - right. rewrite (minus_INR (j + c) N Hge). field. lra.
  Qed.

  (* =======================================================================
     2. Periodicity and the reduction of an angle
     ======================================================================= *)

  Lemma trig_unit_shift : forall x x', (x' = x \/ x' = x - 1) ->
    cos (2 * PI * x') = cos (2 * PI * x) /\ sin (2 * PI * x') = sin (2 * PI * x).
  Proof.
    intros x x' [-> | ->]; [split; reflexivity |].
    assert (E : 2 * PI * x = 2 * PI * (x - 1) + 2 * INR 1 * PI)
      by (cbn [INR]; ring).
    rewrite E. split; symmetry; [apply cos_period | apply sin_period].
  Qed.

  Lemma trig_int_shift : forall u (z : Z),
    cos (u + 2 * IZR z * PI) = cos u /\ sin (u + 2 * IZR z * PI) = sin u.
  Proof.
    intros u z. destruct (Z_le_gt_dec 0 z) as [Hz | Hz].
    - assert (E : IZR z = INR (Z.to_nat z)).
      { rewrite INR_IZR_INZ, Z2Nat.id by exact Hz. reflexivity. }
      rewrite E. split; [apply cos_period | apply sin_period].
    - assert (E : IZR z = - INR (Z.to_nat (- z))).
      { rewrite INR_IZR_INZ, Z2Nat.id by lia. rewrite opp_IZR. ring. }
      rewrite E. set (m := Z.to_nat (- z)).
      rewrite <- (cos_period (u + 2 * - INR m * PI) m),
              <- (sin_period (u + 2 * - INR m * PI) m).
      assert (E' : u + 2 * - INR m * PI + 2 * INR m * PI = u) by ring.
      rewrite E'. split; reflexivity.
  Qed.

  (* every angle is 2 pi b for some b in [0,1), up to a multiple of 2 pi *)
  Lemma angle_reduce : forall t, exists b, 0 <= b < 1 /\
    cos (2 * PI * b) = cos t /\ sin (2 * PI * b) = sin t.
  Proof.
    intro t. pose proof PI_RGT_0 as HPI.
    assert (Ha : exists a, t = 2 * PI * a).
    { exists (t / (2 * PI)). field. lra. }
    destruct Ha as [a ->].
    destruct (archimed a) as [H1 H2].
    exists (a - IZR (up a - 1)). split.
    - rewrite minus_IZR. lra.
    - destruct (trig_int_shift (2 * PI * (a - IZR (up a - 1))) (up a - 1))
        as [Hc Hs].
      assert (E : 2 * PI * (a - IZR (up a - 1)) + 2 * IZR (up a - 1) * PI
                  = 2 * PI * a) by ring.
      rewrite E in Hc, Hs. split; symmetry; assumption.
  Qed.

  Lemma nat_floor : forall x, 0 <= x -> exists m : nat, INR m <= x < INR m + 1.
  Proof.
    intros x Hx. destruct (archimed x) as [H1 H2].
    assert (Hz : (0 <= up x - 1)%Z).
    { assert (H : 0 < IZR (up x)) by lra. apply lt_IZR in H. lia. }
    exists (Z.to_nat (up x - 1)).
    rewrite INR_IZR_INZ, Z2Nat.id by exact Hz. rewrite minus_IZR. lra.
  Qed.

  (* =======================================================================
     3. The rotations in Hopf coordinates
     ======================================================================= *)

  Lemma rot01_trig : forall t t' q, cos t' = cos t -> sin t' = sin t ->
    rot01 t' q = rot01 t q.
  Proof. intros t t' q Hc Hs. unfold rot01. rewrite Hc, Hs. reflexivity. Qed.

  Lemma rot23_trig : forall t t' q, cos t' = cos t -> sin t' = sin t ->
    rot23 t' q = rot23 t q.
  Proof. intros t t' q Hc Hs. unfold rot23. rewrite Hc, Hs. reflexivity. Qed.

  Lemma rot01_unit : forall t q, su2_unit q -> su2_unit (rot01 t q).
  Proof.
    intros t [a b c d]. unfold su2_unit, qnorm2, rot01. cbn [qr qi qj qk].
    intro H. pose proof (sin2_cos2 t) as Ht. unfold Rsqr in Ht.
    transitivity ((sin t * sin t + cos t * cos t) * (a * a + b * b) + c * c + d * d);
      [ring |].
    rewrite Ht. lra.
  Qed.

  Lemma rot23_unit : forall t q, su2_unit q -> su2_unit (rot23 t q).
  Proof.
    intros t [a b c d]. unfold su2_unit, qnorm2, rot23. cbn [qr qi qj qk].
    intro H. pose proof (sin2_cos2 t) as Ht. unfold Rsqr in Ht.
    transitivity (a * a + b * b + (sin t * sin t + cos t * cos t) * (c * c + d * d));
      [ring |].
    rewrite Ht. lra.
  Qed.

  Lemma rot_pair_close : forall c s x y d : R,
    -1 <= c <= 1 -> -1 <= s <= 1 -> Rabs x < d -> Rabs y < d ->
    Rabs (c * x - s * y) < 2 * d /\ Rabs (s * x + c * y) < 2 * d.
  Proof.
    intros c s x y d Hc Hs Hx Hy.
    assert (B : forall a z, -1 <= a <= 1 -> Rabs (a * z) <= Rabs z).
    { intros a z Ha. rewrite Rabs_mult.
      assert (Rabs a <= 1) by (apply Rabs_le; exact Ha).
      pose proof (Rabs_pos a). pose proof (Rabs_pos z). nra. }
    pose proof (B c x Hc) as B1. pose proof (B s y Hs) as B2.
    pose proof (B s x Hs) as B3. pose proof (B c y Hc) as B4.
    split.
    - unfold Rminus. eapply Rle_lt_trans; [apply Rabs_triang |].
      rewrite Rabs_Ropp. lra.
    - eapply Rle_lt_trans; [apply Rabs_triang |]. lra.
  Qed.

  (* the rotations are uniformly continuous *)
  Lemma rot01_close : forall t d u v,
    su2_close d u v -> su2_close (2 * d) (rot01 t u) (rot01 t v).
  Proof.
    intros t d u v (H1 & H2 & H3 & H4).
    destruct (rot_pair_close (cos t) (sin t) _ _ d (COS_bound t) (SIN_bound t) H1 H2)
      as [K1 K2].
    pose proof (Rabs_pos (qj u - qj v)) as P3.
    unfold su2_close, rot01. cbn [qr qi qj qk].
    replace (cos t * qr u - sin t * qi u - (cos t * qr v - sin t * qi v))
      with (cos t * (qr u - qr v) - sin t * (qi u - qi v)) by ring.
    replace (sin t * qr u + cos t * qi u - (sin t * qr v + cos t * qi v))
      with (sin t * (qr u - qr v) + cos t * (qi u - qi v)) by ring.
    repeat split; solve [assumption | lra].
  Qed.

  Lemma rot23_close : forall t d u v,
    su2_close d u v -> su2_close (2 * d) (rot23 t u) (rot23 t v).
  Proof.
    intros t d u v (H1 & H2 & H3 & H4).
    destruct (rot_pair_close (cos t) (sin t) _ _ d (COS_bound t) (SIN_bound t) H3 H4)
      as [K1 K2].
    pose proof (Rabs_pos (qr u - qr v)) as P1.
    unfold su2_close, rot23. cbn [qr qi qj qk].
    replace (cos t * qj u - sin t * qk u - (cos t * qj v - sin t * qk v))
      with (cos t * (qj u - qj v) - sin t * (qk u - qk v)) by ring.
    replace (sin t * qj u + cos t * qk u - (sin t * qj v + cos t * qk v))
      with (sin t * (qj u - qj v) + cos t * (qk u - qk v)) by ring.
    repeat split; solve [assumption | lra].
  Qed.

  (* composition with a rotation preserves the bounded uniformly continuous
     functions *)
  Lemma fn_bc_rot01 : forall t (h : Quat -> R),
    fn_bc h -> fn_bc (fun q => h (rot01 t q)).
  Proof.
    intros t h [[M HM] Hc]. split.
    - exists M. intros u Hu. apply HM. apply rot01_unit. exact Hu.
    - intros eps He. destruct (Hc eps He) as [delta [Hd H]].
      exists (delta / 2). split; [lra |]. intros u v Hu Hv Hcl.
      apply H; [apply rot01_unit; exact Hu | apply rot01_unit; exact Hv |].
      assert (E : delta = 2 * (delta / 2)) by field.
      rewrite E. apply rot01_close. exact Hcl.
  Qed.

  Lemma fn_bc_rot23 : forall t (h : Quat -> R),
    fn_bc h -> fn_bc (fun q => h (rot23 t q)).
  Proof.
    intros t h [[M HM] Hc]. split.
    - exists M. intros u Hu. apply HM. apply rot23_unit. exact Hu.
    - intros eps He. destruct (Hc eps He) as [delta [Hd H]].
      exists (delta / 2). split; [lra |]. intros u v Hu Hv Hcl.
      apply H; [apply rot23_unit; exact Hu | apply rot23_unit; exact Hv |].
      assert (E : delta = 2 * (delta / 2)) by field.
      rewrite E. apply rot23_close. exact Hcl.
  Qed.

  (* the rotation by 2 pi b shifts a Hopf angle by b *)
  Lemma hopf_rot01 : forall b s x y,
    rot01 (2 * PI * b) (su2_hopf s x y) = su2_hopf s (x + b) y.
  Proof.
    intros b s x y.
    assert (E : 2 * PI * (x + b) = 2 * PI * x + 2 * PI * b) by ring.
    apply quat_eq; unfold rot01, su2_hopf; cbn [qr qi qj qk];
      try reflexivity; rewrite E.
    - rewrite cos_plus. ring.
    - rewrite sin_plus. ring.
  Qed.

  Lemma hopf_rot23 : forall b s x y,
    rot23 (2 * PI * b) (su2_hopf s x y) = su2_hopf s x (y + b).
  Proof.
    intros b s x y.
    assert (E : 2 * PI * (y + b) = 2 * PI * y + 2 * PI * b) by ring.
    apply quat_eq; unfold rot23, su2_hopf; cbn [qr qi qj qk];
      try reflexivity; rewrite E.
    - rewrite cos_plus. ring.
    - rewrite sin_plus. ring.
  Qed.

  (* the Hopf coordinates are periodic in both angles *)
  Lemma hopf_x_cshift : forall N c j s y, (0 < N)%nat ->
    su2_hopf s (INR (cshift N c j) / INR N) y =
    su2_hopf s (INR (j + c) / INR N) y.
  Proof.
    intros N c j s y HN.
    destruct (trig_unit_shift _ _ (cshift_frac N c j HN)) as [Hc Hs].
    unfold su2_hopf. rewrite Hc, Hs. reflexivity.
  Qed.

  Lemma hopf_y_cshift : forall N c k s x, (0 < N)%nat ->
    su2_hopf s x (INR (cshift N c k) / INR N) =
    su2_hopf s x (INR (k + c) / INR N).
  Proof.
    intros N c k s x HN.
    destruct (trig_unit_shift _ _ (cshift_frac N c k HN)) as [Hc Hs].
    unfold su2_hopf. rewrite Hc, Hs. reflexivity.
  Qed.

  (* a shifted grid angle is within the mesh of a grid angle *)
  Lemma shift_frac_close : forall N c j b eta, (0 < N)%nat ->
    INR c <= b * INR N < INR c + 1 -> / INR N <= eta ->
    Rabs (INR j / INR N + b - INR (j + c) / INR N) < eta.
  Proof.
    intros N c j b eta HN [Hc1 Hc2] Heta.
    assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
    assert (Hinv : 0 < / INR N) by (apply Rinv_0_lt_compat; exact HN').
    rewrite plus_INR.
    replace (INR j / INR N + b - (INR j + INR c) / INR N)
      with ((b * INR N - INR c) * / INR N) by (field; lra).
    rewrite Rabs_pos_eq by (apply Rmult_le_pos; lra).
    apply Rlt_le_trans with (1 * / INR N); [| lra].
    apply Rmult_lt_compat_r; lra.
  Qed.

  Lemma abs_self_lt : forall x e : R, 0 < e -> Rabs (x - x) < e.
  Proof.
    intros x e He. unfold Rminus. rewrite Rplus_opp_r, Rabs_R0. exact He.
  Qed.

  (* =======================================================================
     4. The grid averages of a rotated function
     ======================================================================= *)

  Lemma mean3_rot01_close : forall (h : Quat -> R) (b delta eps : R) (N : nat),
    0 <= b < 1 -> 0 < delta ->
    (forall u v, su2_unit u -> su2_unit v -> su2_close delta u v ->
       Rabs (h u - h v) <= eps) ->
    (0 < N)%nat -> / INR N <= delta / 9 ->
    Rabs (mean N (fun i => mean N (fun j => mean N (fun k =>
            h (rot01 (2 * PI * b) (gpt N i j k)))))
          - mean N (fun i => mean N (fun j => mean N (fun k =>
              h (gpt N i j k))))) <= eps.
  Proof.
    intros h b delta eps N Hb Hd Hm HN Hn.
    assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
    destruct (nat_floor (b * INR N)) as [c Hc]; [nra |].
    assert (HcN : (c < N)%nat) by (apply INR_lt; nra).
    assert (E : mean N (fun i => mean N (fun j => mean N (fun k =>
                  h (gpt N i j k)))) =
                mean N (fun i => mean N (fun j => mean N (fun k =>
                  h (gpt N i (cshift N c j) k))))).
    { apply mean_ext. intros i _. symmetry.
      apply (mean_cshift N c (fun j => mean N (fun k => h (gpt N i j k)))). lia. }
    rewrite E.
    apply mean_close; [exact HN |]. intros i Hi. cbv beta.
    apply mean_close; [exact HN |]. intros j Hj. cbv beta.
    apply mean_close; [exact HN |]. intros k Hk. cbv beta.
    unfold gpt. rewrite hopf_rot01, (hopf_x_cshift N c j _ _ HN).
    assert (Hs : 0 <= INR i / INR N <= 1) by (apply frac_range; exact Hi).
    apply Hm.
    - apply hopf_unit. exact Hs.
    - apply hopf_unit. exact Hs.
    - assert (Ed : delta = 9 * (delta / 9)) by field.
      rewrite Ed. apply hopf_close.
      + lra.
      + exact Hs.
      + exact Hs.
      + apply abs_self_lt. apply Rmult_lt_0_compat; lra.
      + apply shift_frac_close; assumption.
      + apply abs_self_lt. lra.
  Qed.

  Lemma mean3_rot23_close : forall (h : Quat -> R) (b delta eps : R) (N : nat),
    0 <= b < 1 -> 0 < delta ->
    (forall u v, su2_unit u -> su2_unit v -> su2_close delta u v ->
       Rabs (h u - h v) <= eps) ->
    (0 < N)%nat -> / INR N <= delta / 9 ->
    Rabs (mean N (fun i => mean N (fun j => mean N (fun k =>
            h (rot23 (2 * PI * b) (gpt N i j k)))))
          - mean N (fun i => mean N (fun j => mean N (fun k =>
              h (gpt N i j k))))) <= eps.
  Proof.
    intros h b delta eps N Hb Hd Hm HN Hn.
    assert (HN' : 0 < INR N) by (apply lt_0_INR; exact HN).
    destruct (nat_floor (b * INR N)) as [c Hc]; [nra |].
    assert (HcN : (c < N)%nat) by (apply INR_lt; nra).
    assert (E : mean N (fun i => mean N (fun j => mean N (fun k =>
                  h (gpt N i j k)))) =
                mean N (fun i => mean N (fun j => mean N (fun k =>
                  h (gpt N i j (cshift N c k)))))).
    { apply mean_ext. intros i _. apply mean_ext. intros j _. symmetry.
      apply (mean_cshift N c (fun k => h (gpt N i j k))). lia. }
    rewrite E.
    apply mean_close; [exact HN |]. intros i Hi. cbv beta.
    apply mean_close; [exact HN |]. intros j Hj. cbv beta.
    apply mean_close; [exact HN |]. intros k Hk. cbv beta.
    unfold gpt. rewrite hopf_rot23, (hopf_y_cshift N c k _ _ HN).
    assert (Hs : 0 <= INR i / INR N <= 1) by (apply frac_range; exact Hi).
    apply Hm.
    - apply hopf_unit. exact Hs.
    - apply hopf_unit. exact Hs.
    - assert (Ed : delta = 9 * (delta / 9)) by field.
      rewrite Ed. apply hopf_close.
      + lra.
      + exact Hs.
      + exact Hs.
      + apply abs_self_lt. apply Rmult_lt_0_compat; lra.
      + apply abs_self_lt. lra.
      + apply shift_frac_close; assumption.
  Qed.

  Lemma gmean_rot01_close : forall (h : Quat -> R) (b delta eps : R) (n : nat),
    0 <= b < 1 -> 0 < delta ->
    (forall u v, su2_unit u -> su2_unit v -> su2_close delta u v ->
       Rabs (h u - h v) <= eps) ->
    / INR (2 ^ n) <= delta / 9 ->
    Rabs (gmean n (fun q => h (rot01 (2 * PI * b) q)) - gmean n h) <= eps.
  Proof.
    intros h b delta eps n Hb Hd Hm Hn.
    rewrite (gmean_mean n (fun q => h (rot01 (2 * PI * b) q))), (gmean_mean n h).
    cbv beta.
    exact (mean3_rot01_close h b delta eps (2 ^ n) Hb Hd Hm (pow2_pos n) Hn).
  Qed.

  Lemma gmean_rot23_close : forall (h : Quat -> R) (b delta eps : R) (n : nat),
    0 <= b < 1 -> 0 < delta ->
    (forall u v, su2_unit u -> su2_unit v -> su2_close delta u v ->
       Rabs (h u - h v) <= eps) ->
    / INR (2 ^ n) <= delta / 9 ->
    Rabs (gmean n (fun q => h (rot23 (2 * PI * b) q)) - gmean n h) <= eps.
  Proof.
    intros h b delta eps n Hb Hd Hm Hn.
    rewrite (gmean_mean n (fun q => h (rot23 (2 * PI * b) q))), (gmean_mean n h).
    cbv beta.
    exact (mean3_rot23_close h b delta eps (2 ^ n) Hb Hd Hm (pow2_pos n) Hn).
  Qed.

  (* =======================================================================
     5. Invariance of the Haar integral under the torus
     ======================================================================= *)

  (* two functions whose grid averages become arbitrarily close have the
     same Haar integral *)
  Lemma haar_lim_close : forall (h h' : Quat -> R) (v : R),
    (forall eps, 0 < eps -> exists n0 : nat, forall n, (n0 <= n)%nat ->
       Rabs (gmean n h' - gmean n h) <= eps) ->
    haar_lim h v -> haar_lim h' v.
  Proof.
    intros h h' v Hc Hv eps He.
    assert (He2 : 0 < eps / 2) by lra.
    destruct (Hc (eps / 2) He2) as [n0 Hn0].
    destruct (Hv (eps / 2) He2) as [n1 Hn1].
    exists (Nat.max n0 n1). intros n Hn.
    assert (L0 : (n0 <= n)%nat) by lia.
    assert (L1 : (n >= n1)%nat) by lia.
    pose proof (Hn0 n L0) as K1. pose proof (Hn1 n L1) as K2.
    unfold R_dist in *. cbv beta in K2.
    replace (gmean n h' - v)
      with ((gmean n h' - gmean n h) + (gmean n h - v)) by ring.
    eapply Rle_lt_trans; [apply Rabs_triang |]. lra.
  Qed.

  Theorem haar_rot01 : forall (t : R) (h : Quat -> R) (v : R),
    fn_bc h -> haar_lim h v -> haar_lim (fun q => h (rot01 t q)) v.
  Proof.
    intros t h v Hh Hv.
    destruct (angle_reduce t) as [b [Hb [Hc Hs]]].
    apply (haar_lim_close h); [| exact Hv].
    intros eps He.
    destruct (fn_bc_modulus h Hh eps He) as [delta [Hd Hm]].
    assert (Hd9 : 0 < delta / 9) by lra.
    destruct (pow2_inv_small (delta / 9) Hd9) as [n0 Hn0].
    exists n0. intros n Hn.
    assert (E : gmean n (fun q => h (rot01 t q)) =
                gmean n (fun q => h (rot01 (2 * PI * b) q))).
    { apply gmean_ext. intros u _.
      rewrite (rot01_trig t (2 * PI * b) u Hc Hs). reflexivity. }
    rewrite E.
    apply (gmean_rot01_close h b delta eps n Hb Hd Hm).
    left. apply Hn0. exact Hn.
  Qed.

  Theorem haar_rot23 : forall (t : R) (h : Quat -> R) (v : R),
    fn_bc h -> haar_lim h v -> haar_lim (fun q => h (rot23 t q)) v.
  Proof.
    intros t h v Hh Hv.
    destruct (angle_reduce t) as [b [Hb [Hc Hs]]].
    apply (haar_lim_close h); [| exact Hv].
    intros eps He.
    destruct (fn_bc_modulus h Hh eps He) as [delta [Hd Hm]].
    assert (Hd9 : 0 < delta / 9) by lra.
    destruct (pow2_inv_small (delta / 9) Hd9) as [n0 Hn0].
    exists n0. intros n Hn.
    assert (E : gmean n (fun q => h (rot23 t q)) =
                gmean n (fun q => h (rot23 (2 * PI * b) q))).
    { apply gmean_ext. intros u _.
      rewrite (rot23_trig t (2 * PI * b) u Hc Hs). reflexivity. }
    rewrite E.
    apply (gmean_rot23_close h b delta eps n Hb Hd Hm).
    left. apply Hn0. exact Hn.
  Qed.

End SU2HaarTorus.
