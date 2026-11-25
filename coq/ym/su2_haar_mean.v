(* =========================================================================
   ym/su2_haar_mean.v

   The averages over the dyadic Hopf grids of functions on SU(2)
   (`su2_grid_mean` of verification/ChallengeSU2GaugeInvariance.v) as a
   positive normalized linear functional, and their limit.

     - algebra of the grid averages: linearity, monotonicity, bounds,
       exchange of two averages;
     - `gmean_refine`: the averages of the levels n and n + m of a function
       that varies by at most eps over delta-close points differ by at most
       eps, as soon as n >= n0(delta) -- uniformly in the function;
     - `haar_exists`: the averages of a bounded uniformly continuous
       function converge; `haar_approx`: uniform rate;
     - the Euclidean inner product `qdot` of quaternions and elementary
       isometries of S^3 (`swap12`, `rot01`, `rot23`).

   Zero Axiom / Parameter / Admitted declarations.
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
Require Import ym.su2_haar_grid.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeSU2Gauge ChallengeSU2GaugeInvariance.
Import DupClustering SU2Algebra SU2HaarGrid.
Open Scope R_scope.

Module SU2HaarMean.

  Notation gmean := su2_grid_mean.
  Notation fn_bc := su2_fn_bounded_continuous.
  Notation haar_lim := su2_haar_integral_is.

  (* =======================================================================
     1. Quaternions as vectors of R^4
     ======================================================================= *)

  (* the Euclidean inner product; for unit quaternions, (1/2) tr (p q^{-1}) *)
  Definition qdot (p q : Quat) : R :=
    qr p * qr q + qi p * qi q + qj p * qj q + qk p * qk q.

  (* monomials in the four coordinates *)
  Definition mono (a b c d : nat) (q : Quat) : R :=
    qr q ^ a * qi q ^ b * qj q ^ c * qk q ^ d.

  (* exchange of the second and third coordinates *)
  Definition swap12 (q : Quat) : Quat := mkQuat (qr q) (qj q) (qi q) (qk q).

  (* rotation by the angle t in the plane of the first two coordinates,
     and in the plane of the last two *)
  Definition rot01 (t : R) (q : Quat) : Quat :=
    mkQuat (cos t * qr q - sin t * qi q) (sin t * qr q + cos t * qi q) (qj q) (qk q).

  Definition rot23 (t : R) (q : Quat) : Quat :=
    mkQuat (qr q) (qi q) (cos t * qj q - sin t * qk q) (sin t * qj q + cos t * qk q).

  Lemma close_sym : forall d p q, su2_close d p q -> su2_close d q p.
  Proof.
    intros d p q (H1 & H2 & H3 & H4). unfold su2_close.
    rewrite (Rabs_minus_sym (qr q)), (Rabs_minus_sym (qi q)),
            (Rabs_minus_sym (qj q)), (Rabs_minus_sym (qk q)).
    repeat split; assumption.
  Qed.

  Lemma close_dec : forall d p q, {su2_close d p q} + {~ su2_close d p q}.
  Proof.
    intros d p q. unfold su2_close.
    destruct (Rlt_dec (Rabs (qr p - qr q)) d) as [H1 | H1];
      [| right; intros (K & _); exact (H1 K)].
    destruct (Rlt_dec (Rabs (qi p - qi q)) d) as [H2 | H2];
      [| right; intros (_ & K & _); exact (H2 K)].
    destruct (Rlt_dec (Rabs (qj p - qj q)) d) as [H3 | H3];
      [| right; intros (_ & _ & K & _); exact (H3 K)].
    destruct (Rlt_dec (Rabs (qk p - qk q)) d) as [H4 | H4];
      [| right; intros (_ & _ & _ & K); exact (H4 K)].
    left. repeat split; assumption.
  Qed.

  Lemma qdot_sym : forall p q, qdot p q = qdot q p.
  Proof. intros p q. unfold qdot. ring. Qed.

  Lemma qdot_bounds : forall p q, su2_unit p -> su2_unit q -> -1 <= qdot p q <= 1.
  Proof.
    intros [a b c d] [a' b' c' d']. unfold su2_unit, qnorm2, qdot.
    cbn [qr qi qj qk]. intros Hp Hq.
    pose proof (Rle_0_sqr (a - a')). pose proof (Rle_0_sqr (b - b')).
    pose proof (Rle_0_sqr (c - c')). pose proof (Rle_0_sqr (d - d')).
    pose proof (Rle_0_sqr (a + a')). pose proof (Rle_0_sqr (b + b')).
    pose proof (Rle_0_sqr (c + c')). pose proof (Rle_0_sqr (d + d')).
    unfold Rsqr in *. split; nra.
  Qed.

  Lemma sq_ge_of_abs : forall x d, 0 < d -> ~ Rabs x < d -> d * d <= x * x.
  Proof.
    intros x d Hd H. apply Rnot_lt_le in H. unfold Rabs in H.
    destruct (Rcase_abs x); nra.
  Qed.

  (* far points have a small inner product *)
  Lemma qdot_far : forall d p q, 0 < d -> su2_unit p -> su2_unit q ->
    ~ su2_close d p q -> qdot p q <= 1 - d * d / 2.
  Proof.
    intros d [a b c e] [a' b' c' e'] Hd Hp Hq Hn.
    unfold su2_unit, qnorm2 in Hp, Hq. unfold qdot, su2_close in *.
    cbn [qr qi qj qk] in *.
    pose proof (Rle_0_sqr (a - a')) as S1. pose proof (Rle_0_sqr (b - b')) as S2.
    pose proof (Rle_0_sqr (c - c')) as S3. pose proof (Rle_0_sqr (e - e')) as S4.
    unfold Rsqr in *.
    assert (Hbig : d * d <= (a - a') * (a - a') + (b - b') * (b - b')
                           + (c - c') * (c - c') + (e - e') * (e - e')).
    { destruct (Rlt_dec (Rabs (a - a')) d) as [H1 | H1];
        [| pose proof (sq_ge_of_abs _ d Hd H1); lra].
      destruct (Rlt_dec (Rabs (b - b')) d) as [H2 | H2];
        [| pose proof (sq_ge_of_abs _ d Hd H2); lra].
      destruct (Rlt_dec (Rabs (c - c')) d) as [H3 | H3];
        [| pose proof (sq_ge_of_abs _ d Hd H3); lra].
      destruct (Rlt_dec (Rabs (e - e')) d) as [H4 | H4];
        [| pose proof (sq_ge_of_abs _ d Hd H4); lra].
      exfalso. apply Hn. repeat split; assumption. }
    nra.
  Qed.

  (* the inner product with a unit vector is Lipschitz *)
  Lemma qdot_close : forall d p p' q, su2_unit q -> su2_close d p p' ->
    Rabs (qdot p q - qdot p' q) <= 4 * d.
  Proof.
    intros d p p' q Hq (H1 & H2 & H3 & H4).
    destruct (unit_components q Hq) as (C1 & C2 & C3 & C4).
    unfold qdot.
    replace (qr p * qr q + qi p * qi q + qj p * qj q + qk p * qk q
             - (qr p' * qr q + qi p' * qi q + qj p' * qj q + qk p' * qk q))
      with ((qr p - qr p') * qr q + (qi p - qi p') * qi q
            + (qj p - qj p') * qj q + (qk p - qk p') * qk q) by ring.
    assert (E : forall x y, Rabs x < d -> -1 <= y <= 1 -> Rabs (x * y) <= d).
    { intros x y Hx Hy. rewrite Rabs_mult.
      assert (Rabs y <= 1) by (apply Rabs_le; lra).
      pose proof (Rabs_pos x). pose proof (Rabs_pos y). nra. }
    pose proof (E _ _ H1 C1). pose proof (E _ _ H2 C2).
    pose proof (E _ _ H3 C3). pose proof (E _ _ H4 C4).
    eapply Rle_trans; [apply Rabs_triang |].
    eapply Rle_trans; [apply Rplus_le_compat_r; apply Rabs_triang |].
    eapply Rle_trans;
      [apply Rplus_le_compat_r; apply Rplus_le_compat_r; apply Rabs_triang |].
    lra.
  Qed.

  (* =======================================================================
     2. Algebra of the grid averages
     ======================================================================= *)

  Lemma gmean_rsum : forall n (h : Quat -> R),
    gmean n h = rsum (su2_grid n) h / INR (length (su2_grid n)).
  Proof. reflexivity. Qed.

  Lemma gmean_mean : forall n (h : Quat -> R),
    gmean n h =
    mean (2 ^ n) (fun i => mean (2 ^ n) (fun j => mean (2 ^ n) (fun k =>
      h (gpt (2 ^ n) i j k)))).
  Proof.
    intros n h. rewrite gmean_rsum, grid_gridN. apply gridN_mean. apply pow2_pos.
  Qed.

  Lemma grid_point_unit : forall n u, In u (su2_grid n) -> su2_unit u.
  Proof. intros n u Hu. exact (proj1 (Forall_forall _ _) (grid_unit n) u Hu). Qed.

  Lemma gmean_ext : forall n (h h' : Quat -> R),
    (forall u, su2_unit u -> h u = h' u) -> gmean n h = gmean n h'.
  Proof.
    intros n h h' H. rewrite !gmean_rsum. unfold Rdiv. apply Rmult_eq_compat_r.
    apply rsum_ext. intros u Hu. apply H. exact (grid_point_unit n u Hu).
  Qed.

  Lemma gmean_bounds : forall n (h : Quat -> R) a b,
    (forall u, su2_unit u -> a <= h u <= b) -> a <= gmean n h <= b.
  Proof.
    intros n h a b H. rewrite gmean_mean.
    apply mean_bounds; [apply pow2_pos |]. intros i Hi.
    apply mean_bounds; [apply pow2_pos |]. intros j Hj.
    apply mean_bounds; [apply pow2_pos |]. intros k Hk.
    apply H. apply gpt_unit. exact Hi.
  Qed.

  Lemma gmean_plus : forall n (h h' : Quat -> R),
    gmean n (fun u => h u + h' u) = gmean n h + gmean n h'.
  Proof.
    intros n h h'. rewrite !gmean_rsum, rsum_plus. unfold Rdiv. ring.
  Qed.

  Lemma gmean_scal : forall n c (h : Quat -> R),
    gmean n (fun u => c * h u) = c * gmean n h.
  Proof.
    intros n c h. rewrite !gmean_rsum, rsum_scal. unfold Rdiv. ring.
  Qed.

  Lemma gmean_minus : forall n (h h' : Quat -> R),
    gmean n (fun u => h u - h' u) = gmean n h - gmean n h'.
  Proof.
    intros n h h'. rewrite !gmean_rsum, rsum_minus. unfold Rdiv. ring.
  Qed.

  Lemma gmean_const : forall n c, gmean n (fun _ => c) = c.
  Proof.
    intros n c.
    pose proof (gmean_bounds n (fun _ => c) c c (fun _ _ => conj (Rle_refl c) (Rle_refl c))).
    lra.
  Qed.

  Lemma gmean_le : forall n (h h' : Quat -> R),
    (forall u, su2_unit u -> h u <= h' u) -> gmean n h <= gmean n h'.
  Proof.
    intros n h h' H. rewrite !gmean_rsum. unfold Rdiv.
    apply Rmult_le_compat_r.
    - left. apply Rinv_0_lt_compat. apply grid_length_pos.
    - apply rsum_le. intros u Hu. apply H. exact (grid_point_unit n u Hu).
  Qed.

  Lemma abs_le_inv : forall x a : R, Rabs x <= a -> - a <= x <= a.
  Proof. intros x a H. unfold Rabs in H. destruct (Rcase_abs x); lra. Qed.

  Lemma gmean_close : forall n (h h' : Quat -> R) eps,
    (forall u, su2_unit u -> Rabs (h u - h' u) <= eps) ->
    Rabs (gmean n h - gmean n h') <= eps.
  Proof.
    intros n h h' eps H. rewrite <- gmean_minus. apply Rabs_le.
    apply (gmean_bounds n (fun u => h u - h' u) (- eps) eps).
    intros u Hu. apply abs_le_inv. apply H. exact Hu.
  Qed.

  Lemma gmean_abs_le : forall n (h : Quat -> R) M,
    (forall u, su2_unit u -> Rabs (h u) <= M) -> Rabs (gmean n h) <= M.
  Proof.
    intros n h M H. apply Rabs_le. apply (gmean_bounds n h (- M) M).
    intros u Hu. apply abs_le_inv. apply H. exact Hu.
  Qed.

  (* two grid averages commute *)
  Lemma gmean_swap : forall n m (Phi : Quat -> Quat -> R),
    gmean n (fun x => gmean m (fun y => Phi x y)) =
    gmean m (fun y => gmean n (fun x => Phi x y)).
  Proof.
    intros n m Phi. rewrite (gmean_rsum n), (gmean_rsum m).
    unfold su2_grid_mean, Rdiv.
    change (fun x : Quat => fold_right Rplus 0 (map (fun y : Quat => Phi x y) (su2_grid m))
                            * / INR (length (su2_grid m)))
      with (fun x : Quat => rsum (su2_grid m) (fun y => Phi x y)
                            * / INR (length (su2_grid m))).
    change (fun y : Quat => fold_right Rplus 0 (map (fun x : Quat => Phi x y) (su2_grid n))
                            * / INR (length (su2_grid n)))
      with (fun y : Quat => rsum (su2_grid n) (fun x => Phi x y)
                            * / INR (length (su2_grid n))).
    rewrite !rsum_scal_r, (rsum_swap (su2_grid n) (su2_grid m) Phi). ring.
  Qed.

  (* =======================================================================
     3. Refinement: the uniform Cauchy property
     ======================================================================= *)

  Lemma gmean_refine : forall delta, 0 < delta ->
    exists n0 : nat, forall (n m : nat) (h : Quat -> R) (eps : R),
      (n0 <= n)%nat ->
      (forall u v, su2_unit u -> su2_unit v -> su2_close delta u v ->
         Rabs (h u - h v) <= eps) ->
      Rabs (gmean (n + m) h - gmean n h) <= eps.
  Proof.
    intros delta Hd. destruct (hopf_modulus delta Hd) as [n0 Hn0].
    exists n0. intros n m h eps Hn Hh.
    rewrite !gmean_mean, Nat.pow_add_r.
    pose proof (pow2_pos n) as HN. pose proof (pow2_pos m) as HM.
    apply mean_refine; [exact HN | exact HM |]. intros i r1 Hi Hr1.
    apply mean_refine; [exact HN | exact HM |]. intros j r2 Hj Hr2.
    apply mean_refine; [exact HN | exact HM |]. intros k r3 Hk Hr3.
    apply Hh.
    - apply gpt_unit. nia.
    - apply gpt_unit. exact Hi.
    - apply close_sym. apply (Hn0 n m i j k r1 r2 r3); assumption.
  Qed.

  (* =======================================================================
     4. The limit of the grid averages
     ======================================================================= *)

  Lemma cv_ext0 : forall (u u' : nat -> R) (l : R),
    (forall n, u n = u' n) -> Un_cv u l -> Un_cv u' l.
  Proof.
    intros u u' l H Hu eps He. destruct (Hu eps He) as [N HN].
    exists N. intros n Hn. rewrite <- H. apply HN. exact Hn.
  Qed.

  Lemma haar_unique : forall (h : Quat -> R) v v',
    haar_lim h v -> haar_lim h v' -> v = v'.
  Proof. intros h v v' H H'. exact (UL_sequence _ _ _ H H'). Qed.

  Lemma haar_ext : forall (h h' : Quat -> R) v,
    (forall u, su2_unit u -> h u = h' u) -> haar_lim h v -> haar_lim h' v.
  Proof.
    intros h h' v H Hv. apply (cv_ext0 (fun n => gmean n h)); [| exact Hv].
    intro n. apply gmean_ext. exact H.
  Qed.

  Lemma haar_const : forall c, haar_lim (fun _ => c) c.
  Proof.
    intros c eps He. exists 0%nat. intros n _. rewrite gmean_const.
    unfold R_dist. replace (c - c) with 0 by ring. rewrite Rabs_R0. exact He.
  Qed.

  Lemma haar_plus : forall (h h' : Quat -> R) v v',
    haar_lim h v -> haar_lim h' v' -> haar_lim (fun u => h u + h' u) (v + v').
  Proof.
    intros h h' v v' H H'.
    apply (cv_ext0 (fun n => gmean n h + gmean n h')).
    - intro n. symmetry. apply gmean_plus.
    - exact (CV_plus _ _ _ _ H H').
  Qed.

  Lemma haar_scal : forall c (h : Quat -> R) v,
    haar_lim h v -> haar_lim (fun u => c * h u) (c * v).
  Proof.
    intros c h v H.
    apply (cv_ext0 (fun n => c * gmean n h)).
    - intro n. symmetry. apply gmean_scal.
    - apply (CV_mult (fun _ => c) (fun n => gmean n h) c v); [| exact H].
      intros eps He. exists 0%nat. intros n _. unfold R_dist.
      replace (c - c) with 0 by ring. rewrite Rabs_R0. exact He.
  Qed.

  Lemma cv_bounds0 : forall (u : nat -> R) l a b,
    Un_cv u l -> (forall n, a <= u n <= b) -> a <= l <= b.
  Proof.
    intros u l a b Hu H. split.
    - apply Rnot_lt_le. intro Hlt.
      destruct (Hu (a - l) ltac:(lra)) as [N HN].
      specialize (HN N (le_n N)). unfold R_dist in HN.
      apply Rabs_def2 in HN. specialize (H N). lra.
    - apply Rnot_lt_le. intro Hlt.
      destruct (Hu (l - b) ltac:(lra)) as [N HN].
      specialize (HN N (le_n N)). unfold R_dist in HN.
      apply Rabs_def2 in HN. specialize (H N). lra.
  Qed.

  Lemma haar_bounds : forall (h : Quat -> R) v a b,
    haar_lim h v -> (forall u, su2_unit u -> a <= h u <= b) -> a <= v <= b.
  Proof.
    intros h v a b Hv H. apply (cv_bounds0 (fun n => gmean n h)); [exact Hv |].
    intro n. apply gmean_bounds. exact H.
  Qed.

  (* weak-inequality form of the modulus of continuity *)
  Lemma fn_bc_modulus : forall h : Quat -> R, fn_bc h ->
    forall eps, 0 < eps -> exists delta, 0 < delta /\
      forall u v, su2_unit u -> su2_unit v -> su2_close delta u v ->
        Rabs (h u - h v) <= eps.
  Proof.
    intros h [_ Hc] eps He. destruct (Hc eps He) as [delta [Hd H]].
    exists delta. split; [exact Hd |]. intros u v Hu Hv Hcl. left. apply H; assumption.
  Qed.

  Theorem haar_exists : forall h : Quat -> R, fn_bc h -> exists v : R, haar_lim h v.
  Proof.
    intros h Hh.
    assert (HC : Cauchy_crit (fun n => gmean n h)).
    { intros eps He.
      destruct (fn_bc_modulus h Hh (eps / 3) ltac:(lra)) as [delta [Hd Hm]].
      destruct (gmean_refine delta Hd) as [n0 Hn0].
      exists n0. intros n m Hn Hm'. unfold R_dist.
      assert (E : forall k, (k >= n0)%nat -> Rabs (gmean k h - gmean n0 h) <= eps / 3).
      { intros k Hk. replace k with (n0 + (k - n0))%nat by lia.
        apply (Hn0 n0 (k - n0)%nat h (eps / 3) (le_n n0) Hm). }
      pose proof (E n Hn) as E1. pose proof (E m Hm') as E2.
      replace (gmean n h - gmean m h)
        with ((gmean n h - gmean n0 h) - (gmean m h - gmean n0 h)) by ring.
      eapply Rle_lt_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
    destruct (R_complete _ HC) as [v Hv]. exists v. exact Hv.
  Qed.

  (* uniform rate of convergence over an equicontinuous family *)
  Lemma haar_approx : forall delta, 0 < delta ->
    exists n0 : nat, forall (n : nat) (h : Quat -> R) (eps v : R),
      (n0 <= n)%nat ->
      (forall u w, su2_unit u -> su2_unit w -> su2_close delta u w ->
         Rabs (h u - h w) <= eps) ->
      haar_lim h v ->
      Rabs (gmean n h - v) <= eps.
  Proof.
    intros delta Hd. destruct (gmean_refine delta Hd) as [n0 Hn0].
    exists n0. intros n h eps v Hn Hm Hv.
    apply Rnot_lt_le. intro Hlt.
    set (eta := Rabs (gmean n h - v) - eps) in *.
    assert (Heta : 0 < eta) by (unfold eta; lra).
    destruct (Hv eta Heta) as [N HN].
    specialize (HN (n + N)%nat ltac:(lia)). unfold R_dist in HN.
    pose proof (Hn0 n N h eps Hn Hm) as H1.
    assert (H2 : Rabs (gmean n h - v) <= Rabs (gmean (n + N) h - gmean n h)
                                         + Rabs (gmean (n + N) h - v)).
    { replace (gmean n h - v)
        with (- (gmean (n + N) h - gmean n h) + (gmean (n + N) h - v)) by ring.
      eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. lra. }
    unfold eta in HN. lra.
  Qed.

  (* =======================================================================
     5. Bounded uniformly continuous functions on SU(2)
     ======================================================================= *)

  Lemma fn_bc_const : forall c : R, fn_bc (fun _ => c).
  Proof.
    intro c. split.
    - exists (Rabs c). intros u _. apply Rle_refl.
    - intros eps He. exists 1. split; [lra |]. intros u v _ _ _.
      replace (c - c) with 0 by ring. rewrite Rabs_R0. exact He.
  Qed.

  Lemma fn_bc_qr : fn_bc qr.
  Proof.
    split.
    - exists 1. intros u Hu. apply Rabs_le. exact (proj1 (unit_components u Hu)).
    - intros eps He. exists eps. split; [exact He |].
      intros u v _ _ (H & _). exact H.
  Qed.

  Lemma fn_bc_qi : fn_bc qi.
  Proof.
    split.
    - exists 1. intros u Hu. apply Rabs_le.
      exact (proj1 (proj2 (unit_components u Hu))).
    - intros eps He. exists eps. split; [exact He |].
      intros u v _ _ (_ & H & _). exact H.
  Qed.

  Lemma fn_bc_qj : fn_bc qj.
  Proof.
    split.
    - exists 1. intros u Hu. apply Rabs_le.
      exact (proj1 (proj2 (proj2 (unit_components u Hu)))).
    - intros eps He. exists eps. split; [exact He |].
      intros u v _ _ (_ & _ & H & _). exact H.
  Qed.

  Lemma fn_bc_qk : fn_bc qk.
  Proof.
    split.
    - exists 1. intros u Hu. apply Rabs_le.
      exact (proj2 (proj2 (proj2 (unit_components u Hu)))).
    - intros eps He. exists eps. split; [exact He |].
      intros u v _ _ (_ & _ & _ & H). exact H.
  Qed.

  Lemma fn_bc_ext : forall h h' : Quat -> R,
    (forall u, su2_unit u -> h u = h' u) -> fn_bc h -> fn_bc h'.
  Proof.
    intros h h' E [[M HM] Hc]. split.
    - exists M. intros u Hu. rewrite <- (E u Hu). apply HM. exact Hu.
    - intros eps He. destruct (Hc eps He) as [delta [Hd H]].
      exists delta. split; [exact Hd |]. intros u v Hu Hv Hcl.
      rewrite <- (E u Hu), <- (E v Hv). apply H; assumption.
  Qed.

  Lemma fn_bc_plus : forall h h' : Quat -> R,
    fn_bc h -> fn_bc h' -> fn_bc (fun u => h u + h' u).
  Proof.
    intros h h' [[M HM] Hc] [[M' HM'] Hc']. split.
    - exists (M + M'). intros u Hu.
      eapply Rle_trans; [apply Rabs_triang |].
      apply Rplus_le_compat; [apply HM | apply HM']; exact Hu.
    - intros eps He.
      destruct (Hc (eps / 2) ltac:(lra)) as [d [Hd H]].
      destruct (Hc' (eps / 2) ltac:(lra)) as [d' [Hd' H']].
      exists (Rmin d d'). split; [apply Rmin_pos; assumption |].
      intros u v Hu Hv Hcl.
      replace (h u + h' u - (h v + h' v)) with ((h u - h v) + (h' u - h' v)) by ring.
      eapply Rle_lt_trans; [apply Rabs_triang |].
      assert (C1 : su2_close d u v).
      { destruct Hcl as (K1 & K2 & K3 & K4). pose proof (Rmin_l d d').
        unfold su2_close. repeat split; lra. }
      assert (C2 : su2_close d' u v).
      { destruct Hcl as (K1 & K2 & K3 & K4). pose proof (Rmin_r d d').
        unfold su2_close. repeat split; lra. }
      pose proof (H u v Hu Hv C1). pose proof (H' u v Hu Hv C2). lra.
  Qed.

  Lemma fn_bc_scal : forall c (h : Quat -> R), fn_bc h -> fn_bc (fun u => c * h u).
  Proof.
    intros c h [[M HM] Hc]. split.
    - exists (Rabs c * M). intros u Hu. rewrite Rabs_mult.
      apply Rmult_le_compat_l; [apply Rabs_pos | apply HM; exact Hu].
    - intros eps He.
      destruct (Hc (eps / (Rabs c + 1))) as [d [Hd H]].
      { apply Rdiv_lt_0_compat; [exact He |]. pose proof (Rabs_pos c). lra. }
      exists d. split; [exact Hd |]. intros u v Hu Hv Hcl.
      replace (c * h u - c * h v) with (c * (h u - h v)) by ring.
      rewrite Rabs_mult. pose proof (H u v Hu Hv Hcl) as K.
      pose proof (Rabs_pos c) as Pc. pose proof (Rabs_pos (h u - h v)) as Ph.
      assert (E : eps = (Rabs c + 1) * (eps / (Rabs c + 1))) by (field; lra).
      rewrite E. apply Rle_lt_trans with (Rabs c * (eps / (Rabs c + 1))).
      + apply Rmult_le_compat_l; [exact Pc | lra].
      + assert (0 < eps / (Rabs c + 1)) by (apply Rdiv_lt_0_compat; lra). nra.
  Qed.

  Lemma fn_bc_mult : forall h h' : Quat -> R,
    fn_bc h -> fn_bc h' -> fn_bc (fun u => h u * h' u).
  Proof.
    intros h h' [[M HM] Hc] [[M' HM'] Hc']. split.
    - exists (Rabs M * Rabs M'). intros u Hu. rewrite Rabs_mult.
      apply Rmult_le_compat; try apply Rabs_pos.
      + eapply Rle_trans; [apply HM; exact Hu | apply Rle_abs].
      + eapply Rle_trans; [apply HM'; exact Hu | apply Rle_abs].
    - intros eps He.
      set (K := Rabs M + Rabs M' + 1).
      assert (HK : 0 < K) by (unfold K; pose proof (Rabs_pos M); pose proof (Rabs_pos M'); lra).
      destruct (Hc (eps / (2 * K))) as [d [Hd H]].
      { apply Rdiv_lt_0_compat; lra. }
      destruct (Hc' (eps / (2 * K))) as [d' [Hd' H']].
      { apply Rdiv_lt_0_compat; lra. }
      exists (Rmin d d'). split; [apply Rmin_pos; assumption |].
      intros u v Hu Hv Hcl.
      assert (C1 : su2_close d u v).
      { destruct Hcl as (K1 & K2 & K3 & K4). pose proof (Rmin_l d d').
        unfold su2_close. repeat split; lra. }
      assert (C2 : su2_close d' u v).
      { destruct Hcl as (K1 & K2 & K3 & K4). pose proof (Rmin_r d d').
        unfold su2_close. repeat split; lra. }
      pose proof (H u v Hu Hv C1) as E1. pose proof (H' u v Hu Hv C2) as E2.
      replace (h u * h' u - h v * h' v)
        with (h u * (h' u - h' v) + h' v * (h u - h v)) by ring.
      eapply Rle_lt_trans; [apply Rabs_triang |]. rewrite !Rabs_mult.
      assert (B1 : Rabs (h u) <= K).
      { eapply Rle_trans; [apply HM; exact Hu |]. unfold K.
        pose proof (Rle_abs M). pose proof (Rabs_pos M'). lra. }
      assert (B2 : Rabs (h' v) <= K).
      { eapply Rle_trans; [apply HM'; exact Hv |]. unfold K.
        pose proof (Rle_abs M'). pose proof (Rabs_pos M). lra. }
      pose proof (Rabs_pos (h u)). pose proof (Rabs_pos (h' v)).
      pose proof (Rabs_pos (h u - h v)). pose proof (Rabs_pos (h' u - h' v)).
      assert (E : eps = K * (eps / (2 * K)) + K * (eps / (2 * K))) by (field; lra).
      assert (P : 0 < eps / (2 * K)) by (apply Rdiv_lt_0_compat; lra).
      rewrite E. apply Rplus_le_lt_compat.
      + apply Rmult_le_compat; lra.
      + apply Rle_lt_trans with (K * Rabs (h u - h v)).
        * apply Rmult_le_compat_r; lra.
        * apply Rmult_lt_compat_l; lra.
  Qed.

  Lemma fn_bc_pow : forall (h : Quat -> R) k, fn_bc h -> fn_bc (fun u => h u ^ k).
  Proof.
    intros h k Hh. induction k as [| k IH].
    - exact (fn_bc_const 1).
    - exact (fn_bc_mult h (fun u => h u ^ k) Hh IH).
  Qed.

  Lemma fn_bc_mono : forall a b c d, fn_bc (mono a b c d).
  Proof.
    intros a b c d. unfold mono.
    apply fn_bc_mult; [apply fn_bc_mult; [apply fn_bc_mult |] |].
    - exact (fn_bc_pow qr a fn_bc_qr).
    - exact (fn_bc_pow qi b fn_bc_qi).
    - exact (fn_bc_pow qj c fn_bc_qj).
    - exact (fn_bc_pow qk d fn_bc_qk).
  Qed.

End SU2HaarMean.
