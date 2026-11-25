(* =========================================================================
   ym/su2_haar_invariance.v

   The limit of the Hopf-grid averages is the Haar measure of SU(2): it is
   invariant under every isometry of S^3, in particular under left and
   right translations and under inversion (TARGET 11a).

   Proof.  Let kap k x y = ((1 + <x, y>) / 2) ^ k.  Its Haar integral N_k
   over x does not depend on the unit quaternion y (ym/su2_haar_poly.v),
   and N_k >= c * theta ^ k because a neighbourhood of 1 carries a positive
   fraction of the grid (ym/su2_haar_orbit.v), while kap k x y <= rho ^ k
   with rho < theta when x and y are not delta-close.  Hence the kernel
   kap k / N_k is an approximate identity: for a function h that varies by
   at most eps over delta-close points,
       | avg_y h(y) kap k x y  -  h(x) N_k |  <=  (small) * N_k
   uniformly in x.  For an isometry g with adjoint g',
       avg_x avg_y h(y) kap k (g x) y
   is on the one hand close to N_k avg_x h(g x) (apply the above at g x),
   and on the other hand, exchanging the two finite averages and using
   <g x, y> = <x, g' y>, close to N_k avg_y h(y).  All estimates are
   uniform in h (given its bound and its modulus) and in g.

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
Require Import ym.su2_continuity.
Require Import ym.su2_haar_grid.
Require Import ym.su2_haar_mean.
Require Import ym.su2_haar_orbit.
Require Import ym.su2_haar_poly.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeSU2Gauge ChallengeSU2GaugeInvariance.
Import DupClustering SU2Algebra SU2HaarGrid SU2HaarMean SU2HaarPoly.
Open Scope R_scope.

Module SU2HaarInvariance.

  (* =======================================================================
     1. Elementary facts
     ======================================================================= *)

  Lemma pow_lip : forall (k : nat) (a b : R), 0 <= a <= 1 -> 0 <= b <= 1 ->
    Rabs (a ^ k - b ^ k) <= INR k * Rabs (a - b).
  Proof.
    induction k as [| k IH]; intros a b Ha Hb.
    - cbn [pow INR]. replace (1 - 1) with 0 by ring. rewrite Rabs_R0. lra.
    - rewrite S_INR. cbn [pow].
      replace (a * a ^ k - b * b ^ k)
        with (a * (a ^ k - b ^ k) + b ^ k * (a - b)) by ring.
      eapply Rle_trans; [apply Rabs_triang |]. rewrite !Rabs_mult.
      specialize (IH a b Ha Hb).
      assert (A1 : Rabs a <= 1) by (apply Rabs_le; lra).
      assert (B0 : 0 <= b ^ k) by (apply pow_le; lra).
      assert (B1 : b ^ k <= 1).
      { apply Rle_trans with (1 ^ k); [apply pow_incr; lra | rewrite pow1; lra]. }
      assert (B2 : Rabs (b ^ k) <= 1) by (apply Rabs_le; lra).
      pose proof (Rabs_pos (a ^ k - b ^ k)) as P1. pose proof (Rabs_pos (a - b)) as P2.
      pose proof (Rabs_pos a) as P3. pose proof (Rabs_pos (b ^ k)) as P4.
      assert (Q1 : Rabs a * Rabs (a ^ k - b ^ k) <= 1 * Rabs (a ^ k - b ^ k))
        by (apply Rmult_le_compat_r; lra).
      assert (Q2 : Rabs (b ^ k) * Rabs (a - b) <= 1 * Rabs (a - b))
        by (apply Rmult_le_compat_r; lra).
      lra.
  Qed.

  (* the kernels are equicontinuous in the first argument *)
  Lemma kap_close : forall k d x x' z,
    su2_unit x -> su2_unit x' -> su2_unit z -> su2_close d x x' ->
    Rabs (kap k x z - kap k x' z) <= INR k * (2 * d).
  Proof.
    intros k d x x' z Hx Hx' Hz Hcl. unfold kap.
    eapply Rle_trans;
      [apply pow_lip; [apply kap_base_bounds | apply kap_base_bounds]; assumption |].
    apply Rmult_le_compat_l; [apply pos_INR |].
    replace ((1 + qdot x z) / 2 - (1 + qdot x' z) / 2)
      with ((qdot x z - qdot x' z) * / 2) by field.
    rewrite Rabs_mult, (Rabs_pos_eq (/ 2)) by lra.
    pose proof (qdot_close d x x' z Hz Hcl). lra.
  Qed.

  Lemma cv_lower_from : forall (u : nat -> R) (l a : R) (N : nat),
    Un_cv u l -> (forall n, (N <= n)%nat -> a <= u n) -> a <= l.
  Proof.
    intros u l a N Hu H. apply Rnot_lt_le. intro Hlt.
    destruct (Hu (a - l) ltac:(lra)) as [N' HN'].
    specialize (HN' (Nat.max N N') (Nat.le_max_r N N')). unfold R_dist in HN'.
    apply Rabs_def2 in HN'. specialize (H (Nat.max N N') (Nat.le_max_l N N')). lra.
  Qed.

  (* domination of a grid average *)
  Lemma gmean_abs_dom : forall n (f g : Quat -> R),
    (forall u, su2_unit u -> Rabs (f u) <= g u) -> Rabs (gmean n f) <= gmean n g.
  Proof.
    intros n f g H.
    assert (H1 : gmean n f <= gmean n g).
    { apply gmean_le. intros u Hu. pose proof (abs_le_inv _ _ (H u Hu)). lra. }
    assert (H2 : gmean n (fun u => -1 * f u) <= gmean n g).
    { apply gmean_le. intros u Hu. pose proof (abs_le_inv _ _ (H u Hu)). lra. }
    rewrite gmean_scal in H2. apply Rabs_le. lra.
  Qed.

  Lemma qdot_one_r : forall u, qdot u qone = qr u.
  Proof. intro u. unfold qdot, qone. cbn [qr qi qj qk]. ring. Qed.

  (* =======================================================================
     2. The main estimate
     ======================================================================= *)

  (* the normalization N_k of the kernel dominates its mass far away *)
  Lemma kernel_setup : forall M delta eps : R,
    0 <= M -> 0 < delta <= 1 -> 0 < eps ->
    exists (k : nat) (Nk : R),
      0 < Nk /\
      haar_lim (fun x => kap k x qone) Nk /\
      2 * M * (1 - delta * delta / 4) ^ k <= eps * Nk.
  Proof.
    intros M delta eps HM [Hd0 Hd1] He.
    set (rho := 1 - delta * delta / 4).
    set (theta := 1 - delta * delta / 16).
    assert (Hdd : 0 < delta * delta <= 1) by nra.
    assert (Hrho : 0 < rho < theta) by (unfold rho, theta; lra).
    assert (Htheta : 0 < theta <= 1) by (unfold theta; lra).
    destruct (SU2HaarOrbit.cap_positive (delta * delta / 8) ltac:(lra)) as [c [n0 [Hc Hcap]]].
    assert (Hratio : Rabs (rho / theta) < 1).
    { rewrite Rabs_pos_eq.
      - apply Rmult_lt_reg_r with theta; [lra |].
        unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
      - apply Rmult_le_pos; [lra |]. left. apply Rinv_0_lt_compat. lra. }
    assert (Hy : 0 < eps * c / (2 * M + 1)).
    { apply Rdiv_lt_0_compat; [apply Rmult_lt_0_compat; lra | lra]. }
    destruct (pow_lt_1_zero (rho / theta) Hratio _ Hy) as [k Hk].
    specialize (Hk k (le_n k)).
    assert (Htk : 0 < theta ^ k) by (apply pow_lt; lra).
    assert (Hrk : 0 <= rho ^ k) by (apply pow_le; lra).
    assert (Hpow : rho ^ k < eps * c / (2 * M + 1) * theta ^ k).
    { unfold Rdiv in Hk at 1. rewrite Rpow_mult_distr, pow_inv in Hk.
      rewrite Rabs_pos_eq in Hk.
      - apply Rmult_lt_reg_r with (/ theta ^ k); [apply Rinv_0_lt_compat; exact Htk |].
        rewrite (Rmult_assoc _ (theta ^ k)), Rinv_r by lra. lra.
      - apply Rmult_le_pos; [exact Hrk |]. left. apply Rinv_0_lt_compat. exact Htk. }
    destruct (haar_exists (fun x => kap k x qone) (kap_fn_bc k qone)) as [Nk HNk].
    assert (Hlow : c * theta ^ k <= Nk).
    { apply (cv_lower_from (fun n => gmean n (fun x => kap k x qone)) Nk _ n0 HNk).
      intros n Hn.
      pose proof (Hcap n (fun u => / theta ^ k * kap k u qone) Hn) as Hc1.
      rewrite gmean_scal in Hc1.
      assert (Hc2 : c <= / theta ^ k * gmean n (fun x => kap k x qone)).
      { apply Hc1.
        - intros u Hu. apply Rmult_le_pos.
          + left. apply Rinv_0_lt_compat. exact Htk.
          + exact (proj1 (kap_bounds k u qone Hu unit_one)).
        - intros u Hu (Hcl & _). cbn [qr qone] in Hcl.
          apply Rabs_def2 in Hcl.
          assert (Hb : theta <= (1 + qdot u qone) / 2).
          { rewrite qdot_one_r. unfold theta. lra. }
          assert (Hk1 : theta ^ k <= kap k u qone).
          { unfold kap. apply pow_incr. lra. }
          apply Rmult_le_reg_l with (theta ^ k); [exact Htk |].
          rewrite <- Rmult_assoc, Rinv_r, Rmult_1_l by lra. lra. }
      apply Rmult_le_reg_l with (/ theta ^ k); [apply Rinv_0_lt_compat; exact Htk |].
      rewrite (Rmult_comm c), <- Rmult_assoc, Rinv_l, Rmult_1_l by lra. exact Hc2. }
    exists k, Nk.
    assert (HNk0 : 0 < Nk).
    { apply Rlt_le_trans with (c * theta ^ k); [apply Rmult_lt_0_compat; lra | exact Hlow]. }
    split; [exact HNk0 |]. split; [exact HNk |]. fold rho.
    assert (E1 : (2 * M + 1) * rho ^ k < eps * c * theta ^ k).
    { apply Rmult_lt_reg_l with (/ (2 * M + 1)); [apply Rinv_0_lt_compat; lra |].
      rewrite <- Rmult_assoc, Rinv_l, Rmult_1_l by lra.
      unfold Rdiv in Hpow. lra. }
    assert (E2 : eps * (c * theta ^ k) <= eps * Nk)
      by (apply Rmult_le_compat_l; lra).
    nra.
  Qed.

  (* TARGET 11a, uniform form *)
  Theorem haar_isometry_uniform : forall M delta eps : R,
    0 <= M -> 0 < delta -> 0 < eps ->
    exists n1 : nat, forall (n m : nat) (g g' : Quat -> Quat) (h : Quat -> R),
      (n1 <= n)%nat -> (n1 <= m)%nat ->
      (forall x, su2_unit x -> su2_unit (g x)) ->
      (forall y, su2_unit y -> su2_unit (g' y)) ->
      (forall x y, su2_unit x -> su2_unit y -> qdot (g x) y = qdot x (g' y)) ->
      (forall u, su2_unit u -> Rabs (h u) <= M) ->
      (forall u v, su2_unit u -> su2_unit v -> su2_close delta u v ->
         Rabs (h u - h v) <= eps) ->
      Rabs (gmean n (fun x => h (g x)) - gmean m h) <= (2 * M + 3) * eps.
  Proof.
    intros M delta eps HM Hd He.
    set (d1 := Rmin delta 1).
    assert (Hd1 : 0 < d1 <= 1).
    { unfold d1. split; [apply Rmin_pos; lra | apply Rmin_r]. }
    assert (Hd1d : d1 <= delta) by (unfold d1; apply Rmin_l).
    destruct (kernel_setup M d1 eps HM Hd1 He) as [k [Nk [HNk0 [HNk Hsmall]]]].
    set (rho := 1 - d1 * d1 / 4) in *.
    assert (Hrho0 : 0 <= rho) by (unfold rho; nra).
    assert (Hrk : 0 <= rho ^ k) by (apply pow_le; exact Hrho0).
    set (e' := Nk * Rmin eps 1).
    assert (Hmin : 0 < Rmin eps 1 <= 1) by (split; [apply Rmin_pos; lra | apply Rmin_r]).
    assert (Hmin2 : Rmin eps 1 <= eps) by apply Rmin_l.
    assert (He' : 0 < e') by (unfold e'; apply Rmult_lt_0_compat; lra).
    assert (He'1 : e' <= Nk) by (unfold e'; nra).
    assert (He'2 : e' <= Nk * eps) by (unfold e'; apply Rmult_le_compat_l; lra).
    set (dk := e' / (2 * INR k + 1)).
    pose proof (pos_INR k) as Hk0.
    assert (Hdk : 0 < dk) by (unfold dk; apply Rdiv_lt_0_compat; lra).
    destruct (haar_approx dk Hdk) as [n1 Hn1]. exists n1.
    intros n m g g' h Hn Hm Hg Hg' Hadj Hbd Hmod.
    (* the kernel averages are uniformly close to N_k *)
    assert (HD : forall j z, (n1 <= j)%nat -> su2_unit z ->
              Rabs (gmean j (fun x => kap k x z) - Nk) <= e').
    { intros j z Hj Hz.
      destruct (haar_exists (fun x => kap k x z) (kap_fn_bc k z)) as [vz Hvz].
      assert (E : vz = Nk) by exact (kernel_const k z vz Nk Hz Hvz HNk). subst vz.
      apply (Hn1 j (fun x => kap k x z) e' Nk Hj); [| exact Hvz].
      intros u w Hu Hw Hcl.
      eapply Rle_trans; [apply (kap_close k dk u w z Hu Hw Hz Hcl) |].
      unfold dk.
      replace (INR k * (2 * (e' / (2 * INR k + 1))))
        with (e' * (2 * INR k * / (2 * INR k + 1))) by (field; lra).
      apply Rle_trans with (e' * 1); [| lra].
      apply Rmult_le_compat_l; [lra |].
      apply Rmult_le_reg_r with (2 * INR k + 1); [lra |].
      rewrite Rmult_assoc, Rinv_l by lra. lra. }
    (* pointwise estimate *)
    assert (Hpt : forall x' y, su2_unit x' -> su2_unit y ->
              Rabs ((h y - h x') * kap k x' y)
              <= eps * kap k x' y + 2 * M * rho ^ k).
    { intros x' y Hx Hy. destruct (kap_bounds k x' y Hx Hy) as [K0 K1].
      rewrite Rabs_mult, (Rabs_pos_eq _ K0).
      pose proof (Rabs_pos (h y - h x')) as P.
      assert (Hc : 0 <= 2 * M * rho ^ k) by (apply Rmult_le_pos; lra).
      destruct (close_dec d1 y x') as [Hcl | Hncl].
      - assert (E : Rabs (h y - h x') <= eps).
        { apply Hmod; [exact Hy | exact Hx |].
          exact (SU2Continuity.close_mono d1 delta y x' Hd1d Hcl). }
        assert (Q : Rabs (h y - h x') * kap k x' y <= eps * kap k x' y)
          by (apply Rmult_le_compat_r; lra).
        lra.
      - assert (E : kap k x' y <= rho ^ k).
        { unfold kap. apply pow_incr. split; [exact (proj1 (kap_base_bounds x' y Hx Hy)) |].
          pose proof (qdot_far d1 y x' (proj1 Hd1) Hy Hx Hncl) as F.
          rewrite (qdot_sym x' y). unfold rho. lra. }
        assert (B : Rabs (h y - h x') <= 2 * M).
        { unfold Rminus. eapply Rle_trans; [apply Rabs_triang |].
          rewrite Rabs_Ropp. pose proof (Hbd y Hy). pose proof (Hbd x' Hx). lra. }
        assert (Q1 : Rabs (h y - h x') * kap k x' y <= 2 * M * kap k x' y)
          by (apply Rmult_le_compat_r; lra).
        assert (Q2 : 2 * M * kap k x' y <= 2 * M * rho ^ k)
          by (apply Rmult_le_compat_l; lra).
        assert (Q3 : 0 <= eps * kap k x' y) by (apply Rmult_le_pos; lra).
        lra. }
    (* smoothing at a point *)
    assert (H1 : forall x', su2_unit x' ->
              Rabs (gmean m (fun y => h y * kap k x' y) - h x' * Nk)
              <= eps * (Nk + e') + 2 * M * rho ^ k + M * e').
    { intros x' Hx.
      set (Dm := gmean m (fun y => kap k x' y)).
      assert (HDm : Rabs (Dm - Nk) <= e').
      { unfold Dm.
        rewrite (gmean_ext m (fun y => kap k x' y) (fun y => kap k y x'))
          by (intros y _; apply kap_sym).
        apply HD; assumption. }
      assert (Hdiff : Rabs (gmean m (fun y => h y * kap k x' y) - h x' * Dm)
                      <= eps * Dm + 2 * M * rho ^ k).
      { assert (E1 : gmean m (fun y => h y * kap k x' y) - h x' * Dm
                     = gmean m (fun y => (h y - h x') * kap k x' y)).
        { unfold Dm. rewrite <- gmean_scal, <- gmean_minus.
          apply gmean_ext. intros y _. ring. }
        assert (E2 : eps * Dm + 2 * M * rho ^ k
                     = gmean m (fun y => eps * kap k x' y + 2 * M * rho ^ k)).
        { unfold Dm.
          rewrite (gmean_plus m (fun y => eps * kap k x' y) (fun _ => 2 * M * rho ^ k)),
                  gmean_scal, gmean_const.
          reflexivity. }
        rewrite E1, E2. apply gmean_abs_dom. intros y Hy. apply Hpt; assumption. }
      replace (gmean m (fun y => h y * kap k x' y) - h x' * Nk)
        with ((gmean m (fun y => h y * kap k x' y) - h x' * Dm) + h x' * (Dm - Nk))
        by ring.
      eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_mult.
      pose proof (abs_le_inv _ _ HDm) as HDm'.
      assert (Q1 : eps * Dm <= eps * (Nk + e')) by (apply Rmult_le_compat_l; lra).
      assert (Q2 : Rabs (h x') * Rabs (Dm - Nk) <= M * e').
      { apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hbd; exact Hx
                               | exact HDm]. }
      lra. }
    set (A := gmean n (fun x => gmean m (fun y => h y * kap k (g x) y))).
    assert (HA1 : Rabs (A - Nk * gmean n (fun x => h (g x)))
                  <= eps * (Nk + e') + 2 * M * rho ^ k + M * e').
    { unfold A. rewrite <- gmean_scal, <- gmean_minus.
      apply gmean_abs_le. intros x Hx.
      replace (gmean m (fun y => h y * kap k (g x) y) - Nk * h (g x))
        with (gmean m (fun y => h y * kap k (g x) y) - h (g x) * Nk) by ring.
      apply H1. apply Hg. exact Hx. }
    assert (HA2 : Rabs (A - Nk * gmean m h) <= M * e').
    { unfold A. rewrite (gmean_swap n m (fun x y => h y * kap k (g x) y)).
      rewrite <- gmean_scal, <- gmean_minus.
      apply gmean_abs_le. intros y Hy. rewrite gmean_scal.
      replace (h y * gmean n (fun x => kap k (g x) y) - Nk * h y)
        with (h y * (gmean n (fun x => kap k (g x) y) - Nk)) by ring.
      rewrite Rabs_mult.
      assert (E : Rabs (gmean n (fun x => kap k (g x) y) - Nk) <= e').
      { rewrite (gmean_ext n (fun x => kap k (g x) y) (fun x => kap k x (g' y))).
        - apply HD; [exact Hn | apply Hg'; exact Hy].
        - intros x Hx. unfold kap. rewrite (Hadj x y Hx Hy). reflexivity. }
      apply Rmult_le_compat; [apply Rabs_pos | apply Rabs_pos | apply Hbd; exact Hy
                             | exact E]. }
    (* conclusion *)
    set (a := gmean n (fun x => h (g x))) in *. set (b := gmean m h) in *.
    assert (Hab : Nk * Rabs (a - b) <= Nk * ((2 * M + 3) * eps)).
    { rewrite <- (Rabs_pos_eq Nk) at 1 by lra. rewrite <- Rabs_mult.
      replace (Nk * (a - b)) with ((A - Nk * b) - (A - Nk * a)) by ring.
      unfold Rminus at 1. eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp.
      assert (Q1 : eps * (Nk + e') <= eps * (Nk + Nk)) by (apply Rmult_le_compat_l; lra).
      assert (Q2 : M * e' <= M * (Nk * eps)) by (apply Rmult_le_compat_l; lra).
      lra. }
    apply Rmult_le_reg_l with Nk; [exact HNk0 | exact Hab].
  Qed.

  (* invariance of the Haar integral under an isometry with an adjoint *)
  Theorem haar_isometry : forall (g g' : Quat -> Quat) (h : Quat -> R) (v : R),
    (forall x, su2_unit x -> su2_unit (g x)) ->
    (forall y, su2_unit y -> su2_unit (g' y)) ->
    (forall x y, su2_unit x -> su2_unit y -> qdot (g x) y = qdot x (g' y)) ->
    fn_bc h -> haar_lim h v -> haar_lim (fun x => h (g x)) v.
  Proof.
    intros g g' h v Hg Hg' Hadj Hh Hv eta Heta.
    destruct Hh as [[M0 HM0] Hc].
    set (M := Rmax M0 0).
    assert (HM : 0 <= M) by (unfold M; apply Rmax_r).
    assert (HbM : forall u, su2_unit u -> Rabs (h u) <= M).
    { intros u Hu. eapply Rle_trans; [apply HM0; exact Hu | unfold M; apply Rmax_l]. }
    set (eps := eta / (2 * (2 * M + 3))).
    assert (Heps : 0 < eps) by (unfold eps; apply Rdiv_lt_0_compat; lra).
    destruct (Hc eps Heps) as [delta [Hdelta Hmod]].
    destruct (haar_isometry_uniform M delta eps HM Hdelta Heps) as [n1 Hn1].
    destruct (Hv (eta / 2) ltac:(lra)) as [N2 HN2].
    exists n1. intros n Hn. unfold R_dist.
    set (m := Nat.max n1 N2).
    pose proof (Hn1 n m g g' h Hn (Nat.le_max_l n1 N2) Hg Hg' Hadj HbM
                  (fun u w Hu Hw Hcl => Rlt_le _ _ (Hmod u w Hu Hw Hcl))) as E1.
    pose proof (HN2 m (Nat.le_max_r n1 N2)) as E2. unfold R_dist in E2.
    replace (gmean n (fun x => h (g x)) - v)
      with ((gmean n (fun x => h (g x)) - gmean m h) + (gmean m h - v)) by ring.
    eapply Rle_lt_trans; [apply Rabs_triang |].
    assert (E3 : (2 * M + 3) * eps = eta / 2) by (unfold eps; field; lra).
    lra.
  Qed.

  (* =======================================================================
     3. Translations and inversion are isometries
     ======================================================================= *)

  Lemma qdot_translate : forall a b x y,
    qdot (qmul a (qmul x b)) y = qdot x (qmul (qconj a) (qmul y (qconj b))).
  Proof.
    intros [a0 a1 a2 a3] [b0 b1 b2 b3] [x0 x1 x2 x3] [y0 y1 y2 y3].
    unfold qdot, qmul, qconj. cbn [qr qi qj qk]. ring.
  Qed.

  Lemma qdot_conj : forall x y, qdot (qconj x) y = qdot x (qconj y).
  Proof. intros x y. unfold qdot, qconj. cbn [qr qi qj qk]. ring. Qed.

  Theorem haar_translate : forall (a b : Quat) (h : Quat -> R) (v : R),
    su2_unit a -> su2_unit b -> fn_bc h -> haar_lim h v ->
    haar_lim (fun u => h (qmul a (qmul u b))) v.
  Proof.
    intros a b h v Ha Hb Hh Hv.
    apply (haar_isometry (fun u => qmul a (qmul u b))
             (fun y => qmul (qconj a) (qmul y (qconj b))) h v); [| | | exact Hh | exact Hv].
    - intros x Hx. apply unit_mul; [exact Ha |]. apply unit_mul; assumption.
    - intros y Hy. apply unit_mul; [apply unit_conj; exact Ha |].
      apply unit_mul; [exact Hy | apply unit_conj; exact Hb].
    - intros x y _ _. apply qdot_translate.
  Qed.

  Theorem haar_inverse : forall (h : Quat -> R) (v : R),
    fn_bc h -> haar_lim h v -> haar_lim (fun u => h (qconj u)) v.
  Proof.
    intros h v Hh Hv.
    apply (haar_isometry qconj qconj h v); [| | | exact Hh | exact Hv].
    - intros x Hx. apply unit_conj. exact Hx.
    - intros y Hy. apply unit_conj. exact Hy.
    - intros x y _ _. apply qdot_conj.
  Qed.

  (* TARGET 11a *)
  Theorem su2_haar_bi_invariance : Challenge_SU2_HaarBiInvariance.
  Proof.
    intros h Hh. destruct (haar_exists h Hh) as [v Hv]. exists v.
    split; [exact Hv |]. split.
    - intros a b Ha Hb. exact (haar_translate a b h v Ha Hb Hh Hv).
    - exact (haar_inverse h v Hh Hv).
  Qed.

End SU2HaarInvariance.
