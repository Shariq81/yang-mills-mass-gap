(* =========================================================================
   ym/su2_infinite_volume.v

   The infinite-volume Gibbs state of the 4D SU(2) Wilson lattice gauge
   theory at strong coupling (TARGETS 9b, 9c, 9d), proved directly for the
   frozen objects of `verification/ChallengeSU2InfiniteVolume.v`.

     9b  Thermodynamic limit.  Let v_n be the Haar-measure Gibbs
         expectation of f in the volume Lambda_n = `su2_box n` (Target 8c).
         Lambda_{n+1} is a permutation of Q_n ++ Lambda_n, where every
         plaquette of the shell Q_n is at distance >= (n + 1 - n0) / 2 from
         the plaquettes on which f is localized (ym/lattice_boxes.v).  By
         the volume-dependence estimate of Target 9a (which holds for every
         Hopf grid, hence for the Haar limits) with mu = 2 ln 16,
           |v_{n+1} - v_n| <= K |Lambda_{n+1}| 16^{-n} <= K' 2^{-n},
         because |Lambda_{n+1}| <= 486 * 8^n.  A sequence with geometrically
         summable increments is Cauchy, hence convergent.  The sequence v_n
         itself is obtained from the completeness of R (no choice).
     9c  The clustering bound of Target 8d holds in every Lambda_n, hence
         for the limits.
     9d  The area-law bound of Target 8e holds in every Lambda_n that
         contains the loop, hence for the limit.

   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import rg.product_measure_perm.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.z2_polymer_gas.
Require Import ym.su2_algebra.
Require Import ym.su2_area_law.
Require Import ym.su2_continuity.
Require Import ym.su2_haar_grid.
Require Import ym.su2_haar_limit.
Require Import ym.su2_volume.
Require Import ym.lattice_boxes.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import ChallengeSU2InfiniteVolume.
Import DupClustering Z2GaugeExpansion Z2PolymerGas SU2Algebra.
Open Scope R_scope.

Module SU2InfiniteVolume.

  (* =======================================================================
     1. Expectations: permutations of the volume, scalars
     ======================================================================= *)

  Lemma links_perm : forall Lam Lam' : list Plaq4D,
    Permutation Lam Lam' -> Permutation (z2_links Lam) (z2_links Lam').
  Proof.
    intros Lam Lam' H.
    apply NoDup_Permutation;
      [apply SU2AreaLaw.dedup_NoDup | apply SU2AreaLaw.dedup_NoDup |].
    intro l. unfold z2_links. split; intro Hl.
    - apply (proj1 (dedup_In l _)) in Hl. apply (proj2 (dedup_In l _)).
      apply in_flat_map in Hl. destruct Hl as [p [Hp Hlp]].
      apply in_flat_map. exists p. split; [exact (Permutation_in p H Hp) | exact Hlp].
    - apply (proj1 (dedup_In l _)) in Hl. apply (proj2 (dedup_In l _)).
      apply in_flat_map in Hl. destruct Hl as [p [Hp Hlp]].
      apply in_flat_map. exists p.
      split; [exact (Permutation_in p (Permutation_sym H) Hp) | exact Hlp].
  Qed.

  Lemma expect_perm : forall (G : list Quat) (beta : R) (Lam Lam' : list Plaq4D)
      (F : SU2Config -> R),
    Permutation Lam Lam' -> su2_expect_on G beta Lam F = su2_expect_on G beta Lam' F.
  Proof.
    intros G beta Lam Lam' F H.
    assert (Hact : forall U, su2_wilson_action beta Lam U = su2_wilson_action beta Lam' U).
    { intro U. unfold su2_wilson_action. apply Rmult_eq_compat_l.
      exact (ProductMeasure.rsum_perm Lam Lam' (su2_plaq U) H). }
    pose proof (links_perm Lam Lam' H) as HE.
    rewrite !expect_csum.
    rewrite (ProductMeasurePerm.csum_perm Link4D Quat link4D_eqb link4D_eqb_spec G
               (z2_links Lam) (z2_links Lam') HE
               (fun U => F U * exp (- su2_wilson_action beta Lam U)) (fun _ => qone)).
    rewrite (ProductMeasurePerm.csum_perm Link4D Quat link4D_eqb link4D_eqb_spec G
               (z2_links Lam) (z2_links Lam') HE
               (fun U => exp (- su2_wilson_action beta Lam U)) (fun _ => qone)).
    rewrite (csum_ext Link4D Quat link4D_eqb G (z2_links Lam')
               (fun U => F U * exp (- su2_wilson_action beta Lam U))
               (fun U => F U * exp (- su2_wilson_action beta Lam' U)))
      by (intro U; rewrite Hact; reflexivity).
    rewrite (csum_ext Link4D Quat link4D_eqb G (z2_links Lam')
               (fun U => exp (- su2_wilson_action beta Lam U))
               (fun U => exp (- su2_wilson_action beta Lam' U)))
      by (intro U; rewrite Hact; reflexivity).
    reflexivity.
  Qed.

  Lemma expect_ext : forall (G : list Quat) (beta : R) (Lam : list Plaq4D)
      (F F' : SU2Config -> R),
    (forall U, F U = F' U) -> su2_expect_on G beta Lam F = su2_expect_on G beta Lam F'.
  Proof.
    intros G beta Lam F F' H. rewrite !expect_csum.
    rewrite (csum_ext Link4D Quat link4D_eqb G (z2_links Lam)
               (fun U => F U * exp (- su2_wilson_action beta Lam U))
               (fun U => F' U * exp (- su2_wilson_action beta Lam U)))
      by (intro U; rewrite H; reflexivity).
    reflexivity.
  Qed.

  Lemma expect_scal : forall (G : list Quat) (beta : R) (Lam : list Plaq4D) (c : R)
      (F : SU2Config -> R),
    su2_expect_on G beta Lam (fun U => c * F U) = c * su2_expect_on G beta Lam F.
  Proof.
    intros G beta Lam c F. rewrite !expect_csum.
    rewrite (csum_ext Link4D Quat link4D_eqb G (z2_links Lam)
               (fun U => c * F U * exp (- su2_wilson_action beta Lam U))
               (fun U => c * (F U * exp (- su2_wilson_action beta Lam U))))
      by (intro U; ring).
    rewrite csum_scal. unfold Rdiv. ring.
  Qed.

  (* =======================================================================
     2. Sequences with geometrically summable increments converge
     ======================================================================= *)

  Lemma cv_const : forall c : R, Un_cv (fun _ => c) c.
  Proof.
    intros c eps Heps. exists 0%nat. intros n _. unfold R_dist.
    replace (c - c) with 0 by ring. rewrite Rabs_R0. exact Heps.
  Qed.

  Lemma half_pow_small : forall eps, 0 < eps ->
    exists N : nat, forall n, (N <= n)%nat -> (/ 2) ^ n < eps.
  Proof.
    intros eps Heps.
    assert (Hh : Rabs (/ 2) < 1) by (rewrite Rabs_pos_eq; lra).
    destruct (pow_lt_1_zero (/ 2) Hh eps Heps) as [N HN].
    exists N. intros n Hn. specialize (HN n Hn).
    rewrite Rabs_pos_eq in HN; [exact HN | apply pow_le; lra].
  Qed.

  Lemma geom_increments : forall (v : nat -> R) (K : R) (n0 : nat),
    0 <= K ->
    (forall n, (n0 <= n)%nat -> Rabs (v (S n) - v n) <= K * (/ 2) ^ n) ->
    forall n j, (n0 <= n)%nat -> Rabs (v (n + j)%nat - v n) <= 2 * K * (/ 2) ^ n.
  Proof.
    intros v K n0 HK Hinc n j Hn.
    assert (Hp : 0 < (/ 2) ^ n) by (apply pow_lt; lra).
    assert (HKp : 0 <= K * (/ 2) ^ n) by (apply Rmult_le_pos; lra).
    assert (Hstrong :
      Rabs (v (n + j)%nat - v n) <= 2 * (K * (/ 2) ^ n) * (1 - (/ 2) ^ j)).
    { induction j as [| j IH].
      - rewrite Nat.add_0_r. replace (v n - v n) with 0 by ring.
        rewrite Rabs_R0. cbn [pow]. lra.
      - replace (n + S j)%nat with (S (n + j)) by lia.
        replace (v (S (n + j)) - v n)
          with ((v (S (n + j)) - v (n + j)%nat) + (v (n + j)%nat - v n)) by ring.
        eapply Rle_trans; [apply Rabs_triang |].
        pose proof (Hinc (n + j)%nat ltac:(lia)) as H1.
        rewrite pow_add in H1. cbn [pow].
        set (a := K * (/ 2) ^ n) in *. set (b := (/ 2) ^ j) in *.
        replace (K * ((/ 2) ^ n * b)) with (a * b) in H1 by (unfold a; ring).
        lra. }
    assert (Hq : 0 < (/ 2) ^ j) by (apply pow_lt; lra).
    assert (Hprod : 0 <= (K * (/ 2) ^ n) * (/ 2) ^ j) by (apply Rmult_le_pos; lra).
    lra.
  Qed.

  Lemma geom_cauchy : forall (v : nat -> R) (K : R) (n0 : nat),
    0 <= K ->
    (forall n, (n0 <= n)%nat -> Rabs (v (S n) - v n) <= K * (/ 2) ^ n) ->
    exists l : R, Un_cv v l.
  Proof.
    intros v K n0 HK Hinc.
    assert (Hc : Cauchy_crit v).
    { intros eps Heps.
      assert (Hd : 0 < 4 * K + 1) by lra.
      destruct (half_pow_small (eps / (4 * K + 1))
                  ltac:(apply Rdiv_lt_0_compat; lra)) as [N HN].
      exists (Nat.max N n0). intros n m Hn Hm.
      set (M := Nat.max N n0) in *.
      assert (HMN : (N <= M)%nat) by apply Nat.le_max_l.
      assert (HM0 : (n0 <= M)%nat) by apply Nat.le_max_r.
      pose proof (geom_increments v K n0 HK Hinc M (n - M) HM0) as H1.
      pose proof (geom_increments v K n0 HK Hinc M (m - M) HM0) as H2.
      replace (M + (n - M))%nat with n in H1 by lia.
      replace (M + (m - M))%nat with m in H2 by lia.
      pose proof (HN M HMN) as Hsmall.
      assert (Hp : 0 < (/ 2) ^ M) by (apply pow_lt; lra).
      assert (Hlt : (/ 2) ^ M * (4 * K + 1) < eps).
      { apply Rmult_lt_reg_r with (/ (4 * K + 1)); [apply Rinv_0_lt_compat; exact Hd |].
        rewrite Rmult_assoc, Rinv_r by lra. rewrite Rmult_1_r. exact Hsmall. }
      unfold R_dist.
      apply Rle_lt_trans with (Rabs (v n - v M) + Rabs (v m - v M)).
      { replace (v n - v m) with ((v n - v M) + - (v m - v M)) by ring.
        eapply Rle_trans; [apply Rabs_triang |]. rewrite Rabs_Ropp. apply Rle_refl. }
      set (a := K * (/ 2) ^ M) in *.
      replace (2 * K * (/ 2) ^ M) with (2 * a) in H1, H2 by (unfold a; ring).
      replace ((/ 2) ^ M * (4 * K + 1)) with (4 * a + (/ 2) ^ M) in Hlt by (unfold a; ring).
      lra. }
    destruct (R_complete v Hc) as [l Hl]. exists l. exact Hl.
  Qed.

  (* =======================================================================
     3. The decay rate mu0 = 2 ln 16 and the smallness conditions
     ======================================================================= *)

  Definition mu0 : R := 2 * ln 16.

  Lemma ln16_pos : 0 < ln 16.
  Proof. rewrite <- ln_1. apply ln_increasing; lra. Qed.

  Lemma mu0_nonneg : 0 <= mu0.
  Proof. unfold mu0. pose proof ln16_pos. lra. Qed.

  Lemma exp_ln16 : exp (- ln 16) = / 16.
  Proof. rewrite exp_Ropp, exp_ln by lra. reflexivity. Qed.

  Lemma exp_mu0 : exp (- mu0) = / 256.
  Proof.
    unfold mu0. replace (- (2 * ln 16)) with (- ln 16 + - ln 16) by ring.
    rewrite exp_plus, exp_ln16. field.
  Qed.

  Lemma small_168 : forall beta, 43008 * Rabs beta <= 1 -> 168 * Rabs beta <= exp (- mu0).
  Proof. intros beta H. rewrite exp_mu0. lra. Qed.

  Lemma small_63 : forall beta, 43008 * Rabs beta <= 1 ->
    63 * (exp (2 * Rabs beta) - 1) <= 1.
  Proof.
    intros beta H. pose proof (Rabs_pos beta) as Hb.
    pose proof (SU2Continuity.exp_minus_one_bound (2 * Rabs beta)) as He.
    rewrite (Rabs_pos_eq (2 * Rabs beta)) in He by lra.
    assert (Hh : 2 * Rabs beta <= 1 / 2) by lra.
    specialize (He Hh).
    pose proof (Rle_abs (exp (2 * Rabs beta) - 1)) as H1. lra.
  Qed.

  (* =======================================================================
     4. The thermodynamic limit for observables bounded by 1
     ======================================================================= *)

  Section Thermo.
    Variable beta : R.
    Hypothesis Hbeta : 43008 * Rabs beta <= 1.
    Variable P : list Plaq4D.
    Variable f : SU2Config -> R.
    Hypothesis f_loc : su2_local_on f P.
    Hypothesis f_bc : su2_bounded_continuous f.
    Hypothesis f_bd : forall U, su2_unit_config U -> Rabs (f U) <= 1.
    Variable n0 : nat.
    Hypothesis P_in : incl P (su2_box n0).

    (* Target 9a for the Haar-measure expectations *)
    Lemma haar_volume_dependence : forall (Lam' Lam Q : list Plaq4D) (v' v : R),
      Permutation Lam' (Q ++ Lam) -> NoDup (Q ++ Lam) -> Forall wf_plaq_4D (Q ++ Lam) ->
      incl P Lam ->
      su2_haar_expect_is beta Lam' f v' -> su2_haar_expect_is beta Lam f v ->
      Rabs (v' - v)
      <= 2 * exp (2 * Rabs beta) *
         rsum Q (fun q => rsum P (fun p => exp (- mu0 * (plaq4D_dist p q - 1)))).
    Proof.
      intros Lam' Lam Q v' v Hperm Hnd Hwf HP Hv' Hv.
      apply (SU2HaarLimit.cv_bound
               (fun k => su2_expect_on (su2_grid k) beta Lam' f
                         - su2_expect_on (su2_grid k) beta Lam f)
               (v' - v) _ 0%nat).
      - exact (CV_minus (fun k => su2_expect_on (su2_grid k) beta Lam' f)
                        (fun k => su2_expect_on (su2_grid k) beta Lam f) v' v Hv' Hv).
      - intros k _. rewrite (expect_perm (su2_grid k) beta Lam' (Q ++ Lam) f Hperm).
        exact (SU2Volume.su2_volume_dependence (su2_grid k) beta mu0 Lam Q P f
                 (SU2HaarGrid.grid_nonempty k) (SU2HaarGrid.grid_unit k)
                 mu0_nonneg (small_168 beta Hbeta) Hnd Hwf HP f_loc f_bd).
    Qed.

    Definition Acst : R := exp (INR (S n0) * ln 16).
    Definition Kcst : R :=
      2 * exp (2 * Rabs beta) * (486 * (INR (length P) * Acst)).

    Lemma Kcst_nonneg : 0 <= Kcst.
    Proof.
      unfold Kcst, Acst.
      pose proof (exp_pos (2 * Rabs beta)) as H1.
      pose proof (exp_pos (INR (S n0) * ln 16)) as H2.
      pose proof (pos_INR (length P)) as H3.
      apply Rmult_le_pos; [lra |]. apply Rmult_le_pos; [lra |].
      apply Rmult_le_pos; lra.
    Qed.

    (* a plaquette of the shell n is far from P *)
    Lemma far_term : forall n p q, (n0 <= n)%nat -> In p P ->
      In q (su2_box (S n)) -> ~ In q (su2_box n) ->
      exp (- mu0 * (plaq4D_dist p q - 1)) <= Acst * (/ 16) ^ n.
    Proof.
      intros n p q Hn Hp Hq Hnq.
      pose proof (LatticeBoxes.shell_far n0 n p q Hn (P_in p Hp) Hq Hnq) as Hd.
      unfold Acst. rewrite <- exp_ln16, Z2GaugeClustering.exp_pow_INR, <- exp_plus.
      apply Z2GaugeClustering.exp_le. unfold mu0.
      pose proof ln16_pos as Hl.
      rewrite S_INR in Hd. rewrite S_INR.
      set (d := plaq4D_dist p q) in *. set (L := ln 16) in *.
      assert (Hprod : 0 <= L * (d - (INR n + 1 - INR n0) / 2)).
      { apply Rmult_le_pos; lra. }
      lra.
    Qed.

    Lemma step_bound : forall vn : nat -> R,
      (forall n, su2_haar_expect_is beta (su2_box n) f (vn n)) ->
      forall n, (n0 <= n)%nat -> Rabs (vn (S n) - vn n) <= Kcst * (/ 2) ^ n.
    Proof.
      intros vn Hvn n Hn.
      destruct (LatticeBoxes.box_split n) as [Q [Hperm [HQ HlenQ]]].
      assert (Hnd : NoDup (Q ++ su2_box n)).
      { exact (Permutation_NoDup Hperm (LatticeBoxes.box_nodup (S n))). }
      assert (Hwf : Forall wf_plaq_4D (Q ++ su2_box n)).
      { apply Forall_forall. intros x Hx.
        apply (proj1 (Forall_forall wf_plaq_4D (su2_box (S n))) (LatticeBoxes.box_wf (S n))).
        exact (Permutation_in x (Permutation_sym Hperm) Hx). }
      assert (HPn : incl P (su2_box n)).
      { intros p Hp. exact (LatticeBoxes.box_mono n0 n Hn p (P_in p Hp)). }
      eapply Rle_trans;
        [exact (haar_volume_dependence (su2_box (S n)) (su2_box n) Q (vn (S n)) (vn n)
                  Hperm Hnd Hwf HPn (Hvn (S n)) (Hvn n)) |].
      pose proof (exp_pos (2 * Rabs beta)) as He.
      assert (HA : 0 < Acst) by (unfold Acst; apply exp_pos).
      assert (H16 : 0 < (/ 16) ^ n) by (apply pow_lt; lra).
      assert (HP0 : 0 <= INR (length P)) by apply pos_INR.
      apply Rle_trans with
        (2 * exp (2 * Rabs beta) *
         rsum Q (fun q => rsum P (fun p => Acst * (/ 16) ^ n))).
      - apply Rmult_le_compat_l; [lra |].
        apply rsum_le. intros q Hq. apply rsum_le. intros p Hp.
        destruct (HQ q Hq) as [Hq1 Hq2]. exact (far_term n p q Hn Hp Hq1 Hq2).
      - rewrite (rsum_ext Q (fun q => rsum P (fun p => Acst * (/ 16) ^ n))
                   (fun _ => INR (length P) * (Acst * (/ 16) ^ n)))
          by (intros q _; apply ProductMeasure.rsum_const).
        rewrite ProductMeasure.rsum_const.
        assert (HQn : INR (length Q) <= 486 * 8 ^ n).
        { eapply Rle_trans; [apply le_INR; exact HlenQ |].
          apply LatticeBoxes.box_card_bound. }
        assert (H816 : 8 ^ n * (/ 16) ^ n = (/ 2) ^ n).
        { rewrite <- Rpow_mult_distr. f_equal. field. }
        assert (Hin : 0 <= INR (length P) * (Acst * (/ 16) ^ n)).
        { apply Rmult_le_pos; [exact HP0 |]. apply Rmult_le_pos; lra. }
        apply Rle_trans with
          (2 * exp (2 * Rabs beta) *
           ((486 * 8 ^ n) * (INR (length P) * (Acst * (/ 16) ^ n)))).
        + apply Rmult_le_compat_l; [lra |].
          apply Rmult_le_compat_r; [exact Hin | exact HQn].
        + unfold Kcst. rewrite <- H816. apply Req_le. ring.
    Qed.

    Theorem thermo_limit_bounded : exists v : R, su2_infinite_volume_expect_is beta f v.
    Proof.
      assert (Hc : forall n,
                Cauchy_crit (fun k => su2_expect_on (su2_grid k) beta (su2_box n) f)).
      { intro n.
        destruct (SU2HaarLimit.haar_state_exists beta (su2_box n) f f_bc) as [v Hv].
        exact (CV_Cauchy (fun k => su2_expect_on (su2_grid k) beta (su2_box n) f)
                 (exist (fun l => Un_cv (fun k => su2_expect_on (su2_grid k) beta
                                                    (su2_box n) f) l) v Hv)). }
      set (vn := fun n =>
             proj1_sig (R_complete (fun k => su2_expect_on (su2_grid k) beta (su2_box n) f)
                          (Hc n))).
      assert (Hvn : forall n, su2_haar_expect_is beta (su2_box n) f (vn n)).
      { intro n.
        exact (proj2_sig (R_complete (fun k => su2_expect_on (su2_grid k) beta (su2_box n) f)
                            (Hc n))). }
      destruct (geom_cauchy vn Kcst n0 Kcst_nonneg (step_bound vn Hvn)) as [l Hl].
      exists l. exists vn. split; assumption.
    Qed.

  End Thermo.

  (* =======================================================================
     5. TARGET 9b
     ======================================================================= *)

  Theorem su2_thermodynamic_limit : Challenge_SU2Gauge4D_ThermodynamicLimit.
  Proof.
    intros beta P f Hbeta Hwf Hloc Hbc.
    destruct (LatticeBoxes.box_exhaust P Hwf) as [n0 Hn0].
    destruct Hbc as [[M HM] Hcont].
    set (c := Rmax M 1).
    assert (Hc1 : 1 <= c) by apply Rmax_r.
    assert (HcM : M <= c) by apply Rmax_l.
    set (f1 := fun U : SU2Config => / c * f U).
    assert (Hf1_loc : su2_local_on f1 P).
    { intros U U' H. unfold f1. rewrite (Hloc U U' H). reflexivity. }
    assert (Hf1_bc : su2_bounded_continuous f1).
    { apply SU2Continuity.bc_scal. split; [exists M; exact HM | exact Hcont]. }
    assert (Hf1_bd : forall U, su2_unit_config U -> Rabs (f1 U) <= 1).
    { intros U HU. unfold f1.
      rewrite Rabs_mult, (Rabs_pos_eq (/ c)) by (left; apply Rinv_0_lt_compat; lra).
      pose proof (HM U HU) as H1.
      apply Rmult_le_reg_l with c; [lra |].
      rewrite <- Rmult_assoc, Rinv_r by lra. lra. }
    destruct (thermo_limit_bounded beta Hbeta P f1 Hf1_loc Hf1_bc Hf1_bd n0 Hn0)
      as [v1 [vn1 [Hvn1 Hcv1]]].
    exists (c * v1). exists (fun n => c * vn1 n). split.
    - intro n. unfold su2_haar_expect_is.
      apply (SU2HaarLimit.cv_ext
               (fun k => c * su2_expect_on (su2_grid k) beta (su2_box n) f1)).
      + intro k. rewrite <- expect_scal. apply expect_ext. intro U. unfold f1. field. lra.
      + exact (CV_mult (fun _ => c)
                 (fun k => su2_expect_on (su2_grid k) beta (su2_box n) f1)
                 c (vn1 n) (cv_const c) (Hvn1 n)).
    - exact (CV_mult (fun _ => c) vn1 c v1 (cv_const c) Hcv1).
  Qed.

  (* =======================================================================
     6. TARGET 9c
     ======================================================================= *)

  Theorem su2_infinite_volume_clustering : Challenge_SU2Gauge4D_InfiniteVolumeClustering.
  Proof.
    intros beta mu p1 p2 f g Hmu Hsmall Hbeta Hw1 Hw2 Hf Hg Hfc Hgc Hfb Hgb.
    assert (Hloc_fg : su2_local_on (fun U => f U * g U) [p1; p2]).
    { intros U U' H. rewrite (Hf U U'), (Hg U U'); [reflexivity | |].
      - intros l Hl. apply (H p2 l); [right; left; reflexivity | exact Hl].
      - intros l Hl. apply (H p1 l); [left; reflexivity | exact Hl]. }
    assert (Hloc_f : su2_local_on f [p1]).
    { intros U U' H. apply Hf. intros l Hl. apply (H p1 l); [left; reflexivity | exact Hl]. }
    assert (Hloc_g : su2_local_on g [p2]).
    { intros U U' H. apply Hg. intros l Hl. apply (H p2 l); [left; reflexivity | exact Hl]. }
    destruct (su2_thermodynamic_limit beta [p1; p2] (fun U => f U * g U) Hbeta
                (Forall_cons p1 Hw1 (Forall_cons p2 Hw2 (Forall_nil _)))
                Hloc_fg (SU2Continuity.bc_mult f g Hfc Hgc))
      as [vfg [nfg [Hnfg Hcfg]]].
    destruct (su2_thermodynamic_limit beta [p1] f Hbeta
                (Forall_cons p1 Hw1 (Forall_nil _)) Hloc_f Hfc)
      as [vf [nf [Hnf Hcf]]].
    destruct (su2_thermodynamic_limit beta [p2] g Hbeta
                (Forall_cons p2 Hw2 (Forall_nil _)) Hloc_g Hgc)
      as [vg [ng [Hng Hcg]]].
    exists vfg, vf, vg.
    split; [exists nfg; split; assumption |].
    split; [exists nf; split; assumption |].
    split; [exists ng; split; assumption |].
    apply (SU2HaarLimit.cv_bound (fun n => nfg n - nf n * ng n) (vfg - vf * vg) _ 0%nat).
    - exact (CV_minus nfg (fun n => nf n * ng n) vfg (vf * vg) Hcfg
               (CV_mult nf ng vf vg Hcf Hcg)).
    - intros n _.
      destruct (SU2HaarLimit.su2_haar_clustering beta mu (su2_box n) p1 p2 f g
                  Hmu Hsmall (LatticeBoxes.box_nodup n) (LatticeBoxes.box_wf n)
                  Hw1 Hf Hg Hfc Hgc Hfb Hgb)
        as [a [b [c [Ha [Hb [Hc Hbound]]]]]].
      rewrite (UL_sequence
                 (fun k => su2_expect_on (su2_grid k) beta (su2_box n) (fun U => f U * g U))
                 (nfg n) a (Hnfg n) Ha).
      rewrite (UL_sequence (fun k => su2_expect_on (su2_grid k) beta (su2_box n) f)
                 (nf n) b (Hnf n) Hb).
      rewrite (UL_sequence (fun k => su2_expect_on (su2_grid k) beta (su2_box n) g)
                 (ng n) c (Hng n) Hc).
      exact Hbound.
  Qed.

  (* =======================================================================
     7. TARGET 9d
     ======================================================================= *)

  (* a canonical plaquette containing a given link *)
  Definition cover_plaq (l : Link4D) : Plaq4D :=
    match snd l with
    | D4_t => mkPlaq4D (fst l) D4_t D4_x
    | D4_x => mkPlaq4D (fst l) D4_t D4_x
    | D4_y => mkPlaq4D (fst l) D4_t D4_y
    | D4_z => mkPlaq4D (fst l) D4_t D4_z
    end.

  Lemma cover_wf : forall l, wf_plaq_4D (cover_plaq l).
  Proof.
    intros [s d]. unfold cover_plaq, wf_plaq_4D, canonical_planes_4D.
    destruct d; cbn [snd fst p4_mu p4_nu In];
      repeat (first [left; reflexivity | right]).
  Qed.

  Lemma cover_In : forall l, In l (plaq4D_links (cover_plaq l)).
  Proof.
    intros [s d]. unfold cover_plaq, plaq4D_links.
    destruct d; cbn [snd fst p4_site p4_mu p4_nu In];
      [left | right; left | right; left | right; left]; reflexivity.
  Qed.

  Theorem su2_infinite_volume_area_law : Challenge_SU2Gauge4D_InfiniteVolumeAreaLaw.
  Proof.
    intros beta s mu nu a b Hbeta Hmn.
    set (P := map cover_plaq (z2_rect_loop s mu nu a b)).
    assert (HPwf : Forall wf_plaq_4D P).
    { apply Forall_forall. intros p Hp. apply in_map_iff in Hp.
      destruct Hp as [l [Hl _]]. subst p. apply cover_wf. }
    assert (Hloc : su2_local_on (fun U => su2_wilson_loop U s mu nu a b) P).
    { intros U U' H. apply wilson_local. intros l Hl.
      apply (H (cover_plaq l) l); [apply in_map; exact Hl | apply cover_In]. }
    destruct (su2_thermodynamic_limit beta P (fun U => su2_wilson_loop U s mu nu a b)
                Hbeta HPwf Hloc (SU2Continuity.bc_wilson_loop s mu nu a b))
      as [w [vn [Hvn Hcv]]].
    exists w. split; [exists vn; split; assumption |].
    destruct (LatticeBoxes.box_exhaust P HPwf) as [n0 Hn0].
    apply (SU2HaarLimit.cv_bound vn w _ n0 Hcv).
    intros n Hn.
    assert (HC : forall l, In l (z2_rect_loop s mu nu a b) -> In l (z2_links (su2_box n))).
    { intros l Hl.
      apply (SU2Volume.links_in (su2_box n) (cover_plaq l) l); [| apply cover_In].
      apply (LatticeBoxes.box_mono n0 n Hn). apply Hn0. apply in_map. exact Hl. }
    destruct (SU2HaarLimit.su2_haar_wilson_loop_area_law beta (su2_box n) s mu nu a b
                (small_63 beta Hbeta) (LatticeBoxes.box_nodup n) (LatticeBoxes.box_wf n)
                Hmn HC) as [w' [Hw' Hb']].
    rewrite (UL_sequence
               (fun k => su2_expect_on (su2_grid k) beta (su2_box n)
                           (fun U => su2_wilson_loop U s mu nu a b))
               (vn n) w' (Hvn n) Hw').
    exact Hb'.
  Qed.

  (* =======================================================================
     8. An instance of Target 9c: the plaquette-plaquette correlation
     ======================================================================= *)

  (* The hypotheses of Target 9c on the observables are satisfied by the
     plaquette variables: the connected plaquette-plaquette correlation
     function of the infinite-volume Gibbs state exists and decays
     exponentially in the distance of the two plaquettes. *)
  Corollary su2_infinite_volume_plaquette_clustering :
    forall (beta mu : R) (p1 p2 : Plaq4D),
      0 <= mu ->
      168 * Rabs beta <= exp (- mu) ->
      43008 * Rabs beta <= 1 ->
      wf_plaq_4D p1 ->
      wf_plaq_4D p2 ->
      exists v12 v1 v2 : R,
        su2_infinite_volume_expect_is beta (fun U => su2_plaq U p1 * su2_plaq U p2) v12 /\
        su2_infinite_volume_expect_is beta (fun U => su2_plaq U p1) v1 /\
        su2_infinite_volume_expect_is beta (fun U => su2_plaq U p2) v2 /\
        Rabs (v12 - v1 * v2) <= 4 * exp (- mu * (plaq4D_dist p1 p2 - 1)).
  Proof.
    intros beta mu p1 p2 Hmu Hsmall Hbeta Hw1 Hw2.
    apply (su2_infinite_volume_clustering beta mu p1 p2
             (fun U => su2_plaq U p1) (fun U => su2_plaq U p2)
             Hmu Hsmall Hbeta Hw1 Hw2).
    - intros U U' H. apply plaq_local. exact H.
    - intros U U' H. apply plaq_local. exact H.
    - apply SU2Continuity.bc_plaq.
    - apply SU2Continuity.bc_plaq.
    - intros U HU. apply Rabs_le. apply plaq_bound. exact HU.
    - intros U HU. apply Rabs_le. apply plaq_bound. exact HU.
  Qed.

End SU2InfiniteVolume.
