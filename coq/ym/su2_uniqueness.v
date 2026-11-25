(* =========================================================================
   ym/su2_uniqueness.v

   The infinite-volume Gibbs state of the 4D SU(2) Wilson lattice gauge
   theory at strong coupling does not depend on the exhausting sequence of
   finite volumes (TARGET 10a), proved directly for the frozen objects of
   `verification/ChallengeSU2MassGap.v`, together with the elementary
   calculus of Haar-measure and infinite-volume expectations (linearity,
   constants, uniqueness of the value).

   Proof of 10a.  Let f be localized on P inside the cube Lambda_{n0}, with
   |f| <= 1, and let Lam be ANY finite duplicate-free volume of canonical
   plaquettes containing the cube Lambda_m, m >= n0.  Lam is a permutation
   of Q ++ Lambda_m with Q the plaquettes of Lam outside the cube, so by
   the volume-dependence estimate of Target 9a for the Haar limits,

     |<f>_Lam - <f>_{Lambda_m}|
        <= 2 e^{2|beta|} sum_{p in P} sum_{q in Q} e^{- mu0 (dist(p,q) - 1)}
        <= C * 2^{-m},

   because the plaquettes outside the cube of side m contribute at most
   972 * 16^{n0+1} * 2^{-m} for each p (`LatticeBoxesTail.outside_box_sum`).
   Since <f>_{Lambda_m} converges, so does <f>_{Lam k} along every sequence
   that eventually contains each cube, to the same limit.

   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import rg.product_measure_perm.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.su2_algebra.
Require Import ym.su2_haar_grid.
Require Import ym.su2_haar_limit.
Require Import ym.lattice_boxes.
Require Import ym.su2_infinite_volume.
Require Import ym.lattice_boxes_tail.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import ChallengeSU2InfiniteVolume ChallengeSU2MassGap.
Import DupClustering Z2GaugeExpansion SU2Algebra.
Open Scope R_scope.

Module SU2Uniqueness.

  (* =======================================================================
     1. Calculus of finite-volume expectations
     ======================================================================= *)

  Lemma expect_plus : forall (G : list Quat) (beta : R) (Lam : list Plaq4D)
      (F F' : SU2Config -> R),
    su2_expect_on G beta Lam (fun U => F U + F' U) =
    su2_expect_on G beta Lam F + su2_expect_on G beta Lam F'.
  Proof.
    intros G beta Lam F F'. rewrite !expect_csum.
    rewrite (csum_ext Link4D Quat link4D_eqb G (z2_links Lam)
               (fun U => (F U + F' U) * exp (- su2_wilson_action beta Lam U))
               (fun U => F U * exp (- su2_wilson_action beta Lam U)
                         + F' U * exp (- su2_wilson_action beta Lam U)))
      by (intro U; ring).
    rewrite csum_plus. unfold Rdiv. ring.
  Qed.

  Lemma expect_const : forall (G : list Quat) (beta : R) (Lam : list Plaq4D) (c : R),
    G <> [] -> su2_expect_on G beta Lam (fun _ => c) = c.
  Proof.
    intros G beta Lam c HG. rewrite expect_csum, csum_scal.
    assert (Hpos : 0 < csum Link4D Quat link4D_eqb G (z2_links Lam)
                         (fun U => exp (- su2_wilson_action beta Lam U)) (fun _ => qone)).
    { apply csum_pos; [exact HG |]. intro A. apply exp_pos. }
    field. lra.
  Qed.

  (* =======================================================================
     2. Calculus of Haar-measure and infinite-volume expectations
     ======================================================================= *)

  Lemma haar_ext : forall beta Lam (f f' : SU2Config -> R) v,
    (forall U, f U = f' U) ->
    su2_haar_expect_is beta Lam f v -> su2_haar_expect_is beta Lam f' v.
  Proof.
    intros beta Lam f f' v H Hv. unfold su2_haar_expect_is in *.
    apply (SU2HaarLimit.cv_ext (fun n => su2_expect_on (su2_grid n) beta Lam f));
      [| exact Hv].
    intro n. apply SU2InfiniteVolume.expect_ext. exact H.
  Qed.

  Lemma haar_scal : forall beta Lam c (f : SU2Config -> R) v,
    su2_haar_expect_is beta Lam f v ->
    su2_haar_expect_is beta Lam (fun U => c * f U) (c * v).
  Proof.
    intros beta Lam c f v H. unfold su2_haar_expect_is in *.
    apply (SU2HaarLimit.cv_ext (fun n => c * su2_expect_on (su2_grid n) beta Lam f)).
    - intro n. symmetry. apply SU2InfiniteVolume.expect_scal.
    - exact (CV_mult (fun _ => c) (fun n => su2_expect_on (su2_grid n) beta Lam f)
               c v (SU2InfiniteVolume.cv_const c) H).
  Qed.

  Lemma haar_plus : forall beta Lam (f g : SU2Config -> R) v w,
    su2_haar_expect_is beta Lam f v -> su2_haar_expect_is beta Lam g w ->
    su2_haar_expect_is beta Lam (fun U => f U + g U) (v + w).
  Proof.
    intros beta Lam f g v w Hv Hw. unfold su2_haar_expect_is in *.
    apply (SU2HaarLimit.cv_ext
             (fun n => su2_expect_on (su2_grid n) beta Lam f
                       + su2_expect_on (su2_grid n) beta Lam g)).
    - intro n. symmetry. apply expect_plus.
    - exact (CV_plus (fun n => su2_expect_on (su2_grid n) beta Lam f)
               (fun n => su2_expect_on (su2_grid n) beta Lam g) v w Hv Hw).
  Qed.

  Lemma haar_const : forall beta Lam c, su2_haar_expect_is beta Lam (fun _ => c) c.
  Proof.
    intros beta Lam c. unfold su2_haar_expect_is.
    apply (SU2HaarLimit.cv_ext (fun _ : nat => c)); [| apply SU2InfiniteVolume.cv_const].
    intro n. symmetry. apply expect_const. apply SU2HaarGrid.grid_nonempty.
  Qed.

  Lemma haar_unique : forall beta Lam (f : SU2Config -> R) v v',
    su2_haar_expect_is beta Lam f v -> su2_haar_expect_is beta Lam f v' -> v = v'.
  Proof.
    intros beta Lam f v v' H H'.
    exact (UL_sequence (fun n => su2_expect_on (su2_grid n) beta Lam f) v v' H H').
  Qed.

  Lemma inf_ext : forall beta (f f' : SU2Config -> R) v,
    (forall U, f U = f' U) ->
    su2_infinite_volume_expect_is beta f v -> su2_infinite_volume_expect_is beta f' v.
  Proof.
    intros beta f f' v H [vn [Hvn Hcv]]. exists vn. split; [| exact Hcv].
    intro n. exact (haar_ext beta (su2_box n) f f' (vn n) H (Hvn n)).
  Qed.

  Lemma inf_scal : forall beta c (f : SU2Config -> R) v,
    su2_infinite_volume_expect_is beta f v ->
    su2_infinite_volume_expect_is beta (fun U => c * f U) (c * v).
  Proof.
    intros beta c f v [vn [Hvn Hcv]]. exists (fun n => c * vn n). split.
    - intro n. apply haar_scal. apply Hvn.
    - exact (CV_mult (fun _ => c) vn c v (SU2InfiniteVolume.cv_const c) Hcv).
  Qed.

  Lemma inf_plus : forall beta (f g : SU2Config -> R) v w,
    su2_infinite_volume_expect_is beta f v -> su2_infinite_volume_expect_is beta g w ->
    su2_infinite_volume_expect_is beta (fun U => f U + g U) (v + w).
  Proof.
    intros beta f g v w [vn [Hvn Hcv]] [wn [Hwn Hcw]].
    exists (fun n => vn n + wn n). split.
    - intro n. apply haar_plus; [apply Hvn | apply Hwn].
    - exact (CV_plus vn wn v w Hcv Hcw).
  Qed.

  Lemma inf_const : forall beta c, su2_infinite_volume_expect_is beta (fun _ => c) c.
  Proof.
    intros beta c. exists (fun _ => c). split.
    - intro n. apply haar_const.
    - apply SU2InfiniteVolume.cv_const.
  Qed.

  Lemma inf_unique : forall beta (f : SU2Config -> R) v v',
    su2_infinite_volume_expect_is beta f v -> su2_infinite_volume_expect_is beta f v' ->
    v = v'.
  Proof.
    intros beta f v v' [vn [Hvn Hcv]] [vn' [Hvn' Hcv']].
    apply (UL_sequence vn v v' Hcv).
    apply (SU2HaarLimit.cv_ext vn'); [| exact Hcv'].
    intro n. exact (haar_unique beta (su2_box n) f (vn' n) (vn n) (Hvn' n) (Hvn n)).
  Qed.

  (* =======================================================================
     3. Any volume containing a large cube
     ======================================================================= *)

  Section Core.
    Variable beta : R.
    Hypothesis Hbeta : 43008 * Rabs beta <= 1.
    Variable P : list Plaq4D.
    Variable f : SU2Config -> R.
    Hypothesis f_loc : su2_local_on f P.
    Hypothesis f_bd : forall U, su2_unit_config U -> Rabs (f U) <= 1.
    Variable n0 : nat.
    Hypothesis P_in : incl P (su2_box n0).

    Definition Ccst : R :=
      2 * exp (2 * Rabs beta) * (INR (length P) * (972 * exp (INR (S n0) * ln 16))).

    Lemma Ccst_nonneg : 0 <= Ccst.
    Proof.
      unfold Ccst.
      pose proof (exp_pos (2 * Rabs beta)) as H1.
      pose proof (exp_pos (INR (S n0) * ln 16)) as H2.
      pose proof (pos_INR (length P)) as H3.
      apply Rmult_le_pos; [lra |]. apply Rmult_le_pos; [exact H3 | lra].
    Qed.

    Lemma compare_box : forall (m : nat) (Lam : list Plaq4D) (w vm : R),
      (n0 <= m)%nat -> NoDup Lam -> Forall wf_plaq_4D Lam -> incl (su2_box m) Lam ->
      su2_haar_expect_is beta Lam f w ->
      su2_haar_expect_is beta (su2_box m) f vm ->
      Rabs (w - vm) <= Ccst * (/ 2) ^ m.
    Proof.
      intros m Lam w vm Hm Hnd Hwf Hincl Hw Hvm.
      set (inb := fun q : Plaq4D => existsb (Z2GaugeClustering.plaq4D_eqb q) (su2_box m)).
      assert (Hinb : forall q, inb q = true <-> In q (su2_box m)).
      { intro q. unfold inb. rewrite existsb_exists. split.
        - intros [x [Hx He]]. apply Z2GaugeClustering.plaq4D_eqb_spec in He.
          subst x. exact Hx.
        - intro Hq. exists q. split; [exact Hq |].
          apply Z2GaugeClustering.plaq4D_eqb_spec. reflexivity. }
      set (Q := filter (fun q => negb (inb q)) Lam).
      assert (HQ : forall q, In q Q <-> In q Lam /\ ~ In q (su2_box m)).
      { intro q. unfold Q. rewrite filter_In, negb_true_iff. split.
        - intros [H1 H2]. split; [exact H1 |]. intro Hin.
          apply (proj2 (Hinb q)) in Hin. congruence.
        - intros [H1 H2]. split; [exact H1 |].
          destruct (inb q) eqn:Hb; [| reflexivity].
          exfalso. apply H2. apply (proj1 (Hinb q)). exact Hb. }
      assert (HQnd : NoDup Q) by (apply NoDup_filter; exact Hnd).
      assert (HndQ : NoDup (Q ++ su2_box m)).
      { apply ProductMeasurePerm.nodup_app;
          [exact HQnd | apply LatticeBoxes.box_nodup |].
        intros a Ha. exact (proj2 (proj1 (HQ a) Ha)). }
      assert (Hperm : Permutation Lam (Q ++ su2_box m)).
      { apply NoDup_Permutation; [exact Hnd | exact HndQ |].
        intro x. rewrite in_app_iff. split.
        - intro Hx. destruct (inb x) eqn:Hb.
          + right. apply (proj1 (Hinb x)). exact Hb.
          + left. apply (proj2 (HQ x)). split; [exact Hx |].
            intro Hin. apply (proj2 (Hinb x)) in Hin. congruence.
        - intros [Hx | Hx]; [exact (proj1 (proj1 (HQ x) Hx)) | exact (Hincl x Hx)]. }
      assert (HwfQ : Forall wf_plaq_4D (Q ++ su2_box m)).
      { apply Forall_forall. intros x Hx.
        apply (proj1 (Forall_forall wf_plaq_4D Lam) Hwf).
        exact (Permutation_in x (Permutation_sym Hperm) Hx). }
      assert (HQwf : Forall wf_plaq_4D Q).
      { apply Forall_forall. intros x Hx.
        apply (proj1 (Forall_forall wf_plaq_4D Lam) Hwf). exact (proj1 (proj1 (HQ x) Hx)). }
      assert (HPm : incl P (su2_box m)).
      { intros p Hp. exact (LatticeBoxes.box_mono n0 m Hm p (P_in p Hp)). }
      eapply Rle_trans;
        [exact (SU2InfiniteVolume.haar_volume_dependence beta Hbeta P f f_loc f_bd
                  Lam (su2_box m) Q w vm Hperm HndQ HwfQ HPm Hw Hvm) |].
      pose proof (exp_pos (2 * Rabs beta)) as He.
      rewrite (rsum_swap Q P
                 (fun q p => exp (- SU2InfiniteVolume.mu0 * (plaq4D_dist p q - 1)))).
      apply Rle_trans with
        (2 * exp (2 * Rabs beta) *
         rsum P (fun _ => 972 * exp (INR (S n0) * ln 16) * (/ 2) ^ m)).
      - apply Rmult_le_compat_l; [lra |]. apply rsum_le. intros p Hp.
        exact (LatticeBoxesTail.outside_box_sum n0 m p Q Hm (P_in p Hp) HQnd HQwf
                 (fun q Hq => proj2 (proj1 (HQ q) Hq))).
      - rewrite ProductMeasure.rsum_const. unfold Ccst. apply Req_le. ring.
    Qed.

    Lemma uniqueness_bounded : forall (Lam : nat -> list Plaq4D) (w : nat -> R) (v : R),
      (forall k, NoDup (Lam k)) ->
      (forall k, Forall wf_plaq_4D (Lam k)) ->
      (forall m, exists K : nat, forall k, (K <= k)%nat -> incl (su2_box m) (Lam k)) ->
      (forall k, su2_haar_expect_is beta (Lam k) f (w k)) ->
      su2_infinite_volume_expect_is beta f v ->
      Un_cv w v.
    Proof.
      intros Lam w v Hnd Hwf Hex Hw [vn [Hvn Hcv]] eps Heps.
      pose proof Ccst_nonneg as HC.
      set (dl := eps / (2 * (Ccst + 1))).
      assert (Hdl : 0 < dl) by (unfold dl; apply Rdiv_lt_0_compat; lra).
      assert (Hdl2 : (Ccst + 1) * dl = eps / 2) by (unfold dl; field; lra).
      destruct (SU2InfiniteVolume.half_pow_small dl Hdl) as [N1 HN1].
      assert (He2 : eps / 2 > 0) by lra.
      destruct (Hcv (eps / 2) He2) as [N2 HN2].
      set (m := Nat.max n0 (Nat.max N1 N2)).
      assert (Hm0 : (n0 <= m)%nat) by apply Nat.le_max_l.
      assert (Hm1 : (N1 <= m)%nat).
      { unfold m. eapply Nat.le_trans; [apply Nat.le_max_l | apply Nat.le_max_r]. }
      assert (Hm2 : (m >= N2)%nat).
      { unfold m, ge. eapply Nat.le_trans; [apply Nat.le_max_r | apply Nat.le_max_r]. }
      destruct (Hex m) as [K HK]. exists K. intros k Hk.
      pose proof (compare_box m (Lam k) (w k) (vn m) Hm0 (Hnd k) (Hwf k) (HK k Hk)
                    (Hw k) (Hvn m)) as H1.
      pose proof (HN2 m Hm2) as H2. unfold R_dist in H2.
      pose proof (HN1 m Hm1) as H3.
      assert (H4 : Ccst * (/ 2) ^ m <= Ccst * dl).
      { apply Rmult_le_compat_l; [exact HC | lra]. }
      unfold R_dist.
      replace (w k - v) with ((w k - vn m) + (vn m - v)) by ring.
      eapply Rle_lt_trans; [apply Rabs_triang |]. lra.
    Qed.
  End Core.

  (* =======================================================================
     4. TARGET 10a
     ======================================================================= *)

  Theorem su2_infinite_volume_uniqueness : Challenge_SU2Gauge4D_InfiniteVolumeUniqueness.
  Proof.
    intros beta P f Lam w v Hbeta HPwf Hloc Hbc Hnd Hwf Hex Hw Hv.
    destruct (LatticeBoxes.box_exhaust P HPwf) as [n0 Hn0].
    destruct Hbc as [[M HM] _].
    set (c := Rmax M 1).
    assert (Hc1 : 1 <= c) by apply Rmax_r.
    assert (HcM : M <= c) by apply Rmax_l.
    set (f1 := fun U : SU2Config => / c * f U).
    assert (Hf1_loc : su2_local_on f1 P).
    { intros U U' H. unfold f1. rewrite (Hloc U U' H). reflexivity. }
    assert (Hf1_bd : forall U, su2_unit_config U -> Rabs (f1 U) <= 1).
    { intros U HU. unfold f1.
      rewrite Rabs_mult, (Rabs_pos_eq (/ c)) by (left; apply Rinv_0_lt_compat; lra).
      pose proof (HM U HU) as H1.
      apply Rmult_le_reg_l with c; [lra |].
      rewrite <- Rmult_assoc, Rinv_r by lra. lra. }
    pose proof (uniqueness_bounded beta Hbeta P f1 Hf1_loc Hf1_bd n0 Hn0
                  Lam (fun k => / c * w k) (/ c * v) Hnd Hwf Hex
                  (fun k => haar_scal beta (Lam k) (/ c) f (w k) (Hw k))
                  (inf_scal beta (/ c) f v Hv)) as H1.
    apply (SU2HaarLimit.cv_ext (fun k => c * (/ c * w k))).
    - intro k. field. lra.
    - replace v with (c * (/ c * v)) by (field; lra).
      exact (CV_mult (fun _ => c) (fun k => / c * w k) c (/ c * v)
               (SU2InfiniteVolume.cv_const c) H1).
  Qed.

  (* =======================================================================
     5. Sequences of Haar-measure expectations, and limits from an index on
     ======================================================================= *)

  (* The Haar-measure expectations of f along a sequence of volumes, as a
     sequence of real numbers: obtained from the completeness of R, without
     any choice axiom. *)
  Lemma haar_seq_exists : forall beta (Lam : nat -> list Plaq4D) (f : SU2Config -> R),
    su2_bounded_continuous f ->
    exists w : nat -> R, forall k, su2_haar_expect_is beta (Lam k) f (w k).
  Proof.
    intros beta Lam f Hbc.
    assert (Hc : forall k,
              Cauchy_crit (fun n => su2_expect_on (su2_grid n) beta (Lam k) f)).
    { intro k. destruct (SU2HaarLimit.haar_state_exists beta (Lam k) f Hbc) as [v Hv].
      exact (CV_Cauchy (fun n => su2_expect_on (su2_grid n) beta (Lam k) f)
               (exist (fun l => Un_cv (fun n => su2_expect_on (su2_grid n) beta (Lam k) f) l)
                      v Hv)). }
    exists (fun k =>
              proj1_sig (R_complete (fun n => su2_expect_on (su2_grid n) beta (Lam k) f)
                           (Hc k))).
    intro k.
    exact (proj2_sig (R_complete (fun n => su2_expect_on (su2_grid n) beta (Lam k) f)
                        (Hc k))).
  Qed.

  Lemma cv_ext_from : forall (u v : nat -> R) (l : R) (n0 : nat),
    (forall n, (n0 <= n)%nat -> u n = v n) -> Un_cv u l -> Un_cv v l.
  Proof.
    intros u v l n0 H Hu eps Heps. destruct (Hu eps Heps) as [N HN].
    exists (Nat.max N n0). intros n Hn.
    rewrite <- (H n) by lia. apply HN. lia.
  Qed.

  Lemma cv_nonneg_from : forall (u : nat -> R) (l : R) (n0 : nat),
    Un_cv u l -> (forall n, (n0 <= n)%nat -> 0 <= u n) -> 0 <= l.
  Proof.
    intros u l n0 Hcv H.
    destruct (Rle_lt_dec 0 l) as [Hl | Hl]; [exact Hl | exfalso].
    assert (Heps : - l / 2 > 0) by lra.
    destruct (Hcv _ Heps) as [N HN].
    assert (H1 : R_dist (u (Nat.max N n0)) l < - l / 2) by (apply HN; lia).
    assert (H2 : 0 <= u (Nat.max N n0)) by (apply H; lia).
    unfold R_dist in H1. apply Rabs_def2 in H1. lra.
  Qed.

End SU2Uniqueness.
