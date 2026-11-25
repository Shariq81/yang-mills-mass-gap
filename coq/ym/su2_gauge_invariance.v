(* =========================================================================
   ym/su2_gauge_invariance.v

   Gauge invariance of the Haar-measure Gibbs states of the 4D SU(2) Wilson
   lattice gauge theory, in finite volume (TARGET 11b) and in infinite
   volume (TARGET 11c).

     - the plaquette variables and the Wilson action are invariant under
       gauge transformations  U(x, mu) |-> g(x) U(x, mu) g(x + mu)^{-1};
     - a gauge transformation acts on each link variable by a left and a
       right translation, under which the Hopf-grid averages are
       asymptotically invariant, uniformly over equicontinuous families
       (ym/su2_haar_invariance.v); treating the links one at a time, the
       normalized grid sums of Phi o g and of Phi differ by at most
       (number of links) * (2 M + 3) * eps  for large grids;
     - the Boltzmann weight being gauge invariant, the Gibbs expectations
       of F o g and of F have the same limit.

   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import verification.ChallengeSU2GaugeInvariance.
Require Import rg.dup_clustering.
Require Import ym.z2_gauge_expansion.
Require Import ym.su2_algebra.
Require Import ym.su2_continuity.
Require Import ym.su2_haar_grid.
Require Import ym.su2_haar_limit.
Require Import ym.su2_volume.
Require Import ym.lattice_boxes.
Require Import ym.lattice_symmetry.
Require Import ym.su2_uniqueness.
Require Import ym.su2_haar_mean.
Require Import ym.su2_haar_invariance.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeSU2Gauge ChallengeSU2InfiniteVolume.
Import ChallengeSU2GaugeInvariance.
Import DupClustering Z2GaugeExpansion SU2Algebra SU2HaarGrid SU2HaarMean.
Open Scope R_scope.

Module SU2GaugeInvariance.

  (* =======================================================================
     1. Quaternion algebra
     ======================================================================= *)

  Lemma qconj_mul : forall p q, qconj (qmul p q) = qmul (qconj q) (qconj p).
  Proof.
    intros p q. apply quat_eq; unfold qconj, qmul; cbn [qr qi qj qk]; ring.
  Qed.

  Lemma unit_conj_l : forall g, su2_unit g -> qmul (qconj g) g = qone.
  Proof.
    intros [a b c d] H. unfold su2_unit, qnorm2 in H. cbn [qr qi qj qk] in H.
    apply quat_eq; unfold qmul, qconj, qone; cbn [qr qi qj qk];
      [rewrite <- H; ring | ring | ring | ring].
  Qed.

  (* a U b^{-1} *)
  Definition gt (a U b : Quat) : Quat := qmul a (qmul U (qconj b)).

  Lemma gt_mul : forall a b c U V, su2_unit b ->
    qmul (gt a U b) (gt b V c) = gt a (qmul U V) c.
  Proof.
    intros a b c U V Hb. unfold gt. rewrite <- !qmul_assoc.
    rewrite (qmul_assoc (qconj b) b), (unit_conj_l b Hb), qmul_one_l. reflexivity.
  Qed.

  Lemma gt_conj : forall a U b, qconj (gt a U b) = gt b (qconj U) a.
  Proof.
    intros a U b. unfold gt.
    rewrite !qconj_mul, LatticeSymmetry.qconj_invol, <- qmul_assoc. reflexivity.
  Qed.

  Lemma qr_gt : forall g X, su2_unit g -> qr (gt g X g) = qr X.
  Proof.
    intros [a b c d] [x y z w] H. unfold su2_unit, qnorm2 in H.
    cbn [qr qi qj qk] in H. unfold gt, qmul, qconj. cbn [qr qi qj qk].
    transitivity ((a * a + b * b + c * c + d * d) * x); [ring | rewrite H; ring].
  Qed.

  Lemma gt_unit : forall a U b, su2_unit a -> su2_unit U -> su2_unit b ->
    su2_unit (gt a U b).
  Proof.
    intros a U b Ha HU Hb. unfold gt.
    apply unit_mul; [exact Ha |]. apply unit_mul; [exact HU | apply unit_conj; exact Hb].
  Qed.

  (* =======================================================================
     2. Gauge transformations
     ======================================================================= *)

  Lemma gauge_link : forall g U l,
    su2_gauge g U l = gt (g (fst l)) (U l) (g (shift4D (fst l) (snd l))).
  Proof. reflexivity. Qed.

  Lemma plaq_gauge : forall (g : Site4D -> Quat) U p,
    (forall x, su2_unit (g x)) ->
    su2_plaq (su2_gauge g U) p = su2_plaq U p.
  Proof.
    intros g U p Hg. rewrite !LatticeSymmetry.plaq_formula.
    rewrite !gauge_link. cbn [fst snd]. rewrite !gt_conj.
    rewrite (LatticeSymmetry.shift_comm (p4_site p) (p4_nu p) (p4_mu p)).
    rewrite !gt_mul by apply Hg. apply qr_gt. apply Hg.
  Qed.

  Lemma action_gauge : forall beta (L : list Plaq4D) (g : Site4D -> Quat) U,
    (forall x, su2_unit (g x)) ->
    su2_wilson_action beta L (su2_gauge g U) = su2_wilson_action beta L U.
  Proof.
    intros beta L g U Hg. unfold su2_wilson_action.
    assert (E : map (su2_plaq (su2_gauge g U)) L = map (su2_plaq U) L).
    { apply map_ext. intro p. apply plaq_gauge. exact Hg. }
    rewrite E. reflexivity.
  Qed.

  Lemma gauge_unit : forall (g : Site4D -> Quat) U,
    (forall x, su2_unit (g x)) -> su2_unit_config U ->
    su2_unit_config (su2_gauge g U).
  Proof.
    intros g U Hg HU l. rewrite gauge_link. apply gt_unit; [apply Hg | apply HU | apply Hg].
  Qed.

  Lemma gauge_update : forall (g : Site4D -> Quat) U l q,
    su2_gauge g (su2_update U l q) =
    su2_update (su2_gauge g U) l (gt (g (fst l)) q (g (shift4D (fst l) (snd l)))).
  Proof.
    intros g U l q. apply functional_extensionality. intro l'.
    unfold su2_gauge, su2_update, gt.
    destruct (link4D_eqb l' l) eqn:E; [| reflexivity].
    apply link4D_eqb_spec in E. subst l'. reflexivity.
  Qed.

  Lemma gauge_close : forall (g : Site4D -> Quat) U U' d,
    (forall x, su2_unit (g x)) -> 0 < d ->
    su2_unit_config U -> su2_unit_config U' ->
    (forall l, su2_close d (U l) (U' l)) ->
    forall l, su2_close (8 * (8 * d)) (su2_gauge g U l) (su2_gauge g U' l).
  Proof.
    intros g U U' d Hg Hd HU HU' Hcl l. unfold su2_gauge.
    set (A := g (fst l)). set (B := qconj (g (shift4D (fst l) (snd l)))).
    assert (HA : su2_unit A) by apply Hg.
    assert (HB : su2_unit B) by (apply unit_conj; apply Hg).
    apply SU2Continuity.close_mul.
    - exact HA.
    - apply unit_mul; [apply HU' | exact HB].
    - apply SU2Continuity.close_refl. lra.
    - apply SU2Continuity.close_mul;
        [apply HU | exact HB | apply Hcl | apply SU2Continuity.close_refl; exact Hd].
  Qed.

  Lemma bc_gauge : forall (g : Site4D -> Quat) (F : SU2Config -> R),
    (forall x, su2_unit (g x)) -> su2_bounded_continuous F ->
    su2_bounded_continuous (fun U => F (su2_gauge g U)).
  Proof.
    intros g F Hg [[M HM] Hc]. split.
    - exists M. intros U HU. apply HM. apply gauge_unit; assumption.
    - intros eps He. destruct (Hc eps He) as [delta [Hd H]].
      exists (delta / 64). split; [lra |]. intros U U' HU HU' Hcl.
      apply H; [apply gauge_unit; assumption | apply gauge_unit; assumption |].
      intro l.
      replace delta with (8 * (8 * (delta / 64))) by field.
      apply gauge_close; [exact Hg | lra | exact HU | exact HU' | exact Hcl].
  Qed.

  (* =======================================================================
     3. Iterated grid means
     ======================================================================= *)

  Lemma update_close : forall d U U' l q q', 0 < d ->
    (forall l0, su2_close d (U l0) (U' l0)) -> su2_close d q q' ->
    forall l0, su2_close d (su2_update U l q l0) (su2_update U' l q' l0).
  Proof.
    intros d U U' l q q' Hd H Hq l0. unfold su2_update.
    destruct (link4D_eqb l0 l); [exact Hq | apply H].
  Qed.

  Lemma avgR_close : forall N E (Phi : SU2Config -> R) delta eps,
    (0 < N)%nat -> 0 < delta ->
    (forall V V', su2_unit_config V -> su2_unit_config V' ->
       (forall l, su2_close delta (V l) (V' l)) -> Rabs (Phi V - Phi V') <= eps) ->
    forall U U', su2_unit_config U -> su2_unit_config U' ->
      (forall l, su2_close delta (U l) (U' l)) ->
      Rabs (avgR N E Phi U - avgR N E Phi U') <= eps.
  Proof.
    intros N E Phi delta eps HN Hd HPhi.
    induction E as [| l E IH]; intros U U' HU HU' Hcl.
    - cbn [avgR]. apply HPhi; assumption.
    - cbn [avgR].
      apply mean_close; [exact HN |]. intros i Hi.
      apply mean_close; [exact HN |]. intros j Hj.
      apply mean_close; [exact HN |]. intros k Hk.
      apply IH.
      + apply unit_config_update; [exact HU | apply gpt_unit; exact Hi].
      + apply unit_config_update; [exact HU' | apply gpt_unit; exact Hi].
      + apply update_close; [exact Hd | exact Hcl |].
        apply SU2Continuity.close_refl. exact Hd.
  Qed.

  (* the base configuration only matters on the links that are not averaged *)
  Lemma avgR_local : forall N (S E : list Link4D) (Phi : SU2Config -> R),
    (forall V V', (forall l, In l S -> V l = V' l) -> Phi V = Phi V') ->
    forall U U', (forall l, In l S -> ~ In l E -> U l = U' l) ->
      avgR N E Phi U = avgR N E Phi U'.
  Proof.
    intros N S E Phi HPhi. induction E as [| a E IH]; intros U U' H.
    - cbn [avgR]. apply HPhi. intros l Hl. apply H; [exact Hl | intros []].
    - cbn [avgR].
      apply mean_ext. intros i _. apply mean_ext. intros j _. apply mean_ext. intros k _.
      apply IH. intros l Hl HnE. unfold su2_update.
      destruct (link4D_eqb l a) eqn:E0; [reflexivity |].
      apply H; [exact Hl |]. intros [Heq | Hin]; [| exact (HnE Hin)].
      subst a. rewrite (proj2 (link4D_eqb_spec l l) eq_refl) in E0. discriminate.
  Qed.

  Lemma avgn_avgR : forall (Lambda : list Plaq4D) n (Phi : SU2Config -> R),
    SU2HaarLimit.avgn Lambda n Phi = avgR (2 ^ n) (z2_links Lambda) Phi (fun _ => qone).
  Proof.
    intros Lambda n Phi. unfold SU2HaarLimit.avgn. rewrite grid_gridN.
    apply avgR_eq. apply pow2_pos.
  Qed.

  (* =======================================================================
     4. Gauge invariance of the Gibbs states
     ======================================================================= *)

  Section Gauge.
    Variable g : Site4D -> Quat.
    Hypothesis g_unit : forall x, su2_unit (g x).

    Lemma avgR_gauge : forall (Phi : SU2Config -> R) (M delta eps : R),
      0 <= M -> 0 < delta -> 0 < eps ->
      (forall V, su2_unit_config V -> Rabs (Phi V) <= M) ->
      (forall V V', su2_unit_config V -> su2_unit_config V' ->
         (forall l, su2_close delta (V l) (V' l)) -> Rabs (Phi V - Phi V') <= eps) ->
      exists n1 : nat, forall (n : nat) (E : list Link4D) (U : SU2Config),
        (n1 <= n)%nat -> su2_unit_config U ->
        Rabs (avgR (2 ^ n) E (fun V => Phi (su2_gauge g V)) U
              - avgR (2 ^ n) E Phi (su2_gauge g U))
        <= INR (length E) * ((2 * M + 3) * eps).
    Proof.
      intros Phi M delta eps HM Hd He Hbd Hmod.
      destruct (SU2HaarInvariance.haar_isometry_uniform M delta eps HM Hd He) as [n1 Hn1]. exists n1.
      intros n E. induction E as [| l E IH]; intros U Hn HU.
      - cbn [avgR length INR].
        replace (Phi (su2_gauge g U) - Phi (su2_gauge g U)) with 0 by ring.
        rewrite Rabs_R0. lra.
      - cbn [length]. rewrite S_INR.
        pose proof (pow2_pos n) as HN.
        set (a := g (fst l)). set (b := g (shift4D (fst l) (snd l))).
        assert (Ha : su2_unit a) by apply g_unit.
        assert (Hb : su2_unit b) by apply g_unit.
        set (H := fun q : Quat =>
                    avgR (2 ^ n) E Phi (su2_update (su2_gauge g U) l q)).
        assert (HTU : su2_unit_config (su2_gauge g U))
          by (apply gauge_unit; assumption).
        (* step 1: the links of E, by induction *)
        assert (S1 : Rabs (avgR (2 ^ n) (l :: E) (fun V => Phi (su2_gauge g V)) U
                           - gmean n (fun q => H (gt a q b)))
                     <= INR (length E) * ((2 * M + 3) * eps)).
        { rewrite gmean_mean. cbn [avgR].
          apply mean_close; [exact HN |]. intros i Hi.
          apply mean_close; [exact HN |]. intros j Hj.
          apply mean_close; [exact HN |]. intros k Hk.
          unfold H, a, b. rewrite <- gauge_update.
          apply IH; [exact Hn |].
          apply unit_config_update; [exact HU | apply gpt_unit; exact Hi]. }
        (* step 2: the link l, by the invariance of the Haar measure *)
        assert (S2 : Rabs (gmean n (fun q => H (gt a q b))
                           - avgR (2 ^ n) (l :: E) Phi (su2_gauge g U))
                     <= (2 * M + 3) * eps).
        { assert (E2 : avgR (2 ^ n) (l :: E) Phi (su2_gauge g U) = gmean n H).
          { rewrite gmean_mean. reflexivity. }
          rewrite E2.
          apply (Hn1 n n (fun q => gt a q b)
                   (fun y => qmul (qconj a) (qmul y (qconj (qconj b)))) H Hn Hn).
          - intros x Hx. apply gt_unit; assumption.
          - intros y Hy. apply unit_mul; [apply unit_conj; exact Ha |].
            apply unit_mul; [exact Hy |]. apply unit_conj. apply unit_conj. exact Hb.
          - intros x y _ _. unfold gt.
            apply SU2HaarInvariance.qdot_translate.
          - intros u Hu. unfold H. apply Rabs_le.
            apply (avgR_bounds (2 ^ n) E Phi (- M) M HN).
            + intros V HV. apply abs_le_inv. apply Hbd. exact HV.
            + apply unit_config_update; assumption.
          - intros u v Hu Hv Hcl. unfold H.
            apply (avgR_close (2 ^ n) E Phi delta eps HN Hd Hmod).
            + apply unit_config_update; assumption.
            + apply unit_config_update; assumption.
            + apply update_close; [exact Hd | | exact Hcl].
              intro l0. apply SU2Continuity.close_refl. exact Hd. }
        replace (avgR (2 ^ n) (l :: E) (fun V => Phi (su2_gauge g V)) U
                 - avgR (2 ^ n) (l :: E) Phi (su2_gauge g U))
          with ((avgR (2 ^ n) (l :: E) (fun V => Phi (su2_gauge g V)) U
                 - gmean n (fun q => H (gt a q b)))
                + (gmean n (fun q => H (gt a q b))
                   - avgR (2 ^ n) (l :: E) Phi (su2_gauge g U))) by ring.
        eapply Rle_trans; [apply Rabs_triang |]. lra.
    Qed.

    (* TARGET 11b *)
    Theorem haar_gauge_invariance :
      forall (beta : R) (Lambda P : list Plaq4D) (F : SU2Config -> R) (v : R),
        incl P Lambda ->
        su2_local_on F P ->
        su2_bounded_continuous F ->
        su2_haar_expect_is beta Lambda F v ->
        su2_haar_expect_is beta Lambda (fun U => F (su2_gauge g U)) v.
    Proof.
      intros beta Lambda P F v HP Hloc Hbc Hv.
      set (E := z2_links Lambda).
      set (w := fun U : SU2Config => exp (- su2_wilson_action beta Lambda U)).
      set (Phi := fun U : SU2Config => F U * w U).
      assert (HbcPhi : su2_bounded_continuous Phi).
      { exact (SU2Continuity.bc_mult F w Hbc (SU2Continuity.bc_boltzmann beta Lambda)). }
      destruct HbcPhi as [[M0 HM0] HcPhi].
      set (M := Rmax M0 0).
      assert (HM : 0 <= M) by (unfold M; apply Rmax_r).
      assert (HbM : forall V, su2_unit_config V -> Rabs (Phi V) <= M).
      { intros V HV. eapply Rle_trans; [apply HM0; exact HV | unfold M; apply Rmax_l]. }
      (* Phi depends only on the links of the volume *)
      assert (HlocPhi : forall V V', (forall l, In l E -> V l = V' l) -> Phi V = Phi V').
      { intros V V' H. unfold Phi, w.
        rewrite (Hloc V V').
        - rewrite (SU2Volume.action_local beta Lambda V V' H). reflexivity.
        - intros p l Hp Hl. apply H.
          exact (SU2Volume.links_in Lambda p l (HP p Hp) Hl). }
      (* the transformed integrand *)
      assert (Hfun : (fun U : SU2Config => F (su2_gauge g U) * w U)
                     = (fun U : SU2Config => Phi (su2_gauge g U))).
      { apply functional_extensionality. intro U. unfold Phi, w.
        rewrite (action_gauge beta Lambda g U g_unit). reflexivity. }
      set (c := exp (- (Rabs beta * INR (length Lambda)))).
      assert (Hc : 0 < c) by (unfold c; apply exp_pos).
      (* the numerators have the same limit *)
      assert (Hnum : forall eps, 0 < eps -> exists n1 : nat, forall n, (n1 <= n)%nat ->
                Rabs (SU2HaarLimit.avgn Lambda n (fun U => F (su2_gauge g U) * w U)
                      - SU2HaarLimit.avgn Lambda n Phi) <= eps).
      { intros eps He.
        set (K := (INR (length E) + 1) * (2 * M + 3)).
        pose proof (pos_INR (length E)) as HE0.
        assert (HK : 0 < K) by (unfold K; apply Rmult_lt_0_compat; lra).
        set (eps0 := eps / K).
        assert (He0 : 0 < eps0) by (unfold eps0; apply Rdiv_lt_0_compat; lra).
        destruct (HcPhi eps0 He0) as [delta [Hd Hmod]].
        destruct (avgR_gauge Phi M delta eps0 HM Hd He0 HbM
                    (fun V V' HV HV' Hcl => Rlt_le _ _ (Hmod V V' HV HV' Hcl)))
          as [n1 Hn1].
        exists n1. intros n Hn. rewrite Hfun, !avgn_avgR. fold E.
        pose proof (Hn1 n E (fun _ => qone) Hn unit_config_one) as H1.
        rewrite (avgR_local (2 ^ n) E E Phi HlocPhi
                   (su2_gauge g (fun _ => qone)) (fun _ => qone)) in H1.
        - eapply Rle_trans; [exact H1 |].
          assert (E1 : eps = K * eps0) by (unfold eps0; field; lra).
          rewrite E1. unfold K.
          assert (Q : 0 <= (2 * M + 3) * eps0) by (apply Rmult_le_pos; lra).
          nra.
        - intros l Hl Hnl. contradiction. }
      (* hence so do the expectations *)
      intros eta Heta.
      assert (Hec : 0 < eta / 2 * c) by (apply Rmult_lt_0_compat; lra).
      assert (He2 : 0 < eta / 2) by lra.
      destruct (Hnum (eta / 2 * c) Hec) as [n1 Hn1].
      destruct (Hv (eta / 2) He2) as [N2 HN2].
      exists (Nat.max n1 N2). intros n Hn. unfold R_dist.
      assert (Hn1' : (n1 <= n)%nat) by lia.
      assert (Hn2' : (n >= N2)%nat) by lia.
      pose proof (Hn1 n Hn1') as E1.
      pose proof (HN2 n Hn2') as E2. unfold R_dist in E2.
      rewrite (SU2HaarLimit.expect_avg beta Lambda n) in E2 |- *.
      fold w in E2 |- *. fold Phi in E2.
      pose proof (SU2HaarLimit.avg_den_lower beta Lambda n) as HD. fold w c in HD.
      set (D := SU2HaarLimit.avgn Lambda n w) in *.
      set (A' := SU2HaarLimit.avgn Lambda n (fun U => F (su2_gauge g U) * w U)) in *.
      set (A := SU2HaarLimit.avgn Lambda n Phi) in *.
      assert (HDp : 0 < D) by lra.
      assert (E3 : Rabs (A' / D - A / D) <= eta / 2).
      { replace (A' / D - A / D) with ((A' - A) * / D) by (field; lra).
        rewrite Rabs_mult, (Rabs_pos_eq (/ D)) by (left; apply Rinv_0_lt_compat; exact HDp).
        apply Rmult_le_reg_r with D; [exact HDp |].
        rewrite Rmult_assoc, Rinv_l, Rmult_1_r by lra.
        apply Rle_trans with (eta / 2 * c); [exact E1 |].
        apply Rmult_le_compat_l; lra. }
      assert (E4 : Rabs (A / D - v) < eta / 2) by exact E2.
      change (Rabs (A' / D - v) < eta).
      replace (A' / D - v) with ((A' / D - A / D) + (A / D - v)) by ring.
      eapply Rle_lt_trans; [apply Rabs_triang |]. lra.
    Qed.

    (* TARGET 11c *)
    Theorem infinite_volume_gauge_invariance :
      forall (beta : R) (P : list Plaq4D) (F : SU2Config -> R) (v : R),
        Forall wf_plaq_4D P ->
        su2_local_on F P ->
        su2_bounded_continuous F ->
        su2_infinite_volume_expect_is beta F v ->
        su2_infinite_volume_expect_is beta (fun U => F (su2_gauge g U)) v.
    Proof.
      intros beta P F v HP Hloc Hbc [vn [Hvn Hcv]].
      destruct (LatticeBoxes.box_exhaust P HP) as [n0 Hn0].
      destruct (SU2Uniqueness.haar_seq_exists beta su2_box
                  (fun U => F (su2_gauge g U)) (bc_gauge g F g_unit Hbc)) as [w Hw].
      exists w. split; [exact Hw |].
      apply (SU2Uniqueness.cv_ext_from vn w v n0); [| exact Hcv].
      intros n Hn.
      apply (SU2Uniqueness.haar_unique beta (su2_box n) (fun U => F (su2_gauge g U)));
        [| exact (Hw n)].
      apply (haar_gauge_invariance beta (su2_box n) P F (vn n)); [| exact Hloc | exact Hbc
                                                                 | exact (Hvn n)].
      intros p Hp. exact (LatticeBoxes.box_mono n0 n Hn p (Hn0 p Hp)).
    Qed.
  End Gauge.

  (* TARGET 11b *)
  Theorem su2_haar_gauge_invariance : Challenge_SU2Gauge4D_HaarGaugeInvariance.
  Proof.
    intros beta Lambda P F g v HP Hloc Hbc Hg Hv.
    exact (haar_gauge_invariance g Hg beta Lambda P F v HP Hloc Hbc Hv).
  Qed.

  (* TARGET 11c *)
  Theorem su2_infinite_volume_gauge_invariance :
    Challenge_SU2Gauge4D_InfiniteVolumeGaugeInvariance.
  Proof.
    intros beta P F g v HP Hloc Hbc Hg Hv.
    exact (infinite_volume_gauge_invariance g Hg beta P F v HP Hloc Hbc Hv).
  Qed.

End SU2GaugeInvariance.
