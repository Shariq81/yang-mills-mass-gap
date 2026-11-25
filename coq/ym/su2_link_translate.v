(* =========================================================================
   ym/su2_link_translate.v

   Link-wise translations of SU(2) gauge fields,
       (ltr a b U)(l) = a(l) U(l) b(l)^{-1},
   with arbitrary SU(2)-valued functions a, b on the links (gauge
   transformations are the special case a(l) = g(x), b(l) = g(x + mu)).

   `avgR_ltr`: the normalized Hopf-grid sums of Phi o ltr a b and of Phi
   differ by at most (number of links) * (2 M + 3) * eps for large grids,
   uniformly in a, b and in Phi (given a bound M and a modulus of
   continuity).  This is the uniform Haar invariance of
   ym/su2_haar_invariance.v applied to one link at a time.

   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2GaugeInvariance.
Require Import rg.dup_clustering.
Require Import ym.z2_gauge_expansion.
Require Import ym.su2_algebra.
Require Import ym.su2_continuity.
Require Import ym.su2_haar_grid.
Require Import ym.su2_haar_mean.
Require Import ym.su2_haar_invariance.
Require Import ym.su2_gauge_invariance.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeSU2Gauge ChallengeSU2GaugeInvariance.
Import DupClustering Z2GaugeExpansion SU2Algebra SU2HaarGrid SU2HaarMean.
Import SU2GaugeInvariance.
Open Scope R_scope.

Module SU2LinkTranslate.

  Definition ltr (a b : Link4D -> Quat) (U : SU2Config) : SU2Config :=
    fun l => gt (a l) (U l) (b l).

  Lemma ltr_unit : forall (a b : Link4D -> Quat) U,
    (forall l, su2_unit (a l)) -> (forall l, su2_unit (b l)) ->
    su2_unit_config U -> su2_unit_config (ltr a b U).
  Proof.
    intros a b U Ha Hb HU l. unfold ltr. apply gt_unit; [apply Ha | apply HU | apply Hb].
  Qed.

  Lemma ltr_update : forall (a b : Link4D -> Quat) U l q,
    ltr a b (su2_update U l q) = su2_update (ltr a b U) l (gt (a l) q (b l)).
  Proof.
    intros a b U l q. apply functional_extensionality. intro l'.
    unfold ltr, su2_update.
    destruct (link4D_eqb l' l) eqn:E; [| reflexivity].
    apply link4D_eqb_spec in E. subst l'. reflexivity.
  Qed.

  Lemma ltr_close : forall (a b : Link4D -> Quat) U U' d,
    (forall l, su2_unit (a l)) -> (forall l, su2_unit (b l)) -> 0 < d ->
    su2_unit_config U -> su2_unit_config U' ->
    (forall l, su2_close d (U l) (U' l)) ->
    forall l, su2_close (8 * (8 * d)) (ltr a b U l) (ltr a b U' l).
  Proof.
    intros a b U U' d Ha Hb Hd HU HU' Hcl l. unfold ltr, gt.
    assert (HB : su2_unit (qconj (b l))) by (apply unit_conj; apply Hb).
    apply SU2Continuity.close_mul.
    - apply Ha.
    - apply unit_mul; [apply HU' | exact HB].
    - apply SU2Continuity.close_refl. lra.
    - apply SU2Continuity.close_mul;
        [apply HU | exact HB | apply Hcl | apply SU2Continuity.close_refl; exact Hd].
  Qed.

  Theorem avgR_ltr : forall M delta eps : R,
    0 <= M -> 0 < delta -> 0 < eps ->
    exists n1 : nat,
      forall (n : nat) (a b : Link4D -> Quat) (Phi : SU2Config -> R)
             (E : list Link4D) (U : SU2Config),
        (n1 <= n)%nat ->
        (forall l, su2_unit (a l)) -> (forall l, su2_unit (b l)) ->
        (forall W, su2_unit_config W -> Rabs (Phi W) <= M) ->
        (forall W W', su2_unit_config W -> su2_unit_config W' ->
           (forall l, su2_close delta (W l) (W' l)) -> Rabs (Phi W - Phi W') <= eps) ->
        su2_unit_config U ->
        Rabs (avgR (2 ^ n) E (fun W => Phi (ltr a b W)) U
              - avgR (2 ^ n) E Phi (ltr a b U))
        <= INR (length E) * ((2 * M + 3) * eps).
  Proof.
    intros M delta eps HM Hd He.
    destruct (SU2HaarInvariance.haar_isometry_uniform M delta eps HM Hd He) as [n1 Hn1].
    exists n1. intros n a b Phi E U Hn Ha Hb Hbd Hmod. revert U.
    induction E as [| l E IH]; intros U HU.
    - cbn [avgR length INR].
      replace (Phi (ltr a b U) - Phi (ltr a b U)) with 0 by ring.
      rewrite Rabs_R0. lra.
    - cbn [length]. rewrite S_INR.
      pose proof (pow2_pos n) as HN.
      set (H := fun q : Quat => avgR (2 ^ n) E Phi (su2_update (ltr a b U) l q)).
      assert (HTU : su2_unit_config (ltr a b U)) by (apply ltr_unit; assumption).
      assert (S1 : Rabs (avgR (2 ^ n) (l :: E) (fun W => Phi (ltr a b W)) U
                         - gmean n (fun q => H (gt (a l) q (b l))))
                   <= INR (length E) * ((2 * M + 3) * eps)).
      { rewrite gmean_mean. cbn [avgR].
        apply mean_close; [exact HN |]. intros i Hi.
        apply mean_close; [exact HN |]. intros j Hj.
        apply mean_close; [exact HN |]. intros k Hk.
        unfold H. rewrite <- ltr_update.
        apply IH. apply unit_config_update; [exact HU | apply gpt_unit; exact Hi]. }
      assert (S2 : Rabs (gmean n (fun q => H (gt (a l) q (b l)))
                         - avgR (2 ^ n) (l :: E) Phi (ltr a b U))
                   <= (2 * M + 3) * eps).
      { assert (E2 : avgR (2 ^ n) (l :: E) Phi (ltr a b U) = gmean n H).
        { rewrite gmean_mean. reflexivity. }
        rewrite E2.
        apply (Hn1 n n (fun q => gt (a l) q (b l))
                 (fun y => qmul (qconj (a l)) (qmul y (qconj (qconj (b l))))) H Hn Hn).
        - intros x Hx. apply gt_unit; [apply Ha | exact Hx | apply Hb].
        - intros y Hy. apply unit_mul; [apply unit_conj; apply Ha |].
          apply unit_mul; [exact Hy |]. apply unit_conj. apply unit_conj. apply Hb.
        - intros x y _ _. unfold gt. apply SU2HaarInvariance.qdot_translate.
        - intros u Hu. unfold H. apply Rabs_le.
          apply (avgR_bounds (2 ^ n) E Phi (- M) M HN).
          + intros W HW. apply abs_le_inv. apply Hbd. exact HW.
          + apply unit_config_update; assumption.
        - intros u v Hu Hv Hcl. unfold H.
          apply (avgR_close (2 ^ n) E Phi delta eps HN Hd Hmod).
          + apply unit_config_update; assumption.
          + apply unit_config_update; assumption.
          + apply update_close; [exact Hd | | exact Hcl].
            intro l0. apply SU2Continuity.close_refl. exact Hd. }
      replace (avgR (2 ^ n) (l :: E) (fun W => Phi (ltr a b W)) U
               - avgR (2 ^ n) (l :: E) Phi (ltr a b U))
        with ((avgR (2 ^ n) (l :: E) (fun W => Phi (ltr a b W)) U
               - gmean n (fun q => H (gt (a l) q (b l))))
              + (gmean n (fun q => H (gt (a l) q (b l)))
                 - avgR (2 ^ n) (l :: E) Phi (ltr a b U))) by ring.
      eapply Rle_trans; [apply Rabs_triang |]. lra.
  Qed.

End SU2LinkTranslate.
