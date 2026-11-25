(* =========================================================================
   ym/su2_multi_clustering.v

   Exponential clustering of the 4D SU(2) Wilson lattice gauge theory at
   strong coupling for observables localized on arbitrary finite lists of
   plaquettes (TARGET 10d), proved directly for the frozen objects of
   `verification/ChallengeSU2MassGap.v`:

     |<f g> - <f><g>| <= 4 * sum_{p in P1} sum_{q in P2} exp(- mu (dist(p,q) - 1))

   first for every finite a-priori link distribution and every finite
   volume, then for the Haar-measure state, then in infinite volume.

   The abstract duplicate-system theorem `dup_clustering` is applied with
   the links of all plaquettes of P1 as seed and the links of all
   plaquettes of P2 as target.  Its chain sums are subadditive in the seed
   (`SU2Volume.reach_flat`) and in the target (`reach_target_flat` below),
   and each pair (p, q) is bounded as in Target 7b.

   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import verification.Verify.
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.su2_algebra.
Require Import ym.su2_clustering.
Require Import ym.su2_continuity.
Require Import ym.su2_haar_grid.
Require Import ym.su2_haar_limit.
Require Import ym.su2_volume.
Require Import ym.lattice_boxes.
Require Import ym.su2_infinite_volume.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import ChallengeSU2InfiniteVolume ChallengeSU2MassGap.
Import DupClustering Z2GaugeExpansion SU2Algebra.
Open Scope R_scope.

Module SU2MultiClustering.

  (* =======================================================================
     1. The chain sums are subadditive in the target
     ======================================================================= *)

  Section ReachTarget.
    Variable Lambda : list Plaq4D.
    Variable eps : R.
    Hypothesis eps_nonneg : 0 <= eps.

    Local Notation reachT :=
      (fun T : list Link4D => reach Link4D Plaq4D link4D_eqb plaq4D_links Lambda T eps).
    Local Notation touchI := (touchb Link4D link4D_eqb).

    Lemma touchb_target_app : forall S T1 T2 : list Link4D,
      touchI S (T1 ++ T2) = touchI S T1 || touchI S T2.
    Proof.
      intros S T1 T2. unfold touchb. induction S as [| e S IH].
      - reflexivity.
      - cbn [existsb]. rewrite IH. unfold memb. rewrite existsb_app.
        destruct (existsb (link4D_eqb e) T1), (existsb (link4D_eqb e) T2),
                 (existsb (fun e0 => existsb (link4D_eqb e0) T1) S),
                 (existsb (fun e0 => existsb (link4D_eqb e0) T2) S); reflexivity.
    Qed.

    Lemma touchb_target_nil : forall S : list Link4D, touchI S [] = false.
    Proof.
      intro S. unfold touchb. induction S as [| e S IH]; [reflexivity |].
      cbn [existsb]. rewrite IH. reflexivity.
    Qed.

    Lemma reach_target_app : forall k (S T1 T2 : list Link4D),
      reachT (T1 ++ T2) k S <= reachT T1 k S + reachT T2 k S.
    Proof.
      induction k as [| k IH]; intros S T1 T2; cbn [reach].
      - rewrite touchb_target_app.
        destruct (touchI S T1), (touchI S T2); cbn [orb]; lra.
      - rewrite <- rsum_plus. apply rsum_le. intros b _.
        destruct (touchI S (plaq4D_links b)); [| lra].
        apply Rle_trans with
          (eps * (reachT T1 k (plaq4D_links b) + reachT T2 k (plaq4D_links b))).
        + apply Rmult_le_compat_l; [exact eps_nonneg | apply IH].
        + apply Req_le. ring.
    Qed.

    Lemma reach_target_nil : forall k (S : list Link4D), reachT [] k S = 0.
    Proof.
      induction k as [| k IH]; intro S; cbn [reach].
      - rewrite touchb_target_nil. reflexivity.
      - apply rsum_zero. intros b _.
        destruct (touchI S (plaq4D_links b)); [rewrite IH; ring | reflexivity].
    Qed.

    Lemma reach_target_flat : forall k (S : list Link4D) (P2 : list Plaq4D),
      reachT (flat_map plaq4D_links P2) k S
      <= rsum P2 (fun q => reachT (plaq4D_links q) k S).
    Proof.
      intros k S P2. induction P2 as [| q P2 IH].
      - cbn [flat_map]. rewrite reach_target_nil, rsum_nil. apply Rle_refl.
      - cbn [flat_map]. rewrite rsum_cons.
        eapply Rle_trans; [apply reach_target_app |]. lra.
    Qed.
  End ReachTarget.

  (* =======================================================================
     2. Finite volume, finite a-priori distribution
     ======================================================================= *)

  Section Instance.
    Variable G : list Quat.
    Hypothesis G_nonempty : G <> [].
    Hypothesis G_unit : Forall su2_unit G.
    Variable beta : R.
    Variable Lambda : list Plaq4D.
    Hypothesis Hnd : NoDup Lambda.
    Hypothesis Hwf : Forall wf_plaq_4D Lambda.
    Variables f g : SU2Config -> R.
    Variables P1 P2 : list Plaq4D.
    Hypothesis P1_wf : Forall wf_plaq_4D P1.
    Hypothesis f_loc : su2_local_on f P1.
    Hypothesis g_loc : su2_local_on g P2.
    Hypothesis f_bd : forall U, su2_unit_config U -> Rabs (f U) <= 1.
    Hypothesis g_bd : forall U, su2_unit_config U -> Rabs (g U) <= 1.
    Variable mu : R.
    Hypothesis Hmu : 0 <= mu.
    Hypothesis Hsmall : 168 * Rabs beta <= exp (- mu).

    Local Notation mlowI := (Z2GaugeClustering.mlow beta).
    Local Notation epsI := (Z2GaugeClustering.epsv beta).
    Local Notation phiI := (SU2Clustering.phi beta).
    Local Notation Seed1 := (flat_map plaq4D_links P1).
    Local Notation Seed2 := (flat_map plaq4D_links P2).
    Local Notation reachTo :=
      (fun T : list Link4D => reach Link4D Plaq4D link4D_eqb plaq4D_links Lambda T epsI).

    Definition fcl (U : SU2Config) : R := SU2Clustering.clamp (f U).
    Definition gcl (U : SU2Config) : R := SU2Clustering.clamp (g U).

    Lemma fcl_local : forall A A' : Link4D -> Quat,
      (forall e, In e Seed1 -> A e = A' e) -> fcl A = fcl A'.
    Proof.
      intros A A' H. unfold fcl. rewrite (f_loc A A'); [reflexivity |].
      intros p l Hp Hl. apply H. apply in_flat_map. exists p. split; assumption.
    Qed.

    Lemma gcl_local : forall A A' : Link4D -> Quat,
      (forall e, In e Seed2 -> A e = A' e) -> gcl A = gcl A'.
    Proof.
      intros A A' H. unfold gcl. rewrite (g_loc A A'); [reflexivity |].
      intros p l Hp Hl. apply H. apply in_flat_map. exists p. split; assumption.
    Qed.

    Lemma fcl_osc : forall A A' : Link4D -> Quat, Rabs (fcl A - fcl A') <= 2.
    Proof. intros A A'. apply SU2Clustering.clamp_diff. Qed.

    Lemma gcl_osc : forall A A' : Link4D -> Quat, Rabs (gcl A - gcl A') <= 2.
    Proof. intros A A'. apply SU2Clustering.clamp_diff. Qed.

    Lemma chain_bound :
      rsum (seq 0 (S (length Lambda))) (fun k => reachTo Seed2 k Seed1)
      <= rsum P1 (fun p => rsum P2 (fun q => 2 * exp (- mu * (plaq4D_dist p q - 1)))).
    Proof.
      pose proof (Z2GaugeClustering.epsv_nonneg beta) as He.
      apply Rle_trans with
        (rsum (seq 0 (S (length Lambda)))
           (fun k => rsum P1 (fun p => rsum P2
              (fun q => reachTo (plaq4D_links q) k (plaq4D_links p))))).
      - apply rsum_le. intros k _.
        eapply Rle_trans; [exact (SU2Volume.reach_flat Lambda Seed2 epsI He k P1) |].
        apply rsum_le. intros p _.
        exact (reach_target_flat Lambda epsI He k (plaq4D_links p) P2).
      - rewrite (rsum_swap (seq 0 (S (length Lambda))) P1
                   (fun k p => rsum P2
                      (fun q => reachTo (plaq4D_links q) k (plaq4D_links p)))).
        apply rsum_le. intros p Hp.
        rewrite (rsum_swap (seq 0 (S (length Lambda))) P2
                   (fun k q => reachTo (plaq4D_links q) k (plaq4D_links p))).
        apply rsum_le. intros q _.
        exact (Z2GaugeClustering.reach_sum_bound beta Lambda Hnd Hwf q mu Hmu Hsmall
                 (S (length Lambda)) p
                 (proj1 (Forall_forall wf_plaq_4D P1) P1_wf p Hp)).
    Qed.

    Theorem instance_multi_clustering :
      Rabs (su2_truncated_on G beta Lambda f g)
      <= 4 * rsum P1 (fun p => rsum P2 (fun q => exp (- mu * (plaq4D_dist p q - 1)))).
    Proof.
      pose proof (dup_clustering Link4D Quat Plaq4D
                    link4D_eqb link4D_eqb_spec
                    Z2GaugeClustering.plaq4D_eqb Z2GaugeClustering.plaq4D_eqb_spec
                    G plaq4D_links phiI Lambda (z2_links Lambda) SU2Clustering.base
                    fcl gcl Seed1 Seed2 mlowI epsI 2 2 Hnd G_nonempty
                    (SU2Clustering.phi_local beta Lambda) (SU2Clustering.phi_pos beta Lambda)
                    (Z2GaugeClustering.mlow_pos beta) (Z2GaugeClustering.epsv_nonneg beta)
                    (SU2Clustering.phi_osc_lo beta Lambda) (SU2Clustering.phi_osc_hi beta Lambda)
                    fcl_local gcl_local fcl_osc gcl_osc) as Hdup.
      unfold su2_truncated_on.
      rewrite (SU2Clustering.expect_bridge G G_unit beta Lambda
                 (fun U => f U * g U) (fun U => fcl U * gcl U)).
      2: { intros U HU. unfold fcl, gcl.
           rewrite (SU2Clustering.clamp_id_abs _ (f_bd U HU)),
                   (SU2Clustering.clamp_id_abs _ (g_bd U HU)).
           reflexivity. }
      rewrite (SU2Clustering.expect_bridge G G_unit beta Lambda f fcl).
      2: { intros U HU. unfold fcl. apply SU2Clustering.clamp_id_abs. apply f_bd. exact HU. }
      rewrite (SU2Clustering.expect_bridge G G_unit beta Lambda g gcl).
      2: { intros U HU. unfold gcl. apply SU2Clustering.clamp_id_abs. apply g_bd. exact HU. }
      eapply Rle_trans; [exact Hdup |].
      pose proof chain_bound as Hch.
      rewrite (rsum_ext P1
                 (fun p => rsum P2 (fun q => 2 * exp (- mu * (plaq4D_dist p q - 1))))
                 (fun p => 2 * rsum P2 (fun q => exp (- mu * (plaq4D_dist p q - 1)))))
        in Hch by (intros p _; apply rsum_scal).
      rewrite rsum_scal in Hch.
      lra.
    Qed.
  End Instance.

  (* finite a-priori distribution, finite volume *)
  Theorem su2_multi_clustering_finite :
    forall (G : list Quat) (beta mu : R) (Lambda P1 P2 : list Plaq4D)
           (f g : SU2Config -> R),
      G <> [] -> Forall su2_unit G ->
      0 <= mu -> 168 * Rabs beta <= exp (- mu) ->
      NoDup Lambda -> Forall wf_plaq_4D Lambda -> Forall wf_plaq_4D P1 ->
      su2_local_on f P1 -> su2_local_on g P2 ->
      (forall U, su2_unit_config U -> Rabs (f U) <= 1) ->
      (forall U, su2_unit_config U -> Rabs (g U) <= 1) ->
      Rabs (su2_truncated_on G beta Lambda f g)
      <= 4 * rsum P1 (fun p => rsum P2 (fun q => exp (- mu * (plaq4D_dist p q - 1)))).
  Proof.
    intros G beta mu Lambda P1 P2 f g HG HGu Hmu Hsmall Hnd Hwf HP1 Hf Hg Hfb Hgb.
    exact (instance_multi_clustering G HG HGu beta Lambda Hnd Hwf f g P1 P2 HP1 Hf Hg
             Hfb Hgb mu Hmu Hsmall).
  Qed.

  (* =======================================================================
     3. The Haar-measure state in finite volume
     ======================================================================= *)

  Theorem su2_haar_multi_clustering :
    forall (beta mu : R) (Lambda P1 P2 : list Plaq4D) (f g : SU2Config -> R),
      0 <= mu -> 168 * Rabs beta <= exp (- mu) ->
      NoDup Lambda -> Forall wf_plaq_4D Lambda -> Forall wf_plaq_4D P1 ->
      su2_local_on f P1 -> su2_local_on g P2 ->
      su2_bounded_continuous f -> su2_bounded_continuous g ->
      (forall U, su2_unit_config U -> Rabs (f U) <= 1) ->
      (forall U, su2_unit_config U -> Rabs (g U) <= 1) ->
      exists vfg vf vg : R,
        su2_haar_expect_is beta Lambda (fun U => f U * g U) vfg /\
        su2_haar_expect_is beta Lambda f vf /\
        su2_haar_expect_is beta Lambda g vg /\
        Rabs (vfg - vf * vg)
        <= 4 * rsum P1 (fun p => rsum P2 (fun q => exp (- mu * (plaq4D_dist p q - 1)))).
  Proof.
    intros beta mu Lambda P1 P2 f g Hmu Hsmall Hnd Hwf HP1 Hf Hg Hfc Hgc Hfb Hgb.
    destruct (SU2HaarLimit.haar_state_exists beta Lambda (fun U => f U * g U)
                (SU2Continuity.bc_mult f g Hfc Hgc)) as [vfg Hfg].
    destruct (SU2HaarLimit.haar_state_exists beta Lambda f Hfc) as [vf Hvf].
    destruct (SU2HaarLimit.haar_state_exists beta Lambda g Hgc) as [vg Hvg].
    exists vfg, vf, vg.
    split; [exact Hfg |]. split; [exact Hvf |]. split; [exact Hvg |].
    apply (SU2HaarLimit.cv_bound
             (fun n => su2_truncated_on (su2_grid n) beta Lambda f g)
             (vfg - vf * vg) _ 0%nat).
    - unfold su2_truncated_on.
      apply (CV_minus
               (fun n => su2_expect_on (su2_grid n) beta Lambda (fun U => f U * g U))
               (fun n => su2_expect_on (su2_grid n) beta Lambda f
                         * su2_expect_on (su2_grid n) beta Lambda g)
               vfg (vf * vg) Hfg).
      exact (CV_mult _ _ vf vg Hvf Hvg).
    - intros n _.
      exact (su2_multi_clustering_finite (su2_grid n) beta mu Lambda P1 P2 f g
               (SU2HaarGrid.grid_nonempty n) (SU2HaarGrid.grid_unit n)
               Hmu Hsmall Hnd Hwf HP1 Hf Hg Hfb Hgb).
  Qed.

  (* =======================================================================
     4. TARGET 10d: infinite volume
     ======================================================================= *)

  Lemma local_mult : forall (f g : SU2Config -> R) (P1 P2 : list Plaq4D),
    su2_local_on f P1 -> su2_local_on g P2 ->
    su2_local_on (fun U => f U * g U) (P1 ++ P2).
  Proof.
    intros f g P1 P2 Hf Hg U U' H. rewrite (Hf U U'), (Hg U U'); [reflexivity | |].
    - intros p l Hp Hl. apply (H p l); [apply in_or_app; right; exact Hp | exact Hl].
    - intros p l Hp Hl. apply (H p l); [apply in_or_app; left; exact Hp | exact Hl].
  Qed.

  Theorem su2_multi_plaquette_clustering : Challenge_SU2Gauge4D_MultiPlaquetteClustering.
  Proof.
    intros beta mu P1 P2 f g Hmu Hsmall Hbeta HP1 HP2 Hf Hg Hfc Hgc Hfb Hgb.
    destruct (SU2InfiniteVolume.su2_thermodynamic_limit beta (P1 ++ P2)
                (fun U => f U * g U) Hbeta
                (proj2 (Forall_app wf_plaq_4D P1 P2) (conj HP1 HP2))
                (local_mult f g P1 P2 Hf Hg) (SU2Continuity.bc_mult f g Hfc Hgc))
      as [vfg [nfg [Hnfg Hcfg]]].
    destruct (SU2InfiniteVolume.su2_thermodynamic_limit beta P1 f Hbeta HP1 Hf Hfc)
      as [vf [nf [Hnf Hcf]]].
    destruct (SU2InfiniteVolume.su2_thermodynamic_limit beta P2 g Hbeta HP2 Hg Hgc)
      as [vg [ng [Hng Hcg]]].
    exists vfg, vf, vg.
    split; [exists nfg; split; assumption |].
    split; [exists nf; split; assumption |].
    split; [exists ng; split; assumption |].
    apply (SU2HaarLimit.cv_bound (fun n => nfg n - nf n * ng n) (vfg - vf * vg) _ 0%nat).
    - exact (CV_minus nfg (fun n => nf n * ng n) vfg (vf * vg) Hcfg
               (CV_mult nf ng vf vg Hcf Hcg)).
    - intros n _.
      destruct (su2_haar_multi_clustering beta mu (su2_box n) P1 P2 f g
                  Hmu Hsmall (LatticeBoxes.box_nodup n) (LatticeBoxes.box_wf n)
                  HP1 Hf Hg Hfc Hgc Hfb Hgb)
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

End SU2MultiClustering.
