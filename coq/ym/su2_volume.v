(* =========================================================================
   ym/su2_volume.v

   Exponentially small dependence on the volume of the 4D SU(2) Wilson
   lattice gauge theory at strong coupling (TARGET 9a), proved directly for
   the frozen objects of `verification/ChallengeSU2InfiniteVolume.v`:

     |<f>_{Q ++ Lambda} - <f>_Lambda|
       <= 2 exp(2|beta|) * sum_{q in Q} sum_{p in P} exp(- mu (dist(p,q) - 1))

   for an observable f, |f| <= 1, localized on the plaquettes P of Lambda,
   whenever 168 |beta| <= exp(- mu), uniformly in the finite a-priori link
   distribution.

   Steps, for one added plaquette q (then telescope over Q):
     1. The weight of q :: Lambda is the weight of Lambda times
        e^{|beta|} g_q with g_q = exp(beta P_q - |beta|) in (0, 1], so
          <f>_{q :: Lambda} = <f g_q>' / <g_q>',
        where <.>' is the expectation for the weight of Lambda in which the
        links of q are summed as well.
     2. Summing over additional links on which neither the observable nor
        the weight depends does not change an expectation
        (rg/product_measure_perm.v), so <f>' = <f>_Lambda.
     3. Hence <f>_{q :: Lambda} - <f>_Lambda = (<f g_q>' - <f>'<g_q>') / <g_q>'.
        The truncated correlation is bounded by the abstract duplicate-system
        theorem `dup_clustering` (the seed being the links of all plaquettes
        of P; the chain sums are subadditive in the seed and are bounded
        plaquette by plaquette as in Target 7b), and <g_q>' >= exp(-2|beta|).

   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.Verify.
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import rg.product_measure_perm.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.z2_polymer_gas.
Require Import ym.su2_algebra.
Require Import ym.su2_clustering.
Require Import ym.su2_area_law.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import ChallengeSU2InfiniteVolume.
Import DupClustering Z2GaugeExpansion Z2PolymerGas SU2Algebra.
Open Scope R_scope.

Module SU2Volume.

  (* =======================================================================
     1. Links of a volume
     ======================================================================= *)

  Lemma links_in : forall (Lam : list Plaq4D) p l,
    In p Lam -> In l (plaq4D_links p) -> In l (z2_links Lam).
  Proof.
    intros Lam p l Hp Hl. unfold z2_links. apply (proj2 (dedup_In l _)).
    apply in_flat_map. exists p. split; assumption.
  Qed.

  Lemma links_incl_cons : forall q (Lam : list Plaq4D),
    incl (z2_links Lam) (z2_links (q :: Lam)).
  Proof.
    intros q Lam l Hl. unfold z2_links in *.
    apply (proj1 (dedup_In l _)) in Hl. apply (proj2 (dedup_In l _)).
    cbn [flat_map]. apply in_or_app. right. exact Hl.
  Qed.

  Lemma action_local : forall beta (Lam : list Plaq4D) (U U' : SU2Config),
    (forall l, In l (z2_links Lam) -> U l = U' l) ->
    su2_wilson_action beta Lam U = su2_wilson_action beta Lam U'.
  Proof.
    intros beta Lam U U' H. unfold su2_wilson_action.
    rewrite (map_ext_in (su2_plaq U) (su2_plaq U') Lam); [reflexivity |].
    intros p Hp. apply plaq_local. intros l Hl. apply H. exact (links_in Lam p l Hp Hl).
  Qed.

  (* =======================================================================
     2. The chain sums are subadditive in the seed
     ======================================================================= *)

  Section Reach.
    Variable Lambda : list Plaq4D.
    Variable Sg : list Link4D.
    Variable eps : R.
    Hypothesis eps_nonneg : 0 <= eps.

    Local Notation reachI := (reach Link4D Plaq4D link4D_eqb plaq4D_links Lambda Sg eps).
    Local Notation touchI := (touchb Link4D link4D_eqb).

    Lemma touchb_app : forall S1 S2 T : list Link4D,
      touchI (S1 ++ S2) T = touchI S1 T || touchI S2 T.
    Proof. intros S1 S2 T. unfold touchb. apply existsb_app. Qed.

    Lemma reach_nonneg : forall k S, 0 <= reachI k S.
    Proof.
      induction k as [| k IH]; intro S; cbn [reach].
      - destruct (touchI S Sg); lra.
      - apply rsum_nonneg. intros b _.
        destruct (touchI S (plaq4D_links b)); [| apply Rle_refl].
        apply Rmult_le_pos; [exact eps_nonneg | apply IH].
    Qed.

    Lemma reach_app : forall k S1 S2, reachI k (S1 ++ S2) <= reachI k S1 + reachI k S2.
    Proof.
      intros k S1 S2. destruct k as [| k]; cbn [reach].
      - rewrite touchb_app. destruct (touchI S1 Sg), (touchI S2 Sg); cbn [orb]; lra.
      - rewrite <- rsum_plus. apply rsum_le. intros b _. rewrite touchb_app.
        pose proof (reach_nonneg k (plaq4D_links b)) as Hr.
        assert (Hp : 0 <= eps * reachI k (plaq4D_links b))
          by (apply Rmult_le_pos; assumption).
        destruct (touchI S1 (plaq4D_links b)), (touchI S2 (plaq4D_links b)); cbn [orb]; lra.
    Qed.

    Lemma reach_nil : forall k, reachI k [] = 0.
    Proof.
      intro k. destruct k as [| k]; cbn [reach]; unfold touchb; cbn [existsb].
      - reflexivity.
      - apply rsum_zero. intros b _. reflexivity.
    Qed.

    Lemma reach_flat : forall k (P : list Plaq4D),
      reachI k (flat_map plaq4D_links P) <= rsum P (fun p => reachI k (plaq4D_links p)).
    Proof.
      intros k P. induction P as [| p P IH].
      - cbn [flat_map]. rewrite reach_nil, rsum_nil. apply Rle_refl.
      - cbn [flat_map]. rewrite rsum_cons.
        eapply Rle_trans; [apply reach_app |]. lra.
    Qed.
  End Reach.

  (* =======================================================================
     3. Adding one plaquette to the volume
     ======================================================================= *)

  Section Step.
    Variable G : list Quat.
    Hypothesis G_nonempty : G <> [].
    Hypothesis G_unit : Forall su2_unit G.
    Variables beta mu : R.
    Hypothesis Hmu : 0 <= mu.
    Hypothesis Hsmall : 168 * Rabs beta <= exp (- mu).

    Local Notation Cs := (csum Link4D Quat link4D_eqb G).
    Local Notation mlowI := (Z2GaugeClustering.mlow beta).
    Local Notation epsI := (Z2GaugeClustering.epsv beta).
    Local Notation phiI := (SU2Clustering.phi beta).
    Local Notation LocalOn := (ProductMeasure.local_on Link4D Quat).

    Definition base : SU2Config := fun _ => qone.

    Definition wgt (Lam : list Plaq4D) (U : SU2Config) : R :=
      exp (- su2_wilson_action beta Lam U).

    (* expectation for the weight of Lam, summing over an arbitrary link list E0 *)
    Definition expE (E0 : list Link4D) (Lam : list Plaq4D) (F : SU2Config -> R) : R :=
      Cs E0 (fun U => F U * wgt Lam U) base / Cs E0 (wgt Lam) base.

    (* normalized Boltzmann factor of one plaquette, with values in (0, 1] *)
    Definition gq (q : Plaq4D) (U : SU2Config) : R :=
      exp (beta * su2_plaq U q - Rabs beta).

    Lemma G_good : forall v, In v G -> su2_unit v.
    Proof. exact (proj1 (Forall_forall su2_unit G) G_unit). Qed.

    Lemma base_unit : su2_unit_config base.
    Proof. exact unit_config_one. Qed.

    Lemma NG_pos : 0 < INR (length G).
    Proof.
      apply lt_0_INR.
      assert (H : length G <> 0%nat).
      { intro H0. apply G_nonempty. apply length_zero_iff_nil. exact H0. }
      lia.
    Qed.

    Lemma wgt_pos : forall Lam U, 0 < wgt Lam U.
    Proof. intros Lam U. unfold wgt. apply exp_pos. Qed.

    Lemma Zpos : forall E0 Lam, 0 < Cs E0 (wgt Lam) base.
    Proof.
      intros E0 Lam. apply csum_pos; [exact G_nonempty |]. intro A. apply wgt_pos.
    Qed.

    Lemma cs_unit_ext : forall E0 (F F' : SU2Config -> R),
      (forall U, su2_unit_config U -> F U = F' U) -> Cs E0 F base = Cs E0 F' base.
    Proof.
      intros E0 F F' H.
      exact (ProductMeasure.csum_ext_good Link4D Quat link4D_eqb G su2_unit G_good
               E0 F F' H base base_unit).
    Qed.

    Lemma cs_unit_le : forall E0 (F F' : SU2Config -> R),
      (forall U, su2_unit_config U -> F U <= F' U) -> Cs E0 F base <= Cs E0 F' base.
    Proof.
      intros E0 F F' H.
      exact (ProductMeasure.csum_le_good Link4D Quat link4D_eqb G su2_unit G_good
               E0 F F' H base base_unit).
    Qed.

    Lemma expE_links : forall Lam (F : SU2Config -> R),
      expE (z2_links Lam) Lam F = su2_expect_on G beta Lam F.
    Proof. intros Lam F. symmetry. exact (expect_csum G beta Lam F). Qed.

    (* ---------- Step 2: additional links do not matter ---------- *)

    Lemma wgt_local : forall Lam, LocalOn (z2_links Lam) (wgt Lam).
    Proof.
      intros Lam A A' H. unfold wgt. rewrite (action_local beta Lam A A' H). reflexivity.
    Qed.

    Lemma expE_extra : forall E0 Lam (F : SU2Config -> R),
      NoDup E0 -> incl (z2_links Lam) E0 -> LocalOn (z2_links Lam) F ->
      expE E0 Lam F = expE (z2_links Lam) Lam F.
    Proof.
      intros E0 Lam F HE Hincl HF. unfold expE.
      assert (HFw : LocalOn (z2_links Lam) (fun U => F U * wgt Lam U)).
      { intros A A' H. rewrite (HF A A' H), (wgt_local Lam A A' H). reflexivity. }
      rewrite (ProductMeasurePerm.csum_extra Link4D Quat link4D_eqb link4D_eqb_spec G
                 (z2_links Lam) (fun U => F U * wgt Lam U) HFw (z2_links Lam) E0
                 (SU2AreaLaw.dedup_NoDup _) HE Hincl (fun e _ Hn => Hn) base).
      rewrite (ProductMeasurePerm.csum_extra Link4D Quat link4D_eqb link4D_eqb_spec G
                 (z2_links Lam) (wgt Lam) (wgt_local Lam) (z2_links Lam) E0
                 (SU2AreaLaw.dedup_NoDup _) HE Hincl (fun e _ Hn => Hn) base).
      pose proof (Zpos (z2_links Lam) Lam) as HZ.
      assert (HN : 0 < INR (length G) ^ (length E0 - length (z2_links Lam)))
        by (apply pow_lt; exact NG_pos).
      field. split; lra.
    Qed.

    (* ---------- Step 1: the weight of one more plaquette ---------- *)

    Lemma wgt_cons : forall q Lam U,
      wgt (q :: Lam) U = exp (Rabs beta) * (gq q U * wgt Lam U).
    Proof.
      intros q Lam U. unfold wgt, gq, su2_wilson_action. cbn [map fold_right].
      rewrite <- !exp_plus. f_equal. ring.
    Qed.

    Lemma expect_cons : forall q Lam (F : SU2Config -> R),
      su2_expect_on G beta (q :: Lam) F =
      expE (z2_links (q :: Lam)) Lam (fun U => F U * gq q U)
      / expE (z2_links (q :: Lam)) Lam (gq q).
    Proof.
      intros q Lam F. rewrite expect_csum. unfold expE.
      set (E' := z2_links (q :: Lam)).
      rewrite (csum_ext Link4D Quat link4D_eqb G E'
                 (fun U => F U * exp (- su2_wilson_action beta (q :: Lam) U))
                 (fun U => exp (Rabs beta) * ((F U * gq q U) * wgt Lam U))).
      2: { intro U.
           change (exp (- su2_wilson_action beta (q :: Lam) U)) with (wgt (q :: Lam) U).
           rewrite wgt_cons. ring. }
      rewrite (csum_ext Link4D Quat link4D_eqb G E'
                 (fun U => exp (- su2_wilson_action beta (q :: Lam) U))
                 (fun U => exp (Rabs beta) * (gq q U * wgt Lam U))).
      2: { intro U.
           change (exp (- su2_wilson_action beta (q :: Lam) U)) with (wgt (q :: Lam) U).
           apply wgt_cons. }
      rewrite !csum_scal.
      pose proof (exp_pos (Rabs beta)) as Hb.
      pose proof (Zpos E' Lam) as HZ.
      assert (HG : 0 < Cs E' (fun U => gq q U * wgt Lam U) base).
      { apply csum_pos; [exact G_nonempty |]. intro A.
        apply Rmult_lt_0_compat; [unfold gq; apply exp_pos | apply wgt_pos]. }
      change (fun _ : Link4D => qone) with base.
      field. repeat split; lra.
    Qed.

    Lemma gq_lower : forall q U, su2_unit_config U -> exp (- (2 * Rabs beta)) <= gq q U.
    Proof.
      intros q U HU. unfold gq. apply Z2GaugeClustering.exp_le.
      pose proof (SU2Clustering.times_bound beta _ (plaq_bound U q HU)). lra.
    Qed.

    Lemma expE_gq_lower : forall E0 Lam q, exp (- (2 * Rabs beta)) <= expE E0 Lam (gq q).
    Proof.
      intros E0 Lam q. unfold expE. pose proof (Zpos E0 Lam) as HZ.
      apply Rmult_le_reg_r with (Cs E0 (wgt Lam) base); [exact HZ |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
      rewrite <- (csum_scal Link4D Quat link4D_eqb G E0 (exp (- (2 * Rabs beta)))
                    (wgt Lam) base).
      apply cs_unit_le. intros U HU.
      apply Rmult_le_compat_r; [left; apply wgt_pos | apply gq_lower; exact HU].
    Qed.

    (* ---------- Step 3: the truncated correlation with the new plaquette ---------- *)

    Section Cov.
      Variable E0 : list Link4D.
      Variable Lam : list Plaq4D.
      Hypothesis Hnd : NoDup Lam.
      Hypothesis Hwf : Forall wf_plaq_4D Lam.
      Variable P : list Plaq4D.
      Hypothesis HP : incl P Lam.
      Variable f : SU2Config -> R.
      Hypothesis f_loc : su2_local_on f P.
      Hypothesis f_bd : forall U, su2_unit_config U -> Rabs (f U) <= 1.
      Variable q : Plaq4D.

      Definition fc (U : SU2Config) : R := SU2Clustering.clamp (f U).
      Definition gc (U : SU2Config) : R :=
        exp (beta * SU2Clustering.clamp (su2_plaq U q) - Rabs beta).

      Local Notation SeedP := (flat_map plaq4D_links P).
      Local Notation NfI := (Nf Link4D Quat Plaq4D link4D_eqb G phiI Lam E0 base).
      Local Notation ZfI := (Zf Link4D Quat Plaq4D link4D_eqb G phiI Lam E0 base).
      Local Notation reachQ :=
        (reach Link4D Plaq4D link4D_eqb plaq4D_links Lam (plaq4D_links q) epsI).

      Lemma fc_local : forall A A' : Link4D -> Quat,
        (forall e, In e SeedP -> A e = A' e) -> fc A = fc A'.
      Proof.
        intros A A' H. unfold fc. rewrite (f_loc A A'); [reflexivity |].
        intros p l Hp Hl. apply H. apply in_flat_map. exists p. split; assumption.
      Qed.

      Lemma gc_local : forall A A' : Link4D -> Quat,
        (forall e, In e (plaq4D_links q) -> A e = A' e) -> gc A = gc A'.
      Proof. intros A A' H. unfold gc. rewrite (plaq_local A A' q H). reflexivity. Qed.

      Lemma gc_range : forall A : SU2Config, exp (- (2 * Rabs beta)) <= gc A <= 1.
      Proof.
        intro A. unfold gc.
        pose proof (SU2Clustering.times_bound beta _
                      (SU2Clustering.clamp_bound (su2_plaq A q))) as [H1 H2].
        split.
        - apply Z2GaugeClustering.exp_le. lra.
        - apply Rle_trans with (exp 0); [apply Z2GaugeClustering.exp_le; lra |].
          rewrite exp_0. apply Rle_refl.
      Qed.

      Lemma fc_osc : forall A A' : Link4D -> Quat, Rabs (fc A - fc A') <= 2.
      Proof. intros A A'. apply SU2Clustering.clamp_diff. Qed.

      Lemma gc_osc : forall A A' : Link4D -> Quat, Rabs (gc A - gc A') <= 1.
      Proof.
        intros A A'. pose proof (gc_range A) as [H1 H2]. pose proof (gc_range A') as [H3 H4].
        pose proof (exp_pos (- (2 * Rabs beta))) as Hp.
        apply Rabs_le. lra.
      Qed.

      Lemma bridge : forall F Fc : SU2Config -> R,
        (forall U, su2_unit_config U -> Fc U = F U) -> NfI Fc / ZfI = expE E0 Lam F.
      Proof.
        intros F Fc HF.
        assert (HN : NfI Fc = Cs E0 (fun U => F U * wgt Lam U) base).
        { unfold Nf. apply cs_unit_ext. intros U HU.
          rewrite (HF U HU), (SU2Clustering.weight_W beta Lam U HU). reflexivity. }
        assert (HZ : ZfI = Cs E0 (wgt Lam) base).
        { unfold Zf. apply cs_unit_ext. intros U HU.
          exact (SU2Clustering.weight_W beta Lam U HU). }
        unfold expE. rewrite HN, HZ. reflexivity.
      Qed.

      Lemma cov_bound :
        Rabs (expE E0 Lam (fun U => f U * gq q U) - expE E0 Lam f * expE E0 Lam (gq q))
        <= rsum P (fun p => 2 * exp (- mu * (plaq4D_dist p q - 1))).
      Proof.
        pose proof (dup_clustering Link4D Quat Plaq4D
                      link4D_eqb link4D_eqb_spec
                      Z2GaugeClustering.plaq4D_eqb Z2GaugeClustering.plaq4D_eqb_spec
                      G plaq4D_links phiI Lam E0 base fc gc SeedP (plaq4D_links q)
                      mlowI epsI 2 1 Hnd G_nonempty
                      (SU2Clustering.phi_local beta Lam) (SU2Clustering.phi_pos beta Lam)
                      (Z2GaugeClustering.mlow_pos beta) (Z2GaugeClustering.epsv_nonneg beta)
                      (SU2Clustering.phi_osc_lo beta Lam) (SU2Clustering.phi_osc_hi beta Lam)
                      fc_local gc_local fc_osc gc_osc) as Hdup.
        assert (B1 : NfI (fun U : SU2Config => fc U * gc U) / ZfI
                     = expE E0 Lam (fun U => f U * gq q U)).
        { apply bridge. intros U HU. unfold fc, gc, gq.
          rewrite (SU2Clustering.clamp_id_abs _ (f_bd U HU)),
                  (SU2Clustering.clamp_id _ (plaq_bound U q HU)).
          reflexivity. }
        assert (B2 : NfI fc / ZfI = expE E0 Lam f).
        { apply bridge. intros U HU. unfold fc. apply SU2Clustering.clamp_id_abs.
          apply f_bd. exact HU. }
        assert (B3 : NfI gc / ZfI = expE E0 Lam (gq q)).
        { apply bridge. intros U HU. unfold gc, gq.
          rewrite (SU2Clustering.clamp_id _ (plaq_bound U q HU)). reflexivity. }
        assert (Hdup' :
          Rabs (NfI (fun U : SU2Config => fc U * gc U) / ZfI
                - NfI fc / ZfI * (NfI gc / ZfI))
          <= 2 * 1 / 2 * rsum (seq 0 (S (length Lam))) (fun k => reachQ k SeedP))
          by exact Hdup.
        rewrite B1, B2, B3 in Hdup'.
        eapply Rle_trans; [exact Hdup' |].
        assert (Hchain :
          rsum (seq 0 (S (length Lam))) (fun k => reachQ k SeedP)
          <= rsum P (fun p => 2 * exp (- mu * (plaq4D_dist p q - 1)))).
        { apply Rle_trans with
            (rsum (seq 0 (S (length Lam)))
               (fun k => rsum P (fun p => reachQ k (plaq4D_links p)))).
          - apply rsum_le. intros k _.
            exact (reach_flat Lam (plaq4D_links q) epsI
                     (Z2GaugeClustering.epsv_nonneg beta) k P).
          - rewrite (rsum_swap (seq 0 (S (length Lam))) P
                       (fun k p => reachQ k (plaq4D_links p))).
            apply rsum_le. intros p Hp.
            exact (Z2GaugeClustering.reach_sum_bound beta Lam Hnd Hwf q mu Hmu Hsmall
                     (S (length Lam)) p
                     (proj1 (Forall_forall wf_plaq_4D Lam) Hwf p (HP p Hp))). }
        lra.
      Qed.
    End Cov.

    (* ---------- one added plaquette ---------- *)

    Theorem one_step : forall (Lam P : list Plaq4D) (q : Plaq4D) (f : SU2Config -> R),
      NoDup (q :: Lam) -> Forall wf_plaq_4D (q :: Lam) -> incl P Lam ->
      su2_local_on f P -> (forall U, su2_unit_config U -> Rabs (f U) <= 1) ->
      Rabs (su2_expect_on G beta (q :: Lam) f - su2_expect_on G beta Lam f)
      <= 2 * exp (2 * Rabs beta) * rsum P (fun p => exp (- mu * (plaq4D_dist p q - 1))).
    Proof.
      intros Lam P q f Hnd Hwf HP Hloc Hfb.
      assert (HndL : NoDup Lam) by (inversion Hnd; assumption).
      assert (HwfL : Forall wf_plaq_4D Lam) by (inversion Hwf; assumption).
      assert (HE' : NoDup (z2_links (q :: Lam))) by (apply SU2AreaLaw.dedup_NoDup).
      assert (Hf_links : LocalOn (z2_links Lam) f).
      { intros A A' H. apply Hloc. intros p l Hp Hl. apply H.
        exact (links_in Lam p l (HP p Hp) Hl). }
      rewrite expect_cons, <- (expE_links Lam f).
      rewrite <- (expE_extra (z2_links (q :: Lam)) Lam f HE' (links_incl_cons q Lam) Hf_links).
      pose proof (cov_bound (z2_links (q :: Lam)) Lam HndL HwfL P HP f Hloc Hfb q) as Hcov.
      pose proof (expE_gq_lower (z2_links (q :: Lam)) Lam q) as Hlow.
      set (afg := expE (z2_links (q :: Lam)) Lam (fun U => f U * gq q U)) in *.
      set (ag := expE (z2_links (q :: Lam)) Lam (gq q)) in *.
      set (af := expE (z2_links (q :: Lam)) Lam f) in *.
      pose proof (exp_pos (- (2 * Rabs beta))) as Hpos.
      pose proof (exp_pos (2 * Rabs beta)) as He.
      assert (Hag : 0 < ag) by lra.
      assert (Hone : exp (- (2 * Rabs beta)) * exp (2 * Rabs beta) = 1).
      { rewrite <- exp_plus. replace (- (2 * Rabs beta) + 2 * Rabs beta) with 0 by ring.
        apply exp_0. }
      assert (Hinv : / ag <= exp (2 * Rabs beta)).
      { apply Rmult_le_reg_l with ag; [exact Hag |]. rewrite Rinv_r by lra. nra. }
      rewrite (rsum_scal P 2 (fun p => exp (- mu * (plaq4D_dist p q - 1)))) in Hcov.
      assert (Hs0 : 0 <= rsum P (fun p => exp (- mu * (plaq4D_dist p q - 1)))).
      { apply rsum_nonneg. intros p _. left. apply exp_pos. }
      set (Sm := rsum P (fun p => exp (- mu * (plaq4D_dist p q - 1)))) in *.
      replace (afg / ag - af) with ((afg - af * ag) * / ag) by (field; lra).
      rewrite Rabs_mult, (Rabs_pos_eq (/ ag)) by (left; apply Rinv_0_lt_compat; exact Hag).
      pose proof (Rabs_pos (afg - af * ag)) as Hc0.
      assert (Hi0 : 0 <= / ag) by (left; apply Rinv_0_lt_compat; exact Hag).
      apply Rle_trans with ((2 * Sm) * exp (2 * Rabs beta)).
      - apply Rmult_le_compat; assumption.
      - apply Req_le. ring.
    Qed.

    (* ---------- telescoping over the added plaquettes ---------- *)

    Theorem volume_dependence : forall (Lambda Q P : list Plaq4D) (f : SU2Config -> R),
      NoDup (Q ++ Lambda) -> Forall wf_plaq_4D (Q ++ Lambda) -> incl P Lambda ->
      su2_local_on f P -> (forall U, su2_unit_config U -> Rabs (f U) <= 1) ->
      Rabs (su2_expect_on G beta (Q ++ Lambda) f - su2_expect_on G beta Lambda f)
      <= 2 * exp (2 * Rabs beta) *
         rsum Q (fun q => rsum P (fun p => exp (- mu * (plaq4D_dist p q - 1)))).
    Proof.
      intros Lambda Q P f Hnd Hwf HP Hloc Hfb. induction Q as [| q Q IH].
      - cbn [app]. rewrite rsum_nil.
        replace (su2_expect_on G beta Lambda f - su2_expect_on G beta Lambda f) with 0
          by ring.
        rewrite Rabs_R0. lra.
      - cbn [app] in *.
        assert (HndQ : NoDup (Q ++ Lambda)) by (inversion Hnd; assumption).
        assert (HwfQ : Forall wf_plaq_4D (Q ++ Lambda)) by (inversion Hwf; assumption).
        specialize (IH HndQ HwfQ).
        assert (HPQ : incl P (Q ++ Lambda)).
        { intros p Hp. apply in_or_app. right. exact (HP p Hp). }
        pose proof (one_step (Q ++ Lambda) P q f Hnd Hwf HPQ Hloc Hfb) as H1.
        rewrite rsum_cons.
        pose proof (exp_pos (2 * Rabs beta)) as He.
        set (X := su2_expect_on G beta (q :: Q ++ Lambda) f) in *.
        set (Y := su2_expect_on G beta (Q ++ Lambda) f) in *.
        set (Z := su2_expect_on G beta Lambda f) in *.
        replace (X - Z) with ((X - Y) + (Y - Z)) by ring.
        eapply Rle_trans; [apply Rabs_triang |]. nra.
    Qed.

  End Step.

  (* TARGET 9a *)
  Theorem su2_volume_dependence : Challenge_SU2Gauge4D_VolumeDependence.
  Proof.
    intros G beta mu Lambda Q P f HG HGu Hmu Hsmall Hnd Hwf HP Hloc Hfb.
    exact (volume_dependence G HG HGu beta mu Hmu Hsmall Lambda Q P f Hnd Hwf HP Hloc Hfb).
  Qed.

End SU2Volume.
