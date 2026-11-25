(* =========================================================================
   ym/su2_transfer_positivity.v

   Positivity of the transfer operator of the 4D SU(2) Wilson lattice gauge
   theory for beta >= 0 (TARGETS 12a, 12b), and its symmetry and
   contractivity (TARGETS 12c, 12d, corollaries of Target 10):

       (f, T f) = <(Theta f) (tau f)> >= 0

   for observables f at non-negative times, i.e. reflection positivity with
   respect to the hyperplane t = 1/2 that cuts the time-like links between
   t = 0 and t = 1 (ym/lattice_link_reflection.v).

   Proof, in a finite volume Sc ++ Sp ++ mirror (Sp) symmetric under the
   link reflection (Sc: the crossing plaquettes, Sp: plaquettes at times
   >= 1), for the Hopf grid of level n as a-priori distribution.  With
   chi = tau f, X = chi * exp (- S_Sp), u = the cut link variables, A the
   variables at times >= 1 and A' the mirror image of the others, the
   integrand is
       T (U) = X (A) X (A') exp (beta * sum_p < u A u^{-1} , A' >_p),
   the sum running over the crossing plaquettes.

   1. For every SU(2)-valued w on the cut links, T (U) = Phi_w (w . U),
      where w . U multiplies the cut variables by w on the left and
         Phi_w (U) = X (A) X (A') exp (beta * sum_p < u A u^{-1} , w A' w^{-1} >_p).
   2. The grid sums are asymptotically invariant under u -> w u, uniformly
      in w (ym/su2_link_translate.v, a consequence of the invariance of the
      Haar measure, Target 11a): avg T >= avg Phi_w - eta for large grids.
   3. Averaging over w, the mirror variables A' together with w form an
      independent second copy of (u, A) (rg/product_measure_two_copy.v):
         sum_w sum_U Phi_w (U) = sum_{(u,A)} sum_{(w,A')} X X' exp (beta * S),
      with S a finite sum of products k (u, A) k (w, A'): the exponential of
      a positive kernel is positive (rg/positive_kernel.v), so this is >= 0.
   Hence avg T >= - eta for every eta > 0 and large grids; the limit of the
   expectations is >= 0, and passes to infinite volume by the uniqueness of
   the thermodynamic limit (Target 10a) along symmetric volumes.

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
Require Import verification.ChallengeSU2TransferPositivity.
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import rg.product_measure_perm.
Require Import rg.product_measure_relabel.
Require Import rg.product_measure_two_copy.
Require Import rg.positive_kernel.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_polymer_gas.
Require Import ym.su2_algebra.
Require Import ym.su2_area_law.
Require Import ym.su2_continuity.
Require Import ym.su2_haar_grid.
Require Import ym.su2_haar_limit.
Require Import ym.su2_volume.
Require Import ym.lattice_boxes.
Require Import ym.lattice_symmetry.
Require Import ym.su2_covariance.
Require Import ym.su2_uniqueness.
Require Import ym.su2_haar_grid_conj.
Require Import ym.su2_mass_gap.
Require Import ym.su2_haar_mean.
Require Import ym.su2_gauge_invariance.
Require Import ym.su2_link_translate.
Require Import ym.lattice_link_reflection.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeSU2Gauge ChallengeSU2InfiniteVolume.
Import ChallengeSU2MassGap ChallengeSU2TransferPositivity.
Import DupClustering Z2GaugeExpansion Z2PolymerGas SU2Algebra SU2HaarGrid.
Import LatticeSymmetry SU2HaarMean SU2GaugeInvariance LatticeLinkReflection.
Open Scope R_scope.

Module SU2TransferPositivity.

  Local Notation U0 := (fun _ : Link4D => qone).
  Local Notation Cs := (csum Link4D Quat link4D_eqb).

  (* =======================================================================
     1. Preliminaries
     ======================================================================= *)

  Lemma action_app2 : forall beta (L1 L2 : list Plaq4D) (U : SU2Config),
    su2_wilson_action beta (L1 ++ L2) U =
    su2_wilson_action beta L1 U + su2_wilson_action beta L2 U.
  Proof.
    intros beta L1 L2 U. unfold su2_wilson_action.
    change (fold_right Rplus 0 (map (su2_plaq U) (L1 ++ L2)))
      with (rsum (L1 ++ L2) (su2_plaq U)).
    rewrite rsum_app. unfold rsum. ring.
  Qed.

  Lemma isPp_notC : forall l, isPp l = true -> isC l = false.
  Proof.
    intros l H. destruct (isC l) eqn:E; [| reflexivity].
    rewrite (isC_not_Pp l E) in H. discriminate.
  Qed.

  Lemma isMm_notC : forall l, isMm l = true -> isC l = false.
  Proof.
    intros l H. destruct (isC l) eqn:E; [| reflexivity].
    rewrite (isC_not_Mm l E) in H. discriminate.
  Qed.

  (* multiplication of the cut link variables by w, resp. by w^{-1}, on the left *)
  Definition aw (w : SU2Config) (l : Link4D) : Quat := if isC l then w l else qone.
  Definition abar (w : SU2Config) (l : Link4D) : Quat :=
    if isC l then qconj (w l) else qone.

  Definition Lw (w U : SU2Config) : SU2Config :=
    SU2LinkTranslate.ltr (aw w) (fun _ => qone) U.
  Definition Lbar (w U : SU2Config) : SU2Config :=
    SU2LinkTranslate.ltr (abar w) (fun _ => qone) U.

  Lemma aw_unit : forall w, su2_unit_config w -> forall l, su2_unit (aw w l).
  Proof. intros w Hw l. unfold aw. destruct (isC l); [apply Hw | apply unit_one]. Qed.

  Lemma abar_unit : forall w, su2_unit_config w -> forall l, su2_unit (abar w l).
  Proof.
    intros w Hw l. unfold abar.
    destruct (isC l); [apply unit_conj; apply Hw | apply unit_one].
  Qed.

  Lemma Lbar_C : forall w U l, isC l = true -> Lbar w U l = qmul (qconj (w l)) (U l).
  Proof.
    intros w U l H. unfold Lbar, SU2LinkTranslate.ltr, abar. rewrite H. apply gt_one_r.
  Qed.

  Lemma Lbar_notC : forall w U l, isC l = false -> Lbar w U l = U l.
  Proof.
    intros w U l H. unfold Lbar, SU2LinkTranslate.ltr, abar.
    rewrite H, gt_one_r. apply qmul_one_l.
  Qed.

  Lemma Lbar_Lw : forall w U, su2_unit_config w -> Lbar w (Lw w U) = U.
  Proof.
    intros w U Hw. apply functional_extensionality. intro l.
    unfold Lbar, Lw, SU2LinkTranslate.ltr, abar, aw.
    destruct (isC l); rewrite !gt_one_r.
    - rewrite qmul_assoc, (unit_conj_l (w l) (Hw l)). apply qmul_one_l.
    - rewrite !qmul_one_l. reflexivity.
  Qed.

  (* =======================================================================
     2. Positivity in a finite volume symmetric under the link reflection
     ======================================================================= *)

  Section FiniteRP.
    Variable beta : R.
    Hypothesis beta_pos : 0 <= beta.
    Variables Sc Sp Q : list Plaq4D.
    Hypothesis Sc_wf : Forall wf_plaq_4D Sc.
    Hypothesis Sc_C : Forall plaqC Sc.
    Hypothesis Sp_wf : Forall wf_plaq_4D Sp.
    Hypothesis Sp_P : Forall plaqPp Sp.
    Hypothesis Q_in : incl Q Sp.
    Variable f : SU2Config -> R.
    Hypothesis f_bc : su2_bounded_continuous f.
    Hypothesis chi_loc : su2_local_on (obs_translate D4_t f) Q.

    Local Notation chi := (obs_translate D4_t f).
    Local Notation Vol := (Sc ++ Sp ++ map plaqL Sp).
    Local Notation LinksV := (z2_links Vol).
    Local Notation pullP := (ProductMeasureRelabel.pull Link4D Quat phiL refl_sigma).

    Definition Ec : list Link4D := filter isC LinksV.
    Definition Ep : list Link4D := filter isPp LinksV.
    Definition Em : list Link4D := filter isMm LinksV.

    Definition X (U : SU2Config) : R := chi U * exp (- su2_wilson_action beta Sp U).

    Definition T (U : SU2Config) : R :=
      obs_reflect f U * obs_translate_n D4_t 1 f U * exp (- su2_wilson_action beta Vol U).

    Definition Sker (U U' : SU2Config) : R :=
      rsum Sc (fun p => qdot (phi_c p U) (phi_c p U')).

    Definition inC (l : Link4D) : bool := existsb (link4D_eqb l) Ec.

    Local Notation mergeC := (ProductMeasureTwoCopy.merge Link4D Quat inC).

    (* ---------- the volume ---------- *)

    Lemma Sc_in : forall p, In p Sc -> wf_plaq_4D p /\ plaqC p.
    Proof.
      intros p Hp. split;
        [exact (proj1 (Forall_forall _ _) Sc_wf p Hp)
        | exact (proj1 (Forall_forall _ _) Sc_C p Hp)].
    Qed.

    Lemma Sp_in : forall p, In p Sp -> wf_plaq_4D p /\ plaqPp p.
    Proof.
      intros p Hp. split;
        [exact (proj1 (Forall_forall _ _) Sp_wf p Hp)
        | exact (proj1 (Forall_forall _ _) Sp_P p Hp)].
    Qed.

    Lemma in_vol_c : forall p, In p Sc -> In p Vol.
    Proof. intros p Hp. apply in_or_app. left. exact Hp. Qed.

    Lemma in_vol_p : forall p, In p Sp -> In p Vol.
    Proof. intros p Hp. apply in_or_app. right. apply in_or_app. left. exact Hp. Qed.

    Lemma vol_wf : forall p, In p Vol -> wf_plaq_4D p.
    Proof.
      intros p Hp. apply in_app_or in Hp. destruct Hp as [Hp | Hp];
        [exact (proj1 (Sc_in p Hp)) |].
      apply in_app_or in Hp. destruct Hp as [Hp | Hp]; [exact (proj1 (Sp_in p Hp)) |].
      apply in_map_iff in Hp. destruct Hp as [q [Hq Hin]]. subst p.
      apply plaqL_wf. exact (proj1 (Sp_in q Hin)).
    Qed.

    Lemma vol_sym : forall p, In p Vol -> In (plaqL p) Vol.
    Proof.
      intros p Hp. apply in_app_or in Hp. destruct Hp as [Hp | Hp].
      - rewrite (plaqC_fixed p (proj2 (Sc_in p Hp))). apply in_or_app. left. exact Hp.
      - apply in_app_or in Hp. apply in_or_app. right. destruct Hp as [Hp | Hp].
        + apply in_or_app. right. apply in_map. exact Hp.
        + apply in_map_iff in Hp. destruct Hp as [q [Hq Hin]]. subst p.
          rewrite plaqL_invol. apply in_or_app. left. exact Hin.
    Qed.

    Lemma links_sym : forall l, In l LinksV -> In (phiL l) LinksV.
    Proof.
      intros l Hl. unfold z2_links in Hl. apply (proj1 (dedup_In l _)) in Hl.
      apply in_flat_map in Hl. destruct Hl as [p [Hp Hlp]].
      apply (SU2Volume.links_in Vol (plaqL p) (phiL l) (vol_sym p Hp)).
      apply links_plaqL; [exact (vol_wf p Hp) | exact Hlp].
    Qed.

    Lemma links_nodup : NoDup LinksV.
    Proof. unfold z2_links. apply SU2AreaLaw.dedup_NoDup. Qed.

    Lemma in_Ec : forall l, In l Ec <-> In l LinksV /\ isC l = true.
    Proof. intro l. unfold Ec. apply filter_In. Qed.

    Lemma in_Ep : forall l, In l Ep <-> In l LinksV /\ isPp l = true.
    Proof. intro l. unfold Ep. apply filter_In. Qed.

    Lemma in_Em : forall l, In l Em <-> In l LinksV /\ isMm l = true.
    Proof. intro l. unfold Em. apply filter_In. Qed.

    Lemma Ec_Ep : forall l, In l Ec -> ~ In l Ep.
    Proof.
      intros l H H'. apply in_Ec in H. apply in_Ep in H'.
      pose proof (isC_not_Pp l (proj2 H)) as K. destruct H' as [_ H']. congruence.
    Qed.

    Lemma Ec_Em : forall l, In l Ec -> ~ In l Em.
    Proof.
      intros l H H'. apply in_Ec in H. apply in_Em in H'.
      pose proof (isC_not_Mm l (proj2 H)) as K. destruct H' as [_ H']. congruence.
    Qed.

    Lemma Ep_Em : forall l, In l Ep -> ~ In l Em.
    Proof.
      intros l H H'. apply in_Ep in H. apply in_Em in H'.
      pose proof (isPp_not_Mm l (proj2 H)) as K. destruct H' as [_ H']. congruence.
    Qed.

    Lemma E_perm : Permutation LinksV ((Ec ++ Ep) ++ Em).
    Proof.
      apply NoDup_Permutation; [exact links_nodup | |].
      - apply ProductMeasurePerm.nodup_app.
        + apply ProductMeasurePerm.nodup_app;
            [apply NoDup_filter; exact links_nodup
            | apply NoDup_filter; exact links_nodup | exact Ec_Ep].
        + apply NoDup_filter. exact links_nodup.
        + intros a Ha. apply in_app_or in Ha.
          destruct Ha as [Ha | Ha]; [exact (Ec_Em a Ha) | exact (Ep_Em a Ha)].
      - intro l. split.
        + intro Hl. apply in_or_app.
          destruct (class_cases l) as [H | [H | H]].
          * left. apply in_or_app. left. apply in_Ec. split; assumption.
          * left. apply in_or_app. right. apply in_Ep. split; assumption.
          * right. apply in_Em. split; assumption.
        + intro Hl. apply in_app_or in Hl. destruct Hl as [Hl | Hl].
          * apply in_app_or in Hl. destruct Hl as [Hl | Hl].
            -- exact (proj1 (proj1 (in_Ec l) Hl)).
            -- exact (proj1 (proj1 (in_Ep l) Hl)).
          * exact (proj1 (proj1 (in_Em l) Hl)).
    Qed.

    Lemma phiL_inj : forall x y, phiL x = phiL y -> x = y.
    Proof. intros x y H. rewrite <- (phiL_invol x), <- (phiL_invol y), H. reflexivity. Qed.

    Lemma Em_Ep : Permutation (map phiL Em) Ep.
    Proof.
      apply NoDup_Permutation.
      - apply (SU2Covariance.NoDup_map_inj _ _ phiL Em phiL_inj).
        unfold Em. apply NoDup_filter. exact links_nodup.
      - unfold Ep. apply NoDup_filter. exact links_nodup.
      - intro l. split.
        + intro Hl. apply in_map_iff in Hl. destruct Hl as [m [Hm Hin]]. subst l.
          apply in_Em in Hin. destruct Hin as [HmE HmM].
          apply in_Ep. split; [exact (links_sym m HmE) |].
          rewrite isPp_phiL, phiL_invol. exact HmM.
        + intro Hl. apply in_Ep in Hl. destruct Hl as [HlE HlP].
          apply in_map_iff. exists (phiL l). split; [apply phiL_invol |].
          apply in_Em. split; [exact (links_sym l HlE) |].
          rewrite <- isPp_phiL. exact HlP.
    Qed.

    Lemma inC_true : forall l, In l Ec -> inC l = true.
    Proof.
      intros l H. unfold inC. apply existsb_exists. exists l. split; [exact H |].
      apply (proj2 (link4D_eqb_spec l l)). reflexivity.
    Qed.

    Lemma inC_spec : forall l, inC l = true <-> In l Ec.
    Proof.
      intro l. split; [| apply inC_true].
      intro H. unfold inC in H. apply existsb_exists in H.
      destruct H as [x [Hx Hlx]]. apply link4D_eqb_spec in Hlx. subst x. exact Hx.
    Qed.

    Lemma inC_false : forall l, isC l = false -> inC l = false.
    Proof.
      intros l H. destruct (inC l) eqn:E; [| reflexivity].
      apply inC_spec in E. apply in_Ec in E. destruct E as [_ E]. congruence.
    Qed.

    (* ---------- locality ---------- *)

    Lemma X_agree : forall V V' : SU2Config,
      (forall l, isPp l = true -> In l LinksV -> V l = V' l) -> X V = X V'.
    Proof.
      intros V V' H. unfold X.
      rewrite (chi_loc V V'), (SU2Volume.action_local beta Sp V V'); [reflexivity | |].
      - intros l Hl. unfold z2_links in Hl. apply (proj1 (dedup_In l _)) in Hl.
        apply in_flat_map in Hl. destruct Hl as [p [Hp Hlp]]. apply H.
        + exact (plaqPp_links p l (proj2 (Sp_in p Hp)) Hlp).
        + exact (SU2Volume.links_in Vol p l (in_vol_p p Hp) Hlp).
      - intros p l Hp Hl. apply H.
        + exact (plaqPp_links p l (proj2 (Sp_in p (Q_in p Hp))) Hl).
        + exact (SU2Volume.links_in Vol p l (in_vol_p p (Q_in p Hp)) Hl).
    Qed.

    Lemma X_local : ProductMeasure.local_on Link4D Quat Ep X.
    Proof.
      intros A A' H. apply X_agree. intros l HP HL. apply H. apply in_Ep. split; assumption.
    Qed.

    Lemma T_decomp : forall U,
      T U = X U * X (pullL U) * exp (beta * rsum Sc (su2_plaq U)).
    Proof.
      intro U. unfold T, X. rewrite <- (obs_pullL f U).
      change (obs_translate_n D4_t 1 f U) with (chi U).
      rewrite !action_app2, <- (action_pullL beta Sp U Sp_wf).
      assert (HSc : su2_wilson_action beta Sc U = - (beta * rsum Sc (su2_plaq U)))
        by (unfold su2_wilson_action, rsum; ring).
      rewrite HSc.
      replace (- (- (beta * rsum Sc (su2_plaq U))
                  + (su2_wilson_action beta Sp U + su2_wilson_action beta Sp (pullL U))))
        with (- su2_wilson_action beta Sp U
              + (- su2_wilson_action beta Sp (pullL U) + beta * rsum Sc (su2_plaq U)))
        by ring.
      rewrite !exp_plus. ring.
    Qed.

    Lemma pullL_at : forall U l, pullL U l = refl_sigma l (U (phiL l)).
    Proof. intros U l. reflexivity. Qed.

    Lemma T_local : forall V V' : SU2Config,
      (forall l, In l LinksV -> V l = V' l) -> T V = T V'.
    Proof.
      intros V V' H. rewrite !T_decomp.
      rewrite (X_agree V V'), (X_agree (pullL V) (pullL V')).
      - assert (E : rsum Sc (su2_plaq V) = rsum Sc (su2_plaq V')).
        { apply rsum_ext. intros p Hp. apply plaq_local. intros l Hl. apply H.
          exact (SU2Volume.links_in Vol p l (in_vol_c p Hp) Hl). }
        rewrite E. reflexivity.
      - intros l _ Hl. rewrite !pullL_at. rewrite (H (phiL l) (links_sym l Hl)). reflexivity.
      - intros l _ Hl. apply H. exact Hl.
    Qed.

    (* ---------- the crossing term ---------- *)

    Lemma crossing_identity : forall (w U : SU2Config) p, In p Sc ->
      su2_plaq (Lbar w U) p = qdot (phi_c p U) (phi_c p (mergeC w (pullL U))).
    Proof.
      intros w U p Hp. destruct (Sc_in p Hp) as [Hwf HC].
      destruct (crossing_links p Hwf HC) as (H1 & H2 & H3 & H4 & H5 & H6 & I1 & I2 & I3).
      pose proof (SU2Volume.links_in Vol p (c1 p) (in_vol_c p Hp) I1) as L1.
      pose proof (SU2Volume.links_in Vol p (c2 p) (in_vol_c p Hp) I2) as L2.
      rewrite (plaq_cross (Lbar w U) p (proj1 HC)).
      unfold phi_c.
      rewrite (Lbar_C w U (c1 p) H1), (Lbar_C w U (c2 p) H2),
              (Lbar_notC w U (cA p) H4), (Lbar_notC w U (cB p) H5).
      rewrite gt_gt, qdot_gt_adj.
      unfold ProductMeasureTwoCopy.merge.
      rewrite (inC_true (c1 p)) by (apply in_Ec; split; assumption).
      rewrite (inC_true (c2 p)) by (apply in_Ec; split; assumption).
      rewrite (inC_false (cA p) H4), (H6 U). reflexivity.
    Qed.

    Lemma key_identity : forall w U : SU2Config,
      T (Lbar w U) = X U * X (pullL U) * exp (beta * Sker U (mergeC w (pullL U))).
    Proof.
      intros w U. rewrite T_decomp.
      rewrite (X_agree (Lbar w U) U), (X_agree (pullL (Lbar w U)) (pullL U)).
      - assert (E : rsum Sc (su2_plaq (Lbar w U)) = Sker U (mergeC w (pullL U))).
        { unfold Sker. apply rsum_ext. intros p Hp. apply crossing_identity. exact Hp. }
        rewrite E. reflexivity.
      - intros l HP _. rewrite !pullL_at.
        rewrite (Lbar_notC w U (phiL l)); [reflexivity |].
        apply isMm_notC. rewrite <- isPp_phiL. exact HP.
      - intros l HP _. apply Lbar_notC. apply isPp_notC. exact HP.
    Qed.

    Lemma phi_c_agree : forall p (U U' : SU2Config), In p Sc ->
      (forall l, In l (Ec ++ Ep) -> U l = U' l) -> phi_c p U = phi_c p U'.
    Proof.
      intros p U U' Hp H. destruct (Sc_in p Hp) as [Hwf HC].
      destruct (crossing_links p Hwf HC) as (H1 & H2 & H3 & H4 & H5 & H6 & I1 & I2 & I3).
      pose proof (SU2Volume.links_in Vol p (c1 p) (in_vol_c p Hp) I1) as L1.
      pose proof (SU2Volume.links_in Vol p (c2 p) (in_vol_c p Hp) I2) as L2.
      pose proof (SU2Volume.links_in Vol p (cA p) (in_vol_c p Hp) I3) as L3.
      unfold phi_c.
      rewrite (H (c1 p)), (H (cA p)), (H (c2 p)); [reflexivity | | |].
      - apply in_or_app. left. apply in_Ec. split; assumption.
      - apply in_or_app. right. apply in_Ep. split; assumption.
      - apply in_or_app. left. apply in_Ec. split; assumption.
    Qed.

    Lemma Sker_rk : PositiveKernel.rk Link4D Quat Sker.
    Proof.
      unfold Sker. apply PositiveKernel.rk_rsum. intros p _.
      apply (PositiveKernel.rk_ext Link4D Quat
               (fun U U' : SU2Config =>
                  qr (phi_c p U) * qr (phi_c p U')
                  + (qi (phi_c p U) * qi (phi_c p U')
                     + (qj (phi_c p U) * qj (phi_c p U')
                        + qk (phi_c p U) * qk (phi_c p U'))))).
      - intros U U'. unfold qdot. ring.
      - apply PositiveKernel.rk_plus;
          [exact (PositiveKernel.rk_one Link4D Quat (fun U => qr (phi_c p U))) |].
        apply PositiveKernel.rk_plus;
          [exact (PositiveKernel.rk_one Link4D Quat (fun U => qi (phi_c p U))) |].
        apply PositiveKernel.rk_plus;
          [exact (PositiveKernel.rk_one Link4D Quat (fun U => qj (phi_c p U)))
          | exact (PositiveKernel.rk_one Link4D Quat (fun U => qk (phi_c p U)))].
    Qed.

    (* ---------- the averaged sum is non-negative ---------- *)

    Lemma averaged_nonneg : forall G : list Quat,
      Permutation (map qconj G) G ->
      0 <= Cs G Ec (fun w : SU2Config => Cs G LinksV (fun U : SU2Config => T (Lbar w U)) U0) U0.
    Proof.
      intros G HG.
      rewrite (csum_ext Link4D Quat link4D_eqb G Ec _
                 (fun w => Cs G ((Ec ++ Ep) ++ Em)
                             (fun U => X U * X (pullP U)
                                       * exp (beta * Sker U (mergeC w (pullP U)))) U0)).
      2: { intro w.
           rewrite (ProductMeasurePerm.csum_perm Link4D Quat link4D_eqb link4D_eqb_spec G
                      LinksV ((Ec ++ Ep) ++ Em) E_perm).
           apply csum_ext. intro U. rewrite <- pullL_pull. apply key_identity. }
      rewrite (ProductMeasureTwoCopy.two_copy_identity Link4D Quat link4D_eqb
                 link4D_eqb_spec G phiL phiL phiL_invol phiL_invol refl_sigma
                 (SU2Covariance.refl_sigma_sum G HG) Ec Ep Em Em_Ep Ec_Ep Ec_Em Ep_Em
                 X X_local (fun U U' => exp (beta * Sker U U'))).
      - exact (PositiveKernel.double_exp_nonneg Link4D Quat link4D_eqb G Sker beta
                 Sker_rk beta_pos (Ec ++ Ep) X U0).
      - intros U U' Z H. unfold Sker.
        rewrite (rsum_ext Sc (fun p => qdot (phi_c p U) (phi_c p Z))
                   (fun p => qdot (phi_c p U') (phi_c p Z)));
          [reflexivity |].
        intros p Hp. rewrite (phi_c_agree p U U' Hp H). reflexivity.
      - intros U Z Z' H. unfold Sker.
        rewrite (rsum_ext Sc (fun p => qdot (phi_c p U) (phi_c p Z))
                   (fun p => qdot (phi_c p U) (phi_c p Z')));
          [reflexivity |].
        intros p Hp. rewrite (phi_c_agree p Z Z' Hp H). reflexivity.
      - exact inC_spec.
    Qed.

    (* ---------- the normalized grid sums of T are asymptotically >= 0 ---------- *)

    Lemma avgR_csum : forall n (Psi : SU2Config -> R),
      avgR (2 ^ n) LinksV Psi U0 =
      Cs (su2_grid n) LinksV Psi U0 / INR (length (su2_grid n)) ^ length LinksV.
    Proof.
      intros n Psi. rewrite <- (avgR_eq (2 ^ n) LinksV Psi U0 (pow2_pos n)).
      rewrite <- grid_gridN, su2_sum_csum. reflexivity.
    Qed.

    Lemma numerator_lower : forall eta : R, 0 < eta ->
      exists n2 : nat, forall n, (n2 <= n)%nat ->
        - eta <= SU2HaarLimit.avgn Vol n T.
    Proof.
      intros eta Heta.
      assert (HbcT : su2_bounded_continuous T).
      { unfold T.
        apply (SU2Continuity.bc_mult
                 (fun U => obs_reflect f U * obs_translate_n D4_t 1 f U)
                 (fun U => exp (- su2_wilson_action beta Vol U))).
        - apply (SU2Continuity.bc_mult (obs_reflect f) (obs_translate_n D4_t 1 f)).
          + apply bc_reflect. exact f_bc.
          + apply bc_translate_n. exact f_bc.
        - apply SU2Continuity.bc_boltzmann. }
      destruct HbcT as [[M0 HM0] HcT].
      set (M := Rmax M0 0).
      assert (HM : 0 <= M) by (unfold M; apply Rmax_r).
      assert (HbM : forall W, su2_unit_config W -> Rabs (T W) <= M).
      { intros W HW. eapply Rle_trans; [apply HM0; exact HW | unfold M; apply Rmax_l]. }
      set (NE := INR (length LinksV)).
      pose proof (pos_INR (length LinksV)) as HNE. fold NE in HNE.
      set (K := (NE + 1) * (2 * M + 3)).
      assert (HK : 0 < K) by (unfold K; apply Rmult_lt_0_compat; lra).
      set (eps := eta / K).
      assert (Heps : 0 < eps) by (unfold eps; apply Rdiv_lt_0_compat; lra).
      destruct (HcT eps Heps) as [d0 [Hd0 Hmod0]].
      assert (Hd : 0 < d0 / 64) by lra.
      destruct (SU2LinkTranslate.avgR_ltr M (d0 / 64) eps HM Hd Heps) as [n1 Hn1].
      exists (Nat.max n1 1). intros n Hn.
      assert (Hn1' : (n1 <= n)%nat) by lia.
      assert (Hn1'' : (1 <= n)%nat) by lia.
      set (G := su2_grid n).
      pose proof (SU2HaarGridConj.grid_conj n Hn1'') as HG. fold G in HG.
      set (g := INR (length G)).
      assert (Hg : 0 < g) by (unfold g, G; apply grid_length_pos).
      set (gE := g ^ length LinksV).
      assert (HgE : 0 < gE) by (unfold gE; apply pow_lt; exact Hg).
      (* for every w: avg T >= avg Phi_w - eta *)
      assert (Hw : forall w, su2_unit_config w ->
                Cs G LinksV (fun U : SU2Config => T (Lbar w U)) U0 + - eta * gE
                <= Cs G LinksV T U0).
      { intros w Hwu.
        pose proof (Hn1 n (aw w) (fun _ => qone) (fun U : SU2Config => T (Lbar w U)) LinksV U0 Hn1'
                      (aw_unit w Hwu) (fun _ => unit_one)) as B.
        assert (B' : Rabs (avgR (2 ^ n) LinksV (fun W => T (Lbar w (Lw w W))) U0
                           - avgR (2 ^ n) LinksV (fun U : SU2Config => T (Lbar w U)) (Lw w U0))
                     <= NE * ((2 * M + 3) * eps)).
        { apply B.
          - intros W HW. apply HbM.
            apply SU2LinkTranslate.ltr_unit;
              [apply abar_unit; exact Hwu | intro; apply unit_one | exact HW].
          - intros W W' HW HW' Hcl. left. apply Hmod0.
            + apply SU2LinkTranslate.ltr_unit;
                [apply abar_unit; exact Hwu | intro; apply unit_one | exact HW].
            + apply SU2LinkTranslate.ltr_unit;
                [apply abar_unit; exact Hwu | intro; apply unit_one | exact HW'].
            + intro l. replace d0 with (8 * (8 * (d0 / 64))) by field.
              apply SU2LinkTranslate.ltr_close;
                [apply abar_unit; exact Hwu | intro; apply unit_one | exact Hd
                | exact HW | exact HW' | exact Hcl].
          - exact unit_config_one. }
        assert (E1 : (fun W : SU2Config => T (Lbar w (Lw w W))) = T).
        { apply functional_extensionality. intro W. rewrite (Lbar_Lw w W Hwu). reflexivity. }
        rewrite E1 in B'.
        rewrite (avgR_local (2 ^ n) LinksV LinksV (fun U : SU2Config => T (Lbar w U))) with (U' := U0)
          in B'.
        - rewrite !avgR_csum in B'. fold G g gE in B'.
          apply abs_le_inv in B'.
          assert (E2 : NE * ((2 * M + 3) * eps) <= eta).
          { unfold eps, K.
            replace (NE * ((2 * M + 3) * (eta / ((NE + 1) * (2 * M + 3)))))
              with (eta * (NE * / (NE + 1))) by (field; lra).
            apply Rle_trans with (eta * 1); [| lra].
            apply Rmult_le_compat_l; [lra |].
            apply Rmult_le_reg_r with (NE + 1); [lra |].
            rewrite Rmult_assoc, Rinv_l by lra. lra. }
          assert (E3 : Cs G LinksV (fun U : SU2Config => T (Lbar w U)) U0 / gE - eta
                       <= Cs G LinksV T U0 / gE) by lra.
          apply Rmult_le_reg_r with (/ gE); [apply Rinv_0_lt_compat; exact HgE |].
          rewrite Rmult_plus_distr_r.
          replace (- eta * gE * / gE) with (- eta) by (field; lra).
          unfold Rdiv in E3. lra.
        - intros V V' HVV. apply T_local. intros l Hl.
          unfold Lbar, SU2LinkTranslate.ltr. rewrite (HVV l Hl). reflexivity.
        - intros l Hl Hnl. contradiction. }
      (* summing over w *)
      pose proof (averaged_nonneg G HG) as HD.
      assert (Hsum : Cs G Ec (fun w : SU2Config => Cs G LinksV (fun U : SU2Config => T (Lbar w U)) U0
                                       + - eta * gE) U0
                     <= Cs G Ec (fun _ : SU2Config => Cs G LinksV T U0) U0).
      { apply (ProductMeasure.csum_le_good Link4D Quat link4D_eqb G su2_unit).
        - intros v Hv. exact (grid_point_unit n v Hv).
        - intros w Hwg. apply Hw. exact Hwg.
        - exact unit_config_one. }
      assert (Hplus :
                Cs G Ec (fun w : SU2Config => Cs G LinksV (fun U : SU2Config => T (Lbar w U)) U0
                                              + - eta * gE) U0
                = Cs G Ec (fun w : SU2Config => Cs G LinksV (fun U : SU2Config => T (Lbar w U)) U0) U0
                  + - eta * gE * g ^ length Ec).
      { etransitivity;
          [exact (csum_plus Link4D Quat link4D_eqb G Ec
                    (fun w : SU2Config => Cs G LinksV (fun U : SU2Config => T (Lbar w U)) U0)
                    (fun _ => - eta * gE) U0) |].
        apply Rplus_eq_compat_l.
        exact (ProductMeasure.csum_const Link4D Quat link4D_eqb G Ec (- eta * gE) U0). }
      assert (Hconst : Cs G Ec (fun _ : SU2Config => Cs G LinksV T U0) U0
                       = Cs G LinksV T U0 * g ^ length Ec)
        by exact (ProductMeasure.csum_const Link4D Quat link4D_eqb G Ec
                    (Cs G LinksV T U0) U0).
      rewrite Hplus, Hconst in Hsum.
      set (gC := g ^ length Ec) in *.
      assert (HgC : 0 < gC) by (unfold gC; apply pow_lt; exact Hg).
      assert (Hfin : - eta * gE <= Cs G LinksV T U0).
      { apply Rmult_le_reg_r with gC; [exact HgC |]. lra. }
      unfold SU2HaarLimit.avgn. rewrite su2_sum_csum. fold G g gE.
      apply Rmult_le_reg_r with gE; [exact HgE |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. lra.
    Qed.

    (* reflection positivity with respect to the hyperplane t = 1/2 *)
    Theorem link_rp_finite : forall v : R,
      su2_haar_expect_is beta Vol
        (fun U => obs_reflect f U * obs_translate_n D4_t 1 f U) v ->
      0 <= v.
    Proof.
      intros v Hv. apply Rnot_lt_le. intro Hneg.
      set (c := exp (- (Rabs beta * INR (length Vol)))).
      assert (Hc : 0 < c) by (unfold c; apply exp_pos).
      assert (Heta : 0 < - v * c / 2).
      { apply Rdiv_lt_0_compat; [| lra]. apply Rmult_lt_0_compat; lra. }
      destruct (numerator_lower (- v * c / 2) Heta) as [n2 Hn2].
      assert (Hv2 : 0 < - v / 2) by lra.
      destruct (Hv (- v / 2) Hv2) as [N HN].
      set (n := Nat.max n2 N).
      pose proof (Hn2 n (Nat.le_max_l n2 N)) as E1.
      pose proof (HN n (Nat.le_max_r n2 N)) as E2. unfold R_dist in E2.
      rewrite (SU2HaarLimit.expect_avg beta Vol n) in E2.
      pose proof (SU2HaarLimit.avg_den_lower beta Vol n) as HD. fold c in HD.
      set (D := SU2HaarLimit.avgn Vol n
                  (fun U => exp (- su2_wilson_action beta Vol U))) in *.
      assert (E2' : Rabs (SU2HaarLimit.avgn Vol n T / D - v) < - v / 2) by exact E2.
      set (A := SU2HaarLimit.avgn Vol n T) in *.
      assert (HDp : 0 < D) by lra.
      apply Rabs_def2 in E2'.
      assert (E3 : v / 2 * D <= A) by nra.
      assert (E4 : v / 2 <= A / D).
      { apply Rmult_le_reg_r with D; [exact HDp |].
        unfold Rdiv at 2. rewrite Rmult_assoc, Rinv_l by lra. lra. }
      lra.
    Qed.
  End FiniteRP.

  (* =======================================================================
     3. Volumes symmetric under the link reflection
     ======================================================================= *)

  Definition bC (p : Plaq4D) : bool := tdir (p4_mu p) && (s4_t (p4_site p) =? 0)%Z.
  Definition bPp (p : Plaq4D) : bool := (1 <=? s4_t (p4_site p))%Z.

  Lemma tdir_spec : forall d, tdir d = true <-> d = D4_t.
  Proof. intro d. destruct d; cbn [tdir]; split; intro H; try reflexivity; discriminate. Qed.

  Lemma bC_spec : forall p, bC p = true <-> plaqC p.
  Proof.
    intro p. unfold bC, plaqC. split.
    - intro H. apply andb_true_iff in H. destruct H as [H1 H2].
      split; [apply tdir_spec; exact H1 | apply Z.eqb_eq; exact H2].
    - intros [H1 H2]. apply andb_true_iff.
      split; [apply tdir_spec; exact H1 | apply Z.eqb_eq; exact H2].
  Qed.

  Lemma bPp_spec : forall p, bPp p = true <-> plaqPp p.
  Proof. intro p. unfold bPp, plaqPp. apply Z.leb_le. Qed.

  Definition ScL (k : nat) : list Plaq4D := filter bC (su2_box k).
  Definition SpL (k : nat) : list Plaq4D := filter bPp (su2_box k).
  Definition symL (k : nat) : list Plaq4D := ScL k ++ SpL k ++ map plaqL (SpL k).

  Lemma ScL_in : forall k p, In p (ScL k) <-> In p (su2_box k) /\ plaqC p.
  Proof. intros k p. unfold ScL. rewrite filter_In, bC_spec. reflexivity. Qed.

  Lemma SpL_in : forall k p, In p (SpL k) <-> In p (su2_box k) /\ plaqPp p.
  Proof. intros k p. unfold SpL. rewrite filter_In, bPp_spec. reflexivity. Qed.

  Lemma ScL_wf : forall k, Forall wf_plaq_4D (ScL k).
  Proof.
    intro k. apply Forall_forall. intros p Hp. apply ScL_in in Hp.
    exact (SU2MassGap.box_wf_in k p (proj1 Hp)).
  Qed.

  Lemma ScL_C : forall k, Forall plaqC (ScL k).
  Proof. intro k. apply Forall_forall. intros p Hp. apply ScL_in in Hp. exact (proj2 Hp). Qed.

  Lemma SpL_wf : forall k, Forall wf_plaq_4D (SpL k).
  Proof.
    intro k. apply Forall_forall. intros p Hp. apply SpL_in in Hp.
    exact (SU2MassGap.box_wf_in k p (proj1 Hp)).
  Qed.

  Lemma SpL_P : forall k, Forall plaqPp (SpL k).
  Proof. intro k. apply Forall_forall. intros p Hp. apply SpL_in in Hp. exact (proj2 Hp). Qed.

  Lemma symL_wf : forall k, Forall wf_plaq_4D (symL k).
  Proof.
    intro k. unfold symL. apply Forall_app. split; [apply ScL_wf |].
    apply Forall_app. split; [apply SpL_wf |].
    apply Forall_forall. intros p Hp. apply in_map_iff in Hp. destruct Hp as [q [Hq Hin]].
    subst p. apply plaqL_wf. exact (proj1 (Forall_forall _ _) (SpL_wf k) q Hin).
  Qed.

  Lemma plaqL_inj : forall x y, plaqL x = plaqL y -> x = y.
  Proof. intros x y H. rewrite <- (plaqL_invol x), <- (plaqL_invol y), H. reflexivity. Qed.

  Lemma symL_nodup : forall k, NoDup (symL k).
  Proof.
    intro k. unfold symL. apply ProductMeasurePerm.nodup_app.
    - unfold ScL. apply NoDup_filter. apply LatticeBoxes.box_nodup.
    - apply ProductMeasurePerm.nodup_app.
      + unfold SpL. apply NoDup_filter. apply LatticeBoxes.box_nodup.
      + apply (SU2Covariance.NoDup_map_inj _ _ plaqL (SpL k) plaqL_inj).
        unfold SpL. apply NoDup_filter. apply LatticeBoxes.box_nodup.
      + intros a Ha Ha'. apply SpL_in in Ha. destruct Ha as [_ Ha].
        apply in_map_iff in Ha'. destruct Ha' as [q [Hq Hin]]. subst a.
        apply SpL_in in Hin. exact (proj1 (plaqPp_mirror q (proj2 Hin)) Ha).
    - intros a Ha Ha'. apply ScL_in in Ha. destruct Ha as [_ [Hmu Ht]].
      apply in_app_or in Ha'. destruct Ha' as [Ha' | Ha'].
      + apply SpL_in in Ha'. destruct Ha' as [_ Ha']. unfold plaqPp in Ha'. lia.
      + apply in_map_iff in Ha'. destruct Ha' as [q [Hq Hin]]. subst a.
        apply SpL_in in Hin.
        exact (proj2 (plaqPp_mirror q (proj2 Hin)) (conj Hmu Ht)).
  Qed.

  Lemma box_plaqL : forall m p, In p (su2_box m) -> In (plaqL p) (su2_box (S (S m))).
  Proof.
    intros m p Hp. unfold plaqL. apply box_shift. apply box_reflect. exact Hp.
  Qed.

  Lemma symL_exhaust : forall m, exists K : nat,
    forall k, (K <= k)%nat -> incl (su2_box m) (symL k).
  Proof.
    intro m. exists (S (S m)). intros k Hk p Hp. unfold symL.
    assert (Hpk : In p (su2_box k)).
    { apply (LatticeBoxes.box_mono m k); [lia | exact Hp]. }
    destruct (mirror_class p) as [H | [H | H]].
    - apply in_or_app. left. apply ScL_in. split; assumption.
    - apply in_or_app. right. apply in_or_app. left. apply SpL_in. split; assumption.
    - apply in_or_app. right. apply in_or_app. right. apply in_map_iff.
      exists (plaqL p). split; [apply plaqL_invol |].
      apply SpL_in. split; [| exact H].
      apply (LatticeBoxes.box_mono (S (S m)) k Hk). apply box_plaqL. exact Hp.
  Qed.

  (* =======================================================================
     4. The infinite-volume state
     ======================================================================= *)

  Lemma abs_beta : forall beta : R, 0 <= beta -> Rabs beta = beta.
  Proof. intros beta H. apply Rabs_pos_eq. exact H. Qed.

  Lemma shifted_pos : forall (P : list Plaq4D),
    Forall wf_plaq_4D P -> Forall pos_time_plaq P ->
    Forall wf_plaq_4D (map (plaq_shift D4_t) P) /\
    Forall plaqPp (map (plaq_shift D4_t) P).
  Proof.
    intros P HP Hpos. split.
    - apply Forall_forall. intros p Hp. apply in_map_iff in Hp.
      destruct Hp as [q [Hq Hin]]. subst p. apply plaq_shift_wf.
      exact (proj1 (Forall_forall _ _) HP q Hin).
    - apply Forall_forall. intros p Hp. apply in_map_iff in Hp.
      destruct Hp as [q [Hq Hin]]. subst p.
      pose proof (proj1 (Forall_forall _ _) Hpos q Hin) as Ht.
      unfold pos_time_plaq in Ht. unfold plaqPp, plaq_shift.
      cbn [p4_site shift4D s4_t]. lia.
  Qed.

  (* TARGET 12a *)
  Theorem su2_transfer_matrix_positivity : Challenge_SU2Gauge4D_TransferMatrixPositivity.
  Proof.
    intros beta P f Hb0 Hb HP Hpos Hloc Hbc.
    assert (Hbeta : 43008 * Rabs beta <= 1) by (rewrite (abs_beta beta Hb0); exact Hb).
    assert (Hf : SU2MassGap.PosObs f)
      by (split; [exact Hbc |]; exists P; repeat split; assumption).
    assert (Hg : SU2MassGap.LocObs
                   (fun U => obs_reflect f U * obs_translate_n D4_t 1 f U)).
    { apply SU2MassGap.loc_mult;
        [apply SU2MassGap.loc_reflect | apply SU2MassGap.loc_translate_n];
        apply SU2MassGap.pos_loc; exact Hf. }
    destruct (SU2MassGap.loc_exists beta Hbeta _ Hg) as [v Hv].
    exists v. split; [exact Hv |].
    destruct Hg as [Hbc2 [Q2 [HQ2 Hloc2]]].
    destruct (SU2Uniqueness.haar_seq_exists beta symL
                (fun U => obs_reflect f U * obs_translate_n D4_t 1 f U) Hbc2) as [w Hw].
    pose proof (SU2Uniqueness.su2_infinite_volume_uniqueness beta Q2
                  (fun U => obs_reflect f U * obs_translate_n D4_t 1 f U) symL w v
                  Hbeta HQ2 Hloc2 Hbc2 symL_nodup symL_wf symL_exhaust Hw Hv) as Hcv.
    destruct (shifted_pos P HP Hpos) as [HQwf HQpos].
    destruct (LatticeBoxes.box_exhaust (map (plaq_shift D4_t) P) HQwf) as [n0 Hn0].
    apply (SU2Uniqueness.cv_nonneg_from w v n0 Hcv). intros k Hk.
    apply (link_rp_finite beta Hb0 (ScL k) (SpL k) (map (plaq_shift D4_t) P)
             (ScL_wf k) (ScL_C k) (SpL_wf k) (SpL_P k)) with (f := f).
    - intros p Hp. apply SpL_in. split.
      + exact (LatticeBoxes.box_mono n0 k Hk p (Hn0 p Hp)).
      + exact (proj1 (Forall_forall _ _) HQpos p Hp).
    - exact Hbc.
    - exact (local_translate D4_t f P Hloc).
    - exact (Hw k).
  Qed.

  (* TARGET 12b *)
  Theorem su2_transfer_matrix_spectral_bounds :
    Challenge_SU2Gauge4D_TransferMatrixSpectralBounds.
  Proof.
    intros beta mu P f Hmu Hb0 Hsmall Hb HP Hpos Hloc Hbc.
    assert (Hbeta : 43008 * Rabs beta <= 1) by (rewrite (abs_beta beta Hb0); exact Hb).
    assert (Hsmall' : 168 * Rabs beta <= exp (- mu))
      by (rewrite (abs_beta beta Hb0); exact Hsmall).
    destruct (SU2MassGap.su2_transfer_matrix_mass_gap beta mu P f 1%nat Hmu Hsmall' Hbeta
                HP Hpos Hloc Hbc) as [v0 [v1 [vf [H0 [H1 [Hvf [Hnn Hgap]]]]]]].
    exists v0, v1, vf.
    split; [exact H0 |]. split; [exact H1 |]. split; [exact Hvf |].
    assert (Hf : SU2MassGap.PosObs f)
      by (split; [exact Hbc |]; exists P; repeat split; assumption).
    (* (psi, T psi) = v1 - vf^2 >= 0 *)
    pose proof (SU2MassGap.form_value beta Hbeta f f vf vf 1%nat v1 Hf Hf Hvf Hvf H1)
      as Hpsi.
    pose proof (SU2MassGap.psi_pos P HP Hpos f Hloc Hbc vf) as [Hbcp [Q' [HQ' [Hpos' Hloc']]]].
    destruct (su2_transfer_matrix_positivity beta Q' (SU2MassGap.psi f vf) Hb0 Hb HQ' Hpos'
                Hloc' Hbcp) as [v1' [Hv1' Hnn']].
    assert (E : v1' = v1 - vf * vf)
      by exact (SU2Uniqueness.inf_unique beta _ v1' (v1 - vf * vf) Hv1' Hpsi).
    split; [lra |].
    replace (- (mu / 2) * INR 1) with (- (mu / 2)) in Hgap by (simpl; ring).
    pose proof (Rle_abs (v1 - vf * vf)). lra.
  Qed.

  (* TARGET 12c *)
  Theorem su2_transfer_matrix_symmetry : Challenge_SU2Gauge4D_TransferMatrixSymmetry.
  Proof.
    intros beta P Q f g Hbeta HP HPpos HQ HQpos Hlf Hlg Hbf Hbg.
    assert (Hf : SU2MassGap.PosObs f)
      by (split; [exact Hbf |]; exists P; repeat split; assumption).
    assert (Hg : SU2MassGap.PosObs g)
      by (split; [exact Hbg |]; exists Q; repeat split; assumption).
    assert (Hl1 : SU2MassGap.LocObs (fun U => obs_reflect f U * g U)).
    { apply SU2MassGap.loc_mult; [apply SU2MassGap.loc_reflect |];
        apply SU2MassGap.pos_loc; assumption. }
    destruct (SU2MassGap.loc_exists beta Hbeta _ Hl1) as [v Hv].
    assert (Hl2 : SU2MassGap.LocObs
                    (fun U => obs_reflect (obs_translate_n D4_t 1 f) U * g U)).
    { apply SU2MassGap.loc_mult;
        [apply SU2MassGap.loc_reflect; apply SU2MassGap.loc_translate_n |];
        apply SU2MassGap.pos_loc; assumption. }
    destruct (SU2MassGap.loc_exists beta Hbeta _ Hl2) as [v' Hv'].
    exists v, v'.
    split; [exact Hv |].
    split; [exact (SU2MassGap.form_sym beta Hbeta f g v Hf Hg Hv) |].
    split; [| exact Hv'].
    pose proof (SU2MassGap.loc_translate_inv beta Hbeta 1%nat _ v' Hl2 Hv') as Ht.
    apply (SU2Uniqueness.inf_ext beta
             (obs_translate_n D4_t 1
                (fun U => obs_reflect (obs_translate_n D4_t 1 f) U * g U))); [| exact Ht].
    intro U. rewrite SU2MassGap.translate_n_mult, translate_reflect_translate.
    reflexivity.
  Qed.

  (* TARGET 12d *)
  Theorem su2_transfer_matrix_contraction : Challenge_SU2Gauge4D_TransferMatrixContraction.
  Proof.
    intros beta P f k Hbeta HP Hpos Hloc Hbc.
    assert (Hsmall : 168 * Rabs beta <= exp (- 0)).
    { rewrite Ropp_0, exp_0. pose proof (Rabs_pos beta). lra. }
    destruct (SU2MassGap.su2_transfer_matrix_mass_gap beta 0 P f k (Rle_refl 0) Hsmall Hbeta
                HP Hpos Hloc Hbc) as [v0 [vk [vf [H0 [Hk [Hvf [Hnn Hgap]]]]]]].
    exists v0, vk. split; [exact H0 |]. split; [exact Hk |].
    replace (- (0 / 2) * INR k) with 0 in Hgap by (unfold Rdiv; ring).
    rewrite exp_0 in Hgap.
    replace vk with ((vk - vf * vf) + vf * vf) by ring.
    eapply Rle_trans; [apply Rabs_triang |].
    assert (Hsq : Rabs (vf * vf) = vf * vf).
    { apply Rabs_pos_eq. pose proof (Rle_0_sqr vf) as Q. unfold Rsqr in Q. exact Q. }
    rewrite Hsq. lra.
  Qed.

End SU2TransferPositivity.
