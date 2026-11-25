(* =========================================================================
   ym/su2_reflection_positivity.v

   Reflection positivity of the 4D SU(2) Wilson lattice gauge theory in a
   finite volume that is symmetric under the time reflection t -> -t, for
   every finite a-priori link distribution G that is invariant under
   inversion:

     0 <= <(Theta F) F>      for F localized at non-negative times.

   The volume is S0 ++ Sp ++ Theta(Sp), with S0 spatial plaquettes in the
   hyperplane t = 0 (each is its own mirror image) and Sp plaquettes at
   non-negative times that are not of this kind.  The links of the volume
   split accordingly into the links E0 of the hyperplane (fixed by the
   reflection), the remaining links Ep at non-negative times, and their
   mirror images Em.  The Boltzmann weight factorizes as
     W0(U) * Wp(U) * Wp(Theta U),
   with W0 depending only on E0 and Wp only on E0 ++ Ep, so the abstract
   identity `ProductMeasureRelabel.csum_reflection_identity` gives

     sum_U (Theta F)(U) F(U) e^{-S(U)}
        = sum_{U on E0} W0(U) * ( sum_{U on Ep} F(U) Wp(U) )^2  >=  0.

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
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import rg.product_measure_perm.
Require Import rg.product_measure_relabel.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_polymer_gas.
Require Import ym.su2_algebra.
Require Import ym.su2_area_law.
Require Import ym.su2_volume.
Require Import ym.lattice_symmetry.
Require Import ym.su2_covariance.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import ChallengeSU2InfiniteVolume ChallengeSU2MassGap.
Import DupClustering Z2GaugeExpansion Z2PolymerGas SU2Algebra LatticeSymmetry.
Open Scope R_scope.

Module SU2ReflectionPositivity.

  Ltac zb :=
    repeat match goal with
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : (_ <=? _)%Z = false |- _ => apply Z.leb_gt in H
           | H : (_ <? _)%Z = true |- _ => apply Z.ltb_lt in H
           | H : (_ <? _)%Z = false |- _ => apply Z.ltb_ge in H
           | H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H
           | H : (_ =? _)%Z = false |- _ => apply Z.eqb_neq in H
           end.

  (* =======================================================================
     1. The three classes of links
     ======================================================================= *)

  Definition link_time (l : Link4D) : Z := s4_t (fst l).

  Definition spatialb (d : Dir4D) : bool :=
    match d with D4_t => false | D4_x => true | D4_y => true | D4_z => true end.

  (* spatial links of the hyperplane t = 0 *)
  Definition is0 (l : Link4D) : bool := spatialb (snd l) && (link_time l =? 0)%Z.
  (* the other links at non-negative times *)
  Definition isP (l : Link4D) : bool := (0 <=? link_time l)%Z && negb (is0 l).
  (* links at negative times *)
  Definition isM (l : Link4D) : bool := (link_time l <? 0)%Z.

  Lemma is0_fixed : forall l, is0 l = true ->
    link_reflect l = l /\ (forall v, refl_sigma l v = v).
  Proof.
    intros [[t x y z] d] H. unfold is0, link_time in H. cbn [fst snd s4_t] in H.
    apply andb_true_iff in H. destruct H as [Hs Ht]. apply Z.eqb_eq in Ht. subst t.
    destruct d; cbn [spatialb] in Hs; try discriminate;
      (split; [reflexivity | intro v; reflexivity]).
  Qed.

  Lemma isP_isM_reflect : forall l, isP l = isM (link_reflect l).
  Proof.
    intros [[t x y z] d]. unfold isP, isM, is0, link_time.
    destruct d; unfold link_reflect, site_reflect;
      cbn [fst snd s4_t spatialb andb negb].
    - destruct (0 <=? t)%Z eqn:H1, (- t - 1 <? 0)%Z eqn:H2;
        cbn [andb negb]; try reflexivity; zb; lia.
    - destruct (0 <=? t)%Z eqn:H1, (t =? 0)%Z eqn:H2, (- t <? 0)%Z eqn:H3;
        cbn [andb negb]; try reflexivity; zb; lia.
    - destruct (0 <=? t)%Z eqn:H1, (t =? 0)%Z eqn:H2, (- t <? 0)%Z eqn:H3;
        cbn [andb negb]; try reflexivity; zb; lia.
    - destruct (0 <=? t)%Z eqn:H1, (t =? 0)%Z eqn:H2, (- t <? 0)%Z eqn:H3;
        cbn [andb negb]; try reflexivity; zb; lia.
  Qed.

  Lemma is0_not_P : forall l, is0 l = true -> isP l = false.
  Proof. intros l H. unfold isP. rewrite H. cbn [negb]. apply andb_false_r. Qed.

  Lemma is0_not_M : forall l, is0 l = true -> isM l = false.
  Proof.
    intros l H. unfold is0 in H. apply andb_true_iff in H. destruct H as [_ H].
    unfold isM. destruct (link_time l <? 0)%Z eqn:H1; [| reflexivity]. zb. lia.
  Qed.

  Lemma isP_not_M : forall l, isP l = true -> isM l = false.
  Proof.
    intros l H. unfold isP in H. apply andb_true_iff in H. destruct H as [H _].
    unfold isM. destruct (link_time l <? 0)%Z eqn:H1; [| reflexivity]. zb. lia.
  Qed.

  Lemma nonneg_cases : forall l, (0 <= link_time l)%Z -> is0 l = true \/ isP l = true.
  Proof.
    intros l H. destruct (is0 l) eqn:H0; [left; reflexivity | right].
    unfold isP. rewrite H0. cbn [negb]. rewrite andb_true_r. apply Z.leb_le. exact H.
  Qed.

  Lemma link_cases : forall l, is0 l = true \/ isP l = true \/ isM l = true.
  Proof.
    intro l. destruct (isM l) eqn:HM; [right; right; reflexivity |].
    unfold isM in HM. zb. destruct (nonneg_cases l HM) as [H | H]; [left | right; left]; exact H.
  Qed.

  (* =======================================================================
     2. The classes of plaquettes
     ======================================================================= *)

  (* spatial plaquettes of the hyperplane t = 0 *)
  Definition plaq0 (p : Plaq4D) : Prop :=
    p4_mu p <> D4_t /\ s4_t (p4_site p) = 0%Z.

  (* the other plaquettes at non-negative times *)
  Definition plaqP (p : Plaq4D) : Prop :=
    (0 <= s4_t (p4_site p))%Z /\ (p4_mu p = D4_t \/ (1 <= s4_t (p4_site p))%Z).

  Lemma plaq0_links : forall p l, wf_plaq_4D p -> plaq0 p ->
    In l (plaq4D_links p) -> is0 l = true.
  Proof.
    intros [[t x y z] mu nu] l Hwf [Hmu Ht] Hl. cbn [p4_mu p4_site s4_t] in *. subst t.
    unfold wf_plaq_4D, canonical_planes_4D in Hwf. cbn [p4_mu p4_nu In] in Hwf.
    unfold plaq4D_links in Hl. cbn [p4_site p4_mu p4_nu In] in Hl.
    destruct Hwf as [H | [H | [H | [H | [H | [H | []]]]]]];
      injection H as Hm Hn; subst mu nu;
      try (exfalso; apply Hmu; reflexivity);
      destruct Hl as [Hl | [Hl | [Hl | [Hl | []]]]]; subst l; reflexivity.
  Qed.

  Lemma plaq0_reflect : forall p, plaq0 p -> plaq_reflect p = p.
  Proof.
    intros [[t x y z] mu nu] [Hmu Ht]. cbn [p4_mu p4_site s4_t] in *. subst t.
    destruct mu; [exfalso; apply Hmu; reflexivity | reflexivity | reflexivity | reflexivity].
  Qed.

  Lemma pos_links : forall p l, (0 <= s4_t (p4_site p))%Z ->
    In l (plaq4D_links p) -> (0 <= link_time l)%Z.
  Proof.
    intros [[t x y z] mu nu] l Ht Hl. cbn [p4_site s4_t] in Ht.
    unfold plaq4D_links in Hl. cbn [p4_site p4_mu p4_nu In] in Hl.
    destruct Hl as [Hl | [Hl | [Hl | [Hl | []]]]]; subst l; unfold link_time; cbn [fst];
      destruct mu, nu; cbn [shift4D s4_t]; lia.
  Qed.

  (* =======================================================================
     3. Reflection positivity in a symmetric finite volume
     ======================================================================= *)

  Section RP.
    Variable G : list Quat.
    Hypothesis G_nonempty : G <> [].
    Hypothesis G_conj : Permutation (map qconj G) G.
    Variable beta : R.
    Variables S0 Sp P : list Plaq4D.
    Hypothesis S0_wf : Forall wf_plaq_4D S0.
    Hypothesis S0_fix : Forall plaq0 S0.
    Hypothesis Sp_wf : Forall wf_plaq_4D Sp.
    Hypothesis Sp_pos : Forall plaqP Sp.
    Hypothesis P_in : incl P (S0 ++ Sp).
    Variable F : SU2Config -> R.
    Hypothesis F_loc : su2_local_on F P.

    Local Notation Vol := (S0 ++ Sp ++ map plaq_reflect Sp).
    Local Notation LinksV := (z2_links Vol).
    Local Notation Cs := (csum Link4D Quat link4D_eqb G).
    Local Notation pullR := (ProductMeasureRelabel.pull Link4D Quat link_reflect refl_sigma).
    Local Notation LocalOn := (ProductMeasure.local_on Link4D Quat).

    Definition E0 : list Link4D := filter is0 LinksV.
    Definition Ep : list Link4D := filter isP LinksV.
    Definition Em : list Link4D := filter isM LinksV.

    Definition W0 (U : SU2Config) : R := exp (- su2_wilson_action beta S0 U).
    Definition X (U : SU2Config) : R := F U * exp (- su2_wilson_action beta Sp U).

    Lemma pull_reflect : forall U : SU2Config, pullR U = su2_reflect U.
    Proof.
      intro U. apply functional_extensionality. intro l.
      unfold ProductMeasureRelabel.pull. symmetry. apply su2_reflect_sigma.
    Qed.

    (* ---------- the volume and its links are symmetric ---------- *)

    Lemma S0_in : forall p, In p S0 -> wf_plaq_4D p /\ plaq0 p.
    Proof.
      intros p Hp. split;
        [exact (proj1 (Forall_forall wf_plaq_4D S0) S0_wf p Hp)
        | exact (proj1 (Forall_forall plaq0 S0) S0_fix p Hp)].
    Qed.

    Lemma Sp_in : forall p, In p Sp -> wf_plaq_4D p /\ plaqP p.
    Proof.
      intros p Hp. split;
        [exact (proj1 (Forall_forall wf_plaq_4D Sp) Sp_wf p Hp)
        | exact (proj1 (Forall_forall plaqP Sp) Sp_pos p Hp)].
    Qed.

    Lemma vol_wf : forall p, In p Vol -> wf_plaq_4D p.
    Proof.
      intros p Hp. apply in_app_or in Hp. destruct Hp as [Hp | Hp];
        [exact (proj1 (S0_in p Hp)) |].
      apply in_app_or in Hp. destruct Hp as [Hp | Hp]; [exact (proj1 (Sp_in p Hp)) |].
      apply in_map_iff in Hp. destruct Hp as [q [Hq Hin]]. subst p.
      apply plaq_reflect_wf. exact (proj1 (Sp_in q Hin)).
    Qed.

    Lemma vol_reflect : forall p, In p Vol -> In (plaq_reflect p) Vol.
    Proof.
      intros p Hp. apply in_app_or in Hp. destruct Hp as [Hp | Hp].
      - rewrite (plaq0_reflect p (proj2 (S0_in p Hp))). apply in_or_app. left. exact Hp.
      - apply in_app_or in Hp. apply in_or_app. right. destruct Hp as [Hp | Hp].
        + apply in_or_app. right. apply in_map. exact Hp.
        + apply in_map_iff in Hp. destruct Hp as [q [Hq Hin]]. subst p.
          rewrite (plaq_reflect_invol q (proj1 (Sp_in q Hin))).
          apply in_or_app. left. exact Hin.
    Qed.

    Lemma links_sym : forall l, In l LinksV -> In (link_reflect l) LinksV.
    Proof.
      intros l Hl. unfold z2_links in Hl. apply (proj1 (dedup_In l _)) in Hl.
      apply in_flat_map in Hl. destruct Hl as [p [Hp Hlp]].
      apply (SU2Volume.links_in Vol (plaq_reflect p) (link_reflect l) (vol_reflect p Hp)).
      apply (proj2 (links_plaq_reflect p (link_reflect l) (vol_wf p Hp))).
      rewrite link_reflect_invol. exact Hlp.
    Qed.

    Lemma links_nodup : NoDup LinksV.
    Proof. unfold z2_links. apply SU2AreaLaw.dedup_NoDup. Qed.

    Lemma E_perm : Permutation LinksV (E0 ++ Ep ++ Em).
    Proof.
      apply NoDup_Permutation; [exact links_nodup | |].
      - apply ProductMeasurePerm.nodup_app; [apply NoDup_filter; exact links_nodup | |].
        + apply ProductMeasurePerm.nodup_app;
            [apply NoDup_filter; exact links_nodup
            | apply NoDup_filter; exact links_nodup |].
          intros a Ha Ha'. unfold Ep in Ha. unfold Em in Ha'.
          apply filter_In in Ha. apply filter_In in Ha'.
          pose proof (isP_not_M a (proj2 Ha)) as H. destruct Ha' as [_ H']. congruence.
        + intros a Ha Ha'. unfold E0 in Ha. apply filter_In in Ha. destruct Ha as [_ Ha].
          apply in_app_or in Ha'. destruct Ha' as [Ha' | Ha'].
          * unfold Ep in Ha'. apply filter_In in Ha'. destruct Ha' as [_ Ha'].
            pose proof (is0_not_P a Ha). congruence.
          * unfold Em in Ha'. apply filter_In in Ha'. destruct Ha' as [_ Ha'].
            pose proof (is0_not_M a Ha). congruence.
      - intro l. split.
        + intro Hl. apply in_or_app.
          destruct (link_cases l) as [H | [H | H]].
          * left. unfold E0. apply filter_In. split; assumption.
          * right. apply in_or_app. left. unfold Ep. apply filter_In. split; assumption.
          * right. apply in_or_app. right. unfold Em. apply filter_In. split; assumption.
        + intro Hl. apply in_app_or in Hl. destruct Hl as [Hl | Hl].
          * unfold E0 in Hl. apply filter_In in Hl. exact (proj1 Hl).
          * apply in_app_or in Hl. destruct Hl as [Hl | Hl].
            -- unfold Ep in Hl. apply filter_In in Hl. exact (proj1 Hl).
            -- unfold Em in Hl. apply filter_In in Hl. exact (proj1 Hl).
    Qed.

    Lemma Em_Ep : Permutation (map link_reflect Em) Ep.
    Proof.
      apply NoDup_Permutation.
      - apply (SU2Covariance.NoDup_map_inj _ _ link_reflect Em SU2Covariance.link_reflect_inj).
        unfold Em. apply NoDup_filter. exact links_nodup.
      - unfold Ep. apply NoDup_filter. exact links_nodup.
      - intro l. split.
        + intro Hl. apply in_map_iff in Hl. destruct Hl as [m [Hm Hin]]. subst l.
          unfold Em in Hin. apply filter_In in Hin. destruct Hin as [HmE HmM].
          unfold Ep. apply filter_In. split; [exact (links_sym m HmE) |].
          rewrite isP_isM_reflect, link_reflect_invol. exact HmM.
        + intro Hl. unfold Ep in Hl. apply filter_In in Hl. destruct Hl as [HlE HlP].
          apply in_map_iff. exists (link_reflect l). split; [apply link_reflect_invol |].
          unfold Em. apply filter_In. split; [exact (links_sym l HlE) |].
          rewrite <- isP_isM_reflect. exact HlP.
    Qed.

    (* ---------- the weight factorizes ---------- *)

    Lemma action_app : forall (L1 L2 : list Plaq4D) (U : SU2Config),
      su2_wilson_action beta (L1 ++ L2) U =
      su2_wilson_action beta L1 U + su2_wilson_action beta L2 U.
    Proof.
      intros L1 L2 U. unfold su2_wilson_action.
      change (fold_right Rplus 0 (map (su2_plaq U) (L1 ++ L2)))
        with (rsum (L1 ++ L2) (su2_plaq U)).
      rewrite rsum_app. unfold rsum. ring.
    Qed.

    Lemma integrand_eq : forall U : SU2Config,
      obs_reflect F U * F U * exp (- su2_wilson_action beta Vol U) =
      W0 U * (X U * X (pullR U)).
    Proof.
      intro U. rewrite pull_reflect. unfold W0, X, obs_reflect.
      rewrite !action_app, <- (action_reflect beta Sp U Sp_wf).
      replace (- (su2_wilson_action beta S0 U
                  + (su2_wilson_action beta Sp U
                     + su2_wilson_action beta Sp (su2_reflect U))))
        with (- su2_wilson_action beta S0 U
              + (- su2_wilson_action beta Sp U
                 + - su2_wilson_action beta Sp (su2_reflect U))) by ring.
      rewrite !exp_plus. ring.
    Qed.

    (* ---------- locality ---------- *)

    Lemma pos_in : forall l, In l LinksV -> (0 <= link_time l)%Z -> In l (E0 ++ Ep).
    Proof.
      intros l Hl Ht. apply in_or_app. destruct (nonneg_cases l Ht) as [H | H].
      - left. unfold E0. apply filter_In. split; assumption.
      - right. unfold Ep. apply filter_In. split; assumption.
    Qed.

    Lemma in_vol_0 : forall p, In p S0 -> In p Vol.
    Proof. intros p Hp. apply in_or_app. left. exact Hp. Qed.

    Lemma in_vol_p : forall p, In p Sp -> In p Vol.
    Proof. intros p Hp. apply in_or_app. right. apply in_or_app. left. exact Hp. Qed.

    Lemma W0_local : LocalOn E0 W0.
    Proof.
      intros A A' H. unfold W0.
      rewrite (SU2Volume.action_local beta S0 A A'); [reflexivity |].
      intros l Hl. apply H. unfold z2_links in Hl. apply (proj1 (dedup_In l _)) in Hl.
      apply in_flat_map in Hl. destruct Hl as [p [Hp Hlp]].
      unfold E0. apply filter_In. split.
      - exact (SU2Volume.links_in Vol p l (in_vol_0 p Hp) Hlp).
      - exact (plaq0_links p l (proj1 (S0_in p Hp)) (proj2 (S0_in p Hp)) Hlp).
    Qed.

    Lemma pos_plaq_link : forall p l, In p (S0 ++ Sp) -> In l (plaq4D_links p) ->
      In l (E0 ++ Ep).
    Proof.
      intros p l Hp Hl. apply in_app_or in Hp. destruct Hp as [Hp | Hp].
      - apply pos_in; [exact (SU2Volume.links_in Vol p l (in_vol_0 p Hp) Hl) |].
        apply (pos_links p l); [| exact Hl].
        destruct (proj2 (S0_in p Hp)) as [_ Ht]. rewrite Ht. lia.
      - apply pos_in; [exact (SU2Volume.links_in Vol p l (in_vol_p p Hp) Hl) |].
        apply (pos_links p l); [| exact Hl].
        exact (proj1 (proj2 (Sp_in p Hp))).
    Qed.

    Lemma X_local : LocalOn (E0 ++ Ep) X.
    Proof.
      intros A A' H. unfold X.
      rewrite (F_loc A A').
      2: { intros p l Hp Hl. apply H. exact (pos_plaq_link p l (P_in p Hp) Hl). }
      rewrite (SU2Volume.action_local beta Sp A A'); [reflexivity |].
      intros l Hl. apply H. unfold z2_links in Hl. apply (proj1 (dedup_In l _)) in Hl.
      apply in_flat_map in Hl. destruct Hl as [p [Hp Hlp]].
      apply (pos_plaq_link p l); [apply in_or_app; right; exact Hp | exact Hlp].
    Qed.

    (* ---------- positivity ---------- *)

    Lemma numerator_nonneg :
      0 <= Cs LinksV
             (fun U => obs_reflect F U * F U * exp (- su2_wilson_action beta Vol U))
             (fun _ => qone).
    Proof.
      rewrite (ProductMeasurePerm.csum_perm Link4D Quat link4D_eqb link4D_eqb_spec G
                 LinksV (E0 ++ Ep ++ Em) E_perm).
      rewrite (csum_ext Link4D Quat link4D_eqb G (E0 ++ Ep ++ Em)
                 (fun U => obs_reflect F U * F U * exp (- su2_wilson_action beta Vol U))
                 (fun U => W0 U * (X U * X (pullR U)))) by exact integrand_eq.
      apply (ProductMeasureRelabel.csum_reflection_positive
               Link4D Quat link4D_eqb link4D_eqb_spec G
               link_reflect link_reflect link_reflect_invol link_reflect_invol
               refl_sigma (SU2Covariance.refl_sigma_sum G G_conj)
               E0 Ep Em).
      - intros l Hl. unfold E0 in Hl. apply filter_In in Hl. exact (is0_fixed l (proj2 Hl)).
      - exact Em_Ep.
      - intros l Hl Hl'. unfold E0 in Hl. unfold Ep in Hl'.
        apply filter_In in Hl. apply filter_In in Hl'.
        pose proof (is0_not_P l (proj2 Hl)) as H. destruct Hl' as [_ H']. congruence.
      - intros l Hl Hl'. unfold E0 in Hl. unfold Em in Hl'.
        apply filter_In in Hl. apply filter_In in Hl'.
        pose proof (is0_not_M l (proj2 Hl)) as H. destruct Hl' as [_ H']. congruence.
      - intros l Hl Hl'. unfold Ep in Hl. unfold Em in Hl'.
        apply filter_In in Hl. apply filter_In in Hl'.
        pose proof (isP_not_M l (proj2 Hl)) as H. destruct Hl' as [_ H']. congruence.
      - exact W0_local.
      - exact X_local.
      - intro A. unfold W0. left. apply exp_pos.
    Qed.

    Theorem instance_reflection_positivity :
      0 <= su2_expect_on G beta Vol (fun U => obs_reflect F U * F U).
    Proof.
      rewrite expect_csum.
      assert (Hpos : 0 < Cs LinksV
                           (fun U => exp (- su2_wilson_action beta Vol U)) (fun _ => qone)).
      { apply csum_pos; [exact G_nonempty |]. intro A. apply exp_pos. }
      unfold Rdiv. apply Rmult_le_pos; [exact numerator_nonneg |].
      left. apply Rinv_0_lt_compat. exact Hpos.
    Qed.
  End RP.

  (* reflection positivity for every symmetric finite volume and every finite
     a-priori distribution invariant under inversion *)
  Theorem reflection_positivity_finite :
    forall (G : list Quat) (beta : R) (S0 Sp P : list Plaq4D) (F : SU2Config -> R),
      G <> [] ->
      Permutation (map qconj G) G ->
      Forall wf_plaq_4D S0 -> Forall plaq0 S0 ->
      Forall wf_plaq_4D Sp -> Forall plaqP Sp ->
      incl P (S0 ++ Sp) ->
      su2_local_on F P ->
      0 <= su2_expect_on G beta (S0 ++ Sp ++ map plaq_reflect Sp)
             (fun U => obs_reflect F U * F U).
  Proof.
    intros G beta S0 Sp P F HG HGc HS0 HS0f HSp HSpp HP HF.
    exact (instance_reflection_positivity G HG HGc beta S0 Sp P HS0 HS0f HSp HSpp HP F HF).
  Qed.

End SU2ReflectionPositivity.
