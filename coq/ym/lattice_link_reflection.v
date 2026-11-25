(* =========================================================================
   ym/lattice_link_reflection.v

   The reflection t -> 1 - t of the lattice Z^4, in the hyperplane t = 1/2
   through the midpoints of the time-like links between t = 0 and t = 1
   ("link reflection"), obtained by composing the site reflection t -> -t of
   verification/ChallengeSU2MassGap.v with the translation by one unit of
   time:

     - `pullL U = su2_reflect (su2_translate D4_t U)`, the reflected gauge
       field; `phiL`, `plaqL`, its action on links and plaquettes;
     - (Theta f) (U) = (tau f) (pullL U): the pair (Theta f, tau f) of
       Target 12 is exchanged by the link reflection;
     - the three classes of links (cut by the hyperplane / at times >= 1 /
       mirror images) and of plaquettes (crossing / at times >= 1 / mirror
       images);
     - a crossing plaquette p reads
         (1/2) tr U_p = < u A u'^{-1} , B >,
       with u, u' its two cut links, A its spatial link at time 1 and B its
       spatial link at time 0, the mirror image of A.

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
Require Import rg.product_measure_relabel.
Require Import ym.su2_algebra.
Require Import ym.lattice_symmetry.
Require Import ym.su2_haar_mean.
Require Import ym.su2_gauge_invariance.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeSU2Gauge ChallengeSU2InfiniteVolume.
Import ChallengeSU2MassGap.
Import DupClustering SU2Algebra LatticeSymmetry SU2HaarMean SU2GaugeInvariance.
Open Scope R_scope.

Module LatticeLinkReflection.

  (* =======================================================================
     1. The link reflection
     ======================================================================= *)

  Definition pullL (U : SU2Config) : SU2Config := su2_reflect (su2_translate D4_t U).

  Definition phiL (l : Link4D) : Link4D := link_shift D4_t (link_reflect l).

  Definition plaqL (p : Plaq4D) : Plaq4D := plaq_shift D4_t (plaq_reflect p).

  Lemma pullL_pull : forall U,
    pullL U = ProductMeasureRelabel.pull Link4D Quat phiL refl_sigma U.
  Proof. intro U. apply functional_extensionality. intro l. reflexivity. Qed.

  Lemma phiL_invol : forall l, phiL (phiL l) = l.
  Proof.
    intro l. unfold phiL. rewrite shift_reflect_shift. apply link_reflect_invol.
  Qed.

  Lemma obs_pullL : forall (f : SU2Config -> R) U,
    obs_translate D4_t f (pullL U) = obs_reflect f U.
  Proof.
    intros f U. unfold obs_translate, obs_reflect, pullL.
    rewrite translate_reflect_translate_cfg. reflexivity.
  Qed.

  Lemma plaqL_wf : forall p, wf_plaq_4D p -> wf_plaq_4D (plaqL p).
  Proof. intros p H. unfold plaqL. apply plaq_shift_wf. apply plaq_reflect_wf. exact H. Qed.

  Lemma plaq_pullL : forall U p, wf_plaq_4D p ->
    su2_plaq (pullL U) p = su2_plaq U (plaqL p).
  Proof.
    intros U p H. unfold pullL, plaqL.
    rewrite (plaq_reflect_cov (su2_translate D4_t U) p H). apply plaq_translate.
  Qed.

  Lemma action_pullL : forall beta (Lam : list Plaq4D) U, Forall wf_plaq_4D Lam ->
    su2_wilson_action beta Lam (pullL U) = su2_wilson_action beta (map plaqL Lam) U.
  Proof.
    intros beta Lam U H. unfold pullL.
    rewrite (action_reflect beta Lam (su2_translate D4_t U) H), action_translate, map_map.
    reflexivity.
  Qed.

  Lemma plaqL_invol : forall p, plaqL (plaqL p) = p.
  Proof.
    intros [[t x y z] mu nu].
    destruct mu; unfold plaqL, plaq_shift, plaq_reflect, site_reflect;
      cbn [p4_site p4_mu p4_nu s4_t s4_x s4_y s4_z shift4D];
      apply plaq_eq; apply site_eq; lia.
  Qed.

  Lemma links_plaqL : forall p l, wf_plaq_4D p ->
    In l (plaq4D_links p) -> In (phiL l) (plaq4D_links (plaqL p)).
  Proof.
    intros p l Hwf Hl. unfold plaqL, phiL. rewrite links_plaq_shift.
    apply in_map. apply (proj2 (links_plaq_reflect p (link_reflect l) Hwf)).
    rewrite link_reflect_invol. exact Hl.
  Qed.

  (* =======================================================================
     2. The three classes of links
     ======================================================================= *)

  Definition ltime (l : Link4D) : Z := s4_t (fst l).

  Definition tdir (d : Dir4D) : bool :=
    match d with D4_t => true | D4_x => false | D4_y => false | D4_z => false end.

  (* the time-like links between t = 0 and t = 1, cut by the hyperplane *)
  Definition isC (l : Link4D) : bool := tdir (snd l) && (ltime l =? 0)%Z.
  (* the links at times >= 1 *)
  Definition isPp (l : Link4D) : bool := (1 <=? ltime l)%Z.
  (* the mirror images of the latter *)
  Definition isMm (l : Link4D) : bool := negb (isC l) && negb (isPp l).

  Ltac zbool :=
    repeat match goal with
           | H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H
           | H : (_ <=? _)%Z = false |- _ => apply Z.leb_gt in H
           | H : (_ =? _)%Z = true |- _ => apply Z.eqb_eq in H
           | H : (_ =? _)%Z = false |- _ => apply Z.eqb_neq in H
           end.

  Lemma isPp_phiL : forall l, isPp l = isMm (phiL l).
  Proof.
    intros [[t x y z] d]. unfold isMm, isC, isPp, phiL, ltime.
    destruct d; unfold link_shift, link_reflect, site_reflect;
      cbn [fst snd s4_t s4_x s4_y s4_z shift4D tdir andb negb];
      repeat match goal with
             | |- context [(?a <=? ?b)%Z] => destruct (Z.leb_spec a b)
             | |- context [(?a =? ?b)%Z] => destruct (Z.eqb_spec a b)
             end;
      cbn [andb negb]; try reflexivity; lia.
  Qed.

  Lemma isC_not_Pp : forall l, isC l = true -> isPp l = false.
  Proof.
    intros l H. unfold isC in H. apply andb_true_iff in H. destruct H as [_ H].
    unfold isPp. destruct (1 <=? ltime l)%Z eqn:E; [| reflexivity]. zbool. lia.
  Qed.

  Lemma isC_not_Mm : forall l, isC l = true -> isMm l = false.
  Proof. intros l H. unfold isMm. rewrite H. reflexivity. Qed.

  Lemma isPp_not_Mm : forall l, isPp l = true -> isMm l = false.
  Proof. intros l H. unfold isMm. rewrite H. cbn [negb]. apply andb_false_r. Qed.

  Lemma class_cases : forall l, isC l = true \/ isPp l = true \/ isMm l = true.
  Proof.
    intro l. unfold isMm. destruct (isC l); [left; reflexivity |].
    destruct (isPp l); [right; left; reflexivity | right; right; reflexivity].
  Qed.

  (* =======================================================================
     3. The classes of plaquettes
     ======================================================================= *)

  (* time-like plaquettes between t = 0 and t = 1 *)
  Definition plaqC (p : Plaq4D) : Prop :=
    p4_mu p = D4_t /\ s4_t (p4_site p) = 0%Z.

  (* plaquettes at times >= 1 *)
  Definition plaqPp (p : Plaq4D) : Prop := (1 <= s4_t (p4_site p))%Z.

  Lemma plaqC_fixed : forall p, plaqC p -> plaqL p = p.
  Proof.
    intros [[t x y z] mu nu] [Hmu Ht]. cbn [p4_mu p4_site s4_t] in *. subst mu t.
    unfold plaqL, plaq_shift, plaq_reflect.
    cbn [p4_site p4_mu p4_nu s4_t s4_x s4_y s4_z shift4D].
    apply plaq_eq. apply site_eq; lia.
  Qed.

  Lemma plaqPp_links : forall p l, plaqPp p -> In l (plaq4D_links p) -> isPp l = true.
  Proof.
    intros [[t x y z] mu nu] l Ht Hl. unfold plaqPp in Ht. cbn [p4_site s4_t] in Ht.
    unfold plaq4D_links in Hl. cbn [p4_site p4_mu p4_nu In] in Hl.
    unfold isPp, ltime. apply Z.leb_le.
    destruct Hl as [Hl | [Hl | [Hl | [Hl | []]]]]; subst l; cbn [fst];
      destruct mu, nu; cbn [shift4D s4_t]; lia.
  Qed.

  Lemma plaqPp_mirror : forall p, plaqPp p ->
    ~ plaqPp (plaqL p) /\ ~ plaqC (plaqL p).
  Proof.
    intros [[t x y z] mu nu] Ht. unfold plaqPp in *. cbn [p4_site s4_t] in Ht.
    unfold plaqC, plaqL, plaq_shift, plaq_reflect, site_reflect.
    destruct mu; cbn [p4_site p4_mu p4_nu s4_t s4_x s4_y s4_z shift4D];
      (split; [lia | intros [K1 K2]; try discriminate K1; lia]).
  Qed.

  Lemma mirror_class : forall p, plaqC p \/ plaqPp p \/ plaqPp (plaqL p).
  Proof.
    intros [[t x y z] mu nu]. unfold plaqC, plaqPp, plaqL, plaq_shift, plaq_reflect,
      site_reflect.
    destruct (Z_le_dec 1 t) as [H1 | H1]; [right; left; exact H1 |].
    destruct mu; cbn [p4_site p4_mu p4_nu s4_t s4_x s4_y s4_z shift4D].
    - destruct (Z.eq_dec t 0) as [H0 | H0];
        [left; split; [reflexivity | exact H0] | right; right; lia].
    - right. right. lia.
    - right. right. lia.
    - right. right. lia.
  Qed.

  (* =======================================================================
     4. Crossing plaquettes
     ======================================================================= *)

  Definition c1 (p : Plaq4D) : Link4D := (p4_site p, D4_t).
  Definition c2 (p : Plaq4D) : Link4D := (shift4D (p4_site p) (p4_nu p), D4_t).
  Definition cA (p : Plaq4D) : Link4D := (shift4D (p4_site p) D4_t, p4_nu p).
  Definition cB (p : Plaq4D) : Link4D := (p4_site p, p4_nu p).

  (* u A u'^{-1} *)
  Definition phi_c (p : Plaq4D) (U : SU2Config) : Quat :=
    gt (U (c1 p)) (U (cA p)) (U (c2 p)).

  Lemma qr_qdot4 : forall u A u' B : Quat,
    qr (qmul u (qmul A (qmul (qconj u') (qconj B)))) =
    qdot (qmul u (qmul A (qconj u'))) B.
  Proof.
    intros [u0 u1 u2 u3] [a0 a1 a2 a3] [v0 v1 v2 v3] [b0 b1 b2 b3].
    unfold qdot, qmul, qconj. cbn [qr qi qj qk]. ring.
  Qed.

  Lemma plaq_cross : forall U p, p4_mu p = D4_t ->
    su2_plaq U p = qdot (phi_c p U) (U (cB p)).
  Proof.
    intros U p Hmu. rewrite plaq_formula, Hmu. unfold phi_c, gt, c1, c2, cA, cB.
    apply qr_qdot4.
  Qed.

  Lemma crossing_links : forall p, wf_plaq_4D p -> plaqC p ->
    isC (c1 p) = true /\ isC (c2 p) = true /\
    isPp (cA p) = true /\ isC (cA p) = false /\ isC (cB p) = false /\
    (forall U, pullL U (cA p) = U (cB p)) /\
    In (c1 p) (plaq4D_links p) /\ In (c2 p) (plaq4D_links p) /\
    In (cA p) (plaq4D_links p).
  Proof.
    intros [[t x y z] mu nu] Hwf [Hmu Ht]. cbn [p4_mu p4_site s4_t] in Hmu, Ht.
    subst mu t. unfold wf_plaq_4D, canonical_planes_4D in Hwf.
    cbn [p4_mu p4_nu In] in Hwf.
    destruct Hwf as [H | [H | [H | [H | [H | [H | []]]]]]];
      inversion H; subst nu;
      (split; [reflexivity |]; split; [reflexivity |]; split; [reflexivity |];
       split; [reflexivity |]; split; [reflexivity |];
       split;
       [ intro U; unfold pullL, cA, cB; rewrite su2_reflect_sigma;
         unfold su2_translate, refl_sigma, link_shift, link_reflect, site_reflect;
         cbn [p4_site p4_nu fst snd s4_t s4_x s4_y s4_z shift4D];
         f_equal; apply link_eq; apply site_eq; lia
       | split; [left; reflexivity |];
         split; [right; right; right; left; reflexivity
                | right; right; left; reflexivity] ]).
  Qed.

  (* =======================================================================
     5. Algebra of the crossing term
     ======================================================================= *)

  Lemma gt_one_r : forall a U, gt a U qone = qmul a U.
  Proof. intros a U. unfold gt. rewrite qconj_one, qmul_one_r. reflexivity. Qed.

  Lemma gt_gt : forall a b u A u',
    gt (qmul a u) A (qmul b u') = gt a (gt u A u') b.
  Proof.
    intros a b u A u'. unfold gt. rewrite qconj_mul, <- !qmul_assoc. reflexivity.
  Qed.

  Lemma qdot_gt_adj : forall a b X Y,
    qdot (gt (qconj a) X (qconj b)) Y = qdot X (gt a Y b).
  Proof.
    intros [a0 a1 a2 a3] [b0 b1 b2 b3] [x0 x1 x2 x3] [y0 y1 y2 y3].
    unfold qdot, gt, qmul, qconj. cbn [qr qi qj qk]. ring.
  Qed.

End LatticeLinkReflection.
