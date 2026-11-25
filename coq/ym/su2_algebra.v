(* =========================================================================
   ym/su2_algebra.v

   Elementary algebra of the unit quaternions (the gauge group SU(2)) and of
   the frozen lattice objects of `verification/ChallengeSU2Gauge.v`:

     - the Hamilton product is norm-multiplicative, so path-ordered products
       and loop holonomies of SU(2)-valued configurations stay in SU(2) and
       every (1/2) tr lies in [-1, 1];
     - a path-ordered product only depends on the links of the path;
     - multiplying one link variable by the central element -1 multiplies a
       path-ordered product by (-1)^(number of occurrences of the link);
     - the Boltzmann weight is the product of the plaquette factors;
     - the frozen finite a-priori sum `su2_sum` is the abstract
       configuration sum `DupClustering.csum`.

   Depends ONLY on Coq stdlib + the frozen challenge files
   + rg.dup_clustering + ym.z2_gauge_expansion + ym.z2_polymer_gas.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import rg.dup_clustering.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_polymer_gas.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import DupClustering Z2GaugeExpansion Z2PolymerGas.
Open Scope R_scope.

Module SU2Algebra.

  (* =======================================================================
     1. Quaternion algebra
     ======================================================================= *)

  Lemma quat_eq : forall p q : Quat,
    qr p = qr q -> qi p = qi q -> qj p = qj q -> qk p = qk q -> p = q.
  Proof.
    intros [a b c d] [a' b' c' d']. cbn [qr qi qj qk]. intros; subst. reflexivity.
  Qed.

  (* multiplication by a real scalar *)
  Definition qscale (c : R) (q : Quat) : Quat :=
    mkQuat (c * qr q) (c * qi q) (c * qj q) (c * qk q).

  Ltac qsolve :=
    apply quat_eq;
    unfold qmul, qconj, qneg, qone, qscale; cbn [qr qi qj qk]; ring.

  Lemma qmul_one_r : forall q, qmul q qone = q.
  Proof. intro q. qsolve. Qed.

  Lemma qmul_one_l : forall q, qmul qone q = q.
  Proof. intro q. qsolve. Qed.

  Lemma qmul_assoc : forall p q r, qmul p (qmul q r) = qmul (qmul p q) r.
  Proof. intros p q r. qsolve. Qed.

  Lemma qconj_one : qconj qone = qone.
  Proof. qsolve. Qed.

  Lemma qneg_scale : forall q, qneg q = qscale (-1) q.
  Proof. intro q. qsolve. Qed.

  Lemma qscale_one : forall q, qscale 1 q = q.
  Proof. intro q. qsolve. Qed.

  Lemma qscale_scale : forall c d q, qscale c (qscale d q) = qscale (c * d) q.
  Proof. intros c d q. qsolve. Qed.

  Lemma qmul_scale_l : forall c p q, qmul (qscale c p) q = qscale c (qmul p q).
  Proof. intros c p q. qsolve. Qed.

  Lemma qmul_scale_r : forall c p q, qmul p (qscale c q) = qscale c (qmul p q).
  Proof. intros c p q. qsolve. Qed.

  Lemma qconj_scale : forall c q, qconj (qscale c q) = qscale c (qconj q).
  Proof. intros c q. qsolve. Qed.

  Lemma qr_scale : forall c q, qr (qscale c q) = c * qr q.
  Proof. intros c q. reflexivity. Qed.

  Lemma qnorm2_mul : forall p q, qnorm2 (qmul p q) = qnorm2 p * qnorm2 q.
  Proof. intros p q. unfold qnorm2, qmul. cbn [qr qi qj qk]. ring. Qed.

  Lemma qnorm2_conj : forall q, qnorm2 (qconj q) = qnorm2 q.
  Proof. intro q. unfold qnorm2, qconj. cbn [qr qi qj qk]. ring. Qed.

  Lemma qnorm2_neg : forall q, qnorm2 (qneg q) = qnorm2 q.
  Proof. intro q. unfold qnorm2, qneg. cbn [qr qi qj qk]. ring. Qed.

  Lemma unit_one : su2_unit qone.
  Proof. unfold su2_unit, qnorm2, qone. cbn [qr qi qj qk]. ring. Qed.

  Lemma unit_mul : forall p q, su2_unit p -> su2_unit q -> su2_unit (qmul p q).
  Proof.
    intros p q Hp Hq. unfold su2_unit in *. rewrite qnorm2_mul, Hp, Hq. ring.
  Qed.

  Lemma unit_conj : forall q, su2_unit q -> su2_unit (qconj q).
  Proof. intros q H. unfold su2_unit in *. rewrite qnorm2_conj. exact H. Qed.

  Lemma unit_neg : forall q, su2_unit q -> su2_unit (qneg q).
  Proof. intros q H. unfold su2_unit in *. rewrite qnorm2_neg. exact H. Qed.

  (* every component of a unit quaternion lies in [-1, 1] *)
  Lemma unit_components : forall q, su2_unit q ->
    (-1 <= qr q <= 1) /\ (-1 <= qi q <= 1) /\ (-1 <= qj q <= 1) /\ (-1 <= qk q <= 1).
  Proof.
    intros [a b c d]. unfold su2_unit, qnorm2. cbn [qr qi qj qk]. intro H.
    pose proof (Rle_0_sqr a) as Ha. pose proof (Rle_0_sqr b) as Hb.
    pose proof (Rle_0_sqr c) as Hc. pose proof (Rle_0_sqr d) as Hd.
    unfold Rsqr in *. repeat split; nra.
  Qed.

  Lemma unit_qr_bound : forall q, su2_unit q -> -1 <= qr q <= 1.
  Proof. intros q H. exact (proj1 (unit_components q H)). Qed.

  Lemma unit_config_one : su2_unit_config (fun _ => qone).
  Proof. intro l. exact unit_one. Qed.

  Lemma unit_config_update : forall U l g,
    su2_unit_config U -> su2_unit g -> su2_unit_config (su2_update U l g).
  Proof.
    intros U l g HU Hg l'. unfold su2_update.
    destruct (link4D_eqb l' l); [exact Hg | apply HU].
  Qed.

  (* =======================================================================
     2. Path-ordered products, loop holonomies, plaquettes
     ======================================================================= *)

  Lemma path_nil : forall U, su2_path U [] = qone.
  Proof. reflexivity. Qed.

  Lemma path_cons : forall U l C, su2_path U (l :: C) = qmul (U l) (su2_path U C).
  Proof. reflexivity. Qed.

  Lemma path_unit : forall U C, su2_unit_config U -> su2_unit (su2_path U C).
  Proof.
    intros U C HU. induction C as [| l C IH].
    - rewrite path_nil. exact unit_one.
    - rewrite path_cons. apply unit_mul; [apply HU | exact IH].
  Qed.

  Lemma rect_unit : forall U s mu nu a b, su2_unit_config U ->
    su2_unit (su2_rect_holonomy U s mu nu a b).
  Proof.
    intros U s mu nu a b HU. unfold su2_rect_holonomy.
    repeat first [apply unit_mul | apply unit_conj | apply path_unit; exact HU].
  Qed.

  Lemma wilson_bound : forall U s mu nu a b, su2_unit_config U ->
    -1 <= su2_wilson_loop U s mu nu a b <= 1.
  Proof.
    intros U s mu nu a b HU. unfold su2_wilson_loop.
    apply unit_qr_bound. apply rect_unit. exact HU.
  Qed.

  Lemma plaq_bound : forall U p, su2_unit_config U -> -1 <= su2_plaq U p <= 1.
  Proof. intros U p HU. unfold su2_plaq. apply wilson_bound. exact HU. Qed.

  Lemma path_local : forall U U' C,
    (forall l, In l C -> U l = U' l) -> su2_path U C = su2_path U' C.
  Proof.
    intros U U' C H. induction C as [| l C IH]; [reflexivity |].
    rewrite !path_cons, (H l (or_introl eq_refl)), IH; [reflexivity |].
    intros l' Hl'. apply H. right. exact Hl'.
  Qed.

  Lemma wilson_local : forall U U' s mu nu a b,
    (forall l, In l (z2_rect_loop s mu nu a b) -> U l = U' l) ->
    su2_wilson_loop U s mu nu a b = su2_wilson_loop U' s mu nu a b.
  Proof.
    intros U U' s mu nu a b H. unfold su2_wilson_loop, su2_rect_holonomy.
    unfold z2_rect_loop in H.
    rewrite (path_local U U' (z2_segment s mu a)),
            (path_local U U' (z2_segment (shift4D_n s mu a) nu b)),
            (path_local U U' (z2_segment (shift4D_n s nu b) mu a)),
            (path_local U U' (z2_segment s nu b)); [reflexivity | | | |];
      intros l Hl; apply H; repeat (apply in_or_app; first [left; exact Hl | right]);
      exact Hl.
  Qed.

  (* the 1 x 1 loop at p runs over the 4 links of p *)
  Lemma rect11_In : forall p l,
    In l (z2_rect_loop (p4_site p) (p4_mu p) (p4_nu p) 1 1) <-> In l (plaq4D_links p).
  Proof.
    intros [s mu nu] l. unfold z2_rect_loop, z2_segment, plaq4D_links.
    cbn [p4_site p4_mu p4_nu seq map shift4D_n app In]. tauto.
  Qed.

  Lemma rect11_count : forall p l,
    link4D_count l (z2_rect_loop (p4_site p) (p4_mu p) (p4_nu p) 1 1) =
    link4D_count l (plaq4D_links p).
  Proof.
    intros [s mu nu] l. unfold z2_rect_loop, z2_segment, plaq4D_links.
    cbn [p4_site p4_mu p4_nu seq map shift4D_n app link4D_count]. lia.
  Qed.

  Lemma plaq_local : forall U U' p,
    (forall l, In l (plaq4D_links p) -> U l = U' l) -> su2_plaq U p = su2_plaq U' p.
  Proof.
    intros U U' p H. unfold su2_plaq. apply wilson_local.
    intros l Hl. apply H. apply rect11_In. exact Hl.
  Qed.

  (* =======================================================================
     3. Multiplying one link variable by the central element -1
     ======================================================================= *)

  Definition flipU (l : Link4D) (U : SU2Config) : SU2Config :=
    su2_update U l (qneg (U l)).

  Lemma path_flip : forall l U C,
    su2_path (flipU l U) C = qscale ((-1) ^ link4D_count l C) (su2_path U C).
  Proof.
    intros l U C. induction C as [| x C IH].
    - rewrite !path_nil. cbn [link4D_count pow]. symmetry. apply qscale_one.
    - rewrite !path_cons, IH. cbn [link4D_count]. unfold flipU at 1, su2_update.
      destruct (link4D_eqb x l) eqn:He.
      + apply link4D_eqb_spec in He. subst x.
        rewrite qneg_scale, qmul_scale_l, qmul_scale_r, qscale_scale.
        f_equal.
      + rewrite qmul_scale_r. reflexivity.
  Qed.

  Lemma wilson_flip : forall l U s mu nu a b,
    su2_wilson_loop (flipU l U) s mu nu a b =
    (-1) ^ link4D_count l (z2_rect_loop s mu nu a b) * su2_wilson_loop U s mu nu a b.
  Proof.
    intros l U s mu nu a b. unfold su2_wilson_loop, su2_rect_holonomy, z2_rect_loop.
    rewrite !path_flip, !count_app, !pow_add.
    repeat first [ rewrite qconj_scale | rewrite qmul_scale_r
                 | rewrite qmul_scale_l | rewrite qscale_scale ].
    rewrite qr_scale. ring.
  Qed.

  Lemma plaq_flip : forall l U p,
    su2_plaq (flipU l U) p = (-1) ^ link4D_count l (plaq4D_links p) * su2_plaq U p.
  Proof.
    intros l U p. unfold su2_plaq. rewrite wilson_flip, rect11_count. reflexivity.
  Qed.

  Lemma flip_unit_config : forall l U, su2_unit_config U -> su2_unit_config (flipU l U).
  Proof.
    intros l U HU. unfold flipU. apply unit_config_update; [exact HU |].
    apply unit_neg. apply HU.
  Qed.

  (* =======================================================================
     4. The Boltzmann weight and the finite a-priori sums
     ======================================================================= *)

  Lemma boltzmann_rprod : forall beta Lambda U,
    exp (- su2_wilson_action beta Lambda U) =
    rprod Lambda (fun p => exp (beta * su2_plaq U p)).
  Proof.
    intros beta Lambda U. unfold su2_wilson_action.
    induction Lambda as [| p Lambda IH].
    - cbn [map fold_right]. rewrite rprod_nil.
      replace (- (- beta * 0)) with 0 by ring. apply exp_0.
    - cbn [map fold_right]. rewrite rprod_cons, <- IH, <- exp_plus. f_equal. ring.
  Qed.

  Lemma su2_sum_csum : forall G E F U,
    su2_sum G E F U = csum Link4D Quat link4D_eqb G E F U.
  Proof.
    intros G E. induction E as [| l E IH]; intros F U; [reflexivity |].
    cbn [su2_sum csum]. unfold rsum. f_equal. apply map_ext. intro g. apply IH.
  Qed.

  Lemma expect_csum : forall G beta Lambda F,
    su2_expect_on G beta Lambda F =
    csum Link4D Quat link4D_eqb G (z2_links Lambda)
      (fun U => F U * exp (- su2_wilson_action beta Lambda U)) (fun _ => qone)
    / csum Link4D Quat link4D_eqb G (z2_links Lambda)
        (fun U => exp (- su2_wilson_action beta Lambda U)) (fun _ => qone).
  Proof.
    intros G beta Lambda F. unfold su2_expect_on. rewrite !su2_sum_csum. reflexivity.
  Qed.

End SU2Algebra.
