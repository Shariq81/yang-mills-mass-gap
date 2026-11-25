(* =========================================================================
   ym/su2_continuity.v

   The class `su2_bounded_continuous` of bounded uniformly continuous
   observables of SU(2)-valued configurations (frozen file
   `verification/ChallengeSU2Gauge.v`) contains the observables of lattice
   gauge theory and is closed under the usual operations:

     - the Hamilton product and the conjugation are Lipschitz on the unit
       quaternions for the componentwise sup-distance `su2_close`, hence so
       are path-ordered products and rectangle holonomies;
     - Wilson loops and plaquette variables are bounded uniformly
       continuous;
     - constants, sums, products, finite sums and exponentials of bounded
       uniformly continuous observables are bounded uniformly continuous;
     - hence the Boltzmann weight exp (- S(U)) of the Wilson action is
       bounded uniformly continuous.

   Depends ONLY on Coq stdlib + the frozen challenge files
   + rg.dup_clustering + ym.su2_algebra.
   Every lemma below is closed with Qed; the file declares no assumptions.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import rg.dup_clustering.
Require Import ym.su2_algebra.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import DupClustering SU2Algebra.
Open Scope R_scope.

Module SU2Continuity.

  (* =======================================================================
     1. The componentwise sup-distance `su2_close`
     ======================================================================= *)

  Lemma close_refl : forall d q, 0 < d -> su2_close d q q.
  Proof.
    intros d q Hd.
    assert (E : forall x : R, Rabs (x - x) < d).
    { intro x. replace (x - x) with 0 by ring. rewrite Rabs_R0. exact Hd. }
    unfold su2_close. repeat split; apply E.
  Qed.

  Lemma close_mono : forall d d' p q,
    d <= d' -> su2_close d p q -> su2_close d' p q.
  Proof.
    intros d d' p q Hd (H1 & H2 & H3 & H4). unfold su2_close.
    repeat split; lra.
  Qed.

  Lemma close_conj : forall d p p',
    su2_close d p p' -> su2_close d (qconj p) (qconj p').
  Proof.
    intros d p p' (H1 & H2 & H3 & H4).
    assert (E : forall x y : R, Rabs (- x - - y) = Rabs (x - y)).
    { intros x y. replace (- x - - y) with (- (x - y)) by ring. apply Rabs_Ropp. }
    unfold su2_close, qconj. cbn [qr qi qj qk]. rewrite !E.
    repeat split; assumption.
  Qed.

  (* |a b - a' b'| <= |a| |b - b'| + |b'| |a - a'| *)
  Lemma abs_prod_close : forall a a' b b' d : R,
    Rabs a <= 1 -> Rabs b' <= 1 ->
    Rabs (a - a') < d -> Rabs (b - b') < d ->
    Rabs (a * b - a' * b') < 2 * d.
  Proof.
    intros a a' b b' d Ha Hb' Haa Hbb.
    replace (a * b - a' * b') with (a * (b - b') + b' * (a - a')) by ring.
    eapply Rle_lt_trans; [apply Rabs_triang |].
    rewrite !Rabs_mult.
    assert (H1 : Rabs a * Rabs (b - b') <= 1 * Rabs (b - b')).
    { apply Rmult_le_compat_r; [apply Rabs_pos | exact Ha]. }
    assert (H2 : Rabs b' * Rabs (a - a') <= 1 * Rabs (a - a')).
    { apply Rmult_le_compat_r; [apply Rabs_pos | exact Hb']. }
    lra.
  Qed.

  (* The Hamilton product is Lipschitz on the unit quaternions: every
     component of a product is a signed sum of 4 products of components. *)
  Lemma close_mul : forall d p p' q q',
    su2_unit p -> su2_unit q' ->
    su2_close d p p' -> su2_close d q q' ->
    su2_close (8 * d) (qmul p q) (qmul p' q').
  Proof.
    intros d p p' q q' Hp Hq' (Hp1 & Hp2 & Hp3 & Hp4) (Hq1 & Hq2 & Hq3 & Hq4).
    destruct (unit_components p Hp) as (Hpr & Hpi & Hpj & Hpk).
    destruct (unit_components q' Hq') as (Hqr & Hqi & Hqj & Hqk).
    assert (P : forall a a' b b' : R,
              -1 <= a <= 1 -> -1 <= b' <= 1 ->
              Rabs (a - a') < d -> Rabs (b - b') < d ->
              a * b - a' * b' < 2 * d /\ - (2 * d) < a * b - a' * b').
    { intros a a' b b' Ha Hb' Haa Hbb. apply Rabs_def2.
      apply abs_prod_close;
        [apply Rabs_le; lra | apply Rabs_le; lra | exact Haa | exact Hbb]. }
    pose proof (P _ _ _ _ Hpr Hqr Hp1 Hq1) as Hrr.
    pose proof (P _ _ _ _ Hpr Hqi Hp1 Hq2) as Hri.
    pose proof (P _ _ _ _ Hpr Hqj Hp1 Hq3) as Hrj.
    pose proof (P _ _ _ _ Hpr Hqk Hp1 Hq4) as Hrk.
    pose proof (P _ _ _ _ Hpi Hqr Hp2 Hq1) as Hir.
    pose proof (P _ _ _ _ Hpi Hqi Hp2 Hq2) as Hii.
    pose proof (P _ _ _ _ Hpi Hqj Hp2 Hq3) as Hij.
    pose proof (P _ _ _ _ Hpi Hqk Hp2 Hq4) as Hik.
    pose proof (P _ _ _ _ Hpj Hqr Hp3 Hq1) as Hjr.
    pose proof (P _ _ _ _ Hpj Hqi Hp3 Hq2) as Hji.
    pose proof (P _ _ _ _ Hpj Hqj Hp3 Hq3) as Hjj.
    pose proof (P _ _ _ _ Hpj Hqk Hp3 Hq4) as Hjk.
    pose proof (P _ _ _ _ Hpk Hqr Hp4 Hq1) as Hkr.
    pose proof (P _ _ _ _ Hpk Hqi Hp4 Hq2) as Hki.
    pose proof (P _ _ _ _ Hpk Hqj Hp4 Hq3) as Hkj.
    pose proof (P _ _ _ _ Hpk Hqk Hp4 Hq4) as Hkk.
    unfold su2_close, qmul. cbn [qr qi qj qk].
    repeat split; apply Rabs_def1; lra.
  Qed.

  (* =======================================================================
     2. Path-ordered products and rectangle holonomies
     ======================================================================= *)

  Lemma close_path : forall d U U' C,
    0 < d -> su2_unit_config U -> su2_unit_config U' ->
    (forall l, su2_close d (U l) (U' l)) ->
    su2_close (8 ^ length C * d) (su2_path U C) (su2_path U' C).
  Proof.
    intros d U U' C Hd HU HU' Hcl. induction C as [| l C IH].
    - rewrite !path_nil. apply close_refl. cbn [length pow]. lra.
    - rewrite !path_cons. cbn [length pow].
      replace (8 * 8 ^ length C * d) with (8 * (8 ^ length C * d)) by ring.
      apply close_mul.
      + apply HU.
      + apply path_unit. exact HU'.
      + apply close_mono with (d := d); [| apply Hcl].
        assert (H1 : 1 <= 8 ^ length C) by (apply pow_R1_Rle; lra).
        rewrite <- (Rmult_1_l d) at 1. apply Rmult_le_compat_r; lra.
      + exact IH.
  Qed.

  Lemma segment_length : forall s d k, length (z2_segment s d k) = k.
  Proof.
    intros s d k. unfold z2_segment. rewrite map_length, seq_length. reflexivity.
  Qed.

  Lemma close_rect : forall d U U' s mu nu a b,
    0 < d -> su2_unit_config U -> su2_unit_config U' ->
    (forall l, su2_close d (U l) (U' l)) ->
    su2_close (512 * 8 ^ (a + b) * d)
      (su2_rect_holonomy U s mu nu a b) (su2_rect_holonomy U' s mu nu a b).
  Proof.
    intros d U U' s mu nu a b Hd HU HU' Hcl.
    set (e := 8 ^ (a + b) * d).
    assert (He : 0 < e).
    { unfold e. apply Rmult_lt_0_compat; [apply pow_lt; lra | exact Hd]. }
    assert (Hseg : forall s' dir k, (k <= a + b)%nat ->
              su2_close e (su2_path U (z2_segment s' dir k))
                          (su2_path U' (z2_segment s' dir k))).
    { intros s' dir k Hk.
      apply close_mono with (d := 8 ^ length (z2_segment s' dir k) * d).
      - rewrite segment_length. unfold e.
        apply Rmult_le_compat_r; [lra | apply Rle_pow; [lra | exact Hk]].
      - apply close_path; assumption. }
    assert (Ha : (a <= a + b)%nat) by lia.
    assert (Hb : (b <= a + b)%nat) by lia.
    unfold su2_rect_holonomy.
    replace (512 * 8 ^ (a + b) * d) with (8 * (8 * (8 * e))) by (unfold e; ring).
    apply close_mul.
    - apply path_unit. exact HU.
    - repeat first [apply unit_mul | apply unit_conj | apply path_unit; exact HU'].
    - apply close_mono with (d := e); [lra | apply Hseg; exact Ha].
    - apply close_mul.
      + apply path_unit. exact HU.
      + repeat first [apply unit_mul | apply unit_conj | apply path_unit; exact HU'].
      + apply close_mono with (d := e); [lra | apply Hseg; exact Hb].
      + apply close_mul.
        * apply unit_conj, path_unit. exact HU.
        * apply unit_conj, path_unit. exact HU'.
        * apply close_conj, Hseg. exact Ha.
        * apply close_conj, Hseg. exact Hb.
  Qed.

  (* Wilson loops are Lipschitz for the sup-distance over the links. *)
  Lemma wilson_lipschitz : forall d U U' s mu nu a b,
    0 < d -> su2_unit_config U -> su2_unit_config U' ->
    (forall l, su2_close d (U l) (U' l)) ->
    Rabs (su2_wilson_loop U s mu nu a b - su2_wilson_loop U' s mu nu a b)
    < 512 * 8 ^ (a + b) * d.
  Proof.
    intros d U U' s mu nu a b Hd HU HU' Hcl. unfold su2_wilson_loop.
    exact (proj1 (close_rect d U U' s mu nu a b Hd HU HU' Hcl)).
  Qed.

  (* =======================================================================
     3. Closure properties of `su2_bounded_continuous`
     ======================================================================= *)

  Lemma bc_ext : forall F G : SU2Config -> R,
    (forall U, F U = G U) ->
    su2_bounded_continuous F -> su2_bounded_continuous G.
  Proof.
    intros F G Hext [[M HM] Hc]. split.
    - exists M. intros U HU. rewrite <- Hext. apply HM. exact HU.
    - intros eps Heps. destruct (Hc eps Heps) as (delta & Hdelta & Hcl).
      exists delta. split; [exact Hdelta |].
      intros U U' HU HU' Hclose. rewrite <- !Hext. apply Hcl; assumption.
  Qed.

  Lemma bc_const : forall c : R, su2_bounded_continuous (fun _ => c).
  Proof.
    intro c. split.
    - exists (Rabs c). intros U _. apply Rle_refl.
    - intros eps Heps. exists 1. split; [lra |].
      intros U U' _ _ _. replace (c - c) with 0 by ring.
      rewrite Rabs_R0. exact Heps.
  Qed.

  Lemma bc_plus : forall F G : SU2Config -> R,
    su2_bounded_continuous F -> su2_bounded_continuous G ->
    su2_bounded_continuous (fun U => F U + G U).
  Proof.
    intros F G [[MF HMF] HcF] [[MG HMG] HcG]. split.
    - exists (MF + MG). intros U HU.
      eapply Rle_trans; [apply Rabs_triang |].
      apply Rplus_le_compat; [apply HMF | apply HMG]; exact HU.
    - intros eps Heps.
      assert (He : 0 < eps / 2) by lra.
      destruct (HcF _ He) as (dF & HdF & HclF).
      destruct (HcG _ He) as (dG & HdG & HclG).
      exists (Rmin dF dG). split; [apply Rmin_glb_lt; assumption |].
      intros U U' HU HU' Hclose.
      assert (HF : Rabs (F U - F U') < eps / 2).
      { apply HclF; try assumption. intro l.
        apply close_mono with (d := Rmin dF dG); [apply Rmin_l | apply Hclose]. }
      assert (HG : Rabs (G U - G U') < eps / 2).
      { apply HclG; try assumption. intro l.
        apply close_mono with (d := Rmin dF dG); [apply Rmin_r | apply Hclose]. }
      replace (F U + G U - (F U' + G U'))
        with ((F U - F U') + (G U - G U')) by ring.
      eapply Rle_lt_trans; [apply Rabs_triang |]. lra.
  Qed.

  Lemma bc_mult : forall F G : SU2Config -> R,
    su2_bounded_continuous F -> su2_bounded_continuous G ->
    su2_bounded_continuous (fun U => F U * G U).
  Proof.
    intros F G [[MF HMF] HcF] [[MG HMG] HcG]. split.
    - exists (MF * MG). intros U HU. rewrite Rabs_mult.
      apply Rmult_le_compat;
        [apply Rabs_pos | apply Rabs_pos | apply HMF; exact HU | apply HMG; exact HU].
    - intros eps Heps.
      set (M := Rmax 1 (Rmax MF MG)).
      assert (HM1 : 1 <= M) by (unfold M; apply Rmax_l).
      assert (HMF' : MF <= M).
      { unfold M. eapply Rle_trans; [apply Rmax_l | apply Rmax_r]. }
      assert (HMG' : MG <= M).
      { unfold M. eapply Rle_trans; [apply Rmax_r | apply Rmax_r]. }
      assert (He : 0 < eps / (2 * M)) by (apply Rdiv_lt_0_compat; lra).
      destruct (HcF _ He) as (dF & HdF & HclF).
      destruct (HcG _ He) as (dG & HdG & HclG).
      exists (Rmin dF dG). split; [apply Rmin_glb_lt; assumption |].
      intros U U' HU HU' Hclose.
      assert (HF : Rabs (F U - F U') < eps / (2 * M)).
      { apply HclF; try assumption. intro l.
        apply close_mono with (d := Rmin dF dG); [apply Rmin_l | apply Hclose]. }
      assert (HG : Rabs (G U - G U') < eps / (2 * M)).
      { apply HclG; try assumption. intro l.
        apply close_mono with (d := Rmin dF dG); [apply Rmin_r | apply Hclose]. }
      replace (F U * G U - F U' * G U')
        with (F U * (G U - G U') + G U' * (F U - F U')) by ring.
      eapply Rle_lt_trans; [apply Rabs_triang |].
      rewrite !Rabs_mult.
      pose proof (HMF U HU) as HFU. pose proof (HMG U' HU') as HGU'.
      assert (H1 : Rabs (F U) * Rabs (G U - G U') <= M * Rabs (G U - G U')).
      { apply Rmult_le_compat_r; [apply Rabs_pos | lra]. }
      assert (H2 : Rabs (G U') * Rabs (F U - F U') <= M * Rabs (F U - F U')).
      { apply Rmult_le_compat_r; [apply Rabs_pos | lra]. }
      assert (H3 : M * Rabs (G U - G U') < M * (eps / (2 * M))).
      { apply Rmult_lt_compat_l; [lra | exact HG]. }
      assert (H4 : M * Rabs (F U - F U') < M * (eps / (2 * M))).
      { apply Rmult_lt_compat_l; [lra | exact HF]. }
      replace (M * (eps / (2 * M))) with (eps / 2) in H3, H4 by (field; lra).
      lra.
  Qed.

  Lemma bc_scal : forall (c : R) (F : SU2Config -> R),
    su2_bounded_continuous F -> su2_bounded_continuous (fun U => c * F U).
  Proof.
    intros c F HF. exact (bc_mult (fun _ => c) F (bc_const c) HF).
  Qed.

  Lemma bc_opp : forall F : SU2Config -> R,
    su2_bounded_continuous F -> su2_bounded_continuous (fun U => - F U).
  Proof.
    intros F HF. apply bc_ext with (F := fun U => -1 * F U).
    - intro U. ring.
    - apply bc_scal. exact HF.
  Qed.

  Lemma bc_minus : forall F G : SU2Config -> R,
    su2_bounded_continuous F -> su2_bounded_continuous G ->
    su2_bounded_continuous (fun U => F U - G U).
  Proof.
    intros F G HF HG.
    exact (bc_plus F (fun U => - G U) HF (bc_opp G HG)).
  Qed.

  (* finite sums, in the `fold_right Rplus 0 (map _ _)` form of the frozen
     files and in the `rsum` form of `rg/dup_clustering.v` *)
  Lemma bc_fold_sum : forall (A : Type) (f : A -> SU2Config -> R) (l : list A),
    (forall x, In x l -> su2_bounded_continuous (f x)) ->
    su2_bounded_continuous (fun U => fold_right Rplus 0 (map (fun x => f x U) l)).
  Proof.
    intros A f l. induction l as [| a l IH]; intro H.
    - exact (bc_const 0).
    - exact (bc_plus (f a) (fun U => fold_right Rplus 0 (map (fun x => f x U) l))
               (H a (or_introl eq_refl)) (IH (fun x Hx => H x (or_intror Hx)))).
  Qed.

  Lemma bc_rsum : forall (A : Type) (f : A -> SU2Config -> R) (l : list A),
    (forall x, In x l -> su2_bounded_continuous (f x)) ->
    su2_bounded_continuous (fun U => rsum l (fun x => f x U)).
  Proof. intros A f l H. exact (bc_fold_sum A f l H). Qed.

  Lemma bc_rprod : forall (A : Type) (f : A -> SU2Config -> R) (l : list A),
    (forall x, In x l -> su2_bounded_continuous (f x)) ->
    su2_bounded_continuous (fun U => rprod l (fun x => f x U)).
  Proof.
    intros A f l. induction l as [| a l IH]; intro H.
    - exact (bc_const 1).
    - exact (bc_mult (f a) (fun U => rprod l (fun x => f x U))
               (H a (or_introl eq_refl)) (IH (fun x Hx => H x (or_intror Hx)))).
  Qed.

  (* =======================================================================
     4. Composition with the exponential
     ======================================================================= *)

  Lemma exp_le_mono : forall x y : R, x <= y -> exp x <= exp y.
  Proof.
    intros x y [H | H].
    - left. apply exp_increasing. exact H.
    - right. rewrite H. reflexivity.
  Qed.

  (* |exp h - 1| <= 2 |h| for |h| <= 1/2, from 1 + x <= exp x at x = h and
     at x = - h *)
  Lemma exp_minus_one_bound : forall h : R,
    Rabs h <= 1 / 2 -> Rabs (exp h - 1) <= 2 * Rabs h.
  Proof.
    intros h Hh.
    pose proof (exp_ineq1_le h) as H1.
    pose proof (exp_ineq1_le (- h)) as H2.
    pose proof (exp_pos h) as Hp.
    assert (H3 : exp h * exp (- h) = 1).
    { rewrite <- exp_plus. replace (h + - h) with 0 by ring. apply exp_0. }
    assert (Hh' : - (1 / 2) <= h <= 1 / 2).
    { revert Hh. unfold Rabs. destruct (Rcase_abs h); lra. }
    assert (H4 : exp h * (1 - h) <= 1).
    { rewrite <- H3. apply Rmult_le_compat_l; lra. }
    assert (H5 : exp h <= 2) by nra.
    unfold Rabs. destruct (Rcase_abs h); destruct (Rcase_abs (exp h - 1)); nra.
  Qed.

  Lemma bc_exp : forall F : SU2Config -> R,
    su2_bounded_continuous F -> su2_bounded_continuous (fun U => exp (F U)).
  Proof.
    intros F [[M HM] Hc]. split.
    - exists (exp M). intros U HU.
      rewrite Rabs_pos_eq by (left; apply exp_pos).
      apply exp_le_mono. eapply Rle_trans; [apply Rle_abs | apply HM; exact HU].
    - intros eps Heps.
      pose proof (exp_pos M) as HeM.
      set (eta := Rmin (1 / 2) (eps / (2 * exp M))).
      assert (Heta : 0 < eta).
      { unfold eta. apply Rmin_glb_lt; [lra | apply Rdiv_lt_0_compat; lra]. }
      destruct (Hc eta Heta) as (delta & Hdelta & Hcl).
      exists delta. split; [exact Hdelta |].
      intros U U' HU HU' Hclose.
      pose proof (Hcl U U' HU HU' Hclose) as Hh.
      assert (Hh1 : Rabs (F U - F U') <= 1 / 2).
      { left. eapply Rlt_le_trans; [exact Hh | apply Rmin_l]. }
      assert (Hh2 : Rabs (F U - F U') < eps / (2 * exp M)).
      { eapply Rlt_le_trans; [exact Hh | apply Rmin_r]. }
      replace (exp (F U) - exp (F U'))
        with (exp (F U') * (exp (F U - F U') - 1)).
      2:{ rewrite Rmult_minus_distr_l, <- exp_plus, Rmult_1_r.
          replace (F U' + (F U - F U')) with (F U) by ring. reflexivity. }
      rewrite Rabs_mult, (Rabs_pos_eq (exp (F U'))) by (left; apply exp_pos).
      assert (Hy : exp (F U') <= exp M).
      { apply exp_le_mono.
        eapply Rle_trans; [apply Rle_abs | apply HM; exact HU']. }
      pose proof (exp_minus_one_bound (F U - F U') Hh1) as Hb.
      pose proof (exp_pos (F U')) as Hpos.
      assert (H1 : exp (F U') * Rabs (exp (F U - F U') - 1)
                   <= exp M * (2 * Rabs (F U - F U'))).
      { apply Rmult_le_compat; [lra | apply Rabs_pos | exact Hy | exact Hb]. }
      assert (H2 : exp M * (2 * Rabs (F U - F U'))
                   < exp M * (2 * (eps / (2 * exp M)))).
      { apply Rmult_lt_compat_l; [exact HeM | lra]. }
      replace (exp M * (2 * (eps / (2 * exp M)))) with eps in H2 by (field; lra).
      lra.
  Qed.

  (* =======================================================================
     5. Wilson loops, plaquettes, the Wilson action, the Boltzmann weight
     ======================================================================= *)

  Lemma bc_wilson_loop : forall (s : Site4D) (mu nu : Dir4D) (a b : nat),
    su2_bounded_continuous (fun U => su2_wilson_loop U s mu nu a b).
  Proof.
    intros s mu nu a b. split.
    - exists 1. intros U HU. apply Rabs_le.
      pose proof (wilson_bound U s mu nu a b HU). lra.
    - intros eps Heps.
      set (K := 512 * 8 ^ (a + b)).
      assert (HK : 0 < K).
      { unfold K. apply Rmult_lt_0_compat; [lra | apply pow_lt; lra]. }
      exists (eps / K). split; [apply Rdiv_lt_0_compat; assumption |].
      intros U U' HU HU' Hclose.
      pose proof (wilson_lipschitz (eps / K) U U' s mu nu a b
                    (Rdiv_lt_0_compat _ _ Heps HK) HU HU' Hclose) as H.
      fold K in H. replace (K * (eps / K)) with eps in H by (field; lra).
      exact H.
  Qed.

  Lemma bc_plaq : forall p : Plaq4D, su2_bounded_continuous (fun U => su2_plaq U p).
  Proof.
    intro p. exact (bc_wilson_loop (p4_site p) (p4_mu p) (p4_nu p) 1%nat 1%nat).
  Qed.

  (* - S(U) = beta * sum_{p in Lambda} (1/2) tr U_p *)
  Lemma bc_neg_action : forall (beta : R) (Lambda : list Plaq4D),
    su2_bounded_continuous (fun U => - su2_wilson_action beta Lambda U).
  Proof.
    intros beta Lambda.
    apply bc_ext
      with (F := fun U => beta * fold_right Rplus 0 (map (su2_plaq U) Lambda)).
    - intro U. unfold su2_wilson_action. ring.
    - apply (bc_scal beta
               (fun U => fold_right Rplus 0 (map (su2_plaq U) Lambda))).
      apply (bc_fold_sum Plaq4D (fun p U => su2_plaq U p) Lambda).
      intros p _. apply bc_plaq.
  Qed.

  Lemma bc_action : forall (beta : R) (Lambda : list Plaq4D),
    su2_bounded_continuous (fun U => su2_wilson_action beta Lambda U).
  Proof.
    intros beta Lambda.
    apply bc_ext with (F := fun U => - - su2_wilson_action beta Lambda U).
    - intro U. ring.
    - apply (bc_opp (fun U => - su2_wilson_action beta Lambda U)).
      apply bc_neg_action.
  Qed.

  Lemma bc_boltzmann : forall (beta : R) (Lambda : list Plaq4D),
    su2_bounded_continuous (fun U => exp (- su2_wilson_action beta Lambda U)).
  Proof.
    intros beta Lambda.
    exact (bc_exp (fun U => - su2_wilson_action beta Lambda U)
             (bc_neg_action beta Lambda)).
  Qed.

End SU2Continuity.
