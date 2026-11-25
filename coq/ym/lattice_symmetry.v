(* =========================================================================
   ym/lattice_symmetry.v

   The lattice symmetries of `verification/ChallengeSU2MassGap.v` (the
   translations and the time reflection t -> -t) acting on links, on
   plaquettes, on SU(2) gauge fields and on observables:

     - the translations and the reflection are bijections of the links and
       of the canonical plaquettes, and they map unit configurations to unit
       configurations;
     - covariance of the plaquette variable (1/2) tr U_p and of the Wilson
       action;
     - translated / reflected local observables are local on the translated
       / reflected plaquettes, and stay bounded and uniformly continuous;
     - tau^k Theta tau^k = Theta for the time translation tau;
     - plaquettes at non-negative times, the distance between a reflected
       plaquette and a time-translated one, and the cubes `su2_box`.

   Depends ONLY on Coq stdlib + the frozen challenge files
   + ym.su2_algebra + ym.su2_continuity + ym.lattice_boxes.
   Zero postulates: every statement below is a closed theorem.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
From Coq Require Import Logic.FunctionalExtensionality.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import ym.su2_algebra.
Require Import ym.su2_continuity.
Require Import ym.lattice_boxes.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import ChallengeSU2InfiniteVolume ChallengeSU2MassGap.
Import SU2Algebra.
Open Scope R_scope.

Module LatticeSymmetry.

  (* =======================================================================
     1. Definitions
     ======================================================================= *)

  Definition site_unshift (s : Site4D) (d : Dir4D) : Site4D :=
    match d with
    | D4_t => mkSite4D (s4_t s - 1) (s4_x s) (s4_y s) (s4_z s)
    | D4_x => mkSite4D (s4_t s) (s4_x s - 1) (s4_y s) (s4_z s)
    | D4_y => mkSite4D (s4_t s) (s4_x s) (s4_y s - 1) (s4_z s)
    | D4_z => mkSite4D (s4_t s) (s4_x s) (s4_y s) (s4_z s - 1)
    end.

  Definition link_unshift (d : Dir4D) (l : Link4D) : Link4D :=
    (site_unshift (fst l) d, snd l).

  Definition plaq_shift (d : Dir4D) (p : Plaq4D) : Plaq4D :=
    mkPlaq4D (shift4D (p4_site p) d) (p4_mu p) (p4_nu p).

  Definition plaq_unshift (d : Dir4D) (p : Plaq4D) : Plaq4D :=
    mkPlaq4D (site_unshift (p4_site p) d) (p4_mu p) (p4_nu p).

  (* mirror image of a canonical plaquette: a time-like plaquette (mu = t)
     anchored at time t occupies [t, t+1] and is mapped to the one anchored
     at time - t - 1 *)
  Definition plaq_reflect (p : Plaq4D) : Plaq4D :=
    match p4_mu p with
    | D4_t => mkPlaq4D (mkSite4D (- s4_t (p4_site p) - 1) (s4_x (p4_site p))
                                 (s4_y (p4_site p)) (s4_z (p4_site p))) D4_t (p4_nu p)
    | D4_x => mkPlaq4D (site_reflect (p4_site p)) D4_x (p4_nu p)
    | D4_y => mkPlaq4D (site_reflect (p4_site p)) D4_y (p4_nu p)
    | D4_z => mkPlaq4D (site_reflect (p4_site p)) D4_z (p4_nu p)
    end.

  (* the value map of the reflection on the link l *)
  Definition refl_sigma (l : Link4D) (q : Quat) : Quat :=
    match snd l with D4_t => qconj q | D4_x => q | D4_y => q | D4_z => q end.

  (* =======================================================================
     2. Sites and links
     ======================================================================= *)

  Lemma site_eq : forall t x y z t' x' y' z' : Z,
    t = t' -> x = x' -> y = y' -> z = z' -> mkSite4D t x y z = mkSite4D t' x' y' z'.
  Proof. intros; subst; reflexivity. Qed.

  Lemma link_eq : forall (s s' : Site4D) (d : Dir4D), s = s' -> (s, d) = (s', d).
  Proof. intros; subst; reflexivity. Qed.

  Lemma plaq_eq : forall (s s' : Site4D) (mu nu : Dir4D),
    s = s' -> mkPlaq4D s mu nu = mkPlaq4D s' mu nu.
  Proof. intros; subst; reflexivity. Qed.

  Lemma shift_comm : forall s a b,
    shift4D (shift4D s a) b = shift4D (shift4D s b) a.
  Proof. intros s a b. destruct a, b; reflexivity. Qed.

  Lemma site_unshift_shift : forall s d, site_unshift (shift4D s d) d = s.
  Proof.
    intros [t x y z] d.
    destruct d; cbn [site_unshift shift4D s4_t s4_x s4_y s4_z]; apply site_eq; lia.
  Qed.

  Lemma site_shift_unshift : forall s d, shift4D (site_unshift s d) d = s.
  Proof.
    intros [t x y z] d.
    destruct d; cbn [site_unshift shift4D s4_t s4_x s4_y s4_z]; apply site_eq; lia.
  Qed.

  Lemma unshift_shift_comm : forall s a d,
    site_unshift (shift4D s a) d = shift4D (site_unshift s d) a.
  Proof.
    intros [t x y z] a d.
    destruct a, d; cbn [site_unshift shift4D s4_t s4_x s4_y s4_z]; apply site_eq; lia.
  Qed.

  Lemma site_reflect_invol : forall s, site_reflect (site_reflect s) = s.
  Proof.
    intros [t x y z]. unfold site_reflect. cbn [s4_t s4_x s4_y s4_z].
    apply site_eq; lia.
  Qed.

  Lemma link_unshift_shift : forall d l, link_unshift d (link_shift d l) = l.
  Proof.
    intros d [s e]. unfold link_unshift, link_shift. cbn [fst snd].
    rewrite site_unshift_shift. reflexivity.
  Qed.

  Lemma link_shift_unshift : forall d l, link_shift d (link_unshift d l) = l.
  Proof.
    intros d [s e]. unfold link_unshift, link_shift. cbn [fst snd].
    rewrite site_shift_unshift. reflexivity.
  Qed.

  Lemma link_reflect_invol : forall l, link_reflect (link_reflect l) = l.
  Proof.
    intros [[t x y z] d].
    destruct d; unfold link_reflect, site_reflect;
      cbn [fst snd s4_t s4_x s4_y s4_z]; apply link_eq; apply site_eq; lia.
  Qed.

  Lemma snd_link_reflect : forall l, snd (link_reflect l) = snd l.
  Proof.
    intros [s d]. destruct d; unfold link_reflect; cbn [fst snd]; reflexivity.
  Qed.

  (* =======================================================================
     3. Gauge fields
     ======================================================================= *)

  Lemma qconj_invol : forall q, qconj (qconj q) = q.
  Proof. intro q. apply quat_eq; unfold qconj; cbn [qr qi qj qk]; ring. Qed.

  Lemma su2_reflect_sigma : forall U l,
    su2_reflect U l = refl_sigma l (U (link_reflect l)).
  Proof. intros U l. reflexivity. Qed.

  Lemma refl_sigma_invol : forall l q, refl_sigma l (refl_sigma (link_reflect l) q) = q.
  Proof.
    intros l q. unfold refl_sigma. rewrite snd_link_reflect.
    destruct (snd l); [apply qconj_invol | reflexivity | reflexivity | reflexivity].
  Qed.

  Lemma su2_reflect_invol : forall U, su2_reflect (su2_reflect U) = U.
  Proof.
    intro U. apply functional_extensionality. intro l.
    rewrite (su2_reflect_sigma (su2_reflect U) l), (su2_reflect_sigma U (link_reflect l)).
    rewrite link_reflect_invol. apply refl_sigma_invol.
  Qed.

  Lemma translate_unit : forall d U, su2_unit_config U -> su2_unit_config (su2_translate d U).
  Proof. intros d U HU l. unfold su2_translate. apply HU. Qed.

  Lemma refl_sigma_unit : forall l q, su2_unit q -> su2_unit (refl_sigma l q).
  Proof.
    intros l q Hq. unfold refl_sigma.
    destruct (snd l); [apply unit_conj; exact Hq | exact Hq | exact Hq | exact Hq].
  Qed.

  Lemma reflect_unit : forall U, su2_unit_config U -> su2_unit_config (su2_reflect U).
  Proof.
    intros U HU l. rewrite su2_reflect_sigma. apply refl_sigma_unit. apply HU.
  Qed.

  (* T R T = R for the time translation T and the reflection R *)
  Lemma shift_reflect_shift : forall l,
    link_shift D4_t (link_reflect (link_shift D4_t l)) = link_reflect l.
  Proof.
    intros [[t x y z] d].
    destruct d; unfold link_shift, link_reflect, site_reflect;
      cbn [fst snd shift4D s4_t s4_x s4_y s4_z]; apply link_eq; apply site_eq; lia.
  Qed.

  Lemma translate_reflect_translate_cfg : forall U,
    su2_translate D4_t (su2_reflect (su2_translate D4_t U)) = su2_reflect U.
  Proof.
    intro U. apply functional_extensionality. intro l.
    unfold su2_translate at 1.
    rewrite (su2_reflect_sigma (su2_translate D4_t U) (link_shift D4_t l)).
    unfold su2_translate. rewrite shift_reflect_shift.
    rewrite (su2_reflect_sigma U l). destruct l as [s d]. reflexivity.
  Qed.

  (* =======================================================================
     4. Plaquettes
     ======================================================================= *)

  Ltac wf_cases H :=
    unfold wf_plaq_4D, canonical_planes_4D in H; cbn [In p4_mu p4_nu] in H;
    destruct H as [H | [H | [H | [H | [H | [H | []]]]]]];
    injection H as ? ?; subst.

  Lemma plaq_shift_unshift : forall d p, plaq_shift d (plaq_unshift d p) = p.
  Proof.
    intros d [s mu nu]. unfold plaq_shift, plaq_unshift. cbn [p4_site p4_mu p4_nu].
    rewrite site_shift_unshift. reflexivity.
  Qed.

  Lemma plaq_unshift_shift : forall d p, plaq_unshift d (plaq_shift d p) = p.
  Proof.
    intros d [s mu nu]. unfold plaq_shift, plaq_unshift. cbn [p4_site p4_mu p4_nu].
    rewrite site_unshift_shift. reflexivity.
  Qed.

  Lemma plaq_reflect_invol : forall p, wf_plaq_4D p -> plaq_reflect (plaq_reflect p) = p.
  Proof.
    intros [[t x y z] mu nu] _.
    destruct mu; unfold plaq_reflect, site_reflect;
      cbn [p4_site p4_mu p4_nu s4_t s4_x s4_y s4_z]; apply plaq_eq; apply site_eq; lia.
  Qed.

  Lemma plaq_shift_wf : forall d p, wf_plaq_4D p -> wf_plaq_4D (plaq_shift d p).
  Proof. intros d p H. exact H. Qed.

  Lemma plaq_unshift_wf : forall d p, wf_plaq_4D p -> wf_plaq_4D (plaq_unshift d p).
  Proof. intros d p H. exact H. Qed.

  Lemma plaq_reflect_wf : forall p, wf_plaq_4D p -> wf_plaq_4D (plaq_reflect p).
  Proof.
    intros [s mu nu] H. unfold wf_plaq_4D in *. unfold plaq_reflect.
    cbn [p4_site p4_mu p4_nu] in *. destruct mu; cbn [p4_mu p4_nu]; exact H.
  Qed.

  Lemma links_plaq_shift : forall d p,
    plaq4D_links (plaq_shift d p) = map (link_shift d) (plaq4D_links p).
  Proof.
    intros d [s mu nu]. unfold plaq4D_links, plaq_shift, link_shift.
    cbn [p4_site p4_mu p4_nu map fst snd].
    rewrite (shift_comm s mu d), (shift_comm s nu d). reflexivity.
  Qed.

  Lemma links_plaq_unshift : forall d p,
    plaq4D_links (plaq_unshift d p) = map (link_unshift d) (plaq4D_links p).
  Proof.
    intros d [s mu nu]. unfold plaq4D_links, plaq_unshift, link_unshift.
    cbn [p4_site p4_mu p4_nu map fst snd].
    rewrite (unshift_shift_comm s mu d), (unshift_shift_comm s nu d). reflexivity.
  Qed.

  Lemma in_map_reflect : forall l (M : list Link4D),
    In (link_reflect l) M <-> In l (map link_reflect M).
  Proof.
    intros l M. split; intro H.
    - rewrite <- (link_reflect_invol l). apply in_map. exact H.
    - apply (proj1 (in_map_iff _ _ _)) in H. destruct H as [x [Hx Hin]]. subst l.
      rewrite link_reflect_invol. exact Hin.
  Qed.

  Lemma links_plaq_reflect : forall p l, wf_plaq_4D p ->
    (In l (plaq4D_links (plaq_reflect p)) <-> In (link_reflect l) (plaq4D_links p)).
  Proof.
    intros p l H.
    assert (HH : In l (plaq4D_links (plaq_reflect p)) <->
                 In l (map link_reflect (plaq4D_links p))).
    { destruct p as [[t x y z] mu nu].
      assert (E1 : (- (t + 1))%Z = (- t - 1)%Z) by lia.
      assert (E2 : (- t - 1 + 1)%Z = (- t)%Z) by lia.
      wf_cases H;
        unfold plaq4D_links, plaq_reflect, link_reflect, site_reflect;
        cbn [p4_site p4_mu p4_nu map fst snd shift4D s4_t s4_x s4_y s4_z];
        rewrite ?E1, ?E2; cbn [In]; tauto. }
    pose proof (in_map_reflect l (plaq4D_links p)) as HR. tauto.
  Qed.

  (* =======================================================================
     5. Covariance of the plaquette variable and of the action
     ======================================================================= *)

  Lemma plaq_formula : forall U p,
    su2_plaq U p =
    qr (qmul (U (p4_site p, p4_mu p))
         (qmul (U (shift4D (p4_site p) (p4_mu p), p4_nu p))
           (qmul (qconj (U (shift4D (p4_site p) (p4_nu p), p4_mu p)))
                 (qconj (U (p4_site p, p4_nu p)))))).
  Proof.
    intros U p. unfold su2_plaq, su2_wilson_loop, su2_rect_holonomy, z2_segment.
    cbn [seq map shift4D_n]. rewrite !path_cons, !path_nil, !qmul_one_r. reflexivity.
  Qed.

  Lemma plaq_translate : forall d U p,
    su2_plaq (su2_translate d U) p = su2_plaq U (plaq_shift d p).
  Proof.
    intros d U [s mu nu]. rewrite !plaq_formula.
    unfold su2_translate, link_shift, plaq_shift. cbn [p4_site p4_mu p4_nu fst snd].
    rewrite (shift_comm s mu d), (shift_comm s nu d). reflexivity.
  Qed.

  Lemma plaq_reflect_cov : forall U p, wf_plaq_4D p ->
    su2_plaq (su2_reflect U) p = su2_plaq U (plaq_reflect p).
  Proof.
    intros U [[t x y z] mu nu] H. rewrite !plaq_formula.
    assert (E1 : (- (t + 1))%Z = (- t - 1)%Z) by lia.
    assert (E2 : (- t - 1 + 1)%Z = (- t)%Z) by lia.
    wf_cases H;
      unfold plaq_reflect, su2_reflect, link_reflect, site_reflect;
      cbn [p4_site p4_mu p4_nu fst snd shift4D s4_t s4_x s4_y s4_z];
      rewrite ?E1, ?E2;
      unfold qmul, qconj; cbn [qr qi qj qk]; ring.
  Qed.

  Lemma action_translate : forall beta d Lam U,
    su2_wilson_action beta Lam (su2_translate d U) =
    su2_wilson_action beta (map (plaq_shift d) Lam) U.
  Proof.
    intros beta d Lam U. unfold su2_wilson_action. rewrite map_map.
    apply Rmult_eq_compat_l. apply (f_equal (fold_right Rplus 0)).
    apply map_ext. intro p. apply plaq_translate.
  Qed.

  Lemma action_reflect : forall beta Lam U, Forall wf_plaq_4D Lam ->
    su2_wilson_action beta Lam (su2_reflect U) =
    su2_wilson_action beta (map plaq_reflect Lam) U.
  Proof.
    intros beta Lam U HLam. unfold su2_wilson_action. rewrite map_map.
    apply Rmult_eq_compat_l. apply (f_equal (fold_right Rplus 0)).
    apply map_ext_in. intros p Hp. apply plaq_reflect_cov.
    exact (proj1 (Forall_forall _ _) HLam p Hp).
  Qed.

  (* =======================================================================
     6. Observables
     ======================================================================= *)

  Lemma local_translate : forall d f P, su2_local_on f P ->
    su2_local_on (obs_translate d f) (map (plaq_shift d) P).
  Proof.
    intros d f P Hf U U' H. unfold obs_translate. apply Hf.
    intros p l Hp Hl. unfold su2_translate.
    apply (H (plaq_shift d p) (link_shift d l)).
    - apply in_map. exact Hp.
    - rewrite links_plaq_shift. apply in_map. exact Hl.
  Qed.

  Lemma local_reflect : forall f P, Forall wf_plaq_4D P -> su2_local_on f P ->
    su2_local_on (obs_reflect f) (map plaq_reflect P).
  Proof.
    intros f P HP Hf U U' H. unfold obs_reflect. apply Hf.
    intros p l Hp Hl.
    rewrite (su2_reflect_sigma U l), (su2_reflect_sigma U' l).
    rewrite (H (plaq_reflect p) (link_reflect l)); [reflexivity | |].
    - apply in_map. exact Hp.
    - apply (proj2 (links_plaq_reflect p (link_reflect l)
                      (proj1 (Forall_forall _ _) HP p Hp))).
      rewrite link_reflect_invol. exact Hl.
  Qed.

  Lemma bc_translate : forall d f,
    su2_bounded_continuous f -> su2_bounded_continuous (obs_translate d f).
  Proof.
    intros d f [[M HM] Hc]. split.
    - exists M. intros U HU. unfold obs_translate. apply HM.
      apply translate_unit. exact HU.
    - intros eps Heps. destruct (Hc eps Heps) as (delta & Hdelta & Hcl).
      exists delta. split; [exact Hdelta |]. intros U U' HU HU' Hclose.
      unfold obs_translate.
      apply Hcl; [apply translate_unit; exact HU | apply translate_unit; exact HU' |].
      intro l. unfold su2_translate. apply Hclose.
  Qed.

  Lemma refl_sigma_close : forall delta l q q',
    su2_close delta q q' -> su2_close delta (refl_sigma l q) (refl_sigma l q').
  Proof.
    intros delta l q q' H. unfold refl_sigma.
    destruct (snd l); [apply SU2Continuity.close_conj; exact H | exact H | exact H | exact H].
  Qed.

  Lemma bc_reflect : forall f,
    su2_bounded_continuous f -> su2_bounded_continuous (obs_reflect f).
  Proof.
    intros f [[M HM] Hc]. split.
    - exists M. intros U HU. unfold obs_reflect. apply HM.
      apply reflect_unit. exact HU.
    - intros eps Heps. destruct (Hc eps Heps) as (delta & Hdelta & Hcl).
      exists delta. split; [exact Hdelta |]. intros U U' HU HU' Hclose.
      unfold obs_reflect.
      apply Hcl; [apply reflect_unit; exact HU | apply reflect_unit; exact HU' |].
      intro l. rewrite (su2_reflect_sigma U l), (su2_reflect_sigma U' l).
      apply refl_sigma_close. apply Hclose.
  Qed.

  Lemma obs_reflect_invol : forall f U, obs_reflect (obs_reflect f) U = f U.
  Proof.
    intros f U. unfold obs_reflect. rewrite su2_reflect_invol. reflexivity.
  Qed.

  Lemma local_translate_n : forall d k f P, su2_local_on f P ->
    su2_local_on (obs_translate_n d k f) (map (Nat.iter k (plaq_shift d)) P).
  Proof.
    intros d k f P Hf. induction k as [| k IH].
    - change (map (Nat.iter 0 (plaq_shift d)) P) with (map (fun p : Plaq4D => p) P).
      rewrite map_id. exact Hf.
    - change (map (Nat.iter (S k) (plaq_shift d)) P)
        with (map (fun p => plaq_shift d (Nat.iter k (plaq_shift d) p)) P).
      rewrite <- (map_map (Nat.iter k (plaq_shift d)) (plaq_shift d)).
      change (obs_translate_n d (S k) f) with (obs_translate d (obs_translate_n d k f)).
      apply local_translate. exact IH.
  Qed.

  Lemma bc_translate_n : forall d k f, su2_bounded_continuous f ->
    su2_bounded_continuous (obs_translate_n d k f).
  Proof.
    intros d k f Hf. induction k as [| k IH]; [exact Hf |].
    change (obs_translate_n d (S k) f) with (obs_translate d (obs_translate_n d k f)).
    apply bc_translate. exact IH.
  Qed.

  Lemma obs_translate_n_add : forall d j k f U,
    obs_translate_n d (j + k) f U = obs_translate_n d j (obs_translate_n d k f) U.
  Proof.
    intros d j k f. induction j as [| j IH]; intro U; [reflexivity |].
    change (obs_translate_n d (S j + k) f U)
      with (obs_translate_n d (j + k) f (su2_translate d U)).
    change (obs_translate_n d (S j) (obs_translate_n d k f) U)
      with (obs_translate_n d j (obs_translate_n d k f) (su2_translate d U)).
    apply IH.
  Qed.

  (* tau^(k+1) = tau^k tau *)
  Lemma obs_translate_n_S : forall d k f,
    obs_translate_n d (S k) f = obs_translate_n d k (obs_translate d f).
  Proof.
    intros d k f. induction k as [| k IH]; [reflexivity |].
    change (obs_translate_n d (S (S k)) f) with (obs_translate d (obs_translate_n d (S k) f)).
    rewrite IH. reflexivity.
  Qed.

  (* tau^k Theta tau^k = Theta for the time direction *)
  Lemma translate_reflect_translate : forall k f U,
    obs_translate_n D4_t k (obs_reflect (obs_translate_n D4_t k f)) U = obs_reflect f U.
  Proof.
    induction k as [| k IH]; intros f U; [reflexivity |].
    change (obs_translate_n D4_t (S k) (obs_reflect (obs_translate_n D4_t (S k) f)) U)
      with (obs_translate_n D4_t k (obs_reflect (obs_translate_n D4_t (S k) f))
              (su2_translate D4_t U)).
    rewrite (obs_translate_n_S D4_t k f), IH.
    unfold obs_reflect, obs_translate.
    rewrite translate_reflect_translate_cfg. reflexivity.
  Qed.

  (* =======================================================================
     7. Non-negative times, distances, cubes
     ======================================================================= *)

  Lemma iter_shift_wf : forall d k p,
    wf_plaq_4D p -> wf_plaq_4D (Nat.iter k (plaq_shift d) p).
  Proof.
    intros d k p H. induction k as [| k IH]; [exact H |].
    change (Nat.iter (S k) (plaq_shift d) p)
      with (plaq_shift d (Nat.iter k (plaq_shift d) p)).
    apply plaq_shift_wf. exact IH.
  Qed.

  Lemma iter_shift_time : forall k p,
    s4_t (p4_site (Nat.iter k (plaq_shift D4_t) p)) = (s4_t (p4_site p) + Z.of_nat k)%Z.
  Proof.
    induction k as [| k IH]; intro p.
    - change (Nat.iter 0 (plaq_shift D4_t) p) with p. lia.
    - change (s4_t (p4_site (Nat.iter (S k) (plaq_shift D4_t) p)))
        with (s4_t (p4_site (Nat.iter k (plaq_shift D4_t) p)) + 1)%Z.
      rewrite IH. lia.
  Qed.

  Lemma pos_iter_shift : forall k p,
    pos_time_plaq p -> pos_time_plaq (Nat.iter k (plaq_shift D4_t) p).
  Proof.
    intros k p H. unfold pos_time_plaq in *. rewrite iter_shift_time. lia.
  Qed.

  Lemma reflect_time_nonpos : forall p,
    pos_time_plaq p -> (s4_t (p4_site (plaq_reflect p)) <= 0)%Z.
  Proof.
    intros [[t x y z] mu nu]. unfold pos_time_plaq, plaq_reflect, site_reflect.
    cbn [p4_site p4_mu p4_nu s4_t s4_x s4_y s4_z]. intro H.
    destruct mu; cbn [p4_site s4_t]; lia.
  Qed.

  Lemma dist_reflect_shift : forall p q k,
    wf_plaq_4D p -> pos_time_plaq p -> pos_time_plaq q ->
    INR k / 2 <= plaq4D_dist (plaq_reflect p) (Nat.iter k (plaq_shift D4_t) q).
  Proof.
    intros p q k _ Hp Hq. unfold plaq4D_dist, site4D_manhattan.
    pose proof (reflect_time_nonpos p Hp) as H1.
    pose proof (iter_shift_time k q) as H2. unfold pos_time_plaq in Hq.
    set (s1 := p4_site (plaq_reflect p)) in *.
    set (s2 := p4_site (Nat.iter k (plaq_shift D4_t) q)) in *.
    rewrite INR_IZR_INZ.
    assert (HZ : (Z.of_nat k <= Z.abs (s4_t s1 - s4_t s2) + Z.abs (s4_x s1 - s4_x s2) +
                               Z.abs (s4_y s1 - s4_y s2) + Z.abs (s4_z s1 - s4_z s2))%Z)
      by lia.
    apply IZR_le in HZ. unfold Rdiv. apply Rmult_le_compat_r; [lra | exact HZ].
  Qed.

  Lemma box_shift : forall d m p, In p (su2_box m) -> In (plaq_shift d p) (su2_box (S m)).
  Proof.
    intros d m p H. apply (proj1 (LatticeBoxes.box_In m p)) in H. destruct H as [Hwf Hc].
    apply (proj2 (LatticeBoxes.box_In (S m) (plaq_shift d p))).
    split; [apply plaq_shift_wf; exact Hwf |].
    unfold LatticeBoxes.site_in_cube in *. destruct p as [[t x y z] mu nu].
    unfold plaq_shift. cbn [p4_site s4_t s4_x s4_y s4_z] in *.
    destruct d; cbn [shift4D s4_t s4_x s4_y s4_z]; lia.
  Qed.

  Lemma box_unshift : forall d m p,
    In p (su2_box m) -> In (plaq_unshift d p) (su2_box (S m)).
  Proof.
    intros d m p H. apply (proj1 (LatticeBoxes.box_In m p)) in H. destruct H as [Hwf Hc].
    apply (proj2 (LatticeBoxes.box_In (S m) (plaq_unshift d p))).
    split; [apply plaq_unshift_wf; exact Hwf |].
    unfold LatticeBoxes.site_in_cube in *. destruct p as [[t x y z] mu nu].
    unfold plaq_unshift. cbn [p4_site s4_t s4_x s4_y s4_z] in *.
    destruct d; cbn [site_unshift s4_t s4_x s4_y s4_z]; lia.
  Qed.

  Lemma box_reflect : forall m p, In p (su2_box m) -> In (plaq_reflect p) (su2_box (S m)).
  Proof.
    intros m p H. apply (proj1 (LatticeBoxes.box_In m p)) in H. destruct H as [Hwf Hc].
    apply (proj2 (LatticeBoxes.box_In (S m) (plaq_reflect p))).
    split; [apply plaq_reflect_wf; exact Hwf |].
    unfold LatticeBoxes.site_in_cube in *. destruct p as [[t x y z] mu nu].
    unfold plaq_reflect, site_reflect. cbn [p4_site p4_mu p4_nu s4_t s4_x s4_y s4_z] in *.
    destruct mu; cbn [p4_site s4_t s4_x s4_y s4_z]; lia.
  Qed.

End LatticeSymmetry.
