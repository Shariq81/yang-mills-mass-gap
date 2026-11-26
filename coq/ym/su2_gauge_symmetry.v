(* =========================================================================
   ym/su2_gauge_symmetry.v

   TARGET 15: the action of the gauge group on the Osterwalder-Schrader
   Hilbert space of the 4D SU(2) Wilson lattice gauge theory at strong
   coupling.

   The lattice input is the gauge invariance of the infinite-volume Gibbs
   state (Target 11c) and one identity: for gauge transformations g, h that
   coincide on the hyperplane t = 0 and observables f1, f2 at non-negative
   times,
       Theta (f1 o g) * (f2 o h)  =  ((Theta f1) * f2) o k ,
   where k = h at times >= 0 and k = g o (site reflection) at times < 0.
   Hence  (f1 o g, f2 o h) = (f1, f2)  for the Osterwalder-Schrader form.
   The rest is the abstract extension of form-preserving maps from a dense
   family (`rg/hilbert_isometry.v`), applied to the Hilbert space of
   Targets 13 and 14, of which only the frozen statement is used.

   ZERO `Axiom`, `Parameter`, `Admitted`.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz.
From Coq Require Import Logic.FunctionalExtensionality.
From Coq Require Import Classical_Prop ClassicalEpsilon.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import verification.ChallengeSU2GaugeInvariance.
Require Import verification.ChallengeSU2HilbertSpace.
Require Import verification.ChallengeSU2TransferSpectrum.
Require Import verification.ChallengeSU2GaugeSymmetry.
Require Import rg.hilbert_completion.
Require Import rg.hilbert_resolvent.
Require Import rg.hilbert_isometry.
Require Import ym.su2_algebra.
Require Import ym.lattice_symmetry.
Require Import ym.su2_uniqueness.
Require Import ym.su2_reflection_positivity.
Require Import ym.su2_mass_gap.
Require Import ym.su2_gauge_invariance.
Require Import ym.su2_os_hilbert_space.
Require Import ym.su2_transfer_spectrum.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import ChallengeSU2InfiniteVolume ChallengeSU2MassGap ChallengeSU2GaugeInvariance.
Import ChallengeSU2HilbertSpace ChallengeSU2TransferSpectrum ChallengeSU2GaugeSymmetry.
Import HilbertCompletion HilbertResolvent HilbertIsometry.

Open Scope R_scope.

Module SU2GaugeSymmetry.

  (* =======================================================================
     1. Algebra of gauge transformations
     ======================================================================= *)

  Lemma shift_time : forall s d, (s4_t s <= s4_t (shift4D s d))%Z.
  Proof. intros [t x y z] d. destruct d; cbn [shift4D s4_t]; lia. Qed.

  Lemma gauge_agree : forall (k1 k2 : Site4D -> Quat) (U : SU2Config) (l : Link4D),
    k1 (fst l) = k2 (fst l) ->
    k1 (shift4D (fst l) (snd l)) = k2 (shift4D (fst l) (snd l)) ->
    su2_gauge k1 U l = su2_gauge k2 U l.
  Proof. intros k1 k2 U l H1 H2. unfold su2_gauge. rewrite H1, H2. reflexivity. Qed.

  (* an observable at non-negative times sees a gauge transformation only
     through its values at the sites of non-negative time *)
  Lemma gauge_pos_agree : forall (f : SU2Config -> R) (P : list Plaq4D)
      (k1 k2 : Site4D -> Quat),
    su2_local_on f P -> Forall pos_time_plaq P ->
    (forall s, (0 <= s4_t s)%Z -> k1 s = k2 s) ->
    forall U, f (su2_gauge k1 U) = f (su2_gauge k2 U).
  Proof.
    intros f P k1 k2 Hloc Hpos Hk U. apply Hloc. intros p l Hp Hl.
    pose proof (proj1 (Forall_forall pos_time_plaq P) Hpos p Hp) as Hpp.
    pose proof (SU2ReflectionPositivity.pos_links p l Hpp Hl) as Ht.
    unfold SU2ReflectionPositivity.link_time in Ht.
    pose proof (shift_time (fst l) (snd l)) as Hs.
    apply gauge_agree; apply Hk; lia.
  Qed.

  Lemma local_gauge : forall (g : Site4D -> Quat) (f : SU2Config -> R) (P : list Plaq4D),
    su2_local_on f P -> su2_local_on (obs_gauge g f) P.
  Proof.
    intros g f P Hloc U U' H. unfold obs_gauge. apply Hloc. intros p l Hp Hl.
    unfold su2_gauge. rewrite (H p l Hp Hl). reflexivity.
  Qed.

  Lemma pos_gauge : forall (g : Site4D -> Quat) (f : SU2Config -> R),
    su2_gauge_fn g -> su2_pos_time_observable f ->
    su2_pos_time_observable (obs_gauge g f).
  Proof.
    intros g f Hg [P [HP [Hpos [Hloc Hbc]]]]. exists P.
    split; [exact HP |]. split; [exact Hpos |].
    split; [exact (local_gauge g f P Hloc) |].
    exact (SU2GaugeInvariance.bc_gauge g f Hg Hbc).
  Qed.

  (* reflection intertwines the gauge transformation k with k o reflection *)
  Lemma reflect_gauge : forall (k : Site4D -> Quat) (U : SU2Config),
    su2_reflect (su2_gauge k U)
    = su2_gauge (fun s => k (site_reflect s)) (su2_reflect U).
  Proof.
    intros k U. apply functional_extensionality. intros [[t x y z] d].
    destruct d; unfold su2_reflect, su2_gauge, link_reflect, site_reflect;
      cbn [fst snd s4_t s4_x s4_y s4_z shift4D]; [| reflexivity | reflexivity | reflexivity].
    replace (- t - 1 + 1)%Z with (- t)%Z by lia.
    replace (- (t + 1))%Z with (- t - 1)%Z by lia.
    rewrite !SU2GaugeInvariance.qconj_mul, LatticeSymmetry.qconj_invol,
      SU2Algebra.qmul_assoc.
    reflexivity.
  Qed.

  Lemma gauge_comp : forall (g h : Site4D -> Quat) (U : SU2Config),
    su2_gauge g (su2_gauge h U) = su2_gauge (fun s => qmul (g s) (h s)) U.
  Proof.
    intros g h U. apply functional_extensionality. intro l. unfold su2_gauge.
    apply SU2Algebra.quat_eq; unfold qmul, qconj; cbn [qr qi qj qk]; ring.
  Qed.

  Lemma gauge_one : forall U : SU2Config, su2_gauge (fun _ => qone) U = U.
  Proof.
    intro U. apply functional_extensionality. intro l. unfold su2_gauge.
    apply SU2Algebra.quat_eq; unfold qmul, qconj, qone; cbn [qr qi qj qk]; ring.
  Qed.

  Lemma gauge_translate : forall (g : Site4D -> Quat) (U : SU2Config),
    (forall s, g (shift4D s D4_t) = g s) ->
    su2_translate D4_t (su2_gauge g U) = su2_gauge g (su2_translate D4_t U).
  Proof.
    intros g U Hg. apply functional_extensionality. intro l.
    unfold su2_translate, su2_gauge, link_shift. cbn [fst snd].
    rewrite (LatticeSymmetry.shift_comm (fst l) D4_t (snd l)), !Hg. reflexivity.
  Qed.

  Lemma obs_gauge_one : forall f : SU2Config -> R, obs_gauge (fun _ => qone) f = f.
  Proof.
    intro f. unfold obs_gauge. apply functional_extensionality. intro U.
    rewrite gauge_one. reflexivity.
  Qed.

  Lemma obs_gauge_comp : forall (g h : Site4D -> Quat) (f : SU2Config -> R),
    obs_gauge h (obs_gauge g f) = obs_gauge (fun s => qmul (g s) (h s)) f.
  Proof.
    intros g h f. unfold obs_gauge. apply functional_extensionality. intro U.
    rewrite gauge_comp. reflexivity.
  Qed.

  Lemma obs_gauge_translate : forall (g : Site4D -> Quat) (f : SU2Config -> R),
    (forall s, g (shift4D s D4_t) = g s) ->
    obs_gauge g (obs_translate_n D4_t 1 f) = obs_translate_n D4_t 1 (obs_gauge g f).
  Proof.
    intros g f Hg. apply functional_extensionality. intro U.
    cbn [obs_translate_n]. unfold obs_translate, obs_gauge.
    rewrite (gauge_translate g U Hg). reflexivity.
  Qed.

  Lemma gauge_fn_one : su2_gauge_fn (fun _ => qone).
  Proof. intro x. exact SU2Algebra.unit_one. Qed.

  Lemma gauge_fn_mul : forall g h : Site4D -> Quat,
    su2_gauge_fn g -> su2_gauge_fn h -> su2_gauge_fn (fun s => qmul (g s) (h s)).
  Proof. intros g h Hg Hh x. apply SU2Algebra.unit_mul; [apply Hg | apply Hh]. Qed.

  (* =======================================================================
     2. Gluing two gauge transformations along the hyperplane t = 0
     ======================================================================= *)

  (* h at times >= 0, the reflection of g at times < 0 *)
  Definition glue (g h : Site4D -> Quat) : Site4D -> Quat :=
    fun s => if (0 <=? s4_t s)%Z then h s else g (site_reflect s).

  Lemma glue_fn : forall g h, su2_gauge_fn g -> su2_gauge_fn h -> su2_gauge_fn (glue g h).
  Proof.
    intros g h Hg Hh s. unfold glue. destruct (0 <=? s4_t s)%Z; [apply Hh | apply Hg].
  Qed.

  Lemma glue_pos : forall g h s, (0 <= s4_t s)%Z -> glue g h s = h s.
  Proof.
    intros g h s Hs. unfold glue.
    destruct (Z.leb_spec 0 (s4_t s)) as [_ | Hlt]; [reflexivity | lia].
  Qed.

  Lemma glue_refl : forall g h,
    (forall s, s4_t s = 0%Z -> g s = h s) ->
    forall s, (0 <= s4_t s)%Z -> glue g h (site_reflect s) = g s.
  Proof.
    intros g h Hag s Hs. unfold glue.
    destruct (Z.leb_spec 0 (s4_t (site_reflect s))) as [Hle | Hlt].
    - assert (E0 : s4_t s = 0%Z)
        by (destruct s as [t x y z]; cbn [site_reflect s4_t] in *; lia).
      assert (Er : site_reflect s = s)
        by (destruct s as [t x y z]; cbn [s4_t] in E0; subst t; reflexivity).
      rewrite Er. symmetry. apply Hag. exact E0.
    - rewrite LatticeSymmetry.site_reflect_invol. reflexivity.
  Qed.

  (* Theta (f1 o g) * (f2 o h) = ((Theta f1) * f2) o (glue g h) *)
  Lemma reflect_glue : forall (g h : Site4D -> Quat) (f1 f2 : SU2Config -> R),
    (forall s, s4_t s = 0%Z -> g s = h s) ->
    su2_pos_time_observable f1 -> su2_pos_time_observable f2 ->
    forall U,
      obs_reflect f1 (su2_gauge (glue g h) U) * f2 (su2_gauge (glue g h) U)
      = obs_reflect (obs_gauge g f1) U * obs_gauge h f2 U.
  Proof.
    intros g h f1 f2 Hag [P1 [_ [Hpos1 [Hloc1 _]]]] [P2 [_ [Hpos2 [Hloc2 _]]]] U.
    unfold obs_reflect, obs_gauge. rewrite reflect_gauge.
    rewrite (gauge_pos_agree f1 P1 (fun s => glue g h (site_reflect s)) g Hloc1 Hpos1
               (glue_refl g h Hag) (su2_reflect U)).
    rewrite (gauge_pos_agree f2 P2 (glue g h) h Hloc2 Hpos2 (glue_pos g h) U).
    reflexivity.
  Qed.

  (* =======================================================================
     3. The gauge action on a Hilbert space with an Osterwalder-Schrader
        embedding and a transfer operator
     ======================================================================= *)

  Section Action.
    Variable beta : R.
    Variable H : Type.
    Variable hadd : H -> H -> H.
    Variable hscal : R -> H -> H.
    Variable ip : H -> H -> R.
    Variable emb : (SU2Config -> R) -> H.
    Variable T : H -> H.
    Hypothesis HH : hs_hilbert_space H hadd hscal ip.
    Hypothesis Hemb : su2_os_embedding beta H hadd hscal ip emb.
    Hypothesis HT : su2_os_transfer_operator H hadd hscal ip emb T.

    Local Notation "x -- y" := (sub hadd hscal x y) (at level 40, left associativity).
    Local Notation infE := (su2_infinite_volume_expect_is beta).

    Lemma HF : form_axioms hadd hscal ip.
    Proof.
      destruct HH as (h1 & h2 & h3 & h4 & _). unfold form_axioms.
      split; [exact h1 |]. split; [exact h2 |]. split; [exact h3 | exact h4].
    Qed.

    Lemma HC : complete hadd hscal ip.
    Proof. destruct HH as (_ & _ & _ & _ & h5). exact h5. Qed.

    Lemma emb_form : forall f g : SU2Config -> R,
      su2_pos_time_observable f -> su2_pos_time_observable g ->
      infE (fun U => obs_reflect f U * g U) (ip (emb f) (emb g)).
    Proof. destruct Hemb as (h1 & _). exact h1. Qed.

    Lemma T_sym : forall x y : H, ip (T x) y = ip x (T y).
    Proof. destruct HT as (_ & _ & h & _). exact h. Qed.

    Lemma T_contr : forall x : H, ip (T x) (T x) <= ip x x.
    Proof. destruct HT as (_ & _ & _ & _ & h & _). exact h. Qed.

    Lemma T_emb : forall f : SU2Config -> R, su2_pos_time_observable f ->
      ip (T (emb f) -- emb (obs_translate_n D4_t 1 f))
         (T (emb f) -- emb (obs_translate_n D4_t 1 f)) = 0.
    Proof. destruct HT as (_ & _ & _ & _ & _ & h). exact h. Qed.

    Lemma T_nonexp : forall x y : H,
      ip (T x -- T y) (T x -- T y) <= ip (x -- y) (x -- y).
    Proof. intros x y. rewrite (A_Q_sub HF T T_sym x y). apply T_contr. Qed.

    Lemma T_null : forall x y : H,
      ip (x -- y) (x -- y) = 0 -> ip (T x -- T y) (T x -- T y) = 0.
    Proof.
      intros x y Hn. pose proof (T_nonexp x y) as H1.
      pose proof (B_pos HF (T x -- T y)) as H2. lra.
    Qed.

    (* ---------- invariance of the Osterwalder-Schrader form ---------- *)

    Lemma form_gauge : forall (g h : Site4D -> Quat) (f1 f2 : SU2Config -> R),
      su2_gauge_fn g -> su2_gauge_fn h ->
      (forall s, s4_t s = 0%Z -> g s = h s) ->
      su2_pos_time_observable f1 -> su2_pos_time_observable f2 ->
      ip (emb (obs_gauge g f1)) (emb (obs_gauge h f2)) = ip (emb f1) (emb f2).
    Proof.
      intros g h f1 f2 Hg Hh Hag P1 P2.
      pose proof (emb_form (obs_gauge g f1) (obs_gauge h f2)
                    (pos_gauge g f1 Hg P1) (pos_gauge h f2 Hh P2)) as A.
      pose proof (emb_form f1 f2 P1 P2) as B0.
      destruct (SU2MassGap.loc_mult (obs_reflect f1) f2
                  (SU2MassGap.loc_reflect f1
                     (SU2MassGap.pos_loc f1 (SU2OSHilbertSpace.obs_pos f1 P1)))
                  (SU2MassGap.pos_loc f2 (SU2OSHilbertSpace.obs_pos f2 P2)))
        as [Hbc [Q [HQ Hloc]]].
      pose proof (SU2GaugeInvariance.su2_infinite_volume_gauge_invariance
                    beta Q (fun U => obs_reflect f1 U * f2 U) (glue g h)
                    (ip (emb f1) (emb f2)) HQ Hloc Hbc (glue_fn g h Hg Hh) B0) as B1.
      apply (SU2Uniqueness.inf_unique beta
               (fun U => obs_reflect (obs_gauge g f1) U * obs_gauge h f2 U)); [exact A |].
      apply (SU2Uniqueness.inf_ext beta
               (fun U => obs_reflect f1 (su2_gauge (glue g h) U)
                         * f2 (su2_gauge (glue g h) U))); [| exact B1].
      exact (reflect_glue g h f1 f2 Hag P1 P2).
    Qed.

    (* two gauge transformations that coincide at time zero give the same
       vector *)
    Lemma emb_gauge_null : forall (g h : Site4D -> Quat) (f : SU2Config -> R),
      su2_gauge_fn g -> su2_gauge_fn h ->
      (forall s, s4_t s = 0%Z -> g s = h s) ->
      su2_pos_time_observable f ->
      ip (emb (obs_gauge g f) -- emb (obs_gauge h f))
         (emb (obs_gauge g f) -- emb (obs_gauge h f)) = 0.
    Proof.
      intros g h f Hg Hh Hag Pf.
      rewrite (Q_sub HF (emb (obs_gauge g f)) (emb (obs_gauge h f))).
      rewrite (form_gauge g g f f Hg Hg (fun s _ => eq_refl) Pf Pf).
      rewrite (form_gauge g h f f Hg Hh Hag Pf Pf).
      rewrite (form_gauge h h f f Hh Hh (fun s _ => eq_refl) Pf Pf).
      ring.
    Qed.

    (* ---------- the dense family of local observables ---------- *)

    Definition V : Type := { f : SU2Config -> R | su2_pos_time_observable f }.

    Definition e (v : V) : H := emb (proj1_sig v).

    Lemma e_dense : forall (x : H) (eps : R), 0 < eps ->
      exists v : V, ip (x -- e v) (x -- e v) < eps.
    Proof.
      intros x eps He. destruct Hemb as (_ & _ & _ & h4).
      destruct (h4 x eps He) as [f [Pf Hf]].
      exists (exist _ f Pf). exact Hf.
    Qed.

    Definition W0 (g : Site4D -> Quat) (v : V) : H := emb (obs_gauge g (proj1_sig v)).

    Lemma W0_iso : forall g : Site4D -> Quat, su2_gauge_fn g ->
      forall u v : V, ip (W0 g u) (W0 g v) = ip (e u) (e v).
    Proof.
      intros g Hg [f1 P1] [f2 P2]. unfold W0, e. cbn [proj1_sig].
      exact (form_gauge g g f1 f2 Hg Hg (fun s _ => eq_refl) P1 P2).
    Qed.

    (* ---------- the maps W g ---------- *)

    Lemma W_ex : forall g : Site4D -> Quat,
      exists Wg : H -> H,
        su2_gauge_fn g ->
        (forall x y : H, ip (Wg x) (Wg y) = ip x y) /\
        (forall f : SU2Config -> R, su2_pos_time_observable f ->
           ip (Wg (emb f) -- emb (obs_gauge g f)) (Wg (emb f) -- emb (obs_gauge g f)) = 0).
    Proof.
      intro g. destruct (classic (su2_gauge_fn g)) as [Hg | Hn].
      - exists (Wext HF V e e_dense HC (W0 g) (W0_iso g Hg)). intros _. split.
        + exact (Wext_iso HF V e e_dense HC (W0 g) (W0_iso g Hg)).
        + intros f Pf.
          exact (Wext_e HF V e e_dense HC (W0 g) (W0_iso g Hg) (exist _ f Pf)).
      - exists (fun x => x). intro Hg. contradiction.
    Qed.

    Definition W (g : Site4D -> Quat) : H -> H :=
      proj1_sig (constructive_indefinite_description _ (W_ex g)).

    Lemma W_iso : forall g : Site4D -> Quat, su2_gauge_fn g ->
      forall x y : H, ip (W g x) (W g y) = ip x y.
    Proof.
      intros g Hg.
      exact (proj1 (proj2_sig (constructive_indefinite_description _ (W_ex g)) Hg)).
    Qed.

    Lemma W_emb : forall (g : Site4D -> Quat) (f : SU2Config -> R),
      su2_gauge_fn g -> su2_pos_time_observable f ->
      ip (W g (emb f) -- emb (obs_gauge g f)) (W g (emb f) -- emb (obs_gauge g f)) = 0.
    Proof.
      intros g f Hg.
      exact (proj2 (proj2_sig (constructive_indefinite_description _ (W_ex g)) Hg) f).
    Qed.

    Lemma W_nonexp : forall g : Site4D -> Quat, su2_gauge_fn g ->
      forall x y : H, ip (W g x -- W g y) (W g x -- W g y) <= ip (x -- y) (x -- y).
    Proof.
      intros g Hg x y. rewrite (iso_Q_sub HF (W g) (W_iso g Hg) x y). apply Rle_refl.
    Qed.

    Lemma W_null : forall g : Site4D -> Quat, su2_gauge_fn g ->
      forall x y : H, ip (x -- y) (x -- y) = 0 -> ip (W g x -- W g y) (W g x -- W g y) = 0.
    Proof. intros g Hg x y. exact (iso_null HF (W g) (W_iso g Hg) x y). Qed.

    (* ---------- identity and composition ---------- *)

    Lemma W_one : forall x : H,
      ip (W (fun _ => qone) x -- x) (W (fun _ => qone) x -- x) = 0.
    Proof.
      apply (agree_dense HF V e e_dense (W (fun _ => qone)) (fun x => x)).
      - exact (W_nonexp _ gauge_fn_one).
      - intros x y. apply Rle_refl.
      - intros [f Pf]. unfold e. cbn [proj1_sig].
        pose proof (W_emb (fun _ => qone) f gauge_fn_one Pf) as H1.
        rewrite obs_gauge_one in H1. exact H1.
    Qed.

    Lemma W_comp : forall (g h : Site4D -> Quat) (x : H),
      su2_gauge_fn g -> su2_gauge_fn h ->
      ip (W h (W g x) -- W (fun s => qmul (g s) (h s)) x)
         (W h (W g x) -- W (fun s => qmul (g s) (h s)) x) = 0.
    Proof.
      intros g h x Hg Hh. revert x.
      pose proof (gauge_fn_mul g h Hg Hh) as Hgh.
      apply (agree_dense HF V e e_dense (fun x => W h (W g x))
               (W (fun s => qmul (g s) (h s)))).
      - intros x y. rewrite (iso_Q_sub HF (W h) (W_iso h Hh) (W g x) (W g y)).
        exact (W_nonexp g Hg x y).
      - exact (W_nonexp _ Hgh).
      - intros [f Pf]. unfold e. cbn [proj1_sig].
        apply (null_trans HF _ (W h (emb (obs_gauge g f)))).
        + exact (W_null h Hh _ _ (W_emb g f Hg Pf)).
        + apply (null_trans HF _ (emb (obs_gauge h (obs_gauge g f)))).
          * exact (W_emb h (obs_gauge g f) Hh (pos_gauge g f Hg Pf)).
          * rewrite obs_gauge_comp. apply (null_sym HF).
            exact (W_emb (fun s => qmul (g s) (h s)) f Hgh Pf).
    Qed.

    (* ---------- only the hyperplane t = 0 matters ---------- *)

    Lemma W_time_zero : forall (g h : Site4D -> Quat) (x : H),
      su2_gauge_fn g -> su2_gauge_fn h ->
      (forall s, s4_t s = 0%Z -> g s = h s) ->
      ip (W g x -- W h x) (W g x -- W h x) = 0.
    Proof.
      intros g h x Hg Hh Hag. revert x.
      apply (agree_dense HF V e e_dense (W g) (W h)).
      - exact (W_nonexp g Hg).
      - exact (W_nonexp h Hh).
      - intros [f Pf]. unfold e. cbn [proj1_sig].
        apply (null_trans HF _ (emb (obs_gauge g f))); [exact (W_emb g f Hg Pf) |].
        apply (null_trans HF _ (emb (obs_gauge h f)));
          [exact (emb_gauge_null g h f Hg Hh Hag Pf) |].
        apply (null_sym HF). exact (W_emb h f Hh Pf).
    Qed.

    (* ---------- commutation with the transfer operator ---------- *)

    Lemma pos_translate : forall f : SU2Config -> R,
      su2_pos_time_observable f -> su2_pos_time_observable (obs_translate_n D4_t 1 f).
    Proof.
      intros f Pf. apply SU2OSHilbertSpace.pos_obs.
      apply SU2MassGap.pos_translate_n. apply SU2OSHilbertSpace.obs_pos. exact Pf.
    Qed.

    Lemma W_T_static : forall (g : Site4D -> Quat) (x : H),
      su2_gauge_fn g -> (forall s, g (shift4D s D4_t) = g s) ->
      ip (W g (T x) -- T (W g x)) (W g (T x) -- T (W g x)) = 0.
    Proof.
      intros g x Hg Hst. revert x.
      apply (agree_dense HF V e e_dense (fun x => W g (T x)) (fun x => T (W g x))).
      - intros x y. rewrite (iso_Q_sub HF (W g) (W_iso g Hg) (T x) (T y)).
        apply T_nonexp.
      - intros x y. apply Rle_trans with (ip (W g x -- W g y) (W g x -- W g y));
          [apply T_nonexp | exact (W_nonexp g Hg x y)].
      - intros [f Pf]. unfold e. cbn [proj1_sig].
        apply (null_trans HF _ (W g (emb (obs_translate_n D4_t 1 f)))).
        + exact (W_null g Hg _ _ (T_emb f Pf)).
        + apply (null_trans HF _ (emb (obs_gauge g (obs_translate_n D4_t 1 f)))).
          * exact (W_emb g _ Hg (pos_translate f Pf)).
          * rewrite (obs_gauge_translate g f Hst).
            apply (null_trans HF _ (T (emb (obs_gauge g f)))).
            -- apply (null_sym HF). exact (T_emb (obs_gauge g f) (pos_gauge g f Hg Pf)).
            -- apply T_null. apply (null_sym HF). exact (W_emb g f Hg Pf).
    Qed.

    (* the time-independent gauge transformation with the same restriction to
       the hyperplane t = 0 *)
    Definition static (g : Site4D -> Quat) : Site4D -> Quat :=
      fun s => g (mkSite4D 0 (s4_x s) (s4_y s) (s4_z s)).

    Lemma W_T : forall (g : Site4D -> Quat) (x : H), su2_gauge_fn g ->
      ip (W g (T x) -- T (W g x)) (W g (T x) -- T (W g x)) = 0.
    Proof.
      intros g x Hg.
      assert (Hs : su2_gauge_fn (static g)) by (intro s; apply Hg).
      assert (Hst : forall s, static g (shift4D s D4_t) = static g s)
        by (intros [t a b c]; reflexivity).
      assert (Hag : forall s, s4_t s = 0%Z -> g s = static g s).
      { intros [t a b c] E. cbn [s4_t] in E. subst t. reflexivity. }
      apply (null_trans HF _ (W (static g) (T x)));
        [exact (W_time_zero g (static g) (T x) Hg Hs Hag) |].
      apply (null_trans HF _ (T (W (static g) x)));
        [exact (W_T_static (static g) x Hs Hst) |].
      apply T_null. apply (null_sym HF). exact (W_time_zero g (static g) x Hg Hs Hag).
    Qed.

    (* ---------- the gauge action ---------- *)

    Theorem gauge_action_ex :
      exists Wf : (Site4D -> Quat) -> H -> H,
        su2_os_gauge_action H hadd hscal ip emb T (emb (fun _ => 1)) Wf.
    Proof.
      exists W.
      split; [exact W_emb |].
      split; [intros g x y Hg; exact (iso_add HF (W g) (W_iso g Hg) x y) |].
      split; [intros g c x Hg; exact (iso_scal HF (W g) (W_iso g Hg) c x) |].
      split; [intros g x y Hg; exact (W_iso g Hg x y) |].
      split; [exact W_one |].
      split; [exact W_comp |].
      split; [exact W_time_zero |].
      split; [exact W_T |].
      intros g Hg.
      exact (W_emb g (fun _ => 1) Hg
               (SU2OSHilbertSpace.pos_obs _ SU2OSHilbertSpace.one_pos)).
    Qed.
  End Action.

  (* TARGET 15 *)
  Theorem su2_gauge_symmetry : Challenge_SU2Gauge4D_GaugeSymmetry.
  Proof.
    intros beta mu Hmu Hb0 Hsmall Hb.
    destruct (SU2TransferSpectrum.su2_transfer_spectrum beta mu Hmu Hb0 Hsmall Hb)
      as (H & hadd & hscal & ip & emb & T & HH & Hemb & HT & HV & HS).
    destruct (gauge_action_ex beta H hadd hscal ip emb T HH Hemb HT) as [Wf HW].
    exists H, hadd, hscal, ip, emb, T, Wf.
    split; [exact HH |]. split; [exact Hemb |]. split; [exact HT |].
    split; [exact HV |]. split; [exact HS | exact HW].
  Qed.

End SU2GaugeSymmetry.
