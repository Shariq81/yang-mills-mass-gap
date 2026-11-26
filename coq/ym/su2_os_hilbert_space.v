(* =========================================================================
   ym/su2_os_hilbert_space.v

   TARGET 13: the Osterwalder-Schrader Hilbert space of the 4D SU(2) Wilson
   lattice gauge theory at strong coupling, the transfer operator as a
   positive self-adjoint contraction on it, and its spectral gap.

   The pre-Hilbert space V is the type of bounded uniformly continuous
   observables localized on finitely many canonical plaquettes at
   non-negative times, with the form
       (f, g) = < (Theta f) g >       (infinite-volume Gibbs state).
   By Targets 10 and 12 the form is symmetric, bilinear and positive
   semidefinite, and the translation T0 by one unit of time is symmetric
   (12c), positive (12a) and a contraction (12c + 12d) for it, with the gap
   estimate 12b.  `rg/hilbert_completion.v` then provides the completion
   (Cauchy sequences) and the extension of T0.

   ZERO `Axiom`, `Parameter`, `Admitted`.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz.
From Coq Require Import Classical_Prop ClassicalEpsilon.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import verification.ChallengeSU2TransferPositivity.
Require Import verification.ChallengeSU2HilbertSpace.
Require Import rg.hilbert_completion.
Require Import ym.su2_continuity.
Require Import ym.su2_uniqueness.
Require Import ym.su2_mass_gap.
Require Import ym.su2_transfer_positivity.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import ChallengeSU2InfiniteVolume ChallengeSU2MassGap.
Import ChallengeSU2TransferPositivity ChallengeSU2HilbertSpace.
Import SU2MassGap HilbertCompletion.

Open Scope R_scope.

Module SU2OSHilbertSpace.

  (* =======================================================================
     1. Preliminaries
     ======================================================================= *)

  Lemma obs_pos : forall f : SU2Config -> R, su2_pos_time_observable f -> PosObs f.
  Proof.
    intros f [P [HP [Hpos [Hloc Hbc]]]]. split; [exact Hbc |].
    exists P. split; [exact HP |]. split; [exact Hpos | exact Hloc].
  Qed.

  Lemma pos_obs : forall f : SU2Config -> R, PosObs f -> su2_pos_time_observable f.
  Proof.
    intros f [Hbc [P [HP [Hpos Hloc]]]]. exists P.
    split; [exact HP |]. split; [exact Hpos |]. split; [exact Hloc | exact Hbc].
  Qed.

  Lemma one_pos : PosObs (fun _ : SU2Config => 1).
  Proof.
    split; [apply SU2Continuity.bc_const |]. exists (@nil Plaq4D).
    split; [constructor |]. split; [constructor |]. intros U U' _. reflexivity.
  Qed.

  Lemma exp_iter : forall (a : R) (k : nat), exp a ^ k = exp (a * INR k).
  Proof.
    intros a k. induction k as [| k IH].
    - simpl. rewrite Rmult_0_r, exp_0. reflexivity.
    - rewrite S_INR. replace (a * (INR k + 1)) with (a + a * INR k) by ring.
      rewrite exp_plus, <- IH. reflexivity.
  Qed.

  (* =======================================================================
     2. The pre-Hilbert space of local observables at non-negative times
     ======================================================================= *)

  Definition V : Type := { f : SU2Config -> R | PosObs f }.

  Definition fn (u : V) : SU2Config -> R := proj1_sig u.

  Definition vadd (u w : V) : V :=
    exist PosObs (fun U => fn u U + fn w U)
      (pos_plus (fn u) (fn w) (proj2_sig u) (proj2_sig w)).

  Definition vscal (c : R) (u : V) : V :=
    exist PosObs (fun U => c * fn u U) (pos_scal c (fn u) (proj2_sig u)).

  (* translation by one unit of time *)
  Definition T0 (u : V) : V :=
    exist PosObs (obs_translate_n D4_t 1 (fn u)) (pos_translate_n 1 (fn u) (proj2_sig u)).

  (* the constant observable 1 *)
  Definition Om0 : V := exist PosObs (fun _ : SU2Config => 1) one_pos.

  Section OS.
    Variables beta mu : R.
    Hypothesis Hmu : 0 <= mu.
    Hypothesis Hb0 : 0 <= beta.
    Hypothesis Hsmall : 168 * beta <= exp (- mu).
    Hypothesis Hb : 43008 * beta <= 1.

    Local Notation infE := (su2_infinite_volume_expect_is beta).

    Lemma Hbeta : 43008 * Rabs beta <= 1.
    Proof. rewrite (Rabs_pos_eq beta Hb0). exact Hb. Qed.

    (* ---------- the Osterwalder-Schrader form ---------- *)

    Lemma form_ex : forall u w : V,
      exists v : R, infE (fun U => obs_reflect (fn u) U * fn w U) v.
    Proof.
      intros u w. apply (loc_exists beta Hbeta).
      apply loc_mult; [apply loc_reflect |]; apply pos_loc;
        [exact (proj2_sig u) | exact (proj2_sig w)].
    Qed.

    Definition BV (u w : V) : R :=
      proj1_sig (constructive_indefinite_description _ (form_ex u w)).

    Lemma BV_spec : forall u w : V,
      infE (fun U => obs_reflect (fn u) U * fn w U) (BV u w).
    Proof.
      intros u w.
      exact (proj2_sig (constructive_indefinite_description _ (form_ex u w))).
    Qed.

    Lemma BV_val : forall (u w : V) (v : R),
      infE (fun U => obs_reflect (fn u) U * fn w U) v -> BV u w = v.
    Proof.
      intros u w v H. exact (SU2Uniqueness.inf_unique beta _ _ _ (BV_spec u w) H).
    Qed.

    Lemma BV_ext : forall u u' w : V, (forall U, fn u U = fn u' U) -> BV u w = BV u' w.
    Proof.
      intros u u' w H. apply BV_val.
      apply (SU2Uniqueness.inf_ext beta (fun U => obs_reflect (fn u') U * fn w U));
        [| apply BV_spec].
      intro U. unfold obs_reflect. rewrite (H (su2_reflect U)). reflexivity.
    Qed.

    Lemma HV : form_axioms vadd vscal BV.
    Proof.
      split; [| split; [| split]].
      - intros u w. apply BV_val.
        apply (form_sym beta Hbeta (fn w) (fn u) (BV w u) (proj2_sig w) (proj2_sig u)).
        apply BV_spec.
      - intros u u' w. apply BV_val.
        apply (SU2Uniqueness.inf_ext beta
                 (fun U => obs_reflect (fn u) U * fn w U + obs_reflect (fn u') U * fn w U)).
        + intro U. unfold vadd, fn, obs_reflect. cbn [proj1_sig]. ring.
        + exact (SU2Uniqueness.inf_plus beta _ _ _ _ (BV_spec u w) (BV_spec u' w)).
      - intros c u w. apply BV_val.
        apply (SU2Uniqueness.inf_ext beta
                 (fun U => c * (obs_reflect (fn u) U * fn w U))).
        + intro U. unfold vscal, fn, obs_reflect. cbn [proj1_sig]. ring.
        + exact (SU2Uniqueness.inf_scal beta c _ _ (BV_spec u w)).
      - intro u.
        destruct (pos_rp beta Hbeta (fn u) (proj2_sig u)) as [v [Hv Hv0]].
        rewrite (BV_val u u v Hv). exact Hv0.
    Qed.

    (* ---------- the translation: symmetric, positive, contraction ---------- *)

    Lemma T0_sym : forall u w : V, BV (T0 u) w = BV u (T0 w).
    Proof.
      intros u w.
      pose proof (proj2_sig u) as [Hbf [P [HP [HPp Hlf]]]].
      pose proof (proj2_sig w) as [Hbg [Q [HQ [HQp Hlg]]]].
      destruct (SU2TransferPositivity.su2_transfer_matrix_symmetry beta P Q (fn u) (fn w)
                  Hbeta HP HPp HQ HQp Hlf Hlg Hbf Hbg) as [v [v' [_ [_ [H3 H4]]]]].
      rewrite (BV_val (T0 u) w v' H4), (BV_val u (T0 w) v' H3). reflexivity.
    Qed.

    Lemma T0_contr : forall u : V, BV (T0 u) (T0 u) <= BV u u.
    Proof.
      intro u.
      pose proof (proj2_sig u) as [Hbf [P [HP [HPp Hlf]]]].
      destruct (SU2TransferPositivity.su2_transfer_matrix_contraction beta P (fn u) 2%nat
                  Hbeta HP HPp Hlf Hbf) as [v0 [vk [H0 [Hk Habs]]]].
      rewrite (T0_sym u (T0 u)), (BV_val u (T0 (T0 u)) vk Hk), (BV_val u u v0 H0).
      pose proof (Rle_abs vk). lra.
    Qed.

    Lemma T0_pos : forall u : V, 0 <= BV u (T0 u).
    Proof.
      intro u.
      pose proof (proj2_sig u) as [Hbf [P [HP [HPp Hlf]]]].
      destruct (SU2TransferPositivity.su2_transfer_matrix_positivity beta P (fn u)
                  Hb0 Hb HP HPp Hlf Hbf) as [v1 [H1 Hnn]].
      rewrite (BV_val u (T0 u) v1 H1). exact Hnn.
    Qed.

    (* ---------- the vacuum ---------- *)

    Lemma Om_norm : BV Om0 Om0 = 1.
    Proof.
      apply BV_val.
      apply (SU2Uniqueness.inf_ext beta (fun _ => 1)); [| apply SU2Uniqueness.inf_const].
      intro U. unfold fn, Om0, obs_reflect. cbn [proj1_sig]. ring.
    Qed.

    Lemma BV_Om : forall (u : V) (vf : R), infE (fn u) vf -> BV u Om0 = vf.
    Proof.
      intros u vf H. apply BV_val.
      apply (SU2Uniqueness.inf_ext beta (obs_reflect (fn u))).
      - intro U. unfold fn, Om0. cbn [proj1_sig]. ring.
      - exact (loc_reflect_inv beta Hbeta (fn u) vf (pos_loc _ (proj2_sig u)) H).
    Qed.

    Lemma T0_Om : forall z : V, BV (T0 Om0) z = BV Om0 z.
    Proof. intro z. apply BV_ext. intro U. reflexivity. Qed.

    Lemma T0_gap : forall u : V,
      BV u (T0 u) - BV u Om0 * BV u Om0
      <= exp (- (mu / 2)) * (BV u u - BV u Om0 * BV u Om0).
    Proof.
      intro u.
      pose proof (proj2_sig u) as [Hbf [P [HP [HPp Hlf]]]].
      destruct (SU2TransferPositivity.su2_transfer_matrix_spectral_bounds beta mu P (fn u)
                  Hmu Hb0 Hsmall Hb HP HPp Hlf Hbf)
        as [v0 [v1 [vf [H0 [H1 [Hvf [Hlo Hup]]]]]]].
      rewrite (BV_val u (T0 u) v1 H1), (BV_val u u v0 H0), (BV_Om u vf Hvf). exact Hup.
    Qed.

    (* =====================================================================
       3. The completion
       ===================================================================== *)

    Definition Hs : Type := @Hc V vadd vscal BV.

    Local Notation hA := (hadd HV).
    Local Notation hS := (hscal HV).
    Local Notation iP := (ip HV).
    Local Notation em0 := (emb HV).
    Local Notation TT := (Text HV T0 T0_sym T0_contr).
    Local Notation hsub := (sub hA hS).
    Local Notation vsub := (sub vadd vscal).

    (* the embedding of all functions: observables at non-negative times are
       sent to their constant sequences, the other functions to the vacuum *)
    Definition emF (f : SU2Config -> R) : Hs :=
      match excluded_middle_informative (PosObs f) with
      | left pf => em0 (exist PosObs f pf)
      | right _ => em0 Om0
      end.

    Lemma emF_pos : forall (f : SU2Config -> R) (pf : PosObs f),
      emF f = em0 (exist PosObs f pf).
    Proof.
      intros f pf. unfold emF.
      destruct (excluded_middle_informative (PosObs f)) as [p | n]; [| contradiction].
      rewrite (proof_irrelevance (PosObs f) p pf). reflexivity.
    Qed.

    Lemma null_seq : forall X Y : Hs,
      (forall n, BV (vsub (seq X n) (seq Y n)) (vsub (seq X n) (seq Y n)) = 0) ->
      iP (hsub X Y) (hsub X Y) = 0.
    Proof.
      intros X Y H. apply (UL_sequence _ _ _ (nrm_cv HV X Y)).
      apply (cv_ext (fun _ => 0)); [| apply cv_const].
      intro n. symmetry. apply H.
    Qed.

    Lemma hilbert_space : hs_hilbert_space Hs hA hS iP.
    Proof.
      destruct (H_form HV) as [S1 [S2 [S3 S4]]].
      split; [exact S1 |]. split; [exact S2 |]. split; [exact S3 |]. split; [exact S4 |].
      exact (complete HV).
    Qed.

    Lemma embedding : su2_os_embedding beta Hs hA hS iP emF.
    Proof.
      split; [| split; [| split]].
      - intros f g Hf Hg. apply obs_pos in Hf. apply obs_pos in Hg.
        rewrite (emF_pos f Hf), (emF_pos g Hg), (ip_emb HV).
        exact (BV_spec (exist PosObs f Hf) (exist PosObs g Hg)).
      - intros f g Hf Hg. apply obs_pos in Hf. apply obs_pos in Hg.
        unfold hs_null.
        rewrite (emF_pos (fun U => f U + g U) (pos_plus f g Hf Hg)),
          (emF_pos f Hf), (emF_pos g Hg).
        apply null_seq. intro n. apply (null_weak HV). intro z.
        apply BV_ext. intro U. reflexivity.
      - intros c f Hf. apply obs_pos in Hf. unfold hs_null.
        rewrite (emF_pos (fun U => c * f U) (pos_scal c f Hf)), (emF_pos f Hf).
        apply null_seq. intro n. apply (null_weak HV). intro z.
        apply BV_ext. intro U. reflexivity.
      - intros x eps He. destruct (dense HV x eps He) as [v Hv].
        destruct v as [f pf]. exists f. split; [apply pos_obs; exact pf |].
        rewrite (emF_pos f pf). exact Hv.
    Qed.

    Lemma TT_sym : forall x y : Hs, iP (TT x) y = iP x (TT y).
    Proof. exact (Text_sym HV T0 T0_sym T0_contr). Qed.

    Lemma TT_pos : forall x : Hs, 0 <= iP x (TT x).
    Proof. exact (Text_pos HV T0 T0_sym T0_contr T0_pos). Qed.

    Lemma transfer_operator : su2_os_transfer_operator Hs hA hS iP emF TT.
    Proof.
      split; [| split; [| split; [| split; [| split]]]].
      - intros x y. exact (A_add_null (H_form HV) TT TT_sym x y).
      - intros c x. exact (A_scal_null (H_form HV) TT TT_sym c x).
      - exact TT_sym.
      - exact TT_pos.
      - exact (Text_contr HV T0 T0_sym T0_contr).
      - intros f Hf. apply obs_pos in Hf. unfold hs_null.
        rewrite (emF_pos f Hf),
          (emF_pos (obs_translate_n D4_t 1 f) (pos_translate_n 1 f Hf)).
        exact (Text_emb HV T0 T0_sym T0_contr (exist PosObs f Hf)).
    Qed.

    (* ---------- vacuum and gap ---------- *)

    Local Notation Om := (em0 Om0).
    Local Notation cgap := (exp (- (mu / 2))).

    Lemma Om_fix : iP (hsub (TT Om) Om) (hsub (TT Om) Om) = 0.
    Proof.
      apply null_seq. intro n. apply (null_weak HV). intro z. exact (T0_Om z).
    Qed.

    Lemma H_gap : forall x : Hs, iP x Om = 0 -> iP x (TT x) <= cgap * iP x x.
    Proof.
      intros x Hx.
      pose proof (Text_gap HV T0 T0_sym T0_contr Om0 cgap T0_gap x) as H.
      rewrite Hx in H. lra.
    Qed.

    Lemma cgap_pos : 0 <= cgap.
    Proof. apply Rlt_le. apply exp_pos. Qed.

    Lemma vacuum_gap : su2_os_vacuum_gap Hs hA hS iP TT (emF (fun _ => 1)) (mu / 2).
    Proof.
      unfold su2_os_vacuum_gap. rewrite (emF_pos (fun _ => 1) one_pos).
      change (exist PosObs (fun _ : SU2Config => 1) one_pos) with Om0.
      split; [| split; [| split; [| split]]].
      - rewrite (ip_emb HV). exact Om_norm.
      - exact Om_fix.
      - exact H_gap.
      - intros k x Hx.
        pose proof (iter_gap (H_form HV) TT TT_sym TT_pos Om Om_fix cgap cgap_pos H_gap
                      k x Hx) as H.
        assert (E : (cgap * cgap) ^ k = exp (- (2 * (mu / 2) * INR k))).
        { rewrite <- exp_plus, exp_iter. f_equal. ring. }
        rewrite E in H. exact H.
      - intros Hm x Hx.
        assert (Hc1 : cgap < 1).
        { rewrite <- exp_0. apply exp_increasing. lra. }
        assert (Hn : iP Om Om = 1) by (rewrite (ip_emb HV); exact Om_norm).
        exact (vacuum_unique (H_form HV) TT TT_sym Om Om_fix cgap H_gap Hc1 Hn x Hx).
    Qed.

    Theorem os_hilbert_space :
      exists (H : Type) (hadd : H -> H -> H) (hscal : R -> H -> H)
             (ip : H -> H -> R) (emb : (SU2Config -> R) -> H) (T : H -> H),
        hs_hilbert_space H hadd hscal ip /\
        su2_os_embedding beta H hadd hscal ip emb /\
        su2_os_transfer_operator H hadd hscal ip emb T /\
        su2_os_vacuum_gap H hadd hscal ip T (emb (fun _ => 1)) (mu / 2).
    Proof.
      exists Hs, hA, hS, iP, emF, TT.
      split; [exact hilbert_space |]. split; [exact embedding |].
      split; [exact transfer_operator | exact vacuum_gap].
    Qed.
  End OS.

  (* TARGET 13 *)
  Theorem su2_os_hilbert_space : Challenge_SU2Gauge4D_OSHilbertSpace.
  Proof.
    intros beta mu Hmu Hb0 Hsmall Hb.
    exact (os_hilbert_space beta mu Hmu Hb0 Hsmall Hb).
  Qed.

End SU2OSHilbertSpace.
