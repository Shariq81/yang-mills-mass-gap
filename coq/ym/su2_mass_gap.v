(* =========================================================================
   ym/su2_mass_gap.v

   Symmetries, reflection positivity and the transfer-matrix mass gap of the
   infinite-volume Gibbs state of the 4D SU(2) Wilson lattice gauge theory
   at strong coupling (TARGETS 10b, 10c, 10e, 10f), proved directly for the
   frozen objects of `verification/ChallengeSU2MassGap.v`.

     10b  Translating (reflecting) an observable is the same as translating
          (reflecting) the finite volume (ym/su2_covariance.v); the images
          of the cubes still exhaust the lattice, so by the uniqueness of
          the thermodynamic limit (Target 10a) the infinite-volume
          expectation is unchanged.
     10c  The cubes are replaced by volumes that are symmetric under the
          time reflection; there reflection positivity holds for every Hopf
          grid of level >= 1 (ym/su2_reflection_positivity.v, the grids
          being invariant under inversion), hence for the Haar limit and,
          by Target 10a again, for the infinite-volume state.
     10e  Write (X, Y) = <(Theta X) Y> for observables at non-negative
          times, T for the translation by one unit of time and
          psi = f - <f>.  By 10b the form is symmetric and
          (T^j psi, T^j psi) = (psi, T^{2j} psi); by 10c it is positive
          semidefinite, so the Cauchy-Schwarz inequality gives
            a_j^2 <= a_0 a_{2j},   a_j = (psi, T^j psi).
          By the multi-plaquette clustering of Target 10d,
            |a_j| <= C_f exp(- (mu/2) j),
          because the supports of Theta psi and T^j psi are at distance
          >= j/2.  The iterated Cauchy-Schwarz lemma of
          rg/cauchy_schwarz_gap.v removes the constant C_f:
            |a_k| <= exp(- (mu/2) k) a_0.
     10f  For phi = f - <f> and psi = g - <g>, by Cauchy-Schwarz and 10e,
            (phi, T^k psi)^2 <= (phi, phi) (T^k psi, T^k psi)
                              = (phi, phi) (psi, T^{2k} psi)
                             <= exp(- mu k) (phi, phi) (psi, psi).

   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import verification.ChallengeSU2MassGap.
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import rg.product_measure_perm.
Require Import rg.cauchy_schwarz_gap.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.su2_algebra.
Require Import ym.su2_continuity.
Require Import ym.su2_haar_grid.
Require Import ym.su2_haar_limit.
Require Import ym.lattice_boxes.
Require Import ym.su2_infinite_volume.
Require Import ym.su2_haar_grid_conj.
Require Import ym.lattice_symmetry.
Require Import ym.su2_covariance.
Require Import ym.su2_uniqueness.
Require Import ym.su2_multi_clustering.
Require Import ym.su2_reflection_positivity.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import ChallengeSU2InfiniteVolume ChallengeSU2MassGap.
Import DupClustering Z2GaugeExpansion SU2Algebra LatticeSymmetry.
Open Scope R_scope.

Module SU2MassGap.

  (* =======================================================================
     1. Images of the cubes under the lattice symmetries
     ======================================================================= *)

  Lemma box_wf_in : forall n p, In p (su2_box n) -> wf_plaq_4D p.
  Proof.
    intros n p Hp. exact (proj1 (Forall_forall wf_plaq_4D (su2_box n)) (LatticeBoxes.box_wf n) p Hp).
  Qed.

  Lemma plaq_unshift_inj : forall d a b, plaq_unshift d a = plaq_unshift d b -> a = b.
  Proof.
    intros d a b H.
    rewrite <- (plaq_shift_unshift d a), <- (plaq_shift_unshift d b), H. reflexivity.
  Qed.

  Lemma unshift_volume_nodup : forall d n, NoDup (map (plaq_unshift d) (su2_box n)).
  Proof.
    intros d n.
    exact (SU2Covariance.NoDup_map_inj _ _ (plaq_unshift d) (su2_box n)
             (plaq_unshift_inj d) (LatticeBoxes.box_nodup n)).
  Qed.

  Lemma unshift_volume_wf : forall d n,
    Forall wf_plaq_4D (map (plaq_unshift d) (su2_box n)).
  Proof.
    intros d n. apply Forall_forall. intros p Hp. apply in_map_iff in Hp.
    destruct Hp as [q [Hq Hin]]. subst p. apply plaq_unshift_wf. exact (box_wf_in n q Hin).
  Qed.

  Lemma unshift_volume_exhaust : forall d m, exists K : nat,
    forall k, (K <= k)%nat -> incl (su2_box m) (map (plaq_unshift d) (su2_box k)).
  Proof.
    intros d m. exists (S m). intros k Hk p Hp. apply in_map_iff.
    exists (plaq_shift d p). split; [apply plaq_unshift_shift |].
    apply (LatticeBoxes.box_mono (S m) k Hk). apply box_shift. exact Hp.
  Qed.

  Lemma reflect_volume_nodup : forall n, NoDup (map plaq_reflect (su2_box n)).
  Proof.
    intro n. apply LatticeBoxes.NoDup_map_inj_on; [| apply LatticeBoxes.box_nodup].
    intros x y Hx Hy H.
    rewrite <- (plaq_reflect_invol x (box_wf_in n x Hx)),
            <- (plaq_reflect_invol y (box_wf_in n y Hy)), H.
    reflexivity.
  Qed.

  Lemma reflect_volume_wf : forall n, Forall wf_plaq_4D (map plaq_reflect (su2_box n)).
  Proof.
    intro n. apply Forall_forall. intros p Hp. apply in_map_iff in Hp.
    destruct Hp as [q [Hq Hin]]. subst p. apply plaq_reflect_wf. exact (box_wf_in n q Hin).
  Qed.

  Lemma reflect_volume_exhaust : forall m, exists K : nat,
    forall k, (K <= k)%nat -> incl (su2_box m) (map plaq_reflect (su2_box k)).
  Proof.
    intro m. exists (S m). intros k Hk p Hp. apply in_map_iff.
    exists (plaq_reflect p). split; [exact (plaq_reflect_invol p (box_wf_in m p Hp)) |].
    apply (LatticeBoxes.box_mono (S m) k Hk). apply box_reflect. exact Hp.
  Qed.

  (* =======================================================================
     2. Volumes symmetric under the time reflection
     ======================================================================= *)

  Definition b0 (p : Plaq4D) : bool :=
    negb (dir4D_eqb (p4_mu p) D4_t) && (s4_t (p4_site p) =? 0)%Z.

  Definition bP (p : Plaq4D) : bool :=
    (0 <=? s4_t (p4_site p))%Z &&
    (dir4D_eqb (p4_mu p) D4_t || (1 <=? s4_t (p4_site p))%Z).

  Lemma b0_spec : forall p, b0 p = true <-> SU2ReflectionPositivity.plaq0 p.
  Proof.
    intro p. unfold b0, SU2ReflectionPositivity.plaq0.
    rewrite andb_true_iff, negb_true_iff, Z.eqb_eq. split; intros [H1 H2]; split;
      try exact H2.
    - intro Heq. apply (proj2 (dir4D_eqb_spec (p4_mu p) D4_t)) in Heq. congruence.
    - destruct (dir4D_eqb (p4_mu p) D4_t) eqn:He; [| reflexivity].
      apply dir4D_eqb_spec in He. contradiction.
  Qed.

  Lemma bP_spec : forall p, bP p = true <-> SU2ReflectionPositivity.plaqP p.
  Proof.
    intro p. unfold bP, SU2ReflectionPositivity.plaqP.
    rewrite andb_true_iff, orb_true_iff, !Z.leb_le, dir4D_eqb_spec. reflexivity.
  Qed.

  Lemma pos_class : forall p, (0 <= s4_t (p4_site p))%Z ->
    SU2ReflectionPositivity.plaq0 p \/ SU2ReflectionPositivity.plaqP p.
  Proof.
    intros p Ht. destruct (dir4D_eqb (p4_mu p) D4_t) eqn:He.
    - right. split; [exact Ht | left; apply dir4D_eqb_spec; exact He].
    - assert (Hmu : p4_mu p <> D4_t).
      { intro Heq. apply (proj2 (dir4D_eqb_spec (p4_mu p) D4_t)) in Heq. congruence. }
      destruct (Z.eq_dec (s4_t (p4_site p)) 0) as [H0 | H0].
      + left. split; assumption.
      + right. split; [exact Ht | right; lia].
  Qed.

  Lemma plaqP_reflect_neg : forall p, SU2ReflectionPositivity.plaqP p ->
    (s4_t (p4_site (plaq_reflect p)) < 0)%Z.
  Proof.
    intros [[t x y z] m n] [H1 H2]. cbn [p4_site p4_mu s4_t] in *.
    unfold plaq_reflect, site_reflect. cbn [p4_site p4_mu p4_nu s4_t s4_x s4_y s4_z].
    destruct m; cbn [p4_site s4_t]; destruct H2 as [H2 | H2]; try discriminate H2; lia.
  Qed.

  Lemma neg_reflect_plaqP : forall p, (s4_t (p4_site p) < 0)%Z ->
    SU2ReflectionPositivity.plaqP (plaq_reflect p).
  Proof.
    intros [[t x y z] m n] H. cbn [p4_site s4_t] in H.
    unfold SU2ReflectionPositivity.plaqP, plaq_reflect, site_reflect.
    cbn [p4_site p4_mu p4_nu s4_t s4_x s4_y s4_z].
    destruct m; cbn [p4_site p4_mu s4_t]; split; try lia;
      first [left; reflexivity | right; lia].
  Qed.

  Definition S0box (n : nat) : list Plaq4D := filter b0 (su2_box n).
  Definition Spbox (n : nat) : list Plaq4D := filter bP (su2_box n).
  Definition symbox (n : nat) : list Plaq4D :=
    S0box n ++ Spbox n ++ map plaq_reflect (Spbox n).

  Lemma S0box_in : forall n p, In p (S0box n) <->
    In p (su2_box n) /\ SU2ReflectionPositivity.plaq0 p.
  Proof. intros n p. unfold S0box. rewrite filter_In, b0_spec. reflexivity. Qed.

  Lemma Spbox_in : forall n p, In p (Spbox n) <->
    In p (su2_box n) /\ SU2ReflectionPositivity.plaqP p.
  Proof. intros n p. unfold Spbox. rewrite filter_In, bP_spec. reflexivity. Qed.

  Lemma S0box_wf : forall n, Forall wf_plaq_4D (S0box n).
  Proof.
    intro n. apply Forall_forall. intros p Hp. apply S0box_in in Hp.
    exact (box_wf_in n p (proj1 Hp)).
  Qed.

  Lemma S0box_fix : forall n, Forall SU2ReflectionPositivity.plaq0 (S0box n).
  Proof. intro n. apply Forall_forall. intros p Hp. apply S0box_in in Hp. exact (proj2 Hp). Qed.

  Lemma Spbox_wf : forall n, Forall wf_plaq_4D (Spbox n).
  Proof.
    intro n. apply Forall_forall. intros p Hp. apply Spbox_in in Hp.
    exact (box_wf_in n p (proj1 Hp)).
  Qed.

  Lemma Spbox_pos : forall n, Forall SU2ReflectionPositivity.plaqP (Spbox n).
  Proof. intro n. apply Forall_forall. intros p Hp. apply Spbox_in in Hp. exact (proj2 Hp). Qed.

  Lemma symbox_wf : forall n, Forall wf_plaq_4D (symbox n).
  Proof.
    intro n. unfold symbox. apply Forall_app. split; [apply S0box_wf |].
    apply Forall_app. split; [apply Spbox_wf |].
    apply Forall_forall. intros p Hp. apply in_map_iff in Hp. destruct Hp as [q [Hq Hin]].
    subst p. apply plaq_reflect_wf.
    exact (proj1 (Forall_forall wf_plaq_4D (Spbox n)) (Spbox_wf n) q Hin).
  Qed.

  Lemma symbox_nodup : forall n, NoDup (symbox n).
  Proof.
    intro n. unfold symbox.
    apply ProductMeasurePerm.nodup_app.
    - unfold S0box. apply NoDup_filter. apply LatticeBoxes.box_nodup.
    - apply ProductMeasurePerm.nodup_app.
      + unfold Spbox. apply NoDup_filter. apply LatticeBoxes.box_nodup.
      + apply LatticeBoxes.NoDup_map_inj_on.
        * intros x y Hx Hy H. apply Spbox_in in Hx. apply Spbox_in in Hy.
          rewrite <- (plaq_reflect_invol x (box_wf_in n x (proj1 Hx))),
                  <- (plaq_reflect_invol y (box_wf_in n y (proj1 Hy))), H.
          reflexivity.
        * unfold Spbox. apply NoDup_filter. apply LatticeBoxes.box_nodup.
      + intros a Ha Ha'. apply Spbox_in in Ha. destruct Ha as [_ [Ht _]].
        apply in_map_iff in Ha'. destruct Ha' as [q [Hq Hin]]. subst a.
        apply Spbox_in in Hin. pose proof (plaqP_reflect_neg q (proj2 Hin)). lia.
    - intros a Ha Ha'. apply S0box_in in Ha. destruct Ha as [_ [Hmu Ht]].
      apply in_app_or in Ha'. destruct Ha' as [Ha' | Ha'].
      + apply Spbox_in in Ha'. destruct Ha' as [_ [_ [H | H]]]; [contradiction | lia].
      + apply in_map_iff in Ha'. destruct Ha' as [q [Hq Hin]]. subst a.
        apply Spbox_in in Hin. pose proof (plaqP_reflect_neg q (proj2 Hin)). lia.
  Qed.

  Lemma symbox_exhaust : forall m, exists K : nat,
    forall k, (K <= k)%nat -> incl (su2_box m) (symbox k).
  Proof.
    intro m. exists (S m). intros k Hk p Hp. unfold symbox.
    assert (Hpk : In p (su2_box k)).
    { apply (LatticeBoxes.box_mono m k); [lia | exact Hp]. }
    destruct (Z_lt_le_dec (s4_t (p4_site p)) 0) as [Hneg | Hnonneg].
    - apply in_or_app. right. apply in_or_app. right. apply in_map_iff.
      exists (plaq_reflect p). split; [exact (plaq_reflect_invol p (box_wf_in m p Hp)) |].
      apply Spbox_in. split; [| exact (neg_reflect_plaqP p Hneg)].
      apply (LatticeBoxes.box_mono (S m) k Hk). apply box_reflect. exact Hp.
    - apply in_or_app. destruct (pos_class p Hnonneg) as [H0 | HP].
      + left. apply S0box_in. split; assumption.
      + right. apply in_or_app. left. apply Spbox_in. split; assumption.
  Qed.

  Lemma pos_in_symbox : forall n (Q : list Plaq4D),
    incl Q (su2_box n) -> Forall pos_time_plaq Q -> incl Q (S0box n ++ Spbox n).
  Proof.
    intros n Q Hincl Hpos p Hp. apply in_or_app.
    pose proof (proj1 (Forall_forall pos_time_plaq Q) Hpos p Hp) as Ht.
    unfold pos_time_plaq in Ht. destruct (pos_class p Ht) as [H0 | HP].
    - left. apply S0box_in. split; [apply Hincl; exact Hp | exact H0].
    - right. apply Spbox_in. split; [apply Hincl; exact Hp | exact HP].
  Qed.

  (* =======================================================================
     3. Classes of observables
     ======================================================================= *)

  (* bounded uniformly continuous, localized on finitely many canonical plaquettes *)
  Definition LocObs (g : SU2Config -> R) : Prop :=
    su2_bounded_continuous g /\
    exists Q : list Plaq4D, Forall wf_plaq_4D Q /\ su2_local_on g Q.

  (* ... all of them at non-negative times *)
  Definition PosObs (g : SU2Config -> R) : Prop :=
    su2_bounded_continuous g /\
    exists Q : list Plaq4D,
      Forall wf_plaq_4D Q /\ Forall pos_time_plaq Q /\ su2_local_on g Q.

  Lemma pos_loc : forall g, PosObs g -> LocObs g.
  Proof.
    intros g [Hbc [Q [HQ [_ Hloc]]]]. split; [exact Hbc |]. exists Q. split; assumption.
  Qed.

  Lemma local_plus : forall (f g : SU2Config -> R) (P1 P2 : list Plaq4D),
    su2_local_on f P1 -> su2_local_on g P2 ->
    su2_local_on (fun U => f U + g U) (P1 ++ P2).
  Proof.
    intros f g P1 P2 Hf Hg U U' H. rewrite (Hf U U'), (Hg U U'); [reflexivity | |].
    - intros p l Hp Hl. apply (H p l); [apply in_or_app; right; exact Hp | exact Hl].
    - intros p l Hp Hl. apply (H p l); [apply in_or_app; left; exact Hp | exact Hl].
  Qed.

  Lemma loc_mult : forall f g, LocObs f -> LocObs g -> LocObs (fun U => f U * g U).
  Proof.
    intros f g [Hbf [Q1 [HQ1 Hl1]]] [Hbg [Q2 [HQ2 Hl2]]]. split.
    - exact (SU2Continuity.bc_mult f g Hbf Hbg).
    - exists (Q1 ++ Q2). split; [apply Forall_app; split; assumption |].
      exact (SU2MultiClustering.local_mult f g Q1 Q2 Hl1 Hl2).
  Qed.

  Lemma loc_reflect : forall g, LocObs g -> LocObs (obs_reflect g).
  Proof.
    intros g [Hbc [Q [HQ Hloc]]]. split; [exact (bc_reflect g Hbc) |].
    exists (map plaq_reflect Q). split; [| exact (local_reflect g Q HQ Hloc)].
    apply Forall_forall. intros p Hp. apply in_map_iff in Hp. destruct Hp as [q [Hq Hin]].
    subst p. apply plaq_reflect_wf. exact (proj1 (Forall_forall wf_plaq_4D Q) HQ q Hin).
  Qed.

  Lemma iter_shift_list_wf : forall j (Q : list Plaq4D), Forall wf_plaq_4D Q ->
    Forall wf_plaq_4D (map (Nat.iter j (plaq_shift D4_t)) Q).
  Proof.
    intros j Q HQ. apply Forall_forall. intros p Hp. apply in_map_iff in Hp.
    destruct Hp as [q [Hq Hin]]. subst p. apply iter_shift_wf.
    exact (proj1 (Forall_forall wf_plaq_4D Q) HQ q Hin).
  Qed.

  Lemma loc_translate_n : forall j g, LocObs g -> LocObs (obs_translate_n D4_t j g).
  Proof.
    intros j g [Hbc [Q [HQ Hloc]]]. split; [exact (bc_translate_n D4_t j g Hbc) |].
    exists (map (Nat.iter j (plaq_shift D4_t)) Q).
    split; [exact (iter_shift_list_wf j Q HQ) | exact (local_translate_n D4_t j g Q Hloc)].
  Qed.

  Lemma pos_translate_n : forall j g, PosObs g -> PosObs (obs_translate_n D4_t j g).
  Proof.
    intros j g [Hbc [Q [HQ [Hpos Hloc]]]]. split; [exact (bc_translate_n D4_t j g Hbc) |].
    exists (map (Nat.iter j (plaq_shift D4_t)) Q).
    split; [exact (iter_shift_list_wf j Q HQ) |].
    split; [| exact (local_translate_n D4_t j g Q Hloc)].
    apply Forall_forall. intros p Hp. apply in_map_iff in Hp. destruct Hp as [q [Hq Hin]].
    subst p. apply pos_iter_shift. exact (proj1 (Forall_forall pos_time_plaq Q) Hpos q Hin).
  Qed.

  Lemma pos_plus : forall f g, PosObs f -> PosObs g -> PosObs (fun U => f U + g U).
  Proof.
    intros f g [Hbf [Q1 [HQ1 [Hp1 Hl1]]]] [Hbg [Q2 [HQ2 [Hp2 Hl2]]]]. split.
    - exact (SU2Continuity.bc_plus f g Hbf Hbg).
    - exists (Q1 ++ Q2). split; [apply Forall_app; split; assumption |].
      split; [apply Forall_app; split; assumption |].
      exact (local_plus f g Q1 Q2 Hl1 Hl2).
  Qed.

  Lemma pos_scal : forall c g, PosObs g -> PosObs (fun U => c * g U).
  Proof.
    intros c g [Hbc [Q [HQ [Hpos Hloc]]]]. split; [exact (SU2Continuity.bc_scal c g Hbc) |].
    exists Q. split; [exact HQ |]. split; [exact Hpos |].
    intros U U' H. rewrite (Hloc U U' H). reflexivity.
  Qed.

  (* pointwise rules for the translation of observables *)
  Lemma translate_n_mult : forall j (A B : SU2Config -> R) U,
    obs_translate_n D4_t j (fun V => A V * B V) U =
    obs_translate_n D4_t j A U * obs_translate_n D4_t j B U.
  Proof.
    induction j as [| j IH]; intros A B U; [reflexivity |].
    cbn [obs_translate_n]. unfold obs_translate. apply IH.
  Qed.

  Lemma translate_n_minus_const : forall j (A : SU2Config -> R) (c : R) U,
    obs_translate_n D4_t j (fun V => A V - c) U = obs_translate_n D4_t j A U - c.
  Proof.
    induction j as [| j IH]; intros A c U; [reflexivity |].
    cbn [obs_translate_n]. unfold obs_translate. apply IH.
  Qed.

  Lemma translate_n_bound : forall (g : SU2Config -> R) (M : R),
    (forall U, su2_unit_config U -> Rabs (g U) <= M) ->
    forall j U, su2_unit_config U -> Rabs (obs_translate_n D4_t j g U) <= M.
  Proof.
    intros g M Hg. induction j as [| j IH]; intros U HU; [apply Hg; exact HU |].
    cbn [obs_translate_n]. unfold obs_translate. apply IH. apply translate_unit. exact HU.
  Qed.

  (* =======================================================================
     4. The infinite-volume state: existence, symmetries, positivity
     ======================================================================= *)

  Section State.
    Variable beta : R.
    Hypothesis Hbeta : 43008 * Rabs beta <= 1.

    Local Notation infE := (su2_infinite_volume_expect_is beta).

    Lemma loc_exists : forall g, LocObs g -> exists v : R, infE g v.
    Proof.
      intros g [Hbc [Q [HQ Hloc]]].
      exact (SU2InfiniteVolume.su2_thermodynamic_limit beta Q g Hbeta HQ Hloc Hbc).
    Qed.

    (* ---------- TARGET 10b ---------- *)

    Lemma inf_translate : forall (Q : list Plaq4D) (g : SU2Config -> R) (v : R) (d : Dir4D),
      Forall wf_plaq_4D Q -> su2_local_on g Q -> su2_bounded_continuous g ->
      infE g v -> infE (obs_translate d g) v.
    Proof.
      intros Q g v d HQ Hloc Hbc Hv.
      destruct (SU2Uniqueness.haar_seq_exists beta
                  (fun n => map (plaq_unshift d) (su2_box n)) g Hbc) as [w Hw].
      exists w. split.
      - intro n. unfold su2_haar_expect_is.
        apply (SU2HaarLimit.cv_ext
                 (fun k => su2_expect_on (su2_grid k) beta
                             (map (plaq_unshift d) (su2_box n)) g)); [| exact (Hw n)].
        intro k. symmetry. apply SU2Covariance.expect_translate.
      - exact (SU2Uniqueness.su2_infinite_volume_uniqueness beta Q g
                 (fun n => map (plaq_unshift d) (su2_box n)) w v Hbeta HQ Hloc Hbc
                 (unshift_volume_nodup d) (unshift_volume_wf d)
                 (unshift_volume_exhaust d) Hw Hv).
    Qed.

    Lemma inf_reflect : forall (Q : list Plaq4D) (g : SU2Config -> R) (v : R),
      Forall wf_plaq_4D Q -> su2_local_on g Q -> su2_bounded_continuous g ->
      infE g v -> infE (obs_reflect g) v.
    Proof.
      intros Q g v HQ Hloc Hbc Hv.
      destruct (SU2Uniqueness.haar_seq_exists beta
                  (fun n => map plaq_reflect (su2_box n)) g Hbc) as [w Hw].
      exists w. split.
      - intro n. unfold su2_haar_expect_is.
        apply (SU2Uniqueness.cv_ext_from
                 (fun k => su2_expect_on (su2_grid k) beta (map plaq_reflect (su2_box n)) g)
                 _ (w n) 1%nat); [| exact (Hw n)].
        intros k Hk. symmetry.
        exact (SU2Covariance.expect_reflect (su2_grid k) beta (su2_box n) g
                 (SU2HaarGridConj.grid_conj k Hk) (LatticeBoxes.box_wf n)).
      - exact (SU2Uniqueness.su2_infinite_volume_uniqueness beta Q g
                 (fun n => map plaq_reflect (su2_box n)) w v Hbeta HQ Hloc Hbc
                 reflect_volume_nodup reflect_volume_wf reflect_volume_exhaust Hw Hv).
    Qed.

    Lemma loc_reflect_inv : forall g v, LocObs g -> infE g v -> infE (obs_reflect g) v.
    Proof.
      intros g v [Hbc [Q [HQ Hloc]]] Hv. exact (inf_reflect Q g v HQ Hloc Hbc Hv).
    Qed.

    Lemma loc_translate_inv : forall j g v, LocObs g -> infE g v ->
      infE (obs_translate_n D4_t j g) v.
    Proof.
      induction j as [| j IH]; intros g v Hg Hv; [exact Hv |].
      cbn [obs_translate_n].
      destruct (loc_translate_n j g Hg) as [Hbc' [Q' [HQ' Hloc']]].
      exact (inf_translate Q' (obs_translate_n D4_t j g) v D4_t HQ' Hloc' Hbc' (IH g v Hg Hv)).
    Qed.

    (* ---------- TARGET 10c ---------- *)

    Lemma pos_rp : forall g, PosObs g ->
      exists v : R, infE (fun U => obs_reflect g U * g U) v /\ 0 <= v.
    Proof.
      intros g Hg. pose proof Hg as [Hbc [Q [HQ [Hpos Hloc]]]].
      assert (Hloc_prod : LocObs (fun U => obs_reflect g U * g U)).
      { apply loc_mult; [apply loc_reflect |]; apply pos_loc; exact Hg. }
      destruct (loc_exists _ Hloc_prod) as [v Hv].
      exists v. split; [exact Hv |].
      pose proof Hloc_prod as [Hbc2 [Q2 [HQ2 Hloc2]]].
      destruct (SU2Uniqueness.haar_seq_exists beta symbox
                  (fun U => obs_reflect g U * g U) Hbc2) as [w Hw].
      pose proof (SU2Uniqueness.su2_infinite_volume_uniqueness beta Q2
                    (fun U => obs_reflect g U * g U) symbox w v Hbeta HQ2 Hloc2 Hbc2
                    symbox_nodup symbox_wf symbox_exhaust Hw Hv) as Hcv.
      destruct (LatticeBoxes.box_exhaust Q HQ) as [n0 Hn0].
      apply (SU2Uniqueness.cv_nonneg_from w v n0 Hcv). intros k Hk.
      apply (SU2Uniqueness.cv_nonneg_from
               (fun j => su2_expect_on (su2_grid j) beta (symbox k)
                           (fun U => obs_reflect g U * g U))
               (w k) 1%nat (Hw k)).
      intros j Hj. unfold symbox.
      apply (SU2ReflectionPositivity.reflection_positivity_finite (su2_grid j) beta
               (S0box k) (Spbox k) Q g
               (SU2HaarGrid.grid_nonempty j) (SU2HaarGridConj.grid_conj j Hj)
               (S0box_wf k) (S0box_fix k) (Spbox_wf k) (Spbox_pos k)).
      - apply pos_in_symbox; [| exact Hpos].
        intros p Hp. exact (LatticeBoxes.box_mono n0 k Hk p (Hn0 p Hp)).
      - exact Hloc.
    Qed.

    (* ---------- sequences of infinite-volume expectations, without choice ---------- *)

    Lemma inf_seq : forall g : nat -> SU2Config -> R, (forall j, LocObs (g j)) ->
      exists a : nat -> R, forall j, infE (g j) (a j).
    Proof.
      intros g Hg.
      assert (Hc1 : forall j n,
                Cauchy_crit (fun k => su2_expect_on (su2_grid k) beta (su2_box n) (g j))).
      { intros j n. destruct (Hg j) as [Hbc _].
        destruct (SU2HaarLimit.haar_state_exists beta (su2_box n) (g j) Hbc) as [v Hv].
        exact (CV_Cauchy (fun k => su2_expect_on (su2_grid k) beta (su2_box n) (g j))
                 (exist (fun l => Un_cv (fun k => su2_expect_on (su2_grid k) beta
                                                    (su2_box n) (g j)) l) v Hv)). }
      set (hn := fun j n =>
             proj1_sig (R_complete
                          (fun k => su2_expect_on (su2_grid k) beta (su2_box n) (g j))
                          (Hc1 j n))).
      assert (Hhn : forall j n, su2_haar_expect_is beta (su2_box n) (g j) (hn j n)).
      { intros j n.
        exact (proj2_sig (R_complete
                            (fun k => su2_expect_on (su2_grid k) beta (su2_box n) (g j))
                            (Hc1 j n))). }
      assert (Hc2 : forall j, Cauchy_crit (hn j)).
      { intro j. destruct (loc_exists (g j) (Hg j)) as [v [vn [Hvn Hcv]]].
        assert (Hcv' : Un_cv (hn j) v).
        { apply (SU2HaarLimit.cv_ext vn); [| exact Hcv]. intro n.
          exact (SU2Uniqueness.haar_unique beta (su2_box n) (g j) (vn n) (hn j n)
                   (Hvn n) (Hhn j n)). }
        exact (CV_Cauchy (hn j) (exist (fun l => Un_cv (hn j) l) v Hcv')). }
      exists (fun j => proj1_sig (R_complete (hn j) (Hc2 j))).
      intro j. exists (hn j). split; [intro n; apply Hhn |].
      exact (proj2_sig (R_complete (hn j) (Hc2 j))).
    Qed.

    (* ---------- the Osterwalder-Schrader form ---------- *)

    Lemma form_sym : forall X Y b, PosObs X -> PosObs Y ->
      infE (fun U => obs_reflect X U * Y U) b ->
      infE (fun U => obs_reflect Y U * X U) b.
    Proof.
      intros X Y b HX HY Hb.
      assert (Hl : LocObs (fun U => obs_reflect X U * Y U)).
      { apply loc_mult; [apply loc_reflect |]; apply pos_loc; assumption. }
      pose proof (loc_reflect_inv _ b Hl Hb) as H.
      apply (SU2Uniqueness.inf_ext beta
               (obs_reflect (fun U => obs_reflect X U * Y U))); [| exact H].
      intro U.
      change (obs_reflect (fun V => obs_reflect X V * Y V) U)
        with (obs_reflect (obs_reflect X) U * obs_reflect Y U).
      rewrite obs_reflect_invol. ring.
    Qed.

    Lemma form_cs : forall X Y a0 b c, PosObs X -> PosObs Y ->
      infE (fun U => obs_reflect X U * X U) a0 ->
      infE (fun U => obs_reflect X U * Y U) b ->
      infE (fun U => obs_reflect Y U * Y U) c ->
      b * b <= a0 * c.
    Proof.
      intros X Y a0 b c HX HY Ha0 Hb Hc.
      assert (Hc0 : 0 <= c).
      { destruct (pos_rp Y HY) as [v [Hv Hv0]].
        rewrite (SU2Uniqueness.inf_unique beta _ c v Hc Hv). exact Hv0. }
      apply CauchySchwarzGap.quad_disc; [exact Hc0 |]. intro lam.
      assert (HZ : PosObs (fun U => X U + lam * Y U)).
      { apply pos_plus; [exact HX | apply pos_scal; exact HY]. }
      destruct (pos_rp _ HZ) as [vz [Hvz Hvz0]].
      assert (Hexp : infE (fun U => obs_reflect (fun V => X V + lam * Y V) U
                                    * (X U + lam * Y U))
                          (a0 + 2 * lam * b + lam * lam * c)).
      { apply (SU2Uniqueness.inf_ext beta
                 (fun U => (obs_reflect X U * X U + lam * (obs_reflect X U * Y U))
                           + (lam * (obs_reflect Y U * X U)
                              + (lam * lam) * (obs_reflect Y U * Y U)))).
        - intro U. unfold obs_reflect. ring.
        - replace (a0 + 2 * lam * b + lam * lam * c)
            with ((a0 + lam * b) + (lam * b + (lam * lam) * c)) by ring.
          apply (SU2Uniqueness.inf_plus beta
                   (fun U => obs_reflect X U * X U + lam * (obs_reflect X U * Y U))
                   (fun U => lam * (obs_reflect Y U * X U)
                             + (lam * lam) * (obs_reflect Y U * Y U))).
          + apply (SU2Uniqueness.inf_plus beta
                     (fun U => obs_reflect X U * X U)
                     (fun U => lam * (obs_reflect X U * Y U))); [exact Ha0 |].
            exact (SU2Uniqueness.inf_scal beta lam
                     (fun U => obs_reflect X U * Y U) b Hb).
          + apply (SU2Uniqueness.inf_plus beta
                     (fun U => lam * (obs_reflect Y U * X U))
                     (fun U => (lam * lam) * (obs_reflect Y U * Y U))).
            * exact (SU2Uniqueness.inf_scal beta lam
                       (fun U => obs_reflect Y U * X U) b (form_sym X Y b HX HY Hb)).
            * exact (SU2Uniqueness.inf_scal beta (lam * lam)
                       (fun U => obs_reflect Y U * Y U) c Hc). }
      rewrite (SU2Uniqueness.inf_unique beta _ _ vz Hexp Hvz). exact Hvz0.
    Qed.
  End State.

  (* TARGET 10b *)
  Theorem su2_infinite_volume_symmetry : Challenge_SU2Gauge4D_InfiniteVolumeSymmetry.
  Proof.
    intros beta P f v Hbeta HP Hloc Hbc Hv. split.
    - intro d. exact (inf_translate beta Hbeta P f v d HP Hloc Hbc Hv).
    - exact (inf_reflect beta Hbeta P f v HP Hloc Hbc Hv).
  Qed.

  (* TARGET 10c *)
  Theorem su2_reflection_positivity : Challenge_SU2Gauge4D_ReflectionPositivity.
  Proof.
    intros beta P f Hbeta HP Hpos Hloc Hbc.
    apply (pos_rp beta Hbeta f). split; [exact Hbc |]. exists P. repeat split; assumption.
  Qed.

  (* =======================================================================
     5. The mass gap
     ======================================================================= *)

  Section Gap.
    Variables beta mu : R.
    Hypothesis Hmu : 0 <= mu.
    Hypothesis Hsmall : 168 * Rabs beta <= exp (- mu).
    Hypothesis Hbeta : 43008 * Rabs beta <= 1.
    Variable P : list Plaq4D.
    Hypothesis HP : Forall wf_plaq_4D P.
    Hypothesis Hpos : Forall pos_time_plaq P.
    Variable f : SU2Config -> R.
    Hypothesis Hloc : su2_local_on f P.
    Hypothesis Hbc : su2_bounded_continuous f.
    Variable vf : R.
    Hypothesis Hvf : su2_infinite_volume_expect_is beta f vf.

    Local Notation infE := (su2_infinite_volume_expect_is beta).
    Local Notation tauN := (obs_translate_n D4_t).

    (* the component of f orthogonal to the vacuum *)
    Definition psi (U : SU2Config) : R := f U - vf.

    Lemma f_pos : PosObs f.
    Proof. split; [exact Hbc |]. exists P. repeat split; assumption. Qed.

    Lemma psi_local : su2_local_on psi P.
    Proof. intros U U' H. unfold psi. rewrite (Hloc U U' H). reflexivity. Qed.

    Lemma psi_bc : su2_bounded_continuous psi.
    Proof.
      exact (SU2Continuity.bc_minus f (fun _ => vf) Hbc (SU2Continuity.bc_const vf)).
    Qed.

    Lemma psi_pos : PosObs psi.
    Proof.
      split; [exact psi_bc |]. exists P.
      split; [exact HP |]. split; [exact Hpos | exact psi_local].
    Qed.

    Lemma psi_zero : infE psi 0.
    Proof.
      apply (SU2Uniqueness.inf_ext beta (fun U => f U + - vf)).
      - intro U. unfold psi. ring.
      - replace 0 with (vf + - vf) by ring.
        exact (SU2Uniqueness.inf_plus beta f (fun _ => - vf) vf (- vf) Hvf
                 (SU2Uniqueness.inf_const beta (- vf))).
    Qed.

    Lemma tau_psi : forall j U, tauN j psi U = tauN j f U - vf.
    Proof. intros j U. exact (translate_n_minus_const j f vf U). Qed.

    (* a_j = (psi, T^j psi) *)
    Variable a : nat -> R.
    Hypothesis Ha : forall j, infE (fun U => obs_reflect psi U * tauN j psi U) (a j).

    Lemma Ha0 : infE (fun U => obs_reflect psi U * psi U) (a 0%nat).
    Proof. exact (Ha 0%nat). Qed.

    Lemma a_double : forall j,
      infE (fun U => obs_reflect (tauN j psi) U * tauN j psi U) (a (2 * j)%nat).
    Proof.
      intro j.
      assert (Hl : LocObs (fun U => obs_reflect (tauN j psi) U * tauN j psi U)).
      { apply loc_mult; [apply loc_reflect |]; apply loc_translate_n; apply pos_loc;
          exact psi_pos. }
      destruct (loc_exists beta Hbeta _ Hl) as [v Hv].
      pose proof (loc_translate_inv beta Hbeta j _ v Hl Hv) as Ht.
      assert (Hv2 : infE (fun U => obs_reflect psi U * tauN (2 * j) psi U) v).
      { apply (SU2Uniqueness.inf_ext beta
                 (tauN j (fun U => obs_reflect (tauN j psi) U * tauN j psi U)));
          [| exact Ht].
        intro U. rewrite translate_n_mult, translate_reflect_translate.
        rewrite <- obs_translate_n_add.
        replace (j + j)%nat with (2 * j)%nat by lia. reflexivity. }
      rewrite (SU2Uniqueness.inf_unique beta _ (a (2 * j)%nat) v (Ha (2 * j)%nat) Hv2).
      exact Hv.
    Qed.

    Lemma a0_nonneg : 0 <= a 0%nat.
    Proof.
      destruct (pos_rp beta Hbeta psi psi_pos) as [v [Hv Hv0]].
      rewrite (SU2Uniqueness.inf_unique beta _ (a 0%nat) v Ha0 Hv). exact Hv0.
    Qed.

    Lemma a_even_nonneg : forall j, 0 <= a (2 * j)%nat.
    Proof.
      intro j.
      destruct (pos_rp beta Hbeta (tauN j psi) (pos_translate_n j psi psi_pos))
        as [v [Hv Hv0]].
      rewrite (SU2Uniqueness.inf_unique beta _ (a (2 * j)%nat) v (a_double j) Hv).
      exact Hv0.
    Qed.

    Lemma a_cs : forall j, a j * a j <= a 0%nat * a (2 * j)%nat.
    Proof.
      intro j.
      exact (form_cs beta Hbeta psi (tauN j psi) (a 0%nat) (a j) (a (2 * j)%nat)
               psi_pos (pos_translate_n j psi psi_pos) Ha0 (Ha j) (a_double j)).
    Qed.

    (* clustering: |a_j| <= C exp(- mu/2)^j *)
    Lemma a_decay : forall M2 : R,
      (forall U, su2_unit_config U -> Rabs (psi U) <= M2) ->
      forall j,
        Rabs (a j)
        <= 4 * (Rmax M2 1 * Rmax M2 1) * (INR (length P) * INR (length P)) * exp mu
           * exp (- (mu / 2)) ^ j.
    Proof.
      intros M2 HM2 j.
      set (c2 := Rmax M2 1).
      assert (Hc1 : 1 <= c2) by apply Rmax_r.
      assert (HcM : M2 <= c2) by apply Rmax_l.
      assert (Hic : 0 < / c2) by (apply Rinv_0_lt_compat; lra).
      set (P1 := map plaq_reflect P).
      set (P2 := map (Nat.iter j (plaq_shift D4_t)) P).
      set (X1 := fun U : SU2Config => / c2 * obs_reflect psi U).
      set (Y1 := fun U : SU2Config => / c2 * tauN j psi U).
      assert (HP1 : Forall wf_plaq_4D P1).
      { apply Forall_forall. intros p Hp. apply in_map_iff in Hp.
        destruct Hp as [q [Hq Hin]]. subst p. apply plaq_reflect_wf.
        exact (proj1 (Forall_forall wf_plaq_4D P) HP q Hin). }
      assert (HP2 : Forall wf_plaq_4D P2) by exact (iter_shift_list_wf j P HP).
      assert (HX1loc : su2_local_on X1 P1).
      { intros U U' H. unfold X1.
        rewrite (local_reflect psi P HP psi_local U U' H). reflexivity. }
      assert (HY1loc : su2_local_on Y1 P2).
      { intros U U' H. unfold Y1.
        rewrite (local_translate_n D4_t j psi P psi_local U U' H). reflexivity. }
      assert (HX1bc : su2_bounded_continuous X1).
      { exact (SU2Continuity.bc_scal (/ c2) (obs_reflect psi) (bc_reflect psi psi_bc)). }
      assert (HY1bc : su2_bounded_continuous Y1).
      { exact (SU2Continuity.bc_scal (/ c2) (tauN j psi) (bc_translate_n D4_t j psi psi_bc)). }
      assert (Hscale : forall x, Rabs x <= M2 -> Rabs (/ c2 * x) <= 1).
      { intros x Hx. rewrite Rabs_mult, (Rabs_pos_eq (/ c2)) by lra.
        apply Rmult_le_reg_l with c2; [lra |].
        rewrite <- Rmult_assoc, Rinv_r by lra. lra. }
      assert (HX1bd : forall U, su2_unit_config U -> Rabs (X1 U) <= 1).
      { intros U HU. unfold X1. apply Hscale. unfold obs_reflect. apply HM2.
        apply reflect_unit. exact HU. }
      assert (HY1bd : forall U, su2_unit_config U -> Rabs (Y1 U) <= 1).
      { intros U HU. unfold Y1. apply Hscale.
        exact (translate_n_bound psi M2 HM2 j U HU). }
      destruct (SU2MultiClustering.su2_multi_plaquette_clustering beta mu P1 P2 X1 Y1
                  Hmu Hsmall Hbeta HP1 HP2 HX1loc HY1loc HX1bc HY1bc HX1bd HY1bd)
        as [v12 [v1 [v2 [H12 [H1 [H2 Hcl]]]]]].
      (* v1 = 0 *)
      assert (Hv1 : v1 = 0).
      { pose proof (loc_reflect_inv beta Hbeta psi 0 (pos_loc psi psi_pos) psi_zero) as Hr.
        pose proof (SU2Uniqueness.inf_scal beta (/ c2) (obs_reflect psi) 0 Hr) as Hs.
        rewrite (SU2Uniqueness.inf_unique beta X1 v1 (/ c2 * 0) H1 Hs). ring. }
      (* v12 = a_j / c2^2 *)
      assert (Hv12 : v12 = / c2 * / c2 * a j).
      { apply (SU2Uniqueness.inf_unique beta (fun U => X1 U * Y1 U) v12 _ H12).
        apply (SU2Uniqueness.inf_ext beta
                 (fun U => (/ c2 * / c2) * (obs_reflect psi U * tauN j psi U))).
        - intro U. unfold X1, Y1. ring.
        - exact (SU2Uniqueness.inf_scal beta (/ c2 * / c2)
                   (fun U => obs_reflect psi U * tauN j psi U) (a j) (Ha j)). }
      (* the double sum *)
      set (T := exp mu * exp (- (mu / 2)) ^ j).
      assert (HT : forall p q, In p P -> In q P ->
                exp (- mu * (plaq4D_dist (plaq_reflect p)
                                 (Nat.iter j (plaq_shift D4_t) q) - 1)) <= T).
      { intros p q Hp Hq.
        pose proof (dist_reflect_shift p q j
                      (proj1 (Forall_forall wf_plaq_4D P) HP p Hp)
                      (proj1 (Forall_forall pos_time_plaq P) Hpos p Hp)
                      (proj1 (Forall_forall pos_time_plaq P) Hpos q Hq)) as Hd.
        unfold T. rewrite Z2GaugeClustering.exp_pow_INR, <- exp_plus.
        apply Z2GaugeClustering.exp_le.
        set (dd := plaq4D_dist (plaq_reflect p) (Nat.iter j (plaq_shift D4_t) q)) in *.
        assert (Hprod : 0 <= mu * (dd - INR j / 2)) by (apply Rmult_le_pos; lra).
        lra. }
      assert (Hsum :
        fold_right Rplus 0
          (map (fun p => fold_right Rplus 0
                           (map (fun q => exp (- mu * (plaq4D_dist p q - 1))) P2)) P1)
        <= INR (length P) * (INR (length P) * T)).
      { change (rsum P1 (fun p => rsum P2 (fun q => exp (- mu * (plaq4D_dist p q - 1))))
                <= INR (length P) * (INR (length P) * T)).
        unfold P1. rewrite rsum_map.
        rewrite <- (ProductMeasure.rsum_const P (INR (length P) * T)).
        apply rsum_le. intros p Hp. unfold P2. rewrite rsum_map.
        rewrite <- (ProductMeasure.rsum_const P T).
        apply rsum_le. intros q Hq. exact (HT p q Hp Hq). }
      rewrite Hv1, Hv12 in Hcl.
      replace (/ c2 * / c2 * a j - 0 * v2) with (/ c2 * / c2 * a j) in Hcl by ring.
      rewrite Rabs_mult, (Rabs_pos_eq (/ c2 * / c2)) in Hcl
        by (apply Rmult_le_pos; lra).
      assert (Hbound : / c2 * / c2 * Rabs (a j) <= 4 * (INR (length P) * (INR (length P) * T)))
        by lra.
      assert (Hcc : 0 < c2 * c2) by (apply Rmult_lt_0_compat; lra).
      assert (Hres : Rabs (a j) <= c2 * c2 * (4 * (INR (length P) * (INR (length P) * T)))).
      { apply Rmult_le_reg_l with (/ c2 * / c2); [apply Rmult_lt_0_compat; lra |].
        replace (/ c2 * / c2 * (c2 * c2 * (4 * (INR (length P) * (INR (length P) * T)))))
          with (4 * (INR (length P) * (INR (length P) * T))) by (field; lra).
        exact Hbound. }
      eapply Rle_trans; [exact Hres |]. unfold T. apply Req_le. ring.
    Qed.

    (* a_j in terms of f *)
    Lemma a_value : forall j vj,
      infE (fun U => obs_reflect f U * tauN j f U) vj -> a j = vj - vf * vf.
    Proof.
      intros j vj Hvj.
      apply (SU2Uniqueness.inf_unique beta
               (fun U => obs_reflect psi U * tauN j psi U) (a j) _ (Ha j)).
      apply (SU2Uniqueness.inf_ext beta
               (fun U => (obs_reflect f U * tauN j f U + (- vf) * obs_reflect f U)
                         + ((- vf) * tauN j f U + vf * vf))).
      - intro U. rewrite tau_psi. unfold obs_reflect, psi. ring.
      - replace (vj - vf * vf) with ((vj + (- vf) * vf) + ((- vf) * vf + vf * vf)) by ring.
        apply (SU2Uniqueness.inf_plus beta
                 (fun U => obs_reflect f U * tauN j f U + (- vf) * obs_reflect f U)
                 (fun U => (- vf) * tauN j f U + vf * vf)).
        + apply (SU2Uniqueness.inf_plus beta
                   (fun U => obs_reflect f U * tauN j f U)
                   (fun U => (- vf) * obs_reflect f U)); [exact Hvj |].
          exact (SU2Uniqueness.inf_scal beta (- vf) (obs_reflect f) vf
                   (loc_reflect_inv beta Hbeta f vf (pos_loc f f_pos) Hvf)).
        + apply (SU2Uniqueness.inf_plus beta
                   (fun U => (- vf) * tauN j f U) (fun _ => vf * vf)).
          * exact (SU2Uniqueness.inf_scal beta (- vf) (tauN j f) vf
                     (loc_translate_inv beta Hbeta j f vf (pos_loc f f_pos) Hvf)).
          * exact (SU2Uniqueness.inf_const beta (vf * vf)).
    Qed.

    Theorem gap_bound : forall k : nat,
      0 <= a 0%nat /\ Rabs (a k) <= exp (- (mu / 2) * INR k) * a 0%nat.
    Proof.
      intro k. split; [exact a0_nonneg |].
      destruct psi_bc as [[M2 HM2] _].
      pose proof (CauchySchwarzGap.cs_gap a
                    (4 * (Rmax M2 1 * Rmax M2 1) * (INR (length P) * INR (length P)) * exp mu)
                    (exp (- (mu / 2)))
                    a0_nonneg a_even_nonneg a_cs (exp_pos (- (mu / 2)))
                    (a_decay M2 HM2) k) as H.
      rewrite Z2GaugeClustering.exp_pow_INR in H.
      replace (- (mu / 2) * INR k) with (INR k * - (mu / 2)) by ring.
      exact H.
    Qed.

    (* (T^j psi, T^j psi) = (psi, T^{2j} psi) <= exp(- mu j) (psi, psi) *)
    Lemma diag_bound : forall (v0 : R) (j : nat) (w : R),
      infE (fun U => obs_reflect f U * f U) v0 ->
      infE (fun U => obs_reflect (tauN j psi) U * tauN j psi U) w ->
      0 <= w /\ w <= exp (- mu * INR j) * (v0 - vf * vf).
    Proof.
      intros v0 j w Hv0 Hw.
      pose proof (SU2Uniqueness.inf_unique beta _ w (a (2 * j)%nat) Hw (a_double j)) as E.
      pose proof (gap_bound (2 * j)%nat) as [_ Hk].
      pose proof (a_even_nonneg j) as Hn.
      pose proof (a_value 0%nat v0 Hv0) as E0.
      rewrite Rabs_pos_eq in Hk by exact Hn.
      rewrite E. split; [exact Hn |].
      rewrite <- E0.
      replace (- mu * INR j) with (- (mu / 2) * INR (2 * j)); [exact Hk |].
      rewrite mult_INR. simpl. field.
    Qed.
  End Gap.

  (* (phi, T^j psi) in terms of f and g *)
  Lemma form_value : forall (beta : R), 43008 * Rabs beta <= 1 ->
    forall (f g : SU2Config -> R) (vf vg : R) (j : nat) (vj : R),
      PosObs f -> PosObs g ->
      su2_infinite_volume_expect_is beta f vf ->
      su2_infinite_volume_expect_is beta g vg ->
      su2_infinite_volume_expect_is beta
        (fun U => obs_reflect f U * obs_translate_n D4_t j g U) vj ->
      su2_infinite_volume_expect_is beta
        (fun U => obs_reflect (psi f vf) U * obs_translate_n D4_t j (psi g vg) U)
        (vj - vf * vg).
  Proof.
    intros beta Hbeta f g vf vg j vj Hf Hg Hvf Hvg Hvj.
    apply (SU2Uniqueness.inf_ext beta
             (fun U => (obs_reflect f U * obs_translate_n D4_t j g U
                        + (- vg) * obs_reflect f U)
                       + ((- vf) * obs_translate_n D4_t j g U + vf * vg))).
    - intro U. rewrite tau_psi. unfold obs_reflect, psi. ring.
    - replace (vj - vf * vg) with ((vj + (- vg) * vf) + ((- vf) * vg + vf * vg)) by ring.
      apply (SU2Uniqueness.inf_plus beta
               (fun U => obs_reflect f U * obs_translate_n D4_t j g U
                         + (- vg) * obs_reflect f U)
               (fun U => (- vf) * obs_translate_n D4_t j g U + vf * vg)).
      + apply (SU2Uniqueness.inf_plus beta
                 (fun U => obs_reflect f U * obs_translate_n D4_t j g U)
                 (fun U => (- vg) * obs_reflect f U)); [exact Hvj |].
        exact (SU2Uniqueness.inf_scal beta (- vg) (obs_reflect f) vf
                 (loc_reflect_inv beta Hbeta f vf (pos_loc f Hf) Hvf)).
      + apply (SU2Uniqueness.inf_plus beta
                 (fun U => (- vf) * obs_translate_n D4_t j g U) (fun _ => vf * vg)).
        * exact (SU2Uniqueness.inf_scal beta (- vf) (obs_translate_n D4_t j g) vg
                   (loc_translate_inv beta Hbeta j g vg (pos_loc g Hg) Hvg)).
        * exact (SU2Uniqueness.inf_const beta (vf * vg)).
  Qed.

  (* TARGET 10e *)
  Theorem su2_transfer_matrix_mass_gap : Challenge_SU2Gauge4D_TransferMatrixMassGap.
  Proof.
    intros beta mu P f k Hmu Hsmall Hbeta HP Hpos Hloc Hbc.
    assert (Hf : PosObs f) by (split; [exact Hbc |]; exists P; repeat split; assumption).
    destruct (loc_exists beta Hbeta f (pos_loc f Hf)) as [vf Hvf].
    assert (Hl0 : LocObs (fun U => obs_reflect f U * f U)).
    { apply loc_mult; [apply loc_reflect |]; apply pos_loc; exact Hf. }
    assert (Hlk : LocObs (fun U => obs_reflect f U * obs_translate_n D4_t k f U)).
    { apply loc_mult; [apply loc_reflect | apply loc_translate_n]; apply pos_loc; exact Hf. }
    destruct (loc_exists beta Hbeta _ Hl0) as [v0 Hv0].
    destruct (loc_exists beta Hbeta _ Hlk) as [vk Hvk].
    exists v0, vk, vf.
    split; [exact Hv0 |]. split; [exact Hvk |]. split; [exact Hvf |].
    (* the sequence a_j = (psi, T^j psi) *)
    assert (Hpsi : PosObs (psi f vf)) by exact (psi_pos P HP Hpos f Hloc Hbc vf).
    destruct (inf_seq beta Hbeta
                (fun j U => obs_reflect (psi f vf) U * obs_translate_n D4_t j (psi f vf) U))
      as [a Ha].
    { intro j. apply loc_mult; [apply loc_reflect | apply loc_translate_n]; apply pos_loc;
        exact Hpsi. }
    pose proof (gap_bound beta mu Hmu Hsmall Hbeta P HP Hpos f Hloc Hbc vf Hvf a Ha k)
      as [H0 Hk].
    pose proof (a_value beta Hbeta P HP Hpos f Hloc Hbc vf Hvf a Ha 0%nat v0 Hv0) as E0.
    pose proof (a_value beta Hbeta P HP Hpos f Hloc Hbc vf Hvf a Ha k vk Hvk) as Ek.
    rewrite E0 in H0, Hk. rewrite Ek in Hk. split; [exact H0 | exact Hk].
  Qed.

  (* TARGET 10f *)
  Theorem su2_transfer_matrix_norm_bound : Challenge_SU2Gauge4D_TransferMatrixNormBound.
  Proof.
    intros beta mu P Q f g k Hmu Hsmall Hbeta HP HPpos HQ HQpos Hlf Hlg Hbf Hbg.
    assert (Hf : PosObs f) by (split; [exact Hbf |]; exists P; repeat split; assumption).
    assert (Hg : PosObs g) by (split; [exact Hbg |]; exists Q; repeat split; assumption).
    destruct (loc_exists beta Hbeta f (pos_loc f Hf)) as [vf Hvf].
    destruct (loc_exists beta Hbeta g (pos_loc g Hg)) as [vg Hvg].
    assert (Hlff : LocObs (fun U => obs_reflect f U * f U)).
    { apply loc_mult; [apply loc_reflect |]; apply pos_loc; exact Hf. }
    assert (Hlgg : LocObs (fun U => obs_reflect g U * g U)).
    { apply loc_mult; [apply loc_reflect |]; apply pos_loc; exact Hg. }
    assert (Hlk : LocObs (fun U => obs_reflect f U * obs_translate_n D4_t k g U)).
    { apply loc_mult; [apply loc_reflect | apply loc_translate_n]; apply pos_loc;
        assumption. }
    destruct (loc_exists beta Hbeta _ Hlff) as [vff Hvff].
    destruct (loc_exists beta Hbeta _ Hlgg) as [vgg Hvgg].
    destruct (loc_exists beta Hbeta _ Hlk) as [vk Hvk].
    exists vff, vgg, vk, vf, vg.
    split; [exact Hvff |]. split; [exact Hvgg |]. split; [exact Hvk |].
    split; [exact Hvf |]. split; [exact Hvg |].
    assert (Hpf : PosObs (psi f vf)) by exact (psi_pos P HP HPpos f Hlf Hbf vf).
    assert (Hpg : PosObs (psi g vg)) by exact (psi_pos Q HQ HQpos g Hlg Hbg vg).
    (* (phi, phi), (phi, T^k psi) and (T^k psi, T^k psi) *)
    pose proof (form_value beta Hbeta f f vf vf 0%nat vff Hf Hf Hvf Hvf Hvff) as Hphi.
    pose proof (form_value beta Hbeta f g vf vg k vk Hf Hg Hvf Hvg Hvk) as Hb.
    assert (Hlw : LocObs (fun U => obs_reflect (obs_translate_n D4_t k (psi g vg)) U
                                   * obs_translate_n D4_t k (psi g vg) U)).
    { apply loc_mult; [apply loc_reflect |]; apply loc_translate_n; apply pos_loc;
        exact Hpg. }
    destruct (loc_exists beta Hbeta _ Hlw) as [w Hw].
    pose proof (form_cs beta Hbeta (psi f vf) (obs_translate_n D4_t k (psi g vg))
                  (vff - vf * vf) (vk - vf * vg) w
                  Hpf (pos_translate_n k (psi g vg) Hpg) Hphi Hb Hw) as Hcs.
    (* (phi, phi) >= 0 *)
    assert (Hphi0 : 0 <= vff - vf * vf).
    { destruct (pos_rp beta Hbeta (psi f vf) Hpf) as [v [Hv Hv0]].
      rewrite (SU2Uniqueness.inf_unique beta _ (vff - vf * vf) v Hphi Hv). exact Hv0. }
    (* (T^k psi, T^k psi) <= exp(- mu k) (psi, psi) *)
    destruct (inf_seq beta Hbeta
                (fun j U => obs_reflect (psi g vg) U * obs_translate_n D4_t j (psi g vg) U))
      as [a Ha].
    { intro j. apply loc_mult; [apply loc_reflect | apply loc_translate_n]; apply pos_loc;
        exact Hpg. }
    pose proof (diag_bound beta mu Hmu Hsmall Hbeta Q HQ HQpos g Hlg Hbg vg Hvg a Ha
                  vgg k w Hvgg Hw) as [Hw0 Hwk].
    eapply Rle_trans; [exact Hcs |].
    replace (exp (- mu * INR k) * ((vff - vf * vf) * (vgg - vg * vg)))
      with ((vff - vf * vf) * (exp (- mu * INR k) * (vgg - vg * vg))) by ring.
    apply Rmult_le_compat_l; [exact Hphi0 | exact Hwk].
  Qed.

End SU2MassGap.
