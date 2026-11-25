(* =========================================================================
   ym/su2_haar_limit.v

   The Gibbs state of the 4D SU(2) Wilson lattice gauge theory with respect
   to the Haar measure (TARGETS 8c, 8d, 8e), proved directly for the frozen
   objects of `verification/ChallengeSU2Gauge.v`.  The Haar measure of SU(2)
   is realized there as the limit of the uniform distributions on the dyadic
   Hopf grids `su2_grid n`.

     8c  For every beta, every finite plaquette list Lambda and every bounded
         uniformly continuous observable F, the grid expectations of F
         converge.  Numerator and denominator are normalized grid averages
         of bounded uniformly continuous functions (ym/su2_continuity.v), so
         both converge (ym/su2_haar_grid.v), and the denominators are
         bounded below by exp(- |beta| |Lambda|) > 0.
     8d  The clustering bound of Target 8a holds for every grid, hence for
         the limits.
     8e  The area-law bound of Target 8b holds for every grid of level
         n >= 1 (these grids are invariant under q |-> - q), hence for the
         limit.

   Depends ONLY on Coq stdlib + the frozen challenge files
   + rg.dup_clustering + rg.product_measure + ym.z2_gauge_clustering
   + ym.su2_algebra + ym.su2_clustering + ym.su2_area_law
   + ym.su2_continuity + ym.su2_haar_grid.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.su2_algebra.
Require Import ym.su2_clustering.
Require Import ym.su2_area_law.
Require Import ym.su2_continuity.
Require Import ym.su2_haar_grid.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import DupClustering Z2GaugeExpansion SU2Algebra.
Open Scope R_scope.

Module SU2HaarLimit.

  (* =======================================================================
     1. Limits of real sequences
     ======================================================================= *)

  Lemma cv_ext : forall (u v : nat -> R) (l : R),
    (forall n, u n = v n) -> Un_cv u l -> Un_cv v l.
  Proof.
    intros u v l H Hu eps Heps. destruct (Hu eps Heps) as [N HN].
    exists N. intros n Hn. rewrite <- H. apply HN. exact Hn.
  Qed.

  (* a bound that holds from some index on passes to the limit *)
  Lemma cv_bound : forall (u : nat -> R) (l B : R) (n0 : nat),
    Un_cv u l -> (forall n, (n0 <= n)%nat -> Rabs (u n) <= B) -> Rabs l <= B.
  Proof.
    intros u l B n0 Hcv Hb.
    destruct (Rle_lt_dec (Rabs l) B) as [H | H]; [exact H | exfalso].
    assert (Heps : (Rabs l - B) / 2 > 0) by lra.
    destruct (Hcv _ Heps) as [N HN].
    pose proof (HN (Nat.max N n0) (Nat.le_max_l N n0)) as H1.
    pose proof (Hb (Nat.max N n0) (Nat.le_max_r N n0)) as H2.
    unfold R_dist in H1.
    pose proof (Rabs_triang (u (Nat.max N n0)) (l - u (Nat.max N n0))) as Ht.
    replace (u (Nat.max N n0) + (l - u (Nat.max N n0))) with l in Ht by ring.
    rewrite (Rabs_minus_sym l (u (Nat.max N n0))) in Ht. lra.
  Qed.

  Lemma cv_lower : forall (u : nat -> R) (l c : R),
    Un_cv u l -> (forall n, c <= u n) -> c <= l.
  Proof.
    intros u l c Hcv Hc.
    destruct (Rle_lt_dec c l) as [H | H]; [exact H | exfalso].
    assert (Heps : (c - l) / 2 > 0) by lra.
    destruct (Hcv _ Heps) as [N HN].
    pose proof (HN N (Nat.le_refl N)) as H1. pose proof (Hc N) as H2.
    unfold R_dist in H1. apply Rabs_def2 in H1. lra.
  Qed.

  Lemma cv_div : forall (u v : nat -> R) (lu lv : R),
    Un_cv u lu -> Un_cv v lv -> lv <> 0 -> Un_cv (fun n => u n / v n) (lu / lv).
  Proof.
    intros u v lu lv Hu Hv Hlv. unfold Rdiv.
    apply (CV_mult u (fun n => / v n) lu (/ lv)); [exact Hu |].
    assert (Hc : continuity_pt (inv_fct id) lv).
    { apply continuity_pt_inv; [| exact Hlv].
      apply derivable_continuous_pt. apply derivable_pt_id. }
    exact (continuity_seq (inv_fct id) v lv Hc Hv).
  Qed.

  (* =======================================================================
     2. Bounds on the action
     ======================================================================= *)

  Lemma plaq_sum_bound : forall (U : SU2Config) (L : list Plaq4D),
    su2_unit_config U ->
    Rabs (fold_right Rplus 0 (map (su2_plaq U) L)) <= INR (length L).
  Proof.
    intros U L HU. induction L as [| p L IH].
    - cbn [map fold_right length INR]. rewrite Rabs_R0. apply Rle_refl.
    - cbn [map fold_right length]. rewrite S_INR.
      eapply Rle_trans; [apply Rabs_triang |].
      pose proof (plaq_bound U p HU) as [H1 H2].
      assert (H3 : Rabs (su2_plaq U p) <= 1) by (apply Rabs_le; lra).
      lra.
  Qed.

  Lemma action_bound : forall (beta : R) (Lambda : list Plaq4D) (U : SU2Config),
    su2_unit_config U ->
    - (Rabs beta * INR (length Lambda)) <= - su2_wilson_action beta Lambda U.
  Proof.
    intros beta Lambda U HU. unfold su2_wilson_action.
    pose proof (plaq_sum_bound U Lambda HU) as H.
    set (X := fold_right Rplus 0 (map (su2_plaq U) Lambda)) in *.
    assert (H1 : Rabs (beta * X) <= Rabs beta * INR (length Lambda)).
    { rewrite Rabs_mult. apply Rmult_le_compat_l; [apply Rabs_pos | exact H]. }
    pose proof (Rle_abs (- (beta * X))) as H2. rewrite Rabs_Ropp in H2.
    replace (- (- beta * X)) with (beta * X) by ring. lra.
  Qed.

  (* =======================================================================
     3. Existence of the Haar-measure Gibbs expectation
     ======================================================================= *)

  Section Limit.
    Variable beta : R.
    Variable Lambda : list Plaq4D.

    Local Notation LinksE := (z2_links Lambda).

    (* normalized average over the level-n grid *)
    Definition avgn (n : nat) (Phi : SU2Config -> R) : R :=
      su2_sum (su2_grid n) LinksE Phi (fun _ => qone)
      / INR (length (su2_grid n)) ^ length LinksE.

    Lemma grid_card_pos : forall n, 0 < INR (length (su2_grid n)).
    Proof.
      intro n. apply lt_0_INR.
      assert (H : length (su2_grid n) <> 0%nat).
      { intro H0. apply (SU2HaarGrid.grid_nonempty n).
        apply length_zero_iff_nil. exact H0. }
      lia.
    Qed.

    Lemma grid_good : forall n v, In v (su2_grid n) -> su2_unit v.
    Proof.
      intro n. exact (proj1 (Forall_forall su2_unit (su2_grid n)) (SU2HaarGrid.grid_unit n)).
    Qed.

    Lemma den_pos : forall n,
      0 < su2_sum (su2_grid n) LinksE
            (fun U => exp (- su2_wilson_action beta Lambda U)) (fun _ => qone).
    Proof.
      intro n. rewrite su2_sum_csum.
      apply csum_pos; [apply SU2HaarGrid.grid_nonempty |]. intro A. apply exp_pos.
    Qed.

    Lemma expect_avg : forall n (F : SU2Config -> R),
      su2_expect_on (su2_grid n) beta Lambda F =
      avgn n (fun U => F U * exp (- su2_wilson_action beta Lambda U))
      / avgn n (fun U => exp (- su2_wilson_action beta Lambda U)).
    Proof.
      intros n F. unfold su2_expect_on, avgn.
      pose proof (den_pos n) as HD.
      pose proof (pow_lt _ (length LinksE) (grid_card_pos n)) as HN.
      field. split; lra.
    Qed.

    Lemma avg_den_lower : forall n,
      exp (- (Rabs beta * INR (length Lambda)))
      <= avgn n (fun U => exp (- su2_wilson_action beta Lambda U)).
    Proof.
      intro n. unfold avgn.
      pose proof (pow_lt _ (length LinksE) (grid_card_pos n)) as HN.
      apply Rmult_le_reg_r with (INR (length (su2_grid n)) ^ length LinksE); [exact HN |].
      unfold Rdiv. rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
      rewrite su2_sum_csum.
      rewrite <- (ProductMeasure.csum_const Link4D Quat link4D_eqb (su2_grid n) LinksE
                    (exp (- (Rabs beta * INR (length Lambda)))) (fun _ => qone)).
      apply (ProductMeasure.csum_le_good Link4D Quat link4D_eqb (su2_grid n)
               su2_unit (grid_good n)).
      - intros A HA. apply Z2GaugeClustering.exp_le. apply action_bound. exact HA.
      - exact unit_config_one.
    Qed.

    Theorem haar_state_exists : forall F : SU2Config -> R,
      su2_bounded_continuous F ->
      exists v : R, su2_haar_expect_is beta Lambda F v.
    Proof.
      intros F HF.
      destruct (SU2HaarGrid.grid_average_converges LinksE
                  (fun U => F U * exp (- su2_wilson_action beta Lambda U))
                  (SU2Continuity.bc_mult F
                     (fun U => exp (- su2_wilson_action beta Lambda U)) HF
                     (SU2Continuity.bc_boltzmann beta Lambda)))
        as [vn Hn].
      destruct (SU2HaarGrid.grid_average_converges LinksE
                  (fun U => exp (- su2_wilson_action beta Lambda U))
                  (SU2Continuity.bc_boltzmann beta Lambda)) as [vd Hd].
      assert (Hvd : exp (- (Rabs beta * INR (length Lambda))) <= vd).
      { apply (cv_lower
                 (fun n => avgn n (fun U => exp (- su2_wilson_action beta Lambda U)))
                 vd _ Hd).
        intro n. apply avg_den_lower. }
      pose proof (exp_pos (- (Rabs beta * INR (length Lambda)))) as Hpos.
      exists (vn / vd). unfold su2_haar_expect_is.
      apply (cv_ext
               (fun n => avgn n (fun U => F U * exp (- su2_wilson_action beta Lambda U))
                         / avgn n (fun U => exp (- su2_wilson_action beta Lambda U)))).
      - intro n. symmetry. apply expect_avg.
      - apply (cv_div
                 (fun n => avgn n (fun U => F U * exp (- su2_wilson_action beta Lambda U)))
                 (fun n => avgn n (fun U => exp (- su2_wilson_action beta Lambda U)))
                 vn vd Hn Hd).
        lra.
    Qed.

  End Limit.

  (* =======================================================================
     4. TARGETS 8c, 8d, 8e
     ======================================================================= *)

  (* TARGET 8c *)
  Theorem su2_haar_state_exists : Challenge_SU2Gauge4D_HaarStateExists.
  Proof. intros beta Lambda F HF. exact (haar_state_exists beta Lambda F HF). Qed.

  (* TARGET 8d *)
  Theorem su2_haar_clustering : Challenge_SU2Gauge4D_HaarClustering.
  Proof.
    intros beta mu Lambda p1 p2 f g Hmu Hsmall Hnd Hwf Hwf1 Hf Hg Hfc Hgc Hfb Hgb.
    destruct (haar_state_exists beta Lambda (fun U => f U * g U)
                (SU2Continuity.bc_mult f g Hfc Hgc)) as [vfg Hfg].
    destruct (haar_state_exists beta Lambda f Hfc) as [vf Hvf].
    destruct (haar_state_exists beta Lambda g Hgc) as [vg Hvg].
    exists vfg, vf, vg.
    split; [exact Hfg |]. split; [exact Hvf |]. split; [exact Hvg |].
    apply (cv_bound (fun n => su2_truncated_on (su2_grid n) beta Lambda f g)
             (vfg - vf * vg) _ 0%nat).
    - unfold su2_truncated_on.
      apply (CV_minus
               (fun n => su2_expect_on (su2_grid n) beta Lambda (fun U => f U * g U))
               (fun n => su2_expect_on (su2_grid n) beta Lambda f
                         * su2_expect_on (su2_grid n) beta Lambda g)
               vfg (vf * vg) Hfg).
      exact (CV_mult _ _ vf vg Hvf Hvg).
    - intros n _.
      exact (SU2Clustering.su2_strong_coupling_clustering (su2_grid n) beta mu Lambda
               p1 p2 f g (SU2HaarGrid.grid_nonempty n) (SU2HaarGrid.grid_unit n)
               Hmu Hsmall Hnd Hwf Hwf1 Hf Hg Hfb Hgb).
  Qed.

  (* TARGET 8e *)
  Theorem su2_haar_wilson_loop_area_law : Challenge_SU2Gauge4D_HaarWilsonLoopAreaLaw.
  Proof.
    intros beta Lambda s mu nu a b Hsmall Hnd Hwf Hmn HC.
    destruct (haar_state_exists beta Lambda (fun U => su2_wilson_loop U s mu nu a b)
                (SU2Continuity.bc_wilson_loop s mu nu a b)) as [w Hw].
    exists w. split; [exact Hw |].
    apply (cv_bound
             (fun n => su2_expect_on (su2_grid n) beta Lambda
                         (fun U => su2_wilson_loop U s mu nu a b))
             w _ 1%nat Hw).
    intros n Hn.
    exact (SU2AreaLaw.su2_wilson_loop_area_law (su2_grid n) beta Lambda s mu nu a b
             (SU2HaarGrid.grid_nonempty n) (SU2HaarGrid.grid_unit n)
             (SU2HaarGrid.grid_center n Hn) Hsmall Hnd Hwf Hmn HC).
  Qed.

  (* =======================================================================
     5. An instance of Target 8d: the plaquette-plaquette correlation
     ======================================================================= *)

  (* The hypotheses of Target 8d on the observables are satisfied by the
     plaquette variables f = (1/2) tr U_p1 and g = (1/2) tr U_p2: the
     connected plaquette-plaquette correlation function of the Haar-measure
     Gibbs state exists and decays exponentially, uniformly in the volume. *)
  Corollary su2_haar_plaquette_clustering :
    forall (beta mu : R) (Lambda : list Plaq4D) (p1 p2 : Plaq4D),
      0 <= mu ->
      168 * Rabs beta <= exp (- mu) ->
      NoDup Lambda ->
      Forall wf_plaq_4D Lambda ->
      wf_plaq_4D p1 ->
      exists v12 v1 v2 : R,
        su2_haar_expect_is beta Lambda (fun U => su2_plaq U p1 * su2_plaq U p2) v12 /\
        su2_haar_expect_is beta Lambda (fun U => su2_plaq U p1) v1 /\
        su2_haar_expect_is beta Lambda (fun U => su2_plaq U p2) v2 /\
        Rabs (v12 - v1 * v2) <= 4 * exp (- mu * (plaq4D_dist p1 p2 - 1)).
  Proof.
    intros beta mu Lambda p1 p2 Hmu Hsmall Hnd Hwf Hwf1.
    apply (su2_haar_clustering beta mu Lambda p1 p2
             (fun U => su2_plaq U p1) (fun U => su2_plaq U p2)
             Hmu Hsmall Hnd Hwf Hwf1).
    - intros U U' H. apply plaq_local. exact H.
    - intros U U' H. apply plaq_local. exact H.
    - apply SU2Continuity.bc_plaq.
    - apply SU2Continuity.bc_plaq.
    - intros U HU. apply Rabs_le. apply plaq_bound. exact HU.
    - intros U HU. apply Rabs_le. apply plaq_bound. exact HU.
  Qed.

End SU2HaarLimit.
