(* =========================================================================
   ym/lattice_4d_kp.v

   Concrete 4D Hypercubic Lattice Z^4 Plaquette Polymer Exponential Decay:
   Combines the zero-axiom exact 21-neighbor coordination theorem
   (ym/lattice_4d_coordination.v) with the genuine Kotecky-Preiss / Penrose
   Ursell cluster expansion theorem (rg/kotecky_preiss.v).

   Result (ZERO analytic assumptions, ZERO combinatorial assumptions,
   ZERO project axioms):
     For every beta > 85, every finite NoDup volume Lambda of canonical
     4D plaquettes, every truncation N_max, and any canonical p1, p2:
       |G_{Lambda, N_max}^{Z^4}(p1, p2)| <= exp(1) * exp(- (1/2) * ||s(p1) - s(p2)||_1).

   Depends ONLY on Coq stdlib + ym.lattice + ym.lattice_4d_coordination + rg.kotecky_preiss.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Lra Lia ZArith Bool List.
From ym Require Import lattice lattice_4d_coordination.
From rg Require Import penrose_tree_bound poly_exp_bound kotecky_preiss cluster_log_partition.

Import ListNotations.
Import Lattice Lattice4DCoord PenroseTreeBound PolyExpBound KoteckyPreiss ClusterLogPartition.
Open Scope R_scope.

Module Lattice4DKP.

  Definition plaq_dist (p1 p2 : plaquette) : R :=
    IZR (site_manhattan (plaq_site p1) (plaq_site p2)) / 2.

  Lemma plaq_dist_refl : forall p, plaq_dist p p = 0.
  Proof.
    intro p. unfold plaq_dist, site_manhattan.
    replace (site_t (plaq_site p) - site_t (plaq_site p))%Z with 0%Z by lia.
    replace (site_x (plaq_site p) - site_x (plaq_site p))%Z with 0%Z by lia.
    replace (site_y (plaq_site p) - site_y (plaq_site p))%Z with 0%Z by lia.
    replace (site_z (plaq_site p) - site_z (plaq_site p))%Z with 0%Z by lia.
    simpl. lra.
  Qed.

  Lemma plaq_dist_triangle : forall p q r,
    plaq_dist p r <= plaq_dist p q + plaq_dist q r.
  Proof.
    intros p q r. unfold plaq_dist.
    assert (Hz : (site_manhattan (plaq_site p) (plaq_site r) <=
                  site_manhattan (plaq_site p) (plaq_site q) +
                  site_manhattan (plaq_site q) (plaq_site r))%Z).
    { unfold site_manhattan.
      pose proof (Z.abs_triangle (site_t (plaq_site p) - site_t (plaq_site q))%Z
                                 (site_t (plaq_site q) - site_t (plaq_site r))%Z).
      pose proof (Z.abs_triangle (site_x (plaq_site p) - site_x (plaq_site q))%Z
                                 (site_x (plaq_site q) - site_x (plaq_site r))%Z).
      pose proof (Z.abs_triangle (site_y (plaq_site p) - site_y (plaq_site q))%Z
                                 (site_y (plaq_site q) - site_y (plaq_site r))%Z).
      pose proof (Z.abs_triangle (site_z (plaq_site p) - site_z (plaq_site q))%Z
                                 (site_z (plaq_site q) - site_z (plaq_site r))%Z).
      lia. }
    apply IZR_le in Hz. rewrite plus_IZR in Hz. lra.
  Qed.

  Lemma plaq_overlap_bool_sym : forall p q,
    plaq_overlap_bool p q = plaq_overlap_bool q p.
  Proof.
    intros p q. apply eq_true_iff_eq. rewrite !plaq_overlap_bool_spec.
    assert (Hdir : forall a b, plaq_overlap a b -> plaq_overlap b a).
    { intros a b [Heq | [Hne [e1 [e2 [He1 [He2 [[H1 H2] | [H1 H2]]]]]]]].
      - left; symmetry; exact Heq.
      - right; split; [congruence | exists e2, e1; repeat split; try assumption; left; split; symmetry; assumption].
      - right; split; [congruence | exists e2, e1; repeat split; try assumption; right; split; symmetry; assumption]. }
    split; apply Hdir.
  Qed.

  Lemma plaq_overlap_dist_le_1 : forall p q,
    plaq_overlap_bool p q = true -> plaq_dist p q <= 1.
  Proof.
    intros p q Hob. apply plaq_overlap_bool_spec in Hob.
    pose proof (overlap_anchor_manhattan p q Hob) as Hle.
    unfold plaq_dist. apply IZR_le in Hle. simpl in Hle. lra.
  Qed.

  (* Elementary real inequality: for beta > 85, 21 * exp(-beta/10 + 2) <= 1 *)
  Lemma kp_numeric_bound_beta85 : forall beta,
    beta > 85 ->
    21 * (exp (- beta / 10) * exp (1 + 1)) <= 1.
  Proof.
    intros beta Hbeta.
    assert (Hexp_low : 21 <= exp (beta / 10 - 2)).
    { pose proof (exp_partial_sum_le (65 / 10) 2%nat ltac:(lra)) as Ht.
      simpl sum_f_R0 in Ht. simpl fact in Ht. simpl pow in Ht.
      assert (H21 : 21 <= exp (65 / 10)) by (simpl INR in Ht; lra).
      assert (Hgt : 65 / 10 < beta / 10 - 2) by lra.
      pose proof (exp_increasing (65 / 10) (beta / 10 - 2) Hgt). lra. }
    rewrite <- exp_plus.
    replace (- beta / 10 + (1 + 1)) with (- (beta / 10 - 2)) by lra.
    rewrite exp_Ropp.
    pose proof (exp_pos (beta / 10 - 2)) as Hpos.
    apply Rmult_le_reg_r with (r := exp (beta / 10 - 2)); [exact Hpos |].
    rewrite Rmult_assoc, Rinv_l; [lra | lra].
  Qed.

  (* Exact 21-neighbor overlap bound discharges KP for any finite NoDup volume Lambda *)
  Lemma lattice4D_kp_at : forall beta Lambda p,
    beta > 85 ->
    NoDup Lambda ->
    Forall wf_plaq Lambda ->
    wf_plaq p ->
    kp_at plaq_overlap_bool Lambda (fun _ => exp (- beta / 10)) (fun _ => 1) (fun _ => 1 * 1) p.
  Proof.
    intros beta Lambda p Hbeta Hnd Hall Hwfp.
    unfold kp_at, sum_overlap_Lambda.
    set (cval := Rabs (exp (- beta / 10)) * exp (1 + 1 * 1)).
    assert (Hcval_eq : cval = exp (- beta / 10) * exp (1 + 1)).
    { unfold cval. rewrite Rabs_right; [replace (1 + 1 * 1) with (1 + 1) by ring; reflexivity |].
      left; apply exp_pos. }
    assert (Hsum_cnt :
      fold_right Rplus 0 (map (fun q => if plaq_overlap_bool p q then cval else 0) Lambda) =
      INR (length (filter (plaq_overlap_bool p) Lambda)) * cval).
    { clear. induction Lambda as [| q qs IH]; simpl; [ring |].
      destruct (plaq_overlap_bool p q); simpl length; [rewrite S_INR, IH; ring | rewrite IH; ring]. }
    rewrite Hsum_cnt, Hcval_eq.
    assert (Hlen_le : (length (filter (plaq_overlap_bool p) Lambda) <= 21)%nat).
    { rewrite <- (plaq_neighbors_exact_21 p Hwfp).
      apply NoDup_incl_length; [apply NoDup_filter; exact Hnd |].
      intros q Hq. apply filter_In in Hq. destruct Hq as [HqL Hob].
      apply plaq_overlap_bool_spec in Hob.
      rewrite Forall_forall in Hall.
      apply plaq_neighbors_complete_wf; [exact (Hall q HqL) | exact Hob]. }
    apply le_INR in Hlen_le.
    assert (H21_eq : INR 21 = 21) by (unfold INR; simpl; ring).
    rewrite H21_eq in Hlen_le.
    eapply Rle_trans.
    - apply Rmult_le_compat_r; [apply Rmult_le_pos; left; apply exp_pos | exact Hlen_le].
    - exact (kp_numeric_bound_beta85 beta Hbeta).
  Qed.

  (* MAIN CONCRETE Z^4 EXPONENTIAL DECAY THEOREM (ZERO ANALYTIC OR COMBINATORIAL HYPOTHESES!) *)
  Theorem lattice4D_kp_exponential_decay : forall beta Lambda N_max p1 p2,
    beta > 85 ->
    NoDup Lambda ->
    Forall wf_plaq Lambda ->
    wf_plaq p1 ->
    Rabs (ursell_correlator plaq_overlap_bool Lambda N_max (fun _ => exp (- beta / 10)) p1 p2) <=
    exp 1 * exp (- plaq_dist p1 p2).
  Proof.
    intros beta Lambda N_max p1 p2 Hbeta Hnd Hall Hwfp1.
    pose proof (kp_correlator_exponential_decay
                  plaq_overlap_bool Lambda
                  (fun _ => exp (- beta / 10)) (fun _ => 1) (fun _ => 1)
                  plaq_dist 1 p1 p2
                  plaq_overlap_bool_sym plaq_dist_refl plaq_dist_triangle
                  plaq_overlap_dist_le_1 (fun _ => Rle_refl 1)
                  ltac:(lra) ltac:(lra) (fun _ _ => ltac:(lra))
                  (lattice4D_kp_at beta Lambda p1 Hbeta Hnd Hall Hwfp1)
                  (fun p Hp => lattice4D_kp_at beta Lambda p Hbeta Hnd Hall
                                 (proj1 (Forall_forall wf_plaq Lambda) Hall p Hp))
                  N_max) as Hdec.
    cbv beta in Hdec.
    replace (1 * exp 1 * exp (- (1) * plaq_dist p1 p2)) with (exp 1 * exp (- plaq_dist p1 p2)) in Hdec
      by (f_equal; [ring | f_equal; ring]).
    exact Hdec.
  Qed.

  Lemma plaq_overlap_bool_refl : forall p, plaq_overlap_bool p p = true.
  Proof. intro p. apply plaq_overlap_bool_spec. left. reflexivity. Qed.

  (* TARGET 6c: Concrete 4D Z^4 Partition Function ln Z_Lambda Convergence & Exact Log-Ratio Decay *)
  Theorem lattice4D_partition_fn_decay : forall beta Lambda p1 p2,
    beta > 85 ->
    NoDup Lambda ->
    Forall wf_plaq Lambda ->
    wf_plaq p1 ->
    let w := fun _ : plaquette => exp (- beta / 10) in
    let Z := partition_fn plaq_overlap_bool Lambda w in
    let Z1 := partition_fn plaq_overlap_bool (filter (fun q => negb (plaq_overlap_bool p1 q)) Lambda) w in
    let Z2 := partition_fn plaq_overlap_bool (filter (fun q => negb (plaq_overlap_bool p2 q)) Lambda) w in
    let Z12 := partition_fn plaq_overlap_bool (filter (fun q => negb (plaq_overlap_bool p1 q) && negb (plaq_overlap_bool p2 q)) Lambda) w in
    0 < Z /\ 0 < Z1 /\ 0 < Z2 /\ 0 < Z12 /\
    Un_cv (fun N => kp_series Lambda N (fun X => ursell_fn plaq_overlap_bool X * prod_weight w X)) (ln Z) /\
    Un_cv (fun N => ursell_correlator plaq_overlap_bool Lambda N w p1 p2) (ln ((Z * Z12) / (Z1 * Z2))) /\
    Rabs (ln ((Z * Z12) / (Z1 * Z2))) <= exp 1 * exp (- plaq_dist p1 p2).
  Proof.
    intros beta Lambda p1 p2 Hbeta Hnd Hall Hwfp1 w Z Z1 Z2 Z12.
    assert (Hkp : forall p, In p Lambda -> kp_at plaq_overlap_bool Lambda w (fun _ => 1) (fun _ => 1 * 1) p).
    { intros p Hp. exact (lattice4D_kp_at beta Lambda p Hbeta Hnd Hall (proj1 (Forall_forall wf_plaq Lambda) Hall p Hp)). }
    assert (Hkp0 : forall p, In p Lambda -> kp_at plaq_overlap_bool Lambda w (fun _ => 1) (fun _ => 0) p).
    { intros p Hp. exact (kp_at_drop_d plaq_overlap_bool Lambda w (fun _ => 1) (fun _ => 1 * 1) p (fun _ => ltac:(lra)) (Hkp p Hp)). }
    destruct (kp_log_partition_fn plaq_overlap_bool Lambda w (fun _ => 1)
                plaq_overlap_bool_refl plaq_overlap_bool_sym (fun _ _ => ltac:(lra)) Hkp0)
      as [_ [_ HcvZ]].
    pose proof (kp_log_ratio_decay
                  plaq_overlap_bool Lambda w (fun _ => 1) (fun _ => 1)
                  plaq_dist 1 p1 p2
                  plaq_overlap_bool_refl plaq_overlap_bool_sym plaq_dist_refl plaq_dist_triangle
                  plaq_overlap_dist_le_1 (fun _ => Rle_refl 1)
                  ltac:(lra) ltac:(lra) (fun _ _ => ltac:(lra))
                  (lattice4D_kp_at beta Lambda p1 Hbeta Hnd Hall Hwfp1)
                  Hkp) as [HZ [HZ1 [HZ2 [HZ12 [HcvR Hdec]]]]].
    cbv beta in Hdec.
    replace (1 * exp 1 * exp (- (1) * plaq_dist p1 p2)) with (exp 1 * exp (- plaq_dist p1 p2)) in Hdec
      by (f_equal; [ring | f_equal; ring]).
    repeat split; assumption.
  Qed.

End Lattice4DKP.
