(* =========================================================================
   ym/z2_free_energy.v

   Kotecky-Preiss criterion and convergent cluster expansion of the free
   energy of the 4D Z_2 Wilson lattice gauge theory at strong coupling
   (TARGET 7d), proved directly for the frozen objects of
   `verification/ChallengeZ2Gauge.v`:

     for 189 * |tanh beta| <= 1 and every finite duplicate-free volume Lambda
     of canonical plaquettes of Z^4,
       (1) the surface-polymer gas of Target 7c satisfies the single-polymer
           Kotecky-Preiss inequality with a(gamma) = 189 |tanh beta| |gamma|;
       (2) the Mayer / Ursell cluster series converges to
             ln Z_Lambda - |Lambda| ln cosh(beta);
       (3) |ln Z_Lambda - |Lambda| ln cosh(beta)| <= 189 |tanh beta| |Lambda|.

   This is where the gauge theory is plugged into the verified
   Kotecky-Preiss / cluster-expansion engine:
     - `ConnectedSubsetBound.kp_connected_subset_pinned_bound`
       (rg/connected_subset_bound.v) applied to the gas of SINGLE plaquettes
       (constant activity, 21 neighbours: Target 4a) bounds the entropy of
       connected plaquette sets touching a given plaquette;
     - that entropy bound gives the Kotecky-Preiss inequality for the
       surface polymers;
     - `ClusterLogPartition.kp_log_partition_fn` (Target 6a) and
       `KoteckyPreiss.kp_overlap_pinned_bound` (Target 5a) then give the
       convergent expansion of ln Xi and its volume-uniform bound;
     - Target 7c identifies Xi with Z / cosh(beta)^{|Lambda|}.

   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.Verify.
Require Import rg.dup_clustering.
Require Import rg.penrose_tree_bound.
Require Import rg.kotecky_preiss.
Require Import rg.cluster_log_partition.
Require Import rg.polymer_representation.
Require Import rg.connected_subset_bound.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.z2_polymer_gas.

Import ListNotations.
Import Challenge ChallengeZ2Gauge.
Import DupClustering Z2GaugeExpansion Z2GaugeClustering Z2PolymerGas.
Open Scope R_scope.

Module Z2FreeEnergy.

  (* =======================================================================
     1. Elementary lemmas on the truncated cluster series
     ======================================================================= *)

  Lemma kp_series_ext : forall {P : Type} (Lam : list P) (N : nat) (f g : list P -> R),
    (forall X, f X = g X) ->
    KoteckyPreiss.kp_series Lam N f = KoteckyPreiss.kp_series Lam N g.
  Proof.
    intros P Lam N f g H. induction N as [| N IH]; [reflexivity |].
    cbn [KoteckyPreiss.kp_series]. rewrite IH. f_equal. f_equal.
    apply KoteckyPreiss.sum_over_tuples_ext. intros Y _. apply H.
  Qed.

  Lemma kp_series_plus : forall {P : Type} (Lam : list P) (N : nat) (f g : list P -> R),
    KoteckyPreiss.kp_series Lam N (fun X => f X + g X) =
    KoteckyPreiss.kp_series Lam N f + KoteckyPreiss.kp_series Lam N g.
  Proof.
    intros P Lam N f g. induction N as [| N IH]; cbn [KoteckyPreiss.kp_series]; [ring |].
    rewrite IH, KoteckyPreiss.sum_over_tuples_plus. ring.
  Qed.

  Lemma kp_series_zero : forall {P : Type} (Lam : list P) (N : nat),
    KoteckyPreiss.kp_series Lam N (fun _ => 0) = 0.
  Proof.
    intros P Lam N. induction N as [| N IH]; cbn [KoteckyPreiss.kp_series]; [reflexivity |].
    rewrite IH. unfold KoteckyPreiss.sum_over_tuples.
    rewrite PenroseTreeBound.fold_right_Rplus_0. ring.
  Qed.

  Lemma kp_series_le : forall {P : Type} (Lam : list P) (N : nat) (f g : list P -> R),
    (forall n Y, In Y (KoteckyPreiss.tuples_of_length Lam n) -> (1 <= n)%nat -> f Y <= g Y) ->
    KoteckyPreiss.kp_series Lam N f <= KoteckyPreiss.kp_series Lam N g.
  Proof.
    intros P Lam N f g H. induction N as [| N IH]; [apply Rle_refl |].
    cbn [KoteckyPreiss.kp_series]. apply Rplus_le_compat; [exact IH |].
    apply Rmult_le_compat_l.
    - left. apply Rinv_0_lt_compat. apply INR_fact_lt_0.
    - apply KoteckyPreiss.sum_over_tuples_le. intros Y HY. apply (H (S N) Y HY). lia.
  Qed.

  Lemma kp_series_abs : forall {P : Type} (Lam : list P) (N : nat) (f : list P -> R),
    Rabs (KoteckyPreiss.kp_series Lam N f) <=
    KoteckyPreiss.kp_series Lam N (fun X => Rabs (f X)).
  Proof.
    intros P Lam N f. induction N as [| N IH].
    - cbn [KoteckyPreiss.kp_series]. rewrite Rabs_R0. apply Rle_refl.
    - cbn [KoteckyPreiss.kp_series]. eapply Rle_trans; [apply Rabs_triang |].
      apply Rplus_le_compat; [exact IH |].
      assert (Hpos : 0 < / INR (fact (S N))) by (apply Rinv_0_lt_compat; apply INR_fact_lt_0).
      rewrite Rabs_mult, (Rabs_right (/ INR (fact (S N)))) by (apply Rle_ge; left; exact Hpos).
      apply Rmult_le_compat_l; [left; exact Hpos |].
      unfold KoteckyPreiss.sum_over_tuples.
      apply PenroseTreeBound.Rabs_fold_right_Rplus_le. intros X _. apply Rle_refl.
  Qed.

  Lemma kp_series_rsum : forall {P A : Type} (Lam : list P) (N : nat) (Pins : list A)
      (G : A -> list P -> R),
    KoteckyPreiss.kp_series Lam N (fun X => rsum Pins (fun pin => G pin X)) =
    rsum Pins (fun pin => KoteckyPreiss.kp_series Lam N (G pin)).
  Proof.
    intros P A Lam N Pins G. induction Pins as [| pin Pins IH].
    - rewrite rsum_nil. apply kp_series_zero.
    - rewrite rsum_cons, <- IH, <- kp_series_plus. apply kp_series_ext. intro X.
      exact (rsum_cons pin Pins (fun pin' => G pin' X)).
  Qed.

  (* Volume bound for the cluster series through a covering family of pins *)
  Lemma kp_series_pins_bound : forall {P : Type} (ob : P -> P -> bool) (Lam : list P)
      (w a : P -> R) (Pins : list P) (N : nat),
    (forall x y, ob x y = ob y x) ->
    (forall p, In p Lam -> 0 <= a p) ->
    (forall p, In p Lam -> KoteckyPreiss.kp_at ob Lam w a (fun _ => 0) p) ->
    (forall pin, In pin Pins -> 0 <= a pin) ->
    (forall pin, In pin Pins -> KoteckyPreiss.kp_at ob Lam w a (fun _ => 0) pin) ->
    (forall q, In q Lam -> exists pin, In pin Pins /\ ob pin q = true) ->
    Rabs (KoteckyPreiss.kp_series Lam N
            (fun X => PenroseTreeBound.ursell_fn ob X * KoteckyPreiss.prod_weight w X))
    <= rsum Pins a.
  Proof.
    intros P ob Lam w a Pins N Hsym Ha Hkp Hpa Hpkp Hcover.
    set (G := fun (pin : P) (X : list P) =>
           if existsb (ob pin) X
           then Rabs (PenroseTreeBound.ursell_fn ob X) *
                KoteckyPreiss.prod_weight (fun q => Rabs (w q) * exp 0) X
           else 0).
    assert (HGnn : forall pin X, 0 <= G pin X).
    { intros pin X. unfold G. destruct (existsb (ob pin) X); [| apply Rle_refl].
      apply Rmult_le_pos; [apply Rabs_pos |]. apply KoteckyPreiss.prod_weight_nonneg.
      intro x. apply Rmult_le_pos; [apply Rabs_pos | left; apply exp_pos]. }
    eapply Rle_trans; [apply kp_series_abs |].
    apply Rle_trans with
      (KoteckyPreiss.kp_series Lam N (fun X => rsum Pins (fun pin => G pin X))).
    - apply kp_series_le. intros n Y HY Hn.
      pose proof (KoteckyPreiss.tuples_of_length_len Lam n Y HY) as Hlen.
      pose proof (KoteckyPreiss.tuples_of_length_in Lam n Y HY) as Hin.
      destruct Y as [| q rest]; [simpl in Hlen; lia |].
      inversion Hin as [| q' rest' HqL Hrest]; subst.
      destruct (Hcover q HqL) as [pin [HpinP Hob]].
      assert (Hex : existsb (ob pin) (q :: rest) = true).
      { cbn [existsb]. rewrite Hob. reflexivity. }
      apply Rle_trans with (G pin (q :: rest)).
      + unfold G. rewrite Hex. rewrite Rabs_mult, KoteckyPreiss.Rabs_prod_weight.
        apply Rmult_le_compat_l; [apply Rabs_pos |].
        apply Req_le. unfold KoteckyPreiss.prod_weight. f_equal. apply map_ext.
        intro x. rewrite exp_0. ring.
      + apply (rsum_ge_term Pins (fun pin' => G pin' (q :: rest)) pin); [| exact HpinP].
        intros pin' _. apply HGnn.
    - rewrite kp_series_rsum. apply rsum_le. intros pin Hpin.
      exact (KoteckyPreiss.kp_overlap_pinned_bound ob Lam w a (fun _ => 0) pin Hsym
               (Hpa pin Hpin) Ha (Hpkp pin Hpin) Hkp N).
  Qed.

  Lemma rsum_const_fun : forall {A : Type} (c : R) (l : list A),
    rsum l (fun _ => c) = INR (length l) * c.
  Proof.
    intros A c l. induction l as [| a l IH].
    - rewrite rsum_nil. cbn [length INR]. ring.
    - rewrite rsum_cons, IH. cbn [length]. rewrite S_INR. ring.
  Qed.

  Lemma prod_weight_const : forall {P : Type} (c : R) (X : list P),
    KoteckyPreiss.prod_weight (fun _ => c) X = c ^ length X.
  Proof.
    intros P c X. unfold KoteckyPreiss.prod_weight, KoteckyPreiss.prod_list.
    induction X as [| x X IH]; [reflexivity |].
    cbn [map fold_right length pow]. rewrite IH. reflexivity.
  Qed.

  Lemma ln_pow_INR : forall x n, 0 < x -> ln (x ^ n) = INR n * ln x.
  Proof.
    intros x n Hx. induction n as [| n IH].
    - cbn [pow INR]. rewrite ln_1. ring.
    - cbn [pow]. rewrite ln_mult; [| exact Hx | apply pow_lt; exact Hx].
      rewrite IH, S_INR. ring.
  Qed.

  (* =======================================================================
     2. Plaquette touching
     ======================================================================= *)

  Lemma touch_sym : forall p q, plaq4D_touch p q = plaq4D_touch q p.
  Proof.
    exact (PolymerRepresentation.touch_sym Link4D Plaq4D link4D_eqb link4D_eqb_spec
             plaq4D_links).
  Qed.

  Lemma touch_refl : forall p, plaq4D_touch p p = true.
  Proof.
    exact (PolymerRepresentation.touch_refl Link4D Plaq4D link4D_eqb link4D_eqb_spec
             plaq4D_links links_nonempty).
  Qed.

  Lemma poly_incompat_refl : forall g, z2_poly_incompat g g = true.
  Proof.
    exact (PolymerRepresentation.incompat_refl Link4D Plaq4D link4D_eqb link4D_eqb_spec
             plaq4D_links links_nonempty).
  Qed.

  Lemma poly_incompat_sym : forall g1 g2, z2_poly_incompat g1 g2 = z2_poly_incompat g2 g1.
  Proof.
    exact (PolymerRepresentation.incompat_sym Link4D Plaq4D link4D_eqb link4D_eqb_spec
             plaq4D_links).
  Qed.

  (* connectivity in the form used by the engine *)
  Definition connP (S : list Plaq4D) : bool :=
    PenroseTreeBound.is_connectedb (length S) (PenroseTreeBound.graph_edges plaq4D_touch S).

  Lemma connP_eq : forall S, connP S = z2_connected S.
  Proof.
    intro S. unfold connP, z2_connected. symmetry.
    transitivity
      (PenroseTreeBound.is_connectedb (length S) (kp_graph_edges plaq4D_touch S)).
    - exact (Verify.kp_is_connectedb_eq (length S) (kp_graph_edges plaq4D_touch S)).
    - reflexivity.
  Qed.

  (* =======================================================================
     3. The surface-polymer gas at strong coupling
     ======================================================================= *)

  Section Z2.
    Variable beta : R.
    Variable Lambda : list Plaq4D.
    Hypothesis Hsmall : 189 * Rabs (tanh beta) <= 1.
    Hypothesis Hnd : NoDup Lambda.
    Hypothesis Hwf : Forall wf_plaq_4D Lambda.

    Definition tabs : R := Rabs (tanh beta).
    Definition alpha : R := 189 * tabs.
    (* effective single-plaquette activity |t| e^{alpha} *)
    Definition xw : R := tabs * exp alpha.
    (* Kotecky-Preiss function of the single-plaquette gas *)
    Definition a0 : R := 21 * exp 1 * xw.

    Definition wP (g : list Plaq4D) : R := z2_poly_activity beta g.
    Definition aP (g : list Plaq4D) : R := 189 * Rabs (tanh beta) * INR (length g).

    Lemma tabs_nonneg : 0 <= tabs.
    Proof. unfold tabs. apply Rabs_pos. Qed.

    Lemma alpha_bounds : 0 <= alpha <= 1.
    Proof. pose proof tabs_nonneg. unfold alpha, tabs in *. lra. Qed.

    Lemma exp_alpha_le_3 : exp alpha <= 3.
    Proof.
      apply Rle_trans with (exp 1); [| exact exp_le_3].
      apply exp_le. apply alpha_bounds.
    Qed.

    Lemma xw_bounds : 0 <= xw <= 3 * tabs.
    Proof.
      pose proof tabs_nonneg as Ht. pose proof exp_alpha_le_3 as He.
      pose proof (exp_pos alpha) as Hp. unfold xw. split.
      - apply Rmult_le_pos; lra.
      - rewrite (Rmult_comm 3 tabs). apply Rmult_le_compat_l; assumption.
    Qed.

    Lemma a0_bounds : 0 <= a0 <= alpha.
    Proof.
      pose proof xw_bounds as [Hx0 Hx1]. pose proof (exp_pos 1) as He0.
      pose proof exp_le_3 as He1. unfold a0, alpha. split.
      - apply Rmult_le_pos; [lra | exact Hx0].
      - apply Rle_trans with (21 * 3 * xw).
        + apply Rmult_le_compat_r; [exact Hx0 | lra].
        + lra.
    Qed.

    Lemma unit_kp_num : 21 * (xw * exp a0) <= a0.
    Proof.
      pose proof xw_bounds as [Hx0 _]. pose proof a0_bounds as [_ Ha1].
      pose proof alpha_bounds as [_ Hal].
      assert (He : exp a0 <= exp 1) by (apply exp_le; lra).
      assert (Hm : xw * exp a0 <= xw * exp 1) by (apply Rmult_le_compat_l; assumption).
      unfold a0 at 2. lra.
    Qed.

    (* Kotecky-Preiss inequality for the gas of single plaquettes *)
    Lemma unit_kp : forall p, wf_plaq_4D p ->
      KoteckyPreiss.kp_at plaq4D_touch Lambda (fun _ => xw) (fun _ => a0) (fun _ => 0) p.
    Proof.
      intros p Hp. unfold KoteckyPreiss.kp_at, KoteckyPreiss.sum_overlap_Lambda.
      change (rsum Lambda (fun q => if plaq4D_touch p q then Rabs xw * exp (a0 + 0) else 0)
              <= a0).
      rewrite (rsum_indicator_const (fun q => plaq4D_touch p q) (Rabs xw * exp (a0 + 0)) Lambda).
      pose proof (touch_count_21 Lambda Hnd Hwf p Hp) as Hcnt.
      change (length (filter (fun q => plaq4D_touch p q) Lambda) <= 21)%nat in Hcnt.
      apply le_INR in Hcnt.
      assert (H21 : INR 21 = 21) by (cbn [INR]; lra).
      rewrite H21 in Hcnt.
      pose proof xw_bounds as [Hx0 _].
      rewrite (Rabs_right xw) by (apply Rle_ge; exact Hx0). rewrite Rplus_0_r.
      apply Rle_trans with (21 * (xw * exp a0)); [| exact unit_kp_num].
      apply Rmult_le_compat_r; [| exact Hcnt].
      apply Rmult_le_pos; [exact Hx0 | left; apply exp_pos].
    Qed.

    (* Entropy (lattice-animal) bound: connected plaquette sets touching p *)
    Lemma animal_bound : forall p, wf_plaq_4D p ->
      rsum (PenroseTreeBound.sublists Lambda)
        (fun S => if existsb (plaq4D_touch p) S && connP S then xw ^ length S else 0)
      <= a0.
    Proof.
      intros p Hp.
      pose proof (ConnectedSubsetBound.kp_connected_subset_pinned_bound
                    plaq4D_touch Lambda (fun _ => xw) (fun _ => a0) p
                    touch_sym Hnd (proj1 a0_bounds) (fun _ _ => proj1 a0_bounds)
                    (unit_kp p Hp)
                    (fun q Hq => unit_kp q (proj1 (Forall_forall wf_plaq_4D Lambda) Hwf q Hq)))
        as H.
      eapply Rle_trans; [| exact H].
      apply Req_le. unfold rsum. apply PenroseTreeBound.fold_right_Rplus_ext. intros S _.
      unfold connP.
      destruct (existsb (plaq4D_touch p) S &&
                PenroseTreeBound.is_connectedb (length S)
                  (PenroseTreeBound.graph_edges plaq4D_touch S)); [| reflexivity].
      rewrite prod_weight_const.
      rewrite (Rabs_right xw) by (apply Rle_ge; apply xw_bounds). reflexivity.
    Qed.

    Lemma weight_pow : forall g, Rabs (wP g) * exp (aP g + 0) = xw ^ length g.
    Proof.
      intro g. unfold wP, z2_poly_activity, aP, xw, alpha, tabs.
      rewrite <- RPow_abs, Rplus_0_r, Rpow_mult_distr, exp_pow_INR.
      f_equal. f_equal. ring.
    Qed.

    Lemma aP_nonneg : forall g, 0 <= aP g.
    Proof.
      intro g. unfold aP. apply Rmult_le_pos; [| apply pos_INR].
      apply Rmult_le_pos; [lra | apply Rabs_pos].
    Qed.

    (* Kotecky-Preiss inequality for the surface polymers, at any list of
       canonical plaquettes g0 (a polymer, or a single-plaquette pin) *)
    Lemma polymer_kp : forall g0, Forall wf_plaq_4D g0 ->
      KoteckyPreiss.kp_at z2_poly_incompat (z2_polymers Lambda) wP aP (fun _ => 0) g0.
    Proof.
      intros g0 Hg0. unfold KoteckyPreiss.kp_at, KoteckyPreiss.sum_overlap_Lambda.
      change (rsum (z2_polymers Lambda)
                (fun g => if z2_poly_incompat g0 g then Rabs (wP g) * exp (aP g + 0) else 0)
              <= aP g0).
      unfold z2_polymers. rewrite rsum_filter, Verify.kp_sublists_eq.
      apply Rle_trans with
        (rsum (PenroseTreeBound.sublists Lambda) (fun g =>
           rsum g0 (fun p =>
             if existsb (plaq4D_touch p) g && connP g then xw ^ length g else 0))).
      - apply rsum_le. intros g _. cbv beta.
        assert (Hnn : forall p,
          0 <= (if existsb (plaq4D_touch p) g && connP g then xw ^ length g else 0)).
        { intro p. destruct (existsb (plaq4D_touch p) g && connP g);
            [apply pow_le; apply xw_bounds | apply Rle_refl]. }
        destruct (z2_closed g && z2_connected g) eqn:Hpoly;
          [| apply rsum_nonneg; intros p _; apply Hnn].
        apply andb_true_iff in Hpoly. destruct Hpoly as [_ Hconn].
        destruct (z2_poly_incompat g0 g) eqn:Hob;
          [| apply rsum_nonneg; intros p _; apply Hnn].
        destruct g as [| y g']; [cbv in Hconn; discriminate Hconn |].
        assert (Hex : existsb (fun p => existsb (plaq4D_touch p) (y :: g')) g0 = true).
        { unfold z2_poly_incompat in Hob. destruct g0; exact Hob. }
        apply existsb_exists in Hex. destruct Hex as [p [Hp Htp]].
        rewrite weight_pow.
        apply Rle_trans with
          (if existsb (plaq4D_touch p) (y :: g') && connP (y :: g')
           then xw ^ length (y :: g') else 0).
        + rewrite Htp, (connP_eq (y :: g')), Hconn. apply Rle_refl.
        + apply (rsum_ge_term g0
                   (fun p' => if existsb (plaq4D_touch p') (y :: g') && connP (y :: g')
                              then xw ^ length (y :: g') else 0) p); [| exact Hp].
          intros p' _. apply Hnn.
      - rewrite rsum_swap.
        apply Rle_trans with (rsum g0 (fun _ => a0)).
        + apply rsum_le. intros p Hp. apply animal_bound.
          exact (proj1 (Forall_forall wf_plaq_4D g0) Hg0 p Hp).
        + rewrite rsum_const_fun. unfold aP. fold tabs. fold alpha.
          rewrite (Rmult_comm alpha).
          apply Rmult_le_compat_l; [apply pos_INR | apply a0_bounds].
    Qed.

    Lemma polymer_facts : forall g, In g (z2_polymers Lambda) ->
      incl g Lambda /\ g <> [].
    Proof.
      intros g Hg. unfold z2_polymers in Hg. apply filter_In in Hg. destruct Hg as [Hsub Hpoly].
      rewrite Verify.kp_sublists_eq in Hsub. split.
      - exact (PenroseTreeBound.sublists_incl Lambda g Hsub).
      - intro Heq. subst g. cbv in Hpoly. discriminate Hpoly.
    Qed.

    Lemma incl_wf : forall g, incl g Lambda -> Forall wf_plaq_4D g.
    Proof.
      intros g Hincl. apply Forall_forall. intros p Hp.
      exact (proj1 (Forall_forall wf_plaq_4D Lambda) Hwf p (Hincl p Hp)).
    Qed.

    Theorem free_energy_expansion :
      (forall g, In g (z2_polymers Lambda) ->
         KoteckyPreiss.kp_at z2_poly_incompat (z2_polymers Lambda) wP aP (fun _ => 0) g) /\
      Un_cv (fun N => KoteckyPreiss.kp_series (z2_polymers Lambda) N
                        (fun X => PenroseTreeBound.ursell_fn z2_poly_incompat X *
                                  KoteckyPreiss.prod_weight wP X))
            (ln (z2_partition_fn beta Lambda) - INR (length Lambda) * ln (cosh beta)) /\
      Rabs (ln (z2_partition_fn beta Lambda) - INR (length Lambda) * ln (cosh beta))
      <= 189 * Rabs (tanh beta) * INR (length Lambda).
    Proof.
      set (Polys := z2_polymers Lambda).
      assert (Hkp : forall g, In g Polys ->
                KoteckyPreiss.kp_at z2_poly_incompat Polys wP aP (fun _ => 0) g).
      { intros g Hg. apply polymer_kp. apply incl_wf. apply (polymer_facts g Hg). }
      destruct (ClusterLogPartition.kp_log_partition_fn z2_poly_incompat Polys wP aP
                  poly_incompat_refl poly_incompat_sym (fun g _ => aP_nonneg g) Hkp)
        as [HXi [_ Hcv]].
      assert (HZ : z2_partition_fn beta Lambda =
                   cosh beta ^ length Lambda *
                   ClusterLogPartition.partition_fn z2_poly_incompat Polys wP).
      { exact (z2_surface_polymer_gas beta Lambda Hnd). }
      assert (Hln : ln (z2_partition_fn beta Lambda) - INR (length Lambda) * ln (cosh beta) =
                    ln (ClusterLogPartition.partition_fn z2_poly_incompat Polys wP)).
      { rewrite HZ, ln_mult; [| apply pow_lt; apply cosh_pos | exact HXi].
        rewrite (ln_pow_INR (cosh beta) (length Lambda) (cosh_pos beta)). ring. }
      rewrite Hln.
      split; [exact Hkp |]. split; [exact Hcv |].
      apply (ClusterLogPartition.Un_cv_Rabs_le _ _ _ Hcv). intro N.
      set (Pins := map (fun p : Plaq4D => [p]) Lambda).
      apply Rle_trans with (rsum Pins aP).
      - apply (kp_series_pins_bound z2_poly_incompat Polys wP aP Pins N poly_incompat_sym
                 (fun g _ => aP_nonneg g) Hkp).
        + intros pin _. apply aP_nonneg.
        + intros pin Hpin. unfold Pins in Hpin. apply in_map_iff in Hpin.
          destruct Hpin as [p [Hpeq Hp]]. subst pin. apply polymer_kp.
          constructor; [exact (proj1 (Forall_forall wf_plaq_4D Lambda) Hwf p Hp) | constructor].
        + intros q Hq. destruct (polymer_facts q Hq) as [Hincl Hne].
          destruct q as [| p rest]; [congruence |].
          exists [p]. split.
          * unfold Pins.
            exact (in_map (fun p' : Plaq4D => [p']) Lambda p (Hincl p (or_introl eq_refl))).
          * unfold z2_poly_incompat. cbn [existsb]. rewrite touch_refl. reflexivity.
      - unfold Pins. rewrite rsum_map.
        apply Rle_trans with (rsum Lambda (fun _ : Plaq4D => 189 * Rabs (tanh beta))).
        + apply Req_le. apply rsum_ext. intros p _. unfold aP. cbn [length INR]. ring.
        + rewrite rsum_const_fun. right. ring.
    Qed.

  End Z2.

  (* TARGET 7d *)
  Theorem z2_free_energy_cluster_expansion :
    Challenge_Z2Gauge4D_FreeEnergyClusterExpansion.
  Proof.
    intros beta Lambda Hsmall Hnd Hwf Polys w a.
    destruct (free_energy_expansion beta Lambda Hsmall Hnd Hwf) as [Hkp [Hcv Hbd]].
    split; [| split].
    - intros g Hg. exact (Hkp g Hg).
    - intros eps Heps. destruct (Hcv eps Heps) as [N0 HN0]. exists N0. intros n Hn.
      assert (Heq :
        Challenge.kp_series Polys n
          (fun X => kp_ursell_fn z2_poly_incompat X * kp_prod_weight w X) =
        KoteckyPreiss.kp_series (z2_polymers Lambda) n
          (fun X => PenroseTreeBound.ursell_fn z2_poly_incompat X *
                    KoteckyPreiss.prod_weight (wP beta) X)).
      { transitivity
          (KoteckyPreiss.kp_series Polys n
             (fun X => kp_ursell_fn z2_poly_incompat X * kp_prod_weight w X)).
        - apply Verify.kp_series_eq.
        - apply kp_series_ext. intro X.
          exact (f_equal2 Rmult (Verify.kp_ursell_fn_eq z2_poly_incompat X) eq_refl). }
      rewrite Heq. exact (HN0 n Hn).
    - exact Hbd.
  Qed.

End Z2FreeEnergy.
