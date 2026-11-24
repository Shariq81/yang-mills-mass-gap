(* =========================================================================
   ym/z2_gauge_clustering.v

   Strong-coupling exponential clustering of the gauge-invariant connected
   plaquette correlator of the 4D Z_2 Wilson lattice gauge theory, proved
   directly for the frozen objects of `verification/ChallengeZ2Gauge.v`:

     for every mu >= 0, every beta with 168 * |beta| <= exp(- mu), every
     finite duplicate-free volume Lambda of canonical plaquettes of Z^4 and
     all p1, p2 in Lambda,

       |<U_p1 U_p2> - <U_p1><U_p2>| <= 4 * exp(- mu * (dist(p1, p2) - 1)).

   Ingredients:
     - the abstract duplicate-system clustering theorem
       `DupClustering.dup_clustering` (rg/dup_clustering.v) applied to the
       factors phi_p(U) = exp(beta * U_p), whose doubled oscillation is
       eps = 1 - exp(- 4 |beta|) <= 4 |beta|;
     - the verified exact 21-neighbour theorem for Z^4 plaquettes
       (`Verify.verified_lattice4D_exact21`, Target 4a), which bounds the
       number of chains of k link-sharing plaquettes by 21^k;
     - link-sharing plaquettes are at scaled anchor distance <= 1.

   Depends ONLY on Coq stdlib + verification.Challenge
   + verification.ChallengeZ2Gauge + verification.Verify (Target 4a)
   + rg.dup_clustering + ym.z2_gauge_expansion.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.Verify.
Require Import rg.dup_clustering.
Require Import ym.z2_gauge_expansion.

Import ListNotations.
Import Challenge ChallengeZ2Gauge DupClustering Z2GaugeExpansion.
Open Scope R_scope.

Module Z2GaugeClustering.

  (* =======================================================================
     1. Plaquette equality and elementary Z^4 geometry
     ======================================================================= *)

  Definition plaq4D_eqb (p q : Plaq4D) : bool :=
    site4D_eqb (p4_site p) (p4_site q) &&
    dir4D_eqb (p4_mu p) (p4_mu q) &&
    dir4D_eqb (p4_nu p) (p4_nu q).

  Lemma plaq4D_eqb_spec : forall p q, plaq4D_eqb p q = true <-> p = q.
  Proof.
    intros [s1 m1 n1] [s2 m2 n2]. unfold plaq4D_eqb. cbn [p4_site p4_mu p4_nu].
    rewrite !andb_true_iff, site4D_eqb_spec, !dir4D_eqb_spec. split.
    - intros [[H1 H2] H3]. subst. reflexivity.
    - intro H. injection H as H1 H2 H3. subst. repeat split.
  Qed.

  Lemma shift4D_comm : forall s a b,
    shift4D (shift4D s a) b = shift4D (shift4D s b) a.
  Proof. intros [t x y z] [] []; reflexivity. Qed.

  Lemma link_in_edges : forall p l, In l (plaq4D_links p) ->
    In (fst l, shift4D (fst l) (snd l)) (plaq4D_edges p).
  Proof.
    intros [s mu nu] l Hl. unfold plaq4D_links in Hl. unfold plaq4D_edges.
    cbn [p4_site p4_mu p4_nu] in *.
    destruct Hl as [Hl | [Hl | [Hl | [Hl | []]]]]; subst l; cbn [fst snd].
    - left. reflexivity.
    - right. left. reflexivity.
    - right. right. left. reflexivity.
    - right. right. right. left. rewrite (shift4D_comm s nu mu). reflexivity.
  Qed.

  (* plaquettes sharing a link overlap in the sense of the frozen Challenge.v *)
  Lemma share_link_overlap : forall p q,
    (exists l, In l (plaq4D_links p) /\ In l (plaq4D_links q)) -> plaq4D_overlap p q.
  Proof.
    intros p q [l [Hp Hq]]. destruct (plaq4D_eqb p q) eqn:He.
    - left. apply plaq4D_eqb_spec. exact He.
    - right. split.
      + intro Heq. apply plaq4D_eqb_spec in Heq. congruence.
      + exists (fst l, shift4D (fst l) (snd l)), (fst l, shift4D (fst l) (snd l)).
        split; [apply link_in_edges; exact Hp |].
        split; [apply link_in_edges; exact Hq |].
        left. split; reflexivity.
  Qed.

  Lemma manhattan_refl : forall s, site4D_manhattan s s = 0%Z.
  Proof. intros [t x y z]. unfold site4D_manhattan. cbn [s4_t s4_x s4_y s4_z]. lia. Qed.

  Lemma manhattan_sym : forall s1 s2, site4D_manhattan s1 s2 = site4D_manhattan s2 s1.
  Proof.
    intros [t1 x1 y1 z1] [t2 x2 y2 z2]. unfold site4D_manhattan.
    cbn [s4_t s4_x s4_y s4_z]. lia.
  Qed.

  Lemma manhattan_triangle : forall s1 s2 s3,
    (site4D_manhattan s1 s3 <= site4D_manhattan s1 s2 + site4D_manhattan s2 s3)%Z.
  Proof.
    intros [t1 x1 y1 z1] [t2 x2 y2 z2] [t3 x3 y3 z3]. unfold site4D_manhattan.
    cbn [s4_t s4_x s4_y s4_z]. lia.
  Qed.

  Lemma manhattan_shift : forall s d, site4D_manhattan s (shift4D s d) = 1%Z.
  Proof.
    intros [t x y z] []; unfold site4D_manhattan, shift4D; cbn [s4_t s4_x s4_y s4_z]; lia.
  Qed.

  Lemma link_site_near : forall p l, In l (plaq4D_links p) ->
    (site4D_manhattan (p4_site p) (fst l) <= 1)%Z.
  Proof.
    intros [s mu nu] l Hl. unfold plaq4D_links in Hl. cbn [p4_site p4_mu p4_nu] in *.
    destruct Hl as [Hl | [Hl | [Hl | [Hl | []]]]]; subst l; cbn [fst].
    - rewrite manhattan_refl. lia.
    - rewrite manhattan_refl. lia.
    - rewrite manhattan_shift. lia.
    - rewrite manhattan_shift. lia.
  Qed.

  Lemma share_link_dist : forall p q,
    (exists l, In l (plaq4D_links p) /\ In l (plaq4D_links q)) -> plaq4D_dist p q <= 1.
  Proof.
    intros p q [l [Hp Hq]]. unfold plaq4D_dist.
    pose proof (link_site_near p l Hp) as H1.
    pose proof (link_site_near q l Hq) as H2.
    pose proof (manhattan_triangle (p4_site p) (fst l) (p4_site q)) as H3.
    rewrite (manhattan_sym (fst l) (p4_site q)) in H3.
    assert (Hz : (site4D_manhattan (p4_site p) (p4_site q) <= 2)%Z) by lia.
    apply IZR_le in Hz. lra.
  Qed.

  Lemma plaq4D_dist_triangle : forall p q r,
    plaq4D_dist p r <= plaq4D_dist p q + plaq4D_dist q r.
  Proof.
    intros p q r. unfold plaq4D_dist.
    pose proof (manhattan_triangle (p4_site p) (p4_site q) (p4_site r)) as H.
    apply IZR_le in H. rewrite plus_IZR in H. lra.
  Qed.

  (* =======================================================================
     2. Elementary real-analysis helpers
     ======================================================================= *)

  Lemma exp_le : forall x y, x <= y -> exp x <= exp y.
  Proof.
    intros x y H. destruct (Rle_lt_or_eq_dec x y H) as [Hlt | Heq].
    - left. apply exp_increasing. exact Hlt.
    - rewrite Heq. apply Rle_refl.
  Qed.

  Lemma exp_pow_INR : forall x n, exp x ^ n = exp (INR n * x).
  Proof.
    intros x n. induction n as [| n IH].
    - cbn [pow INR]. rewrite Rmult_0_l, exp_0. reflexivity.
    - cbn [pow]. rewrite IH, <- exp_plus. f_equal. rewrite S_INR. ring.
  Qed.

  Lemma pm1_times_bound : forall beta s, (s = 1 \/ s = -1) ->
    - Rabs beta <= beta * s <= Rabs beta.
  Proof.
    intros beta s Hs. unfold Rabs. destruct (Rcase_abs beta); destruct Hs; subst s; lra.
  Qed.

  Lemma pm1_diff_bound : forall a b, (a = 1 \/ a = -1) -> (b = 1 \/ b = -1) ->
    Rabs (a - b) <= 2.
  Proof.
    intros a b Ha Hb. unfold Rabs. destruct (Rcase_abs (a - b)); destruct Ha, Hb; subst; lra.
  Qed.

  Lemma geom_half_sum : forall n, rsum (seq 0 n) (fun k => (/ 2) ^ k) = 2 - 2 * (/ 2) ^ n.
  Proof.
    induction n as [| n IH].
    - cbn [seq]. rewrite rsum_nil. cbn [pow]. lra.
    - rewrite seq_S, rsum_app, IH, rsum_cons, rsum_nil. cbn [Nat.add pow]. lra.
  Qed.

  (* =======================================================================
     3. The Z_2 gauge theory as an instance of the abstract model
     ======================================================================= *)

  Section Instance.
    Variable beta : R.
    Variable Lambda : list Plaq4D.
    Hypothesis Hnd : NoDup Lambda.
    Hypothesis Hwf : Forall wf_plaq_4D Lambda.

    Definition phi (p : Plaq4D) (U : Z2Config) : R := exp (beta * z2_plaq U p).
    Definition mlow : R := exp (- (2 * Rabs beta)).
    Definition epsv : R := 1 - exp (- (4 * Rabs beta)).
    Definition base : Z2Config := fun _ => false.
    Local Notation vals2 := (false :: true :: nil).

    Local Notation E := (z2_links Lambda).
    Local Notation NfI := (Nf Link4D bool Plaq4D link4D_eqb vals2 phi Lambda E base).
    Local Notation ZfI := (Zf Link4D bool Plaq4D link4D_eqb vals2 phi Lambda E base).
    Local Notation touchI := (touchb Link4D link4D_eqb).

    Lemma configs_csum : forall (El : list Link4D) (F : Z2Config -> R) (U : Z2Config),
      rsum (z2_configs_from El U) F = csum Link4D bool link4D_eqb vals2 El F U.
    Proof.
      induction El as [| l El IH]; intros F U.
      - cbn [z2_configs_from csum]. rewrite rsum_cons, rsum_nil. ring.
      - cbn [z2_configs_from csum].
        rewrite rsum_app, !IH, !rsum_cons, rsum_nil.
        change (upd Link4D bool link4D_eqb U l false) with (z2_update U l false).
        change (upd Link4D bool link4D_eqb U l true) with (z2_update U l true).
        ring.
    Qed.

    Lemma weight_W : forall U,
      exp (- z2_wilson_action beta Lambda U) = W Link4D bool Plaq4D phi Lambda U.
    Proof. intro U. rewrite boltzmann_rprod. reflexivity. Qed.

    Lemma haar_csum : forall F,
      z2_haar E F = / 2 ^ length E * csum Link4D bool link4D_eqb vals2 E F base.
    Proof.
      intro F. unfold z2_haar, z2_configs. f_equal.
      exact (configs_csum E F (fun _ => false)).
    Qed.

    Lemma expect_bridge : forall F, z2_expect beta Lambda F = NfI F / ZfI.
    Proof.
      intro F. unfold z2_expect, z2_partition_fn. rewrite !haar_csum.
      assert (H2 : 2 ^ length E <> 0) by (apply pow_nonzero; lra).
      assert (HN : csum Link4D bool link4D_eqb vals2 E
                     (fun U : Z2Config => F U * exp (- z2_wilson_action beta Lambda U)) base = NfI F).
      { unfold Nf. apply csum_ext. intro U. rewrite weight_W. reflexivity. }
      assert (HZ : csum Link4D bool link4D_eqb vals2 E
                     (fun U : Z2Config => exp (- z2_wilson_action beta Lambda U)) base = ZfI).
      { unfold Zf. apply csum_ext. intro U. apply weight_W. }
      rewrite HN, HZ.
      assert (HZpos : 0 < ZfI).
      { apply Zf_pos; [discriminate |]. intros b A _. unfold phi. apply exp_pos. }
      field. repeat split; first [exact H2 | lra].
    Qed.

    (* ---------- hypotheses of the abstract theorem ---------- *)

    Lemma phi_local : forall b (A A' : Link4D -> bool), In b Lambda ->
      (forall e, In e (plaq4D_links b) -> A e = A' e) -> phi b A = phi b A'.
    Proof.
      intros b A A' _ H. unfold phi, z2_plaq.
      rewrite (holonomy_local A A' (plaq4D_links b) H). reflexivity.
    Qed.

    Lemma phi_pos : forall b (A : Z2Config), In b Lambda -> 0 < phi b A.
    Proof. intros b A _. unfold phi. apply exp_pos. Qed.

    Lemma mlow_pos : 0 < mlow.
    Proof. unfold mlow. apply exp_pos. Qed.

    Lemma epsv_nonneg : 0 <= epsv.
    Proof.
      unfold epsv. pose proof (Rabs_pos beta) as Hb.
      pose proof (exp_le (- (4 * Rabs beta)) 0 ltac:(lra)) as H. rewrite exp_0 in H. lra.
    Qed.

    Lemma epsv_le : epsv <= 4 * Rabs beta.
    Proof.
      unfold epsv. pose proof (exp_ineq1_le (- (4 * Rabs beta))) as H. lra.
    Qed.

    Lemma phi_prod_bounds : forall b (A A' : Z2Config),
      mlow <= phi b A * phi b A' <= exp (2 * Rabs beta).
    Proof.
      intros b A A'. unfold phi, mlow. rewrite <- exp_plus.
      pose proof (pm1_times_bound beta (z2_plaq A b) (holonomy_pm1 A (plaq4D_links b))) as H1.
      pose proof (pm1_times_bound beta (z2_plaq A' b) (holonomy_pm1 A' (plaq4D_links b))) as H2.
      split; apply exp_le; lra.
    Qed.

    Lemma phi_osc_lo : forall b (A A' : Z2Config), In b Lambda -> mlow <= phi b A * phi b A'.
    Proof. intros b A A' _. apply phi_prod_bounds. Qed.

    Lemma phi_osc_hi : forall b (A A' : Z2Config), In b Lambda ->
      phi b A * phi b A' - mlow <= epsv * (phi b A * phi b A').
    Proof.
      intros b A A' _. destruct (phi_prod_bounds b A A') as [Hlo Hhi].
      set (P := phi b A * phi b A') in *.
      pose proof (exp_pos (- (4 * Rabs beta))) as He4.
      assert (Hkey : P * exp (- (4 * Rabs beta)) <= mlow).
      { apply Rle_trans with (exp (2 * Rabs beta) * exp (- (4 * Rabs beta))).
        - apply Rmult_le_compat_r; [lra | exact Hhi].
        - rewrite <- exp_plus. unfold mlow. apply exp_le. lra. }
      unfold epsv. lra.
    Qed.

    Lemma plaq_local : forall p (A A' : Link4D -> bool),
      (forall e, In e (plaq4D_links p) -> A e = A' e) -> z2_plaq A p = z2_plaq A' p.
    Proof. intros p A A' H. unfold z2_plaq. apply holonomy_local. exact H. Qed.

    Lemma plaq_osc : forall p (A A' : Z2Config), Rabs (z2_plaq A p - z2_plaq A' p) <= 2.
    Proof.
      intros p A A'. apply pm1_diff_bound; unfold z2_plaq; apply holonomy_pm1.
    Qed.

    (* ---------- chains of link-sharing plaquettes on Z^4 ---------- *)

    Lemma touch_share : forall p q,
      touchI (plaq4D_links p) (plaq4D_links q) = true ->
      exists l, In l (plaq4D_links p) /\ In l (plaq4D_links q).
    Proof.
      intros p q H.
      exact (proj1 (touchb_true Link4D link4D_eqb link4D_eqb_spec _ _) H).
    Qed.

    Lemma touch_count_21 : forall p, wf_plaq_4D p ->
      (length (filter (fun b => touchI (plaq4D_links p) (plaq4D_links b)) Lambda) <= 21)%nat.
    Proof.
      intros p Hp.
      destruct Verify.verified_lattice4D_exact21 as [nb [_ [_ [Hspec Hlen]]]].
      rewrite <- (Hlen p Hp).
      apply NoDup_incl_length; [apply NoDup_filter; exact Hnd |].
      intros b Hb. apply filter_In in Hb. destruct Hb as [HbL Ht].
      apply (Hspec p b Hp (proj1 (Forall_forall wf_plaq_4D Lambda) Hwf b HbL)).
      apply share_link_overlap. apply touch_share. exact Ht.
    Qed.

    Variable p2 : Plaq4D.

    Local Notation reachI :=
      (reach Link4D Plaq4D link4D_eqb plaq4D_links Lambda (plaq4D_links p2) epsv).

    Lemma reach_far : forall k p,
      INR k + 1 < plaq4D_dist p p2 -> reachI k (plaq4D_links p) = 0.
    Proof.
      induction k as [| k IH]; intros p Hfar.
      - cbn [reach]. destruct (touchI (plaq4D_links p) (plaq4D_links p2)) eqn:Ht; [| reflexivity].
        pose proof (share_link_dist p p2 (touch_share p p2 Ht)) as Hd.
        cbn [INR] in Hfar. lra.
      - cbn [reach]. apply rsum_zero. intros b _.
        destruct (touchI (plaq4D_links p) (plaq4D_links b)) eqn:Ht; [| reflexivity].
        pose proof (share_link_dist p b (touch_share p b Ht)) as Hd.
        pose proof (plaq4D_dist_triangle p b p2) as Htri.
        rewrite S_INR in Hfar.
        rewrite (IH b ltac:(lra)). ring.
    Qed.

    Lemma reach_le : forall k p, wf_plaq_4D p ->
      reachI k (plaq4D_links p) <= (21 * epsv) ^ k.
    Proof.
      pose proof epsv_nonneg as He.
      induction k as [| k IH]; intros p Hp.
      - cbn [reach pow]. destruct (touchI (plaq4D_links p) (plaq4D_links p2)); lra.
      - cbn [reach pow].
        apply Rle_trans with
          (rsum Lambda (fun b =>
             if touchI (plaq4D_links p) (plaq4D_links b)
             then epsv * (21 * epsv) ^ k else 0)).
        + apply rsum_le. intros b Hb.
          destruct (touchI (plaq4D_links p) (plaq4D_links b)); [| apply Rle_refl].
          apply Rmult_le_compat_l; [exact He |].
          apply IH. exact (proj1 (Forall_forall wf_plaq_4D Lambda) Hwf b Hb).
        + rewrite (rsum_indicator_const
                     (fun b => touchI (plaq4D_links p) (plaq4D_links b))
                     (epsv * (21 * epsv) ^ k) Lambda).
          pose proof (touch_count_21 p Hp) as Hcnt. apply le_INR in Hcnt.
          assert (H21 : INR 21 = 21) by (cbn [INR]; lra).
          rewrite H21 in Hcnt.
          assert (Hpw : 0 <= epsv * (21 * epsv) ^ k).
          { apply Rmult_le_pos; [exact He |]. apply pow_le. lra. }
          apply Rle_trans with (21 * (epsv * (21 * epsv) ^ k)).
          * apply Rmult_le_compat_r; assumption.
          * right. ring.
    Qed.

    (* ---------- the clustering bound ---------- *)

    Variable mu : R.
    Hypothesis Hmu : 0 <= mu.
    Hypothesis Hsmall : 168 * Rabs beta <= exp (- mu).

    Lemma reach_term_bound : forall k p, wf_plaq_4D p ->
      reachI k (plaq4D_links p)
      <= exp (- mu * (plaq4D_dist p p2 - 1)) * (/ 2) ^ k.
    Proof.
      intros k p Hp.
      pose proof (exp_pos (- mu * (plaq4D_dist p p2 - 1))) as Hepos.
      assert (Hhalf : 0 < (/ 2) ^ k) by (apply pow_lt; lra).
      destruct (Rlt_le_dec (INR k + 1) (plaq4D_dist p p2)) as [Hfar | Hnear].
      - rewrite (reach_far k p Hfar). left. apply Rmult_lt_0_compat; assumption.
      - eapply Rle_trans; [apply (reach_le k p Hp) |].
        pose proof epsv_nonneg as He. pose proof epsv_le as Hel.
        pose proof (exp_pos (- mu)) as Hem.
        apply Rle_trans with ((exp (- mu) * / 2) ^ k).
        + apply pow_incr. lra.
        + rewrite Rpow_mult_distr.
          apply Rmult_le_compat_r; [left; exact Hhalf |].
          rewrite exp_pow_INR. apply exp_le.
          assert (Hk : plaq4D_dist p p2 - 1 <= INR k) by lra.
          assert (Hprod : mu * (plaq4D_dist p p2 - 1) <= mu * INR k).
          { apply Rmult_le_compat_l; assumption. }
          lra.
    Qed.

    Lemma reach_sum_bound : forall n p, wf_plaq_4D p ->
      rsum (seq 0 n) (fun k => reachI k (plaq4D_links p))
      <= 2 * exp (- mu * (plaq4D_dist p p2 - 1)).
    Proof.
      intros n p Hp.
      pose proof (exp_pos (- mu * (plaq4D_dist p p2 - 1))) as Hepos.
      apply Rle_trans with
        (rsum (seq 0 n) (fun k => exp (- mu * (plaq4D_dist p p2 - 1)) * (/ 2) ^ k)).
      - apply rsum_le. intros k _. apply reach_term_bound. exact Hp.
      - rewrite rsum_scal, geom_half_sum.
        assert (Hh : 0 < (/ 2) ^ n) by (apply pow_lt; lra).
        assert (Hle : 2 - 2 * (/ 2) ^ n <= 2) by lra.
        apply Rle_trans with (exp (- mu * (plaq4D_dist p p2 - 1)) * 2); [| right; ring].
        apply Rmult_le_compat_l; [left; exact Hepos | exact Hle].
    Qed.

    Theorem instance_clustering : forall p1,
      In p1 Lambda ->
      Rabs (z2_plaq_truncated beta Lambda p1 p2)
      <= 4 * exp (- mu * (plaq4D_dist p1 p2 - 1)).
    Proof.
      intros p1 Hp1.
      assert (Hwf1 : wf_plaq_4D p1) by exact (proj1 (Forall_forall wf_plaq_4D Lambda) Hwf p1 Hp1).
      pose proof (dup_clustering Link4D bool Plaq4D
                    link4D_eqb link4D_eqb_spec plaq4D_eqb plaq4D_eqb_spec
                    vals2 plaq4D_links phi Lambda E base
                    (fun U => z2_plaq U p1) (fun U => z2_plaq U p2)
                    (plaq4D_links p1) (plaq4D_links p2)
                    mlow epsv 2 2
                    Hnd ltac:(discriminate)
                    phi_local phi_pos mlow_pos epsv_nonneg phi_osc_lo phi_osc_hi
                    (plaq_local p1) (plaq_local p2) (plaq_osc p1) (plaq_osc p2)) as Hdup.
      unfold z2_plaq_truncated. rewrite !expect_bridge.
      eapply Rle_trans; [exact Hdup |].
      pose proof (reach_sum_bound (S (length Lambda)) p1 Hwf1) as Hsum.
      lra.
    Qed.

  End Instance.

  (* TARGET 7b *)
  Theorem z2_strong_coupling_clustering : Challenge_Z2Gauge4D_StrongCouplingClustering.
  Proof.
    intros beta mu Lambda p1 p2 Hmu Hsmall Hnd Hwf Hp1 _.
    exact (instance_clustering beta Lambda Hnd Hwf p2 mu Hmu Hsmall p1 Hp1).
  Qed.

End Z2GaugeClustering.
