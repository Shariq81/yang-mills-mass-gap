(* =========================================================================
   ym/su2_clustering.v

   Strong-coupling exponential clustering of the 4D SU(2) Wilson lattice
   gauge theory (TARGET 8a), proved directly for the frozen objects of
   `verification/ChallengeSU2Gauge.v`:

     for every non-empty finite list G of unit quaternions (the a-priori
     link distribution), every mu >= 0, every beta with
     168 * |beta| <= exp(- mu), every finite duplicate-free volume Lambda
     of canonical plaquettes of Z^4, every canonical plaquette p1, every
     plaquette p2 and all observables f, g bounded by 1 that depend only on
     the links of p1 and of p2 respectively,

       |<f g> - <f><g>| <= 4 * exp(- mu * (dist(p1, p2) - 1)).

   Ingredients:
     - the abstract duplicate-system clustering theorem
       `DupClustering.dup_clustering` (rg/dup_clustering.v), which is
       stated for an arbitrary finite list of values of the link variables,
       applied to the factors phi_p(U) = exp(beta * (1/2) tr U_p).  Because
       (1/2) tr U_p lies in [-1, 1] for SU(2)-valued configurations, the
       doubled oscillation is the same eps = 1 - exp(- 4 |beta|) as for the
       gauge group Z_2;
     - the chain-counting bound `Z2GaugeClustering.reach_sum_bound`, which
       only involves the lattice (21 neighbours, Target 4a) and not the
       gauge group.
   The abstract theorem quantifies over ALL configurations, including those
   with non-unit quaternions; it is applied to the factors and observables
   clamped to [-1, 1], which coincide with the true ones on every
   SU(2)-valued configuration, and only such configurations enter the sums.

   Depends ONLY on Coq stdlib + the frozen challenge files
   + verification.Verify (Target 4a) + rg.dup_clustering + rg.product_measure
   + ym.z2_gauge_expansion + ym.z2_gauge_clustering + ym.su2_algebra.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.Verify.
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.su2_algebra.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import DupClustering Z2GaugeExpansion SU2Algebra.
Open Scope R_scope.

Module SU2Clustering.

  (* =======================================================================
     1. Clamping to [-1, 1]
     ======================================================================= *)

  Definition clamp (x : R) : R := Rmax (-1) (Rmin 1 x).

  Lemma clamp_bound : forall x, -1 <= clamp x <= 1.
  Proof.
    intro x. unfold clamp. split; [apply Rmax_l |].
    apply Rmax_lub; [lra | apply Rmin_l].
  Qed.

  Lemma clamp_id : forall x, -1 <= x <= 1 -> clamp x = x.
  Proof.
    intros x [H1 H2]. unfold clamp.
    rewrite (Rmin_right 1 x H2), (Rmax_right (-1) x H1). reflexivity.
  Qed.

  Lemma clamp_id_abs : forall x, Rabs x <= 1 -> clamp x = x.
  Proof.
    intros x H. apply clamp_id. unfold Rabs in H. destruct (Rcase_abs x); lra.
  Qed.

  Lemma clamp_diff : forall x y, Rabs (clamp x - clamp y) <= 2.
  Proof.
    intros x y. pose proof (clamp_bound x). pose proof (clamp_bound y).
    unfold Rabs. destruct (Rcase_abs (clamp x - clamp y)); lra.
  Qed.

  Lemma times_bound : forall beta c, -1 <= c <= 1 ->
    - Rabs beta <= beta * c <= Rabs beta.
  Proof.
    intros beta c [H1 H2]. unfold Rabs. destruct (Rcase_abs beta); split; nra.
  Qed.

  (* =======================================================================
     2. The SU(2) gauge theory as an instance of the abstract model
     ======================================================================= *)

  Section Instance.
    Variable G : list Quat.
    Hypothesis G_nonempty : G <> [].
    Hypothesis G_unit : Forall su2_unit G.
    Variable beta : R.
    Variable Lambda : list Plaq4D.
    Hypothesis Hnd : NoDup Lambda.
    Hypothesis Hwf : Forall wf_plaq_4D Lambda.
    Variables f g : SU2Config -> R.
    Variables p1 p2 : Plaq4D.
    Hypothesis Hwf1 : wf_plaq_4D p1.
    Hypothesis f_loc : su2_local_at f p1.
    Hypothesis g_loc : su2_local_at g p2.
    Hypothesis f_bd : forall U, su2_unit_config U -> Rabs (f U) <= 1.
    Hypothesis g_bd : forall U, su2_unit_config U -> Rabs (g U) <= 1.

    Local Notation E := (z2_links Lambda).
    Local Notation mlowI := (Z2GaugeClustering.mlow beta).
    Local Notation epsI := (Z2GaugeClustering.epsv beta).

    Definition base : SU2Config := fun _ => qone.

    Definition phi (p : Plaq4D) (U : SU2Config) : R :=
      exp (beta * clamp (su2_plaq U p)).
    Definition fc (U : SU2Config) : R := clamp (f U).
    Definition gc (U : SU2Config) : R := clamp (g U).

    Local Notation NfI :=
      (Nf Link4D Quat Plaq4D link4D_eqb G phi Lambda E base).
    Local Notation ZfI :=
      (Zf Link4D Quat Plaq4D link4D_eqb G phi Lambda E base).

    Lemma G_good : forall v, In v G -> su2_unit v.
    Proof. exact (proj1 (Forall_forall su2_unit G) G_unit). Qed.

    (* ---------- hypotheses of the abstract theorem ---------- *)

    Lemma phi_local : forall b (A A' : Link4D -> Quat), In b Lambda ->
      (forall e, In e (plaq4D_links b) -> A e = A' e) -> phi b A = phi b A'.
    Proof.
      intros b A A' _ H. unfold phi. rewrite (plaq_local A A' b H). reflexivity.
    Qed.

    Lemma phi_pos : forall b (A : Link4D -> Quat), In b Lambda -> 0 < phi b A.
    Proof. intros b A _. unfold phi. apply exp_pos. Qed.

    Lemma phi_prod_bounds : forall b (A A' : SU2Config),
      mlowI <= phi b A * phi b A' <= exp (2 * Rabs beta).
    Proof.
      intros b A A'. unfold phi, Z2GaugeClustering.mlow. rewrite <- exp_plus.
      pose proof (times_bound beta _ (clamp_bound (su2_plaq A b))) as H1.
      pose proof (times_bound beta _ (clamp_bound (su2_plaq A' b))) as H2.
      split; apply Z2GaugeClustering.exp_le; lra.
    Qed.

    Lemma phi_osc_lo : forall b (A A' : Link4D -> Quat), In b Lambda ->
      mlowI <= phi b A * phi b A'.
    Proof. intros b A A' _. apply phi_prod_bounds. Qed.

    Lemma phi_osc_hi : forall b (A A' : Link4D -> Quat), In b Lambda ->
      phi b A * phi b A' - mlowI <= epsI * (phi b A * phi b A').
    Proof.
      intros b A A' _. destruct (phi_prod_bounds b A A') as [Hlo Hhi].
      set (P := phi b A * phi b A') in *.
      pose proof (exp_pos (- (4 * Rabs beta))) as He4.
      assert (Hkey : P * exp (- (4 * Rabs beta)) <= mlowI).
      { apply Rle_trans with (exp (2 * Rabs beta) * exp (- (4 * Rabs beta))).
        - apply Rmult_le_compat_r; [lra | exact Hhi].
        - rewrite <- exp_plus. unfold Z2GaugeClustering.mlow.
          apply Z2GaugeClustering.exp_le. lra. }
      unfold Z2GaugeClustering.epsv. lra.
    Qed.

    Lemma fc_local : forall A A' : Link4D -> Quat,
      (forall e, In e (plaq4D_links p1) -> A e = A' e) -> fc A = fc A'.
    Proof. intros A A' H. unfold fc. rewrite (f_loc A A' H). reflexivity. Qed.

    Lemma gc_local : forall A A' : Link4D -> Quat,
      (forall e, In e (plaq4D_links p2) -> A e = A' e) -> gc A = gc A'.
    Proof. intros A A' H. unfold gc. rewrite (g_loc A A' H). reflexivity. Qed.

    Lemma fc_osc : forall A A' : Link4D -> Quat, Rabs (fc A - fc A') <= 2.
    Proof. intros A A'. apply clamp_diff. Qed.

    Lemma gc_osc : forall A A' : Link4D -> Quat, Rabs (gc A - gc A') <= 2.
    Proof. intros A A'. apply clamp_diff. Qed.

    (* ---------- on SU(2)-valued configurations nothing is clamped ---------- *)

    Lemma weight_W : forall U, su2_unit_config U ->
      W Link4D Quat Plaq4D phi Lambda U = exp (- su2_wilson_action beta Lambda U).
    Proof.
      intros U HU. unfold W. rewrite boltzmann_rprod. apply rprod_ext. intros p _.
      unfold phi. rewrite (clamp_id _ (plaq_bound U p HU)). reflexivity.
    Qed.

    Lemma base_unit : su2_unit_config base.
    Proof. exact unit_config_one. Qed.

    Lemma csum_unit_ext : forall F F' : SU2Config -> R,
      (forall U, su2_unit_config U -> F U = F' U) ->
      csum Link4D Quat link4D_eqb G E F base = csum Link4D Quat link4D_eqb G E F' base.
    Proof.
      intros F F' H.
      exact (ProductMeasure.csum_ext_good Link4D Quat link4D_eqb G su2_unit G_good
               E F F' H base base_unit).
    Qed.

    Lemma expect_bridge : forall F Fc : SU2Config -> R,
      (forall U, su2_unit_config U -> Fc U = F U) ->
      su2_expect_on G beta Lambda F = NfI Fc / ZfI.
    Proof.
      intros F Fc HF.
      assert (HN : NfI Fc =
                   csum Link4D Quat link4D_eqb G E
                     (fun U => F U * exp (- su2_wilson_action beta Lambda U)) base).
      { unfold Nf. apply csum_unit_ext. intros U HU.
        rewrite (HF U HU), (weight_W U HU). reflexivity. }
      assert (HZ : ZfI =
                   csum Link4D Quat link4D_eqb G E
                     (fun U => exp (- su2_wilson_action beta Lambda U)) base).
      { unfold Zf. apply csum_unit_ext. intros U HU. apply weight_W. exact HU. }
      rewrite expect_csum, HN, HZ. reflexivity.
    Qed.

    (* ---------- the clustering bound ---------- *)

    Variable mu : R.
    Hypothesis Hmu : 0 <= mu.
    Hypothesis Hsmall : 168 * Rabs beta <= exp (- mu).

    Theorem instance_clustering :
      Rabs (su2_truncated_on G beta Lambda f g)
      <= 4 * exp (- mu * (plaq4D_dist p1 p2 - 1)).
    Proof.
      pose proof (dup_clustering Link4D Quat Plaq4D
                    link4D_eqb link4D_eqb_spec
                    Z2GaugeClustering.plaq4D_eqb Z2GaugeClustering.plaq4D_eqb_spec
                    G plaq4D_links phi Lambda E base fc gc
                    (plaq4D_links p1) (plaq4D_links p2)
                    mlowI epsI 2 2
                    Hnd G_nonempty
                    phi_local phi_pos
                    (Z2GaugeClustering.mlow_pos beta) (Z2GaugeClustering.epsv_nonneg beta)
                    phi_osc_lo phi_osc_hi
                    fc_local gc_local fc_osc gc_osc) as Hdup.
      unfold su2_truncated_on.
      rewrite (expect_bridge (fun U => f U * g U) (fun U => fc U * gc U)).
      2: { intros U HU. unfold fc, gc.
           rewrite (clamp_id_abs _ (f_bd U HU)), (clamp_id_abs _ (g_bd U HU)). reflexivity. }
      rewrite (expect_bridge f fc).
      2: { intros U HU. unfold fc. apply clamp_id_abs. apply f_bd. exact HU. }
      rewrite (expect_bridge g gc).
      2: { intros U HU. unfold gc. apply clamp_id_abs. apply g_bd. exact HU. }
      eapply Rle_trans; [exact Hdup |].
      pose proof (Z2GaugeClustering.reach_sum_bound beta Lambda Hnd Hwf p2 mu Hmu Hsmall
                    (S (length Lambda)) p1 Hwf1) as Hsum.
      lra.
    Qed.

  End Instance.

  (* TARGET 8a *)
  Theorem su2_strong_coupling_clustering : Challenge_SU2Gauge4D_StrongCouplingClustering.
  Proof.
    intros G beta mu Lambda p1 p2 f g HG HGu Hmu Hsmall Hnd Hwf Hwf1 Hf Hg Hfb Hgb.
    exact (instance_clustering G HG HGu beta Lambda Hnd Hwf f g p1 p2 Hwf1 Hf Hg Hfb Hgb
             mu Hmu Hsmall).
  Qed.

End SU2Clustering.
