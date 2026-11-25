(* =========================================================================
   ym/su2_area_law.v

   Wilson-loop area law of the 4D SU(2) Wilson lattice gauge theory at
   strong coupling (TARGET 8b), proved directly for the frozen objects of
   `verification/ChallengeSU2Gauge.v`:

     for every non-empty finite list G of unit quaternions that is invariant
     as a multiset under q |-> - q (the a-priori link distribution), every
     beta with 63 * (exp(2 |beta|) - 1) <= 1, every finite duplicate-free
     volume Lambda of canonical plaquettes of Z^4 and every a x b
     rectangular loop all of whose links belong to the link set of Lambda,

       |< (1/2) tr U(loop) >| <= (63 (exp(2|beta|) - 1))^(a b) * exp(2 (a + b)).

   Steps (W = the Wilson loop, C = its links, P_p = (1/2) tr U_p,
   delta = exp(2|beta|) - 1, <.>_0 = the a-priori average):
     1. Mayer expansion.  exp(beta P_p + |beta|) = 1 + r_p with
        0 <= r_p <= delta, so  <W> = N / Z  with
          N = sum_{S <= Lambda} <W prod_{p in S} r_p>_0,
          Z = <prod_{p in Lambda} (1 + r_p)>_0 >= 1.
     2. The a-priori measure is a product measure, so the weight
        rho(S) = <prod of the factors of S>_0 (the loop being an extra
        element whose links are C) factorizes over parts that share no link
        (rg/product_measure.v).  The rooted expansion of
        rg/rooted_polymer_bound.v splits every S into the part T attached to
        the loop and a rest, and since all factors 1 + r_p are >= 1,
          |N| <= Z * sum_{T attached to C} |<W prod_{p in T} r_p>_0|.
     3. Center symmetry.  Write r_p = r_p^+ + r_p^- (even and odd parts
        under U_p -> - U_p) and expand over the subsets R of T carrying the
        odd parts.  Multiplying ONE link variable by the central element -1
        preserves the a-priori measure and multiplies the term of R by
        (-1)^(number of occurrences of the link in C and in the boundaries
        of the plaquettes of R); hence the term vanishes unless the mod-2
        boundary of R is C.
     4. Minimal area (ym/z2_min_area.v): the mod-2 boundary of R is C only
        if |R| >= a * b.  Together with r^+ + |r^-| <= delta this gives
          |<W prod_{p in T} r_p>_0| <= delta^{|T|} if |T| >= a * b, else 0.
     5. Entropy (`Z2AreaLaw.loop_entropy`, the rooted Kotecky-Preiss bound
        for the gas of single plaquettes of activity 1/63):
          sum_{T attached to C} (1/63)^{|T|} <= exp(|C|).

   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.Verify.
Require Import rg.dup_clustering.
Require Import rg.penrose_tree_bound.
Require Import rg.polymer_representation.
Require Import rg.rooted_polymer_bound.
Require Import rg.product_measure.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.z2_polymer_gas.
Require Import ym.z2_even_holonomy.
Require Import ym.z2_min_area.
Require Import ym.z2_area_law.
Require Import ym.su2_algebra.
Require Import ym.su2_clustering.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge.
Import DupClustering Z2GaugeExpansion Z2PolymerGas Z2EvenHolonomy SU2Algebra.
Open Scope R_scope.

Module SU2AreaLaw.

  (* =======================================================================
     1. Small generic lemmas
     ======================================================================= *)

  Lemma dedup_NoDup : forall M, NoDup (link4D_dedup M).
  Proof.
    induction M as [| x M IH]; [constructor |].
    cbn [link4D_dedup]. destruct (existsb (link4D_eqb x) M) eqn:He; [exact IH |].
    constructor; [| exact IH].
    intro Hin. apply (proj1 (dedup_In x M)) in Hin.
    assert (Ht : existsb (link4D_eqb x) M = true).
    { apply existsb_exists. exists x. split; [exact Hin |].
      apply link4D_eqb_spec. reflexivity. }
    congruence.
  Qed.

  Lemma forallb_false_ex : forall {A : Type} (f : A -> bool) (l : list A),
    forallb f l = false -> exists x, In x l /\ f x = false.
  Proof.
    intros A f l. induction l as [| x l IH]; cbn [forallb]; intro H; [discriminate |].
    destruct (f x) eqn:Hx.
    - cbn [andb] in H. destruct (IH H) as [y [Hy Hfy]].
      exists y. split; [right; exact Hy | exact Hfy].
    - exists x. split; [left; reflexivity | exact Hx].
  Qed.

  Lemma sgn_cases : forall k : nat, (-1) ^ k = 1 \/ (-1) ^ k = -1.
  Proof. intro k. rewrite pow_m1. destruct (Nat.even k); [left | right]; reflexivity. Qed.

  (* product of the signs picked up by the plaquettes of a list *)
  Lemma sign_prod : forall (l : Link4D) (R0 : list Plaq4D),
    rprod R0 (fun p => (-1) ^ link4D_count l (plaq4D_links p)) =
    (-1) ^ link4D_count l (flat_map plaq4D_links R0).
  Proof.
    intros l R0. induction R0 as [| p R0 IH].
    - rewrite rprod_nil. reflexivity.
    - rewrite rprod_cons, IH. cbn [flat_map]. rewrite count_app, pow_add. reflexivity.
  Qed.

  Lemma wilson_00 : forall U s mu nu, su2_wilson_loop U s mu nu 0 0 = 1.
  Proof.
    intros U s mu nu. unfold su2_wilson_loop, su2_rect_holonomy, z2_segment.
    cbn [seq map]. rewrite !path_nil. unfold qmul, qconj, qone. cbn [qr qi qj qk]. ring.
  Qed.

  (* =======================================================================
     2. The model
     ======================================================================= *)

  Section Model.
    Variable G : list Quat.
    Hypothesis G_nonempty : G <> [].
    Hypothesis G_unit : Forall su2_unit G.
    Hypothesis G_center : Permutation (map qneg G) G.
    Variable beta : R.
    Variable Lambda : list Plaq4D.
    Hypothesis Hnd : NoDup Lambda.
    Hypothesis Hwf : Forall wf_plaq_4D Lambda.
    Variables (s : Site4D) (mu nu : Dir4D) (a b : nat).
    Hypothesis Hmn : mu <> nu.

    Local Notation LoopC := (z2_rect_loop s mu nu a b).
    Local Notation LinksE := (z2_links Lambda).
    Local Notation Elt := (option Plaq4D).
    Local Notation Cs := (csum Link4D Quat link4D_eqb G).
    Local Notation esuppC := (Z2AreaLaw.esupp LoopC).
    Local Notation LocalOn := (ProductMeasure.local_on Link4D Quat).
    Local Notation connbC :=
      (PolymerRepresentation.connb Link4D Elt link4D_eqb esuppC).
    Local Notation ptouchC :=
      (PolymerRepresentation.ptouch Link4D Elt link4D_eqb esuppC).

    Hypothesis C_in : forall l, In l LoopC -> In l LinksE.
    Hypothesis C_nonempty : LoopC <> [].
    Hypothesis Hsmall : 63 * (exp (2 * Rabs beta) - 1) <= 1.

    Definition U1 : SU2Config := fun _ => qone.
    Definition NG : R := INR (length G).
    Definition delta : R := exp (2 * Rabs beta) - 1.
    Definition Wobs (U : SU2Config) : R := su2_wilson_loop U s mu nu a b.

    (* plaquette factor: 1 + rr x = exp (beta x + |beta|); even and odd parts *)
    Definition rr (x : R) : R := exp (beta * x + Rabs beta) - 1.
    Definition rp (x : R) : R := (rr x + rr (- x)) / 2.
    Definition rm (x : R) : R := (rr x - rr (- x)) / 2.

    (* ---------- elementary facts ---------- *)

    Lemma NG_pos : 0 < NG.
    Proof.
      unfold NG. apply lt_0_INR.
      assert (H : length G <> 0%nat).
      { intro H0. apply G_nonempty. apply length_zero_iff_nil. exact H0. }
      lia.
    Qed.

    Lemma NGE_pos : 0 < NG ^ length LinksE.
    Proof. apply pow_lt. exact NG_pos. Qed.

    Lemma G_good : forall v, In v G -> su2_unit v.
    Proof. exact (proj1 (Forall_forall su2_unit G) G_unit). Qed.

    Lemma U1_unit : su2_unit_config U1.
    Proof. exact unit_config_one. Qed.

    Lemma sigma_sum : forall h : Quat -> R,
      rsum G (fun v => h (qneg v)) = rsum G h.
    Proof.
      intro h. rewrite <- (rsum_map qneg G h).
      apply ProductMeasure.rsum_perm. exact G_center.
    Qed.

    Lemma E_nodup : NoDup LinksE.
    Proof. unfold z2_links. apply dedup_NoDup. Qed.

    Lemma links_in_E : forall (R0 : list Plaq4D) l, incl R0 Lambda ->
      In l (flat_map plaq4D_links R0) -> In l LinksE.
    Proof.
      intros R0 l Hincl Hl. unfold z2_links. apply dedup_In.
      apply in_flat_map in Hl. destruct Hl as [p [Hp Hlp]].
      apply in_flat_map. exists p. split; [apply Hincl; exact Hp | exact Hlp].
    Qed.

    Lemma delta_nonneg : 0 <= delta.
    Proof.
      unfold delta. pose proof (Rabs_pos beta) as Hb.
      pose proof (Z2GaugeClustering.exp_le 0 (2 * Rabs beta) ltac:(lra)) as H.
      rewrite exp_0 in H. lra.
    Qed.

    Lemma rr_bounds : forall x, -1 <= x <= 1 -> 0 <= rr x <= delta.
    Proof.
      intros x Hx. unfold rr, delta.
      pose proof (SU2Clustering.times_bound beta x Hx) as [H1 H2].
      pose proof (Z2GaugeClustering.exp_le 0 (beta * x + Rabs beta) ltac:(lra)) as Ha.
      rewrite exp_0 in Ha.
      pose proof (Z2GaugeClustering.exp_le (beta * x + Rabs beta) (2 * Rabs beta)
                    ltac:(lra)) as Hb.
      lra.
    Qed.

    Lemma rr_split : forall x, rr x = rp x + rm x.
    Proof. intro x. unfold rp, rm. field. Qed.

    Lemma rp_neg : forall x, rp (- x) = rp x.
    Proof. intro x. unfold rp. rewrite Ropp_involutive. field. Qed.

    Lemma rm_neg : forall x, rm (- x) = - rm x.
    Proof. intro x. unfold rm. rewrite Ropp_involutive. field. Qed.

    Lemma rp_nonneg : forall x, -1 <= x <= 1 -> 0 <= rp x.
    Proof.
      intros x Hx. unfold rp.
      pose proof (rr_bounds x Hx) as H1.
      pose proof (rr_bounds (- x) ltac:(lra)) as H2. lra.
    Qed.

    Lemma rp_rm_bound : forall x, -1 <= x <= 1 -> rp x + Rabs (rm x) <= delta.
    Proof.
      intros x Hx. unfold rp, rm.
      pose proof (rr_bounds x Hx) as H1.
      pose proof (rr_bounds (- x) ltac:(lra)) as H2.
      unfold Rabs. destruct (Rcase_abs ((rr x - rr (- x)) / 2)); lra.
    Qed.

    Lemma rp_sgn : forall (k : nat) x, rp ((-1) ^ k * x) = rp x.
    Proof.
      intros k x. destruct (sgn_cases k) as [Hk | Hk]; rewrite Hk.
      - rewrite Rmult_1_l. reflexivity.
      - replace (-1 * x) with (- x) by ring. apply rp_neg.
    Qed.

    Lemma rm_sgn : forall (k : nat) x, rm ((-1) ^ k * x) = (-1) ^ k * rm x.
    Proof.
      intros k x. destruct (sgn_cases k) as [Hk | Hk]; rewrite Hk.
      - rewrite !Rmult_1_l. reflexivity.
      - replace (-1 * x) with (- x) by ring. rewrite rm_neg. ring.
    Qed.

    (* ---------- the weight of a set of elements (loop = None) ---------- *)

    Definition efun (o : Elt) (U : SU2Config) : R :=
      match o with
      | Some p => rr (su2_plaq U p)
      | None => Wobs U
      end.

    Definition rhoE (S : list Elt) : R :=
      Cs LinksE (fun U => rprod S (fun o => efun o U)) U1 / NG ^ length LinksE.

    Lemma efun_local : forall o, LocalOn (esuppC o) (efun o).
    Proof.
      intros [p |] A A' H; cbn [efun Z2AreaLaw.esupp] in *.
      - rewrite (plaq_local A A' p H). reflexivity.
      - unfold Wobs. apply wilson_local. exact H.
    Qed.

    Lemma rprod_local : forall S : list Elt,
      LocalOn (flat_map esuppC S) (fun U => rprod S (fun o => efun o U)).
    Proof.
      intros S A A' H. apply rprod_ext. intros o Ho. apply efun_local.
      intros e He. apply H. apply in_flat_map. exists o. split; assumption.
    Qed.

    (* Step 2: the weight factorizes over parts that share no link *)
    Lemma rhoE_factor : forall (S : list Elt) (f : Elt -> bool),
      (forall p q, In p S -> In q S -> f p = true -> f q = false ->
                   PolymerRepresentation.touch Link4D Elt link4D_eqb esuppC p q = false) ->
      rhoE S = rhoE (filter f S) * rhoE (filter (fun o => negb (f o)) S).
    Proof.
      intros S f Hnt. unfold rhoE.
      pose proof NGE_pos as HN.
      assert (Hdis : forall e, In e (flat_map esuppC (filter f S)) ->
                               In e (flat_map esuppC (filter (fun o => negb (f o)) S)) ->
                               False).
      { intros e H1 H2. apply in_flat_map in H1. destruct H1 as [p [Hp Hep]].
        apply in_flat_map in H2. destruct H2 as [q [Hq Heq]].
        apply filter_In in Hp. destruct Hp as [HpS Hfp].
        apply filter_In in Hq. destruct Hq as [HqS Hfq]. apply negb_true_iff in Hfq.
        pose proof (Hnt p q HpS HqS Hfp Hfq) as Hno.
        assert (Hyes : PolymerRepresentation.touch Link4D Elt link4D_eqb esuppC p q = true).
        { apply (PolymerRepresentation.touch_true Link4D Elt link4D_eqb link4D_eqb_spec).
          exists e. split; assumption. }
        congruence. }
      pose proof (ProductMeasure.csum_indep Link4D Quat link4D_eqb link4D_eqb_spec G
                    (flat_map esuppC (filter f S))
                    (flat_map esuppC (filter (fun o => negb (f o)) S))
                    (fun U => rprod (filter f S) (fun o => efun o U))
                    (fun U => rprod (filter (fun o => negb (f o)) S) (fun o => efun o U))
                    (rprod_local (filter f S))
                    (rprod_local (filter (fun o => negb (f o)) S))
                    Hdis LinksE U1) as Hind.
      rewrite (csum_ext Link4D Quat link4D_eqb G LinksE
                 (fun U => rprod S (fun o => efun o U))
                 (fun U => rprod (filter f S) (fun o => efun o U) *
                           rprod (filter (fun o => negb (f o)) S) (fun o => efun o U))).
      2: { intro U. apply Z2AreaLaw.rprod_filter_split. }
      fold NG in Hind.
      set (X := Cs LinksE
                  (fun U => rprod (filter f S) (fun o => efun o U) *
                            rprod (filter (fun o => negb (f o)) S) (fun o => efun o U)) U1)
        in *.
      set (A1 := Cs LinksE (fun U => rprod (filter f S) (fun o => efun o U)) U1) in *.
      set (B1 := Cs LinksE
                   (fun U => rprod (filter (fun o => negb (f o)) S) (fun o => efun o U)) U1)
        in *.
      set (N := NG ^ length LinksE) in *.
      transitivity (X * N / (N * N)); [field; lra |].
      rewrite Hind. field. lra.
    Qed.

    (* ---------- Step 1: the Mayer expansion ---------- *)

    Definition wfac (U : SU2Config) (p : Plaq4D) : R := 1 + rr (su2_plaq U p).

    (* normalized partition function of a sub-volume *)
    Definition ZZ (Lam : list Plaq4D) : R :=
      Cs LinksE (fun U => rprod Lam (wfac U)) U1 / NG ^ length LinksE.

    (* normalized numerator *)
    Definition NN : R :=
      Cs LinksE (fun U => Wobs U * rprod Lambda (wfac U)) U1 / NG ^ length LinksE.

    Lemma rprod_map_some : forall (T : list Plaq4D) U,
      rprod (map Some T) (fun o => efun o U) = rprod T (fun p => rr (su2_plaq U p)).
    Proof. intros T U. unfold rprod. rewrite map_map. reflexivity. Qed.

    Lemma sum_closed : forall Lam : list Plaq4D,
      rsum (PenroseTreeBound.sublists (map Some Lam)) rhoE = ZZ Lam.
    Proof.
      intro Lam. rewrite (Verify.map_sublists (@Some Plaq4D) Lam), rsum_map.
      unfold ZZ.
      transitivity
        (rsum (PenroseTreeBound.sublists Lam)
           (fun T => Cs LinksE (fun U => rprod T (fun p => rr (su2_plaq U p))) U1)
         / NG ^ length LinksE).
      - unfold Rdiv. rewrite <- rsum_scal_r. apply rsum_ext. intros T _.
        unfold rhoE, Rdiv. apply Rmult_eq_compat_r. apply csum_ext. intro U.
        apply rprod_map_some.
      - unfold Rdiv. apply Rmult_eq_compat_r. symmetry.
        etransitivity;
          [| exact (ProductMeasure.csum_rsum Link4D Quat link4D_eqb G
                      (PenroseTreeBound.sublists Lam) LinksE
                      (fun T U => rprod T (fun p => rr (su2_plaq U p))) U1)].
        apply csum_ext. intro U. unfold wfac.
        exact (rprod_one_plus Lam (fun p => rr (su2_plaq U p))).
    Qed.

    Lemma sum_rooted :
      rsum (PenroseTreeBound.sublists (map Some Lambda)) (fun S => rhoE (None :: S)) = NN.
    Proof.
      rewrite (Verify.map_sublists (@Some Plaq4D) Lambda), rsum_map. unfold NN.
      transitivity
        (rsum (PenroseTreeBound.sublists Lambda)
           (fun T => Cs LinksE
                       (fun U => Wobs U * rprod T (fun p => rr (su2_plaq U p))) U1)
         / NG ^ length LinksE).
      - unfold Rdiv. rewrite <- rsum_scal_r. apply rsum_ext. intros T _.
        unfold rhoE, Rdiv. apply Rmult_eq_compat_r. apply csum_ext. intro U.
        rewrite rprod_cons, rprod_map_some. reflexivity.
      - unfold Rdiv. apply Rmult_eq_compat_r. symmetry.
        etransitivity;
          [| exact (ProductMeasure.csum_rsum Link4D Quat link4D_eqb G
                      (PenroseTreeBound.sublists Lambda) LinksE
                      (fun T U => Wobs U * rprod T (fun p => rr (su2_plaq U p))) U1)].
        apply csum_ext. intro U. cbv beta. rewrite rsum_scal. unfold wfac.
        apply Rmult_eq_compat_l.
        exact (rprod_one_plus Lambda (fun p => rr (su2_plaq U p))).
    Qed.

    Lemma wfac_pos : forall U p, 0 < wfac U p.
    Proof.
      intros U p. unfold wfac, rr.
      pose proof (exp_pos (beta * su2_plaq U p + Rabs beta)). lra.
    Qed.

    Lemma wfac_ge_1 : forall U p, su2_unit_config U -> 1 <= wfac U p.
    Proof.
      intros U p HU. unfold wfac.
      pose proof (rr_bounds _ (plaq_bound U p HU)). lra.
    Qed.

    Lemma ZZ_pos : forall Lam, 0 < ZZ Lam.
    Proof.
      intro Lam. unfold ZZ. apply Rdiv_lt_0_compat; [| exact NGE_pos].
      apply csum_pos; [exact G_nonempty |]. intro A. apply rprod_pos.
      intros p _. apply wfac_pos.
    Qed.

    Lemma ZZ_mono : forall h : Plaq4D -> bool, ZZ (filter h Lambda) <= ZZ Lambda.
    Proof.
      intro h. unfold ZZ, Rdiv.
      apply Rmult_le_compat_r; [left; apply Rinv_0_lt_compat; exact NGE_pos |].
      apply (ProductMeasure.csum_le_good Link4D Quat link4D_eqb G su2_unit G_good).
      - intros A HA. apply ProductMeasure.rprod_filter_le. intros p _.
        apply wfac_ge_1. exact HA.
      - exact U1_unit.
    Qed.

    Lemma weight_wfac : forall U,
      exp (- su2_wilson_action beta Lambda U) =
      exp (- Rabs beta) ^ length Lambda * rprod Lambda (wfac U).
    Proof.
      intro U.
      rewrite boltzmann_rprod, <- (rprod_const (exp (- Rabs beta)) Lambda), <- rprod_mult.
      apply rprod_ext. intros p _. unfold wfac, rr.
      replace (1 + (exp (beta * su2_plaq U p + Rabs beta) - 1))
        with (exp (beta * su2_plaq U p + Rabs beta)) by ring.
      rewrite <- exp_plus. f_equal. ring.
    Qed.

    Lemma expect_ratio : su2_expect_on G beta Lambda Wobs = NN / ZZ Lambda.
    Proof.
      rewrite expect_csum.
      set (kap := exp (- Rabs beta) ^ length Lambda).
      assert (Hk : 0 < kap) by (apply pow_lt; apply exp_pos).
      rewrite (csum_ext Link4D Quat link4D_eqb G LinksE
                 (fun U => Wobs U * exp (- su2_wilson_action beta Lambda U))
                 (fun U => kap * (Wobs U * rprod Lambda (wfac U)))).
      2: { intro U. rewrite weight_wfac. fold kap. ring. }
      rewrite (csum_ext Link4D Quat link4D_eqb G LinksE
                 (fun U => exp (- su2_wilson_action beta Lambda U))
                 (fun U => kap * rprod Lambda (wfac U))).
      2: { intro U. rewrite weight_wfac. reflexivity. }
      rewrite !csum_scal.
      pose proof NGE_pos as HN. pose proof (ZZ_pos Lambda) as HZ.
      unfold NN, ZZ in *. change (fun _ : Link4D => qone) with U1.
      set (A1 := Cs LinksE (fun U => Wobs U * rprod Lambda (wfac U)) U1) in *.
      set (B1 := Cs LinksE (fun U => rprod Lambda (wfac U)) U1) in *.
      set (N := NG ^ length LinksE) in *.
      assert (HB : 0 < B1).
      { replace B1 with (B1 / N * N) by (field; lra).
        apply Rmult_lt_0_compat; assumption. }
      field. repeat split; lra.
    Qed.

    (* ---------- Step 3: expansion in even / odd parts and center symmetry ---------- *)

    Definition term (P : list Plaq4D * list Plaq4D) (U : SU2Config) : R :=
      Wobs U * (rprod (fst P) (fun p => rm (su2_plaq U p)) *
                rprod (snd P) (fun p => rp (su2_plaq U p))).

    Definition aterm (P : list Plaq4D * list Plaq4D) (U : SU2Config) : R :=
      rprod (fst P) (fun p => Rabs (rm (su2_plaq U p))) *
      rprod (snd P) (fun p => rp (su2_plaq U p)).

    Lemma rhoE_root_eq : forall T : list Plaq4D,
      rhoE (None :: map Some T) =
      rsum (ProductMeasure.splits T) (fun P => Cs LinksE (term P) U1)
      / NG ^ length LinksE.
    Proof.
      intro T. unfold rhoE, Rdiv. apply Rmult_eq_compat_r.
      transitivity
        (Cs LinksE (fun U => rsum (ProductMeasure.splits T) (fun P => term P U)) U1).
      - apply csum_ext. intro U. rewrite rprod_cons, rprod_map_some. cbn [efun].
        rewrite (rprod_ext T (fun p => rr (su2_plaq U p))
                   (fun p => rp (su2_plaq U p) + rm (su2_plaq U p)))
          by (intros p _; apply rr_split).
        rewrite (ProductMeasure.rprod_plus_splits T
                   (fun p => rp (su2_plaq U p)) (fun p => rm (su2_plaq U p))).
        rewrite <- rsum_scal. reflexivity.
      - exact (ProductMeasure.csum_rsum Link4D Quat link4D_eqb G
                 (ProductMeasure.splits T) LinksE term U1).
    Qed.

    Lemma term_flip : forall l P U,
      term P (flipU l U) =
      (-1) ^ link4D_count l (LoopC ++ flat_map plaq4D_links (fst P)) * term P U.
    Proof.
      intros l P U. unfold term, Wobs. rewrite wilson_flip.
      rewrite (rprod_ext (fst P) (fun p => rm (su2_plaq (flipU l U) p))
                 (fun p => (-1) ^ link4D_count l (plaq4D_links p) * rm (su2_plaq U p))).
      2: { intros p _. rewrite plaq_flip. apply rm_sgn. }
      rewrite (rprod_ext (snd P) (fun p => rp (su2_plaq (flipU l U) p))
                 (fun p => rp (su2_plaq U p))).
      2: { intros p _. rewrite plaq_flip. apply rp_sgn. }
      rewrite (rprod_mult (fst P) (fun p => (-1) ^ link4D_count l (plaq4D_links p))
                 (fun p => rm (su2_plaq U p))).
      rewrite (sign_prod l (fst P)), count_app, pow_add. ring.
    Qed.

    (* a term whose odd part does not have mod-2 boundary C vanishes *)
    Lemma term_vanish : forall P, incl (fst P) Lambda ->
      allEven (LoopC ++ flat_map plaq4D_links (fst P)) = false ->
      Cs LinksE (term P) U1 = 0.
    Proof.
      intros P Hincl Hodd. unfold allEven in Hodd.
      destruct (forallb_false_ex _ _ Hodd) as [l [Hl Hev]].
      assert (HlE : In l LinksE).
      { apply in_app_or in Hl. destruct Hl as [Hl | Hl]; [apply C_in; exact Hl |].
        exact (links_in_E (fst P) l Hincl Hl). }
      pose proof (ProductMeasure.csum_flip Link4D Quat link4D_eqb link4D_eqb_spec G
                    qneg sigma_sum LinksE l (term P) U1 E_nodup HlE) as Hflip.
      rewrite (csum_ext Link4D Quat link4D_eqb G LinksE
                 (fun A => term P (ProductMeasure.flip Link4D Quat link4D_eqb qneg l A))
                 (fun A => -1 * term P A)) in Hflip.
      2: { intro A.
           change (ProductMeasure.flip Link4D Quat link4D_eqb qneg l A) with (flipU l A).
           rewrite term_flip, pow_m1, Hev. reflexivity. }
      rewrite csum_scal in Hflip. lra.
    Qed.

    Lemma term_abs : forall P U, su2_unit_config U -> Rabs (term P U) <= aterm P U.
    Proof.
      intros P U HU. unfold term, aterm. rewrite !Rabs_mult.
      rewrite (ProductMeasure.rprod_abs (fst P) (fun p => rm (su2_plaq U p))).
      assert (HW : Rabs (Wobs U) <= 1).
      { pose proof (wilson_bound U s mu nu a b HU) as [H1 H2]. unfold Wobs.
        apply Rabs_le. lra. }
      assert (Hp : 0 <= rprod (snd P) (fun p => rp (su2_plaq U p))).
      { apply rprod_nonneg. intros p _. apply rp_nonneg. apply plaq_bound. exact HU. }
      assert (Hm : 0 <= rprod (fst P) (fun p => Rabs (rm (su2_plaq U p)))).
      { apply rprod_nonneg. intros p _. apply Rabs_pos. }
      rewrite (Rabs_pos_eq _ Hp).
      set (X := rprod (fst P) (fun p => Rabs (rm (su2_plaq U p)))) in *.
      set (Y := rprod (snd P) (fun p => rp (su2_plaq U p))) in *.
      pose proof (Rmult_le_pos X Y Hm Hp) as HXY.
      pose proof (Rabs_pos (Wobs U)) as HW0.
      nra.
    Qed.

    Lemma aterm_sum : forall (T : list Plaq4D) U, su2_unit_config U ->
      rsum (ProductMeasure.splits T) (fun P => aterm P U) <= delta ^ length T.
    Proof.
      intros T U HU. unfold aterm.
      rewrite <- (ProductMeasure.rprod_plus_splits T
                    (fun p => rp (su2_plaq U p)) (fun p => Rabs (rm (su2_plaq U p)))).
      rewrite <- (rprod_const delta T). apply rprod_le. intros p _.
      pose proof (plaq_bound U p HU) as Hb.
      pose proof (rp_nonneg _ Hb). pose proof (rp_rm_bound _ Hb).
      pose proof (Rabs_pos (rm (su2_plaq U p))). lra.
    Qed.

    (* ---------- Step 4: the weight of a set attached to the loop ---------- *)

    Definition gbound (T : list Plaq4D) : R :=
      if (a * b <=? length T)%nat then delta ^ length T else 0.

    Lemma gbound_nonneg : forall T, 0 <= gbound T.
    Proof.
      intro T. unfold gbound.
      destruct (a * b <=? length T)%nat; [apply pow_le; exact delta_nonneg | apply Rle_refl].
    Qed.

    Lemma rooted_bound : forall T : list Plaq4D, incl T Lambda ->
      Rabs (rhoE (None :: map Some T)) <= gbound T.
    Proof.
      intros T HT. rewrite rhoE_root_eq. pose proof NGE_pos as HN.
      unfold Rdiv. rewrite Rabs_mult.
      rewrite (Rabs_pos_eq (/ NG ^ length LinksE))
        by (left; apply Rinv_0_lt_compat; exact HN).
      unfold gbound. destruct (a * b <=? length T)%nat eqn:Hab.
      - apply Rmult_le_reg_r with (NG ^ length LinksE); [exact HN |].
        rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
        eapply Rle_trans; [apply rsum_abs |].
        apply Rle_trans with
          (rsum (ProductMeasure.splits T) (fun P => Cs LinksE (aterm P) U1)).
        + apply rsum_le. intros P _.
          eapply Rle_trans; [apply (ProductMeasure.csum_abs Link4D Quat link4D_eqb G) |].
          apply (ProductMeasure.csum_le_good Link4D Quat link4D_eqb G su2_unit G_good);
            [| exact U1_unit].
          intros A HA. apply term_abs. exact HA.
        + rewrite <- (ProductMeasure.csum_rsum Link4D Quat link4D_eqb G
                        (ProductMeasure.splits T) LinksE aterm U1).
          unfold NG.
          rewrite <- (ProductMeasure.csum_const Link4D Quat link4D_eqb G LinksE
                        (delta ^ length T) U1).
          apply (ProductMeasure.csum_le_good Link4D Quat link4D_eqb G su2_unit G_good);
            [| exact U1_unit].
          intros A HA. apply aterm_sum. exact HA.
      - apply Nat.leb_gt in Hab.
        rewrite (rsum_zero (ProductMeasure.splits T) (fun P => Cs LinksE (term P) U1)).
        + rewrite Rabs_R0, Rmult_0_l. apply Rle_refl.
        + intros P HP. destruct (ProductMeasure.splits_spec T P HP) as [H1 [H2 H3]].
          apply term_vanish; [intros x Hx; apply HT; apply H1; exact Hx |].
          destruct (allEven (LoopC ++ flat_map plaq4D_links (fst P))) eqn:Hev;
            [| reflexivity].
          exfalso.
          assert (Hwf' : Forall wf_plaq_4D (fst P)).
          { apply (Z2AreaLaw.sublist_wf Lambda (fst P) Hwf).
            intros x Hx. apply HT. apply H1. exact Hx. }
          pose proof (Z2MinArea.rect_min_area s mu nu a b (fst P) Hmn Hwf' Hev) as Hmin.
          lia.
    Qed.

    (* ---------- Step 2 (continued): the part attached to the loop ---------- *)

    Lemma NN_expansion :
      NN = rsum (PenroseTreeBound.sublists Lambda)
             (fun T => if connbC (None :: map Some T)
                       then rhoE (None :: map Some T) *
                            ZZ (filter (fun p => negb (ptouchC (None :: map Some T) (Some p)))
                                  Lambda)
                       else 0).
    Proof.
      rewrite <- sum_rooted.
      pose proof (RootedPolymerBound.rooted_expansion
                    Link4D Elt link4D_eqb link4D_eqb_spec
                    Z2AreaLaw.eeqb Z2AreaLaw.eeqb_spec
                    esuppC (Z2AreaLaw.esupp_nonempty LoopC C_nonempty)
                    rhoE rhoE_factor
                    None (map Some Lambda) (Z2AreaLaw.nodup_root Lambda Hnd)) as Hexp.
      rewrite Hexp. rewrite (Verify.map_sublists (@Some Plaq4D) Lambda), rsum_map.
      apply rsum_ext. intros T _. cbv beta.
      destruct (connbC (None :: map Some T)); [| reflexivity].
      apply Rmult_eq_compat_l.
      rewrite (PolymerRepresentation.filter_map_swap (@Some Plaq4D)
                 (fun o => negb (ptouchC (None :: map Some T) o)) Lambda).
      apply sum_closed.
    Qed.

    Lemma numerator_bound :
      Rabs NN <=
      rsum (PenroseTreeBound.sublists Lambda)
        (fun T => if connbC (None :: map Some T) then gbound T else 0) * ZZ Lambda.
    Proof.
      rewrite NN_expansion. eapply Rle_trans; [apply rsum_abs |].
      rewrite <- rsum_scal_r. apply rsum_le. intros T HT.
      pose proof (ZZ_pos Lambda) as HZ.
      destruct (connbC (None :: map Some T)).
      - rewrite Rabs_mult.
        pose proof (ZZ_pos (filter (fun p => negb (ptouchC (None :: map Some T) (Some p)))
                              Lambda)) as H1.
        pose proof (ZZ_mono (fun p => negb (ptouchC (None :: map Some T) (Some p)))) as H2.
        rewrite (Rabs_pos_eq
                   (ZZ (filter (fun p => negb (ptouchC (None :: map Some T) (Some p)))
                          Lambda))) by lra.
        pose proof (rooted_bound T (PenroseTreeBound.sublists_incl Lambda T HT)) as H3.
        pose proof (Rabs_pos (rhoE (None :: map Some T))) as H5.
        apply Rmult_le_compat; lra.
      - rewrite Rabs_R0, Rmult_0_l. apply Rle_refl.
    Qed.

    (* ---------- Step 5: entropy ---------- *)

    Lemma entropy_bound :
      rsum (PenroseTreeBound.sublists Lambda)
        (fun T => if connbC (None :: map Some T) then gbound T else 0)
      <= (63 * delta) ^ (a * b) * exp (INR (length LoopC)).
    Proof.
      pose proof delta_nonneg as Hd. pose proof Z2AreaLaw.xent_pos as Hx.
      assert (H63 : 0 <= 63 * delta <= 1) by (unfold delta in *; lra).
      apply Rle_trans with
        (rsum (PenroseTreeBound.sublists Lambda)
           (fun T => (63 * delta) ^ (a * b) *
                     (if connbC (None :: map Some T) then Z2AreaLaw.xent ^ length T else 0))).
      - apply rsum_le. intros T _. destruct (connbC (None :: map Some T)).
        + unfold gbound. destruct (a * b <=? length T)%nat eqn:Hab.
          * apply Nat.leb_le in Hab.
            replace (delta ^ length T)
              with ((63 * delta) ^ length T * Z2AreaLaw.xent ^ length T).
            2: { rewrite <- Rpow_mult_distr. f_equal. unfold Z2AreaLaw.xent. field. }
            apply Rmult_le_compat_r; [apply pow_le; lra |].
            apply Z2AreaLaw.pow_le_exponent; [exact H63 | exact Hab].
          * apply Rmult_le_pos; apply pow_le; lra.
        + rewrite Rmult_0_r. apply Rle_refl.
      - rewrite rsum_scal. apply Rmult_le_compat_l; [apply pow_le; lra |].
        exact (Z2AreaLaw.loop_entropy LoopC Lambda Hnd Hwf).
    Qed.

    (* ---------- the area law for a non-empty loop ---------- *)

    Theorem instance_area_law :
      Rabs (su2_expect_on G beta Lambda Wobs)
      <= (63 * delta) ^ (a * b) * exp (INR (length LoopC)).
    Proof.
      rewrite expect_ratio. pose proof (ZZ_pos Lambda) as HZ.
      unfold Rdiv. rewrite Rabs_mult.
      rewrite (Rabs_pos_eq (/ ZZ Lambda)) by (left; apply Rinv_0_lt_compat; exact HZ).
      apply Rmult_le_reg_r with (ZZ Lambda); [exact HZ |].
      rewrite Rmult_assoc, Rinv_l by lra. rewrite Rmult_1_r.
      eapply Rle_trans; [exact numerator_bound |].
      apply Rmult_le_compat_r; [lra | exact entropy_bound].
    Qed.

  End Model.

  (* =======================================================================
     3. TARGET 8b
     ======================================================================= *)

  Theorem su2_wilson_loop_area_law : Challenge_SU2Gauge4D_WilsonLoopAreaLaw.
  Proof.
    intros G beta Lambda s mu nu a b HG HGu HGc Hsmall Hnd Hwf Hmn HC.
    assert (Hlen : INR (length (z2_rect_loop s mu nu a b)) = 2 * INR (a + b)).
    { rewrite Z2AreaLaw.rect_loop_length, !plus_INR. ring. }
    destruct (Nat.eq_dec (a + b) 0) as [Hz | Hnz].
    - (* degenerate loop without links: the Wilson loop is identically 1 *)
      assert (Ha : a = 0%nat) by lia. assert (Hb : b = 0%nat) by lia. subst a b.
      rewrite expect_csum.
      rewrite (csum_ext Link4D Quat link4D_eqb G (z2_links Lambda)
                 (fun U => su2_wilson_loop U s mu nu 0 0 *
                           exp (- su2_wilson_action beta Lambda U))
                 (fun U => exp (- su2_wilson_action beta Lambda U))).
      2: { intro U. rewrite wilson_00. ring. }
      assert (Hpos : 0 < csum Link4D Quat link4D_eqb G (z2_links Lambda)
                           (fun U => exp (- su2_wilson_action beta Lambda U))
                           (fun _ => qone)).
      { apply csum_pos; [exact HG |]. intro A. apply exp_pos. }
      unfold Rdiv. rewrite Rinv_r by lra. rewrite Rabs_R1.
      cbn [Nat.mul Nat.add pow INR]. rewrite Rmult_0_r, exp_0. lra.
    - assert (Hne : z2_rect_loop s mu nu a b <> []).
      { intro Heq. pose proof (Z2AreaLaw.rect_loop_length s mu nu a b) as Hl.
        rewrite Heq in Hl. cbn [length] in Hl. lia. }
      rewrite <- Hlen.
      exact (instance_area_law G HG HGu HGc beta Lambda Hnd Hwf s mu nu a b Hmn
               HC Hne Hsmall).
  Qed.

End SU2AreaLaw.
