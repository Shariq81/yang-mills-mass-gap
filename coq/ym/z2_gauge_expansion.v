(* =========================================================================
   ym/z2_gauge_expansion.v

   Exact strong-coupling (high-temperature) expansion of the 4D Z_2 Wilson
   lattice gauge theory (Wegner 1971), proved directly for the frozen
   objects of `verification/ChallengeZ2Gauge.v`:

     For every real beta, every finite plaquette list Lambda of Z^4 and
     every list of links C,

       int prod_{l in C} U_l * exp(beta * sum_{p in Lambda} U_p) dU
         = cosh(beta)^{|Lambda|}
           * sum_{S <= Lambda, dS = C (mod 2)} tanh(beta)^{|S|}.

   Steps:
     1. exp(beta * s) = cosh(beta) * (1 + tanh(beta) * s) for s = +-1;
     2. prod_p (1 + t U_p) = sum_{S <= Lambda} t^{|S|} prod_{p in S} U_p;
     3. the normalized Haar integral of a product of link variables is 1 if
        every link occurs an even number of times and 0 otherwise
        (character orthogonality on Z_2^E).

   Depends ONLY on Coq stdlib + verification.Challenge
   + verification.ChallengeZ2Gauge + rg.dup_clustering (finite sums/products).
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import rg.dup_clustering.

Import ListNotations.
Import Challenge ChallengeZ2Gauge DupClustering.
Open Scope R_scope.

Module Z2GaugeExpansion.

  (* =======================================================================
     1. Boolean equalities on sites, directions, links
     ======================================================================= *)

  Lemma site4D_eqb_spec : forall s1 s2, site4D_eqb s1 s2 = true <-> s1 = s2.
  Proof.
    intros [t1 x1 y1 z1] [t2 x2 y2 z2]. unfold site4D_eqb. cbn [s4_t s4_x s4_y s4_z].
    rewrite !andb_true_iff, !Z.eqb_eq. split.
    - intros [[[H1 H2] H3] H4]. subst. reflexivity.
    - intro H. injection H as H1 H2 H3 H4. subst. repeat split.
  Qed.

  Lemma dir4D_eqb_spec : forall d1 d2, dir4D_eqb d1 d2 = true <-> d1 = d2.
  Proof.
    intros [] []; cbn [dir4D_eqb]; split; intro H;
      try reflexivity; try discriminate.
  Qed.

  Lemma link4D_eqb_spec : forall l1 l2, link4D_eqb l1 l2 = true <-> l1 = l2.
  Proof.
    intros [s1 d1] [s2 d2]. unfold link4D_eqb. cbn [fst snd].
    rewrite andb_true_iff, site4D_eqb_spec, dir4D_eqb_spec. split.
    - intros [H1 H2]. subst. reflexivity.
    - intro H. injection H as H1 H2. subst. split; reflexivity.
  Qed.

  (* =======================================================================
     2. Holonomies
     ======================================================================= *)

  Lemma holonomy_nil : forall U, z2_holonomy U [] = 1.
  Proof. reflexivity. Qed.

  Lemma holonomy_cons : forall U l C,
    z2_holonomy U (l :: C) = z2_sign (U l) * z2_holonomy U C.
  Proof. reflexivity. Qed.

  Lemma holonomy_app : forall U C1 C2,
    z2_holonomy U (C1 ++ C2) = z2_holonomy U C1 * z2_holonomy U C2.
  Proof.
    intros U C1 C2. induction C1 as [| l C1 IH].
    - cbn [app]. rewrite holonomy_nil. ring.
    - cbn [app]. rewrite !holonomy_cons, IH. ring.
  Qed.

  Lemma z2_sign_sq : forall b, z2_sign b * z2_sign b = 1.
  Proof. intros []; cbn [z2_sign]; ring. Qed.

  Lemma holonomy_pm1 : forall U C, z2_holonomy U C = 1 \/ z2_holonomy U C = -1.
  Proof.
    intros U C. induction C as [| l C IH].
    - left. reflexivity.
    - rewrite holonomy_cons.
      destruct (U l); cbn [z2_sign]; destruct IH as [H | H]; rewrite H.
      + right. ring.
      + left. ring.
      + left. ring.
      + right. ring.
  Qed.

  Lemma holonomy_local : forall U U' C,
    (forall l, In l C -> U l = U' l) -> z2_holonomy U C = z2_holonomy U' C.
  Proof.
    intros U U' C H. induction C as [| l C IH]; [reflexivity |].
    rewrite !holonomy_cons, (H l (or_introl eq_refl)), IH; [reflexivity |].
    intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma holonomy_base : forall C, z2_holonomy (fun _ => false) C = 1.
  Proof.
    induction C as [| l C IH]; [reflexivity |].
    rewrite holonomy_cons, IH. cbn [z2_sign]. ring.
  Qed.

  Lemma holonomy_update : forall U l b C,
    z2_holonomy (z2_update U l b) C =
    z2_holonomy U C * (z2_sign b * z2_sign (U l)) ^ link4D_count l C.
  Proof.
    intros U l b C. induction C as [| x C IH].
    - rewrite !holonomy_nil. cbn [link4D_count pow]. ring.
    - rewrite !holonomy_cons, IH. cbn [link4D_count]. unfold z2_update at 1.
      destruct (link4D_eqb x l) eqn:Hx.
      + apply link4D_eqb_spec in Hx. subst x.
        cbn [Nat.add pow].
        pose proof (z2_sign_sq (U l)) as Hsq.
        transitivity
          (z2_sign b * (z2_sign (U l) * z2_sign (U l)) *
           (z2_holonomy U C * (z2_sign b * z2_sign (U l)) ^ link4D_count l C)).
        * rewrite Hsq. ring.
        * ring.
      + cbn [Nat.add]. ring.
  Qed.

  Lemma pow_m1 : forall n, (-1) ^ n = if Nat.even n then 1 else -1.
  Proof.
    intro n.
    assert (H : (-1) ^ n = (if Nat.even n then 1 else -1) /\
                (-1) ^ S n = (if Nat.even (S n) then 1 else -1)).
    { induction n as [| n [IH1 IH2]].
      - split; simpl; ring.
      - split; [exact IH2 |].
        change (Nat.even (S (S n))) with (Nat.even n).
        rewrite <- IH1. simpl. ring. }
    exact (proj1 H).
  Qed.

  (* Summing a holonomy over both values of one link *)
  Lemma holonomy_update_sum : forall U l C,
    z2_holonomy (z2_update U l false) C + z2_holonomy (z2_update U l true) C =
    (if Nat.even (link4D_count l C) then 2 else 0) * z2_holonomy U C.
  Proof.
    intros U l C. rewrite !holonomy_update.
    set (n := link4D_count l C). set (h := z2_holonomy U C).
    destruct (U l); cbn [z2_sign].
    - replace (1 * -1) with (-1) by ring. replace (-1 * -1) with 1 by ring.
      rewrite pow1, pow_m1. destruct (Nat.even n); ring.
    - replace (1 * 1) with 1 by ring. replace (-1 * 1) with (-1) by ring.
      rewrite pow1, pow_m1. destruct (Nat.even n); ring.
  Qed.

  (* =======================================================================
     3. Character orthogonality: sum of a holonomy over all configurations
     ======================================================================= *)

  Lemma configs_holonomy_sum : forall E U M,
    rsum (z2_configs_from E U) (fun V => z2_holonomy V M) =
    rprod E (fun l => if Nat.even (link4D_count l M) then 2 else 0) * z2_holonomy U M.
  Proof.
    induction E as [| l E IH]; intros U M.
    - cbn [z2_configs_from]. rewrite rsum_cons, rsum_nil, rprod_nil. ring.
    - cbn [z2_configs_from]. rewrite rsum_app, !IH, rprod_cons.
      rewrite <- Rmult_plus_distr_l, holonomy_update_sum. ring.
  Qed.

  Lemma rprod_even_indicator : forall {A : Type} (P : A -> bool) (l : list A),
    rprod l (fun x => if P x then 2 else 0) = if forallb P l then 2 ^ length l else 0.
  Proof.
    intros A P l. induction l as [| a l IH].
    - rewrite rprod_nil. reflexivity.
    - rewrite rprod_cons, IH. cbn [forallb length pow].
      destruct (P a), (forallb P l); cbn [andb]; ring.
  Qed.

  Lemma configs_nonempty : forall E U, z2_configs_from E U <> [].
  Proof.
    induction E as [| l E IH]; intro U; cbn [z2_configs_from]; [discriminate |].
    intro H. apply app_eq_nil in H. destruct H as [H _]. exact (IH _ H).
  Qed.

  (* =======================================================================
     4. Expansion of the Boltzmann weight
     ======================================================================= *)

  Lemma boltzmann_rprod : forall beta Lambda U,
    exp (- z2_wilson_action beta Lambda U) =
    rprod Lambda (fun p => exp (beta * z2_plaq U p)).
  Proof.
    intros beta Lambda U. unfold z2_wilson_action.
    change (fold_right Rplus 0 (map (z2_plaq U) Lambda)) with (rsum Lambda (z2_plaq U)).
    replace (- (- beta * rsum Lambda (z2_plaq U))) with (beta * rsum Lambda (z2_plaq U)) by ring.
    induction Lambda as [| p Lambda IH].
    - rewrite rsum_nil, rprod_nil, Rmult_0_r. apply exp_0.
    - rewrite rsum_cons, rprod_cons, Rmult_plus_distr_l, exp_plus, IH. reflexivity.
  Qed.

  Lemma cosh_pos : forall x, 0 < cosh x.
  Proof.
    intro x. unfold cosh. pose proof (exp_pos x). pose proof (exp_pos (- x)). lra.
  Qed.

  Lemma exp_cosh_tanh : forall beta s, (s = 1 \/ s = -1) ->
    exp (beta * s) = cosh beta * (1 + tanh beta * s).
  Proof.
    intros beta s Hs. pose proof (cosh_pos beta) as Hc.
    unfold tanh.
    replace (cosh beta * (1 + sinh beta / cosh beta * s))
      with (cosh beta + sinh beta * s) by (field; lra).
    unfold cosh, sinh. destruct Hs as [Hs | Hs]; subst s.
    - replace (beta * 1) with beta by ring. lra.
    - replace (beta * -1) with (- beta) by ring. lra.
  Qed.

  Lemma plaq_prod_expand : forall t U S,
    rprod S (fun p => t * z2_plaq U p) =
    t ^ length S * z2_holonomy U (flat_map plaq4D_links S).
  Proof.
    intros t U S. induction S as [| p S IH].
    - rewrite rprod_nil. cbn [flat_map length pow]. rewrite holonomy_nil. ring.
    - rewrite rprod_cons, IH. cbn [flat_map length pow]. rewrite holonomy_app.
      unfold z2_plaq. ring.
  Qed.

  Lemma boltzmann_expand : forall beta Lambda U,
    exp (- z2_wilson_action beta Lambda U) =
    cosh beta ^ length Lambda *
    rsum (sublists Lambda)
      (fun S => tanh beta ^ length S * z2_holonomy U (flat_map plaq4D_links S)).
  Proof.
    intros beta Lambda U. rewrite boltzmann_rprod.
    transitivity (rprod Lambda (fun p => cosh beta * (1 + tanh beta * z2_plaq U p))).
    - apply rprod_ext. intros p _. apply exp_cosh_tanh. apply holonomy_pm1.
    - rewrite rprod_mult, rprod_const, rprod_one_plus. f_equal.
      apply rsum_ext. intros S _. apply plaq_prod_expand.
  Qed.

  Lemma kp_sublists_eq : forall {A : Type} (l : list A), kp_sublists l = sublists l.
  Proof.
    intros A l. induction l as [| a l IH]; cbn [kp_sublists sublists];
      [reflexivity | rewrite IH; reflexivity].
  Qed.

  (* =======================================================================
     5. The exact strong-coupling expansion with a Wilson-line insertion
     ======================================================================= *)

  Lemma haar_insert : forall beta Lambda C,
    z2_haar (z2_links Lambda)
      (fun U => z2_holonomy U C * exp (- z2_wilson_action beta Lambda U)) =
    cosh beta ^ length Lambda * z2_surface_sum Lambda C (tanh beta).
  Proof.
    intros beta Lambda C. unfold z2_haar, z2_surface_sum, z2_configs.
    set (E := z2_links Lambda). set (t := tanh beta). set (c := cosh beta ^ length Lambda).
    set (U0 := (fun _ : Link4D => false) : Z2Config).
    assert (H2 : 2 ^ length E <> 0) by (apply pow_nonzero; lra).
    change (/ 2 ^ length E *
            rsum (z2_configs_from E U0)
              (fun U => z2_holonomy U C * exp (- z2_wilson_action beta Lambda U)) =
            c * rsum (kp_sublists Lambda)
                  (fun S => if z2_bdry_is E C S then t ^ length S else 0)).
    rewrite kp_sublists_eq.
    assert (Hinner : forall S,
      rsum (z2_configs_from E U0)
        (fun U => z2_holonomy U (C ++ flat_map plaq4D_links S)) =
      if z2_bdry_is E C S then 2 ^ length E else 0).
    { intro S. rewrite configs_holonomy_sum. unfold U0. rewrite holonomy_base.
      rewrite rprod_even_indicator. unfold z2_bdry_is.
      destruct (forallb (fun l => Nat.even (link4D_count l (C ++ flat_map plaq4D_links S))) E); ring. }
    assert (Hsum :
      rsum (z2_configs_from E U0)
        (fun U => z2_holonomy U C * exp (- z2_wilson_action beta Lambda U)) =
      c * rsum (sublists Lambda)
            (fun S => t ^ length S * (if z2_bdry_is E C S then 2 ^ length E else 0))).
    { transitivity
        (rsum (z2_configs_from E U0) (fun U =>
           rsum (sublists Lambda) (fun S =>
             c * (t ^ length S * z2_holonomy U (C ++ flat_map plaq4D_links S))))).
      - apply rsum_ext. intros U _. rewrite boltzmann_expand. fold t. fold c.
        rewrite <- Rmult_assoc, (Rmult_comm (z2_holonomy U C) c), Rmult_assoc.
        rewrite <- !rsum_scal. apply rsum_ext. intros S _.
        rewrite holonomy_app. ring.
      - rewrite rsum_swap, <- rsum_scal. apply rsum_ext. intros S _.
        rewrite <- (Hinner S), !rsum_scal. reflexivity. }
    rewrite Hsum.
    rewrite <- Rmult_assoc, (Rmult_comm (/ 2 ^ length E) c), Rmult_assoc. f_equal.
    rewrite <- rsum_scal. apply rsum_ext. intros S _.
    destruct (z2_bdry_is E C S); field; exact H2.
  Qed.

  Lemma partition_fn_pos : forall beta Lambda, 0 < z2_partition_fn beta Lambda.
  Proof.
    intros beta Lambda. unfold z2_partition_fn, z2_haar. apply Rmult_lt_0_compat.
    - apply Rinv_0_lt_compat. apply pow_lt. lra.
    - change (0 < rsum (z2_configs (z2_links Lambda))
                    (fun U => exp (- z2_wilson_action beta Lambda U))).
      apply rsum_pos; [apply configs_nonempty | intros U _; apply exp_pos].
  Qed.

  Lemma partition_fn_expand : forall beta Lambda,
    z2_partition_fn beta Lambda =
    cosh beta ^ length Lambda * z2_surface_sum Lambda [] (tanh beta).
  Proof.
    intros beta Lambda. rewrite <- haar_insert. unfold z2_partition_fn, z2_haar. f_equal.
    change (rsum (z2_configs (z2_links Lambda))
              (fun U => exp (- z2_wilson_action beta Lambda U)) =
            rsum (z2_configs (z2_links Lambda))
              (fun U => z2_holonomy U [] * exp (- z2_wilson_action beta Lambda U))).
    apply rsum_ext. intros U _. rewrite holonomy_nil. ring.
  Qed.

  (* TARGET 7a *)
  Theorem z2_strong_coupling_expansion : Challenge_Z2Gauge4D_StrongCouplingExpansion.
  Proof.
    intros beta Lambda.
    pose proof (partition_fn_pos beta Lambda) as HZ.
    pose proof (partition_fn_expand beta Lambda) as HZe.
    assert (Hc : 0 < cosh beta ^ length Lambda) by (apply pow_lt; apply cosh_pos).
    assert (Hs : 0 < z2_surface_sum Lambda [] (tanh beta)).
    { apply Rmult_lt_reg_l with (cosh beta ^ length Lambda); [exact Hc |].
      rewrite Rmult_0_r, <- HZe. exact HZ. }
    split; [exact HZ |]. split; [exact HZe |]. split; [exact Hs |].
    intro C. unfold z2_expect. rewrite haar_insert, HZe. field. split; lra.
  Qed.

End Z2GaugeExpansion.
