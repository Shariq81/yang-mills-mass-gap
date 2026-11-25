(* =========================================================================
   ym/z2_area_law.v

   Wilson-loop area law of the 4D Z_2 Wilson lattice gauge theory at strong
   coupling (TARGET 7e), proved directly for the frozen objects of
   `verification/ChallengeZ2AreaLaw.v`:

     for 63 * |tanh beta| <= 1, every finite duplicate-free volume Lambda of
     canonical plaquettes of Z^4 and every a x b rectangular loop all of
     whose links belong to the link set of Lambda,

       |<prod_{l in loop} U_l>| <= (63 |tanh beta|)^(a b) * exp(2 (a + b)).

   Steps (t = tanh beta, C = the loop):
     1. Target 7a: <W_C> = N_C(t) / N_0(t), where N_C(t) is the sum of
        t^{|S|} over the plaquette sets S of Lambda with mod-2 boundary C.
     2. Parity: with the staggered signs eta every canonical plaquette has
        value -1, so closed surfaces have an even number of plaquettes and
        N_0(t) = N_0(|t|); trivially |N_C(t)| <= N_C(|t|).
     3. The loop is added to the plaquettes as an extra element whose links
        are C.  The weight [all multiplicities even] * t^{#plaquettes}
        factorizes over non-touching parts, so the rooted expansion of
        rg/rooted_polymer_bound.v splits every S into the part G attached
        to the loop and a closed rest, giving for t >= 0
          N_C(t) <= N_0(t) * sum_{G attached to C, dG = C} t^{|G|}.
     4. Minimal area (ym/z2_min_area.v): dG = C forces |G| >= a * b.
     5. Entropy: the rooted Kotecky-Preiss bound applied to the gas of single
        plaquettes of activity 1/63 (21 neighbours, Target 4a) with the loop
        as root gives  sum_{G attached to C} (1/63)^{|G|} <= exp(|C|).

   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.Verify.
Require Import rg.dup_clustering.
Require Import rg.penrose_tree_bound.
Require Import rg.kotecky_preiss.
Require Import rg.cluster_log_partition.
Require Import rg.polymer_representation.
Require Import rg.connected_subset_bound.
Require Import rg.rooted_polymer_bound.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.z2_polymer_gas.
Require Import ym.z2_free_energy.
Require Import ym.z2_even_holonomy.
Require Import ym.z2_min_area.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw.
Import DupClustering Z2GaugeExpansion Z2GaugeClustering Z2PolymerGas Z2EvenHolonomy.
Open Scope R_scope.

Module Z2AreaLaw.

  (* =======================================================================
     1. Small generic lemmas
     ======================================================================= *)

  Lemma rprod_filter_split : forall {A : Type} (f : A -> bool) (g : A -> R) (l : list A),
    rprod l g = rprod (filter f l) g * rprod (filter (fun x => negb (f x)) l) g.
  Proof.
    intros A f g l. induction l as [| a l IH].
    - cbn [filter]. rewrite !rprod_nil. ring.
    - cbn [filter]. rewrite rprod_cons, IH.
      destruct (f a); cbn [negb]; rewrite rprod_cons; ring.
  Qed.

  Lemma filter_length_mono : forall {A : Type} (f g : A -> bool) (l : list A),
    (forall x, In x l -> f x = true -> g x = true) ->
    (length (filter f l) <= length (filter g l))%nat.
  Proof.
    intros A f g l H. induction l as [| a l IH]; [apply le_n |].
    cbn [filter].
    assert (IH' : (length (filter f l) <= length (filter g l))%nat).
    { apply IH. intros x Hx. apply H. right. exact Hx. }
    destruct (f a) eqn:Hf.
    - rewrite (H a (or_introl eq_refl) Hf). cbn [length]. lia.
    - destruct (g a); cbn [length]; lia.
  Qed.

  Lemma filter_orb_length : forall {A : Type} (f g : A -> bool) (l : list A),
    (length (filter (fun x => f x || g x) l)
     <= length (filter f l) + length (filter g l))%nat.
  Proof.
    intros A f g l. induction l as [| a l IH]; [apply le_n |].
    cbn [filter]. destruct (f a), (g a); cbn [orb length]; lia.
  Qed.

  Lemma pow_le_exponent : forall y (A n : nat),
    0 <= y <= 1 -> (A <= n)%nat -> y ^ n <= y ^ A.
  Proof.
    intros y A n Hy Hle. replace n with (A + (n - A))%nat by lia.
    rewrite pow_add. rewrite <- (Rmult_1_r (y ^ A)) at 2.
    apply Rmult_le_compat_l; [apply pow_le; lra |].
    rewrite <- (pow1 (n - A)). apply pow_incr. exact Hy.
  Qed.

  Lemma rsum_sublists_filter_le : forall {A : Type} (f : A -> bool) (l : list A)
      (g : list A -> R),
    (forall S, 0 <= g S) ->
    rsum (PenroseTreeBound.sublists (filter f l)) g <= rsum (PenroseTreeBound.sublists l) g.
  Proof.
    intros A f l g Hg. unfold rsum.
    rewrite <- (ClusterLogPartition.fold_right_Rplus_sublists_filter f l g).
    apply KoteckyPreiss.fold_right_Rplus_le. intros S _.
    destruct (forallb f S); [apply Rle_refl | apply Hg].
  Qed.

  Lemma sublist_wf : forall Lambda S : list Plaq4D,
    Forall wf_plaq_4D Lambda -> incl S Lambda -> Forall wf_plaq_4D S.
  Proof.
    intros Lambda S Hwf Hincl. apply Forall_forall. intros p Hp.
    exact (proj1 (Forall_forall wf_plaq_4D Lambda) Hwf p (Hincl p Hp)).
  Qed.

  (* =======================================================================
     2. Parity: closed surfaces of canonical plaquettes have even size
     ======================================================================= *)

  (* staggered signs: every canonical plaquette has value -1 *)
  Definition eta : Z2Config := fun l =>
    match snd l with
    | D4_t => false
    | D4_x => Z.odd (s4_t (fst l))
    | D4_y => Z.odd (s4_t (fst l) + s4_x (fst l))
    | D4_z => Z.odd (s4_t (fst l) + s4_x (fst l) + s4_y (fst l))
    end.

  Lemma eta_plaq : forall p, wf_plaq_4D p -> z2_plaq eta p = -1.
  Proof.
    intros [[t x y z] m n] Hwf.
    unfold wf_plaq_4D, canonical_planes_4D in Hwf. cbn [p4_mu p4_nu In] in Hwf.
    unfold z2_plaq, plaq4D_links, z2_holonomy. cbn [p4_site p4_mu p4_nu map fold_right].
    destruct Hwf as [H | [H | [H | [H | [H | [H | []]]]]]];
      injection H as Hm Hn; subst m n;
      unfold eta; cbn [fst snd shift4D s4_t s4_x s4_y s4_z];
      rewrite ?Z.odd_add;
      destruct (Z.odd t), (Z.odd x), (Z.odd y), (Z.odd z); cbn; lra.
  Qed.

  Lemma closed_size_parity : forall S, Forall wf_plaq_4D S ->
    allEven (links_of S) = true -> (-1) ^ length S = 1.
  Proof.
    intros S Hwf Hev.
    pose proof (allEven_holonomy eta (links_of S) Hev) as Hh.
    unfold links_of in Hh. rewrite holonomy_flat_map in Hh.
    transitivity (rprod S (z2_plaq eta)); [| exact Hh].
    rewrite <- (rprod_const (-1) S). apply rprod_ext. intros p Hp. symmetry.
    apply eta_plaq. exact (proj1 (Forall_forall wf_plaq_4D S) Hwf p Hp).
  Qed.

  Lemma pow_abs_parity : forall t n, (-1) ^ n = 1 -> t ^ n = Rabs t ^ n.
  Proof.
    intros t n H. unfold Rabs. destruct (Rcase_abs t) as [Hneg | Hpos]; [| reflexivity].
    replace (- t) with (-1 * t) by ring. rewrite Rpow_mult_distr, H. ring.
  Qed.

  (* =======================================================================
     3. Surface sums
     ======================================================================= *)

  Lemma surface_sum_closed_rho : forall Lambda t,
    z2_surface_sum Lambda [] t = rsum (PenroseTreeBound.sublists Lambda) (rho t).
  Proof.
    intros Lambda t. unfold z2_surface_sum. rewrite Verify.kp_sublists_eq.
    unfold rsum. apply PenroseTreeBound.fold_right_Rplus_ext. intros S HS. unfold rho.
    rewrite (bdry_closed Lambda S (PenroseTreeBound.sublists_incl Lambda S HS)). reflexivity.
  Qed.

  (* the closed-surface sum only depends on |t| *)
  Lemma surface_sum_closed_abs : forall Lambda t, Forall wf_plaq_4D Lambda ->
    z2_surface_sum Lambda [] t = z2_surface_sum Lambda [] (Rabs t).
  Proof.
    intros Lambda t Hwf. rewrite !surface_sum_closed_rho.
    apply rsum_ext. intros S HS.
    pose proof (PenroseTreeBound.sublists_incl Lambda S HS) as Hincl.
    unfold rho. destruct (z2_closed S) eqn:Hc; [| reflexivity].
    apply pow_abs_parity. apply closed_size_parity; [exact (sublist_wf Lambda S Hwf Hincl) |].
    exact Hc.
  Qed.

  Lemma surface_sum_closed_nonneg : forall Lambda t, Forall wf_plaq_4D Lambda ->
    0 <= z2_surface_sum Lambda [] t.
  Proof.
    intros Lambda t Hwf. rewrite (surface_sum_closed_abs Lambda t Hwf), surface_sum_closed_rho.
    apply rsum_nonneg. intros S _. unfold rho.
    destruct (z2_closed S); [apply pow_le; apply Rabs_pos | apply Rle_refl].
  Qed.

  Lemma surface_sum_abs_le : forall Lambda C t,
    Rabs (z2_surface_sum Lambda C t) <= z2_surface_sum Lambda C (Rabs t).
  Proof.
    intros Lambda C t. unfold z2_surface_sum.
    apply PenroseTreeBound.Rabs_fold_right_Rplus_le. intros S _.
    destruct (z2_bdry_is (z2_links Lambda) C S).
    - rewrite <- RPow_abs. apply Rle_refl.
    - rewrite Rabs_R0. apply Rle_refl.
  Qed.

  (* =======================================================================
     4. Even multiplicities split over parts that share no link
     ======================================================================= *)

  Lemma count_flat_split : forall {B : Type} (supp : B -> list Link4D) l
      (f : B -> bool) (S : list B),
    link4D_count l (flat_map supp S) =
    (link4D_count l (flat_map supp (filter f S)) +
     link4D_count l (flat_map supp (filter (fun b => negb (f b)) S)))%nat.
  Proof.
    intros B supp l f S. induction S as [| a S IH]; [reflexivity |].
    cbn [flat_map filter]. rewrite count_app, IH.
    destruct (f a); cbn [negb flat_map]; rewrite ?count_app; lia.
  Qed.

  Lemma allEven_split : forall {B : Type} (supp : B -> list Link4D) (S : list B)
      (f : B -> bool),
    (forall p q, In p S -> In q S -> f p = true -> f q = false ->
                 touchb Link4D link4D_eqb (supp p) (supp q) = false) ->
    allEven (flat_map supp S) =
    allEven (flat_map supp (filter f S)) &&
    allEven (flat_map supp (filter (fun b => negb (f b)) S)).
  Proof.
    intros B supp S f Hnt. apply eq_true_iff_eq. rewrite andb_true_iff, !allEven_iff.
    assert (Hdis : forall l,
      link4D_count l (flat_map supp (filter f S)) = 0%nat \/
      link4D_count l (flat_map supp (filter (fun b => negb (f b)) S)) = 0%nat).
    { intro l.
      destruct (Nat.eq_dec (link4D_count l (flat_map supp (filter f S))) 0) as [H1 | H1];
        [left; exact H1 |].
      destruct (Nat.eq_dec
                  (link4D_count l (flat_map supp (filter (fun b => negb (f b)) S))) 0)
        as [H2 | H2]; [right; exact H2 |].
      exfalso.
      assert (Hin1 : In l (flat_map supp (filter f S))) by (apply count_pos_In; lia).
      assert (Hin2 : In l (flat_map supp (filter (fun b => negb (f b)) S)))
        by (apply count_pos_In; lia).
      apply in_flat_map in Hin1. destruct Hin1 as [p [Hp Hlp]].
      apply in_flat_map in Hin2. destruct Hin2 as [q [Hq Hlq]].
      apply filter_In in Hp. destruct Hp as [HpS Hfp].
      apply filter_In in Hq. destruct Hq as [HqS Hfq]. apply negb_true_iff in Hfq.
      pose proof (Hnt p q HpS HqS Hfp Hfq) as Hno.
      assert (Hyes : touchb Link4D link4D_eqb (supp p) (supp q) = true).
      { apply (touchb_true Link4D link4D_eqb link4D_eqb_spec). exists l. split; assumption. }
      congruence. }
    split.
    - intro H. split; intro l; pose proof (H l) as Hl;
        rewrite (count_flat_split supp l f S) in Hl; destruct (Hdis l) as [H0 | H0].
      + rewrite H0. reflexivity.
      + rewrite H0, Nat.add_0_r in Hl. exact Hl.
      + rewrite H0 in Hl. cbn [Nat.add] in Hl. exact Hl.
      + rewrite H0. reflexivity.
    - intros [H1 H2] l. rewrite (count_flat_split supp l f S).
      destruct (Hdis l) as [H0 | H0]; rewrite H0.
      + cbn [Nat.add]. apply H2.
      + rewrite Nat.add_0_r. apply H1.
  Qed.

  (* =======================================================================
     5. Plaquettes of Lambda touching a list of links
     ======================================================================= *)

  Lemma link_plaq_count : forall Lambda l, NoDup Lambda -> Forall wf_plaq_4D Lambda ->
    (length (filter (fun q => memb link4D_eqb l (plaq4D_links q)) Lambda) <= 21)%nat.
  Proof.
    intros Lambda l Hnd Hwf.
    destruct (filter (fun q => memb link4D_eqb l (plaq4D_links q)) Lambda)
      as [| q1 rest] eqn:Hf; [cbn [length]; lia |].
    assert (Hq1 : In q1 (filter (fun q => memb link4D_eqb l (plaq4D_links q)) Lambda))
      by (rewrite Hf; left; reflexivity).
    apply filter_In in Hq1. destruct Hq1 as [Hq1L Hq1l].
    apply (memb_In link4D_eqb link4D_eqb_spec) in Hq1l.
    rewrite <- Hf.
    eapply Nat.le_trans;
      [| exact (touch_count_21 Lambda Hnd Hwf q1
                  (proj1 (Forall_forall wf_plaq_4D Lambda) Hwf q1 Hq1L))].
    apply filter_length_mono. intros q _ Hq.
    apply (memb_In link4D_eqb link4D_eqb_spec) in Hq.
    apply (touchb_true Link4D link4D_eqb link4D_eqb_spec). exists l. split; assumption.
  Qed.

  Lemma loop_touch_count : forall Lambda, NoDup Lambda -> Forall wf_plaq_4D Lambda ->
    forall K : list Link4D,
    (length (filter (fun q => touchb Link4D link4D_eqb K (plaq4D_links q)) Lambda)
     <= 21 * length K)%nat.
  Proof.
    intros Lambda Hnd Hwf K. induction K as [| l K IH].
    - rewrite (PolymerRepresentation.filter_all_false
                 (fun q => touchb Link4D link4D_eqb [] (plaq4D_links q)) Lambda);
        [cbn [length]; lia |].
      intros q _. reflexivity.
    - eapply Nat.le_trans.
      + apply (filter_length_mono
                 (fun q => touchb Link4D link4D_eqb (l :: K) (plaq4D_links q))
                 (fun q => memb link4D_eqb l (plaq4D_links q) ||
                           touchb Link4D link4D_eqb K (plaq4D_links q))).
        intros q _ H. exact H.
      + eapply Nat.le_trans; [apply filter_orb_length |].
        pose proof (link_plaq_count Lambda l Hnd Hwf). cbn [length]. lia.
  Qed.

  (* =======================================================================
     6. The loop as an extra element: weights, rooted expansion, entropy
     ======================================================================= *)

  (* entropy activity and Kotecky-Preiss constant of the single-plaquette gas *)
  Definition xent : R := / 63.
  Definition a0e : R := 21 * exp 1 * xent.

  Lemma xent_pos : 0 < xent.
  Proof. unfold xent. lra. Qed.

  Lemma a0e_bounds : 0 <= a0e <= 1.
  Proof. unfold a0e, xent. pose proof exp_le_3. pose proof (exp_pos 1). lra. Qed.

  Lemma xexp_bound : xent * exp a0e <= / 21.
  Proof.
    pose proof a0e_bounds as [_ H1]. pose proof (exp_le a0e 1 H1) as He.
    pose proof exp_le_3 as H3. unfold xent. lra.
  Qed.

  Lemma unit_kp_num : 21 * (xent * exp a0e) <= a0e.
  Proof.
    pose proof a0e_bounds as [_ H1]. pose proof (exp_le a0e 1 H1) as He.
    unfold a0e at 2. unfold xent. lra.
  Qed.

  Section Loop.
    Variable C : list Link4D.
    Hypothesis C_nonempty : C <> [].

    Local Notation Elt := (option Plaq4D).

    (* links of an element: a plaquette's boundary, or the loop itself *)
    Definition esupp (o : Elt) : list Link4D :=
      match o with
      | Some p => plaq4D_links p
      | None => C
      end.

    Definition eeqb (o1 o2 : Elt) : bool :=
      match o1, o2 with
      | Some p, Some q => plaq4D_eqb p q
      | None, None => true
      | _, _ => false
      end.

    Lemma eeqb_spec : forall x y, eeqb x y = true <-> x = y.
    Proof.
      intros [p |] [q |]; cbn [eeqb].
      - rewrite plaq4D_eqb_spec. split; intro H; [subst q; reflexivity |].
        injection H as H. exact H.
      - split; intro H; discriminate H.
      - split; intro H; discriminate H.
      - split; intros _; reflexivity.
    Qed.

    Lemma esupp_nonempty : forall o, esupp o <> [].
    Proof. intros [p |]; cbn [esupp]; [apply links_nonempty | exact C_nonempty]. Qed.

    Definition ewt (t : R) (o : Elt) : R :=
      match o with
      | Some _ => t
      | None => 1
      end.

    (* [all link multiplicities even] * t^{number of plaquettes} *)
    Definition erho (t : R) (S : list Elt) : R :=
      if allEven (flat_map esupp S) then rprod S (ewt t) else 0.

    Local Notation eTouch := (PolymerRepresentation.touch Link4D Elt link4D_eqb esupp).
    Local Notation eConnb := (PolymerRepresentation.connb Link4D Elt link4D_eqb esupp).

    Lemma erho_factor : forall t (S : list Elt) (f : Elt -> bool),
      (forall p q, In p S -> In q S -> f p = true -> f q = false ->
                   eTouch p q = false) ->
      erho t S = erho t (filter f S) * erho t (filter (fun b => negb (f b)) S).
    Proof.
      intros t S f Hnt. unfold erho.
      rewrite (allEven_split esupp S f Hnt), (rprod_filter_split f (ewt t) S).
      destruct (allEven (flat_map esupp (filter f S))),
               (allEven (flat_map esupp (filter (fun b => negb (f b)) S)));
        cbn [andb]; ring.
    Qed.

    Lemma erho_nonneg : forall t S, 0 <= t -> 0 <= erho t S.
    Proof.
      intros t S Ht. unfold erho. destruct (allEven (flat_map esupp S)); [| apply Rle_refl].
      apply rprod_nonneg. intros o _. destruct o; cbn [ewt]; lra.
    Qed.

    Lemma flat_map_esupp_some : forall S : list Plaq4D,
      flat_map esupp (map Some S) = links_of S.
    Proof.
      induction S as [| p S IH]; [reflexivity |].
      cbn [map flat_map esupp]. rewrite IH. reflexivity.
    Qed.

    Lemma rprod_map_some : forall t (S : list Plaq4D),
      rprod (map Some S) (ewt t) = t ^ length S.
    Proof.
      intros t S. induction S as [| p S IH]; [reflexivity |].
      cbn [map length pow]. rewrite rprod_cons, IH. reflexivity.
    Qed.

    Lemma erho_root : forall t (S : list Plaq4D),
      erho t (None :: map Some S) =
      if allEven (C ++ links_of S) then t ^ length S else 0.
    Proof.
      intros t S. unfold erho. cbn [flat_map esupp]. rewrite flat_map_esupp_some.
      destruct (allEven (C ++ links_of S)); [| reflexivity].
      rewrite rprod_cons, rprod_map_some. cbn [ewt]. ring.
    Qed.

    Lemma erho_closed : forall t (S : list Plaq4D), erho t (map Some S) = rho t S.
    Proof.
      intros t S. unfold erho, rho. rewrite flat_map_esupp_some, rprod_map_some.
      reflexivity.
    Qed.

    Lemma bdry_allEven : forall Lambda S, incl S Lambda -> incl C (z2_links Lambda) ->
      z2_bdry_is (z2_links Lambda) C S = allEven (C ++ links_of S).
    Proof.
      intros Lambda S HS HC. apply eq_true_iff_eq. rewrite allEven_iff.
      unfold z2_bdry_is. fold (links_of S). rewrite forallb_forall. split.
      - intros H l. destruct (memb link4D_eqb l (C ++ links_of S)) eqn:Hm.
        + apply (memb_In link4D_eqb link4D_eqb_spec) in Hm. apply H.
          apply in_app_or in Hm. destruct Hm as [Hm | Hm]; [exact (HC l Hm) |].
          unfold z2_links. apply dedup_In. unfold links_of in Hm.
          apply in_flat_map in Hm. destruct Hm as [p [Hp Hl]].
          apply in_flat_map. exists p. split; [apply HS; exact Hp | exact Hl].
        + apply (memb_false link4D_eqb link4D_eqb_spec) in Hm.
          rewrite (count_zero l _ Hm). reflexivity.
      - intros H l _. exact (H l).
    Qed.

    Lemma surface_sum_root : forall Lambda t, incl C (z2_links Lambda) ->
      z2_surface_sum Lambda C t =
      rsum (PenroseTreeBound.sublists Lambda) (fun S => erho t (None :: map Some S)).
    Proof.
      intros Lambda t HC. unfold z2_surface_sum. rewrite Verify.kp_sublists_eq.
      unfold rsum. apply PenroseTreeBound.fold_right_Rplus_ext. intros S HS.
      rewrite erho_root,
              (bdry_allEven Lambda S (PenroseTreeBound.sublists_incl Lambda S HS) HC).
      reflexivity.
    Qed.

    Lemma nodup_root : forall Lambda : list Plaq4D,
      NoDup Lambda -> NoDup (None :: map Some Lambda).
    Proof.
      intros Lambda Hnd. constructor.
      - intro Hin. apply in_map_iff in Hin. destruct Hin as [p [Hp _]]. discriminate Hp.
      - apply PenroseTreeBound.NoDup_map_in; [exact Hnd |].
        intros x y _ _ H. injection H as H. exact H.
    Qed.

    (* Step 3: the part attached to the loop *)
    Lemma root_decomposition : forall Lambda t,
      0 <= t -> NoDup Lambda -> incl C (z2_links Lambda) ->
      z2_surface_sum Lambda C t <=
      rsum (PenroseTreeBound.sublists Lambda)
        (fun G => if eConnb (None :: map Some G) then erho t (None :: map Some G) else 0)
      * z2_surface_sum Lambda [] t.
    Proof.
      intros Lambda t Ht Hnd HC.
      rewrite (surface_sum_root Lambda t HC).
      pose proof (RootedPolymerBound.rooted_expansion
                    Link4D Elt link4D_eqb link4D_eqb_spec eeqb eeqb_spec
                    esupp esupp_nonempty (erho t) (erho_factor t)
                    None (map Some Lambda) (nodup_root Lambda Hnd)) as Hexp.
      rewrite (Verify.map_sublists (@Some Plaq4D) Lambda), !rsum_map in Hexp.
      cbv beta in Hexp.
      eapply Rle_trans; [right; exact Hexp |].
      rewrite <- rsum_scal_r. apply rsum_le. intros G HG.
      destruct (eConnb (None :: map Some G)).
      - apply Rmult_le_compat_l; [apply erho_nonneg; exact Ht |].
        apply Rle_trans with
          (rsum (PenroseTreeBound.sublists (map Some Lambda)) (erho t)).
        + apply rsum_sublists_filter_le. intro S. apply erho_nonneg. exact Ht.
        + rewrite (Verify.map_sublists (@Some Plaq4D) Lambda), rsum_map.
          rewrite surface_sum_closed_rho. apply Req_le. apply rsum_ext. intros S _.
          apply erho_closed.
      - rewrite Rmult_0_l. apply Rle_refl.
    Qed.

    (* ---------- Step 5: entropy of the plaquette sets attached to the loop ---------- *)

    Definition wE : Elt -> R := fun _ => xent.
    Definition aE (o : Elt) : R :=
      match o with
      | Some _ => a0e
      | None => INR (length C)
      end.

    Lemma aE_nonneg : forall o, 0 <= aE o.
    Proof. intros [p |]; cbn [aE]; [apply a0e_bounds | apply pos_INR]. Qed.

    Lemma kp_some : forall Lambda p,
      NoDup Lambda -> Forall wf_plaq_4D Lambda -> wf_plaq_4D p ->
      KoteckyPreiss.kp_at eTouch (map Some Lambda) wE aE (fun _ => 0) (Some p).
    Proof.
      intros Lambda p Hnd Hwf Hp.
      unfold KoteckyPreiss.kp_at, KoteckyPreiss.sum_overlap_Lambda.
      change (rsum (map Some Lambda)
                (fun q => if eTouch (Some p) q then Rabs (wE q) * exp (aE q + 0) else 0)
              <= a0e).
      rewrite rsum_map.
      change (rsum Lambda
                (fun q => if plaq4D_touch p q then Rabs xent * exp (a0e + 0) else 0)
              <= a0e).
      rewrite (rsum_indicator_const (fun q => plaq4D_touch p q)
                 (Rabs xent * exp (a0e + 0)) Lambda).
      pose proof (touch_count_21 Lambda Hnd Hwf p Hp) as Hcnt.
      change (length (filter (fun q => plaq4D_touch p q) Lambda) <= 21)%nat in Hcnt.
      apply le_INR in Hcnt.
      assert (H21 : INR 21 = 21) by (cbn [INR]; lra).
      rewrite H21 in Hcnt.
      pose proof xent_pos as Hx.
      rewrite (Rabs_right xent) by lra. rewrite Rplus_0_r.
      apply Rle_trans with (21 * (xent * exp a0e)); [| exact unit_kp_num].
      apply Rmult_le_compat_r; [| exact Hcnt].
      apply Rmult_le_pos; [lra | left; apply exp_pos].
    Qed.

    Lemma kp_none : forall Lambda, NoDup Lambda -> Forall wf_plaq_4D Lambda ->
      KoteckyPreiss.kp_at eTouch (map Some Lambda) wE aE (fun _ => 0) None.
    Proof.
      intros Lambda Hnd Hwf.
      unfold KoteckyPreiss.kp_at, KoteckyPreiss.sum_overlap_Lambda.
      change (rsum (map Some Lambda)
                (fun q => if eTouch None q then Rabs (wE q) * exp (aE q + 0) else 0)
              <= INR (length C)).
      rewrite rsum_map.
      change (rsum Lambda
                (fun q => if touchb Link4D link4D_eqb C (plaq4D_links q)
                          then Rabs xent * exp (a0e + 0) else 0)
              <= INR (length C)).
      rewrite (rsum_indicator_const
                 (fun q => touchb Link4D link4D_eqb C (plaq4D_links q))
                 (Rabs xent * exp (a0e + 0)) Lambda).
      pose proof (loop_touch_count Lambda Hnd Hwf C) as Hcnt.
      apply le_INR in Hcnt. rewrite mult_INR in Hcnt.
      assert (H21 : INR 21 = 21) by (cbn [INR]; lra).
      rewrite H21 in Hcnt.
      pose proof xent_pos as Hx. pose proof xexp_bound as Hxe.
      pose proof (exp_pos a0e) as Hep. pose proof (pos_INR (length C)) as HC0.
      rewrite (Rabs_right xent) by lra. rewrite Rplus_0_r.
      apply Rle_trans with (21 * INR (length C) * (xent * exp a0e)).
      - apply Rmult_le_compat_r; [| exact Hcnt].
        apply Rmult_le_pos; lra.
      - apply Rle_trans with (21 * INR (length C) * / 21).
        + apply Rmult_le_compat_l; [| exact Hxe]. apply Rmult_le_pos; lra.
        + right. field.
    Qed.

    Lemma loop_entropy : forall Lambda, NoDup Lambda -> Forall wf_plaq_4D Lambda ->
      rsum (PenroseTreeBound.sublists Lambda)
        (fun G => if eConnb (None :: map Some G) then xent ^ length G else 0)
      <= exp (INR (length C)).
    Proof.
      intros Lambda Hnd Hwf.
      assert (Hkp : forall o, In o (map Some Lambda) ->
                KoteckyPreiss.kp_at eTouch (map Some Lambda) wE aE (fun _ => 0) o).
      { intros o Ho. apply in_map_iff in Ho. destruct Ho as [p [Ho Hp]]. subst o.
        apply kp_some; [exact Hnd | exact Hwf |].
        exact (proj1 (Forall_forall wf_plaq_4D Lambda) Hwf p Hp). }
      pose proof (RootedPolymerBound.kp_rooted_connected_subset_bound
                    eTouch (map Some Lambda) wE aE (fun _ => 0) None
                    (PolymerRepresentation.touch_sym Link4D Elt link4D_eqb
                       link4D_eqb_spec esupp)
                    (pos_INR (length C))
                    (fun o _ => aE_nonneg o)
                    (kp_none Lambda Hnd Hwf)
                    Hkp) as H.
      rewrite (Verify.map_sublists (@Some Plaq4D) Lambda), map_map in H.
      eapply Rle_trans; [| exact H].
      apply Req_le. unfold rsum. apply PenroseTreeBound.fold_right_Rplus_ext. intros G _.
      unfold PolymerRepresentation.connb.
      destruct (PenroseTreeBound.is_connectedb (length (None :: map Some G))
                  (PenroseTreeBound.graph_edges eTouch (None :: map Some G)));
        [| reflexivity].
      symmetry.
      etransitivity;
        [apply (Z2FreeEnergy.prod_weight_const (Rabs xent * exp 0) (map Some G)) |].
      pose proof xent_pos as Hx.
      rewrite map_length, exp_0, Rmult_1_r, (Rabs_right xent) by lra. reflexivity.
    Qed.

    (* ---------- Steps 3-5 combined ---------- *)

    Lemma loop_area_decay : forall Lambda t (A : nat),
      NoDup Lambda -> Forall wf_plaq_4D Lambda ->
      0 <= t -> 63 * t <= 1 ->
      (forall G, In G (PenroseTreeBound.sublists Lambda) ->
                 allEven (C ++ links_of G) = true -> (A <= length G)%nat) ->
      rsum (PenroseTreeBound.sublists Lambda)
        (fun G => if eConnb (None :: map Some G) then erho t (None :: map Some G) else 0)
      <= (63 * t) ^ A * exp (INR (length C)).
    Proof.
      intros Lambda t A Hnd Hwf Ht Ht63 Harea.
      pose proof xent_pos as Hx.
      apply Rle_trans with
        (rsum (PenroseTreeBound.sublists Lambda)
           (fun G => (63 * t) ^ A *
                     (if eConnb (None :: map Some G) then xent ^ length G else 0))).
      - apply rsum_le. intros G HG.
        destruct (eConnb (None :: map Some G)).
        + rewrite erho_root. destruct (allEven (C ++ links_of G)) eqn:Hev.
          * pose proof (Harea G HG Hev) as HA.
            replace (t ^ length G) with ((63 * t) ^ length G * xent ^ length G).
            2: { rewrite <- Rpow_mult_distr. f_equal. unfold xent. field. }
            apply Rmult_le_compat_r; [apply pow_le; lra |].
            apply pow_le_exponent; [lra | exact HA].
          * apply Rmult_le_pos; apply pow_le; lra.
        + rewrite Rmult_0_r. apply Rle_refl.
      - rewrite rsum_scal. apply Rmult_le_compat_l; [apply pow_le; lra |].
        exact (loop_entropy Lambda Hnd Hwf).
    Qed.

    Lemma loop_surface_bound : forall Lambda t (A : nat),
      NoDup Lambda -> Forall wf_plaq_4D Lambda -> incl C (z2_links Lambda) ->
      0 <= t -> 63 * t <= 1 ->
      (forall G, In G (PenroseTreeBound.sublists Lambda) ->
                 allEven (C ++ links_of G) = true -> (A <= length G)%nat) ->
      z2_surface_sum Lambda C t <=
      (63 * t) ^ A * exp (INR (length C)) * z2_surface_sum Lambda [] t.
    Proof.
      intros Lambda t A Hnd Hwf HC Ht Ht63 Harea.
      eapply Rle_trans; [apply (root_decomposition Lambda t Ht Hnd HC) |].
      apply Rmult_le_compat_r; [apply surface_sum_closed_nonneg; exact Hwf |].
      exact (loop_area_decay Lambda t A Hnd Hwf Ht Ht63 Harea).
    Qed.

  End Loop.

  (* =======================================================================
     7. Rectangular loops and the area law
     ======================================================================= *)

  Lemma rect_loop_length : forall s mu nu a b,
    length (z2_rect_loop s mu nu a b) = (a + b + a + b)%nat.
  Proof.
    intros s mu nu a b. unfold z2_rect_loop, z2_segment.
    rewrite !app_length, !map_length, !seq_length. lia.
  Qed.

  Theorem surface_area_law :
    forall (Lambda : list Plaq4D) (t : R) (s : Site4D) (mu nu : Dir4D) (a b : nat),
      63 * Rabs t <= 1 ->
      NoDup Lambda ->
      Forall wf_plaq_4D Lambda ->
      mu <> nu ->
      incl (z2_rect_loop s mu nu a b) (z2_links Lambda) ->
      Rabs (z2_surface_sum Lambda (z2_rect_loop s mu nu a b) t)
      <= (63 * Rabs t) ^ (a * b) * exp (2 * INR (a + b)) * z2_surface_sum Lambda [] t.
  Proof.
    intros Lambda t s mu nu a b Ht Hnd Hwf Hmn HC.
    assert (Hlen : INR (length (z2_rect_loop s mu nu a b)) = 2 * INR (a + b)).
    { rewrite rect_loop_length, !plus_INR. ring. }
    destruct (Nat.eq_dec (a + b) 0) as [Hz | Hnz].
    - (* degenerate loop without links *)
      assert (Ha : a = 0%nat) by lia. assert (Hb : b = 0%nat) by lia. subst a b.
      change (z2_rect_loop s mu nu 0 0) with (@nil Link4D).
      pose proof (surface_sum_closed_nonneg Lambda t Hwf) as HS0.
      rewrite (Rabs_right _ (Rle_ge _ _ HS0)).
      cbn [Nat.mul Nat.add pow INR]. rewrite Rmult_0_r, exp_0. lra.
    - assert (Hne : z2_rect_loop s mu nu a b <> []).
      { intro Heq. pose proof (rect_loop_length s mu nu a b) as Hl.
        rewrite Heq in Hl. cbn [length] in Hl. lia. }
      rewrite (surface_sum_closed_abs Lambda t Hwf).
      eapply Rle_trans; [apply surface_sum_abs_le |].
      rewrite <- Hlen.
      apply (loop_surface_bound (z2_rect_loop s mu nu a b) Hne Lambda (Rabs t) (a * b)
               Hnd Hwf HC (Rabs_pos t) Ht).
      intros G HG Hev.
      apply (Z2MinArea.rect_min_area s mu nu a b G Hmn); [| exact Hev].
      exact (sublist_wf Lambda G Hwf (PenroseTreeBound.sublists_incl Lambda G HG)).
  Qed.

  (* TARGET 7e *)
  Theorem z2_wilson_loop_area_law : Challenge_Z2Gauge4D_WilsonLoopAreaLaw.
  Proof.
    intros beta Lambda s mu nu a b Hsmall Hnd Hwf Hmn HC.
    destruct (z2_strong_coupling_expansion beta Lambda) as [_ [_ [Hpos Hexp]]].
    rewrite (Hexp (z2_rect_loop s mu nu a b)).
    pose proof (surface_area_law Lambda (tanh beta) s mu nu a b Hsmall Hnd Hwf Hmn HC) as H.
    unfold Rdiv. rewrite Rabs_mult.
    rewrite (Rabs_right (/ z2_surface_sum Lambda [] (tanh beta))).
    2: { apply Rle_ge. left. apply Rinv_0_lt_compat. exact Hpos. }
    apply Rmult_le_reg_r with (z2_surface_sum Lambda [] (tanh beta)); [exact Hpos |].
    rewrite Rmult_assoc, Rinv_l; [| lra]. rewrite Rmult_1_r. exact H.
  Qed.

End Z2AreaLaw.
