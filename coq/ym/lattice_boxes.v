(* =========================================================================
   ym/lattice_boxes.v

   Elementary combinatorics and geometry of the exhausting sequence of
   volumes Lambda_n = `su2_box n` of `verification/ChallengeSU2InfiniteVolume.v`
   (all canonical plaquettes of Z^4 anchored at a site of the cube [-n, n]^4):

     box_In          membership: p in Lambda_n iff p is canonical and its
                     anchor lies in the cube [-n, n]^4;
     box_nodup       Lambda_n is duplicate free;
     box_wf          Lambda_n consists of canonical plaquettes;
     box_mono        Lambda_n is increasing in n;
     box_length      |Lambda_n| = 6 * (2 n + 1)^4;
     box_exhaust     every finite list of canonical plaquettes is contained
                     in some Lambda_n;
     box_split       Lambda_{n+1} is a permutation of Q ++ Lambda_n, where Q
                     (the new shell) is disjoint from Lambda_n;
     shell_far       a plaquette of the shell Lambda_{n+1} \ Lambda_n is at
                     distance >= (n + 1 - n0) / 2 from every plaquette of
                     Lambda_{n0};
     box_card_bound  |Lambda_{n+1}| <= 486 * 8^n.

   Depends ONLY on Coq stdlib + the frozen files verification.Challenge,
   verification.ChallengeZ2Gauge, verification.ChallengeZ2AreaLaw,
   verification.ChallengeSU2Gauge, verification.ChallengeSU2InfiniteVolume
   + ym.z2_gauge_expansion + ym.z2_gauge_clustering (plaquette equality).
   Every statement below is a closed theorem: nothing is postulated and no
   proof is left open.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge ChallengeSU2InfiniteVolume.
Open Scope R_scope.

Module LatticeBoxes.

  (* =======================================================================
     1. General list helpers
     ======================================================================= *)

  (* the image of a duplicate-free list under a map injective on that list *)
  Lemma NoDup_map_inj_on : forall {A B : Type} (f : A -> B) (l : list A),
    (forall x y, In x l -> In y l -> f x = f y -> x = y) ->
    NoDup l -> NoDup (map f l).
  Proof.
    intros A B f l Hinj Hnd. induction Hnd as [| a l Hnotin Hnd IH].
    - constructor.
    - cbn [map]. constructor.
      + intro Hin. apply (proj1 (in_map_iff f l (f a))) in Hin.
        destruct Hin as [x [Hfx Hx]].
        assert (Hxa : x = a).
        { apply Hinj; [right; exact Hx | left; reflexivity | exact Hfx]. }
        subst x. apply Hnotin. exact Hx.
      + apply IH. intros x y Hx Hy. apply Hinj; right; assumption.
  Qed.

  (* concatenation of two disjoint duplicate-free lists *)
  Lemma NoDup_app_disj : forall {A : Type} (l1 l2 : list A),
    NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> In x l2 -> False) ->
    NoDup (l1 ++ l2).
  Proof.
    intros A l1 l2 H1 H2 Hd. induction H1 as [| a l1 Hnotin H1 IH].
    - exact H2.
    - cbn [app]. constructor.
      + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        * apply Hnotin. exact Hin.
        * apply (Hd a); [left; reflexivity | exact Hin].
      + apply IH. intros x Hx1 Hx2. apply (Hd x); [right; exact Hx1 | exact Hx2].
  Qed.

  (* a flat_map over a duplicate-free list whose pieces are duplicate free
     and pairwise disjoint (an element determines the piece it lies in) *)
  Lemma NoDup_flat_map_disj : forall {A B : Type} (f : A -> list B) (l : list A),
    NoDup l ->
    (forall a, In a l -> NoDup (f a)) ->
    (forall a a' b, In a l -> In a' l -> In b (f a) -> In b (f a') -> a = a') ->
    NoDup (flat_map f l).
  Proof.
    intros A B f l Hnd. induction Hnd as [| a l Hnotin Hnd IH]; intros Hf Hdisj.
    - constructor.
    - cbn [flat_map]. apply NoDup_app_disj.
      + apply Hf. left. reflexivity.
      + apply IH.
        * intros a' Ha'. apply Hf. right. exact Ha'.
        * intros a1 a2 b H1 H2. apply Hdisj; right; assumption.
      + intros b Hb1 Hb2. apply (proj1 (in_flat_map f l b)) in Hb2.
        destruct Hb2 as [a' [Ha' Hb']].
        assert (Haa : a = a').
        { apply (Hdisj a a' b);
            [left; reflexivity | right; exact Ha' | exact Hb1 | exact Hb']. }
        subst a'. apply Hnotin. exact Ha'.
  Qed.

  (* length of a flat_map whose pieces all have the same length *)
  Lemma flat_map_length_uniform : forall {A B : Type} (f : A -> list B) (l : list A) (c : nat),
    (forall a, In a l -> length (f a) = c) ->
    length (flat_map f l) = (length l * c)%nat.
  Proof.
    intros A B f l c. induction l as [| a l IH]; intro H.
    - reflexivity.
    - cbn [flat_map length]. rewrite app_length.
      rewrite (H a (or_introl eq_refl)).
      rewrite IH.
      + reflexivity.
      + intros a' Ha'. apply H. right. exact Ha'.
  Qed.

  (* =======================================================================
     2. The integer range -n, ..., n
     ======================================================================= *)

  Lemma z_range_In : forall n z,
    In z (z_range n) <-> (- Z.of_nat n <= z <= Z.of_nat n)%Z.
  Proof.
    intros n z. unfold z_range. split.
    - intro H. apply (proj1 (in_map_iff _ _ _)) in H. destruct H as [k [Hk Hin]].
      apply (proj1 (in_seq _ _ _)) in Hin. lia.
    - intro H. apply (proj2 (in_map_iff _ _ _)).
      exists (Z.to_nat (z + Z.of_nat n)). split.
      + rewrite Z2Nat.id by lia. lia.
      + apply (proj2 (in_seq _ _ _)). lia.
  Qed.

  Lemma z_range_NoDup : forall n, NoDup (z_range n).
  Proof.
    intro n. unfold z_range. apply NoDup_map_inj_on.
    - intros x y _ _ H. lia.
    - apply seq_NoDup.
  Qed.

  Lemma z_range_length : forall n, length (z_range n) = (2 * n + 1)%nat.
  Proof. intro n. unfold z_range. rewrite map_length, seq_length. reflexivity. Qed.

  (* =======================================================================
     3. The sites of the cube [-n, n]^4
     ======================================================================= *)

  Definition site_in_cube (n : nat) (s : Site4D) : Prop :=
    (- Z.of_nat n <= s4_t s <= Z.of_nat n)%Z /\ (- Z.of_nat n <= s4_x s <= Z.of_nat n)%Z /\
    (- Z.of_nat n <= s4_y s <= Z.of_nat n)%Z /\ (- Z.of_nat n <= s4_z s <= Z.of_nat n)%Z.

  (* the three nested layers of `cube_sites`, over an arbitrary coordinate list *)
  Lemma in_sites_z : forall (L : list Z) t x y s,
    In s (map (fun z => mkSite4D t x y z) L) ->
    s4_t s = t /\ s4_x s = x /\ s4_y s = y /\ In (s4_z s) L.
  Proof.
    intros L t x y s H. apply (proj1 (in_map_iff _ _ _)) in H.
    destruct H as [z [Hs Hz]]. subst s. cbn [s4_t s4_x s4_y s4_z].
    repeat split; try reflexivity. exact Hz.
  Qed.

  Lemma in_sites_y : forall (L : list Z) t x s,
    In s (flat_map (fun y => map (fun z => mkSite4D t x y z) L) L) ->
    s4_t s = t /\ s4_x s = x /\ In (s4_y s) L /\ In (s4_z s) L.
  Proof.
    intros L t x s H. apply (proj1 (in_flat_map _ _ _)) in H.
    destruct H as [y [Hy H]]. apply in_sites_z in H.
    destruct H as [Ht [Hx [Hy' Hz]]]. rewrite Hy'.
    repeat split; assumption.
  Qed.

  Lemma in_sites_x : forall (L : list Z) t s,
    In s (flat_map (fun x =>
            flat_map (fun y => map (fun z => mkSite4D t x y z) L) L) L) ->
    s4_t s = t /\ In (s4_x s) L /\ In (s4_y s) L /\ In (s4_z s) L.
  Proof.
    intros L t s H. apply (proj1 (in_flat_map _ _ _)) in H.
    destruct H as [x [Hx H]]. apply in_sites_y in H.
    destruct H as [Ht [Hx' [Hy Hz]]]. rewrite Hx'.
    repeat split; assumption.
  Qed.

  Lemma cube_sites_In : forall n s, In s (cube_sites n) <-> site_in_cube n s.
  Proof.
    intros n s. unfold cube_sites, site_in_cube. split.
    - intro H. apply (proj1 (in_flat_map _ _ _)) in H.
      destruct H as [t [Ht H]]. apply in_sites_x in H.
      destruct H as [Ht' [Hx [Hy Hz]]]. rewrite Ht'.
      apply (proj1 (z_range_In n _)) in Ht.
      apply (proj1 (z_range_In n _)) in Hx.
      apply (proj1 (z_range_In n _)) in Hy.
      apply (proj1 (z_range_In n _)) in Hz.
      repeat split; lia.
    - intros [Ht [Hx [Hy Hz]]]. destruct s as [t x y z].
      cbn [s4_t s4_x s4_y s4_z] in Ht, Hx, Hy, Hz.
      apply (proj2 (in_flat_map _ _ _)). exists t.
      split; [apply (proj2 (z_range_In n t)); exact Ht |].
      apply (proj2 (in_flat_map _ _ _)). exists x.
      split; [apply (proj2 (z_range_In n x)); exact Hx |].
      apply (proj2 (in_flat_map _ _ _)). exists y.
      split; [apply (proj2 (z_range_In n y)); exact Hy |].
      apply (proj2 (in_map_iff _ _ _)). exists z.
      split; [reflexivity | apply (proj2 (z_range_In n z)); exact Hz].
  Qed.

  Lemma cube_sites_NoDup : forall n, NoDup (cube_sites n).
  Proof.
    intro n. unfold cube_sites. apply NoDup_flat_map_disj.
    - apply z_range_NoDup.
    - intros t _. apply NoDup_flat_map_disj.
      + apply z_range_NoDup.
      + intros x _. apply NoDup_flat_map_disj.
        * apply z_range_NoDup.
        * intros y _. apply NoDup_map_inj_on.
          -- intros z z' _ _ H. injection H as H. exact H.
          -- apply z_range_NoDup.
        * intros y y' s _ _ H1 H2.
          apply in_sites_z in H1. apply in_sites_z in H2.
          destruct H1 as [_ [_ [H1 _]]]. destruct H2 as [_ [_ [H2 _]]].
          rewrite <- H1. exact H2.
      + intros x x' s _ _ H1 H2.
        apply in_sites_y in H1. apply in_sites_y in H2.
        destruct H1 as [_ [H1 _]]. destruct H2 as [_ [H2 _]].
        rewrite <- H1. exact H2.
    - intros t t' s _ _ H1 H2.
      apply in_sites_x in H1. apply in_sites_x in H2.
      destruct H1 as [H1 _]. destruct H2 as [H2 _].
      rewrite <- H1. exact H2.
  Qed.

  Lemma cube_sites_length : forall n, length (cube_sites n) = ((2 * n + 1) ^ 4)%nat.
  Proof.
    intro n. unfold cube_sites.
    assert (Hz : forall t x y : Z,
              length (map (fun z => mkSite4D t x y z) (z_range n)) = (2 * n + 1)%nat).
    { intros t x y. rewrite map_length. apply z_range_length. }
    assert (Hy : forall t x : Z,
              length (flat_map (fun y => map (fun z => mkSite4D t x y z) (z_range n))
                               (z_range n))
              = ((2 * n + 1) * (2 * n + 1))%nat).
    { intros t x. rewrite (flat_map_length_uniform _ _ (2 * n + 1)%nat).
      - rewrite z_range_length. reflexivity.
      - intros y _. apply Hz. }
    assert (Hx : forall t : Z,
              length (flat_map (fun x =>
                        flat_map (fun y => map (fun z => mkSite4D t x y z) (z_range n))
                                 (z_range n)) (z_range n))
              = ((2 * n + 1) * ((2 * n + 1) * (2 * n + 1)))%nat).
    { intro t. rewrite (flat_map_length_uniform _ _ ((2 * n + 1) * (2 * n + 1))%nat).
      - rewrite z_range_length. reflexivity.
      - intros x _. apply Hy. }
    rewrite (flat_map_length_uniform _ _ ((2 * n + 1) * ((2 * n + 1) * (2 * n + 1)))%nat).
    - rewrite z_range_length. cbn [Nat.pow]. rewrite Nat.mul_1_r. reflexivity.
    - intros t _. apply Hx.
  Qed.

  Lemma site_in_cube_mono : forall n m s,
    (n <= m)%nat -> site_in_cube n s -> site_in_cube m s.
  Proof. unfold site_in_cube. intros n m s Hnm H. lia. Qed.

  (* =======================================================================
     4. The volumes Lambda_n
     ======================================================================= *)

  Lemma canonical_planes_NoDup : NoDup canonical_planes_4D.
  Proof.
    unfold canonical_planes_4D.
    repeat (constructor; [cbn [In]; intuition discriminate |]).
    constructor.
  Qed.

  Lemma box_In : forall n p, In p (su2_box n) <-> (wf_plaq_4D p /\ site_in_cube n (p4_site p)).
  Proof.
    intros n p. unfold su2_box, wf_plaq_4D. split.
    - intro H. apply (proj1 (in_flat_map _ _ _)) in H. destruct H as [s [Hs Hp]].
      apply (proj1 (in_map_iff _ _ _)) in Hp. destruct Hp as [[mu nu] [Hp Hpl]].
      subst p. cbn [p4_site p4_mu p4_nu fst snd].
      split; [exact Hpl | apply (proj1 (cube_sites_In n s)); exact Hs].
    - intros [Hwf Hs]. apply (proj2 (in_flat_map _ _ _)). exists (p4_site p).
      split; [apply (proj2 (cube_sites_In n _)); exact Hs |].
      apply (proj2 (in_map_iff _ _ _)). exists (p4_mu p, p4_nu p).
      split; [destruct p; reflexivity | exact Hwf].
  Qed.

  Lemma box_nodup : forall n, NoDup (su2_box n).
  Proof.
    intro n. unfold su2_box. apply NoDup_flat_map_disj.
    - apply cube_sites_NoDup.
    - intros s _. apply NoDup_map_inj_on.
      + intros [m1 n1] [m2 n2] _ _ H. cbn [fst snd] in H.
        injection H as H1 H2. subst. reflexivity.
      + apply canonical_planes_NoDup.
    - intros s s' p _ _ H1 H2.
      apply (proj1 (in_map_iff _ _ _)) in H1. destruct H1 as [pl1 [E1 _]].
      apply (proj1 (in_map_iff _ _ _)) in H2. destruct H2 as [pl2 [E2 _]].
      rewrite <- E2 in E1. injection E1 as E _ _. exact E.
  Qed.

  Lemma box_wf : forall n, Forall wf_plaq_4D (su2_box n).
  Proof.
    intro n. apply (proj2 (Forall_forall _ _)). intros p Hp.
    apply (proj1 (box_In n p)) in Hp. exact (proj1 Hp).
  Qed.

  Lemma box_mono : forall n m, (n <= m)%nat -> incl (su2_box n) (su2_box m).
  Proof.
    intros n m Hnm p Hp. apply (proj1 (box_In n p)) in Hp. destruct Hp as [Hwf Hs].
    apply (proj2 (box_In m p)).
    split; [exact Hwf | exact (site_in_cube_mono n m _ Hnm Hs)].
  Qed.

  Lemma box_length : forall n, length (su2_box n) = (6 * (2 * n + 1) ^ 4)%nat.
  Proof.
    intro n. unfold su2_box. rewrite (flat_map_length_uniform _ _ 6%nat).
    - rewrite cube_sites_length. apply Nat.mul_comm.
    - intros s _. rewrite map_length. reflexivity.
  Qed.

  (* every finite list of canonical plaquettes lies in some Lambda_n *)
  Definition site_radius (s : Site4D) : nat :=
    Nat.max (Nat.max (Z.abs_nat (s4_t s)) (Z.abs_nat (s4_x s)))
            (Nat.max (Z.abs_nat (s4_y s)) (Z.abs_nat (s4_z s))).

  Lemma site_in_cube_radius : forall s, site_in_cube (site_radius s) s.
  Proof.
    intros [t x y z]. unfold site_in_cube, site_radius.
    cbn [s4_t s4_x s4_y s4_z]. lia.
  Qed.

  Lemma box_exhaust : forall P : list Plaq4D, Forall wf_plaq_4D P -> exists n0, incl P (su2_box n0).
  Proof.
    intros P HP. induction HP as [| p P Hp HP [n0 IH]].
    - exists 0%nat. intros p [].
    - exists (Nat.max (site_radius (p4_site p)) n0). intros q [Hq | Hq].
      + subst q. apply (proj2 (box_In _ p)). split; [exact Hp |].
        apply (site_in_cube_mono (site_radius (p4_site p))).
        * apply Nat.le_max_l.
        * apply site_in_cube_radius.
      + apply (box_mono n0).
        * apply Nat.le_max_r.
        * apply IH. exact Hq.
  Qed.

  (* =======================================================================
     5. The shell Lambda_{n+1} \ Lambda_n
     ======================================================================= *)

  (* the plaquettes added when passing from the cube of side n to the cube of side n + 1 *)
  Lemma box_split : forall n, exists Q : list Plaq4D,
    Permutation (su2_box (S n)) (Q ++ su2_box n) /\
    (forall q, In q Q -> In q (su2_box (S n)) /\ ~ In q (su2_box n)) /\
    (length Q <= length (su2_box (S n)))%nat.
  Proof.
    intro n.
    set (inb := fun q : Plaq4D => existsb (Z2GaugeClustering.plaq4D_eqb q) (su2_box n)).
    assert (Hinb : forall q, inb q = true <-> In q (su2_box n)).
    { intro q. unfold inb. split.
      - intro H. apply (proj1 (existsb_exists _ _)) in H. destruct H as [x [Hx He]].
        apply (proj1 (Z2GaugeClustering.plaq4D_eqb_spec q x)) in He.
        subst x. exact Hx.
      - intro Hq. apply (proj2 (existsb_exists _ _)). exists q.
        split; [exact Hq |].
        apply (proj2 (Z2GaugeClustering.plaq4D_eqb_spec q q)). reflexivity. }
    set (Q := filter (fun q => negb (inb q)) (su2_box (S n))).
    assert (HQ : forall q, In q Q <-> (In q (su2_box (S n)) /\ ~ In q (su2_box n))).
    { intro q. unfold Q. split.
      - intro H. apply (proj1 (filter_In _ _ _)) in H. destruct H as [H1 H2].
        split; [exact H1 |]. intro H3. apply (proj2 (Hinb q)) in H3.
        rewrite H3 in H2. discriminate H2.
      - intros [H1 H2]. apply (proj2 (filter_In _ _ _)). split; [exact H1 |].
        destruct (inb q) eqn:E; [| reflexivity].
        exfalso. apply H2. apply (proj1 (Hinb q)). exact E. }
    exists Q. split; [| split].
    - apply NoDup_Permutation.
      + apply box_nodup.
      + apply NoDup_app_disj.
        * unfold Q. apply NoDup_filter. apply box_nodup.
        * apply box_nodup.
        * intros x Hx1 Hx2. apply (proj1 (HQ x)) in Hx1. exact (proj2 Hx1 Hx2).
      + intro x. split.
        * intro Hx. apply (proj2 (in_app_iff _ _ _)).
          destruct (inb x) eqn:E.
          -- right. apply (proj1 (Hinb x)). exact E.
          -- left. apply (proj2 (HQ x)). split; [exact Hx |].
             intro H. apply (proj2 (Hinb x)) in H. rewrite H in E. discriminate E.
        * intro Hx. apply (proj1 (in_app_iff _ _ _)) in Hx. destruct Hx as [Hx | Hx].
          -- apply (proj1 (HQ x)) in Hx. exact (proj1 Hx).
          -- apply (box_mono n (S n)); [apply Nat.le_succ_diag_r | exact Hx].
    - intros q Hq. apply (proj1 (HQ q)). exact Hq.
    - unfold Q. apply filter_length_le.
  Qed.

  (* a site of the cube of side n + 1 outside the cube of side n is far from
     every site of the cube of side n0 *)
  Lemma cube_shell_manhattan : forall n0 n s1 s2,
    site_in_cube n0 s1 -> site_in_cube (S n) s2 -> ~ site_in_cube n s2 ->
    (Z.of_nat (S n) - Z.of_nat n0 <= site4D_manhattan s1 s2)%Z.
  Proof.
    intros n0 n [t1 x1 y1 z1] [t2 x2 y2 z2].
    unfold site_in_cube, site4D_manhattan. cbn [s4_t s4_x s4_y s4_z].
    intros H1 H2 H3. lia.
  Qed.

  (* a plaquette of the new shell is far from every plaquette of a smaller cube *)
  Lemma shell_far : forall n0 n p q, (n0 <= n)%nat ->
    In p (su2_box n0) -> In q (su2_box (S n)) -> ~ In q (su2_box n) ->
    (INR (S n) - INR n0) / 2 <= plaq4D_dist p q.
  Proof.
    intros n0 n p q Hn Hp Hq Hnq.
    apply (proj1 (box_In n0 p)) in Hp. destruct Hp as [_ Hp].
    apply (proj1 (box_In (S n) q)) in Hq. destruct Hq as [Hwf Hq].
    assert (Hout : ~ site_in_cube n (p4_site q)).
    { intro H. apply Hnq. apply (proj2 (box_In n q)). split; assumption. }
    pose proof (cube_shell_manhattan n0 n (p4_site p) (p4_site q) Hp Hq Hout) as Hz.
    apply IZR_le in Hz. rewrite minus_IZR in Hz.
    rewrite <- !INR_IZR_INZ in Hz.
    unfold plaq4D_dist. lra.
  Qed.

  (* =======================================================================
     6. Geometric growth of the cardinality
     ======================================================================= *)

  Lemma pow4_step : forall a : R, 3 <= a -> (a + 2) ^ 4 <= 8 * a ^ 4.
  Proof.
    intros a Ha.
    assert (H1 : (a + 2) ^ 4 <= (5 / 3 * a) ^ 4).
    { apply pow_incr. lra. }
    rewrite Rpow_mult_distr in H1.
    assert (H2 : (5 / 3) ^ 4 = 625 / 81).
    { cbn [pow]. field. }
    rewrite H2 in H1.
    assert (H3 : 0 <= a ^ 4).
    { apply pow_le. lra. }
    set (A := a ^ 4) in *. set (B := (a + 2) ^ 4) in *. lra.
  Qed.

  Lemma pow4_bound : forall n : nat, (2 * INR n + 3) ^ 4 <= 81 * 8 ^ n.
  Proof.
    induction n as [| n IH].
    - cbn [INR pow]. lra.
    - rewrite S_INR.
      replace (2 * (INR n + 1) + 3) with ((2 * INR n + 3) + 2) by ring.
      assert (Ha : 3 <= 2 * INR n + 3).
      { pose proof (pos_INR n) as Hn. lra. }
      pose proof (pow4_step (2 * INR n + 3) Ha) as H.
      rewrite <- (tech_pow_Rmult 8 n).
      set (A := (2 * INR n + 3) ^ 4) in *.
      set (B := (2 * INR n + 3 + 2) ^ 4) in *.
      set (C := 8 ^ n) in *.
      lra.
  Qed.

  (* the cardinality of the cubes grows at most geometrically *)
  Lemma box_card_bound : forall n : nat, INR (length (su2_box (S n))) <= 486 * 8 ^ n.
  Proof.
    intro n. rewrite box_length.
    replace (2 * S n + 1)%nat with (2 * n + 3)%nat by lia.
    rewrite mult_INR, pow_INR, plus_INR, mult_INR.
    replace (INR 6) with 6 by (symmetry; exact (INR_IZR_INZ 6)).
    replace (INR 2) with 2 by (symmetry; exact (INR_IZR_INZ 2)).
    replace (INR 3) with 3 by (symmetry; exact (INR_IZR_INZ 3)).
    pose proof (pow4_bound n) as H.
    set (A := (2 * INR n + 3) ^ 4) in *. set (C := 8 ^ n) in *. lra.
  Qed.

End LatticeBoxes.
