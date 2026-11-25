(* =========================================================================
   ym/z2_min_area.v

   The minimal-area lemma for rectangular Wilson loops of the 4D Z_2 lattice
   gauge theory (used by the Wilson-loop area law, Target 7e):

     Any list G of canonical plaquettes of Z^4 whose mod-2 boundary is the
     a x b rectangular loop `z2_rect_loop s0 mu nu a b` (mu <> nu) has at
     least a * b plaquettes.

   Proof (a "probe" / intersection-number argument, no topology needed):
   for integers A, B let `probe A B` be the Z_2 link configuration that is
   -1 exactly on the mu-direction links whose base site has mu-coordinate A
   and nu-coordinate > B (in the (mu, nu)-plane picture: the links crossed
   by the ray issued in direction nu from the centre of the cell (A, B)).
   Then
     - the holonomy of `probe A B` around a plaquette with distinct
       directions is -1 only if the plaquette is anchored at mu-coordinate
       A and nu-coordinate B (`probe_plaq_links`, `probe_plaq`);
     - for i < a and j < b the holonomy of
       `probe (coord s0 mu + i) (coord s0 nu + j)` around the rectangular
       loop is -1 (`probe_rect_loop`);
     - a list of links in which every link occurs an even number of times
       has holonomy +1 for every configuration (`allEven_holonomy`).
   Hence each of the a * b cells (i, j) of the rectangle carries the anchor
   coordinates of some plaquette of G (`column_plaquette`), and distinct
   cells give distinct plaquettes, so a * b <= |G| (`rect_min_area`).

   Depends ONLY on Coq stdlib + verification.Challenge
   + verification.ChallengeZ2Gauge + verification.ChallengeZ2AreaLaw
   + rg.dup_clustering + rg.penrose_tree_bound (NoDup_map_in)
   + ym.z2_gauge_expansion + ym.z2_even_holonomy
   (+ ym.z2_gauge_clustering + ym.z2_polymer_gas, loaded by the latter).
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import rg.dup_clustering.
Require Import rg.penrose_tree_bound.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.z2_polymer_gas.
Require Import ym.z2_even_holonomy.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw.
Import DupClustering Z2GaugeExpansion Z2EvenHolonomy.
Open Scope R_scope.

Module Z2MinArea.

  (* =======================================================================
     1. Coordinates of a site
     ======================================================================= *)

  Definition coord (s : Site4D) (d : Dir4D) : Z :=
    match d with
    | D4_t => s4_t s
    | D4_x => s4_x s
    | D4_y => s4_y s
    | D4_z => s4_z s
    end.

  Lemma coord_shift_same : forall s d,
    coord (shift4D s d) d = (coord s d + 1)%Z.
  Proof. intros s []; reflexivity. Qed.

  Lemma coord_shift_other : forall s d d',
    d <> d' -> coord (shift4D s d) d' = coord s d'.
  Proof.
    intros s [] [] H; try reflexivity; exfalso; apply H; reflexivity.
  Qed.

  Lemma coord_shift_n_same : forall s d k,
    coord (shift4D_n s d k) d = (coord s d + Z.of_nat k)%Z.
  Proof.
    intros s d k. induction k as [| k IH].
    - cbn [shift4D_n]. lia.
    - cbn [shift4D_n]. rewrite coord_shift_same, IH. lia.
  Qed.

  Lemma coord_shift_n_other : forall s d d' k,
    d <> d' -> coord (shift4D_n s d k) d' = coord s d'.
  Proof.
    intros s d d' k H. induction k as [| k IH].
    - reflexivity.
    - cbn [shift4D_n]. rewrite (coord_shift_other _ d d' H). exact IH.
  Qed.

  Lemma dir4D_eqb_reflect : forall d d', reflect (d = d') (dir4D_eqb d d').
  Proof. intros [] []; cbn [dir4D_eqb]; constructor; congruence. Qed.

  Lemma dir4D_eqb_refl : forall d, dir4D_eqb d d = true.
  Proof. intros []; reflexivity. Qed.

  Lemma dir4D_eqb_neq : forall d d', d <> d' -> dir4D_eqb d d' = false.
  Proof.
    intros d d' H. destruct (dir4D_eqb_reflect d d') as [E | E];
      [contradiction | reflexivity].
  Qed.

  (* =======================================================================
     2. The probe configuration
     ======================================================================= *)

  (* -1 exactly on the mu-direction links based at a site with
     mu-coordinate A and nu-coordinate strictly above B. *)
  Definition probe (mu nu : Dir4D) (A B : Z) : Z2Config :=
    fun l =>
      dir4D_eqb (snd l) mu && (coord (fst l) mu =? A)%Z
      && (B <? coord (fst l) nu)%Z.

  (* =======================================================================
     3. The probe around a plaquette
     ======================================================================= *)

  (* Two mu-links in the same column c at heights h and h + 1: their signs
     differ only if the column is A and the lower height is B. *)
  Lemma sign_pair_step : forall (A B c h : Z),
    z2_sign ((c =? A)%Z && (B <? h)%Z) *
    z2_sign ((c =? A)%Z && (B <? h + 1)%Z) = -1 ->
    c = A /\ h = B.
  Proof.
    intros A B c h.
    destruct (Z.eqb_spec c A) as [Ha | Ha];
      destruct (Z.ltb_spec B h) as [Hb | Hb];
      destruct (Z.ltb_spec B (h + 1)) as [Hb' | Hb'];
      cbn [andb z2_sign]; intro H; try (exfalso; lra); split; lia.
  Qed.

  (* Two links carrying the same value cancel. *)
  Lemma sign_pair_same : forall (x : bool), z2_sign x * z2_sign x <> -1.
  Proof.
    intros x H. rewrite z2_sign_sq in H. lra.
  Qed.

  Lemma probe_plaq_links : forall mu nu A B s m n,
    mu <> nu -> m <> n ->
    z2_holonomy (probe mu nu A B)
      [(s, m); (s, n); (shift4D s m, n); (shift4D s n, m)] = -1 ->
    coord s mu = A /\ coord s nu = B.
  Proof.
    intros mu nu A B s m n Hmunu Hmn.
    unfold z2_holonomy. cbn [map fold_right]. unfold probe. cbn [fst snd].
    destruct (dir4D_eqb_reflect m mu) as [Em | Em].
    - (* m = mu, hence n <> mu: only (s, mu) and (s + n, mu) can be probed *)
      subst m.
      assert (Hn : n <> mu) by (intro E; apply Hmn; symmetry; exact E).
      rewrite (dir4D_eqb_neq n mu Hn). cbn [andb z2_sign].
      rewrite (coord_shift_other s n mu Hn).
      destruct (dir4D_eqb_reflect n nu) as [En | En].
      + subst n. rewrite (coord_shift_same s nu).
        intro H. apply (sign_pair_step A B (coord s mu) (coord s nu)).
        rewrite <- H. ring.
      + rewrite (coord_shift_other s n nu En).
        intro H. exfalso.
        apply (sign_pair_same ((coord s mu =? A)%Z && (B <? coord s nu)%Z)).
        rewrite <- H. ring.
    - (* m <> mu *)
      cbn [andb z2_sign].
      destruct (dir4D_eqb_reflect n mu) as [En | En].
      + (* n = mu: only (s, mu) and (s + m, mu) can be probed *)
        subst n. cbn [andb].
        rewrite (coord_shift_other s m mu Em).
        destruct (dir4D_eqb_reflect m nu) as [Em' | Em'].
        * subst m. rewrite (coord_shift_same s nu).
          intro H. apply (sign_pair_step A B (coord s mu) (coord s nu)).
          rewrite <- H. ring.
        * rewrite (coord_shift_other s m nu Em').
          intro H. exfalso.
          apply (sign_pair_same ((coord s mu =? A)%Z && (B <? coord s nu)%Z)).
          rewrite <- H. ring.
      + (* neither direction is mu: no link is probed *)
        cbn [andb z2_sign]. intro H. exfalso. lra.
  Qed.

  Lemma wf_plaq_dirs_neq : forall p, wf_plaq_4D p -> p4_mu p <> p4_nu p.
  Proof.
    intros p H Heq. unfold wf_plaq_4D, canonical_planes_4D in H. cbn [In] in H.
    destruct H as [H | [H | [H | [H | [H | [H | []]]]]]];
      injection H as H1 H2; congruence.
  Qed.

  Lemma probe_plaq : forall mu nu A B p,
    mu <> nu -> wf_plaq_4D p ->
    z2_plaq (probe mu nu A B) p = -1 ->
    coord (p4_site p) mu = A /\ coord (p4_site p) nu = B.
  Proof.
    intros mu nu A B p Hmunu Hwf H.
    exact (probe_plaq_links mu nu A B (p4_site p) (p4_mu p) (p4_nu p)
             Hmunu (wf_plaq_dirs_neq p Hwf) H).
  Qed.

  (* =======================================================================
     4. The probe around the rectangular loop
     ======================================================================= *)

  Lemma holonomy_all_false : forall (U : Z2Config) (C : list Link4D),
    (forall l, In l C -> U l = false) -> z2_holonomy U C = 1.
  Proof.
    intros U C H. rewrite (holonomy_local U (fun _ => false) C H).
    apply holonomy_base.
  Qed.

  (* A configuration that is -1 at exactly one index of an indexed family of
     links has holonomy -1 along that family. *)
  Lemma holonomy_seq_single : forall (U : Z2Config) (f : nat -> Link4D) n st i,
    (st <= i < st + n)%nat ->
    (forall k, (st <= k < st + n)%nat -> U (f k) = (k =? i)%nat) ->
    z2_holonomy U (map f (seq st n)) = -1.
  Proof.
    intros U f n. induction n as [| n IH]; intros st i Hi HU.
    - lia.
    - cbn [seq map]. rewrite holonomy_cons.
      destruct (Nat.eq_dec st i) as [Heq | Hne].
      + subst st. rewrite (HU i) by lia. rewrite Nat.eqb_refl. cbn [z2_sign].
        rewrite holonomy_all_false; [lra |].
        intros l Hl. apply in_map_iff in Hl. destruct Hl as [k [Hk Hin]].
        subst l. apply in_seq in Hin. rewrite (HU k) by lia.
        apply Nat.eqb_neq. lia.
      + rewrite (HU st) by lia.
        replace (st =? i)%nat with false
          by (symmetry; apply Nat.eqb_neq; exact Hne).
        cbn [z2_sign]. rewrite (IH (S st) i).
        * lra.
        * lia.
        * intros k Hk. apply HU. lia.
  Qed.

  Lemma probe_rect_loop : forall s0 mu nu a b i j,
    mu <> nu -> (i < a)%nat -> (j < b)%nat ->
    z2_holonomy
      (probe mu nu (coord s0 mu + Z.of_nat i) (coord s0 nu + Z.of_nat j))
      (z2_rect_loop s0 mu nu a b) = -1.
  Proof.
    intros s0 mu nu a b i j Hmn Hi Hj.
    assert (Hnm : nu <> mu) by (intro E; apply Hmn; symmetry; exact E).
    unfold z2_rect_loop. rewrite !holonomy_app.
    set (U := probe mu nu (coord s0 mu + Z.of_nat i) (coord s0 nu + Z.of_nat j)).
    (* bottom side: at height coord s0 nu, not above B *)
    assert (H1 : z2_holonomy U (z2_segment s0 mu a) = 1).
    { apply holonomy_all_false. intros l Hl. unfold z2_segment in Hl.
      apply in_map_iff in Hl. destruct Hl as [k [Hk _]]. subst l.
      unfold U, probe. cbn [fst snd].
      rewrite (coord_shift_n_other s0 mu nu k Hmn).
      replace (coord s0 nu + Z.of_nat j <? coord s0 nu)%Z with false
        by (symmetry; apply Z.ltb_ge; lia).
      apply andb_false_r. }
    (* right and left sides: nu-direction links *)
    assert (Hside : forall s, z2_holonomy U (z2_segment s nu b) = 1).
    { intro s. apply holonomy_all_false. intros l Hl. unfold z2_segment in Hl.
      apply in_map_iff in Hl. destruct Hl as [k [Hk _]]. subst l.
      unfold U, probe. cbn [fst snd].
      rewrite (dir4D_eqb_neq nu mu Hnm). reflexivity. }
    (* top side: exactly the link in column i is probed *)
    assert (H3 : z2_holonomy U (z2_segment (shift4D_n s0 nu b) mu a) = -1).
    { unfold z2_segment.
      apply (holonomy_seq_single U
               (fun k => (shift4D_n (shift4D_n s0 nu b) mu k, mu)) a 0%nat i);
        [lia |].
      intros k Hk. unfold U, probe. cbn [fst snd].
      rewrite dir4D_eqb_refl.
      rewrite (coord_shift_n_same (shift4D_n s0 nu b) mu k).
      rewrite (coord_shift_n_other (shift4D_n s0 nu b) mu nu k Hmn).
      rewrite (coord_shift_n_same s0 nu b).
      rewrite (coord_shift_n_other s0 nu mu b Hnm).
      cbn [andb].
      replace (coord s0 nu + Z.of_nat j <? coord s0 nu + Z.of_nat b)%Z with true
        by (symmetry; apply Z.ltb_lt; lia).
      rewrite andb_true_r.
      destruct (Nat.eqb_spec k i) as [E | E].
      - subst k. apply Z.eqb_refl.
      - apply Z.eqb_neq. lia. }
    rewrite H1, H3, !Hside. lra.
  Qed.

  (* =======================================================================
     5. A plaquette of G in every column of the rectangle
     ======================================================================= *)

  Lemma column_plaquette : forall s0 mu nu a b (G : list Plaq4D) i j,
    mu <> nu ->
    Forall wf_plaq_4D G ->
    allEven (z2_rect_loop s0 mu nu a b ++ flat_map plaq4D_links G) = true ->
    (i < a)%nat -> (j < b)%nat ->
    exists p, In p G /\
      coord (p4_site p) mu = (coord s0 mu + Z.of_nat i)%Z /\
      coord (p4_site p) nu = (coord s0 nu + Z.of_nat j)%Z.
  Proof.
    intros s0 mu nu a b G i j Hmn Hwf Heven Hi Hj.
    pose proof (allEven_holonomy
                  (probe mu nu (coord s0 mu + Z.of_nat i) (coord s0 nu + Z.of_nat j))
                  _ Heven) as H.
    rewrite holonomy_app, (probe_rect_loop s0 mu nu a b i j Hmn Hi Hj),
      holonomy_flat_map in H.
    assert (H' : rprod G (z2_plaq (probe mu nu (coord s0 mu + Z.of_nat i)
                                     (coord s0 nu + Z.of_nat j))) = -1) by lra.
    destruct (rprod_minus_one_exists
                (z2_plaq (probe mu nu (coord s0 mu + Z.of_nat i)
                            (coord s0 nu + Z.of_nat j))) G
                (fun p _ => holonomy_pm1 _ (plaq4D_links p)) H')
      as [p [Hp Hm1]].
    exists p. split; [exact Hp |].
    apply (probe_plaq mu nu _ _ p Hmn); [| exact Hm1].
    exact (proj1 (Forall_forall wf_plaq_4D G) Hwf p Hp).
  Qed.

  (* =======================================================================
     6. Counting
     ======================================================================= *)

  Lemma NoDup_app_disjoint : forall {A : Type} (l1 l2 : list A),
    NoDup l1 -> NoDup l2 -> (forall x, In x l1 -> ~ In x l2) ->
    NoDup (l1 ++ l2).
  Proof.
    intros A l1 l2 H1 H2 Hd. induction H1 as [| x l1 Hx H1 IH].
    - exact H2.
    - cbn [app]. constructor.
      + intro Hin. apply in_app_or in Hin. destruct Hin as [Hin | Hin].
        * exact (Hx Hin).
        * exact (Hd x (or_introl eq_refl) Hin).
      + apply IH. intros y Hy. apply Hd. right. exact Hy.
  Qed.

  Lemma NoDup_list_prod : forall {A B : Type} (l : list A) (l' : list B),
    NoDup l -> NoDup l' -> NoDup (list_prod l l').
  Proof.
    intros A B l l' Hl Hl'. induction Hl as [| x l Hx Hl IH].
    - constructor.
    - cbn [list_prod]. apply NoDup_app_disjoint.
      + apply PenroseTreeBound.NoDup_map_in; [exact Hl' |].
        intros y1 y2 _ _ Heq. injection Heq as Heq. exact Heq.
      + exact IH.
      + intros [x' y'] Hin1 Hin2. apply in_map_iff in Hin1.
        destruct Hin1 as [y [Heq _]]. injection Heq as Hx' Hy'. subst x' y'.
        apply in_prod_iff in Hin2. destruct Hin2 as [Hin2 _]. exact (Hx Hin2).
  Qed.

  (* Any plaquette set whose mod-2 boundary is the a x b rectangular loop has
     at least a * b plaquettes. *)
  Theorem rect_min_area :
    forall (s0 : Site4D) (mu nu : Dir4D) (a b : nat) (G : list Plaq4D),
      mu <> nu ->
      Forall wf_plaq_4D G ->
      allEven (z2_rect_loop s0 mu nu a b ++ flat_map plaq4D_links G) = true ->
      (a * b <= length G)%nat.
  Proof.
    intros s0 mu nu a b G Hmn Hwf Heven.
    set (key := fun p : Plaq4D => (coord (p4_site p) mu, coord (p4_site p) nu)).
    set (K := list_prod
                (map (fun i => (coord s0 mu + Z.of_nat i)%Z) (seq 0 a))
                (map (fun j => (coord s0 nu + Z.of_nat j)%Z) (seq 0 b))).
    assert (HlenK : length K = (a * b)%nat).
    { unfold K. rewrite prod_length, !map_length, !seq_length. reflexivity. }
    assert (HndK : NoDup K).
    { unfold K. apply NoDup_list_prod.
      - apply PenroseTreeBound.NoDup_map_in; [apply seq_NoDup |].
        intros x y _ _ H. cbn beta in H. lia.
      - apply PenroseTreeBound.NoDup_map_in; [apply seq_NoDup |].
        intros x y _ _ H. cbn beta in H. lia. }
    assert (Hincl : incl K (map key G)).
    { intros [x y] Hin. unfold K in Hin. apply in_prod_iff in Hin.
      destruct Hin as [Hx Hy].
      apply in_map_iff in Hx. destruct Hx as [i [Hxi Hi]]. apply in_seq in Hi.
      apply in_map_iff in Hy. destruct Hy as [j [Hyj Hj]]. apply in_seq in Hj.
      destruct (column_plaquette s0 mu nu a b G i j Hmn Hwf Heven)
        as [p [Hp [Hpa Hpb]]]; [lia | lia |].
      apply in_map_iff. exists p. split; [| exact Hp].
      unfold key. rewrite Hpa, Hpb, Hxi, Hyj. reflexivity. }
    rewrite <- HlenK, <- (map_length key G).
    apply NoDup_incl_length; assumption.
  Qed.

End Z2MinArea.
