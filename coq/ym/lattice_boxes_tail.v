(* =========================================================================
   ym/lattice_boxes_tail.v

   The tail of the exponential weight outside a cube of the exhausting
   sequence Lambda_n = `su2_box n` of
   `verification/ChallengeSU2InfiniteVolume.v`.

     rsum_incl_le     a sum of non-negative terms over a duplicate-free list
                      is monotone in the underlying set;
     outside_box_sum  for a plaquette p of Lambda_{n0} and every finite
                      duplicate-free list Q of canonical plaquettes lying
                      outside Lambda_m (m >= n0),
                        sum_{q in Q} exp (- 2 ln 16 * (dist p q - 1))
                          <= 972 * exp ((n0 + 1) ln 16) * 2^{-m}.

   Proof of the second statement.  Q is contained in some Lambda_{m + d}
   (ym/lattice_boxes.v, box_exhaust).  By induction on d, the part of Q
   inside Lambda_{m + d + 1} splits into the part inside Lambda_{m + d} and
   the part in the shell Lambda_{m + d + 1} \ Lambda_{m + d}.  A plaquette of
   that shell is at distance >= (m + d + 1 - n0) / 2 from p (shell_far), so
   its weight is <= exp ((n0 + 1) ln 16) * 16^{-(m + d)}, and there are at
   most |Lambda_{m + d + 1}| <= 486 * 8^{m + d} of them (box_card_bound).
   Hence the shell contributes <= 486 * exp ((n0 + 1) ln 16) * 2^{-(m + d)},
   and the geometric series sums to 972 * exp ((n0 + 1) ln 16) * 2^{-m}.

   Every statement below is a closed theorem: nothing is postulated and no
   proof is left open.
   ========================================================================= *)

From Coq Require Import Reals ZArith Bool Arith List Lia Lra Psatz Permutation.
Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.ChallengeSU2Gauge.
Require Import verification.ChallengeSU2InfiniteVolume.
Require Import rg.dup_clustering.
Require Import rg.product_measure.
Require Import ym.z2_gauge_expansion.
Require Import ym.z2_gauge_clustering.
Require Import ym.lattice_boxes.
Require Import ym.su2_infinite_volume.

Import ListNotations.
Import Challenge ChallengeZ2Gauge ChallengeZ2AreaLaw ChallengeSU2Gauge ChallengeSU2InfiniteVolume.
Import DupClustering.
Open Scope R_scope.

Module LatticeBoxesTail.

  (* =======================================================================
     1. Finite sums: monotonicity in the set, splitting by a predicate
     ======================================================================= *)

  (* a sum of non-negative terms over a duplicate-free list is monotone in the set *)
  Lemma rsum_incl_le : forall {A : Type} (l l' : list A) (t : A -> R),
    NoDup l -> incl l l' -> (forall x, 0 <= t x) -> rsum l t <= rsum l' t.
  Proof.
    intros A l. induction l as [| a l IH]; intros l' t Hnd Hincl Ht.
    - rewrite rsum_nil. apply rsum_nonneg. intros x _. apply Ht.
    - assert (Ha : In a l') by (apply Hincl; left; reflexivity).
      destruct (in_split a l' Ha) as [l1 [l2 Hl']]. subst l'.
      destruct (proj1 (NoDup_cons_iff a l) Hnd) as [Hnotin Hnd'].
      assert (Hi : incl l (l1 ++ l2)).
      { intros x Hx.
        assert (Hx' : In x (l1 ++ a :: l2)) by (apply Hincl; right; exact Hx).
        apply in_app_or in Hx'. apply in_or_app.
        destruct Hx' as [H | [H | H]].
        - left. exact H.
        - exfalso. apply Hnotin. rewrite H. exact Hx.
        - right. exact H. }
      pose proof (IH (l1 ++ l2) t Hnd' Hi Ht) as H.
      rewrite rsum_app in H. rewrite rsum_cons, rsum_app, rsum_cons.
      pose proof (Ht a) as Hta. lra.
  Qed.

  (* a sum splits into the part where a predicate holds and the part where it fails *)
  Lemma rsum_filter_split : forall {A : Type} (f : A -> bool) (l : list A) (t : A -> R),
    rsum l t = rsum (filter f l) t + rsum (filter (fun x => negb (f x)) l) t.
  Proof.
    intros A f l t. induction l as [| a l IH].
    - cbn [filter]. rewrite rsum_nil. ring.
    - cbn [filter]. rewrite rsum_cons, IH.
      destruct (f a); cbn [negb]; rewrite rsum_cons; ring.
  Qed.

  (* =======================================================================
     2. Boolean membership in a list of plaquettes
     ======================================================================= *)

  Definition inb (L : list Plaq4D) (q : Plaq4D) : bool :=
    existsb (Z2GaugeClustering.plaq4D_eqb q) L.

  Lemma inb_spec : forall L q, inb L q = true <-> In q L.
  Proof.
    intros L q. unfold inb. split.
    - intro H. apply (proj1 (existsb_exists _ _)) in H. destruct H as [x [Hx He]].
      apply (proj1 (Z2GaugeClustering.plaq4D_eqb_spec q x)) in He.
      subst x. exact Hx.
    - intro Hq. apply (proj2 (existsb_exists _ _)). exists q.
      split; [exact Hq |].
      apply (proj2 (Z2GaugeClustering.plaq4D_eqb_spec q q)). reflexivity.
  Qed.

  (* =======================================================================
     3. The weight of a plaquette of the shell Lambda_{n+1} \ Lambda_n
     ======================================================================= *)

  Lemma shell_term : forall (n0 n : nat) (p q : Plaq4D), (n0 <= n)%nat ->
    In p (su2_box n0) -> In q (su2_box (S n)) -> ~ In q (su2_box n) ->
    exp (- (2 * ln 16) * (plaq4D_dist p q - 1))
    <= exp (INR (S n0) * ln 16) * (/ 16) ^ n.
  Proof.
    intros n0 n p q Hn Hp Hq Hnq.
    pose proof (LatticeBoxes.shell_far n0 n p q Hn Hp Hq Hnq) as Hd.
    rewrite <- SU2InfiniteVolume.exp_ln16, Z2GaugeClustering.exp_pow_INR, <- exp_plus.
    apply Z2GaugeClustering.exp_le.
    pose proof SU2InfiniteVolume.ln16_pos as Hl.
    rewrite S_INR in Hd. rewrite S_INR.
    set (d := plaq4D_dist p q) in *. set (L := ln 16) in *.
    assert (Hprod : 0 <= L * (d - (INR n + 1 - INR n0) / 2)).
    { apply Rmult_le_pos; lra. }
    lra.
  Qed.

  (* =======================================================================
     4. Summing the shells between Lambda_m and Lambda_{m + d}
     ======================================================================= *)

  Lemma layers_sum : forall (n0 m : nat) (p : Plaq4D),
    (n0 <= m)%nat -> In p (su2_box n0) ->
    forall (d : nat) (Q : list Plaq4D),
      NoDup Q -> incl Q (su2_box (m + d)) ->
      (forall q, In q Q -> ~ In q (su2_box m)) ->
      rsum Q (fun q => exp (- (2 * ln 16) * (plaq4D_dist p q - 1)))
      <= 972 * exp (INR (S n0) * ln 16) * (/ 2) ^ m * (1 - (/ 2) ^ d).
  Proof.
    intros n0 m p Hn Hp.
    set (t := fun q : Plaq4D => exp (- (2 * ln 16) * (plaq4D_dist p q - 1))).
    set (A := exp (INR (S n0) * ln 16)).
    assert (HA : 0 < A) by (unfold A; apply exp_pos).
    assert (Hm : 0 < (/ 2) ^ m) by (apply pow_lt; lra).
    induction d as [| d IH]; intros Q Hnd Hincl Hout.
    - destruct Q as [| q Q].
      + rewrite rsum_nil.
        replace ((/ 2) ^ 0) with 1 by reflexivity.
        replace (972 * A * (/ 2) ^ m * (1 - 1)) with 0 by ring.
        apply Rle_refl.
      + exfalso. apply (Hout q (or_introl eq_refl)).
        rewrite Nat.add_0_r in Hincl. apply Hincl. left. reflexivity.
    - set (j := (m + d)%nat).
      assert (Hj : (m + S d)%nat = S j) by (unfold j; lia).
      rewrite Hj in Hincl.
      assert (Hnj : (n0 <= j)%nat) by (unfold j; lia).
      assert (Hjp : (/ 2) ^ j = (/ 2) ^ m * (/ 2) ^ d) by (unfold j; apply pow_add).
      set (f := inb (su2_box j)).
      rewrite (rsum_filter_split f Q t).
      set (Q2 := filter (fun x => negb (f x)) Q).
      (* the part inside Lambda_{m + d}: induction hypothesis *)
      assert (H1 : rsum (filter f Q) t <= 972 * A * (/ 2) ^ m * (1 - (/ 2) ^ d)).
      { apply IH.
        - apply NoDup_filter. exact Hnd.
        - intros q Hq. apply (proj1 (filter_In _ _ _)) in Hq. destruct Hq as [_ Hq].
          apply (proj1 (inb_spec (su2_box j) q)). exact Hq.
        - intros q Hq. apply (proj1 (filter_In _ _ _)) in Hq. apply Hout.
          exact (proj1 Hq). }
      (* the part in the shell Lambda_{m + d + 1} \ Lambda_{m + d} *)
      assert (HQ2 : forall q, In q Q2 -> In q (su2_box (S j)) /\ ~ In q (su2_box j)).
      { intros q Hq. unfold Q2 in Hq. apply (proj1 (filter_In _ _ _)) in Hq.
        destruct Hq as [Hq1 Hq2]. cbv beta in Hq2.
        split; [apply Hincl; exact Hq1 |].
        intro H3.
        assert (E : f q = true) by (apply (proj2 (inb_spec (su2_box j) q)); exact H3).
        rewrite E in Hq2. discriminate Hq2. }
      assert (Hlen : INR (length Q2) <= 486 * 8 ^ j).
      { eapply Rle_trans; [| apply LatticeBoxes.box_card_bound].
        apply le_INR. apply NoDup_incl_length.
        - unfold Q2. apply NoDup_filter. exact Hnd.
        - intros q Hq. exact (proj1 (HQ2 q Hq)). }
      assert (H2 : rsum Q2 t <= 486 * A * (/ 2) ^ j).
      { apply Rle_trans with (rsum Q2 (fun _ => A * (/ 16) ^ j)).
        - apply rsum_le. intros q Hq. destruct (HQ2 q Hq) as [Ha Hb].
          exact (shell_term n0 j p q Hnj Hp Ha Hb).
        - rewrite ProductMeasure.rsum_const.
          assert (H816 : 8 ^ j * (/ 16) ^ j = (/ 2) ^ j).
          { rewrite <- Rpow_mult_distr. f_equal. field. }
          assert (H16 : 0 < (/ 16) ^ j) by (apply pow_lt; lra).
          rewrite <- H816.
          apply Rle_trans with ((486 * 8 ^ j) * (A * (/ 16) ^ j)).
          + apply Rmult_le_compat_r; [| exact Hlen].
            apply Rmult_le_pos; lra.
          + apply Req_le. ring. }
      rewrite Hjp in H2.
      replace ((/ 2) ^ S d) with (/ 2 * (/ 2) ^ d) by reflexivity.
      replace (972 * A * (/ 2) ^ m * (1 - / 2 * (/ 2) ^ d))
        with (972 * A * (/ 2) ^ m * (1 - (/ 2) ^ d)
              + 486 * A * ((/ 2) ^ m * (/ 2) ^ d)) by field.
      apply Rplus_le_compat; [exact H1 | exact H2].
  Qed.

  (* =======================================================================
     5. The plaquettes outside Lambda_m
     ======================================================================= *)

  (* the plaquettes outside the cube of side m contribute a geometrically small amount *)
  Theorem outside_box_sum : forall (n0 m : nat) (p : Plaq4D) (Q : list Plaq4D),
    (n0 <= m)%nat ->
    In p (su2_box n0) ->
    NoDup Q ->
    Forall wf_plaq_4D Q ->
    (forall q, In q Q -> ~ In q (su2_box m)) ->
    rsum Q (fun q => exp (- (2 * ln 16) * (plaq4D_dist p q - 1)))
    <= 972 * exp (INR (S n0) * ln 16) * (/ 2) ^ m.
  Proof.
    intros n0 m p Q Hn Hp Hnd Hwf Hout.
    destruct (LatticeBoxes.box_exhaust Q Hwf) as [r Hr].
    assert (Hincl : incl Q (su2_box (m + (r - m)))).
    { intros q Hq.
      apply (LatticeBoxes.box_mono r (m + (r - m))%nat); [lia |].
      apply Hr. exact Hq. }
    eapply Rle_trans;
      [exact (layers_sum n0 m p Hn Hp (r - m)%nat Q Hnd Hincl Hout) |].
    assert (HA : 0 < exp (INR (S n0) * ln 16)) by apply exp_pos.
    assert (Hm : 0 < (/ 2) ^ m) by (apply pow_lt; lra).
    assert (Hd : 0 < (/ 2) ^ (r - m)) by (apply pow_lt; lra).
    set (A := exp (INR (S n0) * ln 16)) in *.
    set (X := (/ 2) ^ m) in *. set (Y := (/ 2) ^ (r - m)) in *.
    assert (HAX : 0 < A * X) by (apply Rmult_lt_0_compat; assumption).
    assert (HAXY : 0 < A * X * Y) by (apply Rmult_lt_0_compat; assumption).
    replace (972 * A * X * (1 - Y)) with (972 * (A * X) - 972 * (A * X * Y)) by ring.
    replace (972 * A * X) with (972 * (A * X)) by ring.
    lra.
  Qed.

End LatticeBoxesTail.
