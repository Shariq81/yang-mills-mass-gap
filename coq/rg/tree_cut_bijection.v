(* =========================================================================
   tree_cut_bijection.v

   Exact Vertex-1 Edge-Cut Bijection for Spanning Trees on {0, 1, ..., k}:

     For any polymer p0 and tuple Y of length k >= 1:
       tree_count(p0 :: Y) =
         sum_{mask in {0,1}^k, mask[0] = true}
           (#{i < |Y_A| | ob p0 Y_A[i] = true})
           * tree_count(Y_A)
           * tree_count(p0 :: Y_B)

     where Y_A = select_true mask Y, Y_B = select_false mask Y.

   Depends ONLY on Coq stdlib + rg.penrose_tree_bound.
   Zero Axiom / Parameter / Admitted declarations.
   ========================================================================= *)

From Coq Require Import Reals Bool Arith List Lia Lra Permutation.
From rg Require Import penrose_tree_bound.
Import ListNotations.
Import PenroseTreeBound.

Module TreeCutBijection.

  (* =======================================================================
     1. Boolean Masks, Selection, Position Maps, and Binomial Counting
     ======================================================================= *)

  Fixpoint select_true {A : Type} (mask : list bool) (l : list A) : list A :=
    match mask, l with
    | true :: m', x :: xs => x :: select_true m' xs
    | false :: m', _ :: xs => select_true m' xs
    | _, _ => []
    end.

  Fixpoint select_false {A : Type} (mask : list bool) (l : list A) : list A :=
    match mask, l with
    | true :: m', _ :: xs => select_false m' xs
    | false :: m', x :: xs => x :: select_false m' xs
    | _, _ => []
    end.

  Fixpoint count_true (mask : list bool) : nat :=
    match mask with
    | [] => 0%nat
    | true :: m' => S (count_true m')
    | false :: m' => count_true m'
    end.

  Fixpoint pos_true_from (base : nat) (mask : list bool) : list nat :=
    match mask with
    | [] => []
    | true :: m' => base :: pos_true_from (S base) m'
    | false :: m' => pos_true_from (S base) m'
    end.

  Fixpoint pos_false_from (base : nat) (mask : list bool) : list nat :=
    match mask with
    | [] => []
    | true :: m' => pos_false_from (S base) m'
    | false :: m' => base :: pos_false_from (S base) m'
    end.

  Definition pos_A (mask : list bool) : list nat := pos_true_from 1%nat mask.
  Definition pos_B0 (mask : list bool) : list nat := 0%nat :: pos_false_from 1%nat mask.

  Fixpoint all_masks (k : nat) : list (list bool) :=
    match k with
    | 0%nat => [[]]
    | S k' => map (cons true) (all_masks k') ++ map (cons false) (all_masks k')
    end.

  Definition masks_head_true (k : nat) : list (list bool) :=
    match k with
    | 0%nat => []
    | S k' => map (cons true) (all_masks k')
    end.

  Lemma count_true_le : forall mask, (count_true mask <= length mask)%nat.
  Proof.
    induction mask as [| [|] m' IH]; simpl; lia.
  Qed.

  Lemma select_true_length : forall {A : Type} (mask : list bool) (l : list A),
    length mask = length l -> length (select_true mask l) = count_true mask.
  Proof.
    induction mask as [| [|] m' IH]; intros [| x xs] Hlen; simpl in *; try discriminate; try reflexivity.
    - f_equal. apply IH. lia.
    - apply IH. lia.
  Qed.

  Lemma select_false_length : forall {A : Type} (mask : list bool) (l : list A),
    length mask = length l -> length (select_false mask l) = (length mask - count_true mask)%nat.
  Proof.
    induction mask as [| [|] m' IH]; intros [| x xs] Hlen;
      cbn [length select_false count_true] in *; try discriminate; try reflexivity.
    - rewrite (IH xs ltac:(lia)). lia.
    - pose proof (count_true_le m'). rewrite (IH xs ltac:(lia)). lia.
  Qed.

  Lemma pos_true_from_length : forall base mask,
    length (pos_true_from base mask) = count_true mask.
  Proof.
    intros base mask. revert base.
    induction mask as [| [|] m' IH]; intro base; simpl; [reflexivity | f_equal; apply IH | apply IH].
  Qed.

  Lemma pos_false_from_length : forall base mask,
    length (pos_false_from base mask) = (length mask - count_true mask)%nat.
  Proof.
    intros base mask. revert base.
    induction mask as [| [|] m' IH]; intro base;
      cbn [length pos_false_from count_true]; [reflexivity | rewrite IH; lia |].
    pose proof (count_true_le m'). rewrite IH. lia.
  Qed.

  Lemma pos_A_length : forall mask, length (pos_A mask) = count_true mask.
  Proof. intro mask. apply pos_true_from_length. Qed.

  Lemma pos_B0_length : forall mask, length (pos_B0 mask) = S (length mask - count_true mask).
  Proof. intro mask. unfold pos_B0. simpl. rewrite pos_false_from_length. reflexivity. Qed.

  Lemma pos_true_from_in : forall base mask v,
    In v (pos_true_from base mask) <->
    (base <= v)%nat /\ (v < base + length mask)%nat /\ nth (v - base) mask false = true.
  Proof.
    intros base mask. revert base.
    induction mask as [| [|] m' IH]; intros base v; simpl.
    - split; [intros [] | lia].
    - rewrite IH. split.
      + intros [<- | [H1 [H2 H3]]].
        * rewrite Nat.sub_diag. repeat split; try lia; reflexivity.
        * repeat split; try lia.
          replace (v - base)%nat with (S (v - S base)) by lia. exact H3.
      + intros [H1 [H2 H3]].
        destruct (Nat.eq_dec v base) as [-> | Hne]; [left; reflexivity | right].
        repeat split; try lia.
        replace (v - base)%nat with (S (v - S base)) in H3 by lia. exact H3.
    - rewrite IH. split.
      + intros [H1 [H2 H3]]. repeat split; try lia.
        replace (v - base)%nat with (S (v - S base)) by lia. exact H3.
      + intros [H1 [H2 H3]].
        destruct (Nat.eq_dec v base) as [-> | Hne].
        * rewrite Nat.sub_diag in H3. discriminate.
        * repeat split; try lia.
          replace (v - base)%nat with (S (v - S base)) in H3 by lia. exact H3.
  Qed.

  Lemma pos_false_from_in : forall base mask v,
    In v (pos_false_from base mask) <->
    (base <= v)%nat /\ (v < base + length mask)%nat /\ nth (v - base) mask true = false.
  Proof.
    intros base mask. revert base.
    induction mask as [| [|] m' IH]; intros base v; simpl.
    - split; [intros [] | lia].
    - rewrite IH. split.
      + intros [H1 [H2 H3]]. repeat split; try lia.
        replace (v - base)%nat with (S (v - S base)) by lia. exact H3.
      + intros [H1 [H2 H3]].
        destruct (Nat.eq_dec v base) as [-> | Hne].
        * rewrite Nat.sub_diag in H3. discriminate.
        * repeat split; try lia.
          replace (v - base)%nat with (S (v - S base)) in H3 by lia. exact H3.
    - rewrite IH. split.
      + intros [<- | [H1 [H2 H3]]].
        * rewrite Nat.sub_diag. repeat split; try lia; reflexivity.
        * repeat split; try lia.
          replace (v - base)%nat with (S (v - S base)) by lia. exact H3.
      + intros [H1 [H2 H3]].
        destruct (Nat.eq_dec v base) as [-> | Hne]; [left; reflexivity | right].
        repeat split; try lia.
        replace (v - base)%nat with (S (v - S base)) in H3 by lia. exact H3.
  Qed.

  Lemma pos_A_in : forall mask v,
    In v (pos_A mask) <->
    (1 <= v)%nat /\ (v <= length mask)%nat /\ nth (v - 1) mask false = true.
  Proof.
    intros mask v. unfold pos_A. rewrite pos_true_from_in.
    split; intros [H1 [H2 H3]]; repeat split; try lia; exact H3.
  Qed.

  Lemma pos_B0_in : forall mask v,
    In v (pos_B0 mask) <->
    v = 0%nat \/ ((1 <= v)%nat /\ (v <= length mask)%nat /\ nth (v - 1) mask true = false).
  Proof.
    intros mask v. unfold pos_B0. simpl. rewrite pos_false_from_in.
    split; intros [H0 | [H1 [H2 H3]]]; try (left; lia); right; repeat split; try lia; exact H3.
  Qed.

  Lemma nth_bool_default : forall (mask : list bool) i d1 d2,
    (i < length mask)%nat -> nth i mask d1 = nth i mask d2.
  Proof.
    induction mask as [| b m' IH]; intros [| i'] d1 d2 Hi; simpl in *; try lia; try reflexivity.
    apply IH; lia.
  Qed.

  Lemma pos_A_B0_disjoint : forall mask v,
    In v (pos_A mask) -> In v (pos_B0 mask) -> False.
  Proof.
    intros mask v HA HB.
    apply pos_A_in in HA. apply pos_B0_in in HB.
    destruct HA as [H1 [H2 H3]]. destruct HB as [H0 | [_ [_ H4]]]; [lia |].
    rewrite (nth_bool_default mask (v - 1) true false ltac:(lia)) in H4. congruence.
  Qed.

  Lemma pos_A_B0_cover : forall mask v,
    (v <= length mask)%nat -> In v (pos_A mask) \/ In v (pos_B0 mask).
  Proof.
    intros mask v Hv.
    destruct v as [| v'].
    - right. apply pos_B0_in. left; reflexivity.
    - destruct (nth v' mask false) eqn:Eb.
      + left. apply pos_A_in. replace (S v' - 1)%nat with v' by lia. repeat split; try lia; exact Eb.
      + right. apply pos_B0_in. right. replace (S v' - 1)%nat with v' by lia.
        repeat split; try lia. rewrite (nth_bool_default mask v' true false ltac:(lia)). exact Eb.
  Qed.

  (* Strict monotonicity of pos_true_from / pos_false_from *)
  Lemma pos_true_from_gt : forall base mask x,
    In x (pos_true_from base mask) -> (base <= x)%nat.
  Proof. intros base mask x Hin. apply pos_true_from_in in Hin. lia. Qed.

  Lemma pos_false_from_gt : forall base mask x,
    In x (pos_false_from base mask) -> (base <= x)%nat.
  Proof. intros base mask x Hin. apply pos_false_from_in in Hin. lia. Qed.

  Lemma pos_true_from_strict_mono : forall base mask i j,
    (i < j)%nat -> (j < length (pos_true_from base mask))%nat ->
    (nth i (pos_true_from base mask) 0%nat < nth j (pos_true_from base mask) 0%nat)%nat.
  Proof.
    intros base mask. revert base.
    induction mask as [| [|] m' IH]; intros base i j Hij Hlt; simpl in *; [lia | | apply IH; lia].
    destruct i as [| i']; destruct j as [| j']; try lia.
    - pose proof (pos_true_from_gt (S base) m' (nth j' (pos_true_from (S base) m') 0%nat)
                    (nth_In (pos_true_from (S base) m') 0%nat (ltac:(lia) : (j' < length (pos_true_from (S base) m'))%nat))). lia.
    - apply IH; lia.
  Qed.

  Lemma pos_false_from_strict_mono : forall base mask i j,
    (i < j)%nat -> (j < length (pos_false_from base mask))%nat ->
    (nth i (pos_false_from base mask) 0%nat < nth j (pos_false_from base mask) 0%nat)%nat.
  Proof.
    intros base mask. revert base.
    induction mask as [| [|] m' IH]; intros base i j Hij Hlt; simpl in *; [lia | apply IH; lia |].
    destruct i as [| i']; destruct j as [| j']; try lia.
    - pose proof (pos_false_from_gt (S base) m' (nth j' (pos_false_from (S base) m') 0%nat)
                    (nth_In (pos_false_from (S base) m') 0%nat (ltac:(lia) : (j' < length (pos_false_from (S base) m'))%nat))). lia.
    - apply IH; lia.
  Qed.

  Lemma pos_A_strict_mono : forall mask i j,
    (i < j)%nat -> (j < length (pos_A mask))%nat ->
    (nth i (pos_A mask) 0%nat < nth j (pos_A mask) 0%nat)%nat.
  Proof. intros mask i j. apply pos_true_from_strict_mono. Qed.

  Lemma pos_B0_strict_mono : forall mask i j,
    (i < j)%nat -> (j < length (pos_B0 mask))%nat ->
    (nth i (pos_B0 mask) 0%nat < nth j (pos_B0 mask) 0%nat)%nat.
  Proof.
    intros mask i j Hij Hlt. unfold pos_B0 in *. simpl in *.
    destruct i as [| i']; destruct j as [| j']; try lia.
    - pose proof (pos_false_from_gt 1%nat mask (nth j' (pos_false_from 1%nat mask) 0%nat)
                    (nth_In (pos_false_from 1%nat mask) 0%nat (ltac:(lia) : (j' < length (pos_false_from 1%nat mask))%nat))). lia.
    - apply pos_false_from_strict_mono; lia.
  Qed.

  Lemma pos_A_inj : forall mask i j,
    (i < length (pos_A mask))%nat -> (j < length (pos_A mask))%nat ->
    nth i (pos_A mask) 0%nat = nth j (pos_A mask) 0%nat -> i = j.
  Proof.
    intros mask i j Hi Hj Heq.
    destruct (lt_eq_lt_dec i j) as [[Hlt | He] | Hgt]; [| exact He |].
    - pose proof (pos_A_strict_mono mask i j Hlt Hj). lia.
    - pose proof (pos_A_strict_mono mask j i Hgt Hi). lia.
  Qed.

  Lemma pos_B0_inj : forall mask i j,
    (i < length (pos_B0 mask))%nat -> (j < length (pos_B0 mask))%nat ->
    nth i (pos_B0 mask) 0%nat = nth j (pos_B0 mask) 0%nat -> i = j.
  Proof.
    intros mask i j Hi Hj Heq.
    destruct (lt_eq_lt_dec i j) as [[Hlt | He] | Hgt]; [| exact He |].
    - pose proof (pos_B0_strict_mono mask i j Hlt Hj). lia.
    - pose proof (pos_B0_strict_mono mask j i Hgt Hi). lia.
  Qed.

  (* Index lookup in a list of nats *)
  Fixpoint index_of (x : nat) (l : list nat) : nat :=
    match l with
    | [] => 0%nat
    | a :: xs => if Nat.eqb a x then 0%nat else S (index_of x xs)
    end.

  Lemma index_of_spec : forall x l,
    In x l -> (index_of x l < length l)%nat /\ nth (index_of x l) l 0%nat = x.
  Proof.
    intros x l. induction l as [| a xs IH]; intro Hin; simpl in *; [contradiction |].
    destruct (Nat.eqb_spec a x) as [-> | Hne].
    - split; [lia | reflexivity].
    - destruct Hin as [Heq | Hin]; [congruence |].
      destruct (IH Hin) as [Hlt Hnth]. split; [lia | exact Hnth].
  Qed.

  Lemma index_of_nth : forall l i,
    NoDup l -> (i < length l)%nat -> index_of (nth i l 0%nat) l = i.
  Proof.
    induction l as [| a xs IH]; intros i Hnd Hi; simpl in *; [lia |].
    inversion Hnd as [| ? ? Hnot Hnd']; subst.
    destruct i as [| i'].
    - rewrite Nat.eqb_refl. reflexivity.
    - destruct (Nat.eqb_spec a (nth i' xs 0%nat)) as [Heq | Hne].
      + exfalso. apply Hnot. rewrite Heq. apply nth_In; lia.
      + f_equal. apply IH; [exact Hnd' | lia].
  Qed.

  Lemma strict_mono_NoDup : forall l,
    (forall i j, (i < j)%nat -> (j < length l)%nat -> (nth i l 0%nat < nth j l 0%nat)%nat) ->
    NoDup l.
  Proof.
    intros l Hmono.
    assert (Hgen : forall m, (m <= length l)%nat -> NoDup (skipn (length l - m) l)).
    { induction m as [| m' IH]; intro Hm.
      - rewrite Nat.sub_0_r, skipn_all. constructor.
      - replace (length l - S m')%nat with (length l - S m')%nat by reflexivity.
        set (idx := (length l - S m')%nat).
        assert (Hidx : (idx < length l)%nat) by (unfold idx; lia).
        assert (Heq : skipn idx l = nth idx l 0%nat :: skipn (S idx) l).
        { clear - Hidx. clearbody idx. revert idx Hidx.
          induction l as [| a xs IHl]; intros [| i] Hi; simpl in *; try lia; try reflexivity.
          apply IHl; lia. }
        rewrite Heq. constructor.
        + intro Hin.
          assert (Hex : exists j, (j < length (skipn (S idx) l))%nat /\ nth j (skipn (S idx) l) 0%nat = nth idx l 0%nat).
          { destruct (In_nth (skipn (S idx) l) (nth idx l 0%nat) 0%nat Hin) as [j [Hj Hnth]].
            exists j. split; assumption. }
          destruct Hex as [j [Hj Hnth]].
          rewrite skipn_length in Hj.
          assert (Hsk : nth j (skipn (S idx) l) 0%nat = nth (S idx + j) l 0%nat).
          { clear. clearbody idx. revert j. generalize (S idx) as k.
            induction l as [| a xs IHl].
            - intros [| k'] j; simpl; destruct j; reflexivity.
            - intros [| k'] j; simpl; [reflexivity | apply IHl]. }
          rewrite Hsk in Hnth.
          pose proof (Hmono idx (S idx + j)%nat ltac:(lia) ltac:(lia)). lia.
        + replace (S idx) with (length l - m')%nat by (unfold idx; lia).
          apply IH; lia. }
    specialize (Hgen (length l) (le_n _)).
    rewrite Nat.sub_diag in Hgen. exact Hgen.
  Qed.

  (* Correspondence between select_true / select_false and nth_error via pos_A / pos_B0 *)
  Lemma select_true_nth_error_from : forall {P : Type} base mask (Y : list P) i,
    length mask = length Y ->
    (i < count_true mask)%nat ->
    nth_error (select_true mask Y) i = nth_error Y (nth i (pos_true_from base mask) 0%nat - base).
  Proof.
    intros P base mask. revert base.
    induction mask as [| [|] m' IH]; intros base [| y ys] i Hlen Hi; simpl in *; try discriminate; try lia.
    - destruct i as [| i'].
      + rewrite Nat.sub_diag. reflexivity.
      + pose proof (pos_true_from_gt (S base) m' (nth i' (pos_true_from (S base) m') 0%nat)
                      (nth_In (pos_true_from (S base) m') 0%nat (ltac:(rewrite pos_true_from_length; lia) : (i' < length (pos_true_from (S base) m'))%nat))) as Hge.
        replace (nth i' (pos_true_from (S base) m') 0%nat - base)%nat
          with (S (nth i' (pos_true_from (S base) m') 0%nat - S base)) by lia.
        simpl. apply IH; lia.
    - pose proof (pos_true_from_gt (S base) m' (nth i (pos_true_from (S base) m') 0%nat)
                    (nth_In (pos_true_from (S base) m') 0%nat (ltac:(rewrite pos_true_from_length; lia) : (i < length (pos_true_from (S base) m'))%nat))) as Hge.
      replace (nth i (pos_true_from (S base) m') 0%nat - base)%nat
        with (S (nth i (pos_true_from (S base) m') 0%nat - S base)) by lia.
      simpl. apply IH; lia.
  Qed.

  Lemma select_false_nth_error_from : forall {P : Type} base mask (Y : list P) i,
    length mask = length Y ->
    (i < length mask - count_true mask)%nat ->
    nth_error (select_false mask Y) i = nth_error Y (nth i (pos_false_from base mask) 0%nat - base).
  Proof.
    intros P base mask. revert base.
    induction mask as [| [|] m' IH]; intros base [| y ys] i Hlen Hi;
      cbn [length select_false pos_false_from count_true] in *; try discriminate; try lia.
    - pose proof (pos_false_from_gt (S base) m' (nth i (pos_false_from (S base) m') 0%nat)
                    (nth_In (pos_false_from (S base) m') 0%nat (ltac:(rewrite pos_false_from_length; lia) : (i < length (pos_false_from (S base) m'))%nat))) as Hge.
      replace (nth i (pos_false_from (S base) m') 0%nat - base)%nat
        with (S (nth i (pos_false_from (S base) m') 0%nat - S base)) by lia.
      simpl. apply IH; lia.
    - destruct i as [| i'].
      + rewrite Nat.sub_diag. reflexivity.
      + cbn [nth_error nth]. pose proof (count_true_le m').
        pose proof (pos_false_from_gt (S base) m' (nth i' (pos_false_from (S base) m') 0%nat)
                      (nth_In (pos_false_from (S base) m') 0%nat (ltac:(rewrite pos_false_from_length; lia) : (i' < length (pos_false_from (S base) m'))%nat))) as Hge.
        replace (nth i' (pos_false_from (S base) m') 0%nat - base)%nat
          with (S (nth i' (pos_false_from (S base) m') 0%nat - S base)) by lia.
        cbn [nth_error]. apply IH; lia.
  Qed.

  Lemma select_true_nth_error : forall {P : Type} (p0 : P) mask (Y : list P) i,
    length mask = length Y ->
    (i < count_true mask)%nat ->
    nth_error (select_true mask Y) i = nth_error (p0 :: Y) (nth i (pos_A mask) 0%nat).
  Proof.
    intros P p0 mask Y i Hlen Hi.
    unfold pos_A.
    pose proof (pos_true_from_gt 1%nat mask (nth i (pos_true_from 1%nat mask) 0%nat)
                  (nth_In (pos_true_from 1%nat mask) 0%nat (ltac:(rewrite pos_true_from_length; lia) : (i < length (pos_true_from 1%nat mask))%nat))) as Hge.
    destruct (nth i (pos_true_from 1%nat mask) 0%nat) as [| m] eqn:Em; [lia |].
    simpl. replace m with (S m - 1)%nat by lia. rewrite <- Em.
    apply select_true_nth_error_from; assumption.
  Qed.

  Lemma select_false_nth_error : forall {P : Type} (p0 : P) mask (Y : list P) i,
    length mask = length Y ->
    (i < S (length mask - count_true mask))%nat ->
    nth_error (p0 :: select_false mask Y) i = nth_error (p0 :: Y) (nth i (pos_B0 mask) 0%nat).
  Proof.
    intros P p0 mask Y i Hlen Hi.
    unfold pos_B0. destruct i as [| i']; simpl; [reflexivity |].
    pose proof (pos_false_from_gt 1%nat mask (nth i' (pos_false_from 1%nat mask) 0%nat)
                  (nth_In (pos_false_from 1%nat mask) 0%nat (ltac:(rewrite pos_false_from_length; lia) : (i' < length (pos_false_from 1%nat mask))%nat))) as Hge.
    destruct (nth i' (pos_false_from 1%nat mask) 0%nat) as [| m] eqn:Em; [lia |].
    simpl. replace m with (S m - 1)%nat by lia. rewrite <- Em.
    apply select_false_nth_error_from; [exact Hlen | lia].
  Qed.

  Lemma all_masks_in : forall k m, In m (all_masks k) <-> length m = k.
  Proof.
    induction k as [| k' IH]; intros [| b m']; simpl.
    - split; [intros [_|[]]; reflexivity | intro; left; reflexivity].
    - split; [intros [H|[]]; discriminate | discriminate].
    - rewrite in_app_iff, !in_map_iff. split; [intros [[? [H _]] | [? [H _]]]; discriminate | discriminate].
    - rewrite in_app_iff, !in_map_iff. destruct b.
      + split.
        * intros [[x [Heq Hx]] | [x [Heq _]]]; [| discriminate].
          inversion Heq; subst. rewrite IH in Hx. lia.
        * intro Hlen. left. exists m'. split; [reflexivity | apply IH; lia].
      + split.
        * intros [[x [Heq _]] | [x [Heq Hx]]]; [discriminate |].
          inversion Heq; subst. rewrite IH in Hx. lia.
        * intro Hlen. right. exists m'. split; [reflexivity | apply IH; lia].
  Qed.

  Lemma all_masks_NoDup : forall k, NoDup (all_masks k).
  Proof.
    induction k as [| k' IH]; simpl.
    - constructor; [intros [] | constructor].
    - apply NoDup_app_local.
      + apply NoDup_map_in; [exact IH | intros x y _ _ H; inversion H; reflexivity].
      + apply NoDup_map_in; [exact IH | intros x y _ _ H; inversion H; reflexivity].
      + intros m H1 H2. apply in_map_iff in H1; apply in_map_iff in H2.
        destruct H1 as [x [<- _]]; destruct H2 as [y [Heq _]]. discriminate.
  Qed.

  Lemma masks_head_true_in : forall k m,
    (1 <= k)%nat ->
    In m (masks_head_true k) <-> length m = k /\ nth 0%nat m false = true.
  Proof.
    intros [| k'] m Hk; [lia |].
    unfold masks_head_true. rewrite in_map_iff. split.
    - intros [m' [<- Hm']]. apply all_masks_in in Hm'. simpl. split; [lia | reflexivity].
    - intros [Hlen H0]. destruct m as [| [|] m']; simpl in *; try discriminate.
      exists m'. split; [reflexivity | apply all_masks_in; lia].
  Qed.

  Lemma masks_head_true_NoDup : forall k, NoDup (masks_head_true k).
  Proof.
    intros [| k']; unfold masks_head_true; [constructor |].
    apply NoDup_map_in; [apply all_masks_NoDup | intros x y _ _ H; inversion H; reflexivity].
  Qed.

  (* =======================================================================
     2. Climbing to the Child of Root 0 Toward Vertex 1, and Tree Edge-Cut
     ======================================================================= *)

  Fixpoint climb_to_root_child (n fuel : nat) (T : list (nat * nat)) (v : nat) : nat :=
    match fuel with
    | 0%nat => v
    | S fuel' =>
        let p := bfs_parent n T v in
        if Nat.eqb p 0%nat then v else climb_to_root_child n fuel' T p
    end.

  Definition root_child_of_1 (k : nat) (T : list (nat * nat)) : nat :=
    climb_to_root_child (S k) (S k) T 1%nat.

  Definition remove_edge (e0 : nat * nat) (H : list (nat * nat)) : list (nat * nat) :=
    filter (fun e => negb (edge_eqb e e0)) H.

  Lemma remove_edge_in : forall e0 H e,
    In e (remove_edge e0 H) <-> In e H /\ e <> e0.
  Proof.
    intros e0 H e. unfold remove_edge. rewrite filter_In, negb_true_iff.
    destruct (edge_eqb e e0) eqn:E.
    - apply edge_eqb_spec in E. split; [intros [_ Hc]; discriminate | intros [_ Hne]; congruence].
    - split; [intros [Hin _]; split; [exact Hin | intro Heq; subst; rewrite (proj2 (edge_eqb_spec e0 e0) eq_refl) in E; discriminate] | intros [Hin _]; split; [exact Hin | reflexivity]].
  Qed.

  Lemma remove_edge_length : forall e0 H,
    NoDup H -> In e0 H -> length (remove_edge e0 H) = (length H - 1)%nat.
  Proof.
    intros e0 H Hnd Hin. induction H as [| a xs IH]; simpl in *; [contradiction |].
    inversion Hnd as [| ? ? Hnot Hnd']; subst.
    unfold remove_edge; simpl.
    destruct (edge_eqb a e0) eqn:Ea.
    - apply edge_eqb_spec in Ea. subst a.
      assert (Hfilt : filter (fun e => negb (edge_eqb e e0)) xs = xs).
      { clear - Hnot. induction xs as [| b ys IHy]; simpl; [reflexivity |].
        destruct (edge_eqb b e0) eqn:Eb.
        - apply edge_eqb_spec in Eb. subst b. exfalso. apply Hnot; left; reflexivity.
        - simpl. f_equal. apply IHy. intro Hin. apply Hnot; right; exact Hin. }
      simpl. rewrite Hfilt. lia.
    - simpl. destruct Hin as [Heq | Hin].
      + subst a. rewrite (proj2 (edge_eqb_spec e0 e0) eq_refl) in Ea. discriminate.
      + unfold remove_edge in IH. rewrite (IH Hnd' Hin).
        assert (Hpos : (1 <= length xs)%nat) by (destruct xs; [contradiction | simpl; lia]).
        lia.
  Qed.

  Lemma remove_edge_in_sublists : forall E T e0,
    In T (sublists E) -> In (remove_edge e0 T) (sublists E).
  Proof.
    intros E T e0 Hin.
    assert (Hsub : forall {A : Type} (l h : list A) (f : A -> bool),
      In h (sublists l) -> In (filter f h) (sublists l)).
    { induction l as [| a xs IH]; intros h f Hh; simpl in *.
      - destruct Hh as [<- | []]. left; reflexivity.
      - apply in_app_iff in Hh. apply in_app_iff. destruct Hh as [Hh | Hh].
        + left. exact (IH h f Hh).
        + apply in_map_iff in Hh. destruct Hh as [h' [<- Hh']].
          simpl filter. destruct (f a); [right; apply in_map | left]; exact (IH h' f Hh'). }
    exact (Hsub _ E T _ Hin).
  Qed.

  (* Walk avoiding vertex 0 *)
  Inductive reachable_avoid0 (H : list (nat * nat)) : nat -> nat -> Prop :=
  | ra0_refl : forall u, u <> 0%nat -> reachable_avoid0 H u u
  | ra0_step : forall u v w, u <> 0%nat -> v <> 0%nat -> has_edge H u v ->
      reachable_avoid0 H v w -> reachable_avoid0 H u w.

  Lemma reachable_avoid0_to_remove : forall H r u v,
    reachable_avoid0 H u v -> reachable (remove_edge (0%nat, r) H) u v.
  Proof.
    intros H r u v Hr. induction Hr; [apply reach_refl |].
    eapply reach_step; [| exact IHHr].
    destruct H2 as [Ha | Hb]; [left | right]; apply remove_edge_in; split; try assumption;
      intro Heq; inversion Heq; congruence.
  Qed.

  Lemma ra0_right : forall H u v w,
    reachable_avoid0 H u v -> w <> 0%nat -> has_edge H v w -> reachable_avoid0 H u w.
  Proof.
    intros H u v w Hra Hw He. induction Hra.
    - eapply ra0_step; [exact H0 | exact Hw | exact He | apply ra0_refl; exact Hw].
    - eapply ra0_step; [exact H0 | exact H1 | exact H2 | exact (IHHra He)].
  Qed.

  Lemma climb_spec : forall n T fuel v,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < n)%nat) T ->
    is_connectedb n T = true ->
    (1 <= v < n)%nat ->
    (bfs_dist n T v <= fuel)%nat ->
    let r := climb_to_root_child n fuel T v in
    (1 <= r < n)%nat /\ In (0%nat, r) T /\ reachable_avoid0 T r v.
  Proof.
    intros n T fuel. induction fuel as [| fuel' IH]; intros v HwfT Hconn Hv Hfuel.
    - pose proof Hconn as Hc'. apply (is_connectedb_iff n T HwfT) in Hc'. destruct Hc' as [Hn Hreach].
      pose proof (bfs_dist_nonzero n T v HwfT Hn (Hreach v ltac:(lia)) ltac:(lia)). lia.
    - pose proof Hconn as Hc'. apply (is_connectedb_iff n T HwfT) in Hc'. destruct Hc' as [Hn Hreach].
      pose proof (bfs_parent_spec n T v HwfT Hn (Hreach v ltac:(lia)) ltac:(lia))
        as [Hpu [Hev [Hdv _]]].
      simpl climb_to_root_child.
      destruct (Nat.eqb_spec (bfs_parent n T v) 0%nat) as [Hp0 | Hpne].
      + rewrite Hp0 in Hev.
        assert (Hin0v : In (0%nat, v) T).
        { apply (wf_has_edge_mk n T 0%nat v HwfT) in Hev.
          unfold mk_edge in Hev. destruct (Nat.ltb_spec 0%nat v); [exact Hev | lia]. }
        repeat split; [lia | lia | exact Hin0v | apply ra0_refl; lia].
      + destruct (IH (bfs_parent n T v) HwfT Hconn ltac:(lia) ltac:(lia))
          as [Hr [Hin0r Hra]].
        repeat split; [lia | lia | exact Hin0r |].
        exact (ra0_right T _ (bfs_parent n T v) v Hra ltac:(lia) Hev).
  Qed.

  Lemma root_child_of_1_spec : forall k T,
    (1 <= k)%nat ->
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < S k)%nat) T ->
    is_connectedb (S k) T = true ->
    let r := root_child_of_1 k T in
    (1 <= r <= k)%nat /\ In (0%nat, r) T /\ reachable_avoid0 T r 1%nat.
  Proof.
    intros k T Hk HwfT Hconn.
    pose proof Hconn as Hc'. apply (is_connectedb_iff (S k) T HwfT) in Hc'. destruct Hc' as [Hn Hreach].
    destruct (bfs_dist_spec (S k) T 1%nat HwfT Hn (Hreach 1%nat ltac:(lia))) as [_ [_ Hlt]].
    unfold root_child_of_1.
    destruct (climb_spec (S k) T (S k) 1%nat HwfT Hconn ltac:(lia) ltac:(lia)) as [Hr [Hin0r Hra]].
    repeat split; [lia | lia | exact Hin0r | exact Hra].
  Qed.

  (* Removing ANY edge (0, r) from a spanning tree T disconnects 0 from r and partitions vertices *)
  Lemma tree_cut_partition : forall k E T r,
    (1 <= k)%nat ->
    wf_edges (S k) E ->
    In T (spanning_trees (S k) E) ->
    In (0%nat, r) T ->
    let T' := remove_edge (0%nat, r) T in
    ~ reachable T' 0%nat r /\
    (forall v, (v < S k)%nat -> reachable T' 0%nat v \/ reachable T' r v).
  Proof.
    intros k E T r Hk HwfE HinT Hin0r.
    set (T' := remove_edge (0%nat, r) T).
    unfold spanning_trees in HinT. apply filter_In in HinT.
    destruct HinT as [HinSub Htree].
    unfold is_treeb in Htree. rewrite andb_true_iff, Nat.eqb_eq in Htree.
    destruct Htree as [Hconn Hlen].
    pose proof (sublists_Forall _ E T (proj2 HwfE) HinSub) as HwfT.
    pose proof (sublists_NoDup_elem E T (proj1 HwfE) HinSub) as HndT.
    pose proof (remove_edge_in_sublists E T (0%nat, r) HinSub) as HinSub'.
    pose proof (sublists_Forall _ E T' (proj2 HwfE) HinSub') as HwfT'.
    pose proof (remove_edge_length (0%nat, r) T HndT Hin0r) as Hlen'.
    pose proof Hconn as Hc'. apply (is_connectedb_iff (S k) T HwfT) in Hc'.
    destruct Hc' as [_ HreachT].
    split.
    - intro H0r.
      assert (Hedge_to_T' : forall u v, has_edge T u v -> reachable T' u v).
      { intros u v He.
        destruct (edge_eq_dec (mk_edge u v) (0%nat, r)) as [Heq | Hne].
        - unfold mk_edge in Heq. destruct (Nat.ltb_spec u v); inversion Heq; subst.
          + exact H0r.
          + apply reachable_sym. exact H0r.
        - eapply reach_step; [| apply reach_refl].
          apply (wf_has_edge_mk (S k) T u v HwfT) in He.
          apply (wf_has_edge_mk (S k) T' u v HwfT').
          apply remove_edge_in. split; assumption. }
      assert (Hconn' : is_connectedb (S k) T' = true).
      { assert (Hr_to : forall u w, reachable T u w -> reachable T' u w).
        { intros u w Hrw. induction Hrw; [apply reach_refl | eapply reachable_trans; [apply Hedge_to_T'; eassumption | exact IHHrw]]. }
        apply (is_connectedb_iff (S k) T' HwfT'). split; [lia |].
        intros v Hv. apply Hr_to. exact (HreachT v Hv). }
      pose proof (connected_length_ge (S k) E T' HwfE HinSub' Hconn') as Hge.
      fold T' in Hlen'. lia.
    - intros v Hv.
      assert (Hstep : forall u w, reachable T u w ->
        (reachable T' 0%nat u \/ reachable T' r u) ->
        reachable T' 0%nat w \/ reachable T' r w).
      { intros u w Hrw. induction Hrw; intro Hstart; [exact Hstart |].
        apply IHHrw.
        destruct (edge_eq_dec (mk_edge u v0) (0%nat, r)) as [Heq | Hne].
        - unfold mk_edge in Heq. destruct (Nat.ltb_spec u v0); inversion Heq; subst.
          + right; apply reach_refl.
          + left; apply reach_refl.
        - assert (He' : has_edge T' u v0).
          { apply (wf_has_edge_mk (S k) T u v0 HwfT) in H.
            apply (wf_has_edge_mk (S k) T' u v0 HwfT').
            apply remove_edge_in. split; assumption. }
          destruct Hstart as [H0u | Hru];
            [left; eapply reachable_trans; [exact H0u | eapply reach_step; [exact He' | apply reach_refl]] |
             right; eapply reachable_trans; [exact Hru | eapply reach_step; [exact He' | apply reach_refl]]]. }
      apply (Hstep 0%nat v (HreachT v Hv)). left; apply reach_refl.
  Qed.

  (* =======================================================================
     3. Join and Split Maps for the Vertex-1 Tree Bijection
     ======================================================================= *)

  Definition embed_edges (pos : list nat) (H : list (nat * nat)) : list (nat * nat) :=
    map (fun e => (nth (fst e) pos 0%nat, nth (snd e) pos 0%nat)) H.

  Definition project_edges (pos : list nat) (E_sub T' : list (nat * nat)) : list (nat * nat) :=
    filter (fun e => edge_mem (nth (fst e) pos 0%nat, nth (snd e) pos 0%nat) T') E_sub.

  Definition join_tree (E : list (nat * nat)) (mask : list bool) (idx : nat)
    (TA TB : list (nat * nat)) : list (nat * nat) :=
    let r := nth idx (pos_A mask) 0%nat in
    let comb := (0%nat, r) :: embed_edges (pos_A mask) TA ++ embed_edges (pos_B0 mask) TB in
    filter (fun e => edge_mem e comb) E.

  Definition mask_of_tree (k : nat) (T' : list (nat * nat)) : list bool :=
    map (fun i => negb (existsb (Nat.eqb (S i)) (expand_iter (S k) T' [0%nat]))) (seq 0%nat k).

  Lemma mask_of_tree_nth : forall k T' i,
    (i < k)%nat ->
    nth i (mask_of_tree k T') false =
    negb (existsb (Nat.eqb (S i)) (expand_iter (S k) T' [0%nat])).
  Proof.
    intros k T' i Hi. unfold mask_of_tree.
    set (f := fun j => negb (existsb (Nat.eqb (S j)) (expand_iter (S k) T' [0%nat]))).
    rewrite (nth_indep _ false (f 0%nat)) by (rewrite map_length, seq_length; exact Hi).
    rewrite map_nth, seq_nth by exact Hi. reflexivity.
  Qed.

  Definition split_tree {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P)
    (T : list (nat * nat)) : list bool * nat * list (nat * nat) * list (nat * nat) :=
    let k := length Y in
    let r := root_child_of_1 k T in
    let T' := remove_edge (0%nat, r) T in
    let mask := mask_of_tree k T' in
    let idx := index_of r (pos_A mask) in
    let TA := project_edges (pos_A mask) (graph_edges ob (select_true mask Y)) T' in
    let TB := project_edges (pos_B0 mask) (graph_edges ob (p0 :: select_false mask Y)) T' in
    (mask, idx, TA, TB).

  Definition valid_roots {P : Type} (ob : P -> P -> bool) (p0 : P) (Y_A : list P) : list nat :=
    filter (fun idx => match nth_error Y_A idx with Some q => ob p0 q | None => false end)
           (seq 0%nat (length Y_A)).

  Definition valid_quads {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P)
    : list (list bool * nat * list (nat * nat) * list (nat * nat)) :=
    flat_map (fun mask =>
      let Y_A := select_true mask Y in
      let Y_B := select_false mask Y in
      let treesA := spanning_trees (length Y_A) (graph_edges ob Y_A) in
      let treesB := spanning_trees (length (p0 :: Y_B)) (graph_edges ob (p0 :: Y_B)) in
      flat_map (fun idx =>
        flat_map (fun TA =>
          map (fun TB => (mask, idx, TA, TB)) treesB) treesA)
        (valid_roots ob p0 Y_A))
      (masks_head_true (length Y)).

  (* Helper: length of flat_map *)
  Lemma length_flat_map : forall {A B : Type} (f : A -> list B) (l : list A),
    length (flat_map f l) = fold_right Nat.add 0%nat (map (fun x => length (f x)) l).
  Proof.
    induction l as [| a xs IH]; simpl; [reflexivity | rewrite app_length, IH; reflexivity].
  Qed.

  Lemma fold_right_add_const : forall {A : Type} (c : nat) (l : list A),
    fold_right Nat.add 0%nat (map (fun _ => c) l) = (length l * c)%nat.
  Proof.
    induction l as [| a xs IH]; simpl; [reflexivity | rewrite IH; lia].
  Qed.

  Lemma valid_quads_length : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P),
    length (valid_quads ob p0 Y) =
    fold_right Nat.add 0%nat
      (map (fun mask =>
        (length (valid_roots ob p0 (select_true mask Y)) *
         tree_count ob (select_true mask Y) *
         tree_count ob (p0 :: select_false mask Y))%nat)
        (masks_head_true (length Y))).
  Proof.
    intros P ob p0 Y. unfold valid_quads, tree_count.
    rewrite length_flat_map. f_equal. apply map_ext. intro mask.
    rewrite length_flat_map.
    transitivity (fold_right Nat.add 0%nat
      (map (fun _ =>
        (length (spanning_trees (length (select_true mask Y)) (graph_edges ob (select_true mask Y))) *
         length (spanning_trees (length (p0 :: select_false mask Y)) (graph_edges ob (p0 :: select_false mask Y))))%nat)
        (valid_roots ob p0 (select_true mask Y)))).
    - f_equal. apply map_ext. intro idx.
      rewrite length_flat_map.
      transitivity (fold_right Nat.add 0%nat
        (map (fun _ => length (spanning_trees (length (p0 :: select_false mask Y)) (graph_edges ob (p0 :: select_false mask Y))))
          (spanning_trees (length (select_true mask Y)) (graph_edges ob (select_true mask Y))))).
      + f_equal. apply map_ext. intro TA. apply map_length.
      + apply fold_right_add_const.
    - rewrite fold_right_add_const. lia.
  Qed.

  Lemma valid_quads_in : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P) mask idx TA TB,
    (1 <= length Y)%nat ->
    In (mask, idx, TA, TB) (valid_quads ob p0 Y) <->
    length mask = length Y /\ nth 0%nat mask false = true /\
    (idx < count_true mask)%nat /\
    (exists q, nth_error (select_true mask Y) idx = Some q /\ ob p0 q = true) /\
    In TA (spanning_trees (count_true mask) (graph_edges ob (select_true mask Y))) /\
    In TB (spanning_trees (S (length Y - count_true mask)) (graph_edges ob (p0 :: select_false mask Y))).
  Proof.
    intros P ob p0 Y mask idx TA TB Hk.
    unfold valid_quads. rewrite in_flat_map. split.
    - intros [m [Hm Hin1]].
      apply masks_head_true_in in Hm; [| exact Hk]. destruct Hm as [Hmlen Hm0].
      rewrite in_flat_map in Hin1. destruct Hin1 as [i [Hi Hin2]].
      rewrite in_flat_map in Hin2. destruct Hin2 as [tA [HtA Hin3]].
      rewrite in_map_iff in Hin3. destruct Hin3 as [tB [Heq HtB]].
      inversion Heq; subst m i tA tB.
      unfold valid_roots in Hi. rewrite filter_In, in_seq in Hi.
      destruct Hi as [Hilt Hob].
      rewrite (select_true_length mask Y Hmlen) in *.
      simpl length in HtB. rewrite (select_false_length mask Y Hmlen), Hmlen in HtB.
      repeat split; try assumption; try lia.
      destruct (nth_error (select_true mask Y) idx) as [q |] eqn:Eq; [exists q; split; [reflexivity | exact Hob] | discriminate].
    - intros [Hmlen [Hm0 [Hidx [[q [Hq Hob]] [HTA HTB]]]]].
      exists mask. split; [apply masks_head_true_in; [exact Hk | split; assumption] |].
      rewrite in_flat_map. exists idx. split.
      + unfold valid_roots. apply filter_In. rewrite in_seq, (select_true_length mask Y Hmlen).
        rewrite Hq. split; [lia | exact Hob].
      + rewrite in_flat_map. exists TA. split.
        * rewrite (select_true_length mask Y Hmlen). exact HTA.
        * rewrite in_map_iff. exists TB. split; [reflexivity |].
          simpl length. rewrite (select_false_length mask Y Hmlen), Hmlen. exact HTB.
  Qed.

  Lemma NoDup_flat_map_local : forall {A B : Type} (f : A -> list B) (l : list A),
    NoDup l ->
    (forall x, In x l -> NoDup (f x)) ->
    (forall x y b, In x l -> In y l -> In b (f x) -> In b (f y) -> x = y) ->
    NoDup (flat_map f l).
  Proof.
    induction l as [| a xs IH]; intros Hnd Hall Hdisj; simpl; [constructor |].
    inversion Hnd as [| ? ? Hnot Hnd']; subst.
    apply NoDup_app_local.
    - apply Hall; left; reflexivity.
    - apply IH; [exact Hnd' | intros x Hx; apply Hall; right; exact Hx |].
      intros x y b Hx Hy Hbx Hby. apply (Hdisj x y b); try (right; assumption); assumption.
    - intros b Hba Hbxs. apply in_flat_map in Hbxs. destruct Hbxs as [y [Hy Hby]].
      assert (a = y) by (apply (Hdisj a y b); [left; reflexivity | right; exact Hy | exact Hba | exact Hby]).
      subst y. contradiction.
  Qed.

  Lemma valid_quads_NoDup : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P),
    NoDup (valid_quads ob p0 Y).
  Proof.
    intros P ob p0 Y. unfold valid_quads.
    apply NoDup_flat_map_local; [apply masks_head_true_NoDup | |].
    - intros mask _.
      apply NoDup_flat_map_local; [apply NoDup_filter, seq_NoDup | |].
      + intros idx _.
        apply NoDup_flat_map_local.
        * apply NoDup_filter, sublists_NoDup_list, (proj1 (graph_edges_wf ob _)).
        * intros TA _.
          apply NoDup_map_in.
          -- apply NoDup_filter, sublists_NoDup_list, (proj1 (graph_edges_wf ob _)).
          -- intros t1 t2 _ _ H. inversion H. reflexivity.
        * intros t1 t2 [[[m i] a] b] _ _ H1 H2.
          apply in_map_iff in H1; apply in_map_iff in H2.
          destruct H1 as [? [E1 _]]; destruct H2 as [? [E2 _]].
          inversion E1; inversion E2; congruence.
      + intros i1 i2 [[[m i] a] b] _ _ H1 H2.
        apply in_flat_map in H1; destruct H1 as [? [_ H1]]; apply in_map_iff in H1; destruct H1 as [? [E1 _]].
        apply in_flat_map in H2; destruct H2 as [? [_ H2]]; apply in_map_iff in H2; destruct H2 as [? [E2 _]].
        inversion E1; inversion E2; congruence.
    - intros m1 m2 [[[m i] a] b] _ _ H1 H2.
      apply in_flat_map in H1; destruct H1 as [? [_ H1]]; apply in_flat_map in H1; destruct H1 as [? [_ H1]];
        apply in_map_iff in H1; destruct H1 as [? [E1 _]].
      apply in_flat_map in H2; destruct H2 as [? [_ H2]]; apply in_flat_map in H2; destruct H2 as [? [_ H2]];
        apply in_map_iff in H2; destruct H2 as [? [E2 _]].
      inversion E1; inversion E2; congruence.
  Qed.

  (* Helper: embed_edges maps E_A into E and E_B into E *)
  Lemma embed_A_in_E : forall {P : Type} (ob : P -> P -> bool) (p0 : P) mask (Y : list P) e,
    length mask = length Y ->
    In e (graph_edges ob (select_true mask Y)) ->
    In (nth (fst e) (pos_A mask) 0%nat, nth (snd e) (pos_A mask) 0%nat) (graph_edges ob (p0 :: Y)).
  Proof.
    intros P ob p0 mask Y [u v] Hmlen Hin.
    apply graph_edges_in in Hin. destruct Hin as [Huv [Hvlen [x [y [Hx [Hy Hob]]]]]].
    rewrite (select_true_length mask Y Hmlen) in Hvlen.
    simpl fst; simpl snd.
    apply graph_edges_in.
    assert (Hlt1 : (nth u (pos_A mask) 0%nat < nth v (pos_A mask) 0%nat)%nat).
    { apply pos_A_strict_mono; [exact Huv | rewrite pos_A_length; exact Hvlen]. }
    assert (Hlt2 : (nth v (pos_A mask) 0%nat < length (p0 :: Y))%nat).
    { pose proof (pos_A_in mask (nth v (pos_A mask) 0%nat)) as Hpin.
      destruct (proj1 Hpin (nth_In _ 0%nat ltac:(rewrite pos_A_length; exact Hvlen))) as [_ [Hle _]].
      simpl; lia. }
    repeat split; [exact Hlt1 | exact Hlt2 |].
    exists x, y.
    rewrite <- (select_true_nth_error p0 mask Y u Hmlen ltac:(lia)).
    rewrite <- (select_true_nth_error p0 mask Y v Hmlen Hvlen).
    repeat split; assumption.
  Qed.

  Lemma embed_B0_in_E : forall {P : Type} (ob : P -> P -> bool) (p0 : P) mask (Y : list P) e,
    length mask = length Y ->
    In e (graph_edges ob (p0 :: select_false mask Y)) ->
    In (nth (fst e) (pos_B0 mask) 0%nat, nth (snd e) (pos_B0 mask) 0%nat) (graph_edges ob (p0 :: Y)).
  Proof.
    intros P ob p0 mask Y [u v] Hmlen Hin.
    apply graph_edges_in in Hin. destruct Hin as [Huv [Hvlen [x [y [Hx [Hy Hob]]]]]].
    simpl length in Hvlen. rewrite (select_false_length mask Y Hmlen) in Hvlen.
    simpl fst; simpl snd.
    apply graph_edges_in.
    assert (Hlt1 : (nth u (pos_B0 mask) 0%nat < nth v (pos_B0 mask) 0%nat)%nat).
    { apply pos_B0_strict_mono; [exact Huv | rewrite pos_B0_length; exact Hvlen]. }
    assert (Hlt2 : (nth v (pos_B0 mask) 0%nat < length (p0 :: Y))%nat).
    { pose proof (pos_B0_in mask (nth v (pos_B0 mask) 0%nat)) as Hpin.
      destruct (proj1 Hpin (nth_In _ 0%nat ltac:(rewrite pos_B0_length; exact Hvlen))) as [H0 | [_ [Hle _]]];
        cbn [length]; lia. }
    repeat split; [exact Hlt1 | exact Hlt2 |].
    exists x, y.
    rewrite <- (select_false_nth_error p0 mask Y u Hmlen ltac:(lia)).
    rewrite <- (select_false_nth_error p0 mask Y v Hmlen Hvlen).
    repeat split; assumption.
  Qed.

  Lemma embed_edges_in_pos : forall pos H u v,
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < length pos)%nat) H ->
    In (u, v) (embed_edges pos H) -> In u pos /\ In v pos.
  Proof.
    intros pos H u v Hfor Hin. unfold embed_edges in Hin.
    apply in_map_iff in Hin. destruct Hin as [[a b] [Heq Hab]].
    rewrite Forall_forall in Hfor. pose proof (Hfor (a, b) Hab) as L. simpl in L.
    injection Heq as Eu Ev.
    split; [rewrite <- Eu | rewrite <- Ev]; apply nth_In; lia.
  Qed.

  Lemma embed_edges_in_inv : forall pos H u v,
    (forall i j, (i < length pos)%nat -> (j < length pos)%nat ->
       nth i pos 0%nat = nth j pos 0%nat -> i = j) ->
    Forall (fun e => (fst e < snd e)%nat /\ (snd e < length pos)%nat) H ->
    (u < length pos)%nat -> (v < length pos)%nat ->
    In (nth u pos 0%nat, nth v pos 0%nat) (embed_edges pos H) ->
    In (u, v) H.
  Proof.
    intros pos H u v Hinj Hfor Hu Hv Hin. unfold embed_edges in Hin.
    apply in_map_iff in Hin. destruct Hin as [[a b] [Heq Hab]].
    rewrite Forall_forall in Hfor. pose proof (Hfor (a, b) Hab) as L. simpl in L.
    injection Heq as Eu Ev.
    assert (a = u) by (apply Hinj; [lia | exact Hu | exact Eu]).
    assert (b = v) by (apply Hinj; [lia | exact Hv | exact Ev]).
    subst; exact Hab.
  Qed.

  Lemma join_tree_in_spanning : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P) mask idx TA TB,
    (1 <= length Y)%nat ->
    In (mask, idx, TA, TB) (valid_quads ob p0 Y) ->
    In (join_tree (graph_edges ob (p0 :: Y)) mask idx TA TB)
       (spanning_trees (S (length Y)) (graph_edges ob (p0 :: Y))).
  Proof.
    intros P ob p0 Y mask idx TA TB Hk Hq.
    apply valid_quads_in in Hq; [| exact Hk].
    destruct Hq as [Hmlen [Hm0 [Hidx [[q [Hq Hob]] [HTA HTB]]]]].
    set (E := graph_edges ob (p0 :: Y)).
    set (r := nth idx (pos_A mask) 0%nat).
    set (comb := (0%nat, r) :: embed_edges (pos_A mask) TA ++ embed_edges (pos_B0 mask) TB).
    set (T := join_tree E mask idx TA TB).
    pose proof (graph_edges_wf ob (p0 :: Y)) as HwfE. simpl length in HwfE.
    pose proof (graph_edges_wf ob (select_true mask Y)) as HwfEA.
    rewrite (select_true_length mask Y Hmlen) in HwfEA.
    pose proof (graph_edges_wf ob (p0 :: select_false mask Y)) as HwfEB.
    simpl length in HwfEB. rewrite (select_false_length mask Y Hmlen) in HwfEB.
    unfold spanning_trees in HTA, HTB. apply filter_In in HTA; apply filter_In in HTB.
    destruct HTA as [HsubA HtrA]; destruct HTB as [HsubB HtrB].
    unfold is_treeb in HtrA, HtrB. rewrite !andb_true_iff, !Nat.eqb_eq in HtrA, HtrB.
    destruct HtrA as [HconnA HlenA]; destruct HtrB as [HconnB HlenB].
    (* Every edge in comb belongs to E *)
    assert (Hr_in : In r (pos_A mask)) by (unfold r; apply nth_In; rewrite pos_A_length; exact Hidx).
    assert (Hr_bounds : (1 <= r <= length Y)%nat).
    { apply pos_A_in in Hr_in. lia. }
    assert (H0r_in_E : In (0%nat, r) E).
    { unfold E. apply graph_edges_in. repeat split; [lia | simpl; lia |].
      exists p0, q. unfold r.
      rewrite <- (select_true_nth_error p0 mask Y idx Hmlen Hidx).
      split; [reflexivity | split; [exact Hq | exact Hob]]. }
    assert (Hcomb_in_E : incl comb E).
    { intros e He. unfold comb in He. simpl in He.
      destruct He as [<- | He]; [exact H0r_in_E |].
      apply in_app_iff in He. destruct He as [He | He].
      - unfold embed_edges in He. apply in_map_iff in He. destruct He as [eA [<- HeA]].
        apply (embed_A_in_E ob p0 mask Y eA Hmlen). exact (sublists_incl _ TA HsubA _ HeA).
      - unfold embed_edges in He. apply in_map_iff in He. destruct He as [eB [<- HeB]].
        apply (embed_B0_in_E ob p0 mask Y eB Hmlen). exact (sublists_incl _ TB HsubB _ HeB). }
    assert (HT_iff : forall e, In e T <-> In e comb).
    { intro e. unfold T, join_tree. fold r comb. rewrite filter_In, edge_mem_iff.
      split; [intros [_ H]; exact H | intro H; split; [apply Hcomb_in_E; exact H | exact H]]. }
    (* NoDup comb -> length T = length comb = length Y *)
    assert (Hnd_embA : NoDup (embed_edges (pos_A mask) TA)).
    { apply NoDup_map_in; [exact (sublists_NoDup_elem _ TA (proj1 HwfEA) HsubA) |].
      intros [u1 v1] [u2 v2] H1 H2 Heq.
      pose proof (sublists_Forall _ _ TA (proj2 HwfEA) HsubA) as HforA.
      rewrite Forall_forall in HforA.
      pose proof (HforA (u1, v1) H1) as L1; pose proof (HforA (u2, v2) H2) as L2. simpl in L1, L2.
      injection Heq as E1 E2.
      f_equal; apply (pos_A_inj mask); try (rewrite pos_A_length; lia); assumption. }
    assert (Hnd_embB : NoDup (embed_edges (pos_B0 mask) TB)).
    { apply NoDup_map_in; [exact (sublists_NoDup_elem _ TB (proj1 HwfEB) HsubB) |].
      intros [u1 v1] [u2 v2] H1 H2 Heq.
      pose proof (sublists_Forall _ _ TB (proj2 HwfEB) HsubB) as HforB.
      rewrite Forall_forall in HforB.
      pose proof (HforB (u1, v1) H1) as L1; pose proof (HforB (u2, v2) H2) as L2. simpl in L1, L2.
      injection Heq as E1 E2.
      f_equal; apply (pos_B0_inj mask); try (rewrite pos_B0_length; lia); assumption. }
    assert (HforA_pos : Forall (fun e => (fst e < snd e)%nat /\ (snd e < length (pos_A mask))%nat) TA).
    { rewrite pos_A_length. exact (sublists_Forall _ _ TA (proj2 HwfEA) HsubA). }
    assert (HforB_pos : Forall (fun e => (fst e < snd e)%nat /\ (snd e < length (pos_B0 mask))%nat) TB).
    { rewrite pos_B0_length. exact (sublists_Forall _ _ TB (proj2 HwfEB) HsubB). }
    assert (Hnd_comb : NoDup comb).
    { unfold comb. constructor.
      - intro Hin. apply in_app_iff in Hin. destruct Hin as [Hin | Hin].
        + destruct (embed_edges_in_pos _ _ _ _ HforA_pos Hin) as [H0A _].
          apply pos_A_in in H0A. lia.
        + destruct (embed_edges_in_pos _ _ _ _ HforB_pos Hin) as [_ HrB].
          exact (pos_A_B0_disjoint mask r Hr_in HrB).
      - apply NoDup_app_local; [exact Hnd_embA | exact Hnd_embB |].
        intros [u v] H1 H2.
        destruct (embed_edges_in_pos _ _ _ _ HforA_pos H1) as [HuA _].
        destruct (embed_edges_in_pos _ _ _ _ HforB_pos H2) as [HuB _].
        exact (pos_A_B0_disjoint mask u HuA HuB). }
    assert (Hlen_T : length T = length Y).
    { assert (HndT : NoDup T) by (apply NoDup_filter; exact (proj1 HwfE)).
      assert (Hperm : Permutation T comb) by (apply NoDup_Permutation; assumption).
      rewrite (Permutation_length Hperm). unfold comb. simpl length.
      rewrite app_length; unfold embed_edges; rewrite !map_length, HlenA, HlenB.
      pose proof (count_true_le mask). lia. }
    (* Connectedness of T *)
    assert (Hconn_T : is_connectedb (S (length Y)) T = true).
    { pose proof (sublists_Forall _ E T (proj2 HwfE) (filter_in_sublists _ E)) as HwfT.
      apply (is_connectedb_iff (S (length Y)) T HwfT). split; [lia |].
      pose proof (sublists_Forall _ _ TA (proj2 HwfEA) HsubA) as HforA.
      pose proof (sublists_Forall _ _ TB (proj2 HwfEB) HsubB) as HforB.
      apply (is_connectedb_iff _ _ HforA) in HconnA. destruct HconnA as [_ HreachA].
      rewrite <- Hmlen in HconnB.
      apply (is_connectedb_iff _ _ HforB) in HconnB. destruct HconnB as [_ HreachB].
      assert (HliftA : forall u v, (u < count_true mask)%nat -> reachable TA u v ->
        reachable T (nth u (pos_A mask) 0%nat) (nth v (pos_A mask) 0%nat)).
      { intros u v Hu HrA. induction HrA; [apply reach_refl |].
        pose proof (wf_has_edge_lt _ _ u v HforA H) as [_ [Hv _]].
        eapply reach_step; [| exact (IHHrA Hv)].
        destruct H as [Ha | Hb]; [left | right]; apply HT_iff; unfold comb; right; apply in_app_iff; left;
          unfold embed_edges; [apply (in_map (fun e => (nth (fst e) (pos_A mask) 0%nat, nth (snd e) (pos_A mask) 0%nat)) _ (u, v) Ha) |
                               apply (in_map (fun e => (nth (fst e) (pos_A mask) 0%nat, nth (snd e) (pos_A mask) 0%nat)) _ (v, u) Hb)]. }
      assert (HliftB : forall u v, (u < S (length mask - count_true mask))%nat -> reachable TB u v ->
        reachable T (nth u (pos_B0 mask) 0%nat) (nth v (pos_B0 mask) 0%nat)).
      { intros u v Hu HrB. induction HrB; [apply reach_refl |].
        pose proof (wf_has_edge_lt _ _ u v HforB H) as [_ [Hv _]].
        eapply reach_step; [| apply IHHrB; lia].
        destruct H as [Ha | Hb]; [left | right]; apply HT_iff; unfold comb; right; apply in_app_iff; right;
          unfold embed_edges; [apply (in_map (fun e => (nth (fst e) (pos_B0 mask) 0%nat, nth (snd e) (pos_B0 mask) 0%nat)) _ (u, v) Ha) |
                               apply (in_map (fun e => (nth (fst e) (pos_B0 mask) 0%nat, nth (snd e) (pos_B0 mask) 0%nat)) _ (v, u) Hb)]. }
      intros v Hv.
      destruct (pos_A_B0_cover mask v ltac:(lia)) as [HvA | HvB].
      - destruct (index_of_spec v (pos_A mask) HvA) as [Hiv Hnv].
        rewrite pos_A_length in Hiv.
        assert (H0r : reachable T 0%nat r).
        { eapply reach_step; [left; apply HT_iff; left; reflexivity | apply reach_refl]. }
        assert (Hr_to_v : reachable T r v).
        { unfold r. rewrite <- Hnv.
          assert (Hidx_v : reachable TA idx (index_of v (pos_A mask))).
          { eapply reachable_trans; [apply reachable_sym; apply HreachA; exact Hidx | apply HreachA; exact Hiv]. }
          exact (HliftA idx (index_of v (pos_A mask)) Hidx Hidx_v). }
        eapply reachable_trans; [exact H0r | exact Hr_to_v].
      - destruct (index_of_spec v (pos_B0 mask) HvB) as [Hiv Hnv].
        rewrite pos_B0_length in Hiv.
        rewrite <- Hnv.
        change 0%nat with (nth 0%nat (pos_B0 mask) 0%nat).
        apply (HliftB 0%nat (index_of v (pos_B0 mask)) ltac:(lia)).
        apply HreachB. lia. }
    unfold spanning_trees. apply filter_In. split.
    - unfold T, join_tree. apply filter_in_sublists.
    - unfold is_treeb. rewrite andb_true_iff, Nat.eqb_eq. split; [exact Hconn_T | lia].
  Qed.

  (* Helper: In split_tree, both TA and TB are valid spanning trees *)
  Lemma split_tree_in_quads : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P) T,
    (1 <= length Y)%nat ->
    In T (spanning_trees (S (length Y)) (graph_edges ob (p0 :: Y))) ->
    In (split_tree ob p0 Y T) (valid_quads ob p0 Y).
  Proof.
    intros P ob p0 Y T Hk HinT.
    set (k := length Y).
    set (E := graph_edges ob (p0 :: Y)).
    pose proof (graph_edges_wf ob (p0 :: Y)) as HwfE. simpl length in HwfE.
    pose proof HinT as HinT'.
    unfold spanning_trees in HinT'. apply filter_In in HinT'.
    destruct HinT' as [HinSubT HtreeT].
    unfold is_treeb in HtreeT. rewrite andb_true_iff, Nat.eqb_eq in HtreeT.
    destruct HtreeT as [HconnT HlenT].
    pose proof (sublists_Forall _ E T (proj2 HwfE) HinSubT) as HwfT.
    pose proof (sublists_NoDup_elem E T (proj1 HwfE) HinSubT) as HndT.
    set (r := root_child_of_1 k T).
    pose proof (root_child_of_1_spec k T Hk HwfT HconnT) as [Hr [Hin0r Hra1]].
    fold r in Hr, Hin0r, Hra1.
    set (T' := remove_edge (0%nat, r) T).
    pose proof (tree_cut_partition k E T r Hk HwfE HinT Hin0r) as [Hnot0r Hpart].
    fold T' in Hnot0r, Hpart.
    pose proof (remove_edge_in_sublists E T (0%nat, r) HinSubT) as HinSub'.
    pose proof (sublists_Forall _ E T' (proj2 HwfE) HinSub') as HwfT'.
    pose proof (remove_edge_length (0%nat, r) T HndT Hin0r) as HlenT'.
    fold T' in HlenT'.
    set (mask := mask_of_tree k T').
    assert (Hmlen : length mask = k) by (unfold mask, mask_of_tree; rewrite map_length, seq_length; reflexivity).
    assert (Hmask_nth : forall i, (i < k)%nat ->
      nth i mask false = true <-> ~ reachable T' 0%nat (S i)).
    { intros i Hi. unfold mask. rewrite (mask_of_tree_nth k T' i Hi).
      rewrite negb_true_iff.
      destruct (existsb (Nat.eqb (S i)) (expand_iter (S k) T' [0%nat])) eqn:Ex.
      - split; [discriminate |].
        intro Hnot. apply expand_iter_0_iff in Ex.
        exfalso. apply Hnot. exact (reachable_k_to_reachable T' (S k) 0%nat (S i) Ex).
      - split; [intros _ Hreach | intros _; reflexivity].
        pose proof (reachable_bounded_length (S k) T' 0%nat (S i) HwfT' ltac:(lia) Hreach) as Hrk.
        assert (Hrk' : reachable_k T' (S k) 0%nat (S i)) by (eapply reachable_k_mono; [| exact Hrk]; lia).
        apply expand_iter_0_iff in Hrk'. congruence. }
    assert (HposA_iff : forall v, (v < S k)%nat ->
      In v (pos_A mask) <-> reachable T' r v).
    { intros v Hv. rewrite pos_A_in. rewrite Hmlen. split.
      - intros [H1 [H2 H3]].
        apply (Hmask_nth (v - 1)%nat ltac:(lia)) in H3.
        replace (S (v - 1)) with v in H3 by lia.
        destruct (Hpart v Hv); [contradiction | assumption].
      - intro Hrv.
        assert (Hnot0v : ~ reachable T' 0%nat v).
        { intro H0v. apply Hnot0r. eapply reachable_trans; [exact H0v | apply reachable_sym; exact Hrv]. }
        assert (Hvne0 : v <> 0%nat) by (intro Heq; subst; apply Hnot0v; apply reach_refl).
        repeat split; try lia.
        apply (Hmask_nth (v - 1)%nat ltac:(lia)). replace (S (v - 1)) with v by lia. exact Hnot0v. }
    assert (HposB_iff : forall v, (v < S k)%nat ->
      In v (pos_B0 mask) <-> reachable T' 0%nat v).
    { intros v Hv. split.
      - intro HB. destruct (Hpart v Hv) as [H0v | Hrv]; [exact H0v |].
        exfalso. apply (pos_A_B0_disjoint mask v); [apply (HposA_iff v Hv); exact Hrv | exact HB].
      - intro H0v. destruct (pos_A_B0_cover mask v ltac:(lia)) as [HA | HB]; [| exact HB].
        exfalso. apply (HposA_iff v Hv) in HA.
        apply Hnot0r. eapply reachable_trans; [exact H0v | apply reachable_sym; exact HA]. }
    assert (Hm0 : nth 0%nat mask false = true).
    { apply (Hmask_nth 0%nat ltac:(lia)).
      intro H01. apply Hnot0r.
      eapply reachable_trans; [exact H01 | apply reachable_sym; apply reachable_avoid0_to_remove; exact Hra1]. }
    assert (Hr_inA : In r (pos_A mask)) by (apply (HposA_iff r ltac:(lia)); apply reach_refl).
    destruct (index_of_spec r (pos_A mask) Hr_inA) as [Hidx Hnr].
    rewrite pos_A_length in Hidx.
    set (idx := index_of r (pos_A mask)). fold idx in Hidx, Hnr.
    set (EA := graph_edges ob (select_true mask Y)).
    set (EB := graph_edges ob (p0 :: select_false mask Y)).
    set (TA := project_edges (pos_A mask) EA T').
    set (TB := project_edges (pos_B0 mask) EB T').
    pose proof (graph_edges_wf ob (select_true mask Y)) as HwfEA.
    rewrite (select_true_length mask Y Hmlen) in HwfEA.
    pose proof (graph_edges_wf ob (p0 :: select_false mask Y)) as HwfEB.
    simpl length in HwfEB. rewrite (select_false_length mask Y Hmlen) in HwfEB.
    (* Every edge of T' belongs to either embed(TA) or embed(TB) *)
    assert (HT'_split : forall e, In e T' ->
      In e (embed_edges (pos_A mask) TA) \/ In e (embed_edges (pos_B0 mask) TB)).
    { intros [u v] He.
      rewrite Forall_forall in HwfT'. pose proof (HwfT' (u, v) He) as Huv. simpl in Huv.
      destruct (Hpart u ltac:(lia)) as [H0u | Hru].
      - right.
        assert (H0v : reachable T' 0%nat v).
        { eapply reachable_trans; [exact H0u | eapply reach_step; [left; exact He | apply reach_refl]]. }
        assert (HuB : In u (pos_B0 mask)) by (apply (HposB_iff u ltac:(lia)); exact H0u).
        assert (HvB : In v (pos_B0 mask)) by (apply (HposB_iff v ltac:(lia)); exact H0v).
        destruct (index_of_spec u (pos_B0 mask) HuB) as [Hiu Hnu].
        destruct (index_of_spec v (pos_B0 mask) HvB) as [Hiv Hnv].
        rewrite pos_B0_length in Hiu, Hiv.
        assert (Hiuv : (index_of u (pos_B0 mask) < index_of v (pos_B0 mask))%nat).
        { destruct (lt_eq_lt_dec (index_of u (pos_B0 mask)) (index_of v (pos_B0 mask))) as [[Hlt | Heq] | Hgt];
            [exact Hlt | rewrite <- Hnu, <- Hnv, Heq in Huv; lia |].
          pose proof (pos_B0_strict_mono mask _ _ Hgt ltac:(rewrite pos_B0_length; exact Hiu)). lia. }
        assert (HinEB : In (index_of u (pos_B0 mask), index_of v (pos_B0 mask)) EB).
        { unfold EB. apply graph_edges_in.
          simpl length; rewrite (select_false_length mask Y Hmlen).
          assert (HinE : In (u, v) E) by (exact (sublists_incl E T' HinSub' _ He)).
          apply graph_edges_in in HinE. destruct HinE as [_ [_ [x [y [Hx [Hy Hob]]]]]].
          repeat split; [exact Hiuv | exact Hiv |].
          exists x, y.
          rewrite (select_false_nth_error p0 mask Y _ Hmlen Hiu), Hnu.
          rewrite (select_false_nth_error p0 mask Y _ Hmlen Hiv), Hnv.
          repeat split; assumption. }
        unfold embed_edges. apply in_map_iff.
        exists (index_of u (pos_B0 mask), index_of v (pos_B0 mask)).
        cbv beta; cbn [fst snd].
        rewrite Hnu, Hnv. split; [reflexivity |].
        unfold TB, project_edges. apply filter_In. split; [exact HinEB |].
        cbv beta; cbn [fst snd]. rewrite Hnu, Hnv. apply edge_mem_iff. exact He.
      - left.
        assert (Hrv : reachable T' r v).
        { eapply reachable_trans; [exact Hru | eapply reach_step; [left; exact He | apply reach_refl]]. }
        assert (HuA : In u (pos_A mask)) by (apply (HposA_iff u ltac:(lia)); exact Hru).
        assert (HvA : In v (pos_A mask)) by (apply (HposA_iff v ltac:(lia)); exact Hrv).
        destruct (index_of_spec u (pos_A mask) HuA) as [Hiu Hnu].
        destruct (index_of_spec v (pos_A mask) HvA) as [Hiv Hnv].
        rewrite pos_A_length in Hiu, Hiv.
        assert (Hiuv : (index_of u (pos_A mask) < index_of v (pos_A mask))%nat).
        { destruct (lt_eq_lt_dec (index_of u (pos_A mask)) (index_of v (pos_A mask))) as [[Hlt | Heq] | Hgt];
            [exact Hlt | rewrite <- Hnu, <- Hnv, Heq in Huv; lia |].
          pose proof (pos_A_strict_mono mask _ _ Hgt ltac:(rewrite pos_A_length; exact Hiu)). lia. }
        assert (HinEA : In (index_of u (pos_A mask), index_of v (pos_A mask)) EA).
        { unfold EA. apply graph_edges_in.
          rewrite (select_true_length mask Y Hmlen).
          assert (HinE : In (u, v) E) by (exact (sublists_incl E T' HinSub' _ He)).
          apply graph_edges_in in HinE. destruct HinE as [_ [_ [x [y [Hx [Hy Hob]]]]]].
          repeat split; [exact Hiuv | exact Hiv |].
          exists x, y.
          rewrite (select_true_nth_error p0 mask Y _ Hmlen Hiu), Hnu.
          rewrite (select_true_nth_error p0 mask Y _ Hmlen Hiv), Hnv.
          repeat split; assumption. }
        unfold embed_edges. apply in_map_iff.
        exists (index_of u (pos_A mask), index_of v (pos_A mask)). simpl.
        rewrite Hnu, Hnv. split; [reflexivity |].
        unfold TA, project_edges. apply filter_In. split; [exact HinEA |].
        simpl. rewrite Hnu, Hnv. apply edge_mem_iff. exact He. }
    (* TA and TB are connected *)
    pose proof (sublists_Forall _ EA TA (proj2 HwfEA) (filter_in_sublists _ EA)) as HwfTA.
    pose proof (sublists_Forall _ EB TB (proj2 HwfEB) (filter_in_sublists _ EB)) as HwfTB.
    assert (HwfTA_len : Forall (fun e => (fst e < snd e)%nat /\ (snd e < length (pos_A mask))%nat) TA)
      by (rewrite pos_A_length; exact HwfTA).
    assert (HwfTB_len : Forall (fun e => (fst e < snd e)%nat /\ (snd e < length (pos_B0 mask))%nat) TB)
      by (rewrite pos_B0_length; exact HwfTB).
    rewrite Hmlen in HwfEB, HwfTB.
    assert (Hcount_pos : (1 <= count_true mask)%nat) by (destruct mask as [| [|] ?]; simpl in *; try discriminate; lia).
    assert (Hnd_posA : NoDup (pos_A mask)) by (apply strict_mono_NoDup, pos_A_strict_mono).
    assert (Hnd_posB : NoDup (pos_B0 mask)) by (apply strict_mono_NoDup, pos_B0_strict_mono).
    assert (HprojA_reach : forall u v, (u < S k)%nat -> reachable T' u v ->
      In u (pos_A mask) -> reachable TA (index_of u (pos_A mask)) (index_of v (pos_A mask))).
    { intros u v Hu Hr' HuA. induction Hr'; [apply reach_refl |].
      pose proof (wf_has_edge_lt (S k) T' u v HwfT' H) as [_ [Hv _]].
      assert (HvA : In v (pos_A mask)).
      { apply (HposA_iff v Hv). apply (HposA_iff u Hu) in HuA.
        eapply reachable_trans; [exact HuA | eapply reach_step; [exact H | apply reach_refl]]. }
      eapply reach_step; [| exact (IHHr' Hv HvA)].
      destruct (HT'_split (mk_edge u v) (proj1 (wf_has_edge_mk (S k) T' u v HwfT') H)) as [HinA | HinB].
      - destruct (index_of_spec u (pos_A mask) HuA) as [Hiu Hnu].
        destruct (index_of_spec v (pos_A mask) HvA) as [Hiv Hnv].
        unfold mk_edge in HinA. destruct (Nat.ltb_spec u v); [left | right];
          apply (embed_edges_in_inv (pos_A mask) TA _ _ (pos_A_inj mask) HwfTA_len);
          try assumption; rewrite Hnu, Hnv; exact HinA.
      - unfold mk_edge in HinB. destruct (Nat.ltb_spec u v);
          destruct (embed_edges_in_pos _ _ _ _ HwfTB_len HinB) as [H1 H2];
          exfalso; [exact (pos_A_B0_disjoint mask u HuA H1) | exact (pos_A_B0_disjoint mask u HuA H2)]. }
    assert (HprojB_reach : forall u v, (u < S k)%nat -> reachable T' u v ->
      In u (pos_B0 mask) -> reachable TB (index_of u (pos_B0 mask)) (index_of v (pos_B0 mask))).
    { intros u v Hu Hr' HuB. induction Hr'; [apply reach_refl |].
      pose proof (wf_has_edge_lt (S k) T' u v HwfT' H) as [_ [Hv _]].
      assert (HvB : In v (pos_B0 mask)).
      { apply (HposB_iff v Hv). apply (HposB_iff u Hu) in HuB.
        eapply reachable_trans; [exact HuB | eapply reach_step; [exact H | apply reach_refl]]. }
      eapply reach_step; [| exact (IHHr' Hv HvB)].
      destruct (HT'_split (mk_edge u v) (proj1 (wf_has_edge_mk (S k) T' u v HwfT') H)) as [HinA | HinB].
      - unfold mk_edge in HinA. destruct (Nat.ltb_spec u v);
          destruct (embed_edges_in_pos _ _ _ _ HwfTA_len HinA) as [H1 H2];
          exfalso; [exact (pos_A_B0_disjoint mask u H1 HuB) | exact (pos_A_B0_disjoint mask u H2 HuB)].
      - destruct (index_of_spec u (pos_B0 mask) HuB) as [Hiu Hnu].
        destruct (index_of_spec v (pos_B0 mask) HvB) as [Hiv Hnv].
        unfold mk_edge in HinB. destruct (Nat.ltb_spec u v); [left | right];
          apply (embed_edges_in_inv (pos_B0 mask) TB _ _ (pos_B0_inj mask) HwfTB_len);
          try assumption; rewrite Hnu, Hnv; exact HinB. }
    assert (HconnA : is_connectedb (count_true mask) TA = true).
    { apply (is_connectedb_iff _ TA HwfTA). split; [lia |].
      intros j Hj.
      set (u0 := nth 0%nat (pos_A mask) 0%nat).
      set (uj := nth j (pos_A mask) 0%nat).
      assert (Hu0_in : In u0 (pos_A mask)) by (unfold u0; apply nth_In; rewrite pos_A_length; lia).
      assert (Huj_in : In uj (pos_A mask)) by (unfold uj; apply nth_In; rewrite pos_A_length; lia).
      assert (Hu0_lt : (u0 < S k)%nat) by (apply pos_A_in in Hu0_in; lia).
      assert (Huj_lt : (uj < S k)%nat) by (apply pos_A_in in Huj_in; lia).
      assert (Hr_0j : reachable T' u0 uj).
      { eapply reachable_trans; [apply reachable_sym; apply (HposA_iff u0 Hu0_lt); exact Hu0_in |
                                 apply (HposA_iff uj Huj_lt); exact Huj_in]. }
      pose proof (HprojA_reach u0 uj Hu0_lt Hr_0j Hu0_in) as Hrj.
      unfold u0, uj in Hrj.
      rewrite !index_of_nth in Hrj; try exact Hnd_posA; try (rewrite pos_A_length; lia). exact Hrj. }
    assert (HconnB : is_connectedb (S (k - count_true mask)) TB = true).
    { apply (is_connectedb_iff _ TB HwfTB). split; [lia |].
      intros j Hj.
      set (uj := nth j (pos_B0 mask) 0%nat).
      assert (Huj_in : In uj (pos_B0 mask)) by (unfold uj; apply nth_In; rewrite pos_B0_length; lia).
      assert (Huj_lt : (uj < S k)%nat) by (apply pos_B0_in in Huj_in; destruct Huj_in; lia).
      assert (Hr_0j : reachable T' 0%nat uj) by (apply (HposB_iff uj Huj_lt); exact Huj_in).
      assert (H0B : In 0%nat (pos_B0 mask)) by (left; reflexivity).
      pose proof (HprojB_reach 0%nat uj ltac:(lia) Hr_0j H0B) as Hrj.
      unfold uj in Hrj.
      rewrite (index_of_nth (pos_B0 mask) j Hnd_posB ltac:(rewrite pos_B0_length; lia)) in Hrj.
      unfold pos_B0 in Hrj; simpl index_of in Hrj. exact Hrj. }
    (* Length equality via lower bounds + sum = length T' = k - 1 *)
    pose proof (connected_length_ge (count_true mask) EA TA HwfEA (filter_in_sublists _ EA) HconnA) as HgeA.
    pose proof (connected_length_ge (S (k - count_true mask)) EB TB HwfEB (filter_in_sublists _ EB) HconnB) as HgeB.
    assert (Hlen_sum : (length TA + length TB <= length T')%nat).
    { assert (Hnd_embA : NoDup (embed_edges (pos_A mask) TA)).
      { apply NoDup_map_in; [apply NoDup_filter; exact (proj1 HwfEA) |].
        intros [u1 v1] [u2 v2] H1 H2 Heq.
        rewrite Forall_forall in HwfTA.
        pose proof (HwfTA (u1, v1) H1) as L1; pose proof (HwfTA (u2, v2) H2) as L2; simpl in L1, L2.
        injection Heq as E1 E2. f_equal; apply (pos_A_inj mask); try (rewrite pos_A_length; lia); assumption. }
      assert (Hnd_embB : NoDup (embed_edges (pos_B0 mask) TB)).
      { apply NoDup_map_in; [apply NoDup_filter; exact (proj1 HwfEB) |].
        intros [u1 v1] [u2 v2] H1 H2 Heq.
        rewrite Forall_forall in HwfTB.
        pose proof (HwfTB (u1, v1) H1) as L1; pose proof (HwfTB (u2, v2) H2) as L2; simpl in L1, L2.
        injection Heq as E1 E2. f_equal; apply (pos_B0_inj mask); try (rewrite pos_B0_length; lia); assumption. }
      assert (Hnd_app : NoDup (embed_edges (pos_A mask) TA ++ embed_edges (pos_B0 mask) TB)).
      { apply NoDup_app_local; [exact Hnd_embA | exact Hnd_embB |].
        intros [u v] H1 H2.
        destruct (embed_edges_in_pos _ _ _ _ HwfTA_len H1) as [HuA _].
        destruct (embed_edges_in_pos _ _ _ _ HwfTB_len H2) as [HuB _].
        exact (pos_A_B0_disjoint mask u HuA HuB). }
      assert (Hincl : incl (embed_edges (pos_A mask) TA ++ embed_edges (pos_B0 mask) TB) T').
      { intros e He. apply in_app_iff in He. destruct He as [He | He];
          apply in_map_iff in He; destruct He as [e0 [<- He0]];
          unfold TA, TB, project_edges in He0; apply filter_In in He0;
          destruct He0 as [_ Hm]; apply edge_mem_iff in Hm; exact Hm. }
      pose proof (NoDup_incl_length Hnd_app Hincl) as Hle.
      rewrite app_length in Hle. unfold embed_edges in Hle. rewrite !map_length in Hle. exact Hle. }
    pose proof (count_true_le mask).
    assert (HlenA : length TA = (count_true mask - 1)%nat) by lia.
    assert (HlenB : length TB = (k - count_true mask)%nat) by lia.
    (* Check ob p0 q = true from In (0, r) E *)
    assert (Hob_r : exists q, nth_error (select_true mask Y) idx = Some q /\ ob p0 q = true).
    { assert (Hin0rE : In (0%nat, r) E) by (exact (sublists_incl E T HinSubT _ Hin0r)).
      apply graph_edges_in in Hin0rE. destruct Hin0rE as [_ [_ [x [y [Hx [Hy Hob]]]]]].
      simpl in Hx. inversion Hx; subst x.
      exists y. rewrite (select_true_nth_error p0 mask Y idx Hmlen Hidx), Hnr.
      split; assumption. }
    unfold split_tree. fold k r T' mask idx EA EB TA TB.
    apply valid_quads_in; [exact Hk |].
    repeat split; try assumption.
    - unfold spanning_trees. apply filter_In. split; [apply filter_in_sublists |].
      unfold is_treeb. rewrite andb_true_iff, Nat.eqb_eq. split; [exact HconnA | exact HlenA].
    - unfold spanning_trees. apply filter_In. split; [apply filter_in_sublists |].
      unfold is_treeb. rewrite andb_true_iff, Nat.eqb_eq. split; [exact HconnB | lia].
  Qed.

  (* Round-trip 1: join_tree (split_tree T) = T *)
  Lemma join_split_id : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P) T,
    (1 <= length Y)%nat ->
    In T (spanning_trees (S (length Y)) (graph_edges ob (p0 :: Y))) ->
    let '(mask, idx, TA, TB) := split_tree ob p0 Y T in
    join_tree (graph_edges ob (p0 :: Y)) mask idx TA TB = T.
  Proof.
    intros P ob p0 Y T Hk HinT.
    set (k := length Y).
    set (E := graph_edges ob (p0 :: Y)).
    pose proof (graph_edges_wf ob (p0 :: Y)) as HwfE. simpl length in HwfE.
    pose proof HinT as HinT'.
    unfold spanning_trees in HinT'. apply filter_In in HinT'.
    destruct HinT' as [HinSubT HtreeT].
    unfold is_treeb in HtreeT. rewrite andb_true_iff, Nat.eqb_eq in HtreeT.
    destruct HtreeT as [HconnT HlenT].
    pose proof (sublists_Forall _ E T (proj2 HwfE) HinSubT) as HwfT.
    set (r := root_child_of_1 k T).
    pose proof (root_child_of_1_spec k T Hk HwfT HconnT) as [Hr [Hin0r Hra1]].
    fold r in Hr, Hin0r, Hra1.
    set (T' := remove_edge (0%nat, r) T).
    pose proof (tree_cut_partition k E T r Hk HwfE HinT Hin0r) as [Hnot0r Hpart].
    fold T' in Hnot0r, Hpart.
    pose proof (remove_edge_in_sublists E T (0%nat, r) HinSubT) as HinSub'.
    pose proof (sublists_Forall _ E T' (proj2 HwfE) HinSub') as HwfT'.
    set (mask := mask_of_tree k T').
    assert (Hmlen : length mask = k) by (unfold mask, mask_of_tree; rewrite map_length, seq_length; reflexivity).
    assert (Hmask_nth : forall i, (i < k)%nat ->
      nth i mask false = true <-> ~ reachable T' 0%nat (S i)).
    { intros i Hi. unfold mask. rewrite (mask_of_tree_nth k T' i Hi).
      rewrite negb_true_iff.
      destruct (existsb (Nat.eqb (S i)) (expand_iter (S k) T' [0%nat])) eqn:Ex.
      - split; [discriminate | intro Hnot; apply expand_iter_0_iff in Ex; exfalso; apply Hnot; exact (reachable_k_to_reachable _ _ _ _ Ex)].
      - split; [intros _ Hreach | intros _; reflexivity].
        pose proof (reachable_bounded_length (S k) T' 0%nat (S i) HwfT' ltac:(lia) Hreach) as Hrk.
        assert (Hrk' : reachable_k T' (S k) 0%nat (S i)) by (eapply reachable_k_mono; [| exact Hrk]; lia).
        apply expand_iter_0_iff in Hrk'. congruence. }
    assert (HposA_iff : forall v, (v < S k)%nat -> In v (pos_A mask) <-> reachable T' r v).
    { intros v Hv. rewrite pos_A_in, Hmlen. split.
      - intros [H1 [H2 H3]]. apply (Hmask_nth (v - 1)%nat ltac:(lia)) in H3.
        replace (S (v - 1)) with v in H3 by lia. destruct (Hpart v Hv); [contradiction | assumption].
      - intro Hrv.
        assert (Hnot0v : ~ reachable T' 0%nat v) by (intro H0v; apply Hnot0r; eapply reachable_trans; [exact H0v | apply reachable_sym; exact Hrv]).
        assert (Hvne0 : v <> 0%nat) by (intro Heq; subst; apply Hnot0v; apply reach_refl).
        repeat split; try lia. apply (Hmask_nth (v - 1)%nat ltac:(lia)). replace (S (v - 1)) with v by lia. exact Hnot0v. }
    assert (HposB_iff : forall v, (v < S k)%nat -> In v (pos_B0 mask) <-> reachable T' 0%nat v).
    { intros v Hv. split.
      - intro HB. destruct (Hpart v Hv) as [H0v | Hrv]; [exact H0v |].
        exfalso. apply (pos_A_B0_disjoint mask v); [apply (HposA_iff v Hv); exact Hrv | exact HB].
      - intro H0v. destruct (pos_A_B0_cover mask v ltac:(lia)) as [HA | HB]; [| exact HB].
        exfalso. apply (HposA_iff v Hv) in HA. apply Hnot0r.
        eapply reachable_trans; [exact H0v | apply reachable_sym; exact HA]. }
    assert (Hr_inA : In r (pos_A mask)) by (apply (HposA_iff r ltac:(lia)); apply reach_refl).
    destruct (index_of_spec r (pos_A mask) Hr_inA) as [Hidx Hnr].
    unfold split_tree. fold k r T' mask.
    apply (sublists_ext E _ T (proj1 HwfE) (filter_in_sublists _ E) HinSubT).
    intros [u v]. unfold join_tree. rewrite filter_In, edge_mem_iff. rewrite Hnr.
    split.
    - intros [_ [Heq | Hin]].
      + inversion Heq; subst. exact Hin0r.
      + apply in_app_iff in Hin. destruct Hin as [Hin | Hin];
          apply in_map_iff in Hin; destruct Hin as [e0 [Heq He0]];
          unfold project_edges in He0; apply filter_In in He0; destruct He0 as [_ Hm];
          apply edge_mem_iff in Hm; rewrite Heq in Hm;
          apply remove_edge_in in Hm; exact (proj1 Hm).
    - intro HeT.
      split; [exact (sublists_incl E T HinSubT _ HeT) |].
      destruct (edge_eq_dec (u, v) (0%nat, r)) as [Heq | Hne]; [left; symmetry; exact Heq | right].
      assert (HeT' : In (u, v) T') by (apply remove_edge_in; split; assumption).
      rewrite Forall_forall in HwfT'. pose proof (HwfT' (u, v) HeT') as Huv. simpl in Huv.
      apply in_app_iff.
      destruct (Hpart u ltac:(lia)) as [H0u | Hru].
      + right.
        assert (H0v : reachable T' 0%nat v) by (eapply reachable_trans; [exact H0u | eapply reach_step; [left; exact HeT' | apply reach_refl]]).
        destruct (index_of_spec u (pos_B0 mask) (proj2 (HposB_iff u ltac:(lia)) H0u)) as [Hiu Hnu].
        destruct (index_of_spec v (pos_B0 mask) (proj2 (HposB_iff v ltac:(lia)) H0v)) as [Hiv Hnv].
        rewrite pos_B0_length in Hiu, Hiv.
        assert (Hiuv : (index_of u (pos_B0 mask) < index_of v (pos_B0 mask))%nat).
        { destruct (lt_eq_lt_dec (index_of u (pos_B0 mask)) (index_of v (pos_B0 mask))) as [[Hlt | Heq] | Hgt];
            [exact Hlt | rewrite <- Hnu, <- Hnv, Heq in Huv; lia |].
          pose proof (pos_B0_strict_mono mask _ _ Hgt ltac:(rewrite pos_B0_length; exact Hiu)). lia. }
        apply in_map_iff. exists (index_of u (pos_B0 mask), index_of v (pos_B0 mask)).
        cbv beta; cbn [fst snd]; rewrite Hnu, Hnv. split; [reflexivity |].
        unfold project_edges; apply filter_In; split; [| cbv beta; cbn [fst snd]; rewrite Hnu, Hnv; apply edge_mem_iff; exact HeT'].
        apply graph_edges_in. simpl length; rewrite (select_false_length mask Y Hmlen).
        pose proof (sublists_incl E T HinSubT _ HeT) as HinE.
        apply graph_edges_in in HinE. destruct HinE as [_ [_ [x [y [Hx [Hy Hob]]]]]].
        repeat split; [exact Hiuv | exact Hiv |]. exists x, y.
        rewrite (select_false_nth_error p0 mask Y _ Hmlen Hiu), Hnu.
        rewrite (select_false_nth_error p0 mask Y _ Hmlen Hiv), Hnv. repeat split; assumption.
      + left.
        assert (Hrv : reachable T' r v) by (eapply reachable_trans; [exact Hru | eapply reach_step; [left; exact HeT' | apply reach_refl]]).
        destruct (index_of_spec u (pos_A mask) (proj2 (HposA_iff u ltac:(lia)) Hru)) as [Hiu Hnu].
        destruct (index_of_spec v (pos_A mask) (proj2 (HposA_iff v ltac:(lia)) Hrv)) as [Hiv Hnv].
        rewrite pos_A_length in Hiu, Hiv.
        assert (Hiuv : (index_of u (pos_A mask) < index_of v (pos_A mask))%nat).
        { destruct (lt_eq_lt_dec (index_of u (pos_A mask)) (index_of v (pos_A mask))) as [[Hlt | Heq] | Hgt];
            [exact Hlt | rewrite <- Hnu, <- Hnv, Heq in Huv; lia |].
          pose proof (pos_A_strict_mono mask _ _ Hgt ltac:(rewrite pos_A_length; exact Hiu)). lia. }
        apply in_map_iff. exists (index_of u (pos_A mask), index_of v (pos_A mask)).
        simpl; rewrite Hnu, Hnv. split; [reflexivity |].
        unfold project_edges; apply filter_In; split; [| simpl; rewrite Hnu, Hnv; apply edge_mem_iff; exact HeT'].
        apply graph_edges_in. rewrite (select_true_length mask Y Hmlen).
        pose proof (sublists_incl E T HinSubT _ HeT) as HinE.
        apply graph_edges_in in HinE. destruct HinE as [_ [_ [x [y [Hx [Hy Hob]]]]]].
        repeat split; [exact Hiuv | exact Hiv |]. exists x, y.
        rewrite (select_true_nth_error p0 mask Y _ Hmlen Hiu), Hnu.
        rewrite (select_true_nth_error p0 mask Y _ Hmlen Hiv), Hnv. repeat split; assumption.
  Qed.

  (* Round-trip 2: split_tree (join_tree q) = q *)
  Lemma split_join_id : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P) mask idx TA TB,
    (1 <= length Y)%nat ->
    In (mask, idx, TA, TB) (valid_quads ob p0 Y) ->
    split_tree ob p0 Y (join_tree (graph_edges ob (p0 :: Y)) mask idx TA TB) = (mask, idx, TA, TB).
  Proof.
    intros P ob p0 Y mask idx TA TB Hk Hq.
    pose proof (join_tree_in_spanning ob p0 Y mask idx TA TB Hk Hq) as HinT.
    apply valid_quads_in in Hq; [| exact Hk].
    destruct Hq as [Hmlen [Hm0 [Hidx [[q [Hq Hob]] [HTA HTB]]]]].
    set (k := length Y).
    set (E := graph_edges ob (p0 :: Y)).
    set (r := nth idx (pos_A mask) 0%nat).
    set (T := join_tree E mask idx TA TB).
    pose proof (graph_edges_wf ob (p0 :: Y)) as HwfE. simpl length in HwfE.
    pose proof (graph_edges_wf ob (select_true mask Y)) as HwfEA.
    rewrite (select_true_length mask Y Hmlen) in HwfEA.
    pose proof (graph_edges_wf ob (p0 :: select_false mask Y)) as HwfEB.
    simpl length in HwfEB. rewrite (select_false_length mask Y Hmlen) in HwfEB.
    unfold spanning_trees in HTA, HTB; apply filter_In in HTA; apply filter_In in HTB.
    destruct HTA as [HsubA HtrA]; destruct HTB as [HsubB HtrB].
    unfold is_treeb in HtrA, HtrB; rewrite !andb_true_iff, !Nat.eqb_eq in HtrA, HtrB.
    destruct HtrA as [HconnA HlenA]; destruct HtrB as [HconnB HlenB].
    pose proof (sublists_Forall _ _ TA (proj2 HwfEA) HsubA) as HforA.
    pose proof (sublists_Forall _ _ TB (proj2 HwfEB) HsubB) as HforB.
    assert (Hr_in : In r (pos_A mask)) by (unfold r; apply nth_In; rewrite pos_A_length; exact Hidx).
    assert (Hr_bounds : (1 <= r <= k)%nat) by (apply pos_A_in in Hr_in; lia).
    assert (H0r_in_E : In (0%nat, r) E).
    { unfold E. apply graph_edges_in. repeat split; [lia | simpl; lia |].
      exists p0, q. unfold r. rewrite <- (select_true_nth_error p0 mask Y idx Hmlen Hidx).
      split; [reflexivity | split; [exact Hq | exact Hob]]. }
    assert (HT_iff : forall e, In e T <->
      e = (0%nat, r) \/ In e (embed_edges (pos_A mask) TA) \/ In e (embed_edges (pos_B0 mask) TB)).
    { intro e. unfold T, join_tree. fold r. rewrite filter_In, edge_mem_iff. simpl In. rewrite in_app_iff.
      split; [intros [_ [<- | H]]; [left; reflexivity | right; exact H] |].
      intros [-> | [H | H]]; split; try (left; reflexivity); try (right; left; exact H); try (right; right; exact H).
      - exact H0r_in_E.
      - apply in_map_iff in H; destruct H as [eA [<- HeA]].
        exact (embed_A_in_E ob p0 mask Y eA Hmlen (sublists_incl _ TA HsubA _ HeA)).
      - apply in_map_iff in H; destruct H as [eB [<- HeB]].
        exact (embed_B0_in_E ob p0 mask Y eB Hmlen (sublists_incl _ TB HsubB _ HeB)). }
    (* Edges of T \ {(0, r)} stay inside pos_A or inside pos_B0 *)
    set (T' := remove_edge (0%nat, r) T).
    assert (HforA_len : Forall (fun e => (fst e < snd e)%nat /\ (snd e < length (pos_A mask))%nat) TA)
      by (rewrite pos_A_length; exact HforA).
    assert (HforB_len : Forall (fun e => (fst e < snd e)%nat /\ (snd e < length (pos_B0 mask))%nat) TB)
      by (rewrite pos_B0_length; exact HforB).
    assert (HT'_iff : forall e, In e T' <->
      In e (embed_edges (pos_A mask) TA) \/ In e (embed_edges (pos_B0 mask) TB)).
    { intro e. unfold T'. rewrite remove_edge_in, HT_iff. split.
      - intros [[Heq | H] Hne]; [contradiction | exact H].
      - intros [H | H]; split; try (right; left; exact H); try (right; right; exact H);
          intro Heq; subst e.
        + destruct (embed_edges_in_pos _ _ _ _ HforA_len H) as [H0A _].
          apply pos_A_in in H0A; lia.
        + destruct (embed_edges_in_pos _ _ _ _ HforB_len H) as [_ HrB].
          exact (pos_A_B0_disjoint mask r Hr_in HrB). }
    assert (HT'_stay_A : forall u v, has_edge T' u v -> In v (pos_A mask) -> In u (pos_A mask)).
    { intros u v [He | He] HvA; apply HT'_iff in He; destruct He as [HA | HB].
      - exact (proj1 (embed_edges_in_pos _ _ _ _ HforA_len HA)).
      - exfalso. exact (pos_A_B0_disjoint mask v HvA (proj2 (embed_edges_in_pos _ _ _ _ HforB_len HB))).
      - exact (proj2 (embed_edges_in_pos _ _ _ _ HforA_len HA)).
      - exfalso. exact (pos_A_B0_disjoint mask v HvA (proj1 (embed_edges_in_pos _ _ _ _ HforB_len HB))). }
    assert (Hreach_stay_A : forall u v, reachable T' u v -> In v (pos_A mask) -> In u (pos_A mask)).
    { intros u v Hr' HvA. induction Hr'; [exact HvA | exact (HT'_stay_A u v H (IHHr' HvA))]. }
    (* Step 1: root_child_of_1 k T = r *)
    assert (Hr0_eq : root_child_of_1 k T = r).
    { unfold spanning_trees in HinT; apply filter_In in HinT; destruct HinT as [HsubT HtrT].
      unfold is_treeb in HtrT; rewrite andb_true_iff in HtrT; destruct HtrT as [HconnT _].
      pose proof (sublists_Forall _ E T (proj2 HwfE) HsubT) as HwfT.
      pose proof (root_child_of_1_spec k T Hk HwfT HconnT) as [Hr0 [Hin0r0 Hra1]].
      set (r0 := root_child_of_1 k T) in *.
      assert (H1_inA : In 1%nat (pos_A mask)) by (apply pos_A_in; simpl; repeat split; try lia; exact Hm0).
      assert (Hr0_inA : In r0 (pos_A mask)).
      { apply (Hreach_stay_A r0 1%nat (reachable_avoid0_to_remove T r r0 1%nat Hra1) H1_inA). }
      apply HT_iff in Hin0r0. destruct Hin0r0 as [Heq | [HA | HB]].
      - injection Heq; auto.
      - destruct (embed_edges_in_pos _ _ _ _ HforA_len HA) as [H0A _].
        apply pos_A_in in H0A; lia.
      - destruct (embed_edges_in_pos _ _ _ _ HforB_len HB) as [_ Hr0B].
        exfalso. exact (pos_A_B0_disjoint mask r0 Hr0_inA Hr0B). }
    (* Step 2: mask_of_tree k T' = mask *)
    assert (Hmask_eq : mask_of_tree k T' = mask).
    { pose proof (sublists_Forall _ E T' (proj2 HwfE) (remove_edge_in_sublists E T (0%nat, r) (filter_in_sublists _ E))) as HwfT'.
      (* Every v in pos_B0 is reachable from 0 in T', and no v in pos_A is *)
      rewrite <- Hmlen in HconnB.
      apply (is_connectedb_iff _ TB HforB) in HconnB. destruct HconnB as [_ HreachB].
      assert (HliftB' : forall u v, (u < S (k - count_true mask))%nat -> reachable TB u v ->
        reachable T' (nth u (pos_B0 mask) 0%nat) (nth v (pos_B0 mask) 0%nat)).
      { intros u v Hu HrB. induction HrB; [apply reach_refl |].
        pose proof (wf_has_edge_lt _ _ u v HforB H) as [_ [Hv _]].
        eapply reach_step; [| apply IHHrB; lia].
        destruct H as [Ha | Hb]; [left | right]; apply HT'_iff; right;
          unfold embed_edges; [apply (in_map (fun e => (nth (fst e) (pos_B0 mask) 0%nat, nth (snd e) (pos_B0 mask) 0%nat)) _ (u, v) Ha) |
                               apply (in_map (fun e => (nth (fst e) (pos_B0 mask) 0%nat, nth (snd e) (pos_B0 mask) 0%nat)) _ (v, u) Hb)]. }
      apply (nth_ext _ _ false false).
      - unfold mask_of_tree. rewrite map_length, seq_length. symmetry; exact Hmlen.
      - intros i Hi. unfold mask_of_tree in Hi. rewrite map_length, seq_length in Hi.
        rewrite (mask_of_tree_nth k T' i Hi).
        destruct (nth i mask false) eqn:Emi.
        + apply negb_true_iff.
          destruct (existsb (Nat.eqb (S i)) (expand_iter (S k) T' [0%nat])) eqn:Ex; [| reflexivity].
          apply expand_iter_0_iff in Ex.
          assert (H0A : In 0%nat (pos_A mask)).
          { apply (Hreach_stay_A 0%nat (S i) (reachable_k_to_reachable _ _ _ _ Ex)).
            apply pos_A_in. replace (S i - 1)%nat with i by lia. repeat split; try lia; exact Emi. }
          apply pos_A_in in H0A; lia.
        + apply negb_false_iff. apply expand_iter_0_iff.
          assert (HSiB : In (S i) (pos_B0 mask)).
          { apply pos_B0_in. right. replace (S i - 1)%nat with i by lia.
            repeat split; try lia. rewrite (nth_bool_default mask i true false ltac:(lia)). exact Emi. }
          destruct (index_of_spec (S i) (pos_B0 mask) HSiB) as [Hiv Hnv].
          rewrite pos_B0_length in Hiv.
          assert (Hr0 : reachable T' 0%nat (S i)).
          { rewrite <- Hnv. change 0%nat with (nth 0%nat (pos_B0 mask) 0%nat).
            apply (HliftB' 0%nat _ ltac:(lia)). apply HreachB. lia. }
          eapply reachable_k_mono; [| apply (reachable_bounded_length (S k) T' 0%nat (S i) HwfT' ltac:(lia) Hr0)].
          lia. }
    (* Step 3: idx, TA, TB match *)
    unfold split_tree. fold k. rewrite Hr0_eq. fold T'. rewrite Hmask_eq.
    assert (Hidx_eq : index_of r (pos_A mask) = idx).
    { unfold r. apply index_of_nth; [apply strict_mono_NoDup, pos_A_strict_mono | rewrite pos_A_length; exact Hidx]. }
    assert (HTA_eq : project_edges (pos_A mask) (graph_edges ob (select_true mask Y)) T' = TA).
    { apply (sublists_ext _ _ TA (proj1 HwfEA) (filter_in_sublists _ _) HsubA).
      intros [u v]. unfold project_edges. rewrite filter_In, edge_mem_iff, HT'_iff. simpl fst; simpl snd. split.
      - intros [HinEA [HA | HB]].
        + pose proof (proj2 HwfEA) as HfEA; rewrite Forall_forall in HfEA; pose proof (HfEA (u, v) HinEA) as Luv; simpl in Luv.
          exact (embed_edges_in_inv (pos_A mask) TA u v (pos_A_inj mask) HforA_len ltac:(rewrite pos_A_length; lia) ltac:(rewrite pos_A_length; lia) HA).
        + pose proof (proj2 HwfEA) as HfEA; rewrite Forall_forall in HfEA; pose proof (HfEA (u, v) HinEA) as Luv; simpl in Luv.
          destruct (embed_edges_in_pos _ _ _ _ HforB_len HB) as [HuB _].
          exfalso. apply (pos_A_B0_disjoint mask (nth u (pos_A mask) 0%nat)); [apply nth_In; rewrite pos_A_length; lia | exact HuB].
      - intro Huv. split; [exact (sublists_incl _ TA HsubA _ Huv) |].
        left. apply in_map_iff. exists (u, v). simpl. split; [reflexivity | exact Huv]. }
    assert (HTB_eq : project_edges (pos_B0 mask) (graph_edges ob (p0 :: select_false mask Y)) T' = TB).
    { apply (sublists_ext _ _ TB (proj1 HwfEB) (filter_in_sublists _ _) HsubB).
      intros [u v]. unfold project_edges. rewrite filter_In, edge_mem_iff, HT'_iff. simpl fst; simpl snd. split.
      - intros [HinEB [HA | HB]].
        + pose proof (proj2 HwfEB) as HfEB; rewrite Forall_forall in HfEB; pose proof (HfEB (u, v) HinEB) as Luv; simpl in Luv.
          destruct (embed_edges_in_pos _ _ _ _ HforA_len HA) as [HuA _].
          exfalso. apply (pos_A_B0_disjoint mask (nth u (pos_B0 mask) 0%nat)); [exact HuA | apply nth_In; rewrite pos_B0_length; lia].
        + pose proof (proj2 HwfEB) as HfEB; rewrite Forall_forall in HfEB; pose proof (HfEB (u, v) HinEB) as Luv; simpl in Luv.
          exact (embed_edges_in_inv (pos_B0 mask) TB u v (pos_B0_inj mask) HforB_len ltac:(rewrite pos_B0_length; lia) ltac:(rewrite pos_B0_length; lia) HB).
      - intro Huv. split; [exact (sublists_incl _ TB HsubB _ Huv) |].
        right. apply in_map_iff. exists (u, v). simpl. split; [reflexivity | exact Huv]. }
    rewrite Hidx_eq, HTA_eq, HTB_eq. reflexivity.
  Qed.

  (* =======================================================================
     4. Main Vertex-1 Tree Decomposition Identity (Exact Cardinality!)
     ======================================================================= *)

  Lemma bijection_length : forall {A B : Type} (lA : list A) (lB : list B) (f : A -> B) (g : B -> A),
    NoDup lA -> NoDup lB ->
    (forall a, In a lA -> In (f a) lB) ->
    (forall b, In b lB -> In (g b) lA) ->
    (forall a, In a lA -> g (f a) = a) ->
    (forall b, In b lB -> f (g b) = b) ->
    length lA = length lB.
  Proof.
    intros A B lA lB f g HndA HndB Hf Hg Hgf Hfg.
    assert (Hnd_f : NoDup (map f lA)).
    { apply NoDup_map_in; [exact HndA |].
      intros a1 a2 H1 H2 Heq. rewrite <- (Hgf a1 H1), <- (Hgf a2 H2), Heq. reflexivity. }
    assert (Hnd_g : NoDup (map g lB)).
    { apply NoDup_map_in; [exact HndB |].
      intros b1 b2 H1 H2 Heq. rewrite <- (Hfg b1 H1), <- (Hfg b2 H2), Heq. reflexivity. }
    assert (H1 : incl (map f lA) lB).
    { intros b Hb. apply in_map_iff in Hb. destruct Hb as [a [<- Ha]]. exact (Hf a Ha). }
    assert (H2 : incl (map g lB) lA).
    { intros a Ha. apply in_map_iff in Ha. destruct Ha as [b [<- Hb]]. exact (Hg b Hb). }
    pose proof (NoDup_incl_length Hnd_f H1) as L1.
    pose proof (NoDup_incl_length Hnd_g H2) as L2.
    rewrite map_length in L1, L2. lia.
  Qed.

  Theorem tree_count_decomp : forall {P : Type} (ob : P -> P -> bool) (p0 : P) (Y : list P),
    (1 <= length Y)%nat ->
    tree_count ob (p0 :: Y) =
    fold_right Nat.add 0%nat
      (map (fun mask =>
        (length (valid_roots ob p0 (select_true mask Y)) *
         tree_count ob (select_true mask Y) *
         tree_count ob (p0 :: select_false mask Y))%nat)
        (masks_head_true (length Y))).
  Proof.
    intros P ob p0 Y Hk.
    rewrite <- valid_quads_length.
    unfold tree_count. simpl length.
    apply (bijection_length
             (spanning_trees (S (length Y)) (graph_edges ob (p0 :: Y)))
             (valid_quads ob p0 Y)
             (split_tree ob p0 Y)
             (fun q => let '(mask, idx, TA, TB) := q in join_tree (graph_edges ob (p0 :: Y)) mask idx TA TB)).
    - apply NoDup_filter, sublists_NoDup_list, (proj1 (graph_edges_wf ob (p0 :: Y))).
    - apply valid_quads_NoDup.
    - intros T HT. exact (split_tree_in_quads ob p0 Y T Hk HT).
    - intros [[[mask idx] TA] TB] Hq. exact (join_tree_in_spanning ob p0 Y mask idx TA TB Hk Hq).
    - intros T HT. exact (join_split_id ob p0 Y T Hk HT).
    - intros [[[mask idx] TA] TB] Hq. exact (split_join_id ob p0 Y mask idx TA TB Hk Hq).
  Qed.

End TreeCutBijection.
