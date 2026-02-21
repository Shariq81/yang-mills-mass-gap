Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Fixpoint sum_over_sublists {A : Type} (L : list A) (F : A -> R) : R :=
  match L with
  | [] => 1
  | x :: xs => sum_over_sublists xs F + F x * sum_over_sublists xs F
  end.

Lemma remove_not_in : forall (A:Type) (eqA: forall x y:A, {x=y}+{x<>y}) (l: list A) (x: A),
  ~ In x l -> remove eqA x l = l.
Proof.
  intros A eqA l x H. induction l as [|y ys IH].
  - reflexivity.
  - simpl. destruct (eqA x y) as [Heq|Hneq].
    + subst. exfalso. apply H. left. reflexivity.
    + rewrite IH.
      * reflexivity.
      * intro Hcontra. apply H. right. exact Hcontra.
Qed.

Lemma NoDup_remove : forall (A : Type) (eqA : forall x y : A, {x=y}+{x<>y}) (l : list A) (x : A),
  NoDup l -> NoDup (remove eqA x l).
Proof.
  intros A eqA l x H. induction H as [|y ys Hnin Hnd IH].
  - simpl. constructor.
  - simpl. destruct (eqA x y).
    + exact IH.
    + constructor.
      * intro Hcontra. apply in_remove in Hcontra. destruct Hcontra as [Hcontra_in Hcontra_neq]. contradiction.
      * exact IH.
Qed.

Lemma fold_right_remove : forall (A : Type) (eqA : forall x y : A, {x=y}+{x<>y}) (l : list A) (x : A) (F : A -> R),
  NoDup l -> In x l -> fold_right Rmult 1 (map F l) = F x * fold_right Rmult 1 (map F (remove eqA x l)).
Proof.
  intros A eqA l x F Hnd Hin. induction l as [|y ys IH].
  - inversion Hin.
  - simpl. destruct (eqA x y) as [HeqA|HneqA].
    + subst. inversion Hnd as [|? ? Hnin Hnd_ys]. subst.
      rewrite remove_not_in with (eqA:=eqA) (x:=y) (l:=ys).
      * reflexivity.
      * exact Hnin.
    + inversion Hnd as [|? ? Hnin Hnd_ys]. subst.
      apply in_inv in Hin. destruct Hin as [Heq | Hin_ys].
      * subst. contradiction.
      * simpl. rewrite IH.
        -- lra.
        -- exact Hnd_ys.
        -- exact Hin_ys.
Qed.

Lemma sum_over_sublists_nonneg : forall (A : Type) (xs : list A) (F : A -> R),
  (forall x, In x xs -> 0 <= F x) -> 0 <= sum_over_sublists xs F.
Proof.
  intros A xs F HF. induction xs as [|y ys IH].
  - simpl. lra.
  - simpl. assert (0 <= F y) by (apply HF; left; reflexivity).
    assert (0 <= sum_over_sublists ys F).
    { apply IH. intros x Hinx. apply HF. right. exact Hinx. }
    nra.
Qed.

Lemma prod_over_sublist_le_sum_over_sublists :
  forall (A : Type) (eqA : forall x y : A, {x=y}+{x<>y}) (L qs : list A) (F : A -> R),
    (forall x, In x L -> 0 <= F x) -> NoDup L -> NoDup qs -> incl qs L ->
    fold_right Rmult 1 (map F qs) <= sum_over_sublists L F.
Proof.
  intros A eqA L. induction L as [|x xs IH].
  - intros qs F HF HndL Hndqs Hincl. destruct qs.
    + simpl. lra.
    + exfalso. apply (Hincl a). left. reflexivity.
  - intros qs F HF HndL Hndqs Hincl. inversion HndL as [|? ? Hnin Hndxs]. subst.
    simpl. destruct (in_dec eqA x qs) as [Hinx | Hninx].
    + assert (Hrm: incl (remove eqA x qs) xs).
      { intros y Hy. apply in_remove in Hy. destruct Hy as [Hy_in Hneq].
        assert (H1: In y (x :: xs)) by (apply Hincl; exact Hy_in).
        destruct H1 as [Heq | Hinxs].
        * subst. contradiction.
        * exact Hinxs. }
      assert (Hndrm: NoDup (remove eqA x qs)).
      { apply NoDup_remove. exact Hndqs. }
      assert (IH_rm: fold_right Rmult 1 (map F (remove eqA x qs)) <= sum_over_sublists xs F).
      { apply IH.
        * intros x0 Hinx0. apply HF. right. exact Hinx0.
        * exact Hndxs.
        * exact Hndrm.
        * exact Hrm. }
      rewrite fold_right_remove with (eqA:=eqA) (x:=x) (F:=F) (l:=qs) by assumption.
      assert (H1: F x * fold_right Rmult 1 (map F (remove eqA x qs)) <= F x * sum_over_sublists xs F).
      { apply Rmult_le_compat_l.
        * apply HF. left. reflexivity.
        * exact IH_rm. }
      assert (H2: 0 <= sum_over_sublists xs F).
      { apply sum_over_sublists_nonneg.
        intros x0 Hinx0. apply HF. right. exact Hinx0. }
      nra.
    + assert (Hqs_xs: incl qs xs).
      { intros y Hy. assert (H1: In y (x :: xs)) by (apply Hincl; exact Hy).
        destruct H1 as [Heq | Hin_xs].
        * subst. exfalso. apply Hninx. exact Hy.
        * exact Hin_xs. }
      assert (H_IH: fold_right Rmult 1 (map F qs) <= sum_over_sublists xs F).
      { apply IH.
        * intros x0 Hinx0. apply HF. right. exact Hinx0.
        * exact Hndxs.
        * exact Hndqs.
        * exact Hqs_xs. }
      assert (H2: 0 <= F x) by (apply HF; left; reflexivity).
      assert (H3: 0 <= sum_over_sublists xs F).
      { apply sum_over_sublists_nonneg.
        intros x0 Hinx0. apply HF. right. exact Hinx0. }
      nra.
Qed.
