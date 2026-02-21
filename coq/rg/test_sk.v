Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Require Import Lra.
Import ListNotations.
Open Scope R_scope.

Require Import rg.polymer_types.
Require Import rg.pinned_bound.

(* We define everything needed to prove `rooted_sum_Sk_le_prod_1plus` here
   to avoid cluttering `pinned_bound.v` until it's perfect, then we'll paste it. *)
Fixpoint all_sublists {A:Type} (L : list A) : list (list A) :=
  match L with
  | [] => [[]]
  | x::xs =>
      let S := all_sublists xs in
      S ++ map (fun s => x::s) S
  end.

Lemma sum_over_sublists_nonneg :
  forall (A : Type) (L : list A) (F : A -> R),
    (forall x, In x L -> 0 <= F x) ->
    0 <= sum_over_sublists L F.
Proof.
  intros A L F HF.
  induction L as [|x xs IH].
  - simpl. lra.
  - simpl. assert (Hxs : 0 <= sum_over_sublists xs F) by (apply IH; intros y Hy; apply HF; right; exact Hy).
    assert (Hx : 0 <= F x) by (apply HF; left; reflexivity).
    assert (0 <= F x * sum_over_sublists xs F) by (apply Rmult_le_pos; lra).
    lra.
Qed.

Lemma sum_over_sublists_ge_1 :
  forall (A : Type) (L : list A) (F : A -> R),
    (forall x, In x L -> 0 <= F x) ->
    1 <= sum_over_sublists L F.
Proof.
  intros A L F HF.
  induction L as [|x xs IH].
  - simpl. lra.
  - simpl. assert (Hxs : 1 <= sum_over_sublists xs F) by (apply IH; intros y Hy; apply HF; right; exact Hy).
    assert (Hx : 0 <= F x) by (apply HF; left; reflexivity).
    assert (Hxs0 : 0 <= sum_over_sublists xs F) by (apply Rle_trans with 1; lra).
    assert (0 <= F x * sum_over_sublists xs F) by (apply Rmult_le_pos; lra).
    lra.
Qed.

Lemma prod_over_sublist_le_sum_over_sublists :
  forall (A : Type) (eqA : forall x y : A, {x=y}+{x<>y}) (L qs : list A) (F : A -> R),
    (forall x, In x L -> 0 <= F x) ->
    NoDup L ->
    NoDup qs ->
    incl qs L ->
    fold_right Rmult 1 (map F qs) <= sum_over_sublists L F.
Proof.
Admitted.
