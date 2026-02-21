Require Import Coq.Reals.Reals.
Require Import Coq.Lists.List.
Import ListNotations.
Open Scope R_scope.

Lemma Hlen_test : forall (A : Type) (l : list A),
  fold_right Rplus 0 (map (fun _ => 1) l) = INR (length l).
Proof.
  intros A l. induction l as [|x xs IH].
  - simpl. reflexivity.
  - simpl. rewrite IH. destruct (length xs); ring.
Qed.
