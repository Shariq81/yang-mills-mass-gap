(* Auto-generated test file for tactic verification *)
(* Using apex_harness for standardized imports *)
From algebra Require Import apex_harness.


(* Target: parseval_class_functions (admitted) *)
Lemma test_parseval_class_functions : forall f : G -> R, is_class_function f -> norm_squared f = sum_squared_projections f.
Proof.
  intros.
Qed.
