(* Auto-generated test file for tactic verification *)
(* Using apex_harness for standardized imports *)
From algebra Require Import apex_harness.


(* Target: quadratic_form_decomposition_finite (admitted) *)
Lemma test_quadratic_form_decomposition_finite : forall (beta : R) (f : G -> R), beta >= 0 -> Q beta f = Q_decomposed beta f.
Proof.
  intros.
Qed.
