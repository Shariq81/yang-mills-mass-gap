(* Auto-generated BATCH test file *)
From algebra Require Import apex_harness.

Section BatchTest.

Lemma test_batch : True.
Proof.
  first [ (idtac "APEX_SUCCESS: tactic_0"; exact I.) | (idtac "APEX_SUCCESS: tactic_1"; reflexivity.) | idtac "APEX_ALL_FAILED" ].
Qed.

End BatchTest.
