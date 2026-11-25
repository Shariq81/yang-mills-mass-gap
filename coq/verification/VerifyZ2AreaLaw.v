(* =========================================================================
   verification/VerifyZ2AreaLaw.v

   SOLUTION VERIFICATION MODULE FOR TARGET 7e (Wilson-loop area law of the
   4D Z_2 Wilson lattice gauge theory at strong coupling).

   Assigns the repository's submitted Coq proof
     - ym.z2_area_law.Z2AreaLaw.z2_wilson_loop_area_law
   to the exact frozen proposition declared in
   `verification/ChallengeZ2AreaLaw.v`.

   The submitted proof is stated directly on the frozen definitions, so no
   bridging lemmas are needed: the assignment is a single `exact`.

   This file declares ZERO Axioms, ZERO Parameters, and ZERO Admitted lemmas.
   ========================================================================= *)

Require Import verification.Challenge.
Require Import verification.ChallengeZ2Gauge.
Require Import verification.ChallengeZ2AreaLaw.
Require Import ym.z2_area_law.

Module VerifyZ2AreaLaw.

  (* TARGET 7e: Wilson-loop area law at strong coupling. *)
  Theorem verified_z2gauge4D_wilson_loop_area_law :
    ChallengeZ2AreaLaw.Challenge_Z2Gauge4D_WilsonLoopAreaLaw.
  Proof. exact Z2AreaLaw.z2_wilson_loop_area_law. Qed.

End VerifyZ2AreaLaw.
