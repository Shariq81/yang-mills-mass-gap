(* =========================================================================
   verification/CheckTypesZ2AreaLaw.v

   Typechecks that the verified Target 7e theorem in `VerifyZ2AreaLaw` has
   the exact frozen proposition type declared in `ChallengeZ2AreaLaw`. Kept
   separate from `CheckAxiomsZ2AreaLaw.v` so the axiom log contains ONLY
   `Print Assumptions` output.
   ========================================================================= *)

Require Import verification.ChallengeZ2AreaLaw.
Require Import verification.VerifyZ2AreaLaw.

Check (VerifyZ2AreaLaw.verified_z2gauge4D_wilson_loop_area_law :
         ChallengeZ2AreaLaw.Challenge_Z2Gauge4D_WilsonLoopAreaLaw).
