(* =========================================================================
   verification/CheckTypesSU2HilbertSpace.v

   Typechecks that the verified Target 13 theorem in `VerifySU2HilbertSpace`
   has the exact frozen proposition type declared in
   `ChallengeSU2HilbertSpace`. Kept separate from
   `CheckAxiomsSU2HilbertSpace.v` so the axiom log contains ONLY
   `Print Assumptions` output.
   ========================================================================= *)

Require Import verification.ChallengeSU2HilbertSpace.
Require Import verification.VerifySU2HilbertSpace.

Check (VerifySU2HilbertSpace.verified_su2gauge4D_os_hilbert_space :
         ChallengeSU2HilbertSpace.Challenge_SU2Gauge4D_OSHilbertSpace).
