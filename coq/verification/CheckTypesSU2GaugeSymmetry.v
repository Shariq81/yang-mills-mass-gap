(* =========================================================================
   verification/CheckTypesSU2GaugeSymmetry.v

   Typechecks that the verified Target 15 theorem in `VerifySU2GaugeSymmetry`
   has the exact frozen proposition type declared in
   `ChallengeSU2GaugeSymmetry`. Kept separate from
   `CheckAxiomsSU2GaugeSymmetry.v` so the axiom log contains ONLY
   `Print Assumptions` output.
   ========================================================================= *)

Require Import verification.ChallengeSU2GaugeSymmetry.
Require Import verification.VerifySU2GaugeSymmetry.

Check (VerifySU2GaugeSymmetry.verified_su2gauge4D_gauge_symmetry :
         ChallengeSU2GaugeSymmetry.Challenge_SU2Gauge4D_GaugeSymmetry).
