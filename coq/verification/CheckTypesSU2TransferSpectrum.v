(* =========================================================================
   verification/CheckTypesSU2TransferSpectrum.v

   Typechecks that the verified Target 14 theorem in `VerifySU2TransferSpectrum`
   has the exact frozen proposition type declared in
   `ChallengeSU2TransferSpectrum`. Kept separate from
   `CheckAxiomsSU2TransferSpectrum.v` so the axiom log contains ONLY
   `Print Assumptions` output.
   ========================================================================= *)

Require Import verification.ChallengeSU2TransferSpectrum.
Require Import verification.VerifySU2TransferSpectrum.

Check (VerifySU2TransferSpectrum.verified_su2gauge4D_transfer_spectrum :
         ChallengeSU2TransferSpectrum.Challenge_SU2Gauge4D_TransferSpectrum).
